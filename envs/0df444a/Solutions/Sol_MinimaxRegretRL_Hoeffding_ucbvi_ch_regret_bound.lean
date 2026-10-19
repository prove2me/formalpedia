-- Prove2me | solution 1 for MinimaxRegretRL.Hoeffding.ucbvi_ch_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T14:47:59.470062+00:00
-- url     : https://prove2.me/submissions/294cc259-485a-45da-a42e-e36c4791e1b4

import Mathlib
import Definitions.Def_MinimaxRegretRL_Hoeffding_Analysis

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MinimaxRegretRL.Hoeffding.UCBCH

open MinimaxRegretRL.Hoeffding

/-- Hoeffding's lemma for a finite distribution (from Mathlib's measure-theoretic version). -/
lemma hoeffding_fin {S : Type*} [Fintype S] (p : S → ℝ) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∑ y, p y = 1) (g : S → ℝ) (a b : ℝ) (hg : ∀ y, g y ∈ Set.Icc a b) (t : ℝ) :
    ∑ y, p y * Real.exp (t * (g y - ∑ z, p z * g z)) ≤ Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  classical
  let _ : MeasurableSpace S := ⊤
  have hsum : ∑ y, ENNReal.ofReal (p y) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hp0 y), hp1, ENNReal.ofReal_one]
  set q : PMF S := PMF.ofFintype (fun y => ENNReal.ofReal (p y)) hsum with hq
  set μ : MeasureTheory.Measure S := q.toMeasure with hμ
  have hint : ∀ f : S → ℝ, ∫ y, f y ∂μ = ∑ y, p y * f y := by
    intro f
    rw [hμ, PMF.integral_eq_sum]
    apply Finset.sum_congr rfl
    intro y _
    simp [hq, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hp0 y), smul_eq_mul]
  have hm : AEMeasurable g μ := (Measurable.of_discrete).aemeasurable
  have hb : ∀ᵐ y ∂μ, g y ∈ Set.Icc a b := MeasureTheory.ae_of_all μ hg
  have H := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb
  have h1 := H.mgf_le t
  simp only [ProbabilityTheory.mgf, hint] at h1
  refine le_trans h1 (le_of_eq ?_)
  congr 1
  push_cast
  rw [Real.norm_eq_abs, div_pow, sq_abs]
  ring

/-- Bennett-type MGF bound for an indicator under a finite distribution. -/
lemma bennett_ind {S : Type*} [Fintype S] [DecidableEq S] (p : S → ℝ) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∑ y, p y = 1) (y0 : S) (t : ℝ) :
    ∑ y, p y * Real.exp (t * ((if y = y0 then 1 else 0) - p y0)) ≤
      Real.exp (p y0 * (Real.exp t - 1 - t)) := by
  have e1 : ∑ y, p y * Real.exp (t * ((if y = y0 then 1 else 0) - p y0)) =
      Real.exp (-(t * p y0)) * ∑ y, p y * Real.exp (t * (if y = y0 then 1 else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [mul_sub, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    ring
  have e2 : ∑ y, p y * Real.exp (t * (if y = y0 then 1 else 0)) = 1 + p y0 * (Real.exp t - 1) := by
    have : ∀ y, p y * Real.exp (t * (if y = y0 then 1 else 0)) =
        p y + (if y = y0 then p y0 * (Real.exp t - 1) else 0) := by
      intro y
      by_cases hy : y = y0
      · subst hy; simp; ring
      · simp [hy]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_add_distrib, hp1]
    simp
  rw [e1, e2]
  have h3 : 1 + p y0 * (Real.exp t - 1) ≤ Real.exp (p y0 * (Real.exp t - 1)) := by
    have := Real.add_one_le_exp (p y0 * (Real.exp t - 1))
    linarith
  calc Real.exp (-(t * p y0)) * (1 + p y0 * (Real.exp t - 1))
      ≤ Real.exp (-(t * p y0)) * Real.exp (p y0 * (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp (p y0 * (Real.exp t - 1 - t)) := by
        rw [← Real.exp_add]; congr 1; ring


section Frame

variable {S : Type*} [Fintype S] [DecidableEq S] {K H : ℕ}

/-- Replace the draw at episode `k`, step `h`. -/
def upd (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) : Outcomes S K H :=
  Function.update ω k (Function.update (ω k) h y)

@[simp] lemma upd_self (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) :
    upd ω k h y k h = y := by simp [upd]

lemma upd_ne (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) (k' : Fin K) (h' : Fin H)
    (hne : ¬ (k' = k ∧ h' = h)) : upd ω k h y k' h' = ω k' h' := by
  unfold upd
  by_cases hk : k' = k
  · subst hk
    have hh : h' ≠ h := fun e => hne ⟨rfl, e⟩
    simp [Function.update_of_ne hh]
  · simp [Function.update_of_ne hk]

lemma upd_upd (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (y z : S) :
    upd (upd ω k h y) k h z = upd ω k h z := by
  simp [upd]

lemma upd_eq (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : upd ω k h (ω k h) = ω := by
  simp [upd]

/-- The involution `(ω, y) ↦ (ω[k,h := y], ω k h)`. -/
def updPerm (k : Fin K) (h : Fin H) : Equiv.Perm (Outcomes S K H × S) :=
  Function.Involutive.toPerm (fun p => (upd p.1 k h p.2, p.1 k h)) (by
    rintro ⟨ω, y⟩
    simp only [upd_upd, upd_eq, upd_self])

lemma sum_upd (F : Outcomes S K H → ℝ) (k : Fin K) (h : Fin H) :
    ∑ ω, ∑ y, F (upd ω k h y) = (Fintype.card S : ℝ) * ∑ ω, F ω := by
  have h1 : ∑ p : Outcomes S K H × S, F (upd p.1 k h p.2) =
      ∑ p : Outcomes S K H × S, F p.1 :=
    Fintype.sum_equiv (updPerm k h) _ _ (fun p => rfl)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h1
  rw [h1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- `ω` and `ω'` agree on all draws strictly before time `t` (time of `(k,h)` is `kH+h`). -/
def Agree (t : ℕ) (ω ω' : Outcomes S K H) : Prop :=
  ∀ (k : Fin K) (h : Fin H), k.val * H + h.val < t → ω k h = ω' k h

def Adapted {β : Type*} (t : ℕ) (f : Outcomes S K H → β) : Prop :=
  ∀ ω ω', Agree t ω ω' → f ω = f ω'

lemma Agree.mono {t t' : ℕ} (hle : t ≤ t') {ω ω' : Outcomes S K H} (h : Agree t' ω ω') :
    Agree t ω ω' :=
  fun k j hj => h k j (lt_of_lt_of_le hj hle)

lemma agree_upd (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) :
    Agree (k.val * H + h.val) ω (upd ω k h y) := by
  intro k' h' hlt
  refine (upd_ne ω k h y k' h' ?_).symm
  rintro ⟨rfl, rfl⟩
  exact lt_irrefl _ hlt

lemma pos_inj {k k' : Fin K} {h h' : Fin H}
    (e : k.val * H + h.val = k'.val * H + h'.val) : k = k' ∧ h = h' := by
  have hH : 0 < H := lt_of_le_of_lt (Nat.zero_le _) h.isLt
  have d : ∀ (a b : ℕ), b < H → (a * H + b) / H = a ∧ (a * H + b) % H = b := by
    intro a b hb
    constructor
    · rw [show a * H + b = b + a * H by ring, Nat.add_mul_div_right _ _ hH,
        Nat.div_eq_of_lt hb, zero_add]
    · rw [show a * H + b = b + a * H by ring, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  obtain ⟨a1, b1⟩ := d k h h.isLt
  obtain ⟨a2, b2⟩ := d k' h' h'.isLt
  rw [e] at a1 b1
  exact ⟨Fin.ext (a1.symm.trans a2), Fin.ext (b1.symm.trans b2)⟩

/-- Partial path weight: true kernel factors before time `t`, uniform factors after. -/
noncomputable def ppt (q : Fin K → Fin H → Outcomes S K H → S → ℝ) (t : ℕ)
    (ω : Outcomes S K H) : ℝ :=
  ∏ p : Fin K × Fin H,
    if p.1.val * H + p.2.val < t then q p.1 p.2 ω (ω p.1 p.2) else (Fintype.card S : ℝ)⁻¹

lemma ppt_succ [Nonempty S] (q : Fin K → Fin H → Outcomes S K H → S → ℝ)
    (k0 : Fin K) (h0 : Fin H) (ω : Outcomes S K H) :
    ppt q (k0.val * H + h0.val + 1) ω =
      (Fintype.card S : ℝ) * (ppt q (k0.val * H + h0.val) ω * q k0 h0 ω (ω k0 h0)) := by
  have hc : (Fintype.card S : ℝ) ≠ 0 := by
    have : 0 < Fintype.card S := Fintype.card_pos
    exact_mod_cast this.ne'
  unfold ppt
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (k0, h0)),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (k0, h0))]
  have hrest : ∏ x ∈ Finset.univ.erase (k0, h0),
      (if x.1.val * H + x.2.val < k0.val * H + h0.val + 1 then q x.1 x.2 ω (ω x.1 x.2)
        else (Fintype.card S : ℝ)⁻¹) =
      ∏ x ∈ Finset.univ.erase (k0, h0),
      (if x.1.val * H + x.2.val < k0.val * H + h0.val then q x.1 x.2 ω (ω x.1 x.2)
        else (Fintype.card S : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ (k0, h0) := Finset.ne_of_mem_erase hx
    have hne' : x.1.val * H + x.2.val ≠ k0.val * H + h0.val := by
      intro e
      obtain ⟨e1, e2⟩ := pos_inj e
      exact hne (Prod.ext e1 e2)
    have hiff : x.1.val * H + x.2.val < k0.val * H + h0.val + 1 ↔
        x.1.val * H + x.2.val < k0.val * H + h0.val := by omega
    simp only [hiff]
  rw [hrest]
  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, lt_irrefl, if_true, if_false]
  field_simp

lemma ppt_adapted (q : Fin K → Fin H → Outcomes S K H → S → ℝ)
    (hqad : ∀ k h, Adapted (k.val * H + h.val) (q k h)) (t : ℕ) : Adapted t (ppt q t) := by
  intro ω ω' hag
  unfold ppt
  apply Finset.prod_congr rfl
  intro p _
  split_ifs with hlt
  · rw [hqad p.1 p.2 ω ω' (hag.mono hlt.le), hag p.1 p.2 hlt]
  · rfl

lemma ppt_nonneg (q : Fin K → Fin H → Outcomes S K H → S → ℝ)
    (hq0 : ∀ k h ω y, 0 ≤ q k h ω y) (t : ℕ) (ω : Outcomes S K H) : 0 ≤ ppt q t ω := by
  unfold ppt
  apply Finset.prod_nonneg
  intro p _
  split_ifs
  · exact hq0 _ _ _ _
  · positivity

/-- One supermartingale step: summing out the draw at time `kH+h`. -/
lemma ppt_step [Nonempty S] (q : Fin K → Fin H → Outcomes S K H → S → ℝ)
    (hq0 : ∀ k h ω y, 0 ≤ q k h ω y)
    (hqad : ∀ k h, Adapted (k.val * H + h.val) (q k h))
    (k0 : Fin K) (h0 : Fin H) (Z Z' : Outcomes S K H → ℝ)
    (hstep : ∀ ω, ∑ y, q k0 h0 ω y * Z' (upd ω k0 h0 y) ≤ Z ω) :
    ∑ ω, ppt q (k0.val * H + h0.val + 1) ω * Z' ω ≤
      ∑ ω, ppt q (k0.val * H + h0.val) ω * Z ω := by
  have hc : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have key : ∀ ω y, ppt q (k0.val * H + h0.val + 1) (upd ω k0 h0 y) * Z' (upd ω k0 h0 y) =
      (Fintype.card S : ℝ) * (ppt q (k0.val * H + h0.val) ω *
        (q k0 h0 ω y * Z' (upd ω k0 h0 y))) := by
    intro ω y
    rw [ppt_succ q k0 h0 (upd ω k0 h0 y)]
    have a1 := ppt_adapted q hqad (k0.val * H + h0.val) ω (upd ω k0 h0 y) (agree_upd ω k0 h0 y)
    have a2 := hqad k0 h0 ω (upd ω k0 h0 y) (agree_upd ω k0 h0 y)
    rw [← a1, ← a2, upd_self]
    ring
  have hsum := sum_upd (fun ω => ppt q (k0.val * H + h0.val + 1) ω * Z' ω) k0 h0
  simp only [key] at hsum
  have hL : ∑ ω, ppt q (k0.val * H + h0.val + 1) ω * Z' ω =
      ∑ ω, ppt q (k0.val * H + h0.val) ω * ∑ y, q k0 h0 ω y * Z' (upd ω k0 h0 y) := by
    have e : ∑ ω, ∑ y, (Fintype.card S : ℝ) * (ppt q (k0.val * H + h0.val) ω *
        (q k0 h0 ω y * Z' (upd ω k0 h0 y))) =
        (Fintype.card S : ℝ) * ∑ ω, ppt q (k0.val * H + h0.val) ω *
          ∑ y, q k0 h0 ω y * Z' (upd ω k0 h0 y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [e] at hsum
    exact (mul_left_cancel₀ hc.ne' hsum).symm
  rw [hL]
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hstep ω) (ppt_nonneg q hq0 _ ω)

lemma time_decomp (t : ℕ) (ht : t < K * H) :
    ∃ (k : Fin K) (h : Fin H), k.val * H + h.val = t := by
  have hH : 0 < H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · subst h0; simp at ht
    · exact h0
  refine ⟨⟨t / H, (Nat.div_lt_iff_lt_mul hH).mpr ht⟩, ⟨t % H, Nat.mod_lt _ hH⟩, ?_⟩
  simp only
  rw [mul_comm]
  exact Nat.div_add_mod t H

/-- Iterated supermartingale bound. -/
theorem ppt_chain [Nonempty S] (q : Fin K → Fin H → Outcomes S K H → S → ℝ)
    (hq0 : ∀ k h ω y, 0 ≤ q k h ω y)
    (hqad : ∀ k h, Adapted (k.val * H + h.val) (q k h))
    (Z : ℕ → Outcomes S K H → ℝ)
    (hstep : ∀ (k : Fin K) (h : Fin H) ω,
      ∑ y, q k h ω y * Z (k.val * H + h.val + 1) (upd ω k h y) ≤ Z (k.val * H + h.val) ω) :
    ∀ t, t ≤ K * H → ∑ ω, ppt q t ω * Z t ω ≤ ∑ ω, ppt q 0 ω * Z 0 ω := by
  intro t
  induction t with
  | zero => intro _; exact le_refl _
  | succ t ih =>
    intro ht
    obtain ⟨k, h, e⟩ := time_decomp (K := K) (H := H) t (by omega)
    have st := ppt_step q hq0 hqad k h (Z t) (Z (t + 1)) (by
      intro ω; have := hstep k h ω; rw [e] at this; exact this)
    rw [e] at st
    exact le_trans st (ih (by omega))

lemma sum_ppt_zero [Nonempty S] (q : Fin K → Fin H → Outcomes S K H → S → ℝ) :
    ∑ ω, ppt q 0 ω = 1 := by
  have hc : (Fintype.card S : ℝ) ≠ 0 := by
    have : 0 < Fintype.card S := Fintype.card_pos
    exact_mod_cast this.ne'
  unfold ppt
  simp only [Nat.not_lt_zero, if_false, Finset.prod_const, Finset.card_univ,
    Finset.sum_const, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  push_cast
  rw [← pow_mul, inv_pow, mul_comm H K]
  exact mul_inv_cancel₀ (pow_ne_zero _ hc)

lemma ppt_full (q : Fin K → Fin H → Outcomes S K H → S → ℝ) (ω : Outcomes S K H) :
    ppt q (K * H) ω = ∏ k : Fin K, ∏ h : Fin H, q k h ω (ω k h) := by
  unfold ppt
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro k _
  apply Finset.prod_congr rfl
  intro h _
  have : k.val * H + h.val < K * H := by
    have h1 : k.val + 1 ≤ K := k.isLt
    have h2 := Nat.mul_le_mul_right H h1
    have h3 := h.isLt
    rw [add_one_mul] at h2
    omega
  simp only [this, if_true]

/-- Expectation of a terminal quantity under a supermartingale with constant start. -/
theorem expect_le [Nonempty S] (q : Fin K → Fin H → Outcomes S K H → S → ℝ)
    (hq0 : ∀ k h ω y, 0 ≤ q k h ω y)
    (hqad : ∀ k h, Adapted (k.val * H + h.val) (q k h))
    (Z : ℕ → Outcomes S K H → ℝ) (c : ℝ) (hZ0 : ∀ ω, Z 0 ω = c)
    (hstep : ∀ (k : Fin K) (h : Fin H) ω,
      ∑ y, q k h ω y * Z (k.val * H + h.val + 1) (upd ω k h y) ≤ Z (k.val * H + h.val) ω) :
    ∑ ω, (∏ k : Fin K, ∏ h : Fin H, q k h ω (ω k h)) * Z (K * H) ω ≤ c := by
  have := ppt_chain q hq0 hqad Z hstep (K * H) le_rfl
  simp only [ppt_full, hZ0] at this
  rw [← Finset.sum_mul, sum_ppt_zero, one_mul] at this
  exact this

end Frame

section Process

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

lemma past_eq (ω ω' : Outcomes S K H) (k : Fin K) (hag : Agree (k.val * H) ω ω') :
    past ω k = past ω' k := by
  funext i j
  unfold past
  apply hag
  have h1 : i.val + 1 ≤ k.val := i.isLt
  have h2 := Nat.mul_le_mul_right H h1
  rw [add_one_mul] at h2
  have h3 := j.isLt
  simp only
  omega

lemma stateAt_eq (init : InitialRule S K H) (ω ω' : Outcomes S K H) (k : Fin K) (h : ℕ)
    (hag : Agree (k.val * H + h) ω ω') : stateAt init ω k h = stateAt init ω' k h := by
  cases h with
  | zero =>
    simp only [stateAt]
    rw [past_eq ω ω' k (hag.mono (Nat.le_add_right _ _))]
  | succ h =>
    simp only [stateAt]
    split_ifs with hh
    · exact hag k ⟨h, hh⟩ (by simp only; omega)
    · rw [past_eq ω ω' k (hag.mono (by omega))]

lemma runPrefix_eq (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω ω' : Outcomes S K H) : ∀ n, Agree (n * H) ω ω' →
      runPrefix M H K δ sel init ω n = runPrefix M H K δ sel init ω' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hag
    have hle : n * H ≤ (n + 1) * H := Nat.mul_le_mul_right H (Nat.le_succ n)
    have ih' := ih (hag.mono hle)
    by_cases hn : n < K
    · have e1 : ∀ h : Fin H, stateAt init ω ⟨n, hn⟩ h.val = stateAt init ω' ⟨n, hn⟩ h.val := by
        intro h
        apply stateAt_eq
        apply hag.mono
        have := h.isLt
        rw [add_one_mul]
        simp only
        omega
      have e2 : ∀ h : Fin H, ω ⟨n, hn⟩ h = ω' ⟨n, hn⟩ h := by
        intro h
        apply hag
        have := h.isLt
        rw [add_one_mul]
        simp only
        omega
      simp only [runPrefix, dif_pos hn, ih', e1, e2]
    · simp only [runPrefix, dif_neg hn, ih']

lemma episodeQ_eq (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω ω' : Outcomes S K H) (k : Fin K) (hag : Agree (k.val * H) ω ω') :
    episodeQ M H K δ sel init ω k = episodeQ M H K δ sel init ω' k := by
  unfold episodeQ
  rw [runPrefix_eq M δ sel init ω ω' k.val hag]

lemma actionAt_eq (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω ω' : Outcomes S K H) (k : Fin K) (h : Fin H) (hag : Agree (k.val * H + h.val) ω ω') :
    actionAt M H K δ sel init ω k h = actionAt M H K δ sel init ω' k h := by
  unfold actionAt episodePolicy
  rw [episodeQ_eq M δ sel init ω ω' k (hag.mono (Nat.le_add_right _ _)),
    stateAt_eq init ω ω' k h.val hag]

/-- The kernel factor of the path probability at `(k,h)`. -/
noncomputable def qP (M : MDP S A) (H K : ℕ) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) : Fin K → Fin H → Outcomes S K H → S → ℝ :=
  fun k h ω y => M.P (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) y

lemma qP_adapted (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H) :
    ∀ k h, Adapted (k.val * H + h.val) (qP M H K δ sel init k h) := by
  intro k h ω ω' hag
  funext y
  simp only [qP]
  rw [stateAt_eq init ω ω' k h.val hag, actionAt_eq M δ sel init ω ω' k h hag]

lemma qP_nonneg (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H) :
    ∀ k h ω y, 0 ≤ qP M H K δ sel init k h ω y :=
  fun _ _ _ y => (M.kernel _ _).1 y

lemma qP_sum (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H) :
    ∀ k h ω, ∑ y, qP M H K δ sel init k h ω y = 1 :=
  fun _ _ _ => (M.kernel _ _).2

lemma pathProb_eq (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) :
    pathProb M H K δ sel init ω = ∏ k, ∏ h, qP M H K δ sel init k h ω (ω k h) := rfl

lemma pathProb_nonneg (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) : 0 ≤ pathProb M H K δ sel init ω := by
  rw [pathProb_eq]
  exact Finset.prod_nonneg (fun k _ => Finset.prod_nonneg (fun h _ => qP_nonneg M δ sel init k h ω _))

/-- Supermartingale bound for the UCBVI process. -/
theorem proc_expect_le (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (Z : ℕ → Outcomes S K H → ℝ) (c : ℝ) (hZ0 : ∀ ω, Z 0 ω = c)
    (hstep : ∀ (k : Fin K) (h : Fin H) ω,
      ∑ y, qP M H K δ sel init k h ω y * Z (k.val * H + h.val + 1) (upd ω k h y) ≤
        Z (k.val * H + h.val) ω) :
    ∑ ω, pathProb M H K δ sel init ω * Z (K * H) ω ≤ c := by
  simp only [pathProb_eq]
  exact expect_le _ (qP_nonneg M δ sel init) (qP_adapted M δ sel init) Z c hZ0 hstep

lemma sum_pathProb_le (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H) :
    ∑ ω, pathProb M H K δ sel init ω ≤ 1 := by
  have := proc_expect_le M δ sel init (fun _ _ => 1) 1 (fun _ => rfl) (by
    intro k h ω
    simp only [mul_one, qP_sum M δ sel init k h ω, le_refl])
  simpa using this

/-- Markov: if `Z ≥ 0` everywhere and `Z ≥ c > 0` on `E`, then `P(E) ≤ E[Z]/c`. -/
lemma probEvent_le_markov (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (E : Outcomes S K H → Prop) (Z : Outcomes S K H → ℝ) (c : ℝ) (hc : 0 < c)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZE : ∀ ω, E ω → c ≤ Z ω) :
    c * probEvent M H K δ sel init E ≤ ∑ ω, pathProb M H K δ sel init ω * Z ω := by
  classical
  unfold probEvent
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  have hp := pathProb_nonneg M δ sel init ω
  split_ifs with hE
  · rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hZE ω hE) hp
  · simp only [mul_zero]
    exact mul_nonneg hp (hZ0 ω)

lemma probEvent_mono (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (E F : Outcomes S K H → Prop) (hEF : ∀ ω, E ω → F ω) :
    probEvent M H K δ sel init E ≤ probEvent M H K δ sel init F := by
  classical
  unfold probEvent
  apply Finset.sum_le_sum
  intro ω _
  have hp := pathProb_nonneg M δ sel init ω
  by_cases hE : E ω
  · simp [hE, hEF ω hE]
  · simp only [hE, if_false]
    split_ifs <;> linarith

lemma probEvent_union (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (E F : Outcomes S K H → Prop) :
    probEvent M H K δ sel init (fun ω => E ω ∨ F ω) ≤
      probEvent M H K δ sel init E + probEvent M H K δ sel init F := by
  classical
  unfold probEvent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have hp := pathProb_nonneg M δ sel init ω
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF] <;> linarith

lemma probEvent_le_one (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (E : Outcomes S K H → Prop) : probEvent M H K δ sel init E ≤ 1 := by
  classical
  refine le_trans ?_ (sum_pathProb_le M δ sel init)
  unfold probEvent
  apply Finset.sum_le_sum
  intro ω _
  have hp := pathProb_nonneg M δ sel init ω
  split_ifs <;> linarith

lemma probEvent_false (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (E : Outcomes S K H → Prop) (hE : ∀ ω, ¬ E ω) : probEvent M H K δ sel init E = 0 := by
  classical
  unfold probEvent
  apply Finset.sum_eq_zero
  intro ω _
  simp [hE ω]

/-! Value bounds (copied from our proof of lemma18, Sol_pv_e46e5e41). -/

lemma sup_ge {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ)
    (hf : ∀ i ∈ s, c ≤ f i) : c ≤ s.sup' hs f := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs f
  rw [he]; exact hf i hi

lemma pvf_bounds (M : MDP S A) (H : ℕ) (π : Policy S A H) :
    ∀ (fuel h : ℕ) (x : S), 0 ≤ policyValueFuel M H π fuel h x ∧
      policyValueFuel M H π fuel h x ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro h x; simp [policyValueFuel]
  | succ n ih =>
    intro h x
    simp only [policyValueFuel]
    split_ifs with hh
    · obtain ⟨hP0, hP1⟩ := M.kernel x (π x ⟨h, hh⟩)
      have hR := M.reward_mem x (π x ⟨h, hh⟩)
      constructor
      · have : 0 ≤ ∑ y : S, M.P x (π x ⟨h, hh⟩) y * policyValueFuel M H π n (h + 1) y :=
          Finset.sum_nonneg (fun y _ => mul_nonneg (hP0 y) (ih (h+1) y).1)
        linarith [hR.1]
      · have h2 : ∑ y : S, M.P x (π x ⟨h, hh⟩) y * policyValueFuel M H π n (h + 1) y ≤
            ∑ y : S, M.P x (π x ⟨h, hh⟩) y * (n:ℝ) :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih (h+1) y).2 (hP0 y))
        rw [← Finset.sum_mul, hP1] at h2
        push_cast
        linarith [hR.2]
    · simp only [le_refl, true_and]
      push_cast
      positivity

lemma opt_bounds (M : MDP S A) (H h : ℕ) (x : S) :
    0 ≤ optimalValue M H h x ∧ optimalValue M H h x ≤ ((H - h : ℕ) : ℝ) := by
  unfold optimalValue
  constructor
  · apply sup_ge
    intro π _
    exact (pvf_bounds M H π (H - h) h x).1
  · apply Finset.sup'_le
    intro π _
    exact (pvf_bounds M H π (H - h) h x).2

lemma regret_le (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) : regret M H K δ sel init ω ≤ (K : ℝ) * H := by
  unfold regret
  have : ∀ k : Fin K, optimalValue M H 0 (stateAt init ω k 0) -
      policyValue M H (episodePolicy M H K δ sel init ω k) 0 (stateAt init ω k 0) ≤ (H : ℝ) := by
    intro k
    have h1 := (opt_bounds M H 0 (stateAt init ω k 0)).2
    have h2 := (pvf_bounds M H (episodePolicy M H K δ sel init ω k) (H - 0) 0
      (stateAt init ω k 0)).1
    simp only [Nat.sub_zero] at h1 h2
    unfold policyValue
    simp only [Nat.sub_zero]
    linarith
  calc _ ≤ ∑ _k : Fin K, (H : ℝ) := Finset.sum_le_sum (fun k _ => this k)
    _ = (K : ℝ) * H := by simp

end Process

section Conc

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

/-- Generic exponential supermartingale: if each increment has conditional exponential
moment at most one, the exponential of the total has expectation at most one. -/
theorem exp_sum_le (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (u : Fin K → Fin H → Outcomes S K H → ℝ)
    (hu : ∀ k h, Adapted (k.val * H + h.val + 1) (u k h))
    (hstep : ∀ k h ω, ∑ y, qP M H K δ sel init k h ω y * Real.exp (u k h (upd ω k h y)) ≤ 1) :
    ∑ ω, pathProb M H K δ sel init ω * Real.exp (∑ p : Fin K × Fin H, u p.1 p.2 ω) ≤ 1 := by
  let Z : ℕ → Outcomes S K H → ℝ := fun t ω =>
    Real.exp (∑ p : Fin K × Fin H, if p.1.val * H + p.2.val < t then u p.1 p.2 ω else 0)
  have hZ0 : ∀ ω, Z 0 ω = 1 := by intro ω; simp [Z]
  have hfull : ∀ ω, Z (K * H) ω = Real.exp (∑ p : Fin K × Fin H, u p.1 p.2 ω) := by
    intro ω
    simp only [Z]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    have : p.1.val * H + p.2.val < K * H := by
      have h1 : p.1.val + 1 ≤ K := p.1.isLt
      have h2 := Nat.mul_le_mul_right H h1
      have h3 := p.2.isLt
      rw [add_one_mul] at h2
      omega
    simp only [this, if_true]
  have key := proc_expect_le M δ sel init Z 1 hZ0 (by
    intro k0 h0 ω
    have hsplit : ∀ ω', (∑ p : Fin K × Fin H,
        if p.1.val * H + p.2.val < k0.val * H + h0.val + 1 then u p.1 p.2 ω' else 0) =
        (∑ p : Fin K × Fin H,
          if p.1.val * H + p.2.val < k0.val * H + h0.val then u p.1 p.2 ω' else 0) +
          u k0 h0 ω' := by
      intro ω'
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (k0, h0)),
        ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (k0, h0))]
      have hrest : ∑ x ∈ Finset.univ.erase (k0, h0),
          (if x.1.val * H + x.2.val < k0.val * H + h0.val + 1 then u x.1 x.2 ω' else 0) =
          ∑ x ∈ Finset.univ.erase (k0, h0),
          (if x.1.val * H + x.2.val < k0.val * H + h0.val then u x.1 x.2 ω' else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hne : x ≠ (k0, h0) := Finset.ne_of_mem_erase hx
        have hne' : x.1.val * H + x.2.val ≠ k0.val * H + h0.val := by
          intro e
          obtain ⟨e1, e2⟩ := pos_inj e
          exact hne (Prod.ext e1 e2)
        have hiff : x.1.val * H + x.2.val < k0.val * H + h0.val + 1 ↔
            x.1.val * H + x.2.val < k0.val * H + h0.val := by omega
        simp only [hiff]
      rw [hrest]
      simp only [lt_add_iff_pos_right, Nat.lt_one_iff, lt_irrefl, if_true, if_false]
      ring
    have hpast : ∀ y, (∑ p : Fin K × Fin H,
        if p.1.val * H + p.2.val < k0.val * H + h0.val then u p.1 p.2 (upd ω k0 h0 y) else 0) =
        (∑ p : Fin K × Fin H,
          if p.1.val * H + p.2.val < k0.val * H + h0.val then u p.1 p.2 ω else 0) := by
      intro y
      apply Finset.sum_congr rfl
      intro p _
      split_ifs with hlt
      · exact (hu p.1 p.2 ω (upd ω k0 h0 y) ((agree_upd ω k0 h0 y).mono hlt)).symm
      · rfl
    simp only [Z]
    simp only [hsplit, hpast, Real.exp_add]
    have : ∑ y, qP M H K δ sel init k0 h0 ω y *
        (Real.exp (∑ p : Fin K × Fin H,
          if p.1.val * H + p.2.val < k0.val * H + h0.val then u p.1 p.2 ω else 0) *
          Real.exp (u k0 h0 (upd ω k0 h0 y))) =
        Real.exp (∑ p : Fin K × Fin H,
          if p.1.val * H + p.2.val < k0.val * H + h0.val then u p.1 p.2 ω else 0) *
        ∑ y, qP M H K δ sel init k0 h0 ω y * Real.exp (u k0 h0 (upd ω k0 h0 y)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [this]
    calc _ ≤ Real.exp (∑ p : Fin K × Fin H,
          if p.1.val * H + p.2.val < k0.val * H + h0.val then u p.1 p.2 ω else 0) * 1 :=
          mul_le_mul_of_nonneg_left (hstep k0 h0 ω) (Real.exp_pos _).le
      _ = _ := mul_one _)
  simp only [hfull] at key
  exact key

/-! Visits of a fixed pair and their link with the history counts. -/

/-- Step `(k,h)` visits the pair `(x,a)`. -/
def visit (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (k : Fin K) (h : Fin H) (ω : Outcomes S K H) : Prop :=
  stateAt init ω k h.val = x ∧ actionAt M H K δ sel init ω k h = a

lemma visit_adapted (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (k : Fin K) (h : Fin H) (ω ω' : Outcomes S K H)
    (hag : Agree (k.val * H + h.val) ω ω') :
    visit M δ sel init x a k h ω ↔ visit M δ sel init x a k h ω' := by
  unfold visit
  rw [stateAt_eq init ω ω' k h.val hag, actionAt_eq M δ sel init ω ω' k h hag]

noncomputable instance visitDec (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (k : Fin K) (h : Fin H) (ω : Outcomes S K H) :
    Decidable (visit M δ sel init x a k h ω) := by
  unfold visit; infer_instance

/-- Weighted visit sum before time `t`. -/
noncomputable def vsum (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (g : S → ℝ) (t : ℕ) (ω : Outcomes S K H) : ℝ := by
  classical
  exact ∑ p : Fin K × Fin H,
    if p.1.val * H + p.2.val < t ∧ visit M δ sel init x a p.1 p.2 ω then g (ω p.1 p.2) else 0

/-- Visit count before time `t`. -/
noncomputable def cnt (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (t : ℕ) (ω : Outcomes S K H) : ℝ :=
  vsum M δ sel init x a (fun _ => 1) t ω

lemma countSAS_cons (t : S × A × S) (l : List (S × A × S)) (x : S) (a : A) (y : S) :
    countSAS (t :: l) x a y = countSAS l x a y + (if t.1 = x ∧ t.2.1 = a ∧ t.2.2 = y then 1 else 0) := by
  unfold countSAS
  by_cases ht : t.1 = x ∧ t.2.1 = a ∧ t.2.2 = y
  · simp [List.filter_cons, ht]
  · simp only [List.filter_cons, ht, decide_false]
    simp

lemma hist_wsum (l : List (S × A × S)) (x : S) (a : A) (g : S → ℝ) :
    ∑ y, (countSAS l x a y : ℝ) * g y =
      (l.map (fun t => if t.1 = x ∧ t.2.1 = a then g t.2.2 else 0)).sum := by
  induction l with
  | nil => simp [countSAS]
  | cons t l ih =>
    simp only [countSAS_cons, List.map_cons, List.sum_cons]
    rw [← ih]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    by_cases hx : t.1 = x ∧ t.2.1 = a
    · simp only [hx, true_and, if_true]
      simp [ite_mul, Finset.sum_ite_eq']
    · have : ∀ y, ¬ (t.1 = x ∧ t.2.1 = a ∧ t.2.2 = y) := fun y h => hx ⟨h.1, h.2.1⟩
      simp [this, hx]

lemma tau_lt_iff (j k : ℕ) (h : ℕ) (hh : h < H) : j * H + h < k * H ↔ j < k := by
  constructor
  · intro hlt
    by_contra hjk
    have hjk' : k ≤ j := Nat.le_of_not_lt hjk
    have := Nat.mul_le_mul_right H hjk'
    omega
  · intro hjk
    have h1 : j + 1 ≤ k := hjk
    have h2 := Nat.mul_le_mul_right H h1
    rw [add_one_mul] at h2
    omega

lemma runPrefix_hist_map (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (φ : S × A × S → ℝ) :
    ∀ n, n ≤ K → ((runPrefix M H K δ sel init ω n).history.map φ).sum =
      ∑ j : Fin K, ∑ h : Fin H, if j.val < n then
        φ (stateAt init ω j h.val, actionAt M H K δ sel init ω j h, ω j h) else 0 := by
  intro n
  induction n with
  | zero => intro _; simp [runPrefix]
  | succ n ih =>
    intro hn
    have hnK : n < K := hn
    have hact : ∀ h : Fin H, sel (qAt M H K δ (runPrefix M H K δ sel init ω n).history
        (runPrefix M H K δ sel init ω n).prevQ h.val (stateAt init ω ⟨n, hnK⟩ h.val)) =
        actionAt M H K δ sel init ω ⟨n, hnK⟩ h := fun h => rfl
    simp only [runPrefix, dif_pos hnK, List.map_append, List.sum_append, List.map_ofFn,
      List.sum_ofFn, Function.comp_def, hact]
    rw [ih (by omega)]
    have hsplit : ∀ (j : Fin K) (h : Fin H),
        (if j.val < n + 1 then
          φ (stateAt init ω j h.val, actionAt M H K δ sel init ω j h, ω j h) else 0) =
        (if j.val < n then
          φ (stateAt init ω j h.val, actionAt M H K δ sel init ω j h, ω j h) else 0) +
        (if j = ⟨n, hnK⟩ then
          φ (stateAt init ω j h.val, actionAt M H K δ sel init ω j h, ω j h) else 0) := by
      intro j h
      by_cases h1 : j.val < n
      · have h2 : j ≠ ⟨n, hnK⟩ := fun e => by rw [e] at h1; exact lt_irrefl _ h1
        have h3 : j.val < n + 1 := by omega
        simp only [h1, h2, h3, if_true, if_false, add_zero]
      · by_cases h2 : j = ⟨n, hnK⟩
        · subst h2
          simp
        · have h3 : ¬ j.val < n + 1 := fun h3 => h2 (Fin.ext (by simp only; omega))
          simp only [h1, h2, h3, if_false, add_zero]
    simp only [hsplit, Finset.sum_add_distrib]
    have hcol : ∀ j : Fin K, (∑ h : Fin H, if j = ⟨n, hnK⟩ then
        φ (stateAt init ω j h.val, actionAt M H K δ sel init ω j h, ω j h) else 0) =
        if j = ⟨n, hnK⟩ then ∑ h : Fin H,
          φ (stateAt init ω j h.val, actionAt M H K δ sel init ω j h, ω j h) else 0 := by
      intro j
      split_ifs <;> simp
    simp only [hcol, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma nAt_eq_cnt (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (x : S) (a : A) (g : S → ℝ) :
    ∑ y, (nyAt M H K δ sel init ω k x a y : ℝ) * g y = vsum M δ sel init x a g (k.val * H) ω := by
  classical
  unfold nyAt priorHistory
  rw [hist_wsum, runPrefix_hist_map M δ sel init ω _ k.val k.isLt.le]
  unfold vsum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h _
  have ht := tau_lt_iff (H := H) j.val k.val h.val h.isLt
  by_cases h1 : j.val < k.val
  · have h2 : j.val * H + h.val < k.val * H := ht.mpr h1
    simp [h1, h2, visit]
  · have h2 : ¬ j.val * H + h.val < k.val * H := fun h' => h1 (ht.mp h')
    simp [h1, h2, visit]

lemma nAt_cast (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (x : S) (a : A) :
    (nAt M H K δ sel init ω k x a : ℝ) = cnt M δ sel init x a (k.val * H) ω := by
  unfold cnt
  rw [← nAt_eq_cnt M δ sel init ω k x a (fun _ => 1)]
  unfold nAt countSA nyAt
  push_cast
  simp

end Conc

section Conc2

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

lemma sum_tau_succ (F : Fin K × Fin H → ℝ) (k0 : Fin K) (h0 : Fin H) :
    (∑ p : Fin K × Fin H,
      if p.1.val * H + p.2.val < k0.val * H + h0.val + 1 then F p else 0) =
      (∑ p : Fin K × Fin H,
        if p.1.val * H + p.2.val < k0.val * H + h0.val then F p else 0) + F (k0, h0) := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (k0, h0)),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (k0, h0))]
  have hrest : ∑ x ∈ Finset.univ.erase (k0, h0),
      (if x.1.val * H + x.2.val < k0.val * H + h0.val + 1 then F x else 0) =
      ∑ x ∈ Finset.univ.erase (k0, h0),
      (if x.1.val * H + x.2.val < k0.val * H + h0.val then F x else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ (k0, h0) := Finset.ne_of_mem_erase hx
    have hne' : x.1.val * H + x.2.val ≠ k0.val * H + h0.val := by
      intro e
      obtain ⟨e1, e2⟩ := pos_inj e
      exact hne (Prod.ext e1 e2)
    have hiff : x.1.val * H + x.2.val < k0.val * H + h0.val + 1 ↔
        x.1.val * H + x.2.val < k0.val * H + h0.val := by omega
    simp only [hiff]
  rw [hrest]
  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, lt_irrefl, if_true, if_false]
  ring

lemma vsum_ite (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (g : S → ℝ) (t : ℕ) (ω : Outcomes S K H) :
    vsum M δ sel init x a g t ω = ∑ p : Fin K × Fin H,
      if p.1.val * H + p.2.val < t then
        (if visit M δ sel init x a p.1 p.2 ω then g (ω p.1 p.2) else 0) else 0 := by
  unfold vsum
  apply Finset.sum_congr rfl
  intro p _
  by_cases h1 : p.1.val * H + p.2.val < t <;>
    by_cases h2 : visit M δ sel init x a p.1 p.2 ω <;> simp [h1, h2]

lemma vsum_adapted (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (g : S → ℝ) (t : ℕ) (ω ω' : Outcomes S K H) (hag : Agree t ω ω') :
    vsum M δ sel init x a g t ω = vsum M δ sel init x a g t ω' := by
  rw [vsum_ite, vsum_ite]
  apply Finset.sum_congr rfl
  intro p _
  by_cases ht : p.1.val * H + p.2.val < t
  · have hv := visit_adapted M δ sel init x a p.1 p.2 ω ω' (hag.mono ht.le)
    simp only [ht, if_true, hv, hag p.1 p.2 ht]
  · simp only [ht, if_false]

lemma cnt_adapted (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (t : ℕ) (ω ω' : Outcomes S K H) (hag : Agree t ω ω') :
    cnt M δ sel init x a t ω = cnt M δ sel init x a t ω' :=
  vsum_adapted M δ sel init x a _ t ω ω' hag

lemma cnt_mono (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (t t' : ℕ) (htt : t ≤ t') (ω : Outcomes S K H) :
    cnt M δ sel init x a t ω ≤ cnt M δ sel init x a t' ω := by
  unfold cnt
  rw [vsum_ite, vsum_ite]
  apply Finset.sum_le_sum
  intro p _
  by_cases h1 : p.1.val * H + p.2.val < t
  · have h2 : p.1.val * H + p.2.val < t' := lt_of_lt_of_le h1 htt
    simp only [h1, h2, if_true, le_refl]
  · simp only [h1, if_false]
    split_ifs <;> norm_num

lemma cnt_succ (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (k : Fin K) (h : Fin H) (ω : Outcomes S K H) :
    cnt M δ sel init x a (k.val * H + h.val + 1) ω =
      cnt M δ sel init x a (k.val * H + h.val) ω +
        (if visit M δ sel init x a k h ω then 1 else 0) := by
  unfold cnt
  rw [vsum_ite, vsum_ite]
  exact sum_tau_succ (fun p => if visit M δ sel init x a p.1 p.2 ω then (1 : ℝ) else 0) k h

lemma active_iff (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (n : ℕ) (k : Fin K) (ω : Outcomes S K H)
    (hk : cnt M δ sel init x a (k.val * H) ω = n) (p : Fin K × Fin H) :
    (visit M δ sel init x a p.1 p.2 ω ∧
      cnt M δ sel init x a (p.1.val * H + p.2.val) ω < n) ↔
      (p.1.val * H + p.2.val < k.val * H ∧ visit M δ sel init x a p.1 p.2 ω) := by
  constructor
  · rintro ⟨hv, hc⟩
    refine ⟨?_, hv⟩
    by_contra hlt
    have hle : k.val * H ≤ p.1.val * H + p.2.val := Nat.le_of_not_lt hlt
    have := cnt_mono M δ sel init x a _ _ hle ω
    rw [hk] at this
    linarith
  · rintro ⟨hlt, hv⟩
    refine ⟨hv, ?_⟩
    have h1 := cnt_succ M δ sel init x a p.1 p.2 ω
    simp only [hv, if_true] at h1
    have h2 := cnt_mono M δ sel init x a _ _ (Nat.succ_le_of_lt hlt) ω
    rw [hk, h1] at h2
    linarith

lemma sum_active_eq (F : Fin K × Fin H → ℝ) (c : Fin K × Fin H → Prop) [DecidablePred c]
    (α β : ℝ) :
    (∑ p, if c p then α * F p - β else 0) =
      α * (∑ p, if c p then F p else 0) - β * (∑ p, if c p then (1 : ℝ) else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

/-- Generic concentration at a random count, via a capped exponential supermartingale. -/
theorem conc_generic (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (g : S → ℝ) (lam ψ : ℝ) (hlam : 0 ≤ lam)
    (hmgf : ∑ y, M.P x a y * Real.exp (lam * (g y - ∑ z, M.P x a z * g z)) ≤ Real.exp ψ)
    (n : ℕ) (ε : ℝ) :
    probEvent M H K δ sel init (fun ω => ∃ k : Fin K, cnt M δ sel init x a (k.val * H) ω = n ∧
        (n : ℝ) * ε ≤ vsum M δ sel init x a g (k.val * H) ω - n * ∑ z, M.P x a z * g z) ≤
      Real.exp (-(lam * n * ε - n * ψ)) := by
  classical
  set Pg := ∑ z, M.P x a z * g z with hPg
  let u : Fin K → Fin H → Outcomes S K H → ℝ := fun k h ω =>
    if visit M δ sel init x a k h ω ∧ cnt M δ sel init x a (k.val * H + h.val) ω < n then
      lam * (g (ω k h) - Pg) - ψ else 0
  have hu : ∀ k h, Adapted (k.val * H + h.val + 1) (u k h) := by
    intro k h ω ω' hag
    have hag' : Agree (k.val * H + h.val) ω ω' := hag.mono (Nat.le_succ _)
    have e1 := cnt_adapted M δ sel init x a _ ω ω' hag'
    have e2 := visit_adapted M δ sel init x a k h ω ω' hag'
    have e3 : ω k h = ω' k h := hag k h (Nat.lt_succ_self _)
    simp only [u, e1, e2, e3]
  have hstep : ∀ k h ω,
      ∑ y, qP M H K δ sel init k h ω y * Real.exp (u k h (upd ω k h y)) ≤ 1 := by
    intro k h ω
    by_cases hact : visit M δ sel init x a k h ω ∧
        cnt M δ sel init x a (k.val * H + h.val) ω < n
    · have hq : ∀ y, qP M H K δ sel init k h ω y = M.P x a y := by
        intro y
        simp only [qP]
        rw [hact.1.1, hact.1.2]
      have hu' : ∀ y, u k h (upd ω k h y) = lam * (g y - Pg) - ψ := by
        intro y
        have h1 := (visit_adapted M δ sel init x a k h ω (upd ω k h y)
          (agree_upd ω k h y)).mp hact.1
        have h2 : cnt M δ sel init x a (k.val * H + h.val) (upd ω k h y) < n := by
          rw [← cnt_adapted M δ sel init x a _ ω (upd ω k h y) (agree_upd ω k h y)]
          exact hact.2
        simp only [u, h1, h2, and_self, if_true, upd_self]
      simp only [hq, hu']
      calc ∑ y, M.P x a y * Real.exp (lam * (g y - Pg) - ψ)
          = Real.exp (-ψ) * ∑ y, M.P x a y * Real.exp (lam * (g y - Pg)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            rw [sub_eq_add_neg (lam * (g y - Pg)), Real.exp_add]
            ring
        _ ≤ Real.exp (-ψ) * Real.exp ψ := mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    · have hu' : ∀ y, u k h (upd ω k h y) = 0 := by
        intro y
        have : ¬ (visit M δ sel init x a k h (upd ω k h y) ∧
            cnt M δ sel init x a (k.val * H + h.val) (upd ω k h y) < n) := by
          rw [← visit_adapted M δ sel init x a k h ω (upd ω k h y) (agree_upd ω k h y),
            ← cnt_adapted M δ sel init x a _ ω (upd ω k h y) (agree_upd ω k h y)]
          exact hact
        simp only [u, this, if_false]
      simp only [hu', Real.exp_zero, mul_one, qP_sum M δ sel init k h ω, le_refl]
  have hmain := exp_sum_le M δ sel init u hu hstep
  have hc : 0 < Real.exp (lam * n * ε - n * ψ) := Real.exp_pos _
  have hmk := probEvent_le_markov M δ sel init
    (fun ω => ∃ k : Fin K, cnt M δ sel init x a (k.val * H) ω = n ∧
        (n : ℝ) * ε ≤ vsum M δ sel init x a g (k.val * H) ω - n * Pg)
    (fun ω => Real.exp (∑ p : Fin K × Fin H, u p.1 p.2 ω)) _ hc
    (fun ω => (Real.exp_pos _).le) (by
      rintro ω ⟨k, hk, hev⟩
      apply Real.exp_le_exp.mpr
      have hsum : ∑ p : Fin K × Fin H, u p.1 p.2 ω =
          lam * vsum M δ sel init x a g (k.val * H) ω -
            (lam * Pg + ψ) * cnt M δ sel init x a (k.val * H) ω := by
        have hper : ∀ p : Fin K × Fin H, u p.1 p.2 ω =
            if (p.1.val * H + p.2.val < k.val * H ∧ visit M δ sel init x a p.1 p.2 ω) then
              lam * g (ω p.1 p.2) - (lam * Pg + ψ) else 0 := by
          intro p
          have hiff := active_iff M δ sel init x a n k ω hk p
          by_cases hc2 : (p.1.val * H + p.2.val < k.val * H ∧ visit M δ sel init x a p.1 p.2 ω)
          · simp only [u]
            rw [if_pos (hiff.mpr hc2), if_pos hc2]
            ring
          · simp only [u]
            rw [if_neg (fun hh => hc2 (hiff.mp hh)), if_neg hc2]
        rw [Finset.sum_congr rfl (fun p _ => hper p), sum_active_eq]
        rfl
      rw [hsum, hk]
      linear_combination mul_le_mul_of_nonneg_left hev hlam)
  have := le_trans hmk hmain
  rw [Real.exp_neg, ← one_div, le_div_iff₀ hc]
  linarith

end Conc2

section Events

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

lemma probEvent_exists_le {ι : Type*} [Fintype ι] (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S K H) (E : ι → Outcomes S K H → Prop) :
    probEvent M H K δ sel init (fun ω => ∃ i, E i ω) ≤
      ∑ i, probEvent M H K δ sel init (E i) := by
  classical
  unfold probEvent
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  have hp := pathProb_nonneg M δ sel init ω
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    calc pathProb M H K δ sel init ω
        = (if E i ω then pathProb M H K δ sel init ω else 0) := by rw [if_pos hi]
      _ ≤ ∑ j, (if E j ω then pathProb M H K δ sel init ω else 0) :=
        Finset.single_le_sum (f := fun j => if E j ω then pathProb M H K δ sel init ω else 0)
          (fun j _ => by split_ifs <;> linarith) (Finset.mem_univ i)
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> linarith)

lemma cnt_le (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (t : ℕ) (ω : Outcomes S K H) :
    cnt M δ sel init x a t ω ≤ (K : ℝ) * H := by
  unfold cnt vsum
  calc _ ≤ ∑ _p : Fin K × Fin H, (1 : ℝ) :=
        Finset.sum_le_sum (fun p _ => by split_ifs <;> norm_num)
    _ = (K : ℝ) * H := by simp

lemma nAt_le (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (x : S) (a : A) :
    nAt M H K δ sel init ω k x a ≤ K * H := by
  have h1 := cnt_le M δ sel init x a (k.val * H) ω
  rw [← nAt_cast] at h1
  exact_mod_cast h1

lemma phat_wsum (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (x : S) (a : A) (g : S → ℝ) :
    ∑ y, phatAt M H K δ sel init ω k x a y * g y =
      vsum M δ sel init x a g (k.val * H) ω / cnt M δ sel init x a (k.val * H) ω := by
  rw [← nAt_cast, ← nAt_eq_cnt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  unfold phatAt empirical nyAt nAt
  ring

/-- Concentration of the empirical row against `g`, at count `m`. -/
lemma event_gen (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (g : S → ℝ) (lam ψ : ℝ) (hlam : 0 ≤ lam)
    (hmgf : ∑ y, M.P x a y * Real.exp (lam * (g y - ∑ z, M.P x a z * g z)) ≤ Real.exp ψ)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) :
    probEvent M H K δ sel init (fun ω => ∃ k : Fin K, nAt M H K δ sel init ω k x a = m ∧
        ε ≤ ∑ y, (phatAt M H K δ sel init ω k x a y - M.P x a y) * g y) ≤
      Real.exp (-(lam * m * ε - m * ψ)) := by
  refine le_trans (probEvent_mono M δ sel init _ _ ?_) (conc_generic M δ sel init x a g lam ψ hlam hmgf m ε)
  rintro ω ⟨k, hk, hev⟩
  have hcnt : cnt M δ sel init x a (k.val * H) ω = m := by rw [← nAt_cast, hk]
  refine ⟨k, hcnt, ?_⟩
  have e : ∑ y, (phatAt M H K δ sel init ω k x a y - M.P x a y) * g y =
      vsum M δ sel init x a g (k.val * H) ω / cnt M δ sel init x a (k.val * H) ω -
        ∑ z, M.P x a z * g z := by
    rw [← phat_wsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [e, hcnt] at hev
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have key : (m : ℝ) * (vsum M δ sel init x a g (k.val * H) ω / m - ∑ z, M.P x a z * g z) =
      vsum M δ sel init x a g (k.val * H) ω - m * ∑ z, M.P x a z * g z := by
    field_simp
  have := mul_le_mul_of_nonneg_left hev hm'.le
  linarith [key]

/-- One-sided Hoeffding at a random count. -/
lemma eventA_one (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (g : S → ℝ) (lo hi : ℝ) (hlh : lo < hi) (hg : ∀ y, g y ∈ Set.Icc lo hi)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) :
    probEvent M H K δ sel init (fun ω => ∃ k : Fin K, nAt M H K δ sel init ω k x a = m ∧
        ε ≤ ∑ y, (phatAt M H K δ sel init ω k x a y - M.P x a y) * g y) ≤
      Real.exp (-(2 * m * ε ^ 2 / (hi - lo) ^ 2)) := by
  have hw : 0 < hi - lo := by linarith
  have hmgf := hoeffding_fin (M.P x a) (M.kernel x a).1 (M.kernel x a).2 g lo hi hg
    (4 * ε / (hi - lo) ^ 2)
  have h := event_gen M δ sel init x a g (4 * ε / (hi - lo) ^ 2)
    ((4 * ε / (hi - lo) ^ 2) ^ 2 * (hi - lo) ^ 2 / 8) (by positivity) hmgf m hm ε
  refine le_trans h (le_of_eq ?_)
  congr 1
  field_simp
  ring

/-- Bennett upper tail for one transition entry at a random count. -/
lemma eventB_one (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (y0 : S) (lam : ℝ) (hlam : 0 < lam) (L2 : ℝ) (m : ℕ) (hm : 0 < m) :
    probEvent M H K δ sel init (fun ω => ∃ k : Fin K, nAt M H K δ sel init ω k x a = m ∧
        (Real.exp lam - 1 - lam) / lam * M.P x a y0 + L2 / (lam * m) ≤
          phatAt M H K δ sel init ω k x a y0 - M.P x a y0) ≤ Real.exp (-L2) := by
  have hmgf := bennett_ind (M.P x a) (M.kernel x a).1 (M.kernel x a).2 y0 lam
  have hP : ∑ z, M.P x a z * (if z = y0 then (1 : ℝ) else 0) = M.P x a y0 := by
    simp [mul_ite, Finset.sum_ite_eq']
  have hmgf' : ∑ y, M.P x a y * Real.exp (lam * ((if y = y0 then (1 : ℝ) else 0) -
      ∑ z, M.P x a z * (if z = y0 then (1 : ℝ) else 0))) ≤
      Real.exp (M.P x a y0 * (Real.exp lam - 1 - lam)) := by
    rw [hP]; exact hmgf
  have h := event_gen M δ sel init x a (fun z => if z = y0 then (1 : ℝ) else 0) lam
    (M.P x a y0 * (Real.exp lam - 1 - lam)) hlam.le hmgf' m hm
    ((Real.exp lam - 1 - lam) / lam * M.P x a y0 + L2 / (lam * m))
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hex : (fun ω => ∃ k : Fin K, nAt M H K δ sel init ω k x a = m ∧
        (Real.exp lam - 1 - lam) / lam * M.P x a y0 + L2 / (lam * m) ≤
          phatAt M H K δ sel init ω k x a y0 - M.P x a y0) =
      (fun ω => ∃ k : Fin K, nAt M H K δ sel init ω k x a = m ∧
        (Real.exp lam - 1 - lam) / lam * M.P x a y0 + L2 / (lam * m) ≤
          ∑ y, (phatAt M H K δ sel init ω k x a y - M.P x a y) *
            (fun z => if z = y0 then (1 : ℝ) else 0) y) := by
    funext ω
    simp [mul_ite, Finset.sum_ite_eq']
  rw [hex]
  refine le_trans h (le_of_eq ?_)
  congr 1
  field_simp
  ring

end Events

section GoodEvents

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

/-- Event A: two-sided Hoeffding for `V*_{h+1}` at every observed pair. -/
def GA (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) : Prop :=
  ∀ (k : Fin K) (h : Fin H) (x : S) (a : A), 0 < nAt M H K δ sel init ω k x a →
    |∑ y, (phatAt M H K δ sel init ω k x a y - M.P x a y) * optimalValue M H (h.val + 1) y| ≤
      H * Real.sqrt (theoremLog (Fintype.card S) (Fintype.card A) H K δ /
        (2 * nAt M H K δ sel init ω k x a))

/-- The logarithm used by Event B. -/
noncomputable def logB (S' A' H K : ℕ) (δ : ℝ) : ℝ :=
  Real.log (5 * (S' : ℝ) * S' * A' * ((K * H : ℕ) : ℝ) / δ)

/-- Event B: Bennett upper tail for every transition entry at every observed pair. -/
def GB (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H) (lam : ℝ)
    (ω : Outcomes S K H) : Prop :=
  ∀ (k : Fin K) (x : S) (a : A) (y : S), 0 < nAt M H K δ sel init ω k x a →
    phatAt M H K δ sel init ω k x a y - M.P x a y <
      (Real.exp lam - 1 - lam) / lam * M.P x a y +
        logB (Fintype.card S) (Fintype.card A) H K δ / (lam * nAt M H K δ sel init ω k x a)

lemma exp_neg_log_div (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    Real.exp (-Real.log (c / δ)) = δ / c := by
  rw [Real.exp_neg, Real.exp_log (div_pos hc hδ)]
  field_simp

lemma probA (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (hH : 0 < H) (hδ : 0 < δ) (hL : 0 ≤ theoremLog (Fintype.card S) (Fintype.card A) H K δ) :
    probEvent M H K δ sel init (fun ω => ¬ GA M δ sel init ω) ≤ 2 * δ / 5 := by
  set L := theoremLog (Fintype.card S) (Fintype.card A) H K δ with hLdef
  let ε : ℕ → ℝ := fun n => H * Real.sqrt (L / (2 * n))
  let E : (Fin H × S × A × Fin (K * H) × Bool) → Outcomes S K H → Prop := fun i ω =>
    ∃ k : Fin K, nAt M H K δ sel init ω k i.2.1 i.2.2.1 = i.2.2.2.1.val + 1 ∧
      ε (i.2.2.2.1.val + 1) ≤ ∑ y, (phatAt M H K δ sel init ω k i.2.1 i.2.2.1 y -
        M.P i.2.1 i.2.2.1 y) * (fun z => if i.2.2.2.2 = true then optimalValue M H (i.1.val + 1) z
          else -optimalValue M H (i.1.val + 1) z) y
  have hsub : ∀ ω, ¬ GA M δ sel init ω → ∃ i, E i ω := by
    intro ω hg
    unfold GA at hg
    simp only [not_forall, not_le] at hg
    obtain ⟨k, h, x, a, hpos, hlt⟩ := hg
    have hnle := nAt_le M δ sel init ω k x a
    have hm : nAt M H K δ sel init ω k x a - 1 < K * H := by omega
    have hn1 : nAt M H K δ sel init ω k x a - 1 + 1 = nAt M H K δ sel init ω k x a := by omega
    rcases lt_abs.mp hlt with h1 | h1
    · refine ⟨(h, x, a, ⟨_, hm⟩, true), k, hn1.symm, ?_⟩
      simp only [ε, hn1, if_true]
      exact le_of_lt h1
    · refine ⟨(h, x, a, ⟨_, hm⟩, false), k, hn1.symm, ?_⟩
      simp only [ε, hn1, Bool.false_eq_true, if_false, mul_neg, Finset.sum_neg_distrib]
      exact le_of_lt h1
  refine le_trans (probEvent_mono M δ sel init _ _ hsub)
    (le_trans (probEvent_exists_le M δ sel init E) ?_)
  have hb : ∀ i, probEvent M H K δ sel init (E i) ≤ Real.exp (-L) := by
    rintro ⟨h, x, a, m, s⟩
    have hm : 0 < m.val + 1 := Nat.succ_pos _
    have hε0 : 0 ≤ ε (m.val + 1) := by
      simp only [ε]; positivity
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    have hexp : 2 * ((m.val + 1 : ℕ) : ℝ) * ε (m.val + 1) ^ 2 / (H : ℝ) ^ 2 = L := by
      simp only [ε]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    have hV : ∀ z, 0 ≤ optimalValue M H (h.val + 1) z ∧ optimalValue M H (h.val + 1) z ≤ H := by
      intro z
      obtain ⟨b0, b1⟩ := opt_bounds M H (h.val + 1) z
      exact ⟨b0, le_trans b1 (by exact_mod_cast Nat.sub_le H (h.val + 1))⟩
    cases s
    · have := eventA_one M δ sel init x a (fun z => -optimalValue M H (h.val + 1) z) (-(H : ℝ)) 0
        (by linarith) (fun z => ⟨by linarith [(hV z).2], by linarith [(hV z).1]⟩)
        (m.val + 1) hm (ε (m.val + 1)) hε0
      refine le_trans (probEvent_mono M δ sel init _ _ ?_) (le_trans this (le_of_eq ?_))
      · rintro ω ⟨k, hk, hev⟩
        exact ⟨k, hk, by simpa using hev⟩
      · congr 1
        rw [← hexp]
        congr 1
        ring
    · have := eventA_one M δ sel init x a (fun z => optimalValue M H (h.val + 1) z) 0 (H : ℝ)
        hHr (fun z => ⟨(hV z).1, (hV z).2⟩) (m.val + 1) hm (ε (m.val + 1)) hε0
      refine le_trans (probEvent_mono M δ sel init _ _ ?_) (le_trans this (le_of_eq ?_))
      · rintro ω ⟨k, hk, hev⟩
        exact ⟨k, hk, by simpa using hev⟩
      · congr 1
        rw [← hexp]
        congr 1
        ring
  calc ∑ i, probEvent M H K δ sel init (E i)
      ≤ ∑ _i : (Fin H × S × A × Fin (K * H) × Bool), Real.exp (-L) :=
        Finset.sum_le_sum (fun i _ => hb i)
    _ = ((H : ℝ) * Fintype.card S * Fintype.card A * ((K * H : ℕ) : ℝ) * 2) * Real.exp (-L) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 2 * δ / 5 := by
        by_cases hKH : K * H = 0
        · rw [hKH]; simp; positivity
        · have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
          have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
          have hHr : (0 : ℝ) < H := by exact_mod_cast hH
          have hK : (0 : ℝ) < ((K * H : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hKH
          have hc : 0 < 5 * (H : ℝ) * Fintype.card S * Fintype.card A * ((K * H : ℕ) : ℝ) := by
            positivity
          rw [hLdef]
          unfold theoremLog
          rw [exp_neg_log_div _ δ hc hδ]
          field_simp
          ring_nf
          exact le_refl _

lemma probB (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (hδ : 0 < δ) (lam : ℝ) (hlam : 0 < lam) :
    probEvent M H K δ sel init (fun ω => ¬ GB M δ sel init lam ω) ≤ δ / 5 := by
  set L2 := logB (Fintype.card S) (Fintype.card A) H K δ with hL2
  let E : (S × A × S × Fin (K * H)) → Outcomes S K H → Prop := fun i ω =>
    ∃ k : Fin K, nAt M H K δ sel init ω k i.1 i.2.1 = i.2.2.2.val + 1 ∧
      (Real.exp lam - 1 - lam) / lam * M.P i.1 i.2.1 i.2.2.1 +
        L2 / (lam * ((i.2.2.2.val + 1 : ℕ) : ℝ)) ≤
        phatAt M H K δ sel init ω k i.1 i.2.1 i.2.2.1 - M.P i.1 i.2.1 i.2.2.1
  have hsub : ∀ ω, ¬ GB M δ sel init lam ω → ∃ i, E i ω := by
    intro ω hg
    unfold GB at hg
    simp only [not_forall, not_lt] at hg
    obtain ⟨k, x, a, y, hpos, hle⟩ := hg
    have hnle := nAt_le M δ sel init ω k x a
    have hm : nAt M H K δ sel init ω k x a - 1 < K * H := by omega
    have hn1 : nAt M H K δ sel init ω k x a - 1 + 1 = nAt M H K δ sel init ω k x a := by omega
    refine ⟨(x, a, y, ⟨_, hm⟩), k, hn1.symm, ?_⟩
    simp only [hn1]
    exact hle
  refine le_trans (probEvent_mono M δ sel init _ _ hsub)
    (le_trans (probEvent_exists_le M δ sel init E) ?_)
  have hb : ∀ i, probEvent M H K δ sel init (E i) ≤ Real.exp (-L2) := by
    rintro ⟨x, a, y, m⟩
    exact eventB_one M δ sel init x a y lam hlam L2 (m.val + 1) (Nat.succ_pos _)
  calc ∑ i, probEvent M H K δ sel init (E i)
      ≤ ∑ _i : (S × A × S × Fin (K * H)), Real.exp (-L2) :=
        Finset.sum_le_sum (fun i _ => hb i)
    _ = ((Fintype.card S : ℝ) * Fintype.card A * Fintype.card S * ((K * H : ℕ) : ℝ)) *
          Real.exp (-L2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring
    _ ≤ δ / 5 := by
        by_cases hKH : K * H = 0
        · rw [hKH]; simp; positivity
        · have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
          have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
          have hK : (0 : ℝ) < ((K * H : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hKH
          have hc : 0 < 5 * (Fintype.card S : ℝ) * Fintype.card S * Fintype.card A *
              ((K * H : ℕ) : ℝ) := by positivity
          rw [hL2]
          unfold logB
          rw [exp_neg_log_div _ δ hc hδ]
          field_simp
          ring_nf
          exact le_refl _

end GoodEvents

section Optimism

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A]

lemma pv_succ (M : MDP S A) (H : ℕ) (π : Policy S A H) (h : ℕ) (hh : h < H) (x : S) :
    policyValue M H π h x = M.R x (π x ⟨h, hh⟩) +
      ∑ y : S, M.P x (π x ⟨h, hh⟩) y * policyValue M H π (h + 1) y := by
  unfold policyValue
  rw [show H - h = (H - (h + 1)) + 1 by omega]
  simp only [policyValueFuel, dif_pos hh]

/-- The optimal Q-function. -/
noncomputable def Qs (M : MDP S A) (H h : ℕ) (x : S) (a : A) : ℝ :=
  M.R x a + ∑ y : S, M.P x a y * optimalValue M H (h + 1) y

lemma opt_le_of (M : MDP S A) (H h : ℕ) (hh : h < H) (x : S) (T : ℝ)
    (hT : ∀ a, Qs M H h x a ≤ T) : optimalValue M H h x ≤ T := by
  unfold optimalValue
  apply Finset.sup'_le
  intro π _
  rw [pv_succ M H π h hh x]
  refine le_trans ?_ (hT (π x ⟨h, hh⟩))
  unfold Qs
  have hP0 := (M.kernel x (π x ⟨h, hh⟩)).1
  have : ∑ y : S, M.P x (π x ⟨h, hh⟩) y * policyValue M H π (h + 1) y ≤
      ∑ y : S, M.P x (π x ⟨h, hh⟩) y * optimalValue M H (h + 1) y := by
    apply Finset.sum_le_sum
    intro y _
    apply mul_le_mul_of_nonneg_left _ (hP0 y)
    unfold optimalValue
    exact Finset.le_sup' (fun π : Policy S A H => policyValue M H π (h + 1) y) (by simp)
  linarith

lemma Qs_le_H (M : MDP S A) (H h : ℕ) (hh : h < H) (x : S) (a : A) :
    Qs M H h x a ≤ H := by
  unfold Qs
  obtain ⟨hP0, hP1⟩ := M.kernel x a
  have hR := M.reward_mem x a
  have h2 : ∑ y : S, M.P x a y * optimalValue M H (h + 1) y ≤
      ∑ y : S, M.P x a y * ((H - (h + 1) : ℕ) : ℝ) :=
    Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (opt_bounds M H (h+1) y).2 (hP0 y))
  rw [← Finset.sum_mul, hP1] at h2
  have h3 : ((H - (h + 1) : ℕ) : ℝ) = (H : ℝ) - h - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [h3] at h2
  have : (0:ℝ) ≤ h := Nat.cast_nonneg h
  linarith [hR.2]

lemma value_ge (Q : ℕ → S → A → ℝ) (h : ℕ) (x : S) (a : A) : Q h x a ≤ valueAt Q h x := by
  unfold valueAt
  exact Finset.le_sup' (fun a : A => Q h x a) (Finset.mem_univ a)

lemma step (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ)
    (hprev : ∀ h, h < H → ∀ x a, Qs M H h x a ≤ prevQ h x a)
    (hconf : ∀ h, h < H → ∀ x a, 0 < countSA hist x a →
      -(bonus (Fintype.card S) (Fintype.card A) H K (countSA hist x a) δ) ≤
        ∑ y : S, (empirical hist x a y - M.P x a y) * optimalValue M H (h + 1) y)
    (h : ℕ) (hh : h < H)
    (hnext : ∀ y, optimalValue M H (h + 1) y ≤ valueAt (qAt M H K δ hist prevQ) (h + 1) y)
    (x : S) (a : A) : Qs M H h x a ≤ qAt M H K δ hist prevQ h x a := by
  have hnext' := hnext
  unfold qAt
  unfold qAt at hnext'
  rw [show H - h = (H - (h + 1)) + 1 by omega]
  simp only [qFuel, if_pos hh]
  split_ifs with hc
  · exact Qs_le_H M H h hh x a
  · have hpos : 0 < countSA hist x a := Nat.pos_of_ne_zero hc
    refine le_min (hprev h hh x a) (le_min (Qs_le_H M H h hh x a) ?_)
    have he0 : ∀ y, 0 ≤ empirical hist x a y := fun y => by
      unfold empirical; positivity
    have h1 : ∑ y : S, empirical hist x a y * optimalValue M H (h + 1) y ≤
        ∑ y : S, empirical hist x a y *
          Finset.univ.sup' Finset.univ_nonempty
            (fun a' : A => qFuel M H K δ hist prevQ (H - (h + 1)) (h + 1) y a') := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hnext' y) (he0 y)
    have h2 := hconf h hh x a hpos
    have h3 : ∑ y : S, (empirical hist x a y - M.P x a y) * optimalValue M H (h + 1) y =
        ∑ y : S, empirical hist x a y * optimalValue M H (h + 1) y -
          ∑ y : S, M.P x a y * optimalValue M H (h + 1) y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _; ring
    unfold Qs
    linarith

lemma inner (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ)
    (hprev : ∀ h, h < H → ∀ x a, Qs M H h x a ≤ prevQ h x a)
    (hconf : ∀ h, h < H → ∀ x a, 0 < countSA hist x a →
      -(bonus (Fintype.card S) (Fintype.card A) H K (countSA hist x a) δ) ≤
        ∑ y : S, (empirical hist x a y - M.P x a y) * optimalValue M H (h + 1) y) :
    ∀ m h, H - h = m → h ≤ H → ∀ y,
      optimalValue M H h y ≤ valueAt (qAt M H K δ hist prevQ) h y := by
  intro m
  induction m with
  | zero =>
    intro h hm hh y
    have hH : h = H := by omega
    subst hH
    have b := (opt_bounds M h h y).2
    simp only [Nat.sub_self, Nat.cast_zero] at b
    refine le_trans b (le_trans ?_ (value_ge _ h y (Classical.arbitrary A)))
    unfold qAt
    simp [Nat.sub_self, qFuel]
  | succ m ih =>
    intro h hm hh y
    have hlt : h < H := by omega
    have hnext := ih (h + 1) (by omega) (by omega)
    apply opt_le_of M H h hlt y
    intro a
    exact le_trans (step M H K δ hist prevQ hprev hconf h hlt hnext y a) (value_ge _ h y a)

lemma inner_Q (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ)
    (hprev : ∀ h, h < H → ∀ x a, Qs M H h x a ≤ prevQ h x a)
    (hconf : ∀ h, h < H → ∀ x a, 0 < countSA hist x a →
      -(bonus (Fintype.card S) (Fintype.card A) H K (countSA hist x a) δ) ≤
        ∑ y : S, (empirical hist x a y - M.P x a y) * optimalValue M H (h + 1) y)
    (h : ℕ) (hh : h < H) (x : S) (a : A) :
    Qs M H h x a ≤ qAt M H K δ hist prevQ h x a :=
  step M H K δ hist prevQ hprev hconf h hh
    (fun y => inner M H K δ hist prevQ hprev hconf (H - (h + 1)) (h + 1) rfl (by omega) y) x a

lemma log_ge_one (H K : ℕ) (hH : 0 < H) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ algorithmLog (Fintype.card S) (Fintype.card A) H K δ := by
  unfold algorithmLog
  have hS : (1:ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA : (1:ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hKH : (1:ℝ) ≤ ((K * H : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hK hH
  have h5 : (5:ℝ) ≤ 5 * (Fintype.card S : ℝ) * (Fintype.card A) * ((K * H : ℕ) : ℝ) := by
    have h1 : (1:ℝ) ≤ (Fintype.card S : ℝ) * (Fintype.card A) := one_le_mul_of_one_le_of_one_le hS hA
    have h2 : (1:ℝ) ≤ (Fintype.card S : ℝ) * (Fintype.card A) * ((K * H : ℕ) : ℝ) :=
      one_le_mul_of_one_le_of_one_le h1 hKH
    have e : 5 * (Fintype.card S : ℝ) * (Fintype.card A) * ((K * H : ℕ) : ℝ) =
        5 * ((Fintype.card S : ℝ) * (Fintype.card A) * ((K * H : ℕ) : ℝ)) := by ring
    rw [e]
    linarith
  have h6 : (5:ℝ) ≤ 5 * (Fintype.card S : ℝ) * (Fintype.card A) * ((K * H : ℕ) : ℝ) / δ := by
    rw [le_div_iff₀ hδ]
    have : 5 * δ ≤ 5 := by linarith
    linarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith


lemma sqrt_le_bonus_aux (L La n : ℝ) (hn : 0 < n) (hLa : 1 ≤ La) (hL : 0 ≤ L) (hLL : L ≤ 2 * La) :
    Real.sqrt (L / (2 * n)) ≤ 7 * La / Real.sqrt n := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have e : L / (2 * n) = (L / 2) / n := by ring
  rw [e, Real.sqrt_div (by positivity), div_le_div_iff_of_pos_right hsn]
  have h1 : Real.sqrt (L / 2) ≤ Real.sqrt La := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt La ≤ La := by
    rw [Real.sqrt_le_left (by linarith)]
    rw [sq]
    exact le_mul_of_one_le_left (by linarith) hLa
  linarith

lemma theoremLog_le (S' A' H K : ℕ) (hS : 1 ≤ S') (hA : 1 ≤ A') (hH : 0 < H) (hK : 0 < K)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    theoremLog S' A' H K δ = Real.log H + algorithmLog S' A' H K δ ∧
      Real.log H ≤ algorithmLog S' A' H K δ := by
  unfold theoremLog algorithmLog
  have hS' : (1 : ℝ) ≤ S' := by exact_mod_cast hS
  have hA' : (1 : ℝ) ≤ A' := by exact_mod_cast hA
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKH : ((K * H : ℕ) : ℝ) = (K : ℝ) * H := by push_cast; ring
  have hpos : 0 < 5 * (S' : ℝ) * A' * ((K * H : ℕ) : ℝ) / δ := by rw [hKH]; positivity
  constructor
  · rw [← Real.log_mul (by positivity) hpos.ne']
    congr 1
    ring
  · apply Real.log_le_log (by positivity)
    rw [hKH, le_div_iff₀ hδ]
    have h1 : (H : ℝ) * δ ≤ H := mul_le_of_le_one_right (by positivity) hδ1
    have h2 : (1 : ℝ) ≤ 5 * S' * A' * K := by
      have a1 : (1 : ℝ) ≤ S' * A' := one_le_mul_of_one_le_of_one_le hS' hA'
      have a2 : (1 : ℝ) ≤ S' * A' * K := one_le_mul_of_one_le_of_one_le a1 hK'
      have e : (5 : ℝ) * S' * A' * K = 5 * (S' * A' * K) := by ring
      rw [e]; linarith
    have h3 : (H : ℝ) ≤ 5 * S' * A' * K * H := le_mul_of_one_le_left (by positivity) h2
    have e : (5 : ℝ) * S' * A' * (K * H) = 5 * S' * A' * K * H := by ring
    rw [e]
    linarith

variable {K H : ℕ}

lemma conf_of_GA (M : MDP S A) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (init : InitialRule S K H) (ω : Outcomes S K H)
    (hG : GA M δ sel init ω) (k : Fin K) :
    ∀ h, h < H → ∀ x a, 0 < countSA (priorHistory M H K δ sel init ω k) x a →
      -(bonus (Fintype.card S) (Fintype.card A) H K
          (countSA (priorHistory M H K δ sel init ω k) x a) δ) ≤
        ∑ y : S, (empirical (priorHistory M H K δ sel init ω k) x a y - M.P x a y) *
          optimalValue M H (h + 1) y := by
  intro h hh x a hpos
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hLa := log_ge_one (S := S) (A := A) H K hH hK δ hδ hδ1
  obtain ⟨hTL, hlogH⟩ := theoremLog_le (Fintype.card S) (Fintype.card A) H K Fintype.card_pos
    Fintype.card_pos hH hK δ hδ hδ1
  have hlog0 : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hev := hG k ⟨h, hh⟩ x a hpos
  have hnr : (0 : ℝ) < (countSA (priorHistory M H K δ sel init ω k) x a : ℝ) := by
    exact_mod_cast hpos
  have haux := sqrt_le_bonus_aux (theoremLog (Fintype.card S) (Fintype.card A) H K δ)
    (algorithmLog (Fintype.card S) (Fintype.card A) H K δ)
    (countSA (priorHistory M H K δ sel init ω k) x a : ℝ) hnr hLa (by rw [hTL]; linarith)
    (by rw [hTL]; linarith)
  have hm := (abs_le.mp hev).1
  have e1 : nAt M H K δ sel init ω k x a = countSA (priorHistory M H K δ sel init ω k) x a := rfl
  rw [e1] at hm
  have hHr : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hb : (H : ℝ) * Real.sqrt (theoremLog (Fintype.card S) (Fintype.card A) H K δ /
      (2 * (countSA (priorHistory M H K δ sel init ω k) x a : ℝ))) ≤
      bonus (Fintype.card S) (Fintype.card A) H K
        (countSA (priorHistory M H K δ sel init ω k) x a) δ := by
    unfold bonus
    calc _ ≤ (H : ℝ) * (7 * algorithmLog (Fintype.card S) (Fintype.card A) H K δ /
          Real.sqrt (countSA (priorHistory M H K δ sel init ω k) x a : ℝ)) :=
          mul_le_mul_of_nonneg_left haux hHr
      _ = _ := by ring
  exact le_trans (neg_le_neg hb) hm

lemma prevQ_bound_GA (M : MDP S A) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (init : InitialRule S K H) (ω : Outcomes S K H)
    (hG : GA M δ sel init ω) :
    ∀ n h, h < H → ∀ x a, Qs M H h x a ≤ (runPrefix M H K δ sel init ω n).prevQ h x a := by
  intro n
  induction n with
  | zero =>
    intro h hh x a
    simp only [runPrefix]
    exact Qs_le_H M H h hh x a
  | succ n ih =>
    intro h hh x a
    by_cases hn : n < K
    · simp only [runPrefix, dif_pos hn]
      exact inner_Q M H K δ _ _ ih
        (conf_of_GA M hH δ hδ hδ1 sel init ω hG ⟨n, hn⟩) h hh x a
    · simp only [runPrefix, dif_neg hn]
      exact ih h hh x a

/-- Optimism on Event A. -/
theorem optimism_GA (M : MDP S A) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (init : InitialRule S K H) (ω : Outcomes S K H)
    (hG : GA M δ sel init ω) (k : Fin K) (h : ℕ) (hh : h ≤ H) (x : S) :
    optimalValue M H h x ≤ estimatedValue M H K δ sel init ω k h x :=
  inner M H K δ (runPrefix M H K δ sel init ω k.val).history
    (runPrefix M H K δ sel init ω k.val).prevQ
    (prevQ_bound_GA M hH δ hδ hδ1 sel init ω hG k.val)
    (conf_of_GA M hH δ hδ hδ1 sel init ω hG k) (H - h) h rfl hh x

end Optimism

section Recursion

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

/-- The recursion factor `γ = 1 + η`. -/
noncomputable def gam (lam : ℝ) : ℝ := 1 + (Real.exp lam - 1 - lam) / lam

/-- Per-visit cost. -/
noncomputable def Xf (S' A' H K : ℕ) (δ lam : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then (H : ℝ) else
    min (H : ℝ) (bonus S' A' H K n δ + H * Real.sqrt (theoremLog S' A' H K δ / (2 * n)) +
      S' * H * logB S' A' H K δ / (lam * n))

lemma eta_nonneg (lam : ℝ) (hlam : 0 < lam) : 0 ≤ (Real.exp lam - 1 - lam) / lam := by
  have := Real.add_one_le_exp lam
  apply div_nonneg _ hlam.le
  linarith

lemma gam_ge_one (lam : ℝ) (hlam : 0 < lam) : 1 ≤ gam lam := by
  unfold gam; linarith [eta_nonneg lam hlam]

lemma logB_nonneg (S' A' H K : ℕ) (hS : 1 ≤ S') (hA : 1 ≤ A') (hKH : 0 < K * H) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ logB S' A' H K δ := by
  unfold logB
  apply Real.log_nonneg
  have hS' : (1 : ℝ) ≤ S' := by exact_mod_cast hS
  have hA' : (1 : ℝ) ≤ A' := by exact_mod_cast hA
  have hK' : (1 : ℝ) ≤ ((K * H : ℕ) : ℝ) := by exact_mod_cast hKH
  rw [le_div_iff₀ hδ]
  have h1 : (1 : ℝ) ≤ S' * S' := one_le_mul_of_one_le_of_one_le hS' hS'
  have h2 : (1 : ℝ) ≤ S' * S' * A' := one_le_mul_of_one_le_of_one_le h1 hA'
  have h3 : (1 : ℝ) ≤ S' * S' * A' * ((K * H : ℕ) : ℝ) := one_le_mul_of_one_le_of_one_le h2 hK'
  have e : 5 * (S' : ℝ) * S' * A' * ((K * H : ℕ) : ℝ) = 5 * (S' * S' * A' * ((K * H : ℕ) : ℝ)) := by
    ring
  rw [e, one_mul]
  linarith

lemma valueAt_sel (Q : ℕ → S → A → ℝ) (sel : (A → ℝ) → A)
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (h : ℕ) (x : S) :
    valueAt Q h x = Q h x (sel (Q h x)) := by
  unfold valueAt
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun a _ => hsel (Q h x) a)
  · exact Finset.le_sup' (fun a => Q h x a) (Finset.mem_univ _)

lemma qAt_le_H (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ) (h : ℕ) (x : S) (a : A) :
    qAt M H K δ hist prevQ h x a ≤ H := by
  unfold qAt
  by_cases hh : h < H
  · rw [show H - h = (H - (h + 1)) + 1 by omega]
    simp only [qFuel, if_pos hh]
    split_ifs
    · exact le_refl _
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · rw [show H - h = 0 by omega]
    simp [qFuel]

lemma valueAt_le_H (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ) (h : ℕ) (x : S) :
    valueAt (qAt M H K δ hist prevQ) h x ≤ H := by
  unfold valueAt
  exact Finset.sup'_le _ _ (fun a _ => qAt_le_H M H K δ hist prevQ h x a)

lemma qAt_le_step (M : MDP S A) (H K : ℕ) (δ : ℝ) (hist : List (S × A × S))
    (prevQ : ℕ → S → A → ℝ) (h : ℕ) (hh : h < H) (x : S) (a : A)
    (hn : countSA hist x a ≠ 0) :
    qAt M H K δ hist prevQ h x a ≤ M.R x a +
      ∑ y, empirical hist x a y * valueAt (qAt M H K δ hist prevQ) (h + 1) y +
        bonus (Fintype.card S) (Fintype.card A) H K (countSA hist x a) δ := by
  have e : valueAt (qAt M H K δ hist prevQ) (h + 1) = fun y => Finset.univ.sup' Finset.univ_nonempty
      (fun a' : A => qFuel M H K δ hist prevQ (H - (h + 1)) (h + 1) y a') := by
    funext y; rfl
  rw [e]
  unfold qAt
  rw [show H - h = (H - (h + 1)) + 1 by omega]
  simp only [qFuel, if_pos hh, if_neg hn]
  exact le_trans (min_le_right _ _) (min_le_right _ _)

lemma gapH_zero (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (y : S) :
    surrogateGap M H K δ sel init ω k H y = 0 := by
  unfold surrogateGap estimatedValue valueAt episodeQ qAt policyValue
  simp [qFuel, policyValueFuel]

lemma pv_le_opt (M : MDP S A) (H : ℕ) (π : Policy S A H) (h : ℕ) (y : S) :
    policyValue M H π h y ≤ optimalValue M H h y := by
  unfold optimalValue
  exact Finset.le_sup' (fun π : Policy S A H => policyValue M H π h y) (by simp)

/-- One step of the surrogate-gap recursion on the good events. -/
theorem gap_step (M : MDP S A) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) (ω : Outcomes S K H) (hA : GA M δ sel init ω)
    (lam : ℝ) (hlam : 0 < lam) (hB : GB M δ sel init lam ω) (k : Fin K) (h : ℕ) (hh : h < H)
    (x : S) :
    surrogateGap M H K δ sel init ω k h x ≤
      Xf (Fintype.card S) (Fintype.card A) H K δ lam
        (nAt M H K δ sel init ω k x (episodePolicy M H K δ sel init ω k x ⟨h, hh⟩)) +
      gam lam * ∑ y, M.P x (episodePolicy M H K δ sel init ω k x ⟨h, hh⟩) y *
        surrogateGap M H K δ sel init ω k (h + 1) y := by
  set a := episodePolicy M H K δ sel init ω k x ⟨h, hh⟩ with ha
  set π := episodePolicy M H K δ sel init ω k with hπ
  set hist := priorHistory M H K δ sel init ω k with hhist
  set Q := episodeQ M H K δ sel init ω k with hQ
  have hQdef : Q = qAt M H K δ hist (runPrefix M H K δ sel init ω k.val).prevQ := rfl
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hV : estimatedValue M H K δ sel init ω k h x = Q h x a := by
    unfold estimatedValue
    rw [valueAt_sel Q sel hsel]
    rfl
  have hpv : policyValue M H π h x = M.R x a + ∑ y, M.P x a y * policyValue M H π (h + 1) y :=
    pv_succ M H π h hh x
  have hopt : ∀ y, optimalValue M H (h + 1) y ≤ estimatedValue M H K δ sel init ω k (h + 1) y :=
    fun y => optimism_GA M hH δ hδ hδ1 sel init ω hA k (h + 1) (by omega) y
  have hpvle : ∀ y, policyValue M H π (h + 1) y ≤ optimalValue M H (h + 1) y :=
    fun y => pv_le_opt M H π (h + 1) y
  have hVH : ∀ y, estimatedValue M H K δ sel init ω k (h + 1) y ≤ H := fun y =>
    valueAt_le_H M H K δ _ _ (h + 1) y
  have hV0 : ∀ y, 0 ≤ optimalValue M H (h + 1) y := fun y => (opt_bounds M H (h + 1) y).1
  have hgap0 : ∀ y, 0 ≤ surrogateGap M H K δ sel init ω k (h + 1) y := by
    intro y; unfold surrogateGap; linarith [hopt y, hpvle y]
  have hP0 := (M.kernel x a).1
  have hPG : 0 ≤ ∑ y, M.P x a y * surrogateGap M H K δ sel init ω k (h + 1) y :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hP0 y) (hgap0 y))
  have hg1 := gam_ge_one lam hlam
  have hpv0 : 0 ≤ policyValue M H π h x := (pvf_bounds M H π (H - h) h x).1
  have hQH : Q h x a ≤ H := by rw [hQdef]; exact qAt_le_H M H K δ _ _ h x a
  have hgapH : surrogateGap M H K δ sel init ω k h x ≤ H := by
    unfold surrogateGap; rw [hV]; linarith
  by_cases hn : nAt M H K δ sel init ω k x a = 0
  · unfold Xf
    rw [if_pos hn]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ gam lam) hPG
    linarith
  · unfold Xf
    rw [if_neg hn]
    have hnpos : 0 < nAt M H K δ sel init ω k x a := Nat.pos_of_ne_zero hn
    have hq : Q h x a ≤ M.R x a + ∑ y, phatAt M H K δ sel init ω k x a y *
        estimatedValue M H K δ sel init ω k (h + 1) y +
        bonus (Fintype.card S) (Fintype.card A) H K (nAt M H K δ sel init ω k x a) δ := by
      rw [hQdef]
      exact qAt_le_step M H K δ _ _ h hh x a hn
    have hA' := hA k ⟨h, hh⟩ x a hnpos
    have hA1 := (abs_le.mp hA').2
    set n := nAt M H K δ sel init ω k x a with hndef
    set η := (Real.exp lam - 1 - lam) / lam with hη
    set L2 := logB (Fintype.card S) (Fintype.card A) H K δ with hL2
    have hη0 : 0 ≤ η := eta_nonneg lam hlam
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hL20 : 0 ≤ L2 := logB_nonneg _ _ _ _ Fintype.card_pos Fintype.card_pos
      (Nat.mul_pos hK hH) δ hδ hδ1
    have hc0 : 0 ≤ L2 / (lam * n) := by positivity
    have hterm2 : ∑ y, (phatAt M H K δ sel init ω k x a y - M.P x a y) *
        (estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y) ≤
        η * ∑ y, M.P x a y * surrogateGap M H K δ sel init ω k (h + 1) y +
          (Fintype.card S : ℝ) * (H * (L2 / (lam * n))) := by
      rw [Finset.mul_sum]
      have hcS : (Fintype.card S : ℝ) * (H * (L2 / (lam * n))) =
          ∑ _y : S, (H : ℝ) * (L2 / (lam * n)) := by simp
      rw [hcS, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro y _
      have hBy := hB k x a y hnpos
      have hD0 : 0 ≤ estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y := by
        linarith [hopt y]
      have hDg : estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y ≤
          surrogateGap M H K δ sel init ω k (h + 1) y := by
        unfold surrogateGap; linarith [hpvle y]
      have hDH : estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y ≤ H := by
        linarith [hVH y, hV0 y]
      have h1 : (phatAt M H K δ sel init ω k x a y - M.P x a y) *
          (estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y) ≤
          (η * M.P x a y + L2 / (lam * n)) *
          (estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y) :=
        mul_le_mul_of_nonneg_right hBy.le hD0
      have h2 : η * M.P x a y *
          (estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y) ≤
          η * (M.P x a y * surrogateGap M H K δ sel init ω k (h + 1) y) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDg (hP0 y)) hη0
      have h3 : L2 / (lam * n) *
          (estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y) ≤
          H * (L2 / (lam * n)) := by
        rw [mul_comm (H : ℝ)]
        exact mul_le_mul_of_nonneg_left hDH hc0
      linear_combination h1 + h2 + h3
    have hdecomp : ∑ y, phatAt M H K δ sel init ω k x a y *
        estimatedValue M H K δ sel init ω k (h + 1) y -
        ∑ y, M.P x a y * policyValue M H π (h + 1) y =
        ∑ y, (phatAt M H K δ sel init ω k x a y - M.P x a y) * optimalValue M H (h + 1) y +
        ∑ y, (phatAt M H K δ sel init ω k x a y - M.P x a y) *
          (estimatedValue M H K δ sel init ω k (h + 1) y - optimalValue M H (h + 1) y) +
        ∑ y, M.P x a y * surrogateGap M H K δ sel init ω k (h + 1) y := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      unfold surrogateGap
      ring
    have hgap : surrogateGap M H K δ sel init ω k h x ≤
        bonus (Fintype.card S) (Fintype.card A) H K n δ +
          H * Real.sqrt (theoremLog (Fintype.card S) (Fintype.card A) H K δ / (2 * n)) +
          Fintype.card S * H * L2 / (lam * n) +
          gam lam * ∑ y, M.P x a y * surrogateGap M H K δ sel init ω k (h + 1) y := by
      have e1 : surrogateGap M H K δ sel init ω k h x =
          Q h x a - policyValue M H π h x := by unfold surrogateGap; rw [hV]
      have e2 : (Fintype.card S : ℝ) * H * L2 / (lam * n) =
          (Fintype.card S : ℝ) * (H * (L2 / (lam * n))) := by ring
      rw [e1, hpv, e2]
      unfold gam
      rw [← hη]
      have e3 : (1 + η) * ∑ y, M.P x a y * surrogateGap M H K δ sel init ω k (h + 1) y =
          η * ∑ y, M.P x a y * surrogateGap M H K δ sel init ω k (h + 1) y +
            ∑ y, M.P x a y * surrogateGap M H K δ sel init ω k (h + 1) y := by ring
      linarith [hdecomp, hterm2, hA1, hq]
    rcases le_total (bonus (Fintype.card S) (Fintype.card A) H K n δ +
          H * Real.sqrt (theoremLog (Fintype.card S) (Fintype.card A) H K δ / (2 * n)) +
          Fintype.card S * H * L2 / (lam * n)) (H : ℝ) with hle | hle
    · rw [min_eq_right hle]
      linarith
    · rw [min_eq_left hle]
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ gam lam) hPG
      linarith

end Recursion

section Unroll

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

/-- Martingale difference along the trajectory. -/
noncomputable def epsT (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  ∑ y, M.P (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) y *
    surrogateGap M H K δ sel init ω k (h.val + 1) y -
  surrogateGap M H K δ sel init ω k (h.val + 1) (ω k h)

/-- The count of the visited pair at step `(k,h)`. -/
noncomputable def nS (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℕ :=
  nAt M H K δ sel init ω k (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h)

theorem gap_unroll (M : MDP S A) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) (ω : Outcomes S K H) (hA : GA M δ sel init ω)
    (lam : ℝ) (hlam : 0 < lam) (hB : GB M δ sel init lam ω) (k : Fin K) :
    surrogateGap M H K δ sel init ω k 0 (stateAt init ω k 0) ≤
      ∑ h : Fin H, (gam lam ^ h.val *
          Xf (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k h) +
        gam lam ^ (h.val + 1) * epsT M δ sel init ω k h) := by
  have hg1 := gam_ge_one lam hlam
  have claim : ∀ m, m ≤ H → surrogateGap M H K δ sel init ω k 0 (stateAt init ω k 0) ≤
      (∑ h ∈ Finset.range m, (if hh : h < H then (gam lam ^ h *
          Xf (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k ⟨h, hh⟩) +
        gam lam ^ (h + 1) * epsT M δ sel init ω k ⟨h, hh⟩) else 0)) +
      gam lam ^ m * surrogateGap M H K δ sel init ω k m (stateAt init ω k m) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hmH : m < H := hm
      have ih' := ih (by omega)
      have hstep := gap_step M hH δ hδ hδ1 sel hsel init ω hA lam hlam hB k m hmH
        (stateAt init ω k m)
      have hs1 : stateAt init ω k (m + 1) = ω k ⟨m, hmH⟩ := by simp [stateAt, hmH]
      have hX : Xf (Fintype.card S) (Fintype.card A) H K δ lam
          (nAt M H K δ sel init ω k (stateAt init ω k m)
            (episodePolicy M H K δ sel init ω k (stateAt init ω k m) ⟨m, hmH⟩)) =
          Xf (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k ⟨m, hmH⟩) := rfl
      have heps : ∑ y, M.P (stateAt init ω k m)
          (episodePolicy M H K δ sel init ω k (stateAt init ω k m) ⟨m, hmH⟩) y *
            surrogateGap M H K δ sel init ω k (m + 1) y =
          epsT M δ sel init ω k ⟨m, hmH⟩ +
            surrogateGap M H K δ sel init ω k (m + 1) (stateAt init ω k (m + 1)) := by
        unfold epsT
        rw [hs1]
        simp only [actionAt]
        ring
      rw [hX, heps] at hstep
      rw [Finset.sum_range_succ, dif_pos hmH]
      have hg0 : 0 ≤ gam lam ^ m := pow_nonneg (by linarith) m
      have h2 := mul_le_mul_of_nonneg_left hstep hg0
      have e : gam lam ^ m * (Xf (Fintype.card S) (Fintype.card A) H K δ lam
            (nS M δ sel init ω k ⟨m, hmH⟩) +
          gam lam * (epsT M δ sel init ω k ⟨m, hmH⟩ +
            surrogateGap M H K δ sel init ω k (m + 1) (stateAt init ω k (m + 1)))) =
          gam lam ^ m * Xf (Fintype.card S) (Fintype.card A) H K δ lam
            (nS M δ sel init ω k ⟨m, hmH⟩) +
          gam lam ^ (m + 1) * epsT M δ sel init ω k ⟨m, hmH⟩ +
          gam lam ^ (m + 1) *
            surrogateGap M H K δ sel init ω k (m + 1) (stateAt init ω k (m + 1)) := by
        ring
      linarith
  have hfin := claim H le_rfl
  rw [gapH_zero, mul_zero, add_zero, Finset.sum_range] at hfin
  refine le_trans hfin (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro h _
  rw [dif_pos h.isLt]

/-- Clipped surrogate gap, in `[0,H]`. -/
noncomputable def clipG (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : ℕ) (y : S) : ℝ :=
  max 0 (min (H : ℝ) (surrogateGap M H K δ sel init ω k h y))

/-- Clipped martingale difference. -/
noncomputable def epsC (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  ∑ y, M.P (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) y *
    clipG M δ sel init ω k (h.val + 1) y -
  clipG M δ sel init ω k (h.val + 1) (ω k h)

lemma gap_bounds (M : MDP S A) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (init : InitialRule S K H) (ω : Outcomes S K H)
    (hA : GA M δ sel init ω) (k : Fin K) (h : ℕ) (hh : h ≤ H) (y : S) :
    0 ≤ surrogateGap M H K δ sel init ω k h y ∧ surrogateGap M H K δ sel init ω k h y ≤ H := by
  have h1 := optimism_GA M hH δ hδ hδ1 sel init ω hA k h hh y
  have h2 := pv_le_opt M H (episodePolicy M H K δ sel init ω k) h y
  have h3 := valueAt_le_H M H K δ (runPrefix M H K δ sel init ω k.val).history
    (runPrefix M H K δ sel init ω k.val).prevQ h y
  have h4 := (pvf_bounds M H (episodePolicy M H K δ sel init ω k) (H - h) h y).1
  unfold surrogateGap estimatedValue
  constructor
  · unfold estimatedValue at h1; linarith
  · unfold policyValue; exact by
      have : valueAt (episodeQ M H K δ sel init ω k) h y ≤ H := h3
      linarith

lemma epsC_eq (M : MDP S A) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (init : InitialRule S K H) (ω : Outcomes S K H)
    (hA : GA M δ sel init ω) (k : Fin K) (h : Fin H) :
    epsC M δ sel init ω k h = epsT M δ sel init ω k h := by
  have hc : ∀ y, clipG M δ sel init ω k (h.val + 1) y =
      surrogateGap M H K δ sel init ω k (h.val + 1) y := by
    intro y
    obtain ⟨b0, b1⟩ := gap_bounds M hH δ hδ hδ1 sel init ω hA k (h.val + 1) h.isLt y
    unfold clipG
    rw [min_eq_right b1, max_eq_right b0]
  unfold epsC epsT
  simp only [hc]

end Unroll

section EventC

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

lemma gap_adapted (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω ω' : Outcomes S K H) (k : Fin K) (hag : Agree (k.val * H) ω ω') (h : ℕ) (y : S) :
    surrogateGap M H K δ sel init ω k h y = surrogateGap M H K δ sel init ω' k h y := by
  unfold surrogateGap estimatedValue episodePolicy
  rw [episodeQ_eq M δ sel init ω ω' k hag]

lemma clipG_adapted (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω ω' : Outcomes S K H) (k : Fin K) (hag : Agree (k.val * H) ω ω') (h : ℕ) (y : S) :
    clipG M δ sel init ω k h y = clipG M δ sel init ω' k h y := by
  unfold clipG
  rw [gap_adapted M δ sel init ω ω' k hag]

lemma clipG_mem (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : ℕ) (y : S) :
    0 ≤ clipG M δ sel init ω k h y ∧ clipG M δ sel init ω k h y ≤ H := by
  unfold clipG
  have : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  constructor
  · exact le_max_left _ _
  · exact max_le this (min_le_left _ _)

/-- Event C: the clipped martingale term is small. -/
def GC (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H) (lam : ℝ)
    (ω : Outcomes S K H) : Prop :=
  ∑ k : Fin K, ∑ h : Fin H, gam lam ^ (h.val + 1) * epsC M δ sel init ω k h ≤
    gam lam ^ H * H * Real.sqrt (K * H * theoremLog (Fintype.card S) (Fintype.card A) H K δ / 2)

lemma probC (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (hH : 0 < H) (hK : 0 < K) (hδ : 0 < δ) (lam : ℝ) (hlam : 0 < lam)
    (hL : 0 < theoremLog (Fintype.card S) (Fintype.card A) H K δ) :
    probEvent M H K δ sel init (fun ω => ¬ GC M δ sel init lam ω) ≤ δ / 5 := by
  set L := theoremLog (Fintype.card S) (Fintype.card A) H K δ with hLdef
  set G := gam lam with hGdef
  have hG1 : 1 ≤ G := gam_ge_one lam hlam
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hGH : 0 < G ^ H * H := by positivity
  set τ0 := G ^ H * H * Real.sqrt (K * H * L / 2) with hτ0
  set V := (K : ℝ) * H * (G ^ H * H) ^ 2 with hV
  have hVpos : 0 < V := by positivity
  set t := 4 * τ0 / V with ht
  have ht0 : 0 ≤ t := by positivity
  let u : Fin K → Fin H → Outcomes S K H → ℝ := fun k h ω =>
    t * (G ^ (h.val + 1) * epsC M δ sel init ω k h) - t ^ 2 * (G ^ (h.val + 1) * H) ^ 2 / 8
  have hu : ∀ k h, Adapted (k.val * H + h.val + 1) (u k h) := by
    intro k h ω ω' hag
    have hag1 : Agree (k.val * H + h.val) ω ω' := hag.mono (Nat.le_succ _)
    have hag0 : Agree (k.val * H) ω ω' := hag.mono (by omega)
    simp only [u, epsC]
    rw [stateAt_eq init ω ω' k h.val hag1, actionAt_eq M δ sel init ω ω' k h hag1,
      hag k h (Nat.lt_succ_self _)]
    simp only [clipG_adapted M δ sel init ω ω' k hag0]
  have hstep : ∀ k h ω,
      ∑ y, qP M H K δ sel init k h ω y * Real.exp (u k h (upd ω k h y)) ≤ 1 := by
    intro k h ω
    have ag := agree_upd ω k h
    have hepsC : ∀ y, epsC M δ sel init (upd ω k h y) k h =
        ∑ z, M.P (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) z *
          clipG M δ sel init ω k (h.val + 1) z - clipG M δ sel init ω k (h.val + 1) y := by
      intro y
      unfold epsC
      rw [← stateAt_eq init ω (upd ω k h y) k h.val (ag y),
        ← actionAt_eq M δ sel init ω (upd ω k h y) k h (ag y), upd_self]
      simp only [← clipG_adapted M δ sel init ω (upd ω k h y) k
        ((ag y).mono (Nat.le_add_right _ _))]
    set x0 := stateAt init ω k h.val
    set a0 := actionAt M H K δ sel init ω k h
    have hq : ∀ y, qP M H K δ sel init k h ω y = M.P x0 a0 y := fun y => rfl
    have hGp : 0 ≤ G ^ (h.val + 1) := pow_nonneg (by linarith) _
    let g : S → ℝ := fun y => -(G ^ (h.val + 1) * clipG M δ sel init ω k (h.val + 1) y)
    have hg : ∀ y, g y ∈ Set.Icc (-(G ^ (h.val + 1) * H)) 0 := by
      intro y
      obtain ⟨c0, c1⟩ := clipG_mem M δ sel init ω k (h.val + 1) y
      constructor
      · simp only [g]
        exact neg_le_neg (mul_le_mul_of_nonneg_left c1 hGp)
      · simp only [g]
        exact neg_nonpos.mpr (mul_nonneg hGp c0)
    have hhf := hoeffding_fin (M.P x0 a0) (M.kernel x0 a0).1 (M.kernel x0 a0).2 g _ _ hg t
    have hPg : ∑ z, M.P x0 a0 z * g z =
        -(G ^ (h.val + 1) * ∑ z, M.P x0 a0 z * clipG M δ sel init ω k (h.val + 1) z) := by
      simp only [g]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro z _
      ring
    have hrel : ∀ y, u k h (upd ω k h y) =
        t * (g y - ∑ z, M.P x0 a0 z * g z) - t ^ 2 * (G ^ (h.val + 1) * H) ^ 2 / 8 := by
      intro y
      simp only [u, hepsC, hPg]
      simp only [g]
      ring
    simp only [hq, hrel]
    calc ∑ y, M.P x0 a0 y * Real.exp (t * (g y - ∑ z, M.P x0 a0 z * g z) -
          t ^ 2 * (G ^ (h.val + 1) * H) ^ 2 / 8)
        = Real.exp (-(t ^ 2 * (G ^ (h.val + 1) * H) ^ 2 / 8)) *
          ∑ y, M.P x0 a0 y * Real.exp (t * (g y - ∑ z, M.P x0 a0 z * g z)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          rw [sub_eq_add_neg (t * (g y - ∑ z, M.P x0 a0 z * g z)), Real.exp_add]
          ring
      _ ≤ Real.exp (-(t ^ 2 * (G ^ (h.val + 1) * H) ^ 2 / 8)) *
          Real.exp (t ^ 2 * (0 - -(G ^ (h.val + 1) * H)) ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hhf (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add]
          rw [show -(t ^ 2 * (G ^ (h.val + 1) * H) ^ 2 / 8) +
            t ^ 2 * (0 - -(G ^ (h.val + 1) * H)) ^ 2 / 8 = 0 by ring]
          exact Real.exp_zero
  have hmain := exp_sum_le M δ sel init u hu hstep
  have hc : 0 < Real.exp L := Real.exp_pos _
  have hmk := probEvent_le_markov M δ sel init (fun ω => ¬ GC M δ sel init lam ω)
    (fun ω => Real.exp (∑ p : Fin K × Fin H, u p.1 p.2 ω)) _ hc
    (fun ω => (Real.exp_pos _).le) (by
      intro ω hω
      apply Real.exp_le_exp.mpr
      unfold GC at hω
      rw [not_le] at hω
      have hsum : ∑ p : Fin K × Fin H, u p.1 p.2 ω =
          t * (∑ k : Fin K, ∑ h : Fin H, G ^ (h.val + 1) * epsC M δ sel init ω k h) -
            t ^ 2 / 8 * ∑ k : Fin K, ∑ h : Fin H, (G ^ (h.val + 1) * H) ^ 2 := by
        rw [Fintype.sum_prod_type]
        simp only [u]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro h _
        ring
      have hvar : ∑ k : Fin K, ∑ h : Fin H, (G ^ (h.val + 1) * H) ^ 2 ≤ V := by
        calc ∑ k : Fin K, ∑ h : Fin H, (G ^ (h.val + 1) * H) ^ 2
            ≤ ∑ _k : Fin K, ∑ _h : Fin H, (G ^ H * H) ^ 2 := by
              apply Finset.sum_le_sum; intro k _
              apply Finset.sum_le_sum; intro h _
              have h1 : G ^ (h.val + 1) ≤ G ^ H := pow_le_pow_right₀ hG1 h.isLt
              have h2 : 0 ≤ G ^ (h.val + 1) * H := by positivity
              have h3 : G ^ (h.val + 1) * H ≤ G ^ H * H :=
                mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg H)
              exact pow_le_pow_left₀ h2 h3 2
          _ = V := by simp [hV]; ring
      rw [hsum]
      have hτsq : τ0 ^ 2 = (G ^ H * H) ^ 2 * (K * H * L / 2) := by
        rw [hτ0, mul_pow, Real.sq_sqrt (by positivity)]
      have hkey : t * τ0 - t ^ 2 / 8 * V = L := by
        rw [ht]
        field_simp
        rw [hτsq, hV]
        field_simp
        ring
      have h1 : t * τ0 ≤ t * (∑ k : Fin K, ∑ h : Fin H, G ^ (h.val + 1) * epsC M δ sel init ω k h) :=
        mul_le_mul_of_nonneg_left hω.le ht0
      have h2 : t ^ 2 / 8 * (∑ k : Fin K, ∑ h : Fin H, (G ^ (h.val + 1) * H) ^ 2) ≤ t ^ 2 / 8 * V :=
        mul_le_mul_of_nonneg_left hvar (by positivity)
      linarith)
  have h1 := le_trans hmk hmain
  have hPle : probEvent M H K δ sel init (fun ω => ¬ GC M δ sel init lam ω) ≤ Real.exp (-L) := by
    rw [Real.exp_neg, ← one_div, le_div_iff₀ hc]
    linarith
  refine le_trans hPle ?_
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hKH : (1 : ℝ) ≤ ((K * H : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hK hH
  have hcpos : 0 < 5 * (H : ℝ) * Fintype.card S * Fintype.card A * ((K * H : ℕ) : ℝ) := by
    positivity
  rw [hLdef]
  unfold theoremLog
  rw [exp_neg_log_div _ δ hcpos hδ]
  rw [div_le_div_iff₀ hcpos (by norm_num)]
  have h2 : (1 : ℝ) ≤ (H : ℝ) * Fintype.card S * Fintype.card A * ((K * H : ℕ) : ℝ) := by
    have := mul_le_mul hH1 hS (by norm_num) (by positivity)
    have := mul_le_mul this hA (by norm_num) (by positivity)
    have := mul_le_mul this hKH (by norm_num) (by positivity)
    simpa using this
  linear_combination (5 : ℝ) * mul_le_mul_of_nonneg_left h2 hδ.le

end EventC

section Pigeon

lemma sqrt_step (m N : ℝ) (hm : 0 ≤ m) (hmN : m ≤ N) (hN : 0 < N) :
    m / Real.sqrt N ≤ (1 + Real.sqrt 2) * (Real.sqrt (N + m) - Real.sqrt N) := by
  have ha : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  set a := Real.sqrt N with hadef
  set b := Real.sqrt (N + m) with hbdef
  have ha2 : a ^ 2 = N := Real.sq_sqrt hN.le
  have hb2 : b ^ 2 = N + m := Real.sq_sqrt (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hb2a : b ≤ Real.sqrt 2 * a := by
    rw [hbdef, hadef, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [div_le_iff₀ ha]
  have h1 : 0 ≤ (b - a) * (Real.sqrt 2 * a - b) := mul_nonneg (by linarith) (by linarith)
  linear_combination h1 - hb2 + ha2

lemma log_step (m N : ℝ) (hm : 0 ≤ m) (hmN : m ≤ N) (hN : 0 < N) :
    m / N ≤ 2 * (Real.log (N + m) - Real.log N) := by
  have hNm : 0 < N + m := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hNm hN)
  rw [Real.log_div hNm.ne' hN.ne', inv_div] at h1
  have h2 : 1 - N / (N + m) = m / (N + m) := by field_simp; ring
  rw [h2] at h1
  have h3 : m / N ≤ 2 * (m / (N + m)) := by
    rw [div_le_iff₀ hN]
    have : m / (N + m) * (N + m) = m := by field_simp
    have h4 := mul_le_mul_of_nonneg_left (show N + m ≤ 2 * N by linarith) (div_nonneg hm hNm.le)
    linear_combination h4 - this
  linarith

/-- Potential bound for one pair's visit sequence. -/
lemma seq_bound (J : ℕ) (N : ℕ → ℝ) (H α β : ℝ) (F : ℕ → ℝ) (hH : 0 < H) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hN0 : N 0 = 0) (hmono : ∀ k, k < J → N k ≤ N (k + 1))
    (hstep : ∀ k, k < J → N (k + 1) - N k ≤ H)
    (hfH : ∀ k, k < J → F k ≤ H) (hf0 : ∀ k, k < J → 0 ≤ F k)
    (hf : ∀ k, k < J → H ≤ N k → F k ≤ α / Real.sqrt (N k) + β / N k) :
    ∀ j, j ≤ J → ∑ k ∈ Finset.range j, (N (k + 1) - N k) * F k ≤
      H * min (N j) (2 * H) + (1 + Real.sqrt 2) * α * Real.sqrt (N j) +
        2 * β * (Real.log (max (N j) H) - Real.log H) := by
  have hN : ∀ k, k ≤ J → 0 ≤ N k := by
    intro k
    induction k with
    | zero => intro _; rw [hN0]
    | succ k ih => intro hk; linarith [hmono k (by omega), ih (by omega)]
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, hN0, Real.sqrt_zero, mul_zero, add_zero]
    rw [max_eq_right hH.le, sub_self, mul_zero, add_zero]
    rw [min_eq_left (by linarith)]
    simp
  | succ j ih' =>
    intro hjJ
    have hj : j < J := hjJ
    have ih := ih' (by omega)
    rw [Finset.sum_range_succ]
    have hm0 : 0 ≤ N (j + 1) - N j := by linarith [hmono j hj]
    have hmH := hstep j hj
    have hsq : Real.sqrt (N j) ≤ Real.sqrt (N (j + 1)) := Real.sqrt_le_sqrt (hmono j hj)
    have hs2 : 0 ≤ 1 + Real.sqrt 2 := by positivity
    have hmax : Real.log (max (N j) H) ≤ Real.log (max (N (j + 1)) H) :=
      Real.log_le_log (lt_max_of_lt_right hH) (max_le_max (hmono j hj) le_rfl)
    by_cases hlt : N j < H
    · have hmin1 : min (N j) (2 * H) = N j := min_eq_left (by linarith)
      have hmin2 : min (N (j + 1)) (2 * H) = N (j + 1) := min_eq_left (by linarith)
      rw [hmin1] at ih
      rw [hmin2]
      have hterm : (N (j + 1) - N j) * F j ≤ (N (j + 1) - N j) * H :=
        mul_le_mul_of_nonneg_left (hfH j hj) hm0
      have e1 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hs2 hα)
      have e2 := mul_le_mul_of_nonneg_left (sub_le_sub_right hmax (Real.log H))
        (by positivity : (0 : ℝ) ≤ 2 * β)
      have e3 : (N (j + 1) - N j) * H = H * N (j + 1) - H * N j := by ring
      linarith
    · have hge : H ≤ N j := not_lt.mp hlt
      have hNpos : 0 < N j := lt_of_lt_of_le hH hge
      have hmN : N (j + 1) - N j ≤ N j := le_trans hmH hge
      have hterm : (N (j + 1) - N j) * F j ≤
          (N (j + 1) - N j) * (α / Real.sqrt (N j) + β / N j) :=
        mul_le_mul_of_nonneg_left (hf j hj hge) hm0
      have hs := sqrt_step (N (j + 1) - N j) (N j) hm0 hmN hNpos
      have hl := log_step (N (j + 1) - N j) (N j) hm0 hmN hNpos
      rw [show N j + (N (j + 1) - N j) = N (j + 1) by ring] at hs hl
      have hmax1 : max (N j) H = N j := max_eq_left hge
      have hmax2 : max (N (j + 1)) H = N (j + 1) := max_eq_left (le_trans hge (hmono j hj))
      rw [hmax1] at ih
      rw [hmax2]
      have hmin : min (N j) (2 * H) ≤ min (N (j + 1)) (2 * H) := min_le_min (hmono j hj) le_rfl
      have e0 : (N (j + 1) - N j) * (α / Real.sqrt (N j) + β / N j) =
          α * ((N (j + 1) - N j) / Real.sqrt (N j)) + β * ((N (j + 1) - N j) / N j) := by ring
      have e1 := mul_le_mul_of_nonneg_left hs hα
      have e2 := mul_le_mul_of_nonneg_left hl hβ
      have e3 := mul_le_mul_of_nonneg_left hmin hH.le
      have e4 : α * ((1 + Real.sqrt 2) * (Real.sqrt (N (j + 1)) - Real.sqrt (N j))) =
          (1 + Real.sqrt 2) * α * Real.sqrt (N (j + 1)) - (1 + Real.sqrt 2) * α * Real.sqrt (N j) := by
        ring
      have e5 : β * (2 * (Real.log (N (j + 1)) - Real.log (N j))) =
          2 * β * (Real.log (N (j + 1)) - Real.log H) - 2 * β * (Real.log (N j) - Real.log H) := by
        ring
      linarith

lemma sum_sqrt_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, Real.sqrt (a i) ≤ Real.sqrt (s.card * ∑ i ∈ s, a i) := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => Real.sqrt (a i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have e : ∑ i ∈ s, Real.sqrt (a i) ^ 2 = ∑ i ∈ s, a i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (ha i hi))
  rw [e] at h
  exact h

end Pigeon

section PigeonProc

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

lemma cnt_episode (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (ω : Outcomes S K H) (j : ℕ) (hj : j < K) :
    cnt M δ sel init x a ((j + 1) * H) ω = cnt M δ sel init x a (j * H) ω +
      ∑ h : Fin H, (if visit M δ sel init x a ⟨j, hj⟩ h ω then (1 : ℝ) else 0) := by
  unfold cnt
  rw [vsum_ite, vsum_ite, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hsplit : ∀ (k : Fin K) (h : Fin H),
      (if k.val * H + h.val < (j + 1) * H then
        (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) else 0) =
      (if k.val * H + h.val < j * H then
        (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) else 0) +
      (if k = ⟨j, hj⟩ then (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) else 0) := by
    intro k h
    have e1 := tau_lt_iff (H := H) k.val (j + 1) h.val h.isLt
    have e2 := tau_lt_iff (H := H) k.val j h.val h.isLt
    by_cases h1 : k.val < j
    · have hne : k ≠ ⟨j, hj⟩ := fun e => by rw [e] at h1; exact lt_irrefl _ h1
      rw [if_pos (e1.mpr (by omega)), if_pos (e2.mpr h1), if_neg hne, add_zero]
    · by_cases h2 : k = ⟨j, hj⟩
      · subst h2
        rw [if_pos (e1.mpr (by simp)), if_neg (fun hh => h1 (e2.mp hh)), if_pos rfl, zero_add]
      · have h3 : ¬ k.val < j + 1 := fun hh => h2 (Fin.ext (by simp only; omega))
        rw [if_neg (fun hh => h3 (e1.mp hh)), if_neg (fun hh => h1 (e2.mp hh)), if_neg h2,
          add_zero]
  simp only [hsplit, Finset.sum_add_distrib]
  congr 1
  have hcol : ∀ k : Fin K, (∑ h : Fin H, if k = ⟨j, hj⟩ then
      (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) else 0) =
      if k = ⟨j, hj⟩ then ∑ h : Fin H,
        (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) else 0 := by
    intro k; split_ifs <;> simp
  simp only [hcol, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma visit_single (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (k : Fin K) (h : Fin H) (G : S → A → ℝ) :
    ∑ x : S, ∑ a : A, (if visit M δ sel init x a k h ω then G x a else 0) =
      G (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) := by
  rw [← Fintype.sum_prod_type' (f := fun x a => if visit M δ sel init x a k h ω then G x a else 0)]
  rw [Finset.sum_eq_single (stateAt init ω k h.val, actionAt M H K δ sel init ω k h)]
  · have : visit M δ sel init (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) k h ω :=
      ⟨rfl, rfl⟩
    simp only [this, if_true]
  · intro p _ hne
    rw [if_neg]
    intro hv
    apply hne
    obtain ⟨h1, h2⟩ := hv
    exact Prod.ext h1.symm h2.symm
  · intro hn; exact absurd (Finset.mem_univ _) hn

lemma regroup (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (F : Fin K → S → A → ℝ) :
    ∑ k : Fin K, ∑ h : Fin H, F k (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h) =
      ∑ x : S, ∑ a : A, ∑ k : Fin K, F k x a *
        ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) := by
  calc ∑ k : Fin K, ∑ h : Fin H, F k (stateAt init ω k h.val) (actionAt M H K δ sel init ω k h)
      = ∑ k : Fin K, ∑ h : Fin H, ∑ x : S, ∑ a : A,
          (if visit M δ sel init x a k h ω then F k x a else 0) := by
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro h _
        rw [visit_single M δ sel init ω k h (F k)]
    _ = ∑ k : Fin K, ∑ x : S, ∑ h : Fin H, ∑ a : A,
          (if visit M δ sel init x a k h ω then F k x a else 0) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ k : Fin K, ∑ x : S, ∑ a : A, ∑ h : Fin H,
          (if visit M δ sel init x a k h ω then F k x a else 0) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun x _ => Finset.sum_comm))
    _ = ∑ x : S, ∑ k : Fin K, ∑ a : A, ∑ h : Fin H,
          (if visit M δ sel init x a k h ω then F k x a else 0) := Finset.sum_comm
    _ = ∑ x : S, ∑ a : A, ∑ k : Fin K, ∑ h : Fin H,
          (if visit M δ sel init x a k h ω then F k x a else 0) :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = _ := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro h _
        split_ifs <;> ring

lemma pair_total (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) :
    ∑ x : S, ∑ a : A, cnt M δ sel init x a (K * H) ω = (K : ℝ) * H := by
  have hτ : ∀ p : Fin K × Fin H, p.1.val * H + p.2.val < K * H := by
    intro p
    have h1 : p.1.val + 1 ≤ K := p.1.isLt
    have h2 := Nat.mul_le_mul_right H h1
    have h3 := p.2.isLt
    rw [add_one_mul] at h2
    omega
  have e : ∀ x a, cnt M δ sel init x a (K * H) ω =
      ∑ k : Fin K, ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) := by
    intro x a
    unfold cnt
    rw [vsum_ite, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro h _
    rw [if_pos (hτ (k, h))]
  simp only [e]
  have := regroup M δ sel init ω (fun _ _ _ => (1 : ℝ))
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at this
  rw [← this]

end PigeonProc

section PigeonMain

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

lemma Xf_le_H (S' A' H K : ℕ) (δ lam : ℝ) (n : ℕ) : Xf S' A' H K δ lam n ≤ H := by
  unfold Xf
  split_ifs
  · exact le_refl _
  · exact min_le_left _ _

lemma Xf_nonneg (S' A' H K : ℕ) (δ lam : ℝ) (n : ℕ) (hLa : 0 ≤ algorithmLog S' A' H K δ)
    (hL2 : 0 ≤ logB S' A' H K δ) (hlam : 0 < lam) : 0 ≤ Xf S' A' H K δ lam n := by
  unfold Xf
  split_ifs
  · exact Nat.cast_nonneg _
  · apply le_min (Nat.cast_nonneg _)
    unfold bonus
    positivity

lemma Xf_le (S' A' H K : ℕ) (δ lam : ℝ) (n : ℕ) (hn : 0 < n)
    (hL : 0 ≤ theoremLog S' A' H K δ) :
    Xf S' A' H K δ lam n ≤
      (7 * H * algorithmLog S' A' H K δ + H * Real.sqrt (theoremLog S' A' H K δ / 2)) /
          Real.sqrt n + (S' * H * logB S' A' H K δ / lam) / n := by
  unfold Xf
  rw [if_neg (by omega)]
  refine le_trans (min_le_right _ _) (le_of_eq ?_)
  unfold bonus
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  rw [show theoremLog S' A' H K δ / (2 * n) = (theoremLog S' A' H K δ / 2) / n by ring,
    Real.sqrt_div (by positivity)]
  field_simp

lemma cnt_zero (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (x : S) (a : A) (ω : Outcomes S K H) : cnt M δ sel init x a 0 ω = 0 := by
  unfold cnt
  rw [vsum_ite]
  simp

theorem pigeon (M : MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S K H)
    (ω : Outcomes S K H) (hH : 0 < H) (hK : 0 < K) (lam : ℝ) (hlam : 0 < lam)
    (hLa : 0 ≤ algorithmLog (Fintype.card S) (Fintype.card A) H K δ)
    (hL : 0 ≤ theoremLog (Fintype.card S) (Fintype.card A) H K δ)
    (hL2 : 0 ≤ logB (Fintype.card S) (Fintype.card A) H K δ) :
    ∑ k : Fin K, ∑ h : Fin H, Xf (Fintype.card S) (Fintype.card A) H K δ lam
        (nS M δ sel init ω k h) ≤
      2 * (H : ℝ) ^ 2 * (Fintype.card S * Fintype.card A) +
      (1 + Real.sqrt 2) * (7 * H * algorithmLog (Fintype.card S) (Fintype.card A) H K δ +
          H * Real.sqrt (theoremLog (Fintype.card S) (Fintype.card A) H K δ / 2)) *
        Real.sqrt (Fintype.card S * Fintype.card A * (K * H)) +
      2 * (Fintype.card S * H * logB (Fintype.card S) (Fintype.card A) H K δ / lam) *
        (Fintype.card S * Fintype.card A) * Real.log K := by
  set α := 7 * H * algorithmLog (Fintype.card S) (Fintype.card A) H K δ +
    H * Real.sqrt (theoremLog (Fintype.card S) (Fintype.card A) H K δ / 2) with hαdef
  set β := Fintype.card S * H * logB (Fintype.card S) (Fintype.card A) H K δ / lam with hβdef
  have hα : 0 ≤ α := by positivity
  have hβ : 0 ≤ β := by positivity
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold nS
  rw [regroup M δ sel init ω
    (fun k x a => Xf (Fintype.card S) (Fintype.card A) H K δ lam (nAt M H K δ sel init ω k x a))]
  have hpair : ∀ x a, ∑ k : Fin K, Xf (Fintype.card S) (Fintype.card A) H K δ lam
        (nAt M H K δ sel init ω k x a) *
        ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) ≤
      2 * (H : ℝ) ^ 2 + (1 + Real.sqrt 2) * α * Real.sqrt (cnt M δ sel init x a (K * H) ω) +
        2 * β * Real.log K := by
    intro x a
    let N : ℕ → ℝ := fun j => cnt M δ sel init x a (j * H) ω
    let F : ℕ → ℝ := fun j => if hj : j < K then
      Xf (Fintype.card S) (Fintype.card A) H K δ lam (nAt M H K δ sel init ω ⟨j, hj⟩ x a) else 0
    have hNe : ∀ j (hj : j < K), N (j + 1) = N j +
        ∑ h : Fin H, (if visit M δ sel init x a ⟨j, hj⟩ h ω then (1 : ℝ) else 0) :=
      fun j hj => cnt_episode M δ sel init x a ω j hj
    have hsum : ∑ k : Fin K, Xf (Fintype.card S) (Fintype.card A) H K δ lam
          (nAt M H K δ sel init ω k x a) *
          ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range K, (N (j + 1) - N j) * F j := by
      rw [Finset.sum_range (fun j => (N (j + 1) - N j) * F j)]
      apply Finset.sum_congr rfl
      intro k _
      rw [hNe k.val k.isLt]
      simp only [F, dif_pos k.isLt, Fin.eta]
      ring
    have hvis : ∀ j (hj : j < K), 0 ≤ ∑ h : Fin H,
        (if visit M δ sel init x a ⟨j, hj⟩ h ω then (1 : ℝ) else 0) ∧
        ∑ h : Fin H, (if visit M δ sel init x a ⟨j, hj⟩ h ω then (1 : ℝ) else 0) ≤ H := by
      intro j hj
      constructor
      · exact Finset.sum_nonneg (fun h _ => by split_ifs <;> norm_num)
      · calc _ ≤ ∑ _h : Fin H, (1 : ℝ) :=
              Finset.sum_le_sum (fun h _ => by split_ifs <;> norm_num)
          _ = H := by simp
    have hb := seq_bound K N H α β F hHr hα hβ
      (by simp only [N, zero_mul]; exact cnt_zero M δ sel init x a ω)
      (fun k hk => by rw [hNe k hk]; linarith [(hvis k hk).1])
      (fun k hk => by rw [hNe k hk]; linarith [(hvis k hk).2])
      (fun k hk => by simp only [F, dif_pos hk]; exact Xf_le_H _ _ _ _ _ _ _)
      (fun k hk => by simp only [F, dif_pos hk]; exact Xf_nonneg _ _ _ _ _ _ _ hLa hL2 hlam)
      (fun k hk hHN => by
        simp only [F, dif_pos hk]
        have hcast : (nAt M H K δ sel init ω ⟨k, hk⟩ x a : ℝ) = N k :=
          nAt_cast M δ sel init ω ⟨k, hk⟩ x a
        have hpos : 0 < nAt M H K δ sel init ω ⟨k, hk⟩ x a := by
          have : (0 : ℝ) < nAt M H K δ sel init ω ⟨k, hk⟩ x a := by rw [hcast]; linarith
          exact_mod_cast this
        have := Xf_le (Fintype.card S) (Fintype.card A) H K δ lam _ hpos hL
        rw [hcast] at this
        exact this)
      K le_rfl
    rw [hsum]
    refine le_trans hb ?_
    have hmin : (H : ℝ) * min (N K) (2 * H) ≤ 2 * (H : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left (min_le_right (N K) (2 * (H : ℝ))) (Nat.cast_nonneg H)
      linear_combination this
    have hNK : N K ≤ (K : ℝ) * H := cnt_le M δ sel init x a (K * H) ω
    have hmaxle : max (N K) (H : ℝ) ≤ (K : ℝ) * H := max_le hNK (le_mul_of_one_le_left (Nat.cast_nonneg H) hKr)
    have hlog : Real.log (max (N K) (H : ℝ)) - Real.log H ≤ Real.log K := by
      have h1 : Real.log (max (N K) (H : ℝ)) ≤ Real.log ((K : ℝ) * H) :=
        Real.log_le_log (lt_max_of_lt_right hHr) hmaxle
      rw [Real.log_mul (by positivity) hHr.ne'] at h1
      linarith
    have hl2 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * β)
    show H * min (N K) (2 * H) + (1 + Real.sqrt 2) * α * Real.sqrt (N K) +
        2 * β * (Real.log (max (N K) H) - Real.log H) ≤ _
    simp only [N] at hmin hl2 ⊢
    linarith
  calc ∑ x : S, ∑ a : A, ∑ k : Fin K, Xf (Fintype.card S) (Fintype.card A) H K δ lam
          (nAt M H K δ sel init ω k x a) *
          ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0)
      ≤ ∑ x : S, ∑ a : A, (2 * (H : ℝ) ^ 2 +
          (1 + Real.sqrt 2) * α * Real.sqrt (cnt M δ sel init x a (K * H) ω) +
          2 * β * Real.log K) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun a _ => hpair x a))
    _ = 2 * (H : ℝ) ^ 2 * (Fintype.card S * Fintype.card A) +
          (1 + Real.sqrt 2) * α * (∑ x : S, ∑ a : A,
            Real.sqrt (cnt M δ sel init x a (K * H) ω)) +
          2 * β * (Fintype.card S * Fintype.card A) * Real.log K := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring
    _ ≤ _ := by
        have hcs : ∑ x : S, ∑ a : A, Real.sqrt (cnt M δ sel init x a (K * H) ω) ≤
            Real.sqrt (Fintype.card S * Fintype.card A * (K * H)) := by
          rw [← Fintype.sum_prod_type' (f := fun x a => Real.sqrt (cnt M δ sel init x a (K * H) ω))]
          have h := sum_sqrt_le (Finset.univ : Finset (S × A))
            (fun p => cnt M δ sel init p.1 p.2 (K * H) ω)
            (fun p _ => by
              unfold cnt vsum
              exact Finset.sum_nonneg (fun q _ => by split_ifs <;> norm_num))
          have htot : ∑ p : S × A, cnt M δ sel init p.1 p.2 (K * H) ω = (K : ℝ) * H := by
            exact (Fintype.sum_prod_type' (f := fun x a => cnt M δ sel init x a (K * H) ω)).trans
              (pair_total M δ sel init ω)
          rw [htot, Finset.card_univ, Fintype.card_prod] at h
          push_cast at h
          rw [mul_assoc (Fintype.card S : ℝ)] at h ⊢
          exact h
        have := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt 2) * α)
        linarith

end PigeonMain

section Final

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] {K H : ℕ}

/-- Deterministic regret bound on the good events. -/
theorem regret_good (M : MDP S A) (hH : 0 < H) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) (ω : Outcomes S K H) (lam : ℝ) (hlam : 0 < lam)
    (hA : GA M δ sel init ω) (hB : GB M δ sel init lam ω) (hC : GC M δ sel init lam ω)
    (hLa : 0 ≤ algorithmLog (Fintype.card S) (Fintype.card A) H K δ)
    (hL : 0 ≤ theoremLog (Fintype.card S) (Fintype.card A) H K δ)
    (hL2 : 0 ≤ logB (Fintype.card S) (Fintype.card A) H K δ) :
    regret M H K δ sel init ω ≤
      gam lam ^ H * (2 * (H : ℝ) ^ 2 * (Fintype.card S * Fintype.card A) +
      (1 + Real.sqrt 2) * (7 * H * algorithmLog (Fintype.card S) (Fintype.card A) H K δ +
          H * Real.sqrt (theoremLog (Fintype.card S) (Fintype.card A) H K δ / 2)) *
        Real.sqrt (Fintype.card S * Fintype.card A * (K * H)) +
      2 * (Fintype.card S * H * logB (Fintype.card S) (Fintype.card A) H K δ / lam) *
        (Fintype.card S * Fintype.card A) * Real.log K) +
      gam lam ^ H * H * Real.sqrt (K * H * theoremLog (Fintype.card S) (Fintype.card A) H K δ / 2) := by
  have hg1 := gam_ge_one lam hlam
  have h1 : regret M H K δ sel init ω ≤
      ∑ k : Fin K, surrogateGap M H K δ sel init ω k 0 (stateAt init ω k 0) := by
    unfold regret
    apply Finset.sum_le_sum
    intro k _
    have := optimism_GA M hH δ hδ hδ1 sel init ω hA k 0 (Nat.zero_le _) (stateAt init ω k 0)
    unfold surrogateGap
    linarith
  have h2 : ∑ k : Fin K, surrogateGap M H K δ sel init ω k 0 (stateAt init ω k 0) ≤
      ∑ k : Fin K, ∑ h : Fin H, (gam lam ^ h.val *
          Xf (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k h) +
        gam lam ^ (h.val + 1) * epsT M δ sel init ω k h) :=
    Finset.sum_le_sum (fun k _ => gap_unroll M hH δ hδ hδ1 sel hsel init ω hA lam hlam hB k)
  have h3 : ∑ k : Fin K, ∑ h : Fin H, (gam lam ^ h.val *
          Xf (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k h) +
        gam lam ^ (h.val + 1) * epsT M δ sel init ω k h) =
      ∑ k : Fin K, ∑ h : Fin H, gam lam ^ h.val *
          Xf (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k h) +
      ∑ k : Fin K, ∑ h : Fin H, gam lam ^ (h.val + 1) * epsC M δ sel init ω k h := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    rw [epsC_eq M hH δ hδ hδ1 sel init ω hA k h]
  have h4 : ∑ k : Fin K, ∑ h : Fin H, gam lam ^ h.val *
        Xf (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k h) ≤
      gam lam ^ H * ∑ k : Fin K, ∑ h : Fin H,
        Xf (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    have hx := Xf_nonneg (Fintype.card S) (Fintype.card A) H K δ lam (nS M δ sel init ω k h)
      hLa hL2 hlam
    have hp : gam lam ^ h.val ≤ gam lam ^ H := pow_le_pow_right₀ hg1 h.isLt.le
    exact mul_le_mul_of_nonneg_right hp hx
  have h5 := pigeon M δ sel init ω hH hK lam hlam hLa hL hL2
  have h6 := mul_le_mul_of_nonneg_left h5 (pow_nonneg (by linarith : (0 : ℝ) ≤ gam lam) H)
  unfold GC at hC
  linarith

lemma final_numeric (H S A L La L2 lK g r q sH sK sK0 : ℝ) (hH : 1 ≤ H) (hS : 1 ≤ S)
    (hA : 1 ≤ A) (hL : 8 ≤ L) (hLa0 : 0 ≤ La) (hLa : La ≤ L) (hL20 : 0 ≤ L2)
    (hL2 : L2 ≤ 2 * L) (hlK0 : 0 ≤ lK) (hlK : lK ≤ L) (hg0 : 0 ≤ g) (hg : g ≤ 1.035)
    (hr0 : 0 ≤ r) (hr : r ≤ 1.4143) (hq0 : 0 ≤ q) (hq : q ≤ L / 4) (hsH : 0 < sH)
    (hsK : 0 < sK) (hK0 : 0 ≤ sK0) (hKs : sK0 ≤ sK) :
    g * (2 * H ^ 2 * (S * A) + (1 + r) * (7 * H * La + H * q) * (sK * sH) +
        2 * (30 * S * H ^ 2 * L2) * (S * A) * lK) + g * H * (sK0 * sH * q) <
      20 * H * sH * L * sK + 250 * H ^ 2 * S ^ 2 * A * L ^ 2 := by
  have hX : 0 < H * sH * L * sK := by positivity
  have hY : 0 < H ^ 2 * S ^ 2 * A * L ^ 2 := by positivity
  have hB : 7 * H * La + H * q ≤ 7.25 * (H * L) := by
    have b1 : H * La ≤ H * L := mul_le_mul_of_nonneg_left hLa (by linarith)
    have b2 : H * q ≤ H * (L / 4) := mul_le_mul_of_nonneg_left hq (by linarith)
    have e1 : 7 * H * La = 7 * (H * La) := by ring
    have e2 : H * (L / 4) = 0.25 * (H * L) := by ring
    linarith
  have hB0 : 0 ≤ 7 * H * La + H * q := by positivity
  have t1 : (1 + r) * (7 * H * La + H * q) * (sK * sH) ≤ 2.4143 * (7.25 * (H * L)) * (sK * sH) := by
    have : (1 + r) * (7 * H * La + H * q) ≤ 2.4143 * (7.25 * (H * L)) :=
      mul_le_mul (by linarith) hB hB0 (by norm_num)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have tm : H * (sK0 * sH * q) ≤ H * (sK * sH * (L / 4)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hKs hsH.le) hq hq0 (by positivity)
  have t2 : 2 * H ^ 2 * (S * A) ≤ 2 / 64 * (H ^ 2 * S ^ 2 * A * L ^ 2) := by
    have hL2' : 64 ≤ L ^ 2 := by
      have := mul_le_mul hL hL (by norm_num) (by linarith)
      rw [sq]; linarith
    have hSS : S ≤ S ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (by linarith) hS
    have hSA : S * A ≤ S ^ 2 * A := mul_le_mul_of_nonneg_right hSS (by linarith)
    have : H ^ 2 * (S * A) * 64 ≤ H ^ 2 * S ^ 2 * A * L ^ 2 := by
      have h1 : H ^ 2 * (S * A) ≤ H ^ 2 * (S ^ 2 * A) := mul_le_mul_of_nonneg_left hSA (by positivity)
      have h2 : H ^ 2 * (S ^ 2 * A) * 64 ≤ H ^ 2 * (S ^ 2 * A) * L ^ 2 :=
        mul_le_mul_of_nonneg_left hL2' (by positivity)
      have h3 := mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 64)
      have e : H ^ 2 * S ^ 2 * A * L ^ 2 = H ^ 2 * (S ^ 2 * A) * L ^ 2 := by ring
      linarith
    have e : 2 / 64 * (H ^ 2 * S ^ 2 * A * L ^ 2) = (H ^ 2 * S ^ 2 * A * L ^ 2) / 32 := by ring
    have e2 : 2 * H ^ 2 * (S * A) = 2 * (H ^ 2 * (S * A)) := by ring
    linarith
  have t3 : 2 * (30 * S * H ^ 2 * L2) * (S * A) * lK ≤ 120 * (H ^ 2 * S ^ 2 * A * L ^ 2) := by
    have h1 : L2 * lK ≤ 2 * L * L := mul_le_mul hL2 hlK hlK0 (by linarith)
    have e : 2 * (30 * S * H ^ 2 * L2) * (S * A) * lK = 60 * (H ^ 2 * S ^ 2 * A) * (L2 * lK) := by ring
    rw [e]
    have : 60 * (H ^ 2 * S ^ 2 * A) * (L2 * lK) ≤ 60 * (H ^ 2 * S ^ 2 * A) * (2 * L * L) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e2 : 60 * (H ^ 2 * S ^ 2 * A) * (2 * L * L) = 120 * (H ^ 2 * S ^ 2 * A * L ^ 2) := by ring
    linarith
  have hsum : 2 * H ^ 2 * (S * A) + (1 + r) * (7 * H * La + H * q) * (sK * sH) +
      2 * (30 * S * H ^ 2 * L2) * (S * A) * lK ≤
      2.4143 * 7.25 * (H * sH * L * sK) + (2 / 64 + 120) * (H ^ 2 * S ^ 2 * A * L ^ 2) := by
    have e : 2.4143 * (7.25 * (H * L)) * (sK * sH) = 2.4143 * 7.25 * (H * sH * L * sK) := by ring
    linarith
  have hsum0 : 0 ≤ 2 * H ^ 2 * (S * A) + (1 + r) * (7 * H * La + H * q) * (sK * sH) +
      2 * (30 * S * H ^ 2 * L2) * (S * A) * lK := by positivity
  have g1 := mul_le_mul hg hsum hsum0 (by norm_num)
  have g2 : g * H * (sK0 * sH * q) ≤ 1.035 * (H * (sK * sH * (L / 4))) := by
    rw [mul_assoc]
    exact mul_le_mul hg tm (by positivity) (by norm_num)
  have e2 : 1.035 * (H * (sK * sH * (L / 4))) = 1.035 / 4 * (H * sH * L * sK) := by ring
  linarith

end Final

section Solution

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A]

lemma gam_pow_le (H : ℕ) (hH : 0 < H) : gam (1 / (30 * H)) ^ H ≤ 1.035 := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set lam : ℝ := 1 / (30 * H) with hlamdef
  have hlam : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 / 30 := by
    rw [hlamdef]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have habs : |Real.exp lam - 1 - lam| ≤ lam ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_pos hlam]; linarith)
  have hη : (Real.exp lam - 1 - lam) / lam ≤ lam := by
    rw [div_le_iff₀ hlam]
    have := (abs_le.mp habs).2
    linear_combination this
  have hg : gam lam ≤ Real.exp lam := by
    unfold gam
    have := Real.add_one_le_exp lam
    linarith
  have hg0 : 0 ≤ gam lam := by linarith [gam_ge_one lam hlam]
  have h1 : gam lam ^ H ≤ Real.exp lam ^ H := pow_le_pow_left₀ hg0 hg H
  rw [← Real.exp_nat_mul] at h1
  have hHl : (H : ℝ) * lam = 1 / 30 := by
    rw [hlamdef]; field_simp
  rw [hHl] at h1
  have habs2 : |Real.exp (1 / 30) - 1 - 1 / 30| ≤ (1 / 30) ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_pos (by norm_num)]; norm_num)
  have := (abs_le.mp habs2).2
  linarith

lemma L_ge_8 (L K : ℝ) (hK : 1 ≤ K) (hlog : Real.log (5 * K) ≤ L) (hbig : 250 * L ^ 2 < K) :
    8 ≤ L := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hL1 : 1 ≤ L := by
    have h5 : Real.log 5 ≤ Real.log (5 * K) := by
      apply Real.log_le_log (by norm_num)
      linarith
    have : 1 ≤ Real.log 5 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith
    linarith
  have hK250 : 250 < K := by
    have : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    linarith
  have hL7 : 7 ≤ L := by
    have h7 : Real.exp 7 ≤ 5 * K := by
      have : Real.exp 7 = Real.exp 1 ^ 7 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have : Real.exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 := pow_le_pow_left₀ he0.le he.le 7
      have h2 : (2.7182818286 : ℝ) ^ 7 ≤ 1250 := by norm_num
      linarith
    have : 7 ≤ Real.log (5 * K) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact h7
    linarith
  have hKb : 12250 < K := by
    have : (49 : ℝ) ≤ L ^ 2 := by
      have := mul_le_mul hL7 hL7 (by norm_num) (by linarith)
      rw [sq]; linarith
    linarith
  have h8 : Real.exp 8 ≤ 5 * K := by
    have : Real.exp 8 = Real.exp 1 ^ 8 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have : Real.exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 := pow_le_pow_left₀ he0.le he.le 8
    have h2 : (2.7182818286 : ℝ) ^ 8 ≤ 61250 := by norm_num
    linarith
  have : 8 ≤ Real.log (5 * K) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact h8
  linarith

end Solution

set_option maxHeartbeats 1000000 in
theorem main_bound {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) :
    probEvent M H K δ sel init (fun ω =>
      20 * (H : ℝ) * Real.sqrt H *
          theoremLog (Fintype.card S) (Fintype.card A) H K δ *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) +
        250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A *
          (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 <
        regret M H K δ sel init ω) ≤ δ := by
  classical
  by_cases hδ1 : 1 ≤ δ
  · exact le_trans (probEvent_le_one M δ sel init _) hδ1
  have hδ1' : δ ≤ 1 := le_of_lt (not_le.mp hδ1)
  rcases Nat.eq_zero_or_pos K with hK0 | hK
  · subst hK0
    rw [probEvent_false]
    · exact hδ.le
    intro ω hω
    have hr : regret M H 0 δ sel init ω = 0 := by unfold regret; simp
    rw [hr] at hω
    have h0 : (0 : ℝ) ≤ 20 * (H : ℝ) * Real.sqrt H *
          theoremLog (Fintype.card S) (Fintype.card A) H 0 δ *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * ((0 : ℕ) : ℝ)) +
        250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A *
          (theoremLog (Fintype.card S) (Fintype.card A) H 0 δ) ^ 2 := by
      simp only [Nat.cast_zero, mul_zero, Real.sqrt_zero, zero_add]
      positivity
    linarith
  have hLa1 : 1 ≤ (algorithmLog (Fintype.card S) (Fintype.card A) H K δ) := log_ge_one (S := S) (A := A) H K hH hK δ hδ hδ1'
  obtain ⟨hTL, hlogH⟩ := theoremLog_le (Fintype.card S) (Fintype.card A) H K Fintype.card_pos
    Fintype.card_pos hH hK δ hδ hδ1'
  have hlogH0 : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hLaL : (algorithmLog (Fintype.card S) (Fintype.card A) H K δ) ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ) := by rw [hTL]; linarith
  have hL1 : 1 ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ) := le_trans hLa1 hLaL
  have hL0 : 0 ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ) := by linarith
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA1 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hHr : (0 : ℝ) < H := by linarith
  have hKr : (0 : ℝ) < K := by linarith
  have hKH : ((K * H : ℕ) : ℝ) = (K : ℝ) * H := by push_cast; ring
  have hc0 : 0 < 5 * (H : ℝ) * Fintype.card S * Fintype.card A * ((K * H : ℕ) : ℝ) := by
    rw [hKH]; positivity
  by_cases hreg : (K : ℝ) * H ≤ 250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 *
      Fintype.card A * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2
  · rw [probEvent_false]
    · exact hδ.le
    intro ω hω
    have h1 := regret_le M δ sel init ω
    have h2 : 0 ≤ 20 * (H : ℝ) * Real.sqrt H * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) *
        Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) := by positivity
    linarith
  have hbig : 250 * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 < K := by
    have h1 : 250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 <
        (K : ℝ) * H := not_le.mp hreg
    have h2 : 250 * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 * H ≤ 250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 *
        Fintype.card A * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 := by
      have hSA : (1 : ℝ) ≤ (Fintype.card S : ℝ) ^ 2 * Fintype.card A :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ hS1) hA1
      have hHH : (H : ℝ) ≤ (H : ℝ) ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_left (by linarith) hH1
      have hx : (H : ℝ) ≤ (H : ℝ) ^ 2 * ((Fintype.card S : ℝ) ^ 2 * Fintype.card A) :=
        le_trans hHH (le_mul_of_one_le_right (by positivity) hSA)
      have hL2' : 0 ≤ 250 * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 := by positivity
      linear_combination mul_le_mul_of_nonneg_left hx hL2'
    have h3 : 250 * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 * H < K * H := lt_of_le_of_lt h2 h1
    exact lt_of_mul_lt_mul_right h3 hHr.le
  have hlog5K : Real.log (5 * K) ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ) := by
    unfold theoremLog
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ hδ, hKH]
    have h1 : (1 : ℝ) ≤ (H : ℝ) * Fintype.card S * Fintype.card A * H := by
      have := mul_le_mul hH1 hS1 (by norm_num) (by positivity)
      have := mul_le_mul this hA1 (by norm_num) (by positivity)
      have := mul_le_mul this hH1 (by norm_num) (by positivity)
      simpa using this
    have hK0 : (0 : ℝ) ≤ 5 * K := by positivity
    linear_combination mul_le_mul_of_nonneg_left hδ1' hK0 + mul_le_mul_of_nonneg_left h1 hK0
  have hL8 : 8 ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ) := L_ge_8 (theoremLog (Fintype.card S) (Fintype.card A) H K δ) K hK1 hlog5K hbig
  have hL20 : 0 ≤ (logB (Fintype.card S) (Fintype.card A) H K δ) := logB_nonneg _ _ _ _ Fintype.card_pos Fintype.card_pos
    (Nat.mul_pos hK hH) δ hδ hδ1'
  have hL22 : (logB (Fintype.card S) (Fintype.card A) H K δ) ≤ 2 * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) := by
    unfold logB theoremLog
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by rw [hKH]; positivity)
    rw [hKH]
    have hδ2 : δ ^ 2 ≤ δ := by
      rw [sq]; exact mul_le_of_le_one_left hδ.le hδ1'
    try rw [Real.rpow_two]
    rw [div_pow, div_le_div_iff₀ hδ (by positivity)]
    have hpos : 0 < 5 * (Fintype.card S : ℝ) * Fintype.card A * (K * H) := by positivity
    have hx : 5 * (Fintype.card S : ℝ) * Fintype.card S * Fintype.card A * (K * H) ≤
        (5 * (H : ℝ) * Fintype.card S * Fintype.card A * (K * H)) ^ 2 := by
      have hy : (1 : ℝ) ≤ 5 * (H : ℝ) ^ 2 * Fintype.card A * (K * H) := by
        have a1 : (1 : ℝ) ≤ 5 * (H : ℝ) ^ 2 :=
          one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hH1)
        have a2 : (1 : ℝ) ≤ 5 * (H : ℝ) ^ 2 * Fintype.card A := one_le_mul_of_one_le_of_one_le a1 hA1
        have a3 : (1 : ℝ) ≤ (K : ℝ) * H := one_le_mul_of_one_le_of_one_le hK1 hH1
        exact one_le_mul_of_one_le_of_one_le a2 a3
      have e : (5 * (H : ℝ) * Fintype.card S * Fintype.card A * (K * H)) ^ 2 =
          (5 * (Fintype.card S : ℝ) * Fintype.card S * Fintype.card A * (K * H)) *
            (5 * (H : ℝ) ^ 2 * Fintype.card A * (K * H)) := by ring
      rw [e]
      have : 0 ≤ 5 * (Fintype.card S : ℝ) * Fintype.card S * Fintype.card A * (K * H) := by
        positivity
      exact le_mul_of_one_le_right this hy
    have hx0 : 0 ≤ 5 * (Fintype.card S : ℝ) * Fintype.card S * Fintype.card A * (K * H) := by
      positivity
    exact mul_le_mul hx hδ2 (by positivity) (by positivity)
  have hlK : Real.log K ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ) := le_trans (Real.log_le_log hKr (by linarith)) hlog5K
  have hlK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  set lam : ℝ := 1 / (30 * H) with hlamdef
  have hlam : 0 < lam := by positivity
  have hsub : ∀ ω, (20 * (H : ℝ) * Real.sqrt H * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) +
        250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 <
        regret M H K δ sel init ω) →
      (¬ GA M δ sel init ω ∨ (¬ GB M δ sel init lam ω ∨ ¬ GC M δ sel init lam ω)) := by
    intro ω hω
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨hA, hB, hC⟩ := hcon
    have hr := regret_good M hH hK δ hδ hδ1' sel hsel init ω lam hlam hA hB hC
      (by linarith) hL0 hL20
    have hsH : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr hHr
    have hsK : 0 < Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) := by
      apply Real.sqrt_pos.mpr; positivity
    have hKs : Real.sqrt (K : ℝ) ≤ Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) := by
      apply Real.sqrt_le_sqrt
      have : (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A := one_le_mul_of_one_le_of_one_le hS1 hA1
      exact le_mul_of_one_le_left hKr.le this
    have hq : Real.sqrt ((theoremLog (Fintype.card S) (Fintype.card A) H K δ) / 2) ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ) / 4 := by
      rw [Real.sqrt_le_left (by linarith)]
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ)) (by linarith : (0 : ℝ) ≤ (theoremLog (Fintype.card S) (Fintype.card A) H K δ) - 8)
      linear_combination (1 / 16 : ℝ) * this
    have hr2 : Real.sqrt 2 ≤ 1.4143 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hg := gam_pow_le H hH
    have hg0 : 0 ≤ gam lam ^ H := pow_nonneg (by linarith [gam_ge_one lam hlam]) H
    have e1 : Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * (K * H)) =
        Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) * Real.sqrt H := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    have e2 : Real.sqrt ((K : ℝ) * H * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) / 2) = Real.sqrt K * Real.sqrt H * Real.sqrt ((theoremLog (Fintype.card S) (Fintype.card A) H K δ) / 2) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    have e3 : (Fintype.card S : ℝ) * H * (logB (Fintype.card S) (Fintype.card A) H K δ) / lam = 30 * Fintype.card S * (H : ℝ) ^ 2 * (logB (Fintype.card S) (Fintype.card A) H K δ) := by
      rw [hlamdef]
      field_simp
    rw [e1, e2, e3] at hr
    have hnum := final_numeric (H : ℝ) (Fintype.card S) (Fintype.card A) (theoremLog (Fintype.card S) (Fintype.card A) H K δ) (algorithmLog (Fintype.card S) (Fintype.card A) H K δ) (logB (Fintype.card S) (Fintype.card A) H K δ) (Real.log K)
      (gam lam ^ H) (Real.sqrt 2) (Real.sqrt ((theoremLog (Fintype.card S) (Fintype.card A) H K δ) / 2)) (Real.sqrt H)
      (Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K)) (Real.sqrt K)
      hH1 hS1 hA1 hL8 (by linarith) hLaL hL20 hL22 hlK0 hlK hg0 hg (Real.sqrt_nonneg 2) hr2
      (Real.sqrt_nonneg _) hq hsH hsK (Real.sqrt_nonneg _) hKs
    have e4 : gam lam ^ H * H * (Real.sqrt K * Real.sqrt H * Real.sqrt ((theoremLog (Fintype.card S) (Fintype.card A) H K δ) / 2)) =
        gam lam ^ H * H * (Real.sqrt K * Real.sqrt H * Real.sqrt ((theoremLog (Fintype.card S) (Fintype.card A) H K δ) / 2)) := rfl
    have e5 : 20 * (H : ℝ) * Real.sqrt H * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) =
        20 * (H : ℝ) * Real.sqrt H * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) := rfl
    linarith
  calc probEvent M H K δ sel init (fun ω => 20 * (H : ℝ) * Real.sqrt H * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) +
        250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A * (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 <
        regret M H K δ sel init ω)
      ≤ probEvent M H K δ sel init (fun ω => ¬ GA M δ sel init ω ∨
          (¬ GB M δ sel init lam ω ∨ ¬ GC M δ sel init lam ω)) :=
        probEvent_mono M δ sel init _ _ hsub
    _ ≤ probEvent M H K δ sel init (fun ω => ¬ GA M δ sel init ω) +
          probEvent M H K δ sel init (fun ω => ¬ GB M δ sel init lam ω ∨
            ¬ GC M δ sel init lam ω) := probEvent_union M δ sel init _ _
    _ ≤ probEvent M H K δ sel init (fun ω => ¬ GA M δ sel init ω) +
          (probEvent M H K δ sel init (fun ω => ¬ GB M δ sel init lam ω) +
            probEvent M H K δ sel init (fun ω => ¬ GC M δ sel init lam ω)) :=
        add_le_add le_rfl (probEvent_union M δ sel init _ _)
    _ ≤ 2 * δ / 5 + (δ / 5 + δ / 5) :=
        add_le_add (probA M δ sel init hH hδ hL0)
          (add_le_add (probB M δ sel init hδ lam hlam) (probC M δ sel init hH hK hδ lam hlam
            (by linarith)))
    _ ≤ δ := by linarith

end MinimaxRegretRL.Hoeffding.UCBCH

open MinimaxRegretRL.Hoeffding in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
    (M : MDP S A) (H K : ℕ) (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (init : InitialRule S K H) :
    probEvent M H K δ sel init (fun ω =>
      20 * (H : ℝ) * Real.sqrt H *
          theoremLog (Fintype.card S) (Fintype.card A) H K δ *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) +
        250 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A *
          (theoremLog (Fintype.card S) (Fintype.card A) H K δ) ^ 2 <
        regret M H K δ sel init ω) ≤ δ := by
  exact MinimaxRegretRL.Hoeffding.UCBCH.main_bound M H K hH δ hδ sel hsel init
