-- Prove2me | solution 1 for MinimaxRegretRL.Bernstein.ucbvi_bf_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T14:41:33.174696+00:00
-- url     : https://prove2.me/submissions/427e8289-01fe-498d-893e-26c0158412b4

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_Process

set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSectionVars false

open scoped Classical

namespace MinimaxRegretRL.Bernstein.UCBBF

open MinimaxRegretRL.Bernstein

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
def upd (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) : Hoeffding.Outcomes S K H :=
  Function.update ω k (Function.update (ω k) h y)

@[simp] lemma upd_self (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) :
    upd ω k h y k h = y := by simp [upd]

lemma upd_ne (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) (k' : Fin K) (h' : Fin H)
    (hne : ¬ (k' = k ∧ h' = h)) : upd ω k h y k' h' = ω k' h' := by
  unfold upd
  by_cases hk : k' = k
  · subst hk
    have hh : h' ≠ h := fun e => hne ⟨rfl, e⟩
    simp [Function.update_of_ne hh]
  · simp [Function.update_of_ne hk]

lemma upd_upd (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) (y z : S) :
    upd (upd ω k h y) k h z = upd ω k h z := by
  simp [upd]

lemma upd_eq (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) : upd ω k h (ω k h) = ω := by
  simp [upd]

/-- The involution `(ω, y) ↦ (ω[k,h := y], ω k h)`. -/
def updPerm (k : Fin K) (h : Fin H) : Equiv.Perm (Hoeffding.Outcomes S K H × S) :=
  Function.Involutive.toPerm (fun p => (upd p.1 k h p.2, p.1 k h)) (by
    rintro ⟨ω, y⟩
    simp only [upd_upd, upd_eq, upd_self])

lemma sum_upd (F : Hoeffding.Outcomes S K H → ℝ) (k : Fin K) (h : Fin H) :
    ∑ ω, ∑ y, F (upd ω k h y) = (Fintype.card S : ℝ) * ∑ ω, F ω := by
  have h1 : ∑ p : Hoeffding.Outcomes S K H × S, F (upd p.1 k h p.2) =
      ∑ p : Hoeffding.Outcomes S K H × S, F p.1 :=
    Fintype.sum_equiv (updPerm k h) _ _ (fun p => rfl)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h1
  rw [h1]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- `ω` and `ω'` agree on all draws strictly before time `t` (time of `(k,h)` is `kH+h`). -/
def Agree (t : ℕ) (ω ω' : Hoeffding.Outcomes S K H) : Prop :=
  ∀ (k : Fin K) (h : Fin H), k.val * H + h.val < t → ω k h = ω' k h

def Adapted {β : Type*} (t : ℕ) (f : Hoeffding.Outcomes S K H → β) : Prop :=
  ∀ ω ω', Agree t ω ω' → f ω = f ω'

lemma Agree.mono {t t' : ℕ} (hle : t ≤ t') {ω ω' : Hoeffding.Outcomes S K H} (h : Agree t' ω ω') :
    Agree t ω ω' :=
  fun k j hj => h k j (lt_of_lt_of_le hj hle)

lemma agree_upd (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) (y : S) :
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
noncomputable def ppt (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ) (t : ℕ)
    (ω : Hoeffding.Outcomes S K H) : ℝ :=
  ∏ p : Fin K × Fin H,
    if p.1.val * H + p.2.val < t then q p.1 p.2 ω (ω p.1 p.2) else (Fintype.card S : ℝ)⁻¹

lemma ppt_succ [Nonempty S] (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ)
    (k0 : Fin K) (h0 : Fin H) (ω : Hoeffding.Outcomes S K H) :
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

lemma ppt_adapted (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ)
    (hqad : ∀ k h, Adapted (k.val * H + h.val) (q k h)) (t : ℕ) : Adapted t (ppt q t) := by
  intro ω ω' hag
  unfold ppt
  apply Finset.prod_congr rfl
  intro p _
  split_ifs with hlt
  · rw [hqad p.1 p.2 ω ω' (hag.mono hlt.le), hag p.1 p.2 hlt]
  · rfl

lemma ppt_nonneg (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ)
    (hq0 : ∀ k h ω y, 0 ≤ q k h ω y) (t : ℕ) (ω : Hoeffding.Outcomes S K H) : 0 ≤ ppt q t ω := by
  unfold ppt
  apply Finset.prod_nonneg
  intro p _
  split_ifs
  · exact hq0 _ _ _ _
  · positivity

/-- One supermartingale step: summing out the draw at time `kH+h`. -/
lemma ppt_step [Nonempty S] (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ)
    (hq0 : ∀ k h ω y, 0 ≤ q k h ω y)
    (hqad : ∀ k h, Adapted (k.val * H + h.val) (q k h))
    (k0 : Fin K) (h0 : Fin H) (Z Z' : Hoeffding.Outcomes S K H → ℝ)
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
theorem ppt_chain [Nonempty S] (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ)
    (hq0 : ∀ k h ω y, 0 ≤ q k h ω y)
    (hqad : ∀ k h, Adapted (k.val * H + h.val) (q k h))
    (Z : ℕ → Hoeffding.Outcomes S K H → ℝ)
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

lemma sum_ppt_zero [Nonempty S] (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ) :
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

lemma ppt_full (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ) (ω : Hoeffding.Outcomes S K H) :
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
theorem expect_le [Nonempty S] (q : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ)
    (hq0 : ∀ k h ω y, 0 ≤ q k h ω y)
    (hqad : ∀ k h, Adapted (k.val * H + h.val) (q k h))
    (Z : ℕ → Hoeffding.Outcomes S K H → ℝ) (c : ℝ) (hZ0 : ∀ ω, Z 0 ω = c)
    (hstep : ∀ (k : Fin K) (h : Fin H) ω,
      ∑ y, q k h ω y * Z (k.val * H + h.val + 1) (upd ω k h y) ≤ Z (k.val * H + h.val) ω) :
    ∑ ω, (∏ k : Fin K, ∏ h : Fin H, q k h ω (ω k h)) * Z (K * H) ω ≤ c := by
  have := ppt_chain q hq0 hqad Z hstep (K * H) le_rfl
  simp only [ppt_full, hZ0] at this
  rw [← Finset.sum_mul, sum_ppt_zero, one_mul] at this
  exact this

end Frame

section Process

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma take_ofFn_eq (ω ω' : Hoeffding.Outcomes S K H) (k : Fin K)
    (hag : Agree (k.val * H) ω ω') :
    (List.ofFn ω).take k.val = (List.ofFn ω').take k.val := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    funext j
    apply hag
    have hi : i < k.val := by simp at h1; omega
    have h3 := Nat.mul_le_mul_right H (show i + 1 ≤ k.val by omega)
    have h4 := j.isLt
    rw [add_one_mul] at h3
    simp only
    omega

lemma stateAt_eq (init : InitialRule S H) (ω ω' : Hoeffding.Outcomes S K H) (k : Fin K)
    (h : Fin (H + 1)) (hag : Agree (k.val * H + h.val) ω ω') :
    stateAt init ω k h = stateAt init ω' k h := by
  unfold stateAt
  split_ifs with h0
  · rw [take_ofFn_eq ω ω' k (hag.mono (Nat.le_add_right _ _))]
  · apply hag
    simp only
    omega

lemma runState_eq (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω ω' : Hoeffding.Outcomes S K H) : ∀ n, Agree (n * H) ω ω' →
      runState M δ K H sel init ω n = runState M δ K H sel init ω' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hag
    have hle : n * H ≤ (n + 1) * H := Nat.mul_le_mul_right H (Nat.le_succ n)
    have ih' := ih (hag.mono hle)
    by_cases hn : n < K
    · have e1 : ∀ h : Fin (H + 1), stateAt init ω ⟨n, hn⟩ h = stateAt init ω' ⟨n, hn⟩ h := by
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
      simp only [runState, dif_pos hn, ih']
      unfold advance
      simp only [e1, e2]
    · simp only [runState, dif_neg hn, ih']

lemma policyAt_eq (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω ω' : Hoeffding.Outcomes S K H) (k : Fin K) (hag : Agree (k.val * H) ω ω') :
    policyAt M δ K H sel init ω k = policyAt M δ K H sel init ω' k := by
  unfold policyAt
  rw [runState_eq M δ sel init ω ω' k.val hag]

/-- The action taken at step `(k,h)`. -/
noncomputable def act (M : Hoeffding.MDP S A) (δ : ℝ) (K H : ℕ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) : A :=
  policyAt M δ K H sel init ω k (stateAt init ω k (Fin.castSucc h)) h

lemma act_eq (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω ω' : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H)
    (hag : Agree (k.val * H + h.val) ω ω') :
    act M δ K H sel init ω k h = act M δ K H sel init ω' k h := by
  unfold act
  rw [policyAt_eq M δ sel init ω ω' k (hag.mono (Nat.le_add_right _ _)),
    stateAt_eq init ω ω' k (Fin.castSucc h) (by simpa using hag)]

/-- The kernel factor of the path probability at `(k,h)`. -/
noncomputable def qP (M : Hoeffding.MDP S A) (δ : ℝ) (K H : ℕ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ :=
  fun k h ω y => M.P (stateAt init ω k (Fin.castSucc h)) (act M δ K H sel init ω k h) y

lemma qP_adapted (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H) :
    ∀ k h, Adapted (k.val * H + h.val) (qP M δ K H sel init k h) := by
  intro k h ω ω' hag
  funext y
  simp only [qP]
  rw [stateAt_eq init ω ω' k (Fin.castSucc h) (by simpa using hag),
    act_eq M δ sel init ω ω' k h hag]

lemma qP_nonneg (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H) :
    ∀ k h ω y, 0 ≤ qP M δ K H sel init k h ω y :=
  fun _ _ _ y => (M.kernel _ _).1 y

lemma qP_sum (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H) :
    ∀ k h ω, ∑ y, qP M δ K H sel init k h ω y = 1 :=
  fun _ _ _ => (M.kernel _ _).2

lemma outcomeProb_eq (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) :
    outcomeProb M δ K H sel init ω = ∏ k, ∏ h, qP M δ K H sel init k h ω (ω k h) := rfl

lemma outcomeProb_nonneg (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) :
    0 ≤ outcomeProb M δ K H sel init ω := by
  rw [outcomeProb_eq]
  exact Finset.prod_nonneg (fun k _ => Finset.prod_nonneg
    (fun h _ => qP_nonneg M δ sel init k h ω _))

/-- Supermartingale bound for the UCBVI-BF process. -/
theorem proc_expect_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H)
    (Z : ℕ → Hoeffding.Outcomes S K H → ℝ) (c : ℝ) (hZ0 : ∀ ω, Z 0 ω = c)
    (hstep : ∀ (k : Fin K) (h : Fin H) ω,
      ∑ y, qP M δ K H sel init k h ω y * Z (k.val * H + h.val + 1) (upd ω k h y) ≤
        Z (k.val * H + h.val) ω) :
    ∑ ω, outcomeProb M δ K H sel init ω * Z (K * H) ω ≤ c := by
  simp only [outcomeProb_eq]
  exact expect_le _ (qP_nonneg M δ sel init) (qP_adapted M δ sel init) Z c hZ0 hstep

lemma sum_outcomeProb_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) :
    ∑ ω, outcomeProb M δ K H sel init ω ≤ 1 := by
  have := proc_expect_le (K := K) M δ sel init (fun _ _ => 1) 1 (fun _ => rfl) (by
    intro k h ω
    simp only [mul_one, qP_sum M δ sel init k h ω, le_refl])
  simpa using this

lemma probEvent_le_markov (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H)
    (E : Hoeffding.Outcomes S K H → Prop) (Z : Hoeffding.Outcomes S K H → ℝ) (c : ℝ) (hc : 0 < c)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZE : ∀ ω, E ω → c ≤ Z ω) :
    c * probEvent M δ K H sel init E ≤ ∑ ω, outcomeProb M δ K H sel init ω * Z ω := by
  unfold probEvent
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  have hp := outcomeProb_nonneg M δ sel init ω
  split_ifs with hE
  · rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hZE ω hE) hp
  · simp only [mul_zero]
    exact mul_nonneg hp (hZ0 ω)

lemma probEvent_mono (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (E F : Hoeffding.Outcomes S K H → Prop) (hEF : ∀ ω, E ω → F ω) :
    probEvent M δ K H sel init E ≤ probEvent M δ K H sel init F := by
  unfold probEvent
  apply Finset.sum_le_sum
  intro ω _
  have hp := outcomeProb_nonneg M δ sel init ω
  by_cases hE : E ω
  · simp [hE, hEF ω hE]
  · simp only [hE, if_false]
    split_ifs <;> linarith

lemma probEvent_union (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (E F : Hoeffding.Outcomes S K H → Prop) :
    probEvent M δ K H sel init (fun ω => E ω ∨ F ω) ≤
      probEvent M δ K H sel init E + probEvent M δ K H sel init F := by
  unfold probEvent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have hp := outcomeProb_nonneg M δ sel init ω
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF] <;> linarith

lemma probEvent_le_one (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H)
    (E : Hoeffding.Outcomes S K H → Prop) : probEvent M δ K H sel init E ≤ 1 := by
  refine le_trans ?_ (sum_outcomeProb_le (K := K) M δ sel init)
  unfold probEvent
  apply Finset.sum_le_sum
  intro ω _
  have hp := outcomeProb_nonneg M δ sel init ω
  split_ifs <;> linarith

lemma probEvent_false (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H)
    (E : Hoeffding.Outcomes S K H → Prop) (hE : ∀ ω, ¬ E ω) :
    probEvent M δ K H sel init E = 0 := by
  unfold probEvent
  apply Finset.sum_eq_zero
  intro ω _
  simp [hE ω]

/-! Value bounds. -/

lemma valueAt_bounds (M : Hoeffding.MDP S A) {H : ℕ} (π : Hoeffding.Policy S A H) :
    ∀ (d h : ℕ), H - h = d → ∀ x : S,
      0 ≤ valueAt M π h x ∧ valueAt M π h x ≤ ((H - h : ℕ) : ℝ) := by
  intro d
  induction d with
  | zero =>
    intro h hd x
    rw [valueAt, dif_neg (by omega)]
    simp
  | succ d ih =>
    intro h hd x
    have hh : h < H := by omega
    rw [valueAt, dif_pos hh]
    have ih' := ih (h + 1) (by omega)
    obtain ⟨hP0, hP1⟩ := M.kernel x (π x ⟨h, hh⟩)
    have hR := M.reward_mem x (π x ⟨h, hh⟩)
    have hcast : ((H - h : ℕ) : ℝ) = ((H - (h + 1) : ℕ) : ℝ) + 1 := by
      rw [show H - h = H - (h + 1) + 1 by omega]; push_cast; ring
    constructor
    · have : 0 ≤ ∑ y : S, M.P x (π x ⟨h, hh⟩) y * valueAt M π (h + 1) y :=
        Finset.sum_nonneg (fun y _ => mul_nonneg (hP0 y) (ih' y).1)
      simp only
      linarith [hR.1]
    · have h2 : ∑ y : S, M.P x (π x ⟨h, hh⟩) y * valueAt M π (h + 1) y ≤
          ∑ y : S, M.P x (π x ⟨h, hh⟩) y * ((H - (h + 1) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih' y).2 (hP0 y))
      rw [← Finset.sum_mul, hP1] at h2
      simp only
      rw [hcast]
      linarith [hR.2]

lemma valueAt_nonneg (M : Hoeffding.MDP S A) {H : ℕ} (π : Hoeffding.Policy S A H) (h : ℕ)
    (x : S) : 0 ≤ valueAt M π h x := (valueAt_bounds M π _ h rfl x).1

lemma valueAt_le (M : Hoeffding.MDP S A) {H : ℕ} (π : Hoeffding.Policy S A H) (h : ℕ)
    (x : S) : valueAt M π h x ≤ ((H - h : ℕ) : ℝ) := (valueAt_bounds M π _ h rfl x).2

lemma policy_bdd (M : Hoeffding.MDP S A) (H h : ℕ) (x : S) :
    BddAbove (Set.range fun π : Hoeffding.Policy S A H => valueAt M π h x) :=
  (Set.finite_range _).bddAbove

lemma valueAt_le_opt (M : Hoeffding.MDP S A) {H : ℕ} (π : Hoeffding.Policy S A H) (h : ℕ)
    (x : S) : valueAt M π h x ≤ optimalValue M H h x :=
  le_ciSup (policy_bdd M H h x) π

lemma opt_nonneg (M : Hoeffding.MDP S A) (H h : ℕ) (x : S) : 0 ≤ optimalValue M H h x :=
  le_trans (valueAt_nonneg M (fun _ _ => Classical.arbitrary A) h x)
    (valueAt_le_opt M _ h x)

lemma opt_le (M : Hoeffding.MDP S A) (H h : ℕ) (x : S) :
    optimalValue M H h x ≤ ((H - h : ℕ) : ℝ) :=
  ciSup_le (fun π => valueAt_le M π h x)

lemma regret_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) : regret M δ K H sel init ω ≤ (K : ℝ) * H := by
  unfold regret
  have : ∀ k : Fin K, optimalValue M H 0 (stateAt init ω k ⟨0, by omega⟩) -
      valueAt M (policyAt M δ K H sel init ω k) 0 (stateAt init ω k ⟨0, by omega⟩) ≤ (H : ℝ) := by
    intro k
    have h1 := opt_le M H 0 (stateAt init ω k ⟨0, by omega⟩)
    have h2 := valueAt_nonneg M (policyAt M δ K H sel init ω k) 0 (stateAt init ω k ⟨0, by omega⟩)
    simp only [Nat.sub_zero] at h1
    linarith
  calc _ ≤ ∑ _k : Fin K, (H : ℝ) := Finset.sum_le_sum (fun k _ => this k)
    _ = (K : ℝ) * H := by simp

end Process

section Algebra

set_option maxHeartbeats 1000000 in
/-- Normalised optimism inequality (horizon scaled to 1). `a = √(2ℓ/n)`, `D = (P - P̂) V*`,
`s` = true std of `V*`, `m` = empirical std of `V*`, `sk`, `sd` = empirical stds of `V_k` and
of `Δ = V_k - V*`, `u = P̂ Δ`, `β = √(8 L_a / n)` (so `β² ≥ 8/3 a²` when `ℓ ≤ 3/2 L_a`). -/
lemma opt_alg (a D s m sk sd u β : ℝ) (ha : 0 ≤ a) (hD1 : D ≤ a / 2)
    (hD2 : D ≤ a * s + a ^ 2 / 6) (hm0 : 0 ≤ m) (hm : s ^ 2 - a * s - D ^ 2 ≤ m ^ 2)
    (hmk : m ≤ sk + sd) (hsk : 0 ≤ sk) (hsd : 0 ≤ sd) (hu : sd ^ 2 ≤ u) (hβ0 : 0 ≤ β)
    (hβ : 8 / 3 * a ^ 2 ≤ β ^ 2) : D ≤ u + β * sk + 14 / 9 * a ^ 2 := by
  have hu0 : 0 ≤ u := le_trans (sq_nonneg _) hu
  by_cases hcase : D ≤ 14 / 9 * a ^ 2
  · linarith only [mul_nonneg hβ0 hsk, hcase, hu0]
  push_neg at hcase
  have ha_pos : 0 < a := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · subst h; linarith
  have ha2 : a < 9 / 28 := by
    by_contra hc
    push_neg at hc
    linarith only [mul_le_mul_of_nonneg_left hc ha, hD1, hcase]
  set b := Real.sqrt (8 / 3) * a with hb
  have hb0 : 0 ≤ b := by positivity
  have hbsq : b ^ 2 = 8 / 3 * a ^ 2 := by
    rw [hb, mul_pow, Real.sq_sqrt (by norm_num)]
  have hbβ : b ≤ β := by
    by_contra hcon
    push_neg at hcon
    linarith only [mul_lt_mul'' hcon hcon hβ0 hβ0, hbsq, hβ]
  have hR : b * m - b ^ 2 / 4 ≤ u + β * sk := by
    by_cases hsdm : m ≤ sd
    · linarith only [sq_nonneg (m - b / 2), mul_nonneg hβ0 hsk, mul_le_mul hsdm hsdm hm0 hsd, hu]
    · push_neg at hsdm
      have h1 : m - sd ≤ sk := by linarith only [hmk]
      have h2 : b * (m - sd) ≤ β * sk := mul_le_mul hbβ h1 (by linarith only [hsdm]) hβ0
      linarith only [sq_nonneg (sd - b / 2), h2, hu]
  have hX : 0 ≤ D - 14 / 9 * a ^ 2 := by linarith only [hcase]
  have hq : a ^ 2 / 2 ≤ D - a ^ 2 / 6 := by linarith only [hcase, sq_nonneg a]
  have hp : D - a ^ 2 / 6 ≤ a * s := by linarith only [hD2]
  have hmono : (D - a ^ 2 / 6) ^ 2 - a ^ 2 * (D - a ^ 2 / 6) ≤
      (a * s) ^ 2 - a ^ 2 * (a * s) := by
    linarith only [mul_nonneg (sub_nonneg.2 hp)
      (by linarith only [hq, hp] : (0:ℝ) ≤ a * s + (D - a ^ 2 / 6) - a ^ 2)]
  have hm2 : a ^ 2 * (s ^ 2 - a * s - D ^ 2) ≤ a ^ 2 * m ^ 2 :=
    mul_le_mul_of_nonneg_left hm (sq_nonneg a)
  have hD0 : 0 ≤ D := by linarith only [hcase, sq_nonneg a]
  have e1 : 8 / 3 * a ^ 2 * D ^ 2 ≤ 4 / 3 * a ^ 3 * D := by
    linarith only [mul_nonneg (mul_nonneg (sq_nonneg a) hD0) (by linarith only [hD1] : (0:ℝ) ≤ a / 2 - D)]
  have e2 : 0 ≤ 5 / 3 * D ^ 2 - 16 / 9 * a ^ 2 * D - 22 / 81 * a ^ 4 - 4 / 3 * a ^ 3 * D := by
    linarith only [mul_nonneg hX hX,
      mul_nonneg (mul_nonneg (sq_nonneg a) hX) (by linarith only [ha2] : (0:ℝ) ≤ 9 / 28 - a),
      mul_nonneg (pow_nonneg ha 4) (by linarith only [ha2] : (0:ℝ) ≤ 9 / 28 - a),
      mul_nonneg (sq_nonneg a) hX, pow_nonneg ha 4]
  have hsq : (D - 8 / 9 * a ^ 2) ^ 2 ≤ (b * m) ^ 2 := by
    rw [mul_pow, hbsq]
    linear_combination (8 / 3) * hm2 + (8 / 3) * hmono + e1 + e2
  have hpos : 0 ≤ D - 8 / 9 * a ^ 2 := by linarith only [hcase, sq_nonneg a]
  have hbm : D - 8 / 9 * a ^ 2 ≤ b * m := by
    by_contra hcon
    push_neg at hcon
    linarith only [mul_lt_mul'' hcon hcon (mul_nonneg hb0 hm0) (mul_nonneg hb0 hm0), hsq]
  linarith only [hR, hbm, hbsq]

end Algebra

section MGF

lemma exp_le_quad_neg (y : ℝ) (hy : y ≤ 0) : Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  set t := -y with ht
  have ht0 : 0 ≤ t := by linarith
  have h4 : 1 + t + t ^ 2 / 2 + t ^ 3 / 6 ≤ Real.exp t := by
    have := Real.sum_le_exp_of_nonneg ht0 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hy' : y = -t := by linarith
  have hq : 0 ≤ 1 - t + t ^ 2 / 2 := by nlinarith [sq_nonneg (t - 1)]
  have key : 1 ≤ (1 - t + t ^ 2 / 2) * Real.exp t := by
    nlinarith [mul_le_mul_of_nonneg_left h4 hq, pow_nonneg ht0 3, pow_nonneg ht0 4,
      pow_nonneg ht0 5]
  rw [hy']
  calc Real.exp (-t) = Real.exp (-t) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-t) * ((1 - t + t ^ 2 / 2) * Real.exp t) :=
        mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
    _ = (1 - t + t ^ 2 / 2) * (Real.exp (-t) * Real.exp t) := by ring
    _ = 1 + -t + (-t) ^ 2 / 2 := by rw [← Real.exp_add]; simp; ring

lemma fact_ge (m : ℕ) : 2 * 3 ^ m ≤ (m + 2).factorial := by
  induction m with
  | zero => simp [Nat.factorial]
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

lemma exp_le_bern_pos (y c : ℝ) (hy0 : 0 ≤ y) (hyc : y ≤ c) (hc : c < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - c / 3)) := by
  have hc0 : 0 ≤ c := le_trans hy0 hyc
  have hr0 : 0 ≤ c / 3 := by positivity
  have hr1 : c / 3 < 1 := by linarith
  have hexp : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  let t : ℕ → ℝ := fun n =>
    if n < 2 then y ^ n / (n.factorial : ℝ) else y ^ 2 / 2 * (c / 3) ^ (n - 2)
  have hgeo : HasSum (fun n : ℕ => y ^ 2 / 2 * (c / 3) ^ n) (y ^ 2 / 2 * (1 - c / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left _
  have ht : HasSum t (1 + y + y ^ 2 / (2 * (1 - c / 3))) := by
    rw [← hasSum_nat_add_iff' 2]
    have e : (fun n => t (n + 2)) = fun n : ℕ => y ^ 2 / 2 * (c / 3) ^ n := by
      funext n; simp [t]
    rw [e]
    have h3 : (1 - c / 3) ≠ 0 := by linarith
    have h0 : t 0 = 1 := by simp [t]
    have h1 : t 1 = y := by simp [t]
    have hv : 1 + y + y ^ 2 / (2 * (1 - c / 3)) - ∑ i ∈ Finset.range 2, t i =
        y ^ 2 / 2 * (1 - c / 3)⁻¹ := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1]
      field_simp
      ring
    rw [hv]
    exact hgeo
  refine hasSum_le (fun n => ?_) hexp ht
  simp only [t]
  split_ifs with hn
  · exact le_rfl
  · push_neg at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hf := fact_ge m
    have hfpos : (0:ℝ) < ((m + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h2 : (2 * 3 ^ m : ℝ) ≤ ((m + 2).factorial : ℝ) := by exact_mod_cast hf
    have hcm := pow_le_pow_left₀ hy0 hyc m
    have h1 : y ^ (m + 2) ≤ y ^ 2 * c ^ m := by
      rw [pow_add]; nlinarith [mul_le_mul_of_nonneg_right hcm (sq_nonneg y)]
    rw [div_le_iff₀ hfpos]
    calc y ^ (m + 2) ≤ y ^ 2 * c ^ m := h1
      _ = y ^ 2 / 2 * (c / 3) ^ m * (2 * 3 ^ m) := by rw [div_pow]; field_simp
      _ ≤ y ^ 2 / 2 * (c / 3) ^ m * ((m + 2).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)

lemma exp_le_bern (y c : ℝ) (hyc : y ≤ c) (hc0 : 0 ≤ c) (hc : c < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - c / 3)) := by
  by_cases hy : 0 ≤ y
  · exact exp_le_bern_pos y c hy hyc hc
  · push_neg at hy
    have h1 := exp_le_quad_neg y hy.le
    have h2 : y ^ 2 / 2 ≤ y ^ 2 / (2 * (1 - c / 3)) :=
      div_le_div_of_nonneg_left (sq_nonneg y) (by linarith) (by linarith)
    linarith

/-- Bernstein MGF bound for a finite distribution, increments bounded above by `b`. -/
lemma bern_mgf {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1)
    (g : Ω → ℝ) (b lam : ℝ) (hb0 : 0 ≤ b) (hb : ∀ y, g y - ∑ z, p z * g z ≤ b)
    (hlam : 0 ≤ lam) (hlb : lam * b < 3) :
    ∑ y, p y * Real.exp (lam * (g y - ∑ z, p z * g z)) ≤
      Real.exp (lam ^ 2 * (∑ y, p y * (g y - ∑ z, p z * g z) ^ 2) / (2 * (1 - lam * b / 3))) := by
  set m := ∑ z, p z * g z with hm
  set d := 2 * (1 - lam * b / 3) with hd
  have hpt : ∀ y, Real.exp (lam * (g y - m)) ≤
      1 + lam * (g y - m) + (lam * (g y - m)) ^ 2 / (2 * (1 - lam * b / 3)) :=
    fun y => exp_le_bern _ _ (mul_le_mul_of_nonneg_left (hb y) hlam) (mul_nonneg hlam hb0) hlb
  have e1 : ∑ y, p y * (g y - m) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
    rw [hm]; ring
  have e2 : ∀ y, p y * (1 + lam * (g y - m) + (lam * (g y - m)) ^ 2 / d) =
      p y + lam * (p y * (g y - m)) + lam ^ 2 / d * (p y * (g y - m) ^ 2) := by
    intro y; ring
  calc ∑ y, p y * Real.exp (lam * (g y - m))
      ≤ ∑ y, p y * (1 + lam * (g y - m) + (lam * (g y - m)) ^ 2 / d) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hpt y) (hp0 y))
    _ = 1 + lam ^ 2 * (∑ y, p y * (g y - m) ^ 2) / d := by
        rw [Finset.sum_congr rfl (fun y _ => e2 y), Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, e1]
        ring
    _ ≤ Real.exp (lam ^ 2 * (∑ y, p y * (g y - m) ^ 2) / d) := by
        linarith [Real.add_one_le_exp (lam ^ 2 * (∑ y, p y * (g y - m) ^ 2) / d)]

/-- Lower-tail MGF for a nonnegative statistic (no linear term). Written for `-g` to match
the generic concentration lemma. -/
lemma neg_mgf {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1)
    (g : Ω → ℝ) (hg : ∀ y, 0 ≤ g y) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∑ y, p y * Real.exp (lam * (-g y - ∑ z, p z * -g z)) ≤
      Real.exp (lam ^ 2 * (∑ y, p y * g y ^ 2) / 2) := by
  set m := ∑ z, p z * g z with hm
  have hneg : ∑ z, p z * -g z = -m := by
    rw [hm, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro z _; ring
  rw [hneg]
  have hpt : ∀ y, Real.exp (lam * (-g y - -m)) ≤
      Real.exp (lam * m) * (1 - lam * g y + lam ^ 2 * g y ^ 2 / 2) := by
    intro y
    have h := exp_le_quad_neg (-(lam * g y)) (by nlinarith [hg y])
    have e : lam * (-g y - -m) = lam * m + -(lam * g y) := by ring
    rw [e, Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    nlinarith [h]
  have e2 : ∀ y, p y * (Real.exp (lam * m) * (1 - lam * g y + lam ^ 2 * g y ^ 2 / 2)) =
      Real.exp (lam * m) * (p y - lam * (p y * g y) + lam ^ 2 / 2 * (p y * g y ^ 2)) := by
    intro y; ring
  calc ∑ y, p y * Real.exp (lam * (-g y - -m))
      ≤ ∑ y, p y * (Real.exp (lam * m) * (1 - lam * g y + lam ^ 2 * g y ^ 2 / 2)) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hpt y) (hp0 y))
    _ = Real.exp (lam * m) * (1 - lam * m + lam ^ 2 / 2 * ∑ y, p y * g y ^ 2) := by
        rw [Finset.sum_congr rfl (fun y _ => e2 y), ← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, hm]
    _ ≤ Real.exp (lam * m) * Real.exp (-(lam * m) + lam ^ 2 / 2 * ∑ y, p y * g y ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (-(lam * m) + lam ^ 2 / 2 * ∑ y, p y * g y ^ 2)]
    _ = Real.exp (lam ^ 2 * (∑ y, p y * g y ^ 2) / 2) := by
        rw [← Real.exp_add]; congr 1; ring

end MGF

section Conc

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

theorem exp_sum_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (u : Fin K → Fin H → Hoeffding.Outcomes S K H → ℝ)
    (hu : ∀ k h, Adapted (k.val * H + h.val + 1) (u k h))
    (hstep : ∀ k h ω, ∑ y, qP M δ K H sel init k h ω y * Real.exp (u k h (upd ω k h y)) ≤ 1) :
    ∑ ω, outcomeProb M δ K H sel init ω * Real.exp (∑ p : Fin K × Fin H, u p.1 p.2 ω) ≤ 1 := by
  let Z : ℕ → Hoeffding.Outcomes S K H → ℝ := fun t ω =>
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
    have : ∑ y, qP M δ K H sel init k0 h0 ω y *
        (Real.exp (∑ p : Fin K × Fin H,
          if p.1.val * H + p.2.val < k0.val * H + h0.val then u p.1 p.2 ω else 0) *
          Real.exp (u k0 h0 (upd ω k0 h0 y))) =
        Real.exp (∑ p : Fin K × Fin H,
          if p.1.val * H + p.2.val < k0.val * H + h0.val then u p.1 p.2 ω else 0) *
        ∑ y, qP M δ K H sel init k0 h0 ω y * Real.exp (u k0 h0 (upd ω k0 h0 y)) := by
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

/-- Step `(k,h)` visits the pair `(x,a)`. -/
def visit (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (k : Fin K) (h : Fin H) (ω : Hoeffding.Outcomes S K H) : Prop :=
  stateAt init ω k (Fin.castSucc h) = x ∧ act M δ K H sel init ω k h = a

lemma visit_adapted (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (k : Fin K) (h : Fin H) (ω ω' : Hoeffding.Outcomes S K H)
    (hag : Agree (k.val * H + h.val) ω ω') :
    visit M δ sel init x a k h ω ↔ visit M δ sel init x a k h ω' := by
  unfold visit
  rw [stateAt_eq init ω ω' k (Fin.castSucc h) (by simpa using hag),
    act_eq M δ sel init ω ω' k h hag]

/-- Weighted visit sum before time `t`. -/
noncomputable def vsum (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (g : S → ℝ) (t : ℕ) (ω : Hoeffding.Outcomes S K H) : ℝ :=
  ∑ p : Fin K × Fin H,
    if p.1.val * H + p.2.val < t ∧ visit M δ sel init x a p.1 p.2 ω then g (ω p.1 p.2) else 0

/-- Visit count before time `t`. -/
noncomputable def cnt (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (t : ℕ) (ω : Hoeffding.Outcomes S K H) : ℝ :=
  vsum M δ sel init x a (fun _ => 1) t ω

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

lemma vsum_ite (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (g : S → ℝ) (t : ℕ) (ω : Hoeffding.Outcomes S K H) :
    vsum M δ sel init x a g t ω = ∑ p : Fin K × Fin H,
      if p.1.val * H + p.2.val < t then
        (if visit M δ sel init x a p.1 p.2 ω then g (ω p.1 p.2) else 0) else 0 := by
  unfold vsum
  apply Finset.sum_congr rfl
  intro p _
  by_cases h1 : p.1.val * H + p.2.val < t <;>
    by_cases h2 : visit M δ sel init x a p.1 p.2 ω <;> simp [h1, h2]

lemma vsum_adapted (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (g : S → ℝ) (t : ℕ) (ω ω' : Hoeffding.Outcomes S K H) (hag : Agree t ω ω') :
    vsum M δ sel init x a g t ω = vsum M δ sel init x a g t ω' := by
  rw [vsum_ite, vsum_ite]
  apply Finset.sum_congr rfl
  intro p _
  by_cases ht : p.1.val * H + p.2.val < t
  · have hv := visit_adapted M δ sel init x a p.1 p.2 ω ω' (hag.mono ht.le)
    simp only [ht, if_true, hv, hag p.1 p.2 ht]
  · simp only [ht, if_false]

lemma cnt_adapted (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (t : ℕ) (ω ω' : Hoeffding.Outcomes S K H) (hag : Agree t ω ω') :
    cnt M δ sel init x a t ω = cnt M δ sel init x a t ω' :=
  vsum_adapted M δ sel init x a _ t ω ω' hag

lemma cnt_mono (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (t t' : ℕ) (htt : t ≤ t') (ω : Hoeffding.Outcomes S K H) :
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

lemma cnt_succ (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (k : Fin K) (h : Fin H) (ω : Hoeffding.Outcomes S K H) :
    cnt M δ sel init x a (k.val * H + h.val + 1) ω =
      cnt M δ sel init x a (k.val * H + h.val) ω +
        (if visit M δ sel init x a k h ω then 1 else 0) := by
  unfold cnt
  rw [vsum_ite, vsum_ite]
  exact sum_tau_succ (fun p => if visit M δ sel init x a p.1 p.2 ω then (1 : ℝ) else 0) k h

lemma active_iff (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (n : ℕ) (k : Fin K) (ω : Hoeffding.Outcomes S K H)
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
theorem conc_generic (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (g : S → ℝ) (lam ψ : ℝ) (hlam : 0 ≤ lam)
    (hmgf : ∑ y, M.P x a y * Real.exp (lam * (g y - ∑ z, M.P x a z * g z)) ≤ Real.exp ψ)
    (n : ℕ) (ε : ℝ) :
    probEvent M δ K H sel init (fun ω => ∃ k : Fin K, cnt M δ sel init x a (k.val * H) ω = n ∧
        (n : ℝ) * ε ≤ vsum M δ sel init x a g (k.val * H) ω - n * ∑ z, M.P x a z * g z) ≤
      Real.exp (-(lam * n * ε - n * ψ)) := by
  set Pg := ∑ z, M.P x a z * g z with hPg
  let u : Fin K → Fin H → Hoeffding.Outcomes S K H → ℝ := fun k h ω =>
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
      ∑ y, qP M δ K H sel init k h ω y * Real.exp (u k h (upd ω k h y)) ≤ 1 := by
    intro k h ω
    by_cases hact : visit M δ sel init x a k h ω ∧
        cnt M δ sel init x a (k.val * H + h.val) ω < n
    · have hq : ∀ y, qP M δ K H sel init k h ω y = M.P x a y := by
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

lemma probEvent_exists_le {ι : Type*} [Fintype ι] (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (E : ι → Hoeffding.Outcomes S K H → Prop) :
    probEvent M δ K H sel init (fun ω => ∃ i, E i ω) ≤
      ∑ i, probEvent M δ K H sel init (E i) := by
  unfold probEvent
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  have hp := outcomeProb_nonneg M δ sel init ω
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    calc outcomeProb M δ K H sel init ω
        = (if E i ω then outcomeProb M δ K H sel init ω else 0) := by rw [if_pos hi]
      _ ≤ ∑ j, (if E j ω then outcomeProb M δ K H sel init ω else 0) :=
        Finset.single_le_sum (f := fun j => if E j ω then outcomeProb M δ K H sel init ω else 0)
          (fun j _ => by split_ifs <;> linarith) (Finset.mem_univ i)
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> linarith)

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

/-! Link between the run's triple counts and the visit sums. -/

lemma vsum_eq_fin (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (g : S → ℝ) (n : ℕ) (ω : Hoeffding.Outcomes S K H) :
    vsum M δ sel init x a g (n * H) ω =
      ∑ j : Fin K, ∑ h : Fin H,
        if j.val < n ∧ visit M δ sel init x a j h ω then g (ω j h) else 0 := by
  unfold vsum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h _
  have ht := tau_lt_iff (H := H) j.val n h.val h.isLt
  simp only [ht]

lemma triples_wsum (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (x : S) (a : A) (g : S → ℝ) :
    ∀ n, n ≤ K → ∑ y, ((runState M δ K H sel init ω n).triples x a y : ℝ) * g y =
      ∑ j : Fin K, ∑ h : Fin H,
        if j.val < n ∧ visit M δ sel init x a j h ω then g (ω j h) else 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [runState, initialModel]
  | succ n ih =>
    intro hn
    have hnK : n < K := hn
    have ih' := ih (by omega)
    have hst : (runState M δ K H sel init ω (n + 1)).triples x a = fun y =>
        (runState M δ K H sel init ω n).triples x a y +
          ∑ h : Fin H, if visit M δ sel init x a ⟨n, hnK⟩ h ω ∧ ω ⟨n, hnK⟩ h = y then 1 else 0 := by
      funext y
      simp only [runState, dif_pos hnK, advance]
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      simp only [visit, act, policyAt, and_assoc]
    rw [hst]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib, ih']
    have e1 : ∑ y, (∑ h : Fin H, if visit M δ sel init x a ⟨n, hnK⟩ h ω ∧ ω ⟨n, hnK⟩ h = y
        then (1 : ℝ) else 0) * g y =
        ∑ h : Fin H, if visit M δ sel init x a ⟨n, hnK⟩ h ω then g (ω ⟨n, hnK⟩ h) else 0 := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      by_cases hv : visit M δ sel init x a ⟨n, hnK⟩ h ω
      · simp [hv]
      · simp [hv]
    rw [e1]
    have e2 : ∀ (j : Fin K) (h : Fin H),
        (if j.val < n + 1 ∧ visit M δ sel init x a j h ω then g (ω j h) else 0) =
          (if j.val < n ∧ visit M δ sel init x a j h ω then g (ω j h) else 0) +
          (if j = ⟨n, hnK⟩ ∧ visit M δ sel init x a j h ω then g (ω j h) else 0) := by
      intro j h
      by_cases hj : j = ⟨n, hnK⟩
      · subst hj; simp
      · have hjn : j.val ≠ n := fun e => hj (Fin.ext e)
        by_cases hlt : j.val < n
        · have h2 : j.val < n + 1 := by omega
          simp [hlt, h2, hj]
        · have h2 : ¬ j.val < n + 1 := by omega
          simp [hlt, h2, hj]
    simp only [e2, Finset.sum_add_distrib]
    congr 1
    symm
    rw [Finset.sum_eq_single ⟨n, hnK⟩]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h

lemma countSA_eq_cnt (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (x : S) (a : A) (n : ℕ) (hn : n ≤ K) :
    ((countSA (runState M δ K H sel init ω n) x a : ℕ) : ℝ) = cnt M δ sel init x a (n * H) ω := by
  unfold cnt
  have h1 := triples_wsum M δ sel init ω x a (fun _ => (1 : ℝ)) n hn
  simp only [mul_one] at h1
  rw [vsum_eq_fin, ← h1]
  unfold countSA
  push_cast
  rfl

lemma empiricalExp_eq (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (x : S) (a : A) (g : S → ℝ) (n : ℕ) (hn : n ≤ K) :
    empiricalExp (runState M δ K H sel init ω n) x a g =
      vsum M δ sel init x a g (n * H) ω / cnt M δ sel init x a (n * H) ω := by
  rw [← countSA_eq_cnt M δ sel init ω x a n hn, vsum_eq_fin,
    ← triples_wsum M δ sel init ω x a g n hn]
  unfold empiricalExp finiteExp empiricalP
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Concentration of the empirical row against `g` at count `m` (the run's own counts). -/
lemma event_gen (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (g : S → ℝ) (lam ψ : ℝ) (hlam : 0 ≤ lam)
    (hmgf : ∑ y, M.P x a y * Real.exp (lam * (g y - ∑ z, M.P x a z * g z)) ≤ Real.exp ψ)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) :
    probEvent M δ K H sel init (fun ω => ∃ k : Fin K,
        countSA (runState M δ K H sel init ω k.val) x a = m ∧
        ε ≤ empiricalExp (runState M δ K H sel init ω k.val) x a g - ∑ z, M.P x a z * g z) ≤
      Real.exp (-(lam * m * ε - m * ψ)) := by
  refine le_trans (probEvent_mono M δ sel init _ _ ?_)
    (conc_generic M δ sel init x a g lam ψ hlam hmgf m ε)
  rintro ω ⟨k, hk, hev⟩
  have hcnt : cnt M δ sel init x a (k.val * H) ω = m := by
    rw [← countSA_eq_cnt M δ sel init ω x a k.val k.isLt.le, hk]
  refine ⟨k, hcnt, ?_⟩
  rw [empiricalExp_eq M δ sel init ω x a g k.val k.isLt.le, hcnt] at hev
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have key : (m : ℝ) * (vsum M δ sel init x a g (k.val * H) ω / m - ∑ z, M.P x a z * g z) =
      vsum M δ sel init x a g (k.val * H) ω - m * ∑ z, M.P x a z * g z := by
    field_simp
  have := mul_le_mul_of_nonneg_left hev hm'.le
  linarith [key]

end Conc

section Events

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

/-- MGF when the statistic is almost surely constant. -/
lemma mgf_var_zero {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∑ y, p y = 1) (g : Ω → ℝ) (hV : ∑ y, p y * (g y - ∑ z, p z * g z) ^ 2 = 0)
    (lam : ℝ) :
    ∑ y, p y * Real.exp (lam * (g y - ∑ z, p z * g z)) ≤ Real.exp 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun y _ => mul_nonneg (hp0 y) (sq_nonneg (g y - ∑ z, p z * g z)))).mp hV
  have e : ∀ y, p y * Real.exp (lam * (g y - ∑ z, p z * g z)) = p y := by
    intro y
    rcases mul_eq_zero.mp (hz y (Finset.mem_univ y)) with h | h
    · rw [h]; ring
    · have h0 : g y - ∑ z, p z * g z = 0 := (pow_eq_zero_iff two_ne_zero).mp h
      rw [h0]; simp
  rw [Finset.sum_congr rfl (fun y _ => e y), hp1, Real.exp_zero]

/-- Bernstein upper tail at the run's random count `m`:
deviation threshold `√(2Vℓ/m) + bℓ/(3m)`. -/
lemma event_bern (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (g : S → ℝ) (b V ℓ : ℝ) (hb : 0 < b)
    (hgb : ∀ y, g y - ∑ z, M.P x a z * g z ≤ b)
    (hV : ∑ y, M.P x a y * (g y - ∑ z, M.P x a z * g z) ^ 2 = V) (hℓ : 0 < ℓ)
    (m : ℕ) (hm : 0 < m) :
    probEvent M δ K H sel init (fun ω => ∃ k : Fin K,
        countSA (runState M δ K H sel init ω k.val) x a = m ∧
        Real.sqrt (2 * V * ℓ / m) + b * ℓ / (3 * m) ≤
          empiricalExp (runState M δ K H sel init ω k.val) x a g - ∑ z, M.P x a z * g z) ≤
      Real.exp (-ℓ) := by
  obtain ⟨hp0, hp1⟩ := M.kernel x a
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hV0 : 0 ≤ V := hV ▸ Finset.sum_nonneg (fun y _ => mul_nonneg (hp0 y) (sq_nonneg _))
  rcases hV0.lt_or_eq with hVp | hVz
  · -- positive variance: the optimal Bernstein parameter
    set r := ℓ / m with hr
    have hr0 : 0 < r := div_pos hℓ hm'
    set u := Real.sqrt (2 * r / V) with hu
    have hu0 : 0 < u := Real.sqrt_pos.mpr (by positivity)
    have hu2 : u ^ 2 = 2 * r / V := Real.sq_sqrt (by positivity)
    have hr' : r = u ^ 2 * V / 2 := by rw [hu2]; field_simp
    have hsq : Real.sqrt (2 * V * ℓ / m) = u * V := by
      have e : 2 * V * ℓ / m = (u * V) ^ 2 := by
        rw [mul_pow, hu2]; field_simp; rw [hr]; field_simp
      rw [e]; exact Real.sqrt_sq (by positivity)
    have hbr : b * ℓ / (3 * m) = b / 3 * r := by rw [hr]; field_simp
    have hc : 0 < 1 + b / 3 * u := by positivity
    set lam := u / (1 + b / 3 * u) with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hlb : lam * b < 3 := by
      rw [hlam, div_mul_eq_mul_div, div_lt_iff₀ hc]; nlinarith
    have hmgf := bern_mgf (M.P x a) hp0 hp1 g b lam hb.le hgb hlam0 hlb
    rw [hV] at hmgf
    set ψ := u ^ 2 * V / (2 * (1 + b / 3 * u)) with hψ
    have hψe : lam ^ 2 * V / (2 * (1 - lam * b / 3)) = ψ := by
      rw [hlam, hψ]; field_simp; ring
    rw [hψe] at hmgf
    have h := event_gen (K := K) M δ sel init x a g lam ψ hlam0 hmgf m hm
      (Real.sqrt (2 * V * ℓ / m) + b * ℓ / (3 * m))
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    rw [hsq, hbr]
    have key : lam * (u * V + b / 3 * r) - ψ = r := by
      rw [hr', hlam, hψ]; field_simp; ring
    have hl : ℓ = m * r := by rw [hr]; field_simp
    have : lam * m * (u * V + b / 3 * r) - m * ψ = m * (lam * (u * V + b / 3 * r) - ψ) := by
      ring
    rw [this, key, hl]
  · -- zero variance
    subst hVz
    have hmgf := mgf_var_zero (M.P x a) hp0 hp1 g hV (3 / b)
    have h := event_gen (K := K) M δ sel init x a g (3 / b) 0 (by positivity) hmgf m hm
      (Real.sqrt (2 * 0 * ℓ / m) + b * ℓ / (3 * m))
    refine le_trans h (Real.exp_le_exp.mpr (le_of_eq ?_))
    simp only [mul_zero, zero_mul, zero_div, Real.sqrt_zero, zero_add, sub_zero]
    field_simp

/-- Hoeffding upper tail at the run's random count, for `g` with values in `[lo, hi]`. -/
lemma event_hoeff (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (g : S → ℝ) (lo hi ℓ : ℝ) (hlh : lo < hi)
    (hg : ∀ y, g y ∈ Set.Icc lo hi) (hℓ : 0 < ℓ) (m : ℕ) (hm : 0 < m) :
    probEvent M δ K H sel init (fun ω => ∃ k : Fin K,
        countSA (runState M δ K H sel init ω k.val) x a = m ∧
        (hi - lo) * Real.sqrt (ℓ / (2 * m)) ≤
          empiricalExp (runState M δ K H sel init ω k.val) x a g - ∑ z, M.P x a z * g z) ≤
      Real.exp (-ℓ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : 0 < hi - lo := by linarith
  set ε := (hi - lo) * Real.sqrt (ℓ / (2 * m)) with hε
  have hs2 : Real.sqrt (ℓ / (2 * m)) ^ 2 = ℓ / (2 * m) := Real.sq_sqrt (by positivity)
  have e1 : ε ^ 2 = (hi - lo) ^ 2 * (ℓ / (2 * m)) := by rw [hε, mul_pow, hs2]
  have hε0 : 0 ≤ ε := by positivity
  have hmgf := hoeffding_fin (M.P x a) (M.kernel x a).1 (M.kernel x a).2 g lo hi hg
    (4 * ε / (hi - lo) ^ 2)
  have h := event_gen (K := K) M δ sel init x a g (4 * ε / (hi - lo) ^ 2)
    ((4 * ε / (hi - lo) ^ 2) ^ 2 * (hi - lo) ^ 2 / 8) (by positivity) hmgf m hm ε
  refine le_trans h (Real.exp_le_exp.mpr (le_of_eq ?_))
  have hψ : (4 * ε / (hi - lo) ^ 2) ^ 2 * (hi - lo) ^ 2 / 8 = 2 * ε ^ 2 / (hi - lo) ^ 2 := by
    field_simp; ring
  have hle : 4 * ε / (hi - lo) ^ 2 * m * ε = 4 * m * ε ^ 2 / (hi - lo) ^ 2 := by ring
  rw [hψ, hle, e1]
  field_simp
  ring

/-- Lower tail for a nonnegative statistic (no linear term), strict form. -/
lemma event_nonneg_lower (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (x : S) (a : A) (g : S → ℝ) (hg : ∀ y, 0 ≤ g y) (W ℓ : ℝ)
    (hW : ∑ y, M.P x a y * g y ^ 2 = W) (hℓ : 0 < ℓ) (m : ℕ) (hm : 0 < m) :
    probEvent M δ K H sel init (fun ω => ∃ k : Fin K,
        countSA (runState M δ K H sel init ω k.val) x a = m ∧
        Real.sqrt (2 * W * ℓ / m) < ∑ z, M.P x a z * g z -
          empiricalExp (runState M δ K H sel init ω k.val) x a g) ≤ Real.exp (-ℓ) := by
  obtain ⟨hp0, hp1⟩ := M.kernel x a
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hW0 : 0 ≤ W := hW ▸ Finset.sum_nonneg (fun y _ => mul_nonneg (hp0 y) (sq_nonneg _))
  have hneg : ∀ st : ModelState S A H,
      empiricalExp st x a (fun y => -g y) = -empiricalExp st x a g := by
    intro st; unfold empiricalExp finiteExp
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro y _; ring
  have hPneg : ∑ z, M.P x a z * -g z = -∑ z, M.P x a z * g z := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro y _; ring
  rcases hW0.lt_or_eq with hWp | hWz
  · set ε := Real.sqrt (2 * W * ℓ / m) with hε
    have hε0 : 0 < ε := Real.sqrt_pos.mpr (by positivity)
    have hε2 : ε ^ 2 = 2 * W * ℓ / m := Real.sq_sqrt (by positivity)
    have hmgf := neg_mgf (M.P x a) hp0 hp1 g hg (ε / W) (by positivity)
    rw [hW] at hmgf
    have h := event_gen (K := K) M δ sel init x a (fun y => -g y) (ε / W)
      ((ε / W) ^ 2 * W / 2) (by positivity) hmgf m hm ε
    refine le_trans (probEvent_mono M δ sel init _ _ ?_)
      (le_trans h (Real.exp_le_exp.mpr (le_of_eq ?_)))
    · rintro ω ⟨k, hk, hev⟩
      refine ⟨k, hk, ?_⟩
      simp only [hneg, hPneg]
      linarith
    · have e1 : ε / W * m * ε - m * ((ε / W) ^ 2 * W / 2) = m * ε ^ 2 / (2 * W) := by
        field_simp; ring
      rw [e1, hε2]; field_simp
  · have hW' : ∑ y, M.P x a y * g y ^ 2 = 0 := by rw [hW, ← hWz]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hp0 y) (sq_nonneg (g y)))).mp hW'
    have hPg : ∑ z, M.P x a z * g z = 0 := by
      apply Finset.sum_eq_zero; intro y _
      rcases mul_eq_zero.mp (hz y (Finset.mem_univ y)) with h | h
      · rw [h, zero_mul]
      · rw [(pow_eq_zero_iff two_ne_zero).mp h, mul_zero]
    rw [probEvent_false M δ sel init _ ?_]
    · exact (Real.exp_pos _).le
    · rintro ω ⟨k, _, hev⟩
      rw [hPg] at hev
      have : 0 ≤ empiricalExp (runState M δ K H sel init ω k.val) x a g := by
        unfold empiricalExp finiteExp empiricalP
        exact Finset.sum_nonneg (fun y _ => mul_nonneg
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hg y))
      have hs := Real.sqrt_nonneg (2 * W * ℓ / m)
      linarith

end Events

section GoodOpt

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma cnt_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (t : ℕ) (ω : Hoeffding.Outcomes S K H) :
    cnt M δ sel init x a t ω ≤ (K : ℝ) * H := by
  unfold cnt vsum
  calc _ ≤ ∑ _p : Fin K × Fin H, (1 : ℝ) :=
        Finset.sum_le_sum (fun p _ => by split_ifs <;> norm_num)
    _ = (K : ℝ) * H := by simp

lemma countSA_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (x : S) (a : A) (k : Fin K) :
    countSA (runState M δ K H sel init ω k.val) x a ≤ K * H := by
  have h1 := cnt_le M δ sel init x a (k.val * H) ω
  rw [← countSA_eq_cnt M δ sel init ω x a k.val k.isLt.le] at h1
  exact_mod_cast h1

/-- Expectation under the true row. -/
noncomputable def Pexp (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) : ℝ :=
  ∑ z, M.P x a z * f z

/-- `V*_{h+1}` as a function of the next state. -/
noncomputable def vstar (M : Hoeffding.MDP S A) (H : ℕ) (h : Fin H) : S → ℝ :=
  fun y => optimalValue M H (h.val + 1) y

/-- Squared centred statistic `(f - Pf)²`. -/
noncomputable def csq (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) : S → ℝ :=
  fun y => (f y - Pexp M x a f) ^ 2

/-- True variance `Var_P f`. -/
noncomputable def cvar (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) : ℝ :=
  ∑ y, M.P x a y * csq M x a f y

/-- Second moment of `(f - Pf)²`. -/
noncomputable def cW (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) : ℝ :=
  ∑ y, M.P x a y * csq M x a f y ^ 2

lemma vstar_nonneg (M : Hoeffding.MDP S A) (H : ℕ) (h : Fin H) (y : S) : 0 ≤ vstar M H h y :=
  opt_nonneg M H _ y

lemma vstar_le (M : Hoeffding.MDP S A) (H : ℕ) (h : Fin H) (y : S) : vstar M H h y ≤ H := by
  have h1 := opt_le M H (h.val + 1) y
  have h2 : ((H - (h.val + 1) : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H _
  exact le_trans h1 h2

lemma Pexp_neg (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) :
    ∑ z, M.P x a z * (fun y => -f y) z = -Pexp M x a f := by
  unfold Pexp; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro y _; ring

lemma empExp_neg (st : ModelState S A H) (x : S) (a : A) (f : S → ℝ) :
    empiricalExp st x a (fun y => -f y) = -empiricalExp st x a f := by
  unfold empiricalExp finiteExp
  rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro y _; ring

lemma Pexp_le (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) (c : ℝ) (hf : ∀ y, f y ≤ c) :
    Pexp M x a f ≤ c := by
  obtain ⟨hp0, hp1⟩ := M.kernel x a
  unfold Pexp
  calc _ ≤ ∑ z, M.P x a z * c := Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hf z) (hp0 z))
    _ = c := by rw [← Finset.sum_mul, hp1, one_mul]

lemma Pexp_nonneg (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) (hf : ∀ y, 0 ≤ f y) :
    0 ≤ Pexp M x a f :=
  Finset.sum_nonneg (fun z _ => mul_nonneg ((M.kernel x a).1 z) (hf z))

/-- The optimism good event (blueprint E1-E3) at union log `ℓ`. -/
def GoodOpt (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ℓ : ℝ) (ω : Hoeffding.Outcomes S K H) : Prop :=
  ∀ (k : Fin K) (x : S) (a : A) (h : Fin H),
    0 < countSA (runState M δ K H sel init ω k.val) x a →
    (Pexp M x a (vstar M H h) -
        empiricalExp (runState M δ K H sel init ω k.val) x a (vstar M H h) ≤
      Real.sqrt (2 * cvar M x a (vstar M H h) * ℓ /
          (countSA (runState M δ K H sel init ω k.val) x a : ℝ)) +
        H * ℓ / (3 * (countSA (runState M δ K H sel init ω k.val) x a : ℝ))) ∧
    (Pexp M x a (vstar M H h) -
        empiricalExp (runState M δ K H sel init ω k.val) x a (vstar M H h) ≤
      H * Real.sqrt (ℓ / (2 * (countSA (runState M δ K H sel init ω k.val) x a : ℝ)))) ∧
    (Pexp M x a (csq M x a (vstar M H h)) -
        empiricalExp (runState M δ K H sel init ω k.val) x a (csq M x a (vstar M H h)) ≤
      Real.sqrt (2 * cW M x a (vstar M H h) * ℓ /
          (countSA (runState M δ K H sel init ω k.val) x a : ℝ)))

theorem probOpt (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (hH : 0 < H) :
    probEvent M δ K H sel init (fun ω => ¬ GoodOpt M δ sel init ℓ ω) ≤
      (Fintype.card S * Fintype.card A * H * (K * H) : ℕ) * (3 * Real.exp (-ℓ)) := by
  -- the three bad events at index (x, a, h, m-1)
  let B1 : S × A × Fin H × Fin (K * H) → Hoeffding.Outcomes S K H → Prop := fun i ω =>
    ∃ k : Fin K, countSA (runState M δ K H sel init ω k.val) i.1 i.2.1 = i.2.2.2.val + 1 ∧
      Real.sqrt (2 * (∑ y, M.P i.1 i.2.1 y * ((fun z => -vstar M H i.2.2.1 z) y -
          ∑ z, M.P i.1 i.2.1 z * (fun z => -vstar M H i.2.2.1 z) z) ^ 2) * ℓ /
          ((i.2.2.2.val + 1 : ℕ) : ℝ)) + H * ℓ / (3 * ((i.2.2.2.val + 1 : ℕ) : ℝ)) ≤
        empiricalExp (runState M δ K H sel init ω k.val) i.1 i.2.1
          (fun z => -vstar M H i.2.2.1 z) -
          ∑ z, M.P i.1 i.2.1 z * (fun z => -vstar M H i.2.2.1 z) z
  let B2 : S × A × Fin H × Fin (K * H) → Hoeffding.Outcomes S K H → Prop := fun i ω =>
    ∃ k : Fin K, countSA (runState M δ K H sel init ω k.val) i.1 i.2.1 = i.2.2.2.val + 1 ∧
      (0 - -(H : ℝ)) * Real.sqrt (ℓ / (2 * ((i.2.2.2.val + 1 : ℕ) : ℝ))) ≤
        empiricalExp (runState M δ K H sel init ω k.val) i.1 i.2.1
          (fun z => -vstar M H i.2.2.1 z) -
          ∑ z, M.P i.1 i.2.1 z * (fun z => -vstar M H i.2.2.1 z) z
  let B3 : S × A × Fin H × Fin (K * H) → Hoeffding.Outcomes S K H → Prop := fun i ω =>
    ∃ k : Fin K, countSA (runState M δ K H sel init ω k.val) i.1 i.2.1 = i.2.2.2.val + 1 ∧
      Real.sqrt (2 * cW M i.1 i.2.1 (vstar M H i.2.2.1) * ℓ / ((i.2.2.2.val + 1 : ℕ) : ℝ)) <
        ∑ z, M.P i.1 i.2.1 z * csq M i.1 i.2.1 (vstar M H i.2.2.1) z -
          empiricalExp (runState M δ K H sel init ω k.val) i.1 i.2.1
            (csq M i.1 i.2.1 (vstar M H i.2.2.1))
  have hB : ∀ i, probEvent M δ K H sel init (fun ω => B1 i ω ∨ B2 i ω ∨ B3 i ω) ≤
      3 * Real.exp (-ℓ) := by
    intro i
    obtain ⟨x, a, h, m⟩ := i
    have hf0 := vstar_nonneg M H h
    have hfH := vstar_le M H h
    have hPf := Pexp_le M x a (vstar M H h) H hfH
    have e1 : probEvent M δ K H sel init (B1 (x, a, h, m)) ≤ Real.exp (-ℓ) := by
      refine event_bern M δ sel init x a (fun z => -vstar M H h z) H _ ℓ (by exact_mod_cast hH)
        ?_ rfl hℓ (m.val + 1) (Nat.succ_pos _)
      intro y
      have := Pexp_neg M x a (vstar M H h)
      simp only at this ⊢
      rw [this]
      linarith [hf0 y, hPf]
    have e2 : probEvent M δ K H sel init (B2 (x, a, h, m)) ≤ Real.exp (-ℓ) := by
      refine event_hoeff M δ sel init x a (fun z => -vstar M H h z) (-(H : ℝ)) 0 ℓ
        (by have : (0 : ℝ) < H := by exact_mod_cast hH
            linarith) ?_ hℓ (m.val + 1) (Nat.succ_pos _)
      intro y
      exact ⟨by show -(H : ℝ) ≤ -vstar M H h y; linarith [hfH y],
        by show -vstar M H h y ≤ 0; linarith [hf0 y]⟩
    have e3 : probEvent M δ K H sel init (B3 (x, a, h, m)) ≤ Real.exp (-ℓ) :=
      event_nonneg_lower M δ sel init x a (csq M x a (vstar M H h))
        (fun y => sq_nonneg _) (cW M x a (vstar M H h)) ℓ rfl hℓ (m.val + 1) (Nat.succ_pos _)
    calc _ ≤ probEvent M δ K H sel init (B1 (x, a, h, m)) +
          probEvent M δ K H sel init (fun ω => B2 (x, a, h, m) ω ∨ B3 (x, a, h, m) ω) :=
          probEvent_union M δ sel init _ _
      _ ≤ probEvent M δ K H sel init (B1 (x, a, h, m)) +
          (probEvent M δ K H sel init (B2 (x, a, h, m)) +
            probEvent M δ K H sel init (B3 (x, a, h, m))) :=
          add_le_add le_rfl (probEvent_union M δ sel init _ _)
      _ ≤ 3 * Real.exp (-ℓ) := by linarith
  have hsub : ∀ ω, ¬ GoodOpt M δ sel init ℓ ω →
      ∃ i : S × A × Fin H × Fin (K * H), B1 i ω ∨ B2 i ω ∨ B3 i ω := by
    intro ω hω
    unfold GoodOpt at hω
    push_neg at hω
    obtain ⟨k, x, a, h, hpos, hbad⟩ := hω
    set n := countSA (runState M δ K H sel init ω k.val) x a with hn
    have hnle := countSA_le M δ sel init ω x a k
    refine ⟨(x, a, h, ⟨n - 1, by omega⟩), ?_⟩
    have hn1 : n - 1 + 1 = n := by omega
    have hfeq := Pexp_neg M x a (vstar M H h)
    have hvar : (∑ y, M.P x a y * (-vstar M H h y - -Pexp M x a (vstar M H h)) ^ 2) =
        cvar M x a (vstar M H h) := by
      unfold cvar csq
      apply Finset.sum_congr rfl
      intro y _
      ring
    have hne := empExp_neg (runState M δ K H sel init ω k.val) x a (vstar M H h)
    by_cases c1 : Pexp M x a (vstar M H h) -
        empiricalExp (runState M δ K H sel init ω k.val) x a (vstar M H h) ≤
      Real.sqrt (2 * cvar M x a (vstar M H h) * ℓ / (n : ℝ)) + H * ℓ / (3 * (n : ℝ))
    · by_cases c2 : Pexp M x a (vstar M H h) -
          empiricalExp (runState M δ K H sel init ω k.val) x a (vstar M H h) ≤
        H * Real.sqrt (ℓ / (2 * (n : ℝ)))
      · right; right
        refine ⟨k, by simp only; rw [hn1], ?_⟩
        have := hbad c1 c2
        simp only [hn1]
        unfold Pexp at this
        exact this
      · right; left
        refine ⟨k, by simp only; rw [hn1], ?_⟩
        simp only [hn1, hfeq, hne]
        push_neg at c2
        linarith
    · left
      refine ⟨k, by simp only; rw [hn1], ?_⟩
      simp only [hn1, hfeq, hne]
      rw [hvar]
      push_neg at c1
      linarith
  calc _ ≤ probEvent M δ K H sel init
        (fun ω => ∃ i : S × A × Fin H × Fin (K * H), B1 i ω ∨ B2 i ω ∨ B3 i ω) :=
        probEvent_mono M δ sel init _ _ hsub
    _ ≤ ∑ i : S × A × Fin H × Fin (K * H),
          probEvent M δ K H sel init (fun ω => B1 i ω ∨ B2 i ω ∨ B3 i ω) :=
        probEvent_exists_le M δ sel init _
    _ ≤ ∑ _i : S × A × Fin H × Fin (K * H), 3 * Real.exp (-ℓ) := Finset.sum_le_sum (fun i _ => hB i)
    _ = _ := by simp [Fintype.card_prod, Fintype.card_fin]; ring

end GoodOpt

section OptStep

/-- The optimism step with the horizon scale `H` restored. `D = (P - P̂)V*`, `V = Var_P V*`,
`vhat = Var̂ V*`, `sk² = Var̂ V_k`, `sd` = empirical std of `Δ`, `u = P̂Δ`, `n` = count. -/
lemma opt_step (H n ℓ La V D vhat sk sd u : ℝ) (hH : 0 < H) (hn : 0 < n) (hℓ : 0 ≤ ℓ)
    (hℓLa : ℓ ≤ 3 / 2 * La) (hV0 : 0 ≤ V) (hvh0 : 0 ≤ vhat)
    (hE1 : D ≤ Real.sqrt (2 * V * ℓ / n) + H * ℓ / (3 * n))
    (hE2 : D ≤ H * Real.sqrt (ℓ / (2 * n)))
    (hvh : V - H * Real.sqrt (2 * V * ℓ / n) - D ^ 2 ≤ vhat)
    (hsk : 0 ≤ sk) (hsd : 0 ≤ sd) (hstd : Real.sqrt vhat ≤ sk + sd) (hu : sd ^ 2 ≤ H * u) :
    D ≤ u + Real.sqrt (8 * La * sk ^ 2 / n) + 14 * H * La / (3 * n) := by
  set a := Real.sqrt (2 * ℓ / n) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * ℓ / n := Real.sq_sqrt (by positivity)
  have hsV : Real.sqrt (2 * V * ℓ / n) = a * Real.sqrt V := by
    rw [show 2 * V * ℓ / n = (a * Real.sqrt V) ^ 2 by rw [mul_pow, ha2, Real.sq_sqrt hV0]; ring]
    exact Real.sqrt_sq (by positivity)
  have hhalf : Real.sqrt (ℓ / (2 * n)) = a / 2 := by
    rw [show ℓ / (2 * n) = (a / 2) ^ 2 by rw [div_pow, ha2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hLa0 : 0 ≤ La := by linarith only [hℓ, hℓLa]
  set β := Real.sqrt (8 * La / n) with hβ
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hβ2 : β ^ 2 = 8 * La / n := Real.sq_sqrt (by positivity)
  have hβa : 8 / 3 * a ^ 2 ≤ β ^ 2 := by
    rw [ha2, hβ2, show 8 / 3 * (2 * ℓ / n) = (16 / 3 * ℓ) / n by ring]
    exact div_le_div_of_nonneg_right (by linarith only [hℓLa]) hn.le
  have hbon : Real.sqrt (8 * La * sk ^ 2 / n) = β * sk := by
    rw [show 8 * La * sk ^ 2 / n = (β * sk) ^ 2 by rw [mul_pow, hβ2]; ring]
    exact Real.sqrt_sq (by positivity)
  have hD1 : D / H ≤ a / 2 := by
    rw [div_le_iff₀ hH]
    rw [hhalf] at hE2
    have e : H * (a / 2) = a / 2 * H := by ring
    linarith only [hE2, e]
  have hD2 : D / H ≤ a * (Real.sqrt V / H) + a ^ 2 / 6 := by
    rw [div_le_iff₀ hH]
    have e : (a * (Real.sqrt V / H) + a ^ 2 / 6) * H = a * Real.sqrt V + H * ℓ / (3 * n) := by
      rw [ha2]; field_simp; ring
    rw [e, ← hsV]
    exact hE1
  have hm : (Real.sqrt V / H) ^ 2 - a * (Real.sqrt V / H) - (D / H) ^ 2 ≤
      (Real.sqrt vhat / H) ^ 2 := by
    have e1 : (Real.sqrt V / H) ^ 2 - a * (Real.sqrt V / H) - (D / H) ^ 2 =
        (V - H * (a * Real.sqrt V) - D ^ 2) / H ^ 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt hV0]; field_simp
    have e2 : (Real.sqrt vhat / H) ^ 2 = vhat / H ^ 2 := by
      rw [div_pow, Real.sq_sqrt hvh0]
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [← hsV]
    exact hvh
  have hmk : Real.sqrt vhat / H ≤ sk / H + sd / H := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hstd hH.le
  have hu' : (sd / H) ^ 2 ≤ u / H := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hH]
    calc sd ^ 2 * H ≤ H * u * H := mul_le_mul_of_nonneg_right hu hH.le
      _ = u * H ^ 2 := by ring
  have key := opt_alg a (D / H) (Real.sqrt V / H) (Real.sqrt vhat / H) (sk / H) (sd / H) (u / H) β
    ha0 hD1 hD2 (by positivity) hm hmk (by positivity) (by positivity) hu' hβ0 hβa
  rw [div_le_iff₀ hH] at key
  have e3 : (u / H + β * (sk / H) + 14 / 9 * a ^ 2) * H = u + β * sk + 14 / 9 * a ^ 2 * H := by
    field_simp
  have k3 : 14 / 9 * a ^ 2 * H ≤ 14 * H * La / (3 * n) := by
    rw [ha2, show 14 / 9 * (2 * ℓ / n) * H = (28 / 9 * ℓ * H) / n by ring,
      show 14 * H * La / (3 * n) = (14 / 3 * La * H) / n by field_simp]
    apply div_le_div_of_nonneg_right _ hn.le
    linarith only [mul_le_mul_of_nonneg_right hℓLa hH.le]
  rw [hbon]
  linarith only [key, e3, k3]

end OptStep

section FinVar

variable {Ω : Type*} [Fintype Ω]

lemma fv_shift (p : Ω → ℝ) (hp1 : ∑ y, p y = 1) (f : Ω → ℝ) (c : ℝ) :
    finiteVar p f = finiteExp p (fun y => (f y - c) ^ 2) - (finiteExp p f - c) ^ 2 := by
  simp only [finiteVar, finiteExp]
  have e : ∑ z, p z * (f z - c) ^ 2 =
      ∑ z, p z * f z ^ 2 - 2 * c * ∑ z, p z * f z + c ^ 2 * ∑ z, p z := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro z _; ring
  rw [e, hp1]; ring

lemma fv_centered (p : Ω → ℝ) (hp1 : ∑ y, p y = 1) (f : Ω → ℝ) :
    finiteVar p f = ∑ z, p z * (f z - finiteExp p f) ^ 2 := by
  rw [fv_shift p hp1 f (finiteExp p f)]
  simp only [finiteExp]
  ring

lemma fv_nonneg (p : Ω → ℝ) (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) (f : Ω → ℝ) :
    0 ≤ finiteVar p f := by
  rw [fv_centered p hp1 f]
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (hp0 z) (sq_nonneg _))

/-- Minkowski for standard deviations: `std f ≤ std g + std (g - f)`. -/
lemma fv_std_le (p : Ω → ℝ) (hp0 : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) (f g : Ω → ℝ) :
    Real.sqrt (finiteVar p f) ≤
      Real.sqrt (finiteVar p g) + Real.sqrt (finiteVar p (fun y => g y - f y)) := by
  have hm : finiteExp p (fun y => g y - f y) = finiteExp p g - finiteExp p f := by
    simp only [finiteExp]; rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro z _; ring
  set mg := finiteExp p g with hmg
  set mf := finiteExp p f with hmf
  set X : Ω → ℝ := fun z => Real.sqrt (p z) * (g z - mg) with hX
  set Y : Ω → ℝ := fun z => Real.sqrt (p z) * ((g z - f z) - (mg - mf)) with hY
  have hVg : finiteVar p g = ∑ z, X z ^ 2 := by
    rw [fv_centered p hp1 g, ← hmg]
    apply Finset.sum_congr rfl; intro z _
    simp only [hX]; rw [mul_pow, Real.sq_sqrt (hp0 z)]
  have hVd : finiteVar p (fun y => g y - f y) = ∑ z, Y z ^ 2 := by
    rw [fv_centered p hp1, hm]
    apply Finset.sum_congr rfl; intro z _
    simp only [hY]; rw [mul_pow, Real.sq_sqrt (hp0 z)]
  have hVf : finiteVar p f = ∑ z, (X z - Y z) ^ 2 := by
    rw [fv_centered p hp1 f, ← hmf]
    apply Finset.sum_congr rfl; intro z _
    simp only [hX, hY]
    have h := Real.sq_sqrt (hp0 z)
    linear_combination (-(f z - mf) ^ 2) * h
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ X (fun z => -Y z)
  have e2 : ∑ z, (-Y z) ^ 2 = ∑ z, Y z ^ 2 := by simp [neg_sq]
  rw [e2] at hcs
  have e1 : ∑ z, (X z - Y z) ^ 2 = ∑ z, X z ^ 2 + 2 * ∑ z, X z * (-Y z) + ∑ z, Y z ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro z _; ring
  have ha := Real.sq_sqrt (Finset.sum_nonneg (fun z (_ : z ∈ Finset.univ) => sq_nonneg (X z)))
  have hb := Real.sq_sqrt (Finset.sum_nonneg (fun z (_ : z ∈ Finset.univ) => sq_nonneg (Y z)))
  rw [hVf, hVg, hVd]
  calc Real.sqrt (∑ z, (X z - Y z) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ z, X z ^ 2) + Real.sqrt (∑ z, Y z ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [e1, add_sq, ha, hb]
        linarith
    _ = _ := Real.sqrt_sq (by positivity)

lemma fv_le_mul (p : Ω → ℝ) (hp0 : ∀ y, 0 ≤ p y) (d : Ω → ℝ) (c : ℝ)
    (hd0 : ∀ y, 0 ≤ d y) (hdc : ∀ y, d y ≤ c) :
    finiteVar p d ≤ c * finiteExp p d := by
  simp only [finiteVar, finiteExp]
  have h1 : ∑ z, p z * d z ^ 2 ≤ ∑ z, p z * (c * d z) := by
    apply Finset.sum_le_sum; intro z _
    apply mul_le_mul_of_nonneg_left _ (hp0 z)
    have := mul_le_mul_of_nonneg_right (hdc z) (hd0 z)
    linarith
  have h2 : ∑ z, p z * (c * d z) = c * ∑ z, p z * d z := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
  linarith [sq_nonneg (∑ z, p z * d z)]

end FinVar

section Optimism

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma empP_nonneg (st : ModelState S A H) (x : S) (a : A) (y : S) : 0 ≤ empiricalP st x a y := by
  unfold empiricalP; positivity

lemma empP_sum (st : ModelState S A H) (x : S) (a : A) (hn : 0 < countSA st x a) :
    ∑ y, empiricalP st x a y = 1 := by
  unfold empiricalP
  rw [← Finset.sum_div]
  have e : ((countSA st x a : ℕ) : ℝ) = ∑ y, (st.triples x a y : ℝ) := by
    unfold countSA; push_cast; rfl
  rw [← e]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr hn))

lemma emp_lin (st : ModelState S A H) (x : S) (a : A) (f g : S → ℝ) :
    empiricalExp st x a g = empiricalExp st x a f + empiricalExp st x a (fun y => g y - f y) := by
  unfold empiricalExp finiteExp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z _; ring

/-- The per-step optimism inequality with the empirical quantities of a model state. -/
lemma opt_core (M : Hoeffding.MDP S A) (st : ModelState S A H) (x : S) (a : A) (f nV : S → ℝ)
    (ℓ La : ℝ) (hH : 0 < H) (hn : 0 < countSA st x a) (hℓ : 0 ≤ ℓ) (hℓLa : ℓ ≤ 3 / 2 * La)
    (hf0 : ∀ y, 0 ≤ f y) (hfH : ∀ y, f y ≤ H) (hfn : ∀ y, f y ≤ nV y) (hnH : ∀ y, nV y ≤ H)
    (hE1 : Pexp M x a f - empiricalExp st x a f ≤
      Real.sqrt (2 * cvar M x a f * ℓ / (countSA st x a : ℝ)) +
        H * ℓ / (3 * (countSA st x a : ℝ)))
    (hE2 : Pexp M x a f - empiricalExp st x a f ≤
      H * Real.sqrt (ℓ / (2 * (countSA st x a : ℝ))))
    (hE3 : Pexp M x a (csq M x a f) - empiricalExp st x a (csq M x a f) ≤
      Real.sqrt (2 * cW M x a f * ℓ / (countSA st x a : ℝ))) :
    Pexp M x a f - empiricalExp st x a f ≤
      empiricalExp st x a (fun y => nV y - f y) +
        Real.sqrt (8 * La * empiricalVar st x a nV / (countSA st x a : ℝ)) +
        14 * H * La / (3 * (countSA st x a : ℝ)) := by
  have hn' : (0 : ℝ) < (countSA st x a : ℝ) := Nat.cast_pos.mpr hn
  have hH' : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hp0 : ∀ y, 0 ≤ empiricalP st x a y := fun y => empP_nonneg st x a y
  have hp1 : ∑ y, empiricalP st x a y = 1 := empP_sum st x a hn
  obtain ⟨hP0, hP1⟩ := M.kernel x a
  have hPf0 : 0 ≤ Pexp M x a f := Pexp_nonneg M x a f hf0
  have hPfH : Pexp M x a f ≤ H := Pexp_le M x a f H hfH
  have hcsq0 : ∀ y, 0 ≤ csq M x a f y := fun y => sq_nonneg _
  have hcsqH : ∀ y, csq M x a f y ≤ (H : ℝ) ^ 2 := by
    intro y
    unfold csq
    have a1 : 0 ≤ (H : ℝ) - f y + Pexp M x a f := by linarith [hfH y]
    have a2 : 0 ≤ (H : ℝ) + f y - Pexp M x a f := by linarith [hf0 y]
    nlinarith [mul_nonneg a1 a2]
  have hV0 : 0 ≤ cvar M x a f := Finset.sum_nonneg (fun y _ => mul_nonneg (hP0 y) (hcsq0 y))
  have hW : cW M x a f ≤ (H : ℝ) ^ 2 * cvar M x a f := by
    unfold cW cvar
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro y _
    have := mul_nonneg (mul_nonneg (hP0 y) (hcsq0 y)) (sub_nonneg.mpr (hcsqH y))
    nlinarith
  have hE3' : Pexp M x a (csq M x a f) - empiricalExp st x a (csq M x a f) ≤
      H * Real.sqrt (2 * cvar M x a f * ℓ / (countSA st x a : ℝ)) := by
    calc _ ≤ _ := hE3
      _ ≤ Real.sqrt ((H : ℝ) ^ 2 * (2 * cvar M x a f * ℓ / (countSA st x a : ℝ))) := by
          apply Real.sqrt_le_sqrt
          rw [show (H : ℝ) ^ 2 * (2 * cvar M x a f * ℓ / (countSA st x a : ℝ)) =
            2 * ((H : ℝ) ^ 2 * cvar M x a f) * ℓ / (countSA st x a : ℝ) by ring]
          apply div_le_div_of_nonneg_right _ hn'.le
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by norm_num)) hℓ
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hH'.le]
  have hvid : empiricalVar st x a f = empiricalExp st x a (csq M x a f) -
      (Pexp M x a f - empiricalExp st x a f) ^ 2 := by
    have h := fv_shift (empiricalP st x a) hp1 f (Pexp M x a f)
    show finiteVar (empiricalP st x a) f = _
    rw [h]
    show _ = finiteExp (empiricalP st x a) (csq M x a f) - _
    unfold csq
    unfold empiricalExp
    ring
  have hvh0 : 0 ≤ empiricalVar st x a f := fv_nonneg (empiricalP st x a) hp0 hp1 f
  have hcv : Pexp M x a (csq M x a f) = cvar M x a f := rfl
  have hvh : cvar M x a f - H * Real.sqrt (2 * cvar M x a f * ℓ / (countSA st x a : ℝ)) -
      (Pexp M x a f - empiricalExp st x a f) ^ 2 ≤ empiricalVar st x a f := by
    rw [hvid]; rw [hcv] at hE3'; linarith
  have hstd : Real.sqrt (empiricalVar st x a f) ≤
      Real.sqrt (empiricalVar st x a nV) + Real.sqrt (empiricalVar st x a (fun y => nV y - f y)) :=
    fv_std_le (empiricalP st x a) hp0 hp1 f nV
  have hu : Real.sqrt (empiricalVar st x a (fun y => nV y - f y)) ^ 2 ≤
      H * empiricalExp st x a (fun y => nV y - f y) := by
    have hnn : 0 ≤ empiricalVar st x a (fun y => nV y - f y) := fv_nonneg (empiricalP st x a) hp0 hp1 _
    rw [Real.sq_sqrt hnn]
    exact fv_le_mul (empiricalP st x a) hp0 _ _ (fun y => sub_nonneg.mpr (hfn y))
      (fun y => by linarith [hnH y, hf0 y])
  have key := opt_step (H : ℝ) (countSA st x a : ℝ) ℓ La (cvar M x a f)
    (Pexp M x a f - empiricalExp st x a f) (empiricalVar st x a f)
    (Real.sqrt (empiricalVar st x a nV)) (Real.sqrt (empiricalVar st x a (fun y => nV y - f y)))
    (empiricalExp st x a (fun y => nV y - f y)) hH' hn' hℓ hℓLa hV0 hvh0 hE1 hE2 hvh
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hstd hu
  have hnn2 : 0 ≤ empiricalVar st x a nV := fv_nonneg (empiricalP st x a) hp0 hp1 nV
  rwa [Real.sq_sqrt hnn2] at key

/-- Next-step value used inside `qAt`. -/
noncomputable def nextV (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (h : ℕ) : S → ℝ :=
  fun y => if _hn : h + 1 < H then ⨆ a' : A, qAt M st δ K (h + 1) y a' else 0

lemma qAt_eq (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) (h : ℕ)
    (hh : h < H) (x : S) (a : A) (hc : ¬ countSA st x a = 0) :
    qAt M st δ K h x a = min (min (st.previousQ ⟨h, hh⟩ x a) (H : ℝ))
      (M.R x a + empiricalExp st x a (nextV M st δ K h) +
        bonus st δ K ⟨h, hh⟩ x a (nextV M st δ K h)) := by
  rw [qAt, dif_pos hh, if_neg hc]
  rfl

lemma qAt_le (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) (h : ℕ)
    (x : S) (a : A) : qAt M st δ K h x a ≤ H := by
  by_cases hh : h < H
  · by_cases hc : countSA st x a = 0
    · rw [qAt, dif_pos hh, if_pos hc]
    · rw [qAt_eq M st δ K h hh x a hc]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
  · rw [qAt, dif_neg hh]; positivity

lemma nextV_le (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) (h : ℕ)
    (y : S) : nextV M st δ K h y ≤ H := by
  unfold nextV
  split_ifs
  · exact ciSup_le (fun a' => qAt_le M st δ K (h + 1) y a')
  · positivity

/-- Bellman upper bound for the supremum value. -/
lemma opt_bellman (M : Hoeffding.MDP S A) (H h : ℕ) (hh : h < H) (x : S) :
    optimalValue M H h x ≤
      ⨆ a : A, (M.R x a + Pexp M x a (fun y => optimalValue M H (h + 1) y)) := by
  apply ciSup_le
  intro π
  rw [valueAt, dif_pos hh]
  show M.R x (π x ⟨h, hh⟩) + ∑ y, M.P x (π x ⟨h, hh⟩) y * valueAt M π (h + 1) y ≤ _
  refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove (π x ⟨h, hh⟩))
  have hs : ∑ y, M.P x (π x ⟨h, hh⟩) y * valueAt M π (h + 1) y ≤
      Pexp M x (π x ⟨h, hh⟩) (fun y => optimalValue M H (h + 1) y) := by
    unfold Pexp
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (valueAt_le_opt M π (h + 1) y) ((M.kernel _ _).1 y)
  linarith

lemma qstar_le (M : Hoeffding.MDP S A) (H : ℕ) (h : Fin H) (x : S) (a : A) :
    M.R x a + Pexp M x a (vstar M H h) ≤ H := by
  have h1 : Pexp M x a (vstar M H h) ≤ ((H - (h.val + 1) : ℕ) : ℝ) :=
    Pexp_le M x a _ _ (fun y => opt_le M H (h.val + 1) y)
  have h2 : ((H - (h.val + 1) : ℕ) : ℝ) = (H : ℝ) - (h.val + 1) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h3 := (M.reward_mem x a).2
  have h4 : (0 : ℝ) ≤ h.val := Nat.cast_nonneg _
  linarith

/-- One backward step of optimism for a fixed model state. -/
lemma opt_hstep (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) (ℓ : ℝ)
    (hH : 0 < H) (hℓ : 0 ≤ ℓ)
    (hℓLa : ℓ ≤ 3 / 2 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (hprev : ∀ (h : Fin H) (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H h) ≤ st.previousQ h x a)
    (hgood : ∀ (x : S) (a : A) (h : Fin H), 0 < countSA st x a →
      (Pexp M x a (vstar M H h) - empiricalExp st x a (vstar M H h) ≤
        Real.sqrt (2 * cvar M x a (vstar M H h) * ℓ / (countSA st x a : ℝ)) +
          H * ℓ / (3 * (countSA st x a : ℝ))) ∧
      (Pexp M x a (vstar M H h) - empiricalExp st x a (vstar M H h) ≤
        H * Real.sqrt (ℓ / (2 * (countSA st x a : ℝ)))) ∧
      (Pexp M x a (csq M x a (vstar M H h)) - empiricalExp st x a (csq M x a (vstar M H h)) ≤
        Real.sqrt (2 * cW M x a (vstar M H h) * ℓ / (countSA st x a : ℝ))))
    (h : ℕ) (hh : h < H) (hnext : ∀ y, vstar M H ⟨h, hh⟩ y ≤ nextV M st δ K h y)
    (x : S) (a : A) :
    M.R x a + Pexp M x a (vstar M H ⟨h, hh⟩) ≤ qAt M st δ K h x a := by
  by_cases hc : countSA st x a = 0
  · rw [qAt, dif_pos hh, if_pos hc]
    exact qstar_le M H ⟨h, hh⟩ x a
  rw [qAt_eq M st δ K h hh x a hc]
  refine le_min (le_min (hprev ⟨h, hh⟩ x a) (qstar_le M H ⟨h, hh⟩ x a)) ?_
  have hn : 0 < countSA st x a := Nat.pos_of_ne_zero hc
  obtain ⟨e1, e2, e3⟩ := hgood x a ⟨h, hh⟩ hn
  have core := opt_core M st x a (vstar M H ⟨h, hh⟩) (nextV M st δ K h) ℓ
    (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) hH hn hℓ hℓLa
    (vstar_nonneg M H _) (vstar_le M H _) hnext (nextV_le M st δ K h) e1 e2 e3
  have lin := emp_lin st x a (vstar M H ⟨h, hh⟩) (nextV M st δ K h)
  have hb : Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H *
        empiricalVar st x a (nextV M st δ K h) / (countSA st x a : ℝ)) +
      14 * H * algorithmLog δ (Fintype.card S) (Fintype.card A) K H /
        (3 * (countSA st x a : ℝ)) ≤ bonus st δ K ⟨h, hh⟩ x a (nextV M st δ K h) := by
    unfold bonus
    simp only
    linarith [Real.sqrt_nonneg (8 * empiricalExp st x a
      (extraCap st (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) ⟨h, hh⟩) /
        (countSA st x a : ℝ))]
  unfold Pexp at core ⊢
  linarith

/-- Optimism for a fixed model state, by backward induction on the step. -/
theorem opt_state (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) (ℓ : ℝ)
    (hH : 0 < H) (hℓ : 0 ≤ ℓ)
    (hℓLa : ℓ ≤ 3 / 2 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (hprev : ∀ (h : Fin H) (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H h) ≤ st.previousQ h x a)
    (hgood : ∀ (x : S) (a : A) (h : Fin H), 0 < countSA st x a →
      (Pexp M x a (vstar M H h) - empiricalExp st x a (vstar M H h) ≤
        Real.sqrt (2 * cvar M x a (vstar M H h) * ℓ / (countSA st x a : ℝ)) +
          H * ℓ / (3 * (countSA st x a : ℝ))) ∧
      (Pexp M x a (vstar M H h) - empiricalExp st x a (vstar M H h) ≤
        H * Real.sqrt (ℓ / (2 * (countSA st x a : ℝ)))) ∧
      (Pexp M x a (csq M x a (vstar M H h)) - empiricalExp st x a (csq M x a (vstar M H h)) ≤
        Real.sqrt (2 * cW M x a (vstar M H h) * ℓ / (countSA st x a : ℝ)))) :
    ∀ (h : Fin H) (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H h) ≤ qAt M st δ K h.val x a := by
  have main : ∀ j : ℕ, ∀ (h : ℕ) (hh : h < H), h + j = H - 1 → ∀ (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H ⟨h, hh⟩) ≤ qAt M st δ K h x a := by
    intro j
    induction j with
    | zero =>
      intro h hh hj x a
      apply opt_hstep M st δ K ℓ hH hℓ hℓLa hprev hgood h hh _ x a
      intro y
      have hn : ¬ (h + 1 < H) := by omega
      have h1 := opt_le M H (h + 1) y
      have h2 : H - (h + 1) = 0 := by omega
      rw [h2] at h1
      unfold nextV vstar
      rw [dif_neg hn]
      simpa using h1
    | succ j ih =>
      intro h hh hj x a
      apply opt_hstep M st δ K ℓ hH hℓ hℓLa hprev hgood h hh _ x a
      intro y
      have hn : h + 1 < H := by omega
      have ih' := ih (h + 1) hn (by omega)
      unfold nextV vstar
      rw [dif_pos hn]
      refine le_trans (opt_bellman M H (h + 1) hn y) ?_
      apply ciSup_mono (Set.finite_range _).bddAbove
      intro a'
      exact ih' y a'
  intro h x a
  exact main (H - 1 - h.val) h.val h.isLt (by omega) x a

/-- Optimism along the run on the good event. -/
theorem optimism (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ℓ : ℝ) (hH : 0 < H) (hℓ : 0 ≤ ℓ)
    (hℓLa : ℓ ≤ 3 / 2 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (ω : Hoeffding.Outcomes S K H) (hG : GoodOpt M δ sel init ℓ ω) :
    ∀ k : ℕ, k < K → ∀ (h : Fin H) (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H h) ≤
        qAt M (runState M δ K H sel init ω k) δ K h.val x a := by
  intro k
  induction k with
  | zero =>
    intro hk
    apply opt_state M _ δ K ℓ hH hℓ hℓLa
    · intro h x a
      exact qstar_le M H h x a
    · exact fun x a h hn => hG ⟨0, hk⟩ x a h hn
  | succ k ih =>
    intro hk
    apply opt_state M _ δ K ℓ hH hℓ hℓLa
    · intro h x a
      have hk' : k < K := by omega
      have e : (runState M δ K H sel init ω (k + 1)).previousQ =
          episodeQ M (runState M δ K H sel init ω k) δ K := by
        rw [runState, dif_pos hk']
        rfl
      rw [e]
      exact ih hk' h x a
    · exact fun x a h hn => hG ⟨k + 1, hk⟩ x a h hn

end Optimism

section Azuma

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

/-- Martingale increment: conditional mean minus realised value of `F k h ω ·`. -/
noncomputable def mInc (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (F : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ)
    (k : Fin K) (h : Fin H) (ω : Hoeffding.Outcomes S K H) : ℝ :=
  ∑ y, qP M δ K H sel init k h ω y * F k h ω y - F k h ω (ω k h)

/-- Azuma–Hoeffding for the run: increments of predictable, range-`w` statistics. -/
theorem azuma (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (F : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ)
    (hF : ∀ k h, Adapted (k.val * H + h.val) (F k h))
    (lo : Fin K → Fin H → Hoeffding.Outcomes S K H → ℝ) (w : ℝ) (hw : 0 < w)
    (hb : ∀ k h ω y, F k h ω y ∈ Set.Icc (lo k h ω) (lo k h ω + w))
    (ℓ : ℝ) (hℓ : 0 < ℓ) (hKH : 0 < K * H) :
    probEvent M δ K H sel init (fun ω => w * Real.sqrt (K * H * ℓ / 2) <
      ∑ p : Fin K × Fin H, mInc M δ sel init F p.1 p.2 ω) ≤ Real.exp (-ℓ) := by
  have hN0 : (0 : ℝ) < (K : ℝ) * H := by exact_mod_cast hKH
  have hKr : (K : ℝ) ≠ 0 := by
    have : 0 < K := Nat.pos_of_ne_zero (by rintro rfl; simp at hKH)
    positivity
  have hHr : (H : ℝ) ≠ 0 := by
    have : 0 < H := Nat.pos_of_ne_zero (by rintro rfl; simp at hKH)
    positivity
  set τ0 := w * Real.sqrt ((K : ℝ) * H * ℓ / 2) with hτ0
  set t := 4 * τ0 / ((K : ℝ) * H * w ^ 2) with ht
  have ht0 : 0 ≤ t := by positivity
  let u : Fin K → Fin H → Hoeffding.Outcomes S K H → ℝ := fun k h ω =>
    t * mInc M δ sel init F k h ω - t ^ 2 * w ^ 2 / 8
  have hu : ∀ k h, Adapted (k.val * H + h.val + 1) (u k h) := by
    intro k h ω ω' hag
    have hag1 : Agree (k.val * H + h.val) ω ω' := hag.mono (Nat.le_succ _)
    simp only [u, mInc]
    rw [qP_adapted M δ sel init k h ω ω' hag1, hF k h ω ω' hag1, hag k h (Nat.lt_succ_self _)]
  have hstep : ∀ k h ω,
      ∑ y, qP M δ K H sel init k h ω y * Real.exp (u k h (upd ω k h y)) ≤ 1 := by
    intro k h ω
    have ag := agree_upd ω k h
    set p := qP M δ K H sel init k h ω with hp
    set g : S → ℝ := fun z => -F k h ω z with hg
    have hrel : ∀ y, u k h (upd ω k h y) =
        t * (g y - ∑ z, p z * g z) - t ^ 2 * w ^ 2 / 8 := by
      intro y
      simp only [u, mInc]
      rw [← qP_adapted M δ sel init k h ω (upd ω k h y) (ag y),
        ← hF k h ω (upd ω k h y) (ag y), upd_self, ← hp]
      have e : ∑ z, p z * g z = -∑ z, p z * F k h ω z := by
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro z _
        simp only [hg]; ring
      rw [e]; simp only [hg]; ring
    have hgm : ∀ y, g y ∈ Set.Icc (-(lo k h ω + w)) (-(lo k h ω)) := by
      intro y
      obtain ⟨c0, c1⟩ := hb k h ω y
      simp only [hg, Set.mem_Icc]
      constructor <;> linarith
    have hhf := hoeffding_fin p (qP_nonneg M δ sel init k h ω) (qP_sum M δ sel init k h ω)
      g _ _ hgm t
    calc ∑ y, p y * Real.exp (u k h (upd ω k h y))
        = ∑ y, p y * Real.exp (t * (g y - ∑ z, p z * g z) - t ^ 2 * w ^ 2 / 8) := by
          apply Finset.sum_congr rfl; intro y _; rw [hrel y]
      _ = Real.exp (-(t ^ 2 * w ^ 2 / 8)) *
          ∑ y, p y * Real.exp (t * (g y - ∑ z, p z * g z)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          rw [sub_eq_add_neg (t * (g y - ∑ z, p z * g z)), Real.exp_add]
          ring
      _ ≤ Real.exp (-(t ^ 2 * w ^ 2 / 8)) *
          Real.exp (t ^ 2 * (-lo k h ω - -(lo k h ω + w)) ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hhf (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add]
          rw [show -(t ^ 2 * w ^ 2 / 8) + t ^ 2 * (-lo k h ω - -(lo k h ω + w)) ^ 2 / 8 = 0 by
            ring]
          exact Real.exp_zero
  have hmain := exp_sum_le M δ sel init u hu hstep
  have hc : 0 < Real.exp ℓ := Real.exp_pos _
  have hmk := probEvent_le_markov M δ sel init (fun ω => w * Real.sqrt (K * H * ℓ / 2) <
      ∑ p : Fin K × Fin H, mInc M δ sel init F p.1 p.2 ω)
    (fun ω => Real.exp (∑ p : Fin K × Fin H, u p.1 p.2 ω)) _ hc
    (fun ω => (Real.exp_pos _).le) (by
      intro ω hω
      apply Real.exp_le_exp.mpr
      have hsum : ∑ p : Fin K × Fin H, u p.1 p.2 ω =
          t * (∑ p : Fin K × Fin H, mInc M δ sel init F p.1 p.2 ω) -
            ((K : ℝ) * H) * (t ^ 2 * w ^ 2 / 8) := by
        simp only [u]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
      rw [hsum]
      have hτsq : τ0 ^ 2 = w ^ 2 * ((K : ℝ) * H * ℓ / 2) := by
        rw [hτ0, mul_pow, Real.sq_sqrt (by positivity)]
      have hkey : t * τ0 - ((K : ℝ) * H) * (t ^ 2 * w ^ 2 / 8) = ℓ := by
        rw [ht]
        field_simp
        rw [hτsq]
        field_simp
        ring
      have h1 : t * τ0 ≤ t * (∑ p : Fin K × Fin H, mInc M δ sel init F p.1 p.2 ω) :=
        mul_le_mul_of_nonneg_left hω.le ht0
      linarith)
  have h1 := le_trans hmk hmain
  rw [Real.exp_neg, ← one_div, le_div_iff₀ hc]
  linarith

end Azuma

section GapCore

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma Pexp_sub (M : Hoeffding.MDP S A) (x : S) (a : A) (f g : S → ℝ) :
    Pexp M x a (fun y => g y - f y) = Pexp M x a g - Pexp M x a f := by
  unfold Pexp; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro z _; ring

lemma Pexp_mono (M : Hoeffding.MDP S A) (x : S) (a : A) (f g : S → ℝ)
    (hfg : ∀ y, f y ≤ g y) : Pexp M x a f ≤ Pexp M x a g :=
  Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hfg z) ((M.kernel x a).1 z))

lemma fv_swap {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (f g : Ω → ℝ) :
    finiteVar p (fun y => f y - g y) = finiteVar p (fun y => g y - f y) := by
  simp only [finiteVar, finiteExp]
  have h1 : ∑ z, p z * (f z - g z) = -∑ z, p z * (g z - f z) := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro z _; ring
  have h2 : ∑ z, p z * (f z - g z) ^ 2 = ∑ z, p z * (g z - f z) ^ 2 := by
    apply Finset.sum_congr rfl; intro z _; ring
  rw [h1, h2]; ring

lemma cvar_eq (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) :
    cvar M x a f = finiteVar (M.P x a) f := by
  rw [fv_centered (M.P x a) (M.kernel x a).2 f]; rfl

lemma csq_le (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) (c : ℝ)
    (hf0 : ∀ y, 0 ≤ f y) (hfc : ∀ y, f y ≤ c) (y : S) : csq M x a f y ≤ c ^ 2 := by
  have hP0 : 0 ≤ Pexp M x a f := Pexp_nonneg M x a f hf0
  have hPc : Pexp M x a f ≤ c := Pexp_le M x a f c hfc
  unfold csq
  have a1 : 0 ≤ c - f y + Pexp M x a f := by linarith [hfc y]
  have a2 : 0 ≤ c + f y - Pexp M x a f := by linarith [hf0 y]
  nlinarith [mul_nonneg a1 a2]

lemma cW_le (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) (c : ℝ)
    (hc : ∀ y, csq M x a f y ≤ c) : cW M x a f ≤ c * cvar M x a f := by
  unfold cW cvar
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro y _
  have := mul_nonneg (mul_nonneg ((M.kernel x a).1 y) (sq_nonneg (f y - Pexp M x a f)))
    (sub_nonneg.mpr (hc y))
  unfold csq at this ⊢
  nlinarith

lemma sqrt_frac (u X n : ℝ) (hu : 0 ≤ u) (hn : 0 ≤ n) :
    Real.sqrt (u * X / n) = Real.sqrt u * Real.sqrt X / Real.sqrt n := by
  rw [Real.sqrt_div' _ hn, Real.sqrt_mul hu]

/-- Second-order constant of the gap step. -/
noncomputable def gBeta (H S ℓ La lam c : ℝ) : ℝ :=
  H * ℓ / 3 + S * H * ℓ / lam + H * Real.sqrt (2 * ℓ) * Real.sqrt (8 * La) / 2 +
    H * Real.sqrt (8 * La) * Real.sqrt (S * ℓ / lam) + 14 * H * La / 3 +
    c * (Real.sqrt (2 * ℓ) + 5 / 2 * Real.sqrt (8 * La)) ^ 2 * H ^ 2 / 4

lemma amgm_q (q PG κ m c H : ℝ) (hm : 0 < m) (hc : 0 < c) (hH : 0 < H)
    (hq : q ^ 2 = H * PG) (hκ : 0 ≤ κ) (hq0 : 0 ≤ q) :
    κ * q / m ≤ PG / (c * H) + c * κ ^ 2 * H ^ 2 / 4 / m ^ 2 := by
  have h1 := sq_nonneg (q - c * H ^ 2 * κ / (2 * m))
  have e : PG / (c * H) + c * κ ^ 2 * H ^ 2 / 4 / m ^ 2 - κ * q / m =
      (q - c * H ^ 2 * κ / (2 * m)) ^ 2 / (c * H ^ 2) := by
    have hPG : PG = q ^ 2 / H := by rw [hq]; field_simp
    rw [hPG]; field_simp; ring
  have h2 : 0 ≤ (q - c * H ^ 2 * κ / (2 * m)) ^ 2 / (c * H ^ 2) := by positivity
  linarith

end GapCore

section GapCore2

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

set_option maxHeartbeats 1000000 in
/-- The per-step gap inequality (blueprint §2) for one row, before the extraCap term. -/
lemma gap_core (M : Hoeffding.MDP S A) (st : ModelState S A H) (x : S) (a : A) (f g v : S → ℝ)
    (ℓ La η lam c : ℝ) (hH : 0 < H) (hn : 0 < countSA st x a) (hℓ : 0 ≤ ℓ) (hLa : 0 ≤ La)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 < lam) (hc : 0 < c)
    (hv0 : ∀ y, 0 ≤ v y) (hvf : ∀ y, v y ≤ f y) (hfg : ∀ y, f y ≤ g y) (hgH : ∀ y, g y ≤ H)
    (hR1 : empiricalExp st x a f - Pexp M x a f ≤
      Real.sqrt (2 * cvar M x a f * ℓ / (countSA st x a : ℝ)) +
        H * ℓ / (3 * (countSA st x a : ℝ)))
    (hR2 : empiricalExp st x a (csq M x a f) - Pexp M x a (csq M x a f) ≤
      Real.sqrt (2 * cW M x a f * ℓ / (countSA st x a : ℝ)) +
        (H : ℝ) ^ 2 * ℓ / (3 * (countSA st x a : ℝ)))
    (hGB : ∀ y, empiricalP st x a y - M.P x a y ≤
      η * M.P x a y + ℓ / (lam * (countSA st x a : ℝ))) :
    empiricalExp st x a g +
        Real.sqrt (8 * La * empiricalVar st x a g / (countSA st x a : ℝ)) +
        14 * H * La / (3 * (countSA st x a : ℝ)) - Pexp M x a v ≤
      (1 + η + 1 / (c * H)) * Pexp M x a (fun y => g y - v y) +
        (Real.sqrt (2 * ℓ) + Real.sqrt (8 * La)) * Real.sqrt (cvar M x a v) /
          Real.sqrt (countSA st x a : ℝ) +
        gBeta H (Fintype.card S) ℓ La lam c / (countSA st x a : ℝ) := by
  unfold gBeta
  have hn' : (0 : ℝ) < (countSA st x a : ℝ) := Nat.cast_pos.mpr hn
  have hH' : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  set n : ℝ := (countSA st x a : ℝ) with hndef
  set m := Real.sqrt n with hmdef
  have hm : 0 < m := Real.sqrt_pos.mpr hn'
  have hm2 : m ^ 2 = n := Real.sq_sqrt hn'.le
  have hp0 : ∀ y, 0 ≤ empiricalP st x a y := fun y => empP_nonneg st x a y
  have hp1 : ∑ y, empiricalP st x a y = 1 := empP_sum st x a hn
  obtain ⟨hP0, hP1⟩ := M.kernel x a
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_trans (hv0 y) (hvf y)
  have hfH : ∀ y, f y ≤ H := fun y => le_trans (hfg y) (hgH y)
  have hΔ0 : ∀ y, 0 ≤ g y - f y := fun y => sub_nonneg.mpr (hfg y)
  have hΔH : ∀ y, g y - f y ≤ H := fun y => by linarith [hgH y, hf0 y]
  have hΔG : ∀ y, g y - f y ≤ g y - v y := fun y => by linarith [hvf y]
  -- decomposition
  have e1 : empiricalExp st x a g =
      empiricalExp st x a f + empiricalExp st x a (fun y => g y - f y) := emp_lin st x a f g
  have e2 : Pexp M x a v = Pexp M x a f + Pexp M x a (fun y => g y - f y) -
      Pexp M x a (fun y => g y - v y) := by
    rw [Pexp_sub, Pexp_sub]; ring
  set PG := Pexp M x a (fun y => g y - v y) with hPG
  set PΔ := Pexp M x a (fun y => g y - f y) with hPΔ
  set EΔ := empiricalExp st x a (fun y => g y - f y) with hEΔ
  have hPG0 : 0 ≤ PG := Pexp_nonneg M x a _ (fun y => le_trans (hΔ0 y) (hΔG y))
  have hPΔ0 : 0 ≤ PΔ := Pexp_nonneg M x a _ hΔ0
  have hPΔG : PΔ ≤ PG := Pexp_mono M x a _ _ hΔG
  -- Bennett transfer for Δ
  have hDΔ : EΔ - PΔ ≤ η * PΔ + (Fintype.card S : ℝ) * H * ℓ / lam / n := by
    have e : EΔ - PΔ = ∑ y, (empiricalP st x a y - M.P x a y) * (g y - f y) := by
      rw [hEΔ, hPΔ]
      unfold empiricalExp finiteExp Pexp
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro z _; ring
    rw [e]
    have hsumΔ : ∑ y, (g y - f y) ≤ (Fintype.card S : ℝ) * H := by
      calc ∑ y, (g y - f y) ≤ ∑ _y : S, (H : ℝ) := Finset.sum_le_sum (fun y _ => hΔH y)
        _ = _ := by simp
    have hl0 : 0 ≤ ℓ / (lam * n) := div_nonneg hℓ (by positivity)
    have h1 : ∑ y, (empiricalP st x a y - M.P x a y) * (g y - f y)
        ≤ ∑ y, (η * M.P x a y + ℓ / (lam * n)) * (g y - f y) :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hGB y) (hΔ0 y))
    have h2 : ∑ y, (η * M.P x a y + ℓ / (lam * n)) * (g y - f y) =
        η * PΔ + ℓ / (lam * n) * ∑ y, (g y - f y) := by
      rw [hPΔ]; unfold Pexp
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro z _; ring
    have h3 := mul_le_mul_of_nonneg_left hsumΔ hl0
    have h4 : ℓ / (lam * n) * ((Fintype.card S : ℝ) * H) =
        (Fintype.card S : ℝ) * H * ℓ / lam / n := by
      field_simp
    linarith
  have hEΔle : EΔ ≤ 2 * PG + (Fintype.card S : ℝ) * H * ℓ / lam / n := by
    have := mul_le_mul_of_nonneg_right hη1 hPΔ0
    linarith
  -- standard deviations
  set a1 := Real.sqrt (2 * ℓ) with ha1
  set b0 := Real.sqrt (8 * La) with hb0
  have ha10 : 0 ≤ a1 := Real.sqrt_nonneg _
  have hb00 : 0 ≤ b0 := Real.sqrt_nonneg _
  have ha12 : a1 ^ 2 = 2 * ℓ := Real.sq_sqrt (by linarith)
  set z0 := Real.sqrt ((Fintype.card S : ℝ) * ℓ / lam) with hz0
  have hz00 : 0 ≤ z0 := Real.sqrt_nonneg _
  have hz02 : z0 ^ 2 = (Fintype.card S : ℝ) * ℓ / lam :=
    Real.sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hℓ) hlam.le)
  set q := Real.sqrt (H * PG) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = H * PG := Real.sq_sqrt (mul_nonneg hH'.le hPG0)
  set s := Real.sqrt (cvar M x a f) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hcv0 : 0 ≤ cvar M x a f := by rw [cvar_eq]; exact fv_nonneg _ hP0 hP1 f
  have hs2 : s ^ 2 = cvar M x a f := Real.sq_sqrt hcv0
  set w := Real.sqrt (cvar M x a v) with hw
  set sf := Real.sqrt (empiricalVar st x a f) with hsf
  set sg := Real.sqrt (empiricalVar st x a g) with hsg
  set sΔ := Real.sqrt (empiricalVar st x a (fun y => g y - f y)) with hsΔ
  -- (a) sg ≤ sf + sΔ
  have h_sg : sg ≤ sf + sΔ := by
    have h := fv_std_le (empiricalP st x a) hp0 hp1 g f
    rw [fv_swap] at h
    rw [hsg, hsf, hsΔ]
    exact h
  -- (b) sΔ ≤ √(H EΔ) ≤ 3/2 q + H z0 / m
  have h_sΔ : sΔ ≤ 3 / 2 * q + H * z0 / m := by
    have hb1 : sΔ ≤ Real.sqrt (H * EΔ) := by
      rw [hsΔ, hEΔ]
      exact Real.sqrt_le_sqrt (fv_le_mul (empiricalP st x a) hp0 _ H hΔ0 hΔH)
    have hnn : 0 ≤ 3 / 2 * q + H * z0 / m :=
      add_nonneg (by linarith) (div_nonneg (mul_nonneg hH'.le hz00) hm.le)
    have hb2 : Real.sqrt (H * EΔ) ≤ 3 / 2 * q + H * z0 / m := by
      rw [show (3 / 2 * q + H * z0 / m) = Real.sqrt ((3 / 2 * q + H * z0 / m) ^ 2) from
        (Real.sqrt_sq hnn).symm]
      apply Real.sqrt_le_sqrt
      have e : (H * z0 / m) ^ 2 = H * ((Fintype.card S : ℝ) * H * ℓ / lam / n) := by
        rw [div_pow, mul_pow, hz02, hm2]; field_simp
      have hqz : 0 ≤ q * (H * z0 / m) := mul_nonneg hq0 (div_nonneg (mul_nonneg hH'.le hz00) hm.le)
      have h3 := mul_le_mul_of_nonneg_left hEΔle hH'.le
      linarith [sq_nonneg q]
    linarith
  -- (c) sf ≤ s + H a1 / (2 m)
  have hvid : empiricalVar st x a f = empiricalExp st x a (csq M x a f) -
      (Pexp M x a f - empiricalExp st x a f) ^ 2 := by
    have h := fv_shift (empiricalP st x a) hp1 f (Pexp M x a f)
    show finiteVar (empiricalP st x a) f = _
    rw [h]
    show _ = finiteExp (empiricalP st x a) (csq M x a f) - _
    unfold csq
    unfold empiricalExp
    ring
  have hcW : Real.sqrt (cW M x a f) ≤ H * s := by
    have h := cW_le M x a f ((H : ℝ) ^ 2) (csq_le M x a f H hf0 hfH)
    calc Real.sqrt (cW M x a f) ≤ Real.sqrt ((H : ℝ) ^ 2 * cvar M x a f) := Real.sqrt_le_sqrt h
      _ = H * s := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hH'.le, ← hs]
  have hR2' : Real.sqrt (2 * cW M x a f * ℓ / n) = a1 * Real.sqrt (cW M x a f) / m := by
    rw [show 2 * cW M x a f * ℓ / n = (2 * ℓ) * cW M x a f / n by ring,
      sqrt_frac _ _ _ (by linarith) hn'.le, ← ha1, ← hmdef]
  have h_sf : sf ≤ s + H * a1 / (2 * m) := by
    have hnn : 0 ≤ s + H * a1 / (2 * m) :=
      add_nonneg hs0 (div_nonneg (mul_nonneg hH'.le ha10) (mul_nonneg (by norm_num) hm.le))
    rw [show s + H * a1 / (2 * m) = Real.sqrt ((s + H * a1 / (2 * m)) ^ 2) from
      (Real.sqrt_sq hnn).symm]
    rw [hsf]
    apply Real.sqrt_le_sqrt
    have hcsqP : Pexp M x a (csq M x a f) = s ^ 2 := by rw [hs2]; rfl
    rw [hvid]
    have h1 : a1 * Real.sqrt (cW M x a f) / m ≤ a1 * (H * s) / m :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcW ha10) hm.le
    have h2 : (H : ℝ) ^ 2 * ℓ / (3 * n) ≤ (H * a1 / (2 * m)) ^ 2 := by
      rw [div_pow, mul_pow, ha12, show (2 * m) ^ 2 = 4 * m ^ 2 by ring, hm2]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [mul_nonneg (mul_nonneg (sq_nonneg (H : ℝ)) hℓ) hn'.le]
    have ex : (s + H * a1 / (2 * m)) ^ 2 = s ^ 2 + a1 * (H * s) / m + (H * a1 / (2 * m)) ^ 2 := by
      field_simp; ring
    rw [hR2'] at hR2
    linarith [sq_nonneg (Pexp M x a f - empiricalExp st x a f)]
  -- (d) s ≤ w + q
  have h_s : s ≤ w + q := by
    have h := fv_std_le (M.P x a) hP0 hP1 f v
    rw [fv_swap] at h
    have hV : finiteVar (M.P x a) (fun y => f y - v y) ≤ H * PG := by
      calc finiteVar (M.P x a) (fun y => f y - v y)
          ≤ H * finiteExp (M.P x a) (fun y => f y - v y) :=
            fv_le_mul (M.P x a) hP0 _ H (fun y => sub_nonneg.mpr (hvf y))
              (fun y => by linarith [hfH y, hv0 y])
        _ ≤ H * PG := mul_le_mul_of_nonneg_left
            (Pexp_mono M x a _ _ (fun y => by linarith [hfg y])) hH'.le
    have h2 := Real.sqrt_le_sqrt hV
    rw [← hq] at h2
    have e1 : s = Real.sqrt (finiteVar (M.P x a) f) := by rw [hs, cvar_eq]
    have e2 : w = Real.sqrt (finiteVar (M.P x a) v) := by rw [hw, cvar_eq]
    rw [e1, e2]
    linarith
  -- assemble
  have hR1' : Real.sqrt (2 * cvar M x a f * ℓ / n) = a1 * s / m := by
    rw [show 2 * cvar M x a f * ℓ / n = (2 * ℓ) * cvar M x a f / n by ring,
      sqrt_frac _ _ _ (by linarith) hn'.le, ← ha1, ← hs, ← hmdef]
  rw [hR1'] at hR1
  have hB : Real.sqrt (8 * La * empiricalVar st x a g / n) = b0 * sg / m := by
    rw [sqrt_frac (8 * La) _ n (by linarith) hn'.le, ← hb0, ← hsg, ← hmdef]
  rw [hB]
  have hbm : 0 ≤ b0 / m := div_nonneg hb00 hm.le
  have ham : 0 ≤ a1 / m := div_nonneg ha10 hm.le
  have hbsg : b0 * sg / m ≤ b0 * w / m + 5 / 2 * (b0 * q / m) + H * a1 * b0 / 2 / n +
      H * b0 * z0 / n := by
    have hsum : sg ≤ w + 5 / 2 * q + H * a1 / (2 * m) + H * z0 / m := by linarith
    have h1 := mul_le_mul_of_nonneg_left hsum hbm
    have e : b0 / m * (w + 5 / 2 * q + H * a1 / (2 * m) + H * z0 / m) =
        b0 * w / m + 5 / 2 * (b0 * q / m) + H * a1 * b0 / 2 / n + H * b0 * z0 / n := by
      rw [← hm2]; field_simp
    calc b0 * sg / m = b0 / m * sg := by ring
      _ ≤ _ := h1
      _ = _ := e
  have has : a1 * s / m ≤ a1 * w / m + a1 * q / m := by
    have h1 := mul_le_mul_of_nonneg_left h_s ham
    have e : a1 / m * (w + q) = a1 * w / m + a1 * q / m := by ring
    calc a1 * s / m = a1 / m * s := by ring
      _ ≤ _ := h1
      _ = _ := e
  have hκ : 0 ≤ a1 + 5 / 2 * b0 := by linarith
  have hamgm := amgm_q q PG (a1 + 5 / 2 * b0) m c H hm hc hH' hq2 hκ hq0
  rw [hm2] at hamgm
  have eκ : (a1 + 5 / 2 * b0) * q / m = a1 * q / m + 5 / 2 * (b0 * q / m) := by ring
  have hηΔ : η * PΔ ≤ η * PG := mul_le_mul_of_nonneg_left hPΔG hη
  have eG : (1 + η + 1 / (c * H)) * PG = PG + η * PG + PG / (c * H) := by ring
  have r1 : (H : ℝ) * ℓ / (3 * n) = H * ℓ / 3 / n := by ring
  have r3 : 14 * (H : ℝ) * La / (3 * n) = 14 * H * La / 3 / n := by ring
  have ew : (a1 + b0) * w / m = a1 * w / m + b0 * w / m := by ring
  have eβ : (H * ℓ / 3 + (Fintype.card S : ℝ) * H * ℓ / lam + H * a1 * b0 / 2 +
      H * b0 * z0 + 14 * H * La / 3 + c * (a1 + 5 / 2 * b0) ^ 2 * H ^ 2 / 4) / n =
      H * ℓ / 3 / n + (Fintype.card S : ℝ) * H * ℓ / lam / n + H * a1 * b0 / 2 / n +
      H * b0 * z0 / n + 14 * H * La / 3 / n + c * (a1 + 5 / 2 * b0) ^ 2 * H ^ 2 / 4 / n := by
    ring
  rw [eG, ew, eβ, e1, e2]
  linarith

end GapCore2

section GapRun

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

/-- Estimated value `V_{k,h}(y) = max_a Q_{k,h}(y,a)`. -/
noncomputable def Vk (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) (h : ℕ)
    (y : S) : ℝ :=
  ⨆ a : A, qAt M st δ K h y a

lemma nextV_eq_Vk (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) (h : ℕ)
    (y : S) : nextV M st δ K h y = Vk M st δ K (h + 1) y := by
  unfold nextV Vk
  by_cases hh : h + 1 < H
  · rw [dif_pos hh]
  · rw [dif_neg hh]
    have e : ∀ a', qAt M st δ K (h + 1) y a' = 0 := fun a' => by rw [qAt, dif_neg hh]
    simp [e]

lemma Vk_le (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ) (h : ℕ) (y : S) :
    Vk M st δ K h y ≤ H :=
  ciSup_le (fun a => qAt_le M st δ K h y a)

lemma Vk_sel (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (h : ℕ) (y : S) :
    Vk M st δ K h y = qAt M st δ K h y (sel (fun a => qAt M st δ K h y a)) :=
  le_antisymm (ciSup_le (fun a => hsel _ a)) (le_ciSup (Set.finite_range _).bddAbove _)

/-- Optimism of the estimated values (from Q-optimism and the Bellman bound). -/
lemma opt_le_Vk (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (hopt : ∀ (h : Fin H) (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H h) ≤ qAt M st δ K h.val x a) (h : ℕ) (y : S) :
    optimalValue M H h y ≤ Vk M st δ K h y := by
  by_cases hh : h < H
  · refine le_trans (opt_bellman M H h hh y) ?_
    apply ciSup_mono (Set.finite_range _).bddAbove
    intro a
    exact hopt ⟨h, hh⟩ y a
  · have h1 := opt_le M H h y
    have h2 : H - h = 0 := by omega
    rw [h2] at h1
    have e : ∀ a', qAt M st δ K h y a' = 0 := fun a' => by rw [qAt, dif_neg hh]
    unfold Vk
    simp only [e, ciSup_const]
    simpa using h1

lemma vstar_le_nextV (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (hopt : ∀ (h : Fin H) (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H h) ≤ qAt M st δ K h.val x a) (h : ℕ) (hh : h < H)
    (y : S) : vstar M H ⟨h, hh⟩ y ≤ nextV M st δ K h y := by
  rw [nextV_eq_Vk]
  exact opt_le_Vk M st δ K hopt (h + 1) y

/-- The per-episode gap `V_{k,h} - V^{π}_h`. -/
noncomputable def gapF (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (π : Hoeffding.Policy S A H) (h : ℕ) (y : S) : ℝ :=
  Vk M st δ K h y - valueAt M π h y

lemma gapF_nonneg (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (hopt : ∀ (h : Fin H) (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H h) ≤ qAt M st δ K h.val x a)
    (π : Hoeffding.Policy S A H) (h : ℕ) (y : S) : 0 ≤ gapF M st δ K π h y := by
  unfold gapF
  linarith [opt_le_Vk M st δ K hopt h y, valueAt_le_opt M π h y]

lemma gapF_le (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (π : Hoeffding.Policy S A H) (h : ℕ) (y : S) : gapF M st δ K π h y ≤ H := by
  unfold gapF
  linarith [Vk_le M st δ K h y, valueAt_nonneg M π h y]

/-- The clipped first- and second-order part of the gap step. -/
noncomputable def Xt (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (π : Hoeffding.Policy S A H) (ℓ lam c : ℝ) (h : ℕ) (hh : h < H) (x : S) (a : A) : ℝ :=
  if countSA st x a = 0 then (H : ℝ) else
    min (H : ℝ)
      ((Real.sqrt (2 * ℓ) + Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)) *
          Real.sqrt (cvar M x a (valueAt M π (h + 1))) / Real.sqrt (countSA st x a : ℝ) +
        gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) lam c /
          (countSA st x a : ℝ) +
        Real.sqrt (8 * empiricalExp st x a
          (extraCap st (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) ⟨h, hh⟩) /
            (countSA st x a : ℝ)))

lemma min_add_le (H u X : ℝ) (hu : 0 ≤ u) : min H (u + X) ≤ u + min H X := by
  rcases le_total H X with hX | hX
  · rw [min_eq_left hX]; exact le_trans (min_le_left _ _) (by linarith)
  · rw [min_eq_right hX]; exact min_le_right _ _

/-- The gap step along any row (blueprint §2). -/
theorem gap_step (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (sel : (A → ℝ) → A) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (ℓ η lam c : ℝ) (hH : 0 < H) (hℓ : 0 ≤ ℓ)
    (hLa : 0 ≤ algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 < lam) (hc : 0 < c)
    (hopt : ∀ (h : Fin H) (x : S) (a : A),
      M.R x a + Pexp M x a (vstar M H h) ≤ qAt M st δ K h.val x a)
    (hev : ∀ (x : S) (a : A) (h : Fin H), 0 < countSA st x a →
      (empiricalExp st x a (vstar M H h) - Pexp M x a (vstar M H h) ≤
        Real.sqrt (2 * cvar M x a (vstar M H h) * ℓ / (countSA st x a : ℝ)) +
          H * ℓ / (3 * (countSA st x a : ℝ))) ∧
      (empiricalExp st x a (csq M x a (vstar M H h)) - Pexp M x a (csq M x a (vstar M H h)) ≤
        Real.sqrt (2 * cW M x a (vstar M H h) * ℓ / (countSA st x a : ℝ)) +
          (H : ℝ) ^ 2 * ℓ / (3 * (countSA st x a : ℝ))) ∧
      (∀ y, empiricalP st x a y - M.P x a y ≤
        η * M.P x a y + ℓ / (lam * (countSA st x a : ℝ))))
    (h : ℕ) (hh : h < H) (x : S) :
    gapF M st δ K (greedyPolicy (episodeQ M st δ K) sel) h x ≤
      Xt M st δ K (greedyPolicy (episodeQ M st δ K) sel) ℓ lam c h hh x
          (greedyPolicy (episodeQ M st δ K) sel x ⟨h, hh⟩) +
        (1 + η + 1 / (c * H)) * ∑ y, M.P x (greedyPolicy (episodeQ M st δ K) sel x ⟨h, hh⟩) y *
          gapF M st δ K (greedyPolicy (episodeQ M st δ K) sel) (h + 1) y := by
  set π := greedyPolicy (episodeQ M st δ K) sel with hπ
  set a := π x ⟨h, hh⟩ with ha
  have hH' : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have haq : a = sel (fun a' => qAt M st δ K h x a') := rfl
  have hV : Vk M st δ K h x = qAt M st δ K h x a := by
    rw [Vk_sel M st δ K sel hsel h x, haq]
  have hval : valueAt M π h x = M.R x a + ∑ y, M.P x a y * valueAt M π (h + 1) y := by
    rw [valueAt, dif_pos hh] <;> rfl
  set PG := ∑ y, M.P x a y * gapF M st δ K π (h + 1) y with hPG
  have hPG0 : 0 ≤ PG := Finset.sum_nonneg (fun y _ =>
    mul_nonneg ((M.kernel x a).1 y) (gapF_nonneg M st δ K hopt π (h + 1) y))
  have hγ : 0 ≤ 1 + η + 1 / (c * H) := by positivity
  have hγPG : 0 ≤ (1 + η + 1 / (c * H)) * PG := mul_nonneg hγ hPG0
  have hgle : gapF M st δ K π h x ≤ H := gapF_le M st δ K π h x
  by_cases hn0 : countSA st x a = 0
  · unfold Xt; rw [if_pos hn0]; linarith
  have hn : 0 < countSA st x a := Nat.pos_of_ne_zero hn0
  obtain ⟨hR1, hR2, hGB⟩ := hev x a ⟨h, hh⟩ hn
  have core := gap_core M st x a (vstar M H ⟨h, hh⟩) (nextV M st δ K h) (valueAt M π (h + 1))
    ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) η lam c hH hn hℓ hLa hη hη1 hlam hc
    (fun y => valueAt_nonneg M π (h + 1) y) (fun y => valueAt_le_opt M π (h + 1) y)
    (vstar_le_nextV M st δ K hopt h hh) (nextV_le M st δ K h) hR1 hR2 hGB
  have ePG : Pexp M x a (fun y => nextV M st δ K h y - valueAt M π (h + 1) y) = PG := by
    rw [hPG]; unfold Pexp gapF
    apply Finset.sum_congr rfl; intro y _; beta_reduce; rw [nextV_eq_Vk]
  rw [ePG] at core
  have hq : qAt M st δ K h x a ≤ M.R x a + empiricalExp st x a (nextV M st δ K h) +
      bonus st δ K ⟨h, hh⟩ x a (nextV M st δ K h) := by
    rw [qAt_eq M st δ K h hh x a hn0]; exact min_le_right _ _
  have hbon : bonus st δ K ⟨h, hh⟩ x a (nextV M st δ K h) =
      Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H *
          empiricalVar st x a (nextV M st δ K h) / (countSA st x a : ℝ)) +
        14 * H * algorithmLog δ (Fintype.card S) (Fintype.card A) K H /
          (3 * (countSA st x a : ℝ)) +
        Real.sqrt (8 * empiricalExp st x a
          (extraCap st (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) ⟨h, hh⟩) /
            (countSA st x a : ℝ)) := rfl
  have hPv : Pexp M x a (valueAt M π (h + 1)) = ∑ y, M.P x a y * valueAt M π (h + 1) y := rfl
  have hgap : gapF M st δ K π h x ≤ (1 + η + 1 / (c * H)) * PG +
      ((Real.sqrt (2 * ℓ) + Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)) *
          Real.sqrt (cvar M x a (valueAt M π (h + 1))) / Real.sqrt (countSA st x a : ℝ) +
        gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) lam c /
          (countSA st x a : ℝ) +
        Real.sqrt (8 * empiricalExp st x a
          (extraCap st (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) ⟨h, hh⟩) /
            (countSA st x a : ℝ))) := by
    unfold gapF
    rw [hV, hval]
    rw [hbon] at hq
    rw [hPv] at core
    linarith
  unfold Xt
  rw [if_neg hn0]
  have h2 : gapF M st δ K π h x ≤ min (H : ℝ) ((1 + η + 1 / (c * H)) * PG +
      ((Real.sqrt (2 * ℓ) + Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)) *
          Real.sqrt (cvar M x a (valueAt M π (h + 1))) / Real.sqrt (countSA st x a : ℝ) +
        gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) lam c /
          (countSA st x a : ℝ) +
        Real.sqrt (8 * empiricalExp st x a
          (extraCap st (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) ⟨h, hh⟩) /
            (countSA st x a : ℝ)))) := le_min hgle hgap
  exact le_trans h2 (le_trans (min_add_le _ _ _ hγPG) (le_of_eq (add_comm _ _)))

end GapRun

section Unroll

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma gapF_H (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (π : Hoeffding.Policy S A H) (y : S) : gapF M st δ K π H y = 0 := by
  unfold gapF Vk
  have e : ∀ a', qAt M st δ K H y a' = 0 := fun a' => by rw [qAt, dif_neg (lt_irrefl H)]
  have e2 : valueAt M π H y = 0 := by rw [valueAt, dif_neg (lt_irrefl H)]
  simp [e, e2]

/-- Weighted next-gap statistic (the `F` of the gap martingale). -/
noncomputable def Fg (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (γ : ℝ) : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ :=
  fun k h ω y => γ ^ (h.val + 1) * gapF M (runState M δ K H sel init ω k.val) δ K
    (policyAt M δ K H sel init ω k) (h.val + 1) y

lemma Fg_adapted (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (γ : ℝ) :
    ∀ k h, Adapted (k.val * H + h.val) (Fg (K := K) M δ sel init γ k h) := by
  intro k h ω ω' hag
  have hag0 : Agree (k.val * H) ω ω' := hag.mono (Nat.le_add_right _ _)
  funext y
  simp only [Fg]
  rw [runState_eq M δ sel init ω ω' k.val hag0, policyAt_eq M δ sel init ω ω' k hag0]

/-- Clipped step term along the run. -/
noncomputable def XtR (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ℓ lam c : ℝ) (ω : Hoeffding.Outcomes S K H) (k : Fin K)
    (h : Fin H) : ℝ :=
  Xt M (runState M δ K H sel init ω k.val) δ K (policyAt M δ K H sel init ω k) ℓ lam c h.val
    h.isLt (stateAt init ω k (Fin.castSucc h)) (act M δ K H sel init ω k h)

theorem gap_unroll (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (init : InitialRule S H)
    (ℓ η lam c : ℝ) (hH : 0 < H) (hℓ : 0 ≤ ℓ)
    (hLa : 0 ≤ algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 < lam) (hc : 0 < c)
    (ω : Hoeffding.Outcomes S K H) (k : Fin K)
    (hopt : ∀ (h : Fin H) (x : S) (a : A), M.R x a + Pexp M x a (vstar M H h) ≤
      qAt M (runState M δ K H sel init ω k.val) δ K h.val x a)
    (hev : ∀ (x : S) (a : A) (h : Fin H),
      0 < countSA (runState M δ K H sel init ω k.val) x a →
      (empiricalExp (runState M δ K H sel init ω k.val) x a (vstar M H h) -
          Pexp M x a (vstar M H h) ≤
        Real.sqrt (2 * cvar M x a (vstar M H h) * ℓ /
            (countSA (runState M δ K H sel init ω k.val) x a : ℝ)) +
          H * ℓ / (3 * (countSA (runState M δ K H sel init ω k.val) x a : ℝ))) ∧
      (empiricalExp (runState M δ K H sel init ω k.val) x a (csq M x a (vstar M H h)) -
          Pexp M x a (csq M x a (vstar M H h)) ≤
        Real.sqrt (2 * cW M x a (vstar M H h) * ℓ /
            (countSA (runState M δ K H sel init ω k.val) x a : ℝ)) +
          (H : ℝ) ^ 2 * ℓ / (3 * (countSA (runState M δ K H sel init ω k.val) x a : ℝ))) ∧
      (∀ y, empiricalP (runState M δ K H sel init ω k.val) x a y - M.P x a y ≤
        η * M.P x a y + ℓ / (lam * (countSA (runState M δ K H sel init ω k.val) x a : ℝ)))) :
    gapF M (runState M δ K H sel init ω k.val) δ K (policyAt M δ K H sel init ω k) 0
        (stateAt init ω k ⟨0, by omega⟩) ≤
      ∑ h : Fin H, ((1 + η + 1 / (c * H)) ^ h.val * XtR M δ sel init ℓ lam c ω k h +
        mInc M δ sel init (Fg M δ sel init (1 + η + 1 / (c * H))) k h ω) := by
  set γ := 1 + η + 1 / (c * H) with hγ
  set st := runState M δ K H sel init ω k.val with hst
  set π := policyAt M δ K H sel init ω k with hπ
  have hπ' : π = greedyPolicy (episodeQ M st δ K) sel := rfl
  have hγ1 : 1 ≤ γ := by
    have : 0 ≤ 1 / (c * H) := by positivity
    linarith
  have claim : ∀ m, ∀ _hm : m ≤ H, gapF M st δ K π 0 (stateAt init ω k ⟨0, by omega⟩) ≤
      (∑ h ∈ Finset.range m, (if hh : h < H then (γ ^ h * XtR M δ sel init ℓ lam c ω k ⟨h, hh⟩ +
        mInc M δ sel init (Fg M δ sel init γ) k ⟨h, hh⟩ ω) else 0)) +
      γ ^ m * gapF M st δ K π m (stateAt init ω k ⟨m, by omega⟩) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hmH : m < H := hm
      have ih' := ih (by omega)
      have hstep := gap_step M st δ K sel hsel ℓ η lam c hH hℓ hLa hη hη1 hlam hc hopt hev m hmH
        (stateAt init ω k ⟨m, by omega⟩)
      rw [← hπ', ← hγ] at hstep
      have hs1 : stateAt init ω k ⟨m + 1, by omega⟩ = ω k ⟨m, hmH⟩ := by
        unfold stateAt
        rw [dif_neg (by simp)] <;> simp
      have hX : Xt M st δ K π ℓ lam c m hmH (stateAt init ω k ⟨m, by omega⟩)
          (π (stateAt init ω k ⟨m, by omega⟩) ⟨m, hmH⟩) =
          XtR M δ sel init ℓ lam c ω k ⟨m, hmH⟩ := rfl
      have hm' : mInc M δ sel init (Fg M δ sel init γ) k ⟨m, hmH⟩ ω =
          ∑ y, M.P (stateAt init ω k ⟨m, by omega⟩)
            (π (stateAt init ω k ⟨m, by omega⟩) ⟨m, hmH⟩) y *
              (γ ^ (m + 1) * gapF M st δ K π (m + 1) y) -
            γ ^ (m + 1) * gapF M st δ K π (m + 1) (ω k ⟨m, hmH⟩) := rfl
      have heps : γ ^ m * (γ * ∑ y, M.P (stateAt init ω k ⟨m, by omega⟩)
            (π (stateAt init ω k ⟨m, by omega⟩) ⟨m, hmH⟩) y * gapF M st δ K π (m + 1) y) =
          mInc M δ sel init (Fg M δ sel init γ) k ⟨m, hmH⟩ ω +
            γ ^ (m + 1) * gapF M st δ K π (m + 1) (stateAt init ω k ⟨m + 1, by omega⟩) := by
        rw [hm', hs1, sub_add_cancel, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _; ring
      rw [hX] at hstep
      have hg0 : 0 ≤ γ ^ m := pow_nonneg (by linarith) m
      have h2 := mul_le_mul_of_nonneg_left hstep hg0
      rw [mul_add, heps] at h2
      rw [Finset.sum_range_succ, dif_pos hmH]
      linarith
  have hfin := claim H le_rfl
  rw [gapF_H, mul_zero, add_zero, Finset.sum_range] at hfin
  refine le_trans hfin (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro h _
  rw [dif_pos h.isLt]

end Unroll

section GoodReg

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

/-- Bennett slope `η(λ) = (e^λ - 1 - λ)/λ`. -/
noncomputable def etaB (lam : ℝ) : ℝ := (Real.exp lam - 1 - lam) / lam

/-- Regret-side good event: Bernstein upper tails for `V*` (R1) and `csq V*` (R2), and the
per-coordinate Bennett bound (GB), at every count. -/
def GoodReg (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ℓ lam : ℝ) (ω : Hoeffding.Outcomes S K H) : Prop :=
  ∀ (k : Fin K) (x : S) (a : A) (h : Fin H),
    0 < countSA (runState M δ K H sel init ω k.val) x a →
    (empiricalExp (runState M δ K H sel init ω k.val) x a (vstar M H h) -
        Pexp M x a (vstar M H h) ≤
      Real.sqrt (2 * cvar M x a (vstar M H h) * ℓ /
          (countSA (runState M δ K H sel init ω k.val) x a : ℝ)) +
        H * ℓ / (3 * (countSA (runState M δ K H sel init ω k.val) x a : ℝ))) ∧
    (empiricalExp (runState M δ K H sel init ω k.val) x a (csq M x a (vstar M H h)) -
        Pexp M x a (csq M x a (vstar M H h)) ≤
      Real.sqrt (2 * cW M x a (vstar M H h) * ℓ /
          (countSA (runState M δ K H sel init ω k.val) x a : ℝ)) +
        (H : ℝ) ^ 2 * ℓ / (3 * (countSA (runState M δ K H sel init ω k.val) x a : ℝ))) ∧
    (∀ y, empiricalP (runState M δ K H sel init ω k.val) x a y - M.P x a y ≤
      etaB lam * M.P x a y + ℓ / (lam * (countSA (runState M δ K H sel init ω k.val) x a : ℝ)))

lemma eventB_one (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (y0 : S) (lam : ℝ) (hlam : 0 < lam) (ℓ : ℝ) (m : ℕ) (hm : 0 < m) :
    probEvent M δ K H sel init (fun ω => ∃ k : Fin K,
        countSA (runState M δ K H sel init ω k.val) x a = m ∧
        etaB lam * M.P x a y0 + ℓ / (lam * m) <
          empiricalP (runState M δ K H sel init ω k.val) x a y0 - M.P x a y0) ≤
      Real.exp (-ℓ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hP : ∑ z, M.P x a z * (if z = y0 then (1 : ℝ) else 0) = M.P x a y0 := by
    simp [mul_ite, Finset.sum_ite_eq']
  have hmgf' : ∑ y, M.P x a y * Real.exp (lam * ((if y = y0 then (1 : ℝ) else 0) -
      ∑ z, M.P x a z * (if z = y0 then (1 : ℝ) else 0))) ≤
      Real.exp (M.P x a y0 * (Real.exp lam - 1 - lam)) := by
    rw [hP]; exact bennett_ind (M.P x a) (M.kernel x a).1 (M.kernel x a).2 y0 lam
  have h := event_gen (K := K) M δ sel init x a (fun z => if z = y0 then (1 : ℝ) else 0) lam
    (M.P x a y0 * (Real.exp lam - 1 - lam)) hlam.le hmgf' m hm
    (etaB lam * M.P x a y0 + ℓ / (lam * m))
  have hexp : -(lam * m * (etaB lam * M.P x a y0 + ℓ / (lam * m)) -
      m * (M.P x a y0 * (Real.exp lam - 1 - lam))) = -ℓ := by
    unfold etaB; field_simp; ring
  rw [hexp] at h
  refine le_trans (probEvent_mono M δ sel init _ _ ?_) h
  rintro ω ⟨k, hk, hlt⟩
  refine ⟨k, hk, ?_⟩
  have he : empiricalExp (runState M δ K H sel init ω k.val) x a
      (fun z => if z = y0 then (1 : ℝ) else 0) =
      empiricalP (runState M δ K H sel init ω k.val) x a y0 := by
    unfold empiricalExp finiteExp; simp [mul_ite, Finset.sum_ite_eq']
  rw [he, hP]; exact hlt.le

lemma var_le_second (M : Hoeffding.MDP S A) (x : S) (a : A) (g : S → ℝ) :
    ∑ y, M.P x a y * (g y - ∑ z, M.P x a z * g z) ^ 2 ≤ ∑ y, M.P x a y * g y ^ 2 := by
  have h := fv_shift (M.P x a) (M.kernel x a).2 g (∑ z, M.P x a z * g z)
  have h2 : finiteVar (M.P x a) g = ∑ y, M.P x a y * g y ^ 2 - (∑ z, M.P x a z * g z) ^ 2 := rfl
  have h3 : finiteExp (M.P x a) (fun y => (g y - ∑ z, M.P x a z * g z) ^ 2) =
      ∑ y, M.P x a y * (g y - ∑ z, M.P x a z * g z) ^ 2 := rfl
  have h4 : finiteExp (M.P x a) g = ∑ z, M.P x a z * g z := rfl
  rw [h2, h3, h4, sub_self] at h
  linarith [sq_nonneg (∑ z, M.P x a z * g z)]

theorem probReg (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ℓ lam : ℝ) (hℓ : 0 < ℓ) (hlam : 0 < lam) (hH : 0 < H) :
    probEvent M δ K H sel init (fun ω => ¬ GoodReg M δ sel init ℓ lam ω) ≤
      (Fintype.card S * Fintype.card A * H * (K * H) : ℕ) * (2 * Real.exp (-ℓ)) +
      (Fintype.card S * Fintype.card A * Fintype.card S * (K * H) : ℕ) * Real.exp (-ℓ) := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  let B1 : S × A × Fin H × Fin (K * H) → Hoeffding.Outcomes S K H → Prop := fun i ω =>
    ∃ k : Fin K, countSA (runState M δ K H sel init ω k.val) i.1 i.2.1 = i.2.2.2.val + 1 ∧
      Real.sqrt (2 * cvar M i.1 i.2.1 (vstar M H i.2.2.1) * ℓ / ((i.2.2.2.val + 1 : ℕ) : ℝ)) +
        H * ℓ / (3 * ((i.2.2.2.val + 1 : ℕ) : ℝ)) ≤
      empiricalExp (runState M δ K H sel init ω k.val) i.1 i.2.1 (vstar M H i.2.2.1) -
        ∑ z, M.P i.1 i.2.1 z * vstar M H i.2.2.1 z
  let B2 : S × A × Fin H × Fin (K * H) → Hoeffding.Outcomes S K H → Prop := fun i ω =>
    ∃ k : Fin K, countSA (runState M δ K H sel init ω k.val) i.1 i.2.1 = i.2.2.2.val + 1 ∧
      Real.sqrt (2 * (∑ y, M.P i.1 i.2.1 y * (csq M i.1 i.2.1 (vstar M H i.2.2.1) y -
          ∑ z, M.P i.1 i.2.1 z * csq M i.1 i.2.1 (vstar M H i.2.2.1) z) ^ 2) * ℓ /
          ((i.2.2.2.val + 1 : ℕ) : ℝ)) +
        (H : ℝ) ^ 2 * ℓ / (3 * ((i.2.2.2.val + 1 : ℕ) : ℝ)) ≤
      empiricalExp (runState M δ K H sel init ω k.val) i.1 i.2.1
          (csq M i.1 i.2.1 (vstar M H i.2.2.1)) -
        ∑ z, M.P i.1 i.2.1 z * csq M i.1 i.2.1 (vstar M H i.2.2.1) z
  let B3 : S × A × S × Fin (K * H) → Hoeffding.Outcomes S K H → Prop := fun j ω =>
    ∃ k : Fin K, countSA (runState M δ K H sel init ω k.val) j.1 j.2.1 = j.2.2.2.val + 1 ∧
      etaB lam * M.P j.1 j.2.1 j.2.2.1 + ℓ / (lam * ((j.2.2.2.val + 1 : ℕ) : ℝ)) <
        empiricalP (runState M δ K H sel init ω k.val) j.1 j.2.1 j.2.2.1 - M.P j.1 j.2.1 j.2.2.1
  have hB12 : ∀ i, probEvent M δ K H sel init (fun ω => B1 i ω ∨ B2 i ω) ≤
      2 * Real.exp (-ℓ) := by
    intro i
    obtain ⟨x, a, h, m⟩ := i
    have hf0 := vstar_nonneg M H h
    have hfH := vstar_le M H h
    have hPf0 := Pexp_nonneg M x a (vstar M H h) hf0
    have e1 : probEvent M δ K H sel init (B1 (x, a, h, m)) ≤ Real.exp (-ℓ) := by
      refine event_bern M δ sel init x a (vstar M H h) H _ ℓ hH' ?_ rfl hℓ (m.val + 1)
        (Nat.succ_pos _)
      intro y
      have : ∑ z, M.P x a z * vstar M H h z = Pexp M x a (vstar M H h) := rfl
      rw [this]
      linarith [hfH y]
    have e2 : probEvent M δ K H sel init (B2 (x, a, h, m)) ≤ Real.exp (-ℓ) := by
      refine event_bern M δ sel init x a (csq M x a (vstar M H h)) ((H : ℝ) ^ 2) _ ℓ
        (by positivity) ?_ rfl hℓ (m.val + 1) (Nat.succ_pos _)
      intro y
      have h1 := csq_le M x a (vstar M H h) H hf0 hfH y
      have h2 : 0 ≤ ∑ z, M.P x a z * csq M x a (vstar M H h) z :=
        Finset.sum_nonneg (fun z _ => mul_nonneg ((M.kernel x a).1 z) (sq_nonneg _))
      linarith
    calc _ ≤ probEvent M δ K H sel init (B1 (x, a, h, m)) +
          probEvent M δ K H sel init (B2 (x, a, h, m)) := probEvent_union M δ sel init _ _
      _ ≤ 2 * Real.exp (-ℓ) := by linarith
  have hB3 : ∀ j, probEvent M δ K H sel init (B3 j) ≤ Real.exp (-ℓ) := by
    intro j
    obtain ⟨x, a, y, m⟩ := j
    exact eventB_one M δ sel init x a y lam hlam ℓ (m.val + 1) (Nat.succ_pos _)
  have hsub : ∀ ω, ¬ GoodReg M δ sel init ℓ lam ω →
      (∃ i : S × A × Fin H × Fin (K * H), B1 i ω ∨ B2 i ω) ∨
        (∃ j : S × A × S × Fin (K * H), B3 j ω) := by
    intro ω hω
    unfold GoodReg at hω
    push_neg at hω
    obtain ⟨k, x, a, h, hpos, hbad⟩ := hω
    set n := countSA (runState M δ K H sel init ω k.val) x a with hn
    have hnle := countSA_le M δ sel init ω x a k
    have hn1 : n - 1 + 1 = n := by omega
    have hcnt : countSA (runState M δ K H sel init ω k.val) x a = (n - 1) + 1 := by omega
    by_cases c1 : empiricalExp (runState M δ K H sel init ω k.val) x a (vstar M H h) -
        Pexp M x a (vstar M H h) ≤
      Real.sqrt (2 * cvar M x a (vstar M H h) * ℓ / (n : ℝ)) + H * ℓ / (3 * (n : ℝ))
    · by_cases c2 : empiricalExp (runState M δ K H sel init ω k.val) x a
          (csq M x a (vstar M H h)) - Pexp M x a (csq M x a (vstar M H h)) ≤
        Real.sqrt (2 * cW M x a (vstar M H h) * ℓ / (n : ℝ)) +
          (H : ℝ) ^ 2 * ℓ / (3 * (n : ℝ))
      · right
        obtain ⟨y, hy⟩ := hbad c1 c2
        refine ⟨(x, a, y, ⟨n - 1, by omega⟩), k, hcnt, ?_⟩
        simp only [hn1]
        exact hy
      · left
        refine ⟨(x, a, h, ⟨n - 1, by omega⟩), Or.inr ⟨k, hcnt, ?_⟩⟩
        simp only [hn1]
        push_neg at c2
        have hn' : (0 : ℝ) < n := by exact_mod_cast hpos
        have hvc := var_le_second M x a (csq M x a (vstar M H h))
        have hs : Real.sqrt (2 * (∑ y, M.P x a y * (csq M x a (vstar M H h) y -
            ∑ z, M.P x a z * csq M x a (vstar M H h) z) ^ 2) * ℓ / (n : ℝ)) ≤
            Real.sqrt (2 * cW M x a (vstar M H h) * ℓ / (n : ℝ)) := by
          apply Real.sqrt_le_sqrt
          apply div_le_div_of_nonneg_right _ hn'.le
          apply mul_le_mul_of_nonneg_right _ hℓ.le
          have : cW M x a (vstar M H h) = ∑ y, M.P x a y * csq M x a (vstar M H h) y ^ 2 := rfl
          rw [this]; linarith
        have e : ∑ z, M.P x a z * csq M x a (vstar M H h) z =
            Pexp M x a (csq M x a (vstar M H h)) := rfl
        rw [e] at hs ⊢
        linarith
    · left
      refine ⟨(x, a, h, ⟨n - 1, by omega⟩), Or.inl ⟨k, hcnt, ?_⟩⟩
      simp only [hn1]
      push_neg at c1
      have e : ∑ z, M.P x a z * vstar M H h z = Pexp M x a (vstar M H h) := rfl
      rw [e]
      linarith
  calc _ ≤ probEvent M δ K H sel init (fun ω =>
        (∃ i : S × A × Fin H × Fin (K * H), B1 i ω ∨ B2 i ω) ∨
          (∃ j : S × A × S × Fin (K * H), B3 j ω)) :=
        probEvent_mono M δ sel init _ _ hsub
    _ ≤ probEvent M δ K H sel init (fun ω => ∃ i : S × A × Fin H × Fin (K * H), B1 i ω ∨ B2 i ω) +
        probEvent M δ K H sel init (fun ω => ∃ j : S × A × S × Fin (K * H), B3 j ω) :=
        probEvent_union M δ sel init _ _
    _ ≤ (∑ i : S × A × Fin H × Fin (K * H),
          probEvent M δ K H sel init (fun ω => B1 i ω ∨ B2 i ω)) +
        ∑ j : S × A × S × Fin (K * H), probEvent M δ K H sel init (B3 j) :=
        add_le_add (probEvent_exists_le M δ sel init _) (probEvent_exists_le M δ sel init _)
    _ ≤ (∑ _i : S × A × Fin H × Fin (K * H), 2 * Real.exp (-ℓ)) +
        ∑ _j : S × A × S × Fin (K * H), Real.exp (-ℓ) :=
        add_le_add (Finset.sum_le_sum (fun i _ => hB12 i)) (Finset.sum_le_sum (fun j _ => hB3 j))
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

end GoodReg

section Decomp

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma etaB_nonneg (lam : ℝ) (hlam : 0 < lam) : 0 ≤ etaB lam := by
  unfold etaB
  have := Real.add_one_le_exp lam
  apply div_nonneg _ hlam.le
  linarith

lemma etaB_le (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) : etaB lam ≤ lam := by
  unfold etaB
  have h := Real.abs_exp_sub_one_sub_id_le (x := lam) (by rw [abs_of_pos hlam]; exact hlam1)
  have h2 := le_abs_self (Real.exp lam - 1 - lam)
  rw [div_le_iff₀ hlam]
  nlinarith

/-- Regret decomposition on the good events: per-episode unrolled gaps. -/
theorem regret_decomp (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (init : InitialRule S H)
    (ℓo ℓ lam c : ℝ) (hH : 0 < H) (hℓo : 0 ≤ ℓo)
    (hℓLa : ℓo ≤ 3 / 2 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (hℓ : 0 ≤ ℓ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hc : 0 < c)
    (ω : Hoeffding.Outcomes S K H) (hG : GoodOpt M δ sel init ℓo ω)
    (hR : GoodReg M δ sel init ℓ lam ω) :
    regret M δ K H sel init ω ≤
      ∑ k : Fin K, ∑ h : Fin H,
        ((1 + etaB lam + 1 / (c * H)) ^ h.val * XtR M δ sel init ℓ lam c ω k h +
          mInc M δ sel init (Fg M δ sel init (1 + etaB lam + 1 / (c * H))) k h ω) := by
  have hLa : 0 ≤ algorithmLog δ (Fintype.card S) (Fintype.card A) K H := by linarith
  have hη0 := etaB_nonneg lam hlam
  have hη1 : etaB lam ≤ 1 := le_trans (etaB_le lam hlam hlam1) hlam1
  unfold regret
  apply Finset.sum_le_sum
  intro k _
  have hopt := optimism M δ sel init ℓo hH hℓo hℓLa ω hG k.val k.isLt
  have hun := gap_unroll M δ sel hsel init ℓ (etaB lam) lam c hH hℓ hLa hη0 hη1 hlam hc ω k
    hopt (fun x a h hn => hR k x a h hn)
  have hV := opt_le_Vk M (runState M δ K H sel init ω k.val) δ K hopt 0
    (stateAt init ω k ⟨0, by omega⟩)
  refine le_trans ?_ hun
  unfold gapF
  linarith

end Decomp

section RegretGood

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

/-- Clipped weighted next-gap statistic (range `[0, γ^(h+1) H]` on every outcome). -/
noncomputable def Fgc (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (γ : ℝ) : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ :=
  fun k h ω y => γ ^ (h.val + 1) * min (H : ℝ) (max 0 (gapF M (runState M δ K H sel init ω k.val)
    δ K (policyAt M δ K H sel init ω k) (h.val + 1) y))

lemma Fgc_adapted (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (γ : ℝ) :
    ∀ k h, Adapted (k.val * H + h.val) (Fgc (K := K) M δ sel init γ k h) := by
  intro k h ω ω' hag
  have hag0 : Agree (k.val * H) ω ω' := hag.mono (Nat.le_add_right _ _)
  funext y
  simp only [Fgc]
  rw [runState_eq M δ sel init ω ω' k.val hag0, policyAt_eq M δ sel init ω ω' k hag0]

lemma Fgc_mem (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (γ : ℝ) (hγ : 1 ≤ γ) (k : Fin K) (h : Fin H)
    (ω : Hoeffding.Outcomes S K H) (y : S) :
    Fgc M δ sel init γ k h ω y ∈ Set.Icc 0 (0 + γ ^ H * H) := by
  simp only [Fgc, zero_add, Set.mem_Icc]
  have hg0 : 0 ≤ γ ^ (h.val + 1) := pow_nonneg (by linarith) _
  have hgH : γ ^ (h.val + 1) ≤ γ ^ H := pow_le_pow_right₀ hγ h.isLt
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have c0 : 0 ≤ min (H : ℝ) (max 0 (gapF M (runState M δ K H sel init ω k.val)
      δ K (policyAt M δ K H sel init ω k) (h.val + 1) y)) := le_min hH0 (le_max_left _ _)
  have c1 : min (H : ℝ) (max 0 (gapF M (runState M δ K H sel init ω k.val)
      δ K (policyAt M δ K H sel init ω k) (h.val + 1) y)) ≤ H := min_le_left _ _
  constructor
  · exact mul_nonneg hg0 c0
  · calc _ ≤ γ ^ (h.val + 1) * H := mul_le_mul_of_nonneg_left c1 hg0
      _ ≤ γ ^ H * H := mul_le_mul_of_nonneg_right hgH hH0

lemma Xt_nonneg (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (π : Hoeffding.Policy S A H) (ℓ lam c : ℝ) (hℓ : 0 ≤ ℓ)
    (hLa : 0 ≤ algorithmLog δ (Fintype.card S) (Fintype.card A) K H) (hlam : 0 < lam)
    (hc : 0 < c) (h : ℕ) (hh : h < H) (x : S) (a : A) :
    0 ≤ Xt M st δ K π ℓ lam c h hh x a := by
  unfold Xt
  split_ifs with hn
  · positivity
  · apply le_min (Nat.cast_nonneg H)
    have hn' : (0 : ℝ) < (countSA st x a : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hb : 0 ≤ gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
        lam c := by
      unfold gBeta
      have : 0 ≤ (Fintype.card S : ℝ) * ℓ / lam := by positivity
      positivity
    have h1 : 0 ≤ (Real.sqrt (2 * ℓ) +
        Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)) *
          Real.sqrt (cvar M x a (valueAt M π (h + 1))) / Real.sqrt (countSA st x a : ℝ) := by
      positivity
    have h2 := div_nonneg hb hn'.le
    have h3 := Real.sqrt_nonneg (8 * empiricalExp st x a
          (extraCap st (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) ⟨h, hh⟩) /
            (countSA st x a : ℝ))
    linarith

/-- Regret on the good events, with the clipped gap martingale. -/
theorem regret_good (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (init : InitialRule S H)
    (ℓo ℓ lam c : ℝ) (hH : 0 < H) (hℓo : 0 ≤ ℓo)
    (hℓLa : ℓo ≤ 3 / 2 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (hℓ : 0 ≤ ℓ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hc : 0 < c)
    (ω : Hoeffding.Outcomes S K H) (hG : GoodOpt M δ sel init ℓo ω)
    (hR : GoodReg M δ sel init ℓ lam ω) (B : ℝ)
    (hAz : ∑ p : Fin K × Fin H,
      mInc M δ sel init (Fgc M δ sel init (1 + etaB lam + 1 / (c * H))) p.1 p.2 ω ≤ B) :
    regret M δ K H sel init ω ≤
      (1 + etaB lam + 1 / (c * H)) ^ H *
        ∑ k : Fin K, ∑ h : Fin H, XtR M δ sel init ℓ lam c ω k h + B := by
  set γ := 1 + etaB lam + 1 / (c * H) with hγ
  have hη0 := etaB_nonneg lam hlam
  have hγ1 : 1 ≤ γ := by
    have : 0 ≤ 1 / (c * H) := by positivity
    linarith
  have hLa : 0 ≤ algorithmLog δ (Fintype.card S) (Fintype.card A) K H := by linarith
  have hdec := regret_decomp M δ sel hsel init ℓo ℓ lam c hH hℓo hℓLa hℓ hlam hlam1 hc ω hG hR
  rw [← hγ] at hdec
  -- the unclipped and clipped martingale increments agree on the good event
  have hFeq : ∀ k : Fin K, ∀ h : Fin H, mInc M δ sel init (Fg M δ sel init γ) k h ω =
      mInc M δ sel init (Fgc M δ sel init γ) k h ω := by
    intro k h
    have hopt := optimism M δ sel init ℓo hH hℓo hℓLa ω hG k.val k.isLt
    have hcl : ∀ y, Fg M δ sel init γ k h ω y = Fgc M δ sel init γ k h ω y := by
      intro y
      simp only [Fg, Fgc]
      have g0 := gapF_nonneg M (runState M δ K H sel init ω k.val) δ K hopt
        (policyAt M δ K H sel init ω k) (h.val + 1) y
      have g1 := gapF_le M (runState M δ K H sel init ω k.val) δ K
        (policyAt M δ K H sel init ω k) (h.val + 1) y
      rw [max_eq_right g0, min_eq_right g1]
    unfold mInc
    simp only [hcl]
  have hX : ∀ k : Fin K, ∀ h : Fin H,
      γ ^ h.val * XtR M δ sel init ℓ lam c ω k h ≤ γ ^ H * XtR M δ sel init ℓ lam c ω k h := by
    intro k h
    apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hγ1 h.isLt.le)
    exact Xt_nonneg M _ δ K _ ℓ lam c hℓ hLa hlam hc h.val h.isLt _ _
  calc regret M δ K H sel init ω
      ≤ ∑ k : Fin K, ∑ h : Fin H, (γ ^ h.val * XtR M δ sel init ℓ lam c ω k h +
          mInc M δ sel init (Fg M δ sel init γ) k h ω) := hdec
    _ = ∑ k : Fin K, ∑ h : Fin H, γ ^ h.val * XtR M δ sel init ℓ lam c ω k h +
          ∑ p : Fin K × Fin H, mInc M δ sel init (Fgc M δ sel init γ) p.1 p.2 ω := by
        rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro k _
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro h _
        rw [hFeq k h]
    _ ≤ γ ^ H * ∑ k : Fin K, ∑ h : Fin H, XtR M δ sel init ℓ lam c ω k h + B := by
        rw [Finset.mul_sum]
        have : ∑ k : Fin K, ∑ h : Fin H, γ ^ h.val * XtR M δ sel init ℓ lam c ω k h ≤
            ∑ k : Fin K, γ ^ H * ∑ h : Fin H, XtR M δ sel init ℓ lam c ω k h := by
          apply Finset.sum_le_sum; intro k _
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun h _ => hX k h)
        linarith

end RegretGood

section Pigeon2

lemma log_step2 (m N : ℝ) (hm : 0 ≤ m) (hmN : m ≤ N) (hN : 0 < N) :
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

/-- Harmonic potential: increments counted at `β / N` once `N ≥ H`, nothing before. -/
lemma seq_log (J : ℕ) (N : ℕ → ℝ) (H β : ℝ) (F : ℕ → ℝ) (hH : 0 < H) (hβ : 0 ≤ β)
    (hN0 : N 0 = 0) (hmono : ∀ k, k < J → N k ≤ N (k + 1))
    (hstep : ∀ k, k < J → N (k + 1) - N k ≤ H)
    (hf : ∀ k, k < J → F k ≤ if H ≤ N k then β / N k else 0) :
    ∀ j, j ≤ J → ∑ k ∈ Finset.range j, (N (k + 1) - N k) * F k ≤
      2 * β * (Real.log (max (N j) H) - Real.log H) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, hN0]
    rw [max_eq_right hH.le, sub_self, mul_zero]
  | succ j ih' =>
    intro hjJ
    have hj : j < J := hjJ
    have ih := ih' (by omega)
    rw [Finset.sum_range_succ]
    have hm0 : 0 ≤ N (j + 1) - N j := by linarith [hmono j hj]
    have hmax : Real.log (max (N j) H) ≤ Real.log (max (N (j + 1)) H) :=
      Real.log_le_log (lt_max_of_lt_right hH) (max_le_max (hmono j hj) le_rfl)
    have hmaxβ := mul_le_mul_of_nonneg_left (sub_le_sub_right hmax (Real.log H))
      (by positivity : (0 : ℝ) ≤ 2 * β)
    by_cases hge : H ≤ N j
    · have hf' := hf j hj
      rw [if_pos hge] at hf'
      have hNpos : 0 < N j := lt_of_lt_of_le hH hge
      have hmN : N (j + 1) - N j ≤ N j := le_trans (hstep j hj) hge
      have hterm : (N (j + 1) - N j) * F j ≤ (N (j + 1) - N j) * (β / N j) :=
        mul_le_mul_of_nonneg_left hf' hm0
      have hl := log_step2 (N (j + 1) - N j) (N j) hm0 hmN hNpos
      rw [show N j + (N (j + 1) - N j) = N (j + 1) by ring] at hl
      have hmax1 : max (N j) H = N j := max_eq_left hge
      have hmax2 : max (N (j + 1)) H = N (j + 1) := max_eq_left (le_trans hge (hmono j hj))
      rw [hmax1] at ih
      rw [hmax2]
      have e0 : (N (j + 1) - N j) * (β / N j) = β * ((N (j + 1) - N j) / N j) := by ring
      have e2 := mul_le_mul_of_nonneg_left hl hβ
      linarith
    · have hf' := hf j hj
      rw [if_neg hge] at hf'
      have hterm : (N (j + 1) - N j) * F j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0 hf'
      linarith

/-- Small-count potential: increments counted at `c` while `N < H`. -/
lemma seq_cnt (J : ℕ) (N : ℕ → ℝ) (H c : ℝ) (F : ℕ → ℝ) (hH : 0 ≤ H) (hc : 0 ≤ c)
    (hN0 : N 0 = 0) (hmono : ∀ k, k < J → N k ≤ N (k + 1))
    (hstep : ∀ k, k < J → N (k + 1) - N k ≤ H)
    (hf : ∀ k, k < J → F k ≤ if N k < H then c else 0) :
    ∀ j, j ≤ J → ∑ k ∈ Finset.range j, (N (k + 1) - N k) * F k ≤ c * min (N j) (2 * H) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, hN0]
    rw [min_eq_left (by linarith), mul_zero]
  | succ j ih' =>
    intro hjJ
    have hj : j < J := hjJ
    have ih := ih' (by omega)
    rw [Finset.sum_range_succ]
    have hm0 : 0 ≤ N (j + 1) - N j := by linarith [hmono j hj]
    by_cases hlt : N j < H
    · have hf' := hf j hj
      rw [if_pos hlt] at hf'
      have hterm : (N (j + 1) - N j) * F j ≤ (N (j + 1) - N j) * c :=
        mul_le_mul_of_nonneg_left hf' hm0
      have hmin1 : min (N j) (2 * H) = N j := min_eq_left (by linarith [hstep j hj])
      have hmin2 : min (N (j + 1)) (2 * H) = N (j + 1) := min_eq_left (by linarith [hstep j hj])
      rw [hmin1] at ih
      rw [hmin2]
      linarith
    · have hf' := hf j hj
      rw [if_neg hlt] at hf'
      have hterm : (N (j + 1) - N j) * F j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0 hf'
      have hmin : min (N j) (2 * H) ≤ min (N (j + 1)) (2 * H) := min_le_min (hmono j hj) le_rfl
      have := mul_le_mul_of_nonneg_left hmin hc
      linarith

end Pigeon2

section PigeonProc

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma cnt_episode (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (ω : Hoeffding.Outcomes S K H) (j : ℕ) (hj : j < K) :
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

lemma visit_single (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) (G : S → A → ℝ) :
    ∑ x : S, ∑ a : A, (if visit M δ sel init x a k h ω then G x a else 0) =
      G (stateAt init ω k (Fin.castSucc h)) (act M δ K H sel init ω k h) := by
  rw [← Fintype.sum_prod_type' (f := fun x a => if visit M δ sel init x a k h ω then G x a else 0)]
  rw [Finset.sum_eq_single (stateAt init ω k (Fin.castSucc h), act M δ K H sel init ω k h)]
  · have : visit M δ sel init (stateAt init ω k (Fin.castSucc h)) (act M δ K H sel init ω k h)
        k h ω := ⟨rfl, rfl⟩
    simp only [this, if_true]
  · intro p _ hne
    rw [if_neg]
    intro hv
    apply hne
    obtain ⟨h1, h2⟩ := hv
    exact Prod.ext h1.symm h2.symm
  · intro hn; exact absurd (Finset.mem_univ _) hn

lemma regroup (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (F : Fin K → S → A → ℝ) :
    ∑ k : Fin K, ∑ h : Fin H,
        F k (stateAt init ω k (Fin.castSucc h)) (act M δ K H sel init ω k h) =
      ∑ x : S, ∑ a : A, ∑ k : Fin K, F k x a *
        ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) := by
  calc ∑ k : Fin K, ∑ h : Fin H,
        F k (stateAt init ω k (Fin.castSucc h)) (act M δ K H sel init ω k h)
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

lemma cnt_zero (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (ω : Hoeffding.Outcomes S K H) : cnt M δ sel init x a 0 ω = 0 := by
  unfold cnt
  rw [vsum_ite]
  simp

lemma ep_visits_mem (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (x : S) (a : A) (ω : Hoeffding.Outcomes S K H) (k : Fin K) :
    0 ≤ ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) ∧
      ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) ≤ H := by
  constructor
  · exact Finset.sum_nonneg (fun h _ => by split_ifs <;> norm_num)
  · calc _ ≤ ∑ _h : Fin H, (1 : ℝ) := Finset.sum_le_sum (fun h _ => by split_ifs <;> norm_num)
      _ = H := by simp

/-- The per-pair sum along episodes as an increment sum of the visit counter. -/
lemma pair_rewrite (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (x : S) (a : A) (g : ℝ → ℝ) :
    ∑ k : Fin K, g (countSA (runState M δ K H sel init ω k.val) x a : ℝ) *
        ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) =
      ∑ j ∈ Finset.range K, (cnt M δ sel init x a ((j + 1) * H) ω -
        cnt M δ sel init x a (j * H) ω) * g (cnt M δ sel init x a (j * H) ω) := by
  rw [Finset.sum_range (fun j => (cnt M δ sel init x a ((j + 1) * H) ω -
        cnt M δ sel init x a (j * H) ω) * g (cnt M δ sel init x a (j * H) ω))]
  apply Finset.sum_congr rfl
  intro k _
  rw [cnt_episode M δ sel init x a ω k.val k.isLt,
    countSA_eq_cnt M δ sel init ω x a k.val k.isLt.le]
  simp only [Fin.eta]
  ring

end PigeonProc

section PigeonSums

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

/-- Count of the visited pair at step `(k,h)` (start-of-episode data). -/
noncomputable def nR (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) : ℕ :=
  countSA (runState M δ K H sel init ω k.val) (stateAt init ω k (Fin.castSucc h))
    (act M δ K H sel init ω k h)

noncomputable def psiR (H : ℕ) (t : ℝ) : ℝ := if (H : ℝ) ≤ t then 1 / t else 0

noncomputable def badR (H : ℕ) (t : ℝ) : ℝ := if t < (H : ℝ) then 1 else 0

lemma psiR_nonneg (H : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ psiR H t := by
  unfold psiR; split_ifs <;> positivity

lemma badR_nonneg (H : ℕ) (t : ℝ) : 0 ≤ badR H t := by
  unfold badR; split_ifs <;> norm_num

theorem sum_psi (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (hH : 0 < H) (hK : 0 < K) :
    ∑ k : Fin K, ∑ h : Fin H, psiR H (nR M δ sel init ω k h : ℝ) ≤
      2 * (Fintype.card S * Fintype.card A : ℝ) * Real.log K := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold nR
  rw [regroup M δ sel init ω
    (fun k x a => psiR H (countSA (runState M δ K H sel init ω k.val) x a : ℝ))]
  have hpair : ∀ x a, ∑ k : Fin K, psiR H (countSA (runState M δ K H sel init ω k.val) x a : ℝ) *
      ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) ≤ 2 * Real.log K := by
    intro x a
    rw [pair_rewrite M δ sel init ω x a (psiR H)]
    set N : ℕ → ℝ := fun j => cnt M δ sel init x a (j * H) ω with hNdef
    have hNe : ∀ j (hj : j < K), N (j + 1) = N j +
        ∑ h : Fin H, (if visit M δ sel init x a ⟨j, hj⟩ h ω then (1 : ℝ) else 0) :=
      fun j hj => cnt_episode M δ sel init x a ω j hj
    have hb := seq_log K N H 1 (fun j => psiR H (N j)) hHr zero_le_one
      (by simp only [N, zero_mul]; exact cnt_zero M δ sel init x a ω)
      (fun k hk => by rw [hNe k hk]; linarith [(ep_visits_mem M δ sel init x a ω ⟨k, hk⟩).1])
      (fun k hk => by rw [hNe k hk]; linarith [(ep_visits_mem M δ sel init x a ω ⟨k, hk⟩).2])
      (fun k _ => by simp only [psiR]; split_ifs <;> simp)
      K le_rfl
    refine le_trans hb ?_
    have hNK : N K ≤ (K : ℝ) * H := cnt_le M δ sel init x a (K * H) ω
    have hmaxle : max (N K) (H : ℝ) ≤ (K : ℝ) * H :=
      max_le hNK (le_mul_of_one_le_left (Nat.cast_nonneg H) hKr)
    have h1 : Real.log (max (N K) (H : ℝ)) ≤ Real.log ((K : ℝ) * H) :=
      Real.log_le_log (lt_max_of_lt_right hHr) hmaxle
    rw [Real.log_mul (by positivity) hHr.ne'] at h1
    linarith
  calc _ ≤ ∑ _x : S, ∑ _a : A, 2 * Real.log K :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun a _ => hpair x a))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem sum_bad (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) :
    ∑ k : Fin K, ∑ h : Fin H, badR H (nR M δ sel init ω k h : ℝ) ≤
      2 * (H : ℝ) * (Fintype.card S * Fintype.card A) := by
  unfold nR
  rw [regroup M δ sel init ω
    (fun k x a => badR H (countSA (runState M δ K H sel init ω k.val) x a : ℝ))]
  have hpair : ∀ x a, ∑ k : Fin K, badR H (countSA (runState M δ K H sel init ω k.val) x a : ℝ) *
      ∑ h : Fin H, (if visit M δ sel init x a k h ω then (1 : ℝ) else 0) ≤ 2 * H := by
    intro x a
    rw [pair_rewrite M δ sel init ω x a (badR H)]
    set N : ℕ → ℝ := fun j => cnt M δ sel init x a (j * H) ω with hNdef
    have hNe : ∀ j (hj : j < K), N (j + 1) = N j +
        ∑ h : Fin H, (if visit M δ sel init x a ⟨j, hj⟩ h ω then (1 : ℝ) else 0) :=
      fun j hj => cnt_episode M δ sel init x a ω j hj
    have hb := seq_cnt K N H 1 (fun j => badR H (N j)) (Nat.cast_nonneg H) zero_le_one
      (by simp only [N, zero_mul]; exact cnt_zero M δ sel init x a ω)
      (fun k hk => by rw [hNe k hk]; linarith [(ep_visits_mem M δ sel init x a ω ⟨k, hk⟩).1])
      (fun k hk => by rw [hNe k hk]; linarith [(ep_visits_mem M δ sel init x a ω ⟨k, hk⟩).2])
      (fun k _ => by simp only [badR]; split_ifs <;> simp)
      K le_rfl
    refine le_trans hb ?_
    rw [one_mul]
    exact min_le_right _ _
  calc _ ≤ ∑ _x : S, ∑ _a : A, 2 * (H : ℝ) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun a _ => hpair x a))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end PigeonSums

section XtSplit

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma sqrt_add_le2 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have e1 := Real.sq_sqrt ha
  have e2 := Real.sq_sqrt hb
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    linarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)

lemma sqrt_eq_of_sq (u v : ℝ) (hv : 0 ≤ v) (h : v ^ 2 = u) : Real.sqrt u = v := by
  rw [← h]; exact Real.sqrt_sq hv

lemma extraCap_mem (st : ModelState S A H) (L : ℝ) (h : Fin H) (y : S) :
    0 ≤ extraCap st L h y ∧ extraCap st L h y ≤ (H : ℝ) ^ 2 := by
  unfold extraCap
  simp only
  split_ifs
  · exact ⟨by positivity, le_rfl⟩
  · exact ⟨le_min (by positivity) (by positivity), min_le_right _ _⟩

lemma empExp_cap (M : Hoeffding.MDP S A) (st : ModelState S A H) (x : S) (a : A)
    (C : S → ℝ) (hC0 : ∀ y, 0 ≤ C y) (hCH : ∀ y, C y ≤ (H : ℝ) ^ 2) (η ℓ lam : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hq : 0 ≤ ℓ / (lam * (countSA st x a : ℝ)))
    (hGB : ∀ y, empiricalP st x a y - M.P x a y ≤
      η * M.P x a y + ℓ / (lam * (countSA st x a : ℝ))) :
    empiricalExp st x a C ≤ 2 * Pexp M x a C +
      Fintype.card S * ((H : ℝ) ^ 2 * (ℓ / (lam * (countSA st x a : ℝ)))) := by
  unfold empiricalExp finiteExp Pexp
  set q := ℓ / (lam * (countSA st x a : ℝ))
  have hP0 := (M.kernel x a).1
  have hterm : ∀ y, empiricalP st x a y * C y ≤ 2 * (M.P x a y * C y) + (H : ℝ) ^ 2 * q := by
    intro y
    have h1 : empiricalP st x a y ≤ (1 + η) * M.P x a y + q := by linarith [hGB y]
    have h2 := mul_le_mul_of_nonneg_right h1 (hC0 y)
    have h3 : (1 + η) * M.P x a y * C y ≤ 2 * (M.P x a y * C y) := by
      have := mul_nonneg (hP0 y) (hC0 y)
      linarith [mul_le_mul_of_nonneg_right hη1 this]
    have h4 : q * C y ≤ q * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (hCH y) hq
    linarith
  calc ∑ z, empiricalP st x a z * C z ≤ ∑ z, (2 * (M.P x a z * C z) + (H : ℝ) ^ 2 * q) :=
        Finset.sum_le_sum (fun y _ => hterm y)
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma Xt_split (M : Hoeffding.MDP S A) (st : ModelState S A H) (δ : ℝ) (K : ℕ)
    (π : Hoeffding.Policy S A H) (ℓ lam c : ℝ) (hH : 0 < H) (hℓ : 0 ≤ ℓ) (hlam : 0 < lam)
    (hη1 : etaB lam ≤ 1) (h : ℕ) (hh : h < H) (x : S) (a : A)
    (hGB : 0 < countSA st x a → ∀ y, empiricalP st x a y - M.P x a y ≤
      etaB lam * M.P x a y + ℓ / (lam * (countSA st x a : ℝ))) :
    Xt M st δ K π ℓ lam c h hh x a ≤
      H * badR H (countSA st x a : ℝ) +
      (Real.sqrt (2 * ℓ) + Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)) *
        Real.sqrt (cvar M x a (valueAt M π (h + 1))) * Real.sqrt (psiR H (countSA st x a : ℝ)) +
      (gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) lam c +
        Real.sqrt (8 * Fintype.card S * (H : ℝ) ^ 2 * ℓ / lam)) * psiR H (countSA st x a : ℝ) +
      4 * Real.sqrt (Pexp M x a
          (extraCap st (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) ⟨h, hh⟩)) *
        Real.sqrt (psiR H (countSA st x a : ℝ)) := by
  set La := algorithmLog δ (Fintype.card S) (Fintype.card A) K H with hLa
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hXH : Xt M st δ K π ℓ lam c h hh x a ≤ H := by
    unfold Xt; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  by_cases hlt : ((countSA st x a : ℕ) : ℝ) < H
  · have hb : badR H ((countSA st x a : ℕ) : ℝ) = 1 := if_pos hlt
    have hp : psiR H ((countSA st x a : ℕ) : ℝ) = 0 := if_neg (not_le.mpr hlt)
    rw [hb, hp, Real.sqrt_zero]
    simpa using hXH
  · have hge : (H : ℝ) ≤ (countSA st x a : ℕ) := not_lt.mp hlt
    have hb : badR H ((countSA st x a : ℕ) : ℝ) = 0 := if_neg hlt
    have hp : psiR H ((countSA st x a : ℕ) : ℝ) = 1 / ((countSA st x a : ℕ) : ℝ) := if_pos hge
    have hnr : (0 : ℝ) < (countSA st x a : ℕ) := lt_of_lt_of_le hHr hge
    have hn0 : countSA st x a ≠ 0 := by
      intro e; rw [e] at hnr; simp at hnr
    have hnpos : 0 < countSA st x a := Nat.pos_of_ne_zero hn0
    set n : ℝ := ((countSA st x a : ℕ) : ℝ) with hndef
    rw [hb, hp]
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
    have hsq : Real.sqrt (1 / n) = 1 / Real.sqrt n := by
      rw [Real.sqrt_div' 1 hnr.le, Real.sqrt_one]
    rw [hsq]
    have hcap := extraCap_mem st La ⟨h, hh⟩
    set C := extraCap st La ⟨h, hh⟩ with hCdef
    have hPC0 : 0 ≤ Pexp M x a C := Pexp_nonneg M x a C (fun y => (hcap y).1)
    have hq : 0 ≤ ℓ / (lam * n) := by positivity
    have hE := empExp_cap M st x a C (fun y => (hcap y).1) (fun y => (hcap y).2) (etaB lam) ℓ lam
      (etaB_nonneg lam hlam) hη1 hq (hGB hnpos)
    set PC := Pexp M x a C with hPCdef
    set c1 := 8 * Fintype.card S * (H : ℝ) ^ 2 * ℓ / lam with hc1
    have hc10 : 0 ≤ c1 := by positivity
    have hT3 : Real.sqrt (8 * empiricalExp st x a C / n) ≤
        4 * Real.sqrt PC * (1 / Real.sqrt n) + Real.sqrt c1 * (1 / n) := by
      have hE0 : 0 ≤ empiricalExp st x a C := by
        unfold empiricalExp finiteExp
        exact Finset.sum_nonneg (fun y _ => mul_nonneg (empP_nonneg st x a y) (hcap y).1)
      have h1 : 8 * empiricalExp st x a C / n ≤ 16 * PC / n + c1 / n ^ 2 := by
        have h2 : 8 * empiricalExp st x a C / n ≤
            8 * (2 * PC + Fintype.card S * ((H : ℝ) ^ 2 * (ℓ / (lam * n)))) / n :=
          div_le_div_of_nonneg_right (by linarith) hnr.le
        have h3 : 8 * (2 * PC + Fintype.card S * ((H : ℝ) ^ 2 * (ℓ / (lam * n)))) / n =
            16 * PC / n + c1 / n ^ 2 := by
          rw [hc1]; field_simp; ring
        linarith
      have h4 : 0 ≤ 16 * PC / n := by positivity
      have h5 : 0 ≤ c1 / n ^ 2 := by positivity
      calc Real.sqrt (8 * empiricalExp st x a C / n) ≤ Real.sqrt (16 * PC / n + c1 / n ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ ≤ Real.sqrt (16 * PC / n) + Real.sqrt (c1 / n ^ 2) := sqrt_add_le2 _ _ h4 h5
        _ = 4 * Real.sqrt PC * (1 / Real.sqrt n) + Real.sqrt c1 * (1 / n) := by
          congr 1
          · apply sqrt_eq_of_sq _ _ (by positivity)
            rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hPC0, Real.sq_sqrt hnr.le]; ring
          · apply sqrt_eq_of_sq _ _ (by positivity)
            rw [mul_pow, div_pow, Real.sq_sqrt hc10]; ring
    unfold Xt
    rw [if_neg hn0]
    refine le_trans (min_le_right _ _) ?_
    rw [← hLa, ← hCdef, ← hndef]
    have e1 : (Real.sqrt (2 * ℓ) + Real.sqrt (8 * La)) *
        Real.sqrt (cvar M x a (valueAt M π (h + 1))) / Real.sqrt n =
        (Real.sqrt (2 * ℓ) + Real.sqrt (8 * La)) *
        Real.sqrt (cvar M x a (valueAt M π (h + 1))) * (1 / Real.sqrt n) := by ring
    have e2 : gBeta H (Fintype.card S) ℓ La lam c / n =
        gBeta H (Fintype.card S) ℓ La lam c * (1 / n) := by ring
    rw [e1, e2]
    linarith [hT3]

/-- Variance and extra-cap statistics of the visited pair. -/
noncomputable def WR (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  cvar M (stateAt init ω k (Fin.castSucc h)) (act M δ K H sel init ω k h)
    (valueAt M (policyAt M δ K H sel init ω k) (h.val + 1))

noncomputable def PCR (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) : ℝ :=
  Pexp M (stateAt init ω k (Fin.castSucc h)) (act M δ K H sel init ω k h)
    (extraCap (runState M δ K H sel init ω k.val)
      (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) h)

lemma cvar_nonneg (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) : 0 ≤ cvar M x a f := by
  unfold cvar csq
  exact Finset.sum_nonneg (fun y _ => mul_nonneg ((M.kernel x a).1 y) (sq_nonneg _))

lemma PCR_nonneg (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) :
    0 ≤ PCR M δ sel init ω k h :=
  Pexp_nonneg M _ _ _ (fun y => (extraCap_mem _ _ h y).1)

lemma cs_double (f g : Fin K → Fin H → ℝ) (hf : ∀ k h, 0 ≤ f k h) (hg : ∀ k h, 0 ≤ g k h) :
    ∑ k, ∑ h, Real.sqrt (f k h) * Real.sqrt (g k h) ≤
      Real.sqrt (∑ k, ∑ h, f k h) * Real.sqrt (∑ k, ∑ h, g k h) := by
  rw [← Fintype.sum_prod_type' (f := fun k h => Real.sqrt (f k h) * Real.sqrt (g k h)),
    ← Fintype.sum_prod_type' (f := f), ← Fintype.sum_prod_type' (f := g)]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun p : Fin K × Fin H => Real.sqrt (f p.1 p.2))
    (fun p => Real.sqrt (g p.1 p.2))
  simp only [Real.sq_sqrt (hf _ _), Real.sq_sqrt (hg _ _)] at h
  exact h

/-- The summed step terms on the regret-side good event. -/
theorem sum_XtR (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ℓ lam c : ℝ) (hH : 0 < H) (hℓ : 0 ≤ ℓ) (hlam : 0 < lam) (hη1 : etaB lam ≤ 1)
    (hc : 0 < c) (hLa : 0 ≤ algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (ω : Hoeffding.Outcomes S K H) (hR : GoodReg M δ sel init ℓ lam ω) :
    ∑ k : Fin K, ∑ h : Fin H, XtR M δ sel init ℓ lam c ω k h ≤
      H * ∑ k : Fin K, ∑ h : Fin H, badR H (nR M δ sel init ω k h : ℝ) +
      (Real.sqrt (2 * ℓ) + Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)) *
        (Real.sqrt (∑ k : Fin K, ∑ h : Fin H, WR M δ sel init ω k h) *
          Real.sqrt (∑ k : Fin K, ∑ h : Fin H, psiR H (nR M δ sel init ω k h : ℝ))) +
      (gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) lam c +
        Real.sqrt (8 * Fintype.card S * (H : ℝ) ^ 2 * ℓ / lam)) *
        ∑ k : Fin K, ∑ h : Fin H, psiR H (nR M δ sel init ω k h : ℝ) +
      4 * (Real.sqrt (∑ k : Fin K, ∑ h : Fin H, PCR M δ sel init ω k h) *
          Real.sqrt (∑ k : Fin K, ∑ h : Fin H, psiR H (nR M δ sel init ω k h : ℝ))) := by
  set α := Real.sqrt (2 * ℓ) + Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
  set β := gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) lam c +
        Real.sqrt (8 * Fintype.card S * (H : ℝ) ^ 2 * ℓ / lam)
  have hstep : ∀ k : Fin K, ∀ h : Fin H, XtR M δ sel init ℓ lam c ω k h ≤
      H * badR H (nR M δ sel init ω k h : ℝ) +
      α * (Real.sqrt (WR M δ sel init ω k h) * Real.sqrt (psiR H (nR M δ sel init ω k h : ℝ))) +
      β * psiR H (nR M δ sel init ω k h : ℝ) +
      4 * (Real.sqrt (PCR M δ sel init ω k h) * Real.sqrt (psiR H (nR M δ sel init ω k h : ℝ))) := by
    intro k h
    have := Xt_split M (runState M δ K H sel init ω k.val) δ K (policyAt M δ K H sel init ω k)
      ℓ lam c hH hℓ hlam hη1 h.val h.isLt (stateAt init ω k (Fin.castSucc h))
      (act M δ K H sel init ω k h) (fun hpos => (hR k _ _ h hpos).2.2)
    unfold XtR
    unfold WR PCR nR
    simp only [Fin.eta] at this ⊢
    linarith
  have hψ : ∀ k h, 0 ≤ psiR H (nR M δ sel init ω k h : ℝ) :=
    fun k h => psiR_nonneg H _ (Nat.cast_nonneg _)
  have cs1 := cs_double (fun k h => WR M δ sel init ω k h)
    (fun k h => psiR H (nR M δ sel init ω k h : ℝ))
    (fun k h => cvar_nonneg M _ _ _) hψ
  have cs2 := cs_double (fun k h => PCR M δ sel init ω k h)
    (fun k h => psiR H (nR M δ sel init ω k h : ℝ))
    (fun k h => PCR_nonneg M δ sel init ω k h) hψ
  have hα : 0 ≤ α := by positivity
  calc ∑ k : Fin K, ∑ h : Fin H, XtR M δ sel init ℓ lam c ω k h
      ≤ ∑ k : Fin K, ∑ h : Fin H, (H * badR H (nR M δ sel init ω k h : ℝ) +
        α * (Real.sqrt (WR M δ sel init ω k h) * Real.sqrt (psiR H (nR M δ sel init ω k h : ℝ))) +
        β * psiR H (nR M δ sel init ω k h : ℝ) +
        4 * (Real.sqrt (PCR M δ sel init ω k h) *
          Real.sqrt (psiR H (nR M δ sel init ω k h : ℝ)))) :=
        Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun h _ => hstep k h))
    _ = H * ∑ k : Fin K, ∑ h : Fin H, badR H (nR M δ sel init ω k h : ℝ) +
        α * ∑ k : Fin K, ∑ h : Fin H, (Real.sqrt (WR M δ sel init ω k h) *
          Real.sqrt (psiR H (nR M δ sel init ω k h : ℝ))) +
        β * ∑ k : Fin K, ∑ h : Fin H, psiR H (nR M δ sel init ω k h : ℝ) +
        4 * ∑ k : Fin K, ∑ h : Fin H, (Real.sqrt (PCR M δ sel init ω k h) *
          Real.sqrt (psiR H (nR M δ sel init ω k h : ℝ))) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by
        have a1 := mul_le_mul_of_nonneg_left cs1 hα
        have a2 := mul_le_mul_of_nonneg_left cs2 (by norm_num : (0 : ℝ) ≤ 4)
        linarith

end XtSplit

section LTV

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

/-- Squared next value of the episode's policy. -/
noncomputable def FV (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ :=
  fun k h ω y => valueAt M (policyAt M δ K H sel init ω k) (h.val + 1) y ^ 2

lemma FV_adapted (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) :
    ∀ k h, Adapted (k.val * H + h.val) (FV (K := K) M δ sel init k h) := by
  intro k h ω ω' hag
  have hag0 : Agree (k.val * H) ω ω' := hag.mono (Nat.le_add_right _ _)
  funext y
  simp only [FV]
  rw [policyAt_eq M δ sel init ω ω' k hag0]

lemma valueAt_leH (M : Hoeffding.MDP S A) {H : ℕ} (π : Hoeffding.Policy S A H) (h : ℕ)
    (x : S) : valueAt M π h x ≤ H :=
  le_trans (valueAt_le M π h x) (by exact_mod_cast Nat.sub_le H h)

lemma FV_mem (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (k : Fin K) (h : Fin H) (ω : Hoeffding.Outcomes S K H) (y : S) :
    FV M δ sel init k h ω y ∈ Set.Icc 0 (0 + (H : ℝ) ^ 2) := by
  simp only [FV, zero_add, Set.mem_Icc]
  have h0 := valueAt_nonneg M (policyAt M δ K H sel init ω k) (h.val + 1) y
  have h1 := valueAt_leH M (policyAt M δ K H sel init ω k) (h.val + 1) y
  exact ⟨sq_nonneg _, pow_le_pow_left₀ h0 h1 2⟩

lemma valueAt_step (M : Hoeffding.MDP S A) {H : ℕ} (π : Hoeffding.Policy S A H) (h : ℕ)
    (hh : h < H) (x : S) :
    valueAt M π h x = M.R x (π x ⟨h, hh⟩) + Pexp M x (π x ⟨h, hh⟩) (valueAt M π (h + 1)) := by
  rw [valueAt, dif_pos hh]; rfl

lemma valueAt_top (M : Hoeffding.MDP S A) {H : ℕ} (π : Hoeffding.Policy S A H) (x : S) :
    valueAt M π H x = 0 := by
  rw [valueAt, dif_neg (lt_irrefl H)]

lemma cvar_eq2 (M : Hoeffding.MDP S A) (x : S) (a : A) (f : S → ℝ) :
    cvar M x a f = Pexp M x a (fun y => f y ^ 2) - (Pexp M x a f) ^ 2 := by
  rw [cvar_eq]; rfl

lemma W_step (M : Hoeffding.MDP S A) {H : ℕ} (π : Hoeffding.Policy S A H) (h : ℕ)
    (hh : h < H) (x : S) :
    cvar M x (π x ⟨h, hh⟩) (valueAt M π (h + 1)) ≤
      Pexp M x (π x ⟨h, hh⟩) (fun y => valueAt M π (h + 1) y ^ 2) - valueAt M π h x ^ 2 +
        2 * H := by
  have hv := valueAt_step M π h hh x
  have hR := M.reward_mem x (π x ⟨h, hh⟩)
  have hV0 := valueAt_nonneg M π h x
  have hVH := valueAt_leH M π h x
  rw [cvar_eq2]
  have e : Pexp M x (π x ⟨h, hh⟩) (valueAt M π (h + 1)) = valueAt M π h x - M.R x (π x ⟨h, hh⟩) := by
    linarith
  rw [e]
  have hRV : M.R x (π x ⟨h, hh⟩) * valueAt M π h x ≤ 1 * H :=
    mul_le_mul hR.2 hVH hV0 zero_le_one
  linarith [sq_nonneg (M.R x (π x ⟨h, hh⟩))]

/-- Squared value along episode `k` at time `j ≤ H`. -/
noncomputable def gT (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (k : Fin K) (j : ℕ) : ℝ :=
  if hj : j < H + 1 then
    valueAt M (policyAt M δ K H sel init ω k) j (stateAt init ω k ⟨j, hj⟩) ^ 2
  else 0

lemma stateAt_succ' (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (k : Fin K)
    (h : Fin H) (hj : h.val + 1 < H + 1) : stateAt init ω k ⟨h.val + 1, hj⟩ = ω k h := by
  unfold stateAt
  rw [dif_neg (by simp)]
  rfl

theorem sumW_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A) (init : InitialRule S H)
    (ω : Hoeffding.Outcomes S K H) :
    ∑ k : Fin K, ∑ h : Fin H, WR M δ sel init ω k h ≤
      2 * K * (H : ℝ) ^ 2 + ∑ p : Fin K × Fin H, mInc M δ sel init (FV M δ sel init) p.1 p.2 ω := by
  have hstep : ∀ k : Fin K, ∀ h : Fin H, WR M δ sel init ω k h ≤
      mInc M δ sel init (FV M δ sel init) k h ω +
        (gT M δ sel init ω k (h.val + 1) - gT M δ sel init ω k h.val) + 2 * H := by
    intro k h
    have hw := W_step M (policyAt M δ K H sel init ω k) h.val h.isLt
      (stateAt init ω k (Fin.castSucc h))
    have g1 : gT M δ sel init ω k (h.val + 1) =
        valueAt M (policyAt M δ K H sel init ω k) (h.val + 1) (ω k h) ^ 2 := by
      unfold gT
      rw [dif_pos (by omega), stateAt_succ']
    have g0 : gT M δ sel init ω k h.val =
        valueAt M (policyAt M δ K H sel init ω k) h.val (stateAt init ω k (Fin.castSucc h)) ^ 2 := by
      unfold gT
      rw [dif_pos (by omega)]
      rfl
    rw [g1, g0]
    unfold WR mInc FV qP act
    simp only [Fin.eta] at hw ⊢
    unfold Pexp at hw
    linarith
  have htel : ∀ k : Fin K, ∑ h : Fin H,
      (gT M δ sel init ω k (h.val + 1) - gT M δ sel init ω k h.val) ≤ 0 := by
    intro k
    rw [Fin.sum_univ_eq_sum_range (fun i => gT M δ sel init ω k (i + 1) - gT M δ sel init ω k i) H,
      Finset.sum_range_sub]
    have hT : gT M δ sel init ω k H = 0 := by
      unfold gT
      rw [dif_pos (by omega), valueAt_top]
      simp
    have h0 : 0 ≤ gT M δ sel init ω k 0 := by
      unfold gT; split_ifs <;> positivity
    linarith
  rw [Fintype.sum_prod_type]
  calc ∑ k : Fin K, ∑ h : Fin H, WR M δ sel init ω k h
      ≤ ∑ k : Fin K, ∑ h : Fin H, (mInc M δ sel init (FV M δ sel init) k h ω +
        (gT M δ sel init ω k (h.val + 1) - gT M δ sel init ω k h.val) + 2 * H) :=
        Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun h _ => hstep k h))
    _ = ∑ k : Fin K, (∑ h : Fin H, mInc M δ sel init (FV M δ sel init) k h ω +
        ∑ h : Fin H, (gT M δ sel init ω k (h.val + 1) - gT M δ sel init ω k h.val) +
        2 * (H : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl; intro k _
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
    _ ≤ ∑ k : Fin K, (∑ h : Fin H, mInc M δ sel init (FV M δ sel init) k h ω +
        2 * (H : ℝ) ^ 2) :=
        Finset.sum_le_sum (fun k _ => by linarith [htel k])
    _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end LTV

section CapSum

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

noncomputable def FC (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) : Fin K → Fin H → Hoeffding.Outcomes S K H → S → ℝ :=
  fun k h ω y => extraCap (runState M δ K H sel init ω k.val)
    (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) h y

lemma FC_adapted (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) :
    ∀ k h, Adapted (k.val * H + h.val) (FC (K := K) M δ sel init k h) := by
  intro k h ω ω' hag
  have hag0 : Agree (k.val * H) ω ω' := hag.mono (Nat.le_add_right _ _)
  funext y
  simp only [FC]
  rw [runState_eq M δ sel init ω ω' k.val hag0]

lemma FC_mem (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (k : Fin K) (h : Fin H) (ω : Hoeffding.Outcomes S K H) (y : S) :
    FC M δ sel init k h ω y ∈ Set.Icc 0 (0 + (H : ℝ) ^ 2) := by
  simp only [FC, zero_add, Set.mem_Icc]
  exact extraCap_mem _ _ h y

lemma PCR_split (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (k : Fin K) (h : Fin H) :
    PCR M δ sel init ω k h = mInc M δ sel init (FC M δ sel init) k h ω +
      extraCap (runState M δ K H sel init ω k.val)
        (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) h (ω k h) := by
  unfold PCR mInc FC qP Pexp
  ring

/-- Time-specific visit counter. -/
noncomputable def Nv (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (h : Fin H) (y : S) (j : ℕ) : ℝ :=
  ((runState M δ K H sel init ω j).visits (Fin.succ h) y : ℝ)

lemma Nv_zero (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (h : Fin H) (y : S) :
    Nv M δ sel init ω h y 0 = 0 := by
  simp [Nv, runState, initialModel]

lemma Nv_succ (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (h : Fin H) (y : S) (j : ℕ)
    (hj : j < K) :
    Nv M δ sel init ω h y (j + 1) = Nv M δ sel init ω h y j +
      (if ω ⟨j, hj⟩ h = y then 1 else 0) := by
  have hs : stateAt init ω ⟨j, hj⟩ (Fin.succ h) = ω ⟨j, hj⟩ h := by
    unfold stateAt
    rw [dif_neg (by simp)]
    congr 1
  simp only [Nv, runState, dif_pos hj, advance, hs]
  push_cast
  rfl

lemma Nv_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (h : Fin H) (y : S) :
    ∀ j, j ≤ K → Nv M δ sel init ω h y j ≤ j := by
  intro j
  induction j with
  | zero => intro _; rw [Nv_zero]; simp
  | succ j ih =>
    intro hj
    rw [Nv_succ M δ sel init ω h y j hj]
    have := ih (by omega)
    push_cast
    split_ifs <;> linarith

lemma extraCap_split (st : ModelState S A H) (L : ℝ) (h : Fin H) (y : S) :
    extraCap st L h y ≤
      (if ((st.visits (Fin.succ h) y : ℕ) : ℝ) < 1 then (H : ℝ) ^ 2 else 0) +
      (if (1 : ℝ) ≤ ((st.visits (Fin.succ h) y : ℕ) : ℝ) then
        ((100 : ℝ) ^ 2 * (H : ℝ) ^ 3 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2) /
          ((st.visits (Fin.succ h) y : ℕ) : ℝ) else 0) := by
  unfold extraCap
  simp only
  by_cases h0 : st.visits (Fin.succ h) y = 0
  · rw [if_pos h0, h0]; simp
  · rw [if_neg h0]
    have h1 : (1 : ℝ) ≤ ((st.visits (Fin.succ h) y : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    rw [if_neg (not_lt.mpr h1), if_pos h1, zero_add]
    exact min_le_left _ _

theorem sumCap_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (hK : 0 < K) :
    ∑ k : Fin K, ∑ h : Fin H, extraCap (runState M δ K H sel init ω k.val)
        (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) h (ω k h) ≤
      H * (Fintype.card S * (2 * (H : ℝ) ^ 2 + 2 * ((100 : ℝ) ^ 2 * (H : ℝ) ^ 3 *
        (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) *
        algorithmLog δ (Fintype.card S) (Fintype.card A) K H ^ 2) * Real.log K)) := by
  set La := algorithmLog δ (Fintype.card S) (Fintype.card A) K H
  set c0 := (100 : ℝ) ^ 2 * (H : ℝ) ^ 3 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * La ^ 2
    with hc0
  have hc00 : 0 ≤ c0 := by positivity
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  rw [Finset.sum_comm]
  have hper : ∀ h : Fin H, ∑ k : Fin K, extraCap (runState M δ K H sel init ω k.val) La h (ω k h) ≤
      Fintype.card S * (2 * (H : ℝ) ^ 2 + 2 * c0 * Real.log K) := by
    intro h
    have e1 : ∀ k : Fin K, extraCap (runState M δ K H sel init ω k.val) La h (ω k h) =
        ∑ y : S, (if ω k h = y then (1 : ℝ) else 0) *
          extraCap (runState M δ K H sel init ω k.val) La h y := by
      intro k
      rw [Finset.sum_eq_single (ω k h)]
      · simp
      · intro y _ hy; rw [if_neg (Ne.symm hy), zero_mul]
      · intro hn; exact absurd (Finset.mem_univ _) hn
    simp only [e1]
    rw [Finset.sum_comm]
    have hy : ∀ y : S, ∑ k : Fin K, (if ω k h = y then (1 : ℝ) else 0) *
        extraCap (runState M δ K H sel init ω k.val) La h y ≤ 2 * (H : ℝ) ^ 2 + 2 * c0 * Real.log K := by
      intro y
      set N : ℕ → ℝ := fun j => Nv M δ sel init ω h y j with hN
      have hrw : ∑ k : Fin K, (if ω k h = y then (1 : ℝ) else 0) *
          extraCap (runState M δ K H sel init ω k.val) La h y =
          ∑ j ∈ Finset.range K, (N (j + 1) - N j) *
            (fun j => extraCap (runState M δ K H sel init ω j) La h y) j := by
        rw [Finset.sum_range (fun j => (N (j + 1) - N j) *
            (fun j => extraCap (runState M δ K H sel init ω j) La h y) j)]
        apply Finset.sum_congr rfl; intro k _
        simp only [N]
        rw [Nv_succ M δ sel init ω h y k.val k.isLt]
        simp only [Fin.eta]
        ring
      rw [hrw]
      have hmono : ∀ k, k < K → N k ≤ N (k + 1) := by
        intro k hk; simp only [N]; rw [Nv_succ M δ sel init ω h y k hk]; split_ifs <;> linarith
      have hstep : ∀ k, k < K → N (k + 1) - N k ≤ 1 := by
        intro k hk; simp only [N]; rw [Nv_succ M δ sel init ω h y k hk]; split_ifs <;> linarith
      have hN0 : N 0 = 0 := Nv_zero M δ sel init ω h y
      let F1 : ℕ → ℝ := fun j => if N j < 1 then (H : ℝ) ^ 2 else 0
      let F2 : ℕ → ℝ := fun j => if (1 : ℝ) ≤ N j then c0 / N j else 0
      have hsplit : ∀ j ∈ Finset.range K, (N (j + 1) - N j) *
          extraCap (runState M δ K H sel init ω j) La h y ≤
          (N (j + 1) - N j) * F1 j + (N (j + 1) - N j) * F2 j := by
        intro j hj
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (by linarith [hmono j (Finset.mem_range.mp hj)])
        exact extraCap_split _ La h y
      have b1 := seq_cnt K N 1 ((H : ℝ) ^ 2) F1 zero_le_one (by positivity) hN0 hmono hstep
        (fun k _ => le_rfl) K le_rfl
      have b2 := seq_log K N 1 c0 F2 zero_lt_one hc00 hN0 hmono hstep
        (fun k _ => le_rfl) K le_rfl
      have hNK : N K ≤ K := Nv_le M δ sel init ω h y K le_rfl
      have hlog : Real.log (max (N K) 1) ≤ Real.log K :=
        Real.log_le_log (lt_max_of_lt_right zero_lt_one) (max_le hNK hKr)
      have hmin : min (N K) (2 * 1) ≤ 2 := by
        have := min_le_right (N K) (2 * (1 : ℝ)); linarith
      have m1 := mul_le_mul_of_nonneg_left hmin (by positivity : (0 : ℝ) ≤ (H : ℝ) ^ 2)
      have m2 := mul_le_mul_of_nonneg_left (by rw [Real.log_one, sub_zero]; exact hlog :
        Real.log (max (N K) 1) - Real.log 1 ≤ Real.log K) (by positivity : (0 : ℝ) ≤ 2 * c0)
      calc ∑ j ∈ Finset.range K, (N (j + 1) - N j) *
            (fun j => extraCap (runState M δ K H sel init ω j) La h y) j
          ≤ ∑ j ∈ Finset.range K, ((N (j + 1) - N j) * F1 j + (N (j + 1) - N j) * F2 j) :=
            Finset.sum_le_sum hsplit
        _ = ∑ j ∈ Finset.range K, (N (j + 1) - N j) * F1 j +
            ∑ j ∈ Finset.range K, (N (j + 1) - N j) * F2 j := Finset.sum_add_distrib
        _ ≤ _ := by linarith
    calc ∑ y : S, ∑ k : Fin K, (if ω k h = y then (1 : ℝ) else 0) *
          extraCap (runState M δ K H sel init ω k.val) La h y
        ≤ ∑ _y : S, (2 * (H : ℝ) ^ 2 + 2 * c0 * Real.log K) := Finset.sum_le_sum (fun y _ => hy y)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ∑ h : Fin H, ∑ k : Fin K, extraCap (runState M δ K H sel init ω k.val) La h (ω k h)
      ≤ ∑ _h : Fin H, Fintype.card S * (2 * (H : ℝ) ^ 2 + 2 * c0 * Real.log K) :=
        Finset.sum_le_sum (fun h _ => hper h)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sumPC_le (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (ω : Hoeffding.Outcomes S K H) (hK : 0 < K) :
    ∑ k : Fin K, ∑ h : Fin H, PCR M δ sel init ω k h ≤
      ∑ p : Fin K × Fin H, mInc M δ sel init (FC M δ sel init) p.1 p.2 ω +
      H * (Fintype.card S * (2 * (H : ℝ) ^ 2 + 2 * ((100 : ℝ) ^ 2 * (H : ℝ) ^ 3 *
        (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) *
        algorithmLog δ (Fintype.card S) (Fintype.card A) K H ^ 2) * Real.log K)) := by
  have hc := sumCap_le M δ sel init ω hK
  simp only [PCR_split, Finset.sum_add_distrib]
  rw [Fintype.sum_prod_type]
  linarith

end CapSum

section Numeric

lemma sqrt_le_of_sq' (x y : ℝ) (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y :=
  le_trans (Real.sqrt_le_sqrt h) (le_of_eq (Real.sqrt_sq hy))

lemma beta_bound (h s ℓ La L u : ℝ) (hh : 1 ≤ h) (hs : 1 ≤ s) (hLa0 : 0 ≤ La) (hLaL : La ≤ L)
    (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ 2 * L) (hu1 : 1 ≤ u) (hu2 : u ^ 2 = L) :
    gBeta h s ℓ La (1 / (10 * h)) 10 + Real.sqrt (8 * s * h ^ 2 * ℓ / (1 / (10 * h))) ≤
      283 * s * h ^ 2 * L := by
  have h0 : 0 ≤ h := by linarith only [hh]
  have s0 : 0 ≤ s := by linarith only [hs]
  have hL1 : 1 ≤ L := by rw [← hu2]; nlinarith only [hu1]
  have huL : u ≤ L := by rw [← hu2]; linarith only [mul_nonneg (by linarith only [hu1] : (0 : ℝ) ≤ u) (by linarith only [hu1] : (0 : ℝ) ≤ u - 1)]
  have hα1 : Real.sqrt (2 * ℓ) ≤ 2 * u :=
    sqrt_le_of_sq' _ _ (by linarith only [hu1]) (by rw [mul_pow, hu2]; linarith only [hℓL])
  have hα2 : Real.sqrt (8 * La) ≤ 3 * u :=
    sqrt_le_of_sq' _ _ (by linarith only [hu1]) (by rw [mul_pow, hu2]; linarith only [hLaL, hL1])
  have r0 := Real.sqrt_nonneg (2 * ℓ)
  have r1 := Real.sqrt_nonneg (8 * La)
  unfold gBeta
  simp only [div_div_eq_mul_div, div_one]
  have hsh : 1 ≤ s * h := one_le_mul_of_one_le_of_one_le hs hh
  have L0 : 0 ≤ L := by linarith only [hL1]
  have hhs : h ≤ s * h ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsh h0
    linarith only [this]
  have hh2 : h ^ 2 ≤ s * h ^ 2 := by
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg h)
    linarith only [this]
  have hb4 : Real.sqrt (s * ℓ * (10 * h)) ≤ 5 * s * h * u := by
    apply sqrt_le_of_sq' _ _ (by positivity)
    rw [mul_pow, mul_pow, mul_pow, hu2]
    have : s * ℓ * (10 * h) ≤ 20 * (s * h) * L := by
      have := mul_le_mul_of_nonneg_left hℓL (by positivity : (0 : ℝ) ≤ 10 * (s * h))
      linarith only [this]
    have k1 : s * h ≤ s * h * (s * h) := le_mul_of_one_le_right (by positivity) hsh
    have k2 := mul_le_mul_of_nonneg_right k1 L0
    have k3 : 0 ≤ s * h * (s * h) * L := by positivity
    linarith only [this, k2, k3]
  have hb7 : Real.sqrt (8 * s * h ^ 2 * ℓ * (10 * h)) ≤ 13 * s * h ^ 2 * u := by
    apply sqrt_le_of_sq' _ _ (by positivity)
    rw [mul_pow, mul_pow, mul_pow, hu2]
    have e1 : 8 * s * h ^ 2 * ℓ * (10 * h) ≤ 160 * (s * h ^ 3) * L := by
      have := mul_le_mul_of_nonneg_left hℓL (by positivity : (0 : ℝ) ≤ 80 * (s * h ^ 3))
      linarith only [this]
    have e2 : s * h ^ 3 ≤ s ^ 2 * (h ^ 2) ^ 2 := by
      have : s * h ^ 3 * 1 ≤ s * h ^ 3 * (s * h) := mul_le_mul_of_nonneg_left hsh (by positivity)
      linarith only [this]
    have e3 : 0 ≤ L := L0
    have e4 := mul_le_mul_of_nonneg_right e2 e3
    have e5 : 0 ≤ s ^ 2 * (h ^ 2) ^ 2 * L := by positivity
    linarith only [e1, e4, e5]
  have hb3 : Real.sqrt (2 * ℓ) * Real.sqrt (8 * La) ≤ 2 * u * (3 * u) :=
    mul_le_mul hα1 hα2 r1 (by linarith only [hu1])
  have hb4' : Real.sqrt (8 * La) * Real.sqrt (s * ℓ * (10 * h)) ≤ 3 * u * (5 * s * h * u) :=
    mul_le_mul hα2 hb4 (Real.sqrt_nonneg _) (by linarith only [hu1])
  have hb6 : (Real.sqrt (2 * ℓ) + 5 / 2 * Real.sqrt (8 * La)) ^ 2 ≤ (19 / 2 * u) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hα1, hα2]) 2
  rw [mul_pow, hu2] at hb6
  have hhL := mul_le_mul_of_nonneg_right hhs L0
  have t1 : h * ℓ / 3 ≤ 2 / 3 * (s * h ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left hℓL h0
    linarith only [this, hhL]
  have t2 : s * h * ℓ * (10 * h) ≤ 20 * (s * h ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left hℓL (by positivity : (0 : ℝ) ≤ 10 * (s * h ^ 2))
    linarith only [this]
  have t3 : h * Real.sqrt (2 * ℓ) * Real.sqrt (8 * La) / 2 ≤ 3 * (s * h ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left hb3 h0
    have e : 2 * u * (3 * u) = 6 * L := by rw [← hu2]; ring
    rw [e] at this
    linarith only [this, hhL]
  have t4 : h * Real.sqrt (8 * La) * Real.sqrt (s * ℓ * (10 * h)) ≤ 15 * (s * h ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left hb4' h0
    have e : h * (3 * u * (5 * s * h * u)) = 15 * (s * h ^ 2 * L) := by rw [← hu2]; ring
    rw [e] at this
    linarith only [this]
  have t5 : 14 * h * La / 3 ≤ 14 / 3 * (s * h ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left hLaL h0
    linarith only [this, hhL]
  have t6 : 10 * (Real.sqrt (2 * ℓ) + 5 / 2 * Real.sqrt (8 * La)) ^ 2 * h ^ 2 / 4 ≤
      226 * (s * h ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left hb6 (by positivity : (0 : ℝ) ≤ 10 * h ^ 2 / 4)
    have k3 := mul_le_mul_of_nonneg_right hh2 L0
    have k4 : 0 ≤ h ^ 2 * L := by positivity
    linarith only [this, k3, k4]
  have t7 : 13 * s * h ^ 2 * u ≤ 13 * (s * h ^ 2 * L) := by
    have := mul_le_mul_of_nonneg_left huL (by positivity : (0 : ℝ) ≤ s * h ^ 2)
    linarith only [this]
  have hpos : 0 ≤ s * h ^ 2 * L := by positivity
  linarith only [t1, t2, t3, t4, t5, t6, t7, hb7, hpos]

set_option maxHeartbeats 400000 in
lemma final_numeric (h s a k L La ℓ lK G : ℝ)
    (hh : 1 ≤ h) (hs : 1 ≤ s) (ha : 1 ≤ a) (hk : 1 ≤ k) (hL : 1 ≤ L) (hLa0 : 0 ≤ La)
    (hLaL : La ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ 2 * L) (hlK0 : 0 ≤ lK) (hlK : lK ≤ L)
    (hG0 : 0 ≤ G) (hG : G ≤ 5 / 4) (hreg : h * ℓ ≤ 2 * k) :
    G * (h * (2 * h * (s * a)) +
        (Real.sqrt (2 * ℓ) + Real.sqrt (8 * La)) *
          (Real.sqrt (2 * k * h ^ 2 + h ^ 2 * Real.sqrt (k * h * ℓ / 2)) *
            Real.sqrt (2 * (s * a) * lK)) +
        (gBeta h s ℓ La (1 / (10 * h)) 10 + Real.sqrt (8 * s * h ^ 2 * ℓ / (1 / (10 * h)))) *
          (2 * (s * a) * lK) +
        4 * (Real.sqrt (h ^ 2 * Real.sqrt (k * h * ℓ / 2) + h * (s *
            (2 * h ^ 2 + 2 * ((100 : ℝ) ^ 2 * h ^ 3 * s ^ 2 * a * La ^ 2) * lK))) *
          Real.sqrt (2 * (s * a) * lK))) +
      G * h * Real.sqrt (k * h * ℓ / 2) ≤
    30 * h * L * Real.sqrt (s * a * k) + 2500 * h ^ 2 * s ^ 2 * a * L ^ 2 +
      4 * h * Real.sqrt h * Real.sqrt (k * L) := by
  have h0 : 0 ≤ h := by linarith only [hh]
  have s0 : 0 ≤ s := by linarith only [hs]
  have a0 : 0 ≤ a := by linarith only [ha]
  have k0 : 0 ≤ k := by linarith only [hk]
  have L0 : 0 ≤ L := by linarith only [hL]
  set u := Real.sqrt L with hu
  have hu2 : u ^ 2 = L := Real.sq_sqrt L0
  have hu1 : 1 ≤ u := by
    have := Real.sqrt_le_sqrt hL
    rwa [Real.sqrt_one] at this
  have huL : u ≤ L := by
    rw [← hu2]; linarith only [mul_nonneg (by linarith only [hu1] : (0 : ℝ) ≤ u) (by linarith only [hu1] : (0 : ℝ) ≤ u - 1)]
  set q := Real.sqrt (s * a * k) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = s * a * k := Real.sq_sqrt (by positivity)
  set P := h ^ 2 * s ^ 2 * a * L ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hα1 : Real.sqrt (2 * ℓ) ≤ 2 * u :=
    sqrt_le_of_sq' _ _ (by linarith only [hu1]) (by rw [mul_pow, hu2]; linarith only [hℓL])
  have hα2 : Real.sqrt (8 * La) ≤ 3 * u :=
    sqrt_le_of_sq' _ _ (by linarith only [hu1]) (by rw [mul_pow, hu2]; linarith only [hLaL, hL])
  have hα : Real.sqrt (2 * ℓ) + Real.sqrt (8 * La) ≤ 5 * u := by linarith only [hα1, hα2]
  -- the martingale square root
  have hsq : Real.sqrt (k * h * ℓ / 2) ≤ k := by
    apply sqrt_le_of_sq' _ _ k0
    have := mul_le_mul_of_nonneg_left hreg k0
    linarith only [this]
  have hsq0 : 0 ≤ Real.sqrt (k * h * ℓ / 2) := Real.sqrt_nonneg _
  have hΨ : 2 * (s * a) * lK ≤ 2 * (s * a) * L :=
    mul_le_mul_of_nonneg_left hlK (by positivity)
  have hΨ0 : 0 ≤ 2 * (s * a) * lK := by positivity
  -- variance term
  have hW1 : 2 * k * h ^ 2 + h ^ 2 * Real.sqrt (k * h * ℓ / 2) ≤ 3 * k * h ^ 2 := by
    linarith only [mul_le_mul_of_nonneg_left hsq (sq_nonneg h)]
  have hW0 : 0 ≤ 2 * k * h ^ 2 + h ^ 2 * Real.sqrt (k * h * ℓ / 2) := by positivity
  have hTW : Real.sqrt (2 * k * h ^ 2 + h ^ 2 * Real.sqrt (k * h * ℓ / 2)) *
      Real.sqrt (2 * (s * a) * lK) ≤ 49 / 20 * h * q * u := by
    rw [← Real.sqrt_mul hW0]
    apply sqrt_le_of_sq' _ _ (by positivity)
    have e : (49 / 20 * h * q * u) ^ 2 = (49 / 20) ^ 2 * (h ^ 2 * (s * a * k) * L) := by
      rw [mul_pow, mul_pow, mul_pow, hq2, hu2]; ring
    rw [e]
    have := mul_le_mul hW1 hΨ hΨ0 (by positivity)
    have hpos : 0 ≤ h ^ 2 * (s * a * k) * L := by positivity
    linarith only [this, hpos]
  have hA : (Real.sqrt (2 * ℓ) + Real.sqrt (8 * La)) *
      (Real.sqrt (2 * k * h ^ 2 + h ^ 2 * Real.sqrt (k * h * ℓ / 2)) *
        Real.sqrt (2 * (s * a) * lK)) ≤ 49 / 4 * (h * q * L) := by
    have := mul_le_mul hα hTW (by positivity) (by linarith only [hu1])
    have e : 5 * u * (49 / 20 * h * q * u) = 49 / 4 * (h * q * L) := by rw [← hu2]; ring
    linarith only [this, e]
  -- extra-cap term
  have hLa2 : La ^ 2 * lK ≤ L ^ 2 * L :=
    mul_le_mul (pow_le_pow_left₀ hLa0 hLaL 2) hlK hlK0 (by positivity)
  have hPC1 : h ^ 2 * Real.sqrt (k * h * ℓ / 2) + h * (s *
      (2 * h ^ 2 + 2 * ((100 : ℝ) ^ 2 * h ^ 3 * s ^ 2 * a * La ^ 2) * lK)) ≤
      h ^ 2 * k + 2 * (h ^ 3 * s) + 20000 * (h ^ 4 * s ^ 3 * a * L ^ 3) := by
    have e1 := mul_le_mul_of_nonneg_left hsq (sq_nonneg h)
    have e2 := mul_le_mul_of_nonneg_left hLa2
      (by positivity : (0 : ℝ) ≤ 20000 * (h ^ 4 * s ^ 3 * a))
    linarith only [e1, e2]
  have hPC0 : 0 ≤ h ^ 2 * Real.sqrt (k * h * ℓ / 2) + h * (s *
      (2 * h ^ 2 + 2 * ((100 : ℝ) ^ 2 * h ^ 3 * s ^ 2 * a * La ^ 2) * lK)) := by positivity
  have hmono : h ^ 3 * s ^ 2 * a * L ≤ P ^ 2 := by
    have e : P ^ 2 = (h ^ 3 * s ^ 2 * a * L) * (h * s ^ 2 * a * L ^ 3) := by rw [hP]; ring
    have h1 : 1 ≤ h * s ^ 2 * a * L ^ 3 := by
      have := one_le_mul_of_one_le_of_one_le hh (one_le_pow₀ hs : (1 : ℝ) ≤ s ^ 2)
      have := one_le_mul_of_one_le_of_one_le this ha
      exact one_le_mul_of_one_le_of_one_le this (one_le_pow₀ hL)
    rw [e]
    exact le_mul_of_one_le_right (by positivity) h1
  have hTC : Real.sqrt (h ^ 2 * Real.sqrt (k * h * ℓ / 2) + h * (s *
      (2 * h ^ 2 + 2 * ((100 : ℝ) ^ 2 * h ^ 3 * s ^ 2 * a * La ^ 2) * lK))) *
      Real.sqrt (2 * (s * a) * lK) ≤ 283 / 200 * h * q * u + 201 * P := by
    rw [← Real.sqrt_mul hPC0]
    apply sqrt_le_of_sq' _ _ (by positivity)
    have hprod := mul_le_mul hPC1 hΨ hΨ0 (by positivity)
    have e : (h ^ 2 * k + 2 * (h ^ 3 * s) + 20000 * (h ^ 4 * s ^ 3 * a * L ^ 3)) *
        (2 * (s * a) * L) = 2 * (h ^ 2 * (s * a * k) * L) + 4 * (h ^ 3 * s ^ 2 * a * L) +
          40000 * P ^ 2 := by rw [hP]; ring
    rw [e] at hprod
    have e2 : (283 / 200 * h * q * u + 201 * P) ^ 2 =
        (283 / 200) ^ 2 * (h ^ 2 * (s * a * k) * L) + 2 * (283 / 200 * 201) * (h * q * u * P) +
          201 ^ 2 * P ^ 2 := by
      have : (283 / 200 * h * q * u) ^ 2 = (283 / 200) ^ 2 * (h ^ 2 * (s * a * k) * L) := by
        rw [mul_pow, mul_pow, mul_pow, hq2, hu2]; ring
      rw [add_sq, this]; ring
    rw [e2]
    have hpos : 0 ≤ h ^ 2 * (s * a * k) * L := by positivity
    have hpos2 : 0 ≤ h * q * u * P := by positivity
    have hP2 : 0 ≤ P ^ 2 := sq_nonneg P
    linarith only [hprod, hpos, hpos2, hP2, hmono]
  -- second-order term
  have hβ := beta_bound h s ℓ La L u hh hs hLa0 hLaL hℓ0 hℓL hu1 hu2
  have hB : (gBeta h s ℓ La (1 / (10 * h)) 10 + Real.sqrt (8 * s * h ^ 2 * ℓ / (1 / (10 * h)))) *
      (2 * (s * a) * lK) ≤ 566 * P := by
    have e1 := mul_le_mul_of_nonneg_right hβ hΨ0
    have e2 := mul_le_mul_of_nonneg_left hΨ (by positivity : (0 : ℝ) ≤ 283 * s * h ^ 2 * L)
    have e : 283 * s * h ^ 2 * L * (2 * (s * a) * L) = 566 * P := by rw [hP]; ring
    linarith only [e1, e2, e]
  -- small counts
  have hbad : h * (2 * h * (s * a)) ≤ 2 * P := by
    have e1 : s * a ≤ s ^ 2 * a * L ^ 2 := by
      have : 1 ≤ s * L ^ 2 := one_le_mul_of_one_le_of_one_le hs (one_le_pow₀ hL)
      linarith only [mul_le_mul_of_nonneg_left this (mul_nonneg s0 a0)]
    have := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 2 * h ^ 2)
    rw [hP]; linarith only [this]
  -- martingale term
  have hM : Real.sqrt (k * h * ℓ / 2) ≤ Real.sqrt h * Real.sqrt (k * L) := by
    rw [← Real.sqrt_mul h0]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hℓL (mul_nonneg k0 h0)
    linarith only [this]
  have hrh : 0 ≤ Real.sqrt h * Real.sqrt (k * L) := by positivity
  -- assemble
  have hbr : h * (2 * h * (s * a)) +
        (Real.sqrt (2 * ℓ) + Real.sqrt (8 * La)) *
          (Real.sqrt (2 * k * h ^ 2 + h ^ 2 * Real.sqrt (k * h * ℓ / 2)) *
            Real.sqrt (2 * (s * a) * lK)) +
        (gBeta h s ℓ La (1 / (10 * h)) 10 + Real.sqrt (8 * s * h ^ 2 * ℓ / (1 / (10 * h)))) *
          (2 * (s * a) * lK) +
        4 * (Real.sqrt (h ^ 2 * Real.sqrt (k * h * ℓ / 2) + h * (s *
            (2 * h ^ 2 + 2 * ((100 : ℝ) ^ 2 * h ^ 3 * s ^ 2 * a * La ^ 2) * lK))) *
          Real.sqrt (2 * (s * a) * lK)) ≤ 18 * (h * q * L) + 1372 * P := by
    have hqu : h * q * u ≤ h * q * L := mul_le_mul_of_nonneg_left huL (by positivity)
    have hqL0 : 0 ≤ h * q * L := by positivity
    linarith only [hbad, hA, hB, hTC, hqu, hqL0]
  have hb0 : 0 ≤ 18 * (h * q * L) + 1372 * P := by positivity
  have g1 := mul_le_mul_of_nonneg_left hbr hG0
  have g2 := mul_le_mul_of_nonneg_right hG hb0
  have g3 : G * h * Real.sqrt (k * h * ℓ / 2) ≤ 5 / 4 * h * (Real.sqrt h * Real.sqrt (k * L)) := by
    have := mul_le_mul hG (mul_le_mul_of_nonneg_left hM h0) (by positivity) (by norm_num)
    linarith only [this]
  have e3 : 30 * h * L * q = 30 * (h * q * L) := by ring
  have e4 : 2500 * h ^ 2 * s ^ 2 * a * L ^ 2 = 2500 * P := by rw [hP]; ring
  have e5 : 4 * h * Real.sqrt h * Real.sqrt (k * L) = 4 * (h * (Real.sqrt h * Real.sqrt (k * L))) := by
    ring
  have hpos3 : 0 ≤ h * (Real.sqrt h * Real.sqrt (k * L)) := by positivity
  have hpos4 : 0 ≤ h * q * L := by positivity
  rw [e3, e4, e5]
  linarith only [g1, g2, g3, hpos3, hpos4, hP0]

end Numeric

section Final

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] {K H : ℕ}

lemma gamma_le (H : ℕ) (hH : 0 < H) :
    (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ))) ^ H ≤ 5 / 4 := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlam : 0 < 1 / (10 * (H : ℝ)) := by positivity
  have hlam1 : 1 / (10 * (H : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hη := etaB_le _ hlam hlam1
  have hη0 := etaB_nonneg _ hlam
  have hg : 1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ)) ≤
      Real.exp (2 * (1 / (10 * (H : ℝ)))) := by
    have := Real.add_one_le_exp (2 * (1 / (10 * (H : ℝ)))); linarith
  have h1 := pow_le_pow_left₀ (by linarith) hg H
  rw [← Real.exp_nat_mul] at h1
  have hHl : (H : ℝ) * (2 * (1 / (10 * (H : ℝ)))) = 1 / 5 := by field_simp; ring
  rw [hHl] at h1
  have h2 := Real.add_one_le_exp (-(1 / 5 : ℝ))
  have h3 : Real.exp (1 / 5) * Real.exp (-(1 / 5)) = 1 := by rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos (1 / 5 : ℝ)
  have h5 := mul_le_mul_of_nonneg_left h2 h4.le
  linarith

lemma gamma_ge (H : ℕ) (hH : 0 < H) :
    1 ≤ 1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ)) := by
  have hlam : 0 < 1 / (10 * (H : ℝ)) := by
    have : (0 : ℝ) < H := by exact_mod_cast hH
    positivity
  have := etaB_nonneg _ hlam
  linarith

/-- Deterministic regret bound on the five good events, before numerics. -/
theorem regret_raw (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) (init : InitialRule S H)
    (ℓ : ℝ) (hH : 0 < H) (hK : 0 < K) (hℓ : 0 < ℓ)
    (hℓLa : ℓ ≤ 3 / 2 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
    (ω : Hoeffding.Outcomes S K H) (hG : GoodOpt M δ sel init ℓ ω)
    (hR : GoodReg M δ sel init ℓ (1 / (10 * H)) ω)
    (hAz1 : ∑ p : Fin K × Fin H, mInc M δ sel init
        (Fgc M δ sel init (1 + etaB (1 / (10 * H)) + 1 / (10 * H))) p.1 p.2 ω ≤
      (1 + etaB (1 / (10 * H)) + 1 / (10 * H)) ^ H * H * Real.sqrt (K * H * ℓ / 2))
    (hAz2 : ∑ p : Fin K × Fin H, mInc M δ sel init (FV M δ sel init) p.1 p.2 ω ≤
      (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2))
    (hAz3 : ∑ p : Fin K × Fin H, mInc M δ sel init (FC M δ sel init) p.1 p.2 ω ≤
      (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2)) :
    regret M δ K H sel init ω ≤
      (1 + etaB (1 / (10 * H)) + 1 / (10 * H)) ^ H *
        (H * (2 * H * (Fintype.card S * Fintype.card A)) +
        (Real.sqrt (2 * ℓ) + Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)) *
          (Real.sqrt (2 * K * (H : ℝ) ^ 2 + (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2)) *
            Real.sqrt (2 * (Fintype.card S * Fintype.card A) * Real.log K)) +
        (gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
            (1 / (10 * H)) 10 +
          Real.sqrt (8 * Fintype.card S * (H : ℝ) ^ 2 * ℓ / (1 / (10 * H)))) *
          (2 * (Fintype.card S * Fintype.card A) * Real.log K) +
        4 * (Real.sqrt ((H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2) + H * (Fintype.card S *
            (2 * (H : ℝ) ^ 2 + 2 * ((100 : ℝ) ^ 2 * (H : ℝ) ^ 3 * (Fintype.card S : ℝ) ^ 2 *
              (Fintype.card A : ℝ) * algorithmLog δ (Fintype.card S) (Fintype.card A) K H ^ 2) *
                Real.log K))) *
          Real.sqrt (2 * (Fintype.card S * Fintype.card A) * Real.log K))) +
      (1 + etaB (1 / (10 * H)) + 1 / (10 * H)) ^ H * H * Real.sqrt (K * H * ℓ / 2) := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlam : 0 < 1 / (10 * (H : ℝ)) := by positivity
  have hlam1 : 1 / (10 * (H : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith only [hHr]
  have hη1 : etaB (1 / (10 * (H : ℝ))) ≤ 1 := le_trans (etaB_le _ hlam hlam1) hlam1
  have hLa : 0 ≤ algorithmLog δ (Fintype.card S) (Fintype.card A) K H := by linarith only [hℓ, hℓLa]
  have hr := regret_good M δ sel hsel init ℓ ℓ (1 / (10 * H)) 10 hH hℓ.le hℓLa hℓ.le hlam hlam1
    (by norm_num) ω hG hR _ hAz1
  have hX := sum_XtR M δ sel init ℓ (1 / (10 * H)) 10 hH hℓ.le hlam hη1 (by norm_num) hLa ω hR
  have hbad := sum_bad M δ sel init ω
  have hpsi := sum_psi M δ sel init ω hH hK
  have hW := sumW_le M δ sel init ω
  have hPC := sumPC_le M δ sel init ω hK
  have hG0 : 0 ≤ (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ))) ^ H :=
    pow_nonneg (by linarith only [gamma_ge H hH]) _
  have hψ0 : 0 ≤ ∑ k : Fin K, ∑ h : Fin H, psiR H (nR M δ sel init ω k h : ℝ) :=
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
      (fun h _ => psiR_nonneg H _ (Nat.cast_nonneg _)))
  have s1 := Real.sqrt_le_sqrt (show ∑ k : Fin K, ∑ h : Fin H, WR M δ sel init ω k h ≤
    2 * K * (H : ℝ) ^ 2 + (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2) by linarith only [hW, hAz2])
  have s2 := Real.sqrt_le_sqrt hpsi
  have s3 := Real.sqrt_le_sqrt (show ∑ k : Fin K, ∑ h : Fin H, PCR M δ sel init ω k h ≤
    (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2) + H * (Fintype.card S *
            (2 * (H : ℝ) ^ 2 + 2 * ((100 : ℝ) ^ 2 * (H : ℝ) ^ 3 * (Fintype.card S : ℝ) ^ 2 *
              (Fintype.card A : ℝ) * algorithmLog δ (Fintype.card S) (Fintype.card A) K H ^ 2) *
                Real.log K)) by linarith only [hPC, hAz3])
  have p1 := mul_le_mul s1 s2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have p2 := mul_le_mul s3 s2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hα0 : 0 ≤ Real.sqrt (2 * ℓ) +
      Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H) := by positivity
  have hβ0 : 0 ≤ gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
      (1 / (10 * H)) 10 + Real.sqrt (8 * Fintype.card S * (H : ℝ) ^ 2 * ℓ / (1 / (10 * H))) := by
    have : 0 ≤ gBeta H (Fintype.card S) ℓ
        (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) (1 / (10 * H)) 10 := by
      unfold gBeta
      have : 0 ≤ (Fintype.card S : ℝ) * ℓ / (1 / (10 * H)) := by positivity
      positivity
    positivity
  have q1 := mul_le_mul_of_nonneg_left p1 hα0
  have q2 := mul_le_mul_of_nonneg_left hpsi hβ0
  have q3 := mul_le_mul_of_nonneg_left p2 (by norm_num : (0 : ℝ) ≤ 4)
  have q4 := mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
  have hXb : ∑ k : Fin K, ∑ h : Fin H, XtR M δ sel init ℓ (1 / (10 * H)) 10 ω k h ≤
      H * (2 * H * (Fintype.card S * Fintype.card A)) +
        (Real.sqrt (2 * ℓ) + Real.sqrt (8 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H)) *
          (Real.sqrt (2 * K * (H : ℝ) ^ 2 + (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2)) *
            Real.sqrt (2 * (Fintype.card S * Fintype.card A) * Real.log K)) +
        (gBeta H (Fintype.card S) ℓ (algorithmLog δ (Fintype.card S) (Fintype.card A) K H)
            (1 / (10 * H)) 10 +
          Real.sqrt (8 * Fintype.card S * (H : ℝ) ^ 2 * ℓ / (1 / (10 * H)))) *
          (2 * (Fintype.card S * Fintype.card A) * Real.log K) +
        4 * (Real.sqrt ((H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2) + H * (Fintype.card S *
            (2 * (H : ℝ) ^ 2 + 2 * ((100 : ℝ) ^ 2 * (H : ℝ) ^ 3 * (Fintype.card S : ℝ) ^ 2 *
              (Fintype.card A : ℝ) * algorithmLog δ (Fintype.card S) (Fintype.card A) K H ^ 2) *
                Real.log K))) *
          Real.sqrt (2 * (Fintype.card S * Fintype.card A) * Real.log K)) := by
    linarith only [hX, q1, q2, q3, q4]
  have := mul_le_mul_of_nonneg_left hXb hG0
  linarith only [this, hr]

lemma probEvent_union5 (M : Hoeffding.MDP S A) (δ : ℝ) (sel : (A → ℝ) → A)
    (init : InitialRule S H) (E0 E1 E2 E3 E4 : Hoeffding.Outcomes S K H → Prop) :
    probEvent M δ K H sel init (fun ω => E0 ω ∨ E1 ω ∨ E2 ω ∨ E3 ω ∨ E4 ω) ≤
      probEvent M δ K H sel init E0 + probEvent M δ K H sel init E1 +
        probEvent M δ K H sel init E2 + probEvent M δ K H sel init E3 +
          probEvent M δ K H sel init E4 := by
  have u1 := probEvent_union M δ sel init E0 (fun ω => E1 ω ∨ E2 ω ∨ E3 ω ∨ E4 ω)
  have u2 := probEvent_union M δ sel init E1 (fun ω => E2 ω ∨ E3 ω ∨ E4 ω)
  have u3 := probEvent_union M δ sel init E2 (fun ω => E3 ω ∨ E4 ω)
  have u4 := probEvent_union M δ sel init E3 E4
  linarith

end Final

set_option maxHeartbeats 1000000 in
theorem main_bound {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (M : Hoeffding.MDP S A) (H K : ℕ) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (sel : (A → ℝ) → A)
    (hsel : ∀ f : A → ℝ, ∀ a, f a ≤ f (sel f))
    (init : InitialRule S H) :
    probEvent M δ K H sel init (fun ω =>
      30 * H * Real.log (5 * (H : ℝ) * Fintype.card S * Fintype.card A * (K * H) / δ) *
          Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) +
        2500 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A *
          Real.log (5 * (H : ℝ) * Fintype.card S * Fintype.card A * (K * H) / δ) ^ 2 +
        4 * H * Real.sqrt H * Real.sqrt (K *
          Real.log (5 * (H : ℝ) * Fintype.card S * Fintype.card A * (K * H) / δ)) <
          regret M δ K H sel init ω) ≤ δ := by
  by_cases hδ1 : 1 ≤ δ
  · exact le_trans (probEvent_le_one M δ sel init _) hδ1
  have hδ1' : δ ≤ 1 := le_of_lt (not_le.mp hδ1)
  rcases Nat.eq_zero_or_pos K with hK0 | hK
  · subst hK0
    rw [probEvent_false]
    · exact hδ.le
    intro ω hω
    have hr : regret M δ 0 H sel init ω = 0 := by unfold regret; simp
    rw [hr] at hω
    simp at hω
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA1 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hHr : (0 : ℝ) < H := by linarith only [hH1]
  have hKr : (0 : ℝ) < K := by linarith only [hK1]
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (5 * (H : ℝ) * Fintype.card S * Fintype.card A *
      (K * H) / δ) := ⟨_, rfl⟩
  rw [← hLdef]
  have hsa : 1 ≤ (Fintype.card S : ℝ) * (Fintype.card A : ℝ) := one_le_mul_of_one_le_of_one_le hS1 hA1
  have hKH1 : 1 ≤ (K : ℝ) * H := one_le_mul_of_one_le_of_one_le hK1 hH1
  -- L ≥ 1
  have hX5 : 5 ≤ 5 * (H : ℝ) * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H) / δ := by
    rw [le_div_iff₀ hδ]
    have : 1 ≤ (H : ℝ) * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H) := by
      have := one_le_mul_of_one_le_of_one_le hH1 hS1
      have := one_le_mul_of_one_le_of_one_le this hA1
      exact one_le_mul_of_one_le_of_one_le this hKH1
    linarith only [this, hδ1', hδ]
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have hl5 : 1 ≤ Real.log 5 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith only [this]
    have := Real.log_le_log (by norm_num) hX5
    linarith only [this, hl5]
  have hL0 : 0 ≤ L := by linarith only [hL1]
  -- small regime: the event is empty
  by_cases hreg : (K : ℝ) * H ≤ 2500 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2
  · rw [probEvent_false]
    · exact hδ.le
    intro ω hω
    have h1 := regret_le M δ sel init ω
    have h2 : 0 ≤ 30 * (H : ℝ) * L * Real.sqrt ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * K) :=
      mul_nonneg (mul_nonneg (by positivity) hL0) (Real.sqrt_nonneg _)
    have h4 : 0 ≤ 2500 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 := by positivity
    have h3 : 0 ≤ 4 * (H : ℝ) * Real.sqrt H * Real.sqrt (K * L) := by positivity
    linarith only [h1, hω, h2, h3, h4, hreg]
  have hbig : 2500 * (H : ℝ) * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 < K := by
    have h1 : 2500 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 < K * H := not_le.mp hreg
    have h2 : 2500 * (H : ℝ) * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 * H < K * H := by
      have e : 2500 * (H : ℝ) * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 * H = 2500 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 := by
        ring
      linarith only [h1, e]
    exact lt_of_mul_lt_mul_right h2 hHr.le
  have hs2a : 1 ≤ (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hS1) hA1
  have hLL : L ≤ L ^ 2 := by linarith only [mul_le_mul_of_nonneg_left hL1 hL0]
  have hHLK : (H : ℝ) * L ≤ K := by
    have : (H : ℝ) * L ≤ 2500 * (H : ℝ) * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 := by
      have e1 : (H : ℝ) * L ≤ H * L ^ 2 := mul_le_mul_of_nonneg_left hLL hHr.le
      have e2 : (H : ℝ) * L ^ 2 ≤ H * L ^ 2 * (2500 * ((Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ))) :=
        le_mul_of_one_le_right (by positivity) (by linarith only [hs2a])
      linarith only [e1, e2]
    linarith only [this, hbig]
  have hsHK : (Fintype.card S : ℝ) * H ≤ K := by
    have : (Fintype.card S : ℝ) * H ≤ 2500 * (H : ℝ) * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 := by
      have e1 : (Fintype.card S : ℝ) ≤ (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 := by
        have : 1 ≤ (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * L ^ 2 := one_le_mul_of_one_le_of_one_le hsa (one_le_pow₀ hL1)
        linarith only [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (Fintype.card S : ℝ))]
      have hp : 0 ≤ (H : ℝ) * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 := by positivity
      linarith only [mul_le_mul_of_nonneg_left e1 hHr.le, hp]
    linarith only [this, hbig]
  -- the logs
  have hLaeq : algorithmLog δ (Fintype.card S) (Fintype.card A) K H =
      Real.log (5 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H) / δ) := rfl
  have hY5 : 5 ≤ 5 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H) / δ := by
    rw [le_div_iff₀ hδ]
    have := one_le_mul_of_one_le_of_one_le hsa hKH1
    linarith only [this, hδ1', hδ]
  have hLa0 : 0 ≤ algorithmLog δ (Fintype.card S) (Fintype.card A) K H := by
    rw [hLaeq]; exact Real.log_nonneg (by linarith only [hY5])
  have hLaL : algorithmLog δ (Fintype.card S) (Fintype.card A) K H ≤ L := by
    rw [hLaeq, hLdef]
    apply Real.log_le_log (by linarith only [hY5])
    apply div_le_div_of_nonneg_right _ hδ.le
    have : 0 ≤ 5 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H) := by positivity
    linarith only [mul_le_mul_of_nonneg_left hH1 this]
  have hlK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlK : Real.log K ≤ L := by
    rw [hLdef]
    apply Real.log_le_log hKr
    rw [le_div_iff₀ hδ]
    have : 1 ≤ 5 * (H : ℝ) * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * H := by
      have := one_le_mul_of_one_le_of_one_le hH1 hsa
      have := one_le_mul_of_one_le_of_one_le this hH1
      linarith only [this]
    linarith only [mul_le_mul_of_nonneg_left hδ1' hKr.le, mul_le_mul_of_nonneg_left this hKr.le]
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Real.log (9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) / δ) := ⟨_, rfl⟩
  have hX0 : 0 < 9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) := by positivity
  have hX1 : 1 ≤ (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) := by
    have := one_le_mul_of_one_le_of_one_le hs2a hH1
    exact one_le_mul_of_one_le_of_one_le this hKH1
  have hℓ : 0 < ℓ := by
    rw [hℓdef]
    apply Real.log_pos
    rw [one_lt_div hδ]
    linarith only [hX1, hδ1']
  have hℓL : ℓ ≤ 2 * L := by
    have e := Real.log_pow (5 * (H : ℝ) * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H) / δ) 2
    push_cast at e
    rw [hℓdef, hLdef, ← e]
    apply Real.log_le_log (by positivity)
    rw [div_pow]
    have hY : 9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) ≤ (5 * (H : ℝ) * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H)) ^ 2 := by
      have e : (5 * (H : ℝ) * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H)) ^ 2 =
          25 * ((Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H)) * ((Fintype.card A : ℝ) * H * (K * H)) := by ring
      rw [e]
      have : 1 ≤ (Fintype.card A : ℝ) * H * (K * H) := by
        have := one_le_mul_of_one_le_of_one_le hA1 hH1
        exact one_le_mul_of_one_le_of_one_le this hKH1
      have hX0' : 0 ≤ (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) := by positivity
      linarith only [mul_le_mul_of_nonneg_left this hX0', hX0']
    have hδ2 : δ ^ 2 ≤ δ := by linarith only [mul_le_mul_of_nonneg_left hδ1' hδ.le]
    calc 9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) / δ ≤ (5 * (H : ℝ) * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H)) ^ 2 / δ :=
          div_le_div_of_nonneg_right hY hδ.le
      _ ≤ (5 * (H : ℝ) * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H)) ^ 2 / δ ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hδ2
  have hℓLa : ℓ ≤ 3 / 2 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H := by
    have h2 : 2 * ℓ ≤ 3 * algorithmLog δ (Fintype.card S) (Fintype.card A) K H := by
      have e2 := Real.log_pow (9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) / δ) 2
      have e3 := Real.log_pow (5 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H) / δ) 3
      push_cast at e2 e3
      rw [hℓdef, hLaeq, ← e2, ← e3]
      apply Real.log_le_log (by positivity)
      rw [div_pow, div_pow]
      have hY : (9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H)) ^ 2 ≤ (5 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H)) ^ 3 := by
        have e1 : (9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H)) ^ 2 =
            ((Fintype.card S : ℝ) ^ 3 * (Fintype.card A : ℝ) ^ 2 * (K * H) ^ 2 * H) * (81 * ((Fintype.card S : ℝ) * H)) := by ring
        have e2 : (5 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H)) ^ 3 =
            ((Fintype.card S : ℝ) ^ 3 * (Fintype.card A : ℝ) ^ 2 * (K * H) ^ 2 * H) * (125 * ((Fintype.card A : ℝ) * K)) := by ring
        rw [e1, e2]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hSAK : (Fintype.card S : ℝ) * H ≤ (Fintype.card A : ℝ) * K := by linarith only [mul_le_mul_of_nonneg_right hA1 hKr.le, hsHK]
        have hAK0 : 0 ≤ (Fintype.card A : ℝ) * K := by positivity
        linarith only [hSAK, hAK0]
      have hδ3 : δ ^ 3 ≤ δ ^ 2 := by linarith only [mul_le_mul_of_nonneg_left hδ1' (sq_nonneg δ)]
      calc (9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H)) ^ 2 / δ ^ 2 ≤ (5 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H)) ^ 3 / δ ^ 2 :=
            div_le_div_of_nonneg_right hY (by positivity)
        _ ≤ (5 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (K * H)) ^ 3 / δ ^ 3 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hδ3
    linarith only [h2]
  have hregℓ : (H : ℝ) * ℓ ≤ 2 * K := by linarith only [mul_le_mul_of_nonneg_left hℓL hHr.le, hHLK]
  -- the good events
  have hKHn : 0 < K * H := Nat.mul_pos hK hH
  have hG1 := gamma_ge H hH
  have hG54 := gamma_le H hH
  have hsub : ∀ ω, 30 * H * L * Real.sqrt ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * K) + 2500 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * L ^ 2 +
      4 * H * Real.sqrt H * Real.sqrt (K * L) < regret M δ K H sel init ω →
      ¬ GoodOpt M δ sel init ℓ ω ∨ ¬ GoodReg M δ sel init ℓ (1 / (10 * H)) ω ∨
      (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ))) ^ H * H * Real.sqrt (K * H * ℓ / 2) <
        ∑ p : Fin K × Fin H, mInc M δ sel init (Fgc M δ sel init (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ)))) p.1 p.2 ω ∨
      (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2) <
        ∑ p : Fin K × Fin H, mInc M δ sel init (FV M δ sel init) p.1 p.2 ω ∨
      (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2) <
        ∑ p : Fin K × Fin H, mInc M δ sel init (FC M δ sel init) p.1 p.2 ω := by
    intro ω hω
    by_contra hcon
    simp only [not_or, not_not, not_lt] at hcon
    obtain ⟨hG, hR, hZ1, hZ2, hZ3⟩ := hcon
    have hraw := regret_raw M δ sel hsel init ℓ hH hK hℓ hℓLa ω hG hR hZ1 hZ2 hZ3
    have hnum := final_numeric (H : ℝ) (Fintype.card S : ℝ) (Fintype.card A : ℝ) K L (algorithmLog δ (Fintype.card S) (Fintype.card A) K H) ℓ (Real.log K) ((1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ))) ^ H) hH1 hS1 hA1 hK1 hL1
      hLa0 hLaL hℓ.le hℓL hlK0 hlK (pow_nonneg (by linarith only [hG1]) _) hG54 hregℓ
    linarith only [hω, hraw, hnum]
  -- probability of the bad events
  have hP0 := probOpt (K := K) M δ sel init ℓ hℓ hH
  have hP1 := probReg (K := K) M δ sel init ℓ (1 / (10 * H)) hℓ (by positivity) hH
  have hP2 := azuma M δ sel init (Fgc M δ sel init (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ)))) (Fgc_adapted M δ sel init (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ))))
    (fun _ _ _ => 0) ((1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ))) ^ H * H) (by positivity)
    (fun k h ω y => Fgc_mem M δ sel init (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ))) hG1 k h ω y) ℓ hℓ hKHn
  have hP3 := azuma M δ sel init (FV M δ sel init) (FV_adapted M δ sel init)
    (fun _ _ _ => 0) ((H : ℝ) ^ 2) (by positivity)
    (fun k h ω y => FV_mem M δ sel init k h ω y) ℓ hℓ hKHn
  have hP4 := azuma M δ sel init (FC M δ sel init) (FC_adapted M δ sel init)
    (fun _ _ _ => 0) ((H : ℝ) ^ 2) (by positivity)
    (fun k h ω y => FC_mem M δ sel init k h ω y) ℓ hℓ hKHn
  have hU := probEvent_union5 M δ sel init (fun ω => ¬ GoodOpt M δ sel init ℓ ω)
    (fun ω => ¬ GoodReg M δ sel init ℓ (1 / (10 * H)) ω)
    (fun ω => (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ))) ^ H * H * Real.sqrt (K * H * ℓ / 2) <
        ∑ p : Fin K × Fin H, mInc M δ sel init (Fgc M δ sel init (1 + etaB (1 / (10 * (H : ℝ))) + 1 / (10 * (H : ℝ)))) p.1 p.2 ω)
    (fun ω => (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2) <
        ∑ p : Fin K × Fin H, mInc M δ sel init (FV M δ sel init) p.1 p.2 ω)
    (fun ω => (H : ℝ) ^ 2 * Real.sqrt (K * H * ℓ / 2) <
        ∑ p : Fin K × Fin H, mInc M δ sel init (FC M δ sel init) p.1 p.2 ω)
  have hM := probEvent_mono M δ sel init _ _ hsub
  have hexp : Real.exp (-ℓ) = δ / (9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H)) := by
    rw [Real.exp_neg, hℓdef, Real.exp_log (by positivity), inv_div]
  have hcnt : ((Fintype.card S * Fintype.card A * H * (K * H) : ℕ) : ℝ) * 3 +
      ((Fintype.card S * Fintype.card A * H * (K * H) : ℕ) : ℝ) * 2 +
      ((Fintype.card S * Fintype.card A * Fintype.card S * (K * H) : ℕ) : ℝ) + 3 ≤
      9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) := by
    push_cast
    have e1 : (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * H * (K * H) ≤ (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) := by
      have : (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * H * (K * H) * 1 ≤ (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * H * (K * H) * (Fintype.card S : ℝ) :=
        mul_le_mul_of_nonneg_left hS1 (by positivity)
      linarith only [this]
    have e2 : (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (Fintype.card S : ℝ) * (K * H) ≤ (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H) := by
      have : (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * (K * H) * 1 ≤ (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * (K * H) * H :=
        mul_le_mul_of_nonneg_left hH1 (by positivity)
      linarith only [this]
    linarith only [e1, e2, hX1]
  have hE0 : 0 ≤ Real.exp (-ℓ) := (Real.exp_pos _).le
  have hfin : Real.exp (-ℓ) * (9 * (Fintype.card S : ℝ) ^ 2 * (Fintype.card A : ℝ) * H * (K * H)) = δ := by
    rw [hexp]; field_simp
  have := mul_le_mul_of_nonneg_left hcnt hE0
  linarith only [this, hfin, hU, hM, hP0, hP1, hP2, hP3, hP4]

end MinimaxRegretRL.Bernstein.UCBBF

open MinimaxRegretRL.Bernstein in
theorem solution {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (M : MinimaxRegretRL.Hoeffding.MDP S A) (H K : ℕ) (hH : 0 < H)
    (δ : ℝ) (hδ : 0 < δ) (sel : (A → ℝ) → A)
    (hsel : ∀ f : A → ℝ, ∀ a, f a ≤ f (sel f))
    (init : InitialRule S H) :
    let L := Real.log (5 * (H : ℝ) * Fintype.card S * Fintype.card A * (K * H) / δ)
    probEvent M δ K H sel init (fun ω =>
      30 * H * L * Real.sqrt ((Fintype.card S : ℝ) * Fintype.card A * K) +
        2500 * (H : ℝ) ^ 2 * (Fintype.card S : ℝ) ^ 2 * Fintype.card A * L ^ 2 +
        4 * H * Real.sqrt H * Real.sqrt (K * L) <
          regret M δ K H sel init ω) ≤ δ := by
  intro L
  exact MinimaxRegretRL.Bernstein.UCBBF.main_bound M H K hH δ hδ sel hsel init
