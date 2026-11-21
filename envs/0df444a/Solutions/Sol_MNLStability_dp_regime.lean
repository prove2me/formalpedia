-- Prove2me | solution 1 for MNLStability.dp_regime
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:22:53.423883+00:00
-- url     : https://prove2.me/submissions/ad5f5dd4-1e59-4357-b7cb-5e6ea6b8fd1b

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_Gval
import Definitions.Def_MNLStability_dpSolve

open scoped ENNReal

namespace Aux_MNLS0
open MNLStability

variable {n : ℕ}

abbrev St (n : ℕ) := (Fin n → ℕ) × ℕ

noncomputable def EEx {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' x, μ x * f x

lemma EEx_pure {α : Type*} (a : α) (f : α → ℝ≥0∞) : EEx (PMF.pure a) f = f a := by
  unfold EEx
  rw [tsum_eq_single a]
  · simp [PMF.pure_apply]
  · intro b hb
    simp [PMF.pure_apply, hb]

lemma EEx_bind {α β : Type*} (μ : PMF α) (K : α → PMF β) (f : β → ℝ≥0∞) :
    EEx (μ.bind K) f = ∑' a, μ a * EEx (K a) f := by
  unfold EEx
  simp only [PMF.bind_apply]
  calc ∑' x, (∑' a, μ a * K a x) * f x = ∑' x, ∑' a, μ a * K a x * f x := by
        refine tsum_congr (fun x => ?_)
        rw [ENNReal.tsum_mul_right]
    _ = ∑' a, ∑' x, μ a * K a x * f x := ENNReal.tsum_comm
    _ = ∑' a, μ a * ∑' x, K a x * f x := by
        refine tsum_congr (fun a => ?_)
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        ring

lemma EEx_map {α β : Type*} (μ : PMF α) (h : α → β) (f : β → ℝ≥0∞) :
    EEx (μ.map h) f = ∑' a, μ a * f (h a) := by
  rw [← PMF.bind_pure_comp, EEx_bind]
  refine tsum_congr (fun a => ?_)
  rw [Function.comp_apply, EEx_pure]

lemma EEx_le {α : Type*} (μ : PMF α) (f : α → ℝ≥0∞) (B : ℝ≥0∞) (h : ∀ x, f x ≤ B) :
    EEx μ f ≤ B := by
  unfold EEx
  calc ∑' x, μ x * f x ≤ ∑' x, μ x * B :=
        ENNReal.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_left (h x) (zero_le))
    _ = B := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma EEx_mono {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) (h : ∀ x, f x ≤ g x) :
    EEx μ f ≤ EEx μ g :=
  ENNReal.tsum_le_tsum (fun x => mul_le_mul_of_nonneg_left (h x) (zero_le))

lemma EEx_congr {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) (h : ∀ x, μ x ≠ 0 → f x = g x) :
    EEx μ f = EEx μ g := by
  unfold EEx
  refine tsum_congr (fun x => ?_)
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [h x hx]

lemma EEx_const_mul {α : Type*} (μ : PMF α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    EEx μ (fun x => c * f x) = c * EEx μ f := by
  unfold EEx
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun x => ?_)
  ring

lemma EEx_add {α : Type*} (μ : PMF α) (f g : α → ℝ≥0∞) :
    EEx μ (fun x => f x + g x) = EEx μ f + EEx μ g := by
  unfold EEx
  rw [← ENNReal.tsum_add]
  refine tsum_congr (fun x => ?_)
  ring

def shf : Option (Fin n) → St n → St n
  | none, x => (x.1, x.2 + 1)
  | some i, x => (x.1 + Pi.single i 1, x.2)

def sb1 (V : Fin n → ℕ) : Option (Fin n) → (Fin n → ℕ)
  | none => V
  | some i => V - Pi.single i 1

lemma demand_zero (wt : Weights n) (U : Fin n → ℕ) : demand wt U 0 = PMF.pure (0, 0) := by
  simp only [demand]

lemma demand_succ (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) :
    demand wt U (m + 1) =
      (demand wt U m).bind (fun x => (step wt (U - x.1)).map (fun c => shf c x)) := by
  first
  | rfl
  | (simp only [demand]
     congr 1
     funext x
     congr 1
     funext c
     cases c <;> rfl)

lemma step_sum_one (wt : Weights n) (V : Fin n → ℕ) : ∑ c, step wt V c = 1 := by
  have := PMF.tsum_coe (step wt V)
  rwa [tsum_fintype] at this

lemma EEx_succ_fwd (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) (f : St n → ℝ≥0∞) :
    EEx (demand wt U (m + 1)) f =
      EEx (demand wt U m) (fun x => ∑ c, step wt (U - x.1) c * f (shf c x)) := by
  rw [demand_succ, EEx_bind]
  simp only [EEx_map, tsum_fintype] <;> rfl

lemma shf_comm (c d : Option (Fin n)) (x : St n) : shf d (shf c x) = shf c (shf d x) := by
  rcases c with _ | i <;> rcases d with _ | j
  · rfl
  · rfl
  · rfl
  · refine Prod.ext ?_ rfl
    show x.1 + Pi.single i 1 + Pi.single j 1 = x.1 + Pi.single j 1 + Pi.single i 1
    abel

lemma sub_shf (V : Fin n → ℕ) (c : Option (Fin n)) (x : St n) :
    V - (shf c x).1 = sb1 V c - x.1 := by
  rcases c with _ | i
  · rfl
  · show V - (x.1 + Pi.single i 1) = V - Pi.single i 1 - x.1
    rw [tsub_tsub, add_comm]

lemma EEx_succ_bwd (wt : Weights n) (m : ℕ) : ∀ (V : Fin n → ℕ) (f : St n → ℝ≥0∞),
    EEx (demand wt V (m + 1)) f =
      ∑ c, step wt V c * EEx (demand wt (sb1 V c) m) (f ∘ shf c) := by
  induction m with
  | zero =>
    intro V f
    rw [EEx_succ_fwd, demand_zero, EEx_pure]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [demand_zero, EEx_pure, Function.comp_apply]
    simp only [tsub_zero]
  | succ m ih =>
    intro V f
    rw [EEx_succ_fwd, ih]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [EEx_succ_fwd]
    congr 2
    funext x
    simp only [Function.comp_apply]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [shf_comm c d x, sub_shf V c x]

noncomputable def qq (wt : Weights n) (V : Fin n → ℕ) : Option (Fin n) → ℝ
  | none => wt.w0
  | some i => if 0 < V i then wt.w i else 0

lemma qq_nonneg (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (c : Option (Fin n)) :
    0 ≤ qq wt V c := by
  rcases c with _ | i
  · exact hw.1.le
  · simp only [qq]
    split_ifs <;> linarith [hw.2 i]

lemma ZZ_eq (wt : Weights n) (V : Fin n → ℕ) :
    ∑ c, qq wt V c = wt.w0 + wt.wsum (inStock V) := by
  rw [Fintype.sum_option]
  simp only [qq, Weights.wsum, inStock, Finset.sum_filter]

lemma Z_pos (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) : 0 < ∑ d, qq wt V d := by
  rw [ZZ_eq]
  have : 0 ≤ wt.wsum (inStock V) := Finset.sum_nonneg (fun i _ => (hw.2 i).le)
  linarith [hw.1]

lemma stepMass_eq (wt : Weights n) (V : Fin n → ℕ) (c : Option (Fin n)) :
    stepMass wt V c = ENNReal.ofReal (qq wt V c / ∑ d, qq wt V d) := by
  rw [ZZ_eq]
  rcases c with _ | i
  · rfl
  · simp only [stepMass, qq]
    split_ifs <;> simp

lemma step_eq (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (c : Option (Fin n)) :
    step wt V c = ENNReal.ofReal (qq wt V c / ∑ d, qq wt V d) := by
  have hZ : 0 < ∑ d, qq wt V d := Z_pos wt hw V
  have hsum : ∑ a, stepMass wt V a = 1 := by
    simp only [stepMass_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun d _ => div_nonneg (qq_nonneg wt hw V d) hZ.le),
      ← Finset.sum_div, div_self hZ.ne', ENNReal.ofReal_one]
  unfold step
  rw [dif_pos hsum, PMF.ofFintype_apply, stepMass_eq]

lemma avail_of_ne (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (i : Fin n)
    (h : step wt V (some i) ≠ 0) : 0 < V i := by
  by_contra hc
  apply h
  rw [step_eq wt hw]
  simp only [qq, if_neg hc, zero_div, ENNReal.ofReal_zero]

lemma sum_le_avail (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ)
    (A B : Option (Fin n) → ℝ≥0∞) (h : ∀ c, (∀ i, c = some i → 0 < V i) → A c ≤ B c) :
    ∑ c, step wt V c * A c ≤ ∑ c, step wt V c * B c := by
  refine Finset.sum_le_sum (fun c _ => ?_)
  by_cases hc : step wt V c = 0
  · rw [hc, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left (h c ?_) (zero_le)
    rintro i rfl
    exact avail_of_ne wt hw V i hc


lemma demand_supp (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (m : ℕ) :
    ∀ x, demand wt V m x ≠ 0 → x.1 ≤ V := by
  induction m with
  | zero =>
    intro x hx
    rw [demand_zero, PMF.pure_apply] at hx
    split_ifs at hx with h
    · subst h
      exact Pi.le_def.2 (fun j => Nat.zero_le _)
    · exact absurd rfl hx
  | succ m ih =>
    intro x hx
    have hx' : x ∈ (demand wt V (m + 1)).support := (PMF.mem_support_iff _ _).2 hx
    rw [demand_succ, PMF.mem_support_bind_iff] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    rw [PMF.mem_support_map_iff] at hxy
    obtain ⟨c, hc, rfl⟩ := hxy
    have hyV := ih y ((PMF.mem_support_iff _ _).1 hy)
    rcases c with _ | i
    · exact hyV
    · have hi := avail_of_ne wt hw _ i ((PMF.mem_support_iff _ _).1 hc)
      rw [Pi.sub_apply] at hi
      rw [Pi.le_def]
      intro j
      show y.1 j + (Pi.single i 1 : Fin n → ℕ) j ≤ V j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        omega
      · rw [Pi.single_eq_of_ne hj, add_zero]
        exact hyV j


def Xf (i : Fin n) : St n → ℝ≥0∞ := fun x => ((x.1 i : ℕ) : ℝ≥0∞)

lemma expXm_eq (wt : Weights n) (U : Fin n → ℕ) (m : ℕ) (i : Fin n) :
    expXm wt U m i = (EEx (demand wt U m) (Xf i)).toReal := rfl

lemma EX_min (wt : Weights n) (hw : wt.Pos) (U : Fin n → ℕ) (m : ℕ) (i : Fin n) :
    EEx (demand wt U m) (Xf i) =
      EEx (demand wt U m) (fun x => ((min (x.1 i) (U i) : ℕ) : ℝ≥0∞)) := by
  refine EEx_congr _ _ _ (fun x hx => ?_)
  simp only [Xf]
  rw [min_eq_left (demand_supp wt hw U m x hx i)]

lemma EX_ne_top (wt : Weights n) (hw : wt.Pos) (U : Fin n → ℕ) (m : ℕ) (i : Fin n) :
    EEx (demand wt U m) (Xf i) ≠ ⊤ := by
  rw [EX_min wt hw]
  refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top (U i)) (EEx_le _ _ _ (fun x => ?_))
  exact_mod_cast min_le_right _ _


/-! ## Binomial min-expectations -/

noncomputable def bk (p : ℝ) (m k : ℕ) : ℝ := (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)

lemma bme_eq (p : ℝ) (m u : ℕ) :
    binMinExp p m u = ∑ k ∈ Finset.range (m + 1), bk p m k * ((min u k : ℕ) : ℝ) := rfl

lemma bk_sum (p : ℝ) (m : ℕ) : ∑ k ∈ Finset.range (m + 1), bk p m k = 1 := by
  have h := add_pow p (1 - p) m
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  unfold bk
  ring

lemma bk_zero_of_lt (p : ℝ) {m k : ℕ} (h : m < k) : bk p m k = 0 := by
  unfold bk
  rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul, zero_mul]

lemma bk_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m k : ℕ) : 0 ≤ bk p m k := by
  unfold bk
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (by linarith) _)

lemma bk_succ_succ (p : ℝ) (m k : ℕ) :
    bk p (m + 1) (k + 1) = p * bk p m k + (1 - p) * bk p m (k + 1) := by
  unfold bk
  rw [Nat.choose_succ_succ', Nat.cast_add]
  rcases Nat.lt_or_ge k m with hk | hk
  · have e1 : m + 1 - (k + 1) = m - k := by omega
    have e2 : m - k = (m - (k + 1)) + 1 := by omega
    rw [e1, e2]
    ring
  · have e1 : m + 1 - (k + 1) = m - k := by omega
    rw [Nat.choose_eq_zero_of_lt (by omega : m < k + 1), e1, Nat.cast_zero]
    ring

lemma bme_zero_m (p : ℝ) (u : ℕ) : binMinExp p 0 u = 0 := by
  simp [binMinExp]

lemma bme_zero_u (p : ℝ) (m : ℕ) : binMinExp p m 0 = 0 := by
  simp [binMinExp]

lemma bme_succ (p : ℝ) (m u : ℕ) :
    binMinExp p (m + 1) (u + 1) = p * (1 + binMinExp p m u) + (1 - p) * binMinExp p m (u + 1) := by
  have hA : ∑ k ∈ Finset.range (m + 1), bk p m k * ((min (u + 1) (k + 1) : ℕ) : ℝ) =
      1 + ∑ k ∈ Finset.range (m + 1), bk p m k * ((min u k : ℕ) : ℝ) := by
    rw [← bk_sum p m, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [show min (u + 1) (k + 1) = min u k + 1 by omega]
    push_cast
    ring
  have hB : ∑ k ∈ Finset.range (m + 1), bk p m (k + 1) * ((min (u + 1) (k + 1) : ℕ) : ℝ) =
      ∑ k ∈ Finset.range (m + 1), bk p m k * ((min (u + 1) k : ℕ) : ℝ) := by
    have h1 := Finset.sum_range_succ' (fun k => bk p m k * ((min (u + 1) k : ℕ) : ℝ)) (m + 1)
    have h2 := Finset.sum_range_succ (fun k => bk p m k * ((min (u + 1) k : ℕ) : ℝ)) (m + 1)
    rw [bk_zero_of_lt p (Nat.lt_succ_self m), zero_mul, add_zero] at h2
    simp only [Nat.min_zero, Nat.cast_zero, mul_zero, add_zero] at h1
    linarith
  calc binMinExp p (m + 1) (u + 1)
      = ∑ k ∈ Finset.range (m + 1), bk p (m + 1) (k + 1) * ((min (u + 1) (k + 1) : ℕ) : ℝ) +
          bk p (m + 1) 0 * ((min (u + 1) 0 : ℕ) : ℝ) := by
        rw [bme_eq, Finset.sum_range_succ']
    _ = p * ∑ k ∈ Finset.range (m + 1), bk p m k * ((min (u + 1) (k + 1) : ℕ) : ℝ) +
          (1 - p) * ∑ k ∈ Finset.range (m + 1), bk p m (k + 1) * ((min (u + 1) (k + 1) : ℕ) : ℝ) := by
        rw [Nat.min_zero, Nat.cast_zero, mul_zero, add_zero, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [bk_succ_succ]
        ring
    _ = p * (1 + binMinExp p m u) + (1 - p) * binMinExp p m (u + 1) := by
        rw [hA, hB, bme_eq, bme_eq]

lemma bme_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m u : ℕ) : 0 ≤ binMinExp p m u := by
  rw [bme_eq]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (bk_nonneg hp0 hp1 m k) (Nat.cast_nonneg _)

lemma bme_succ_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m u : ℕ) :
    binMinExp p m (u + 1) ≤ 1 + binMinExp p m u := by
  rw [bme_eq, bme_eq, ← bk_sum p m, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have h1 : ((min (u + 1) k : ℕ) : ℝ) ≤ 1 + ((min u k : ℕ) : ℝ) := by
    have : min (u + 1) k ≤ 1 + min u k := by omega
    exact_mod_cast this
  have := mul_le_mul_of_nonneg_left h1 (bk_nonneg hp0 hp1 m k)
  linarith

lemma bme_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m u : ℕ) :
    binMinExp p m u ≤ binMinExp p m (u + 1) := by
  rw [bme_eq, bme_eq]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (bk_nonneg hp0 hp1 m k)
  have : min u k ≤ min (u + 1) k := by omega
  exact_mod_cast this

lemma bme_thin {l p : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ m u, l * binMinExp p m u ≤ binMinExp (l * p) m u := by
  have hlp0 : 0 ≤ l * p := mul_nonneg hl0 hp0
  have hlp1 : l * p ≤ 1 := by nlinarith
  intro m
  induction m with
  | zero => intro u; simp [bme_zero_m]
  | succ m ih =>
    intro u
    rcases u with _ | u
    · simp [bme_zero_u]
    · rw [bme_succ, bme_succ]
      have hA := ih u
      have hB := ih (u + 1)
      have hmono := bme_mono hp0 hp1 m u
      have h1 : 0 ≤ 1 - l * p := by linarith
      have hX := mul_le_mul_of_nonneg_left hA hlp0
      have hY := mul_le_mul_of_nonneg_left hB h1
      have hZ : 0 ≤ l * p * (1 - l) * (binMinExp p m (u + 1) - binMinExp p m u) :=
        mul_nonneg (mul_nonneg hlp0 (by linarith)) (by linarith)
      nlinarith

/-! ## Expected sales recursion -/

lemma EEx_const' {α : Type*} (μ : PMF α) (c : ℝ≥0∞) : EEx μ (fun _ => c) = c := by
  unfold EEx
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma Xf_shf (i : Fin n) (c : Option (Fin n)) :
    (Xf i ∘ shf c) = fun x => Xf i x + (if c = some i then 1 else 0) := by
  funext x
  rcases c with _ | j
  · simp [Xf, shf]
  · by_cases hj : j = i
    · subst hj
      simp [Xf, shf]
    · simp [Xf, shf, Pi.single_apply, hj, Ne.symm hj]

lemma sb1_apply (V : Fin n → ℕ) (i : Fin n) (c : Option (Fin n)) :
    (sb1 V c) i = V i - (if c = some i then 1 else 0) := by
  rcases c with _ | j
  · simp [sb1]
  · by_cases hj : j = i
    · subst hj
      simp [sb1]
    · simp [sb1, Pi.single_apply, hj, Ne.symm hj]

noncomputable def Ef (wt : Weights n) (i : Fin n) (m : ℕ) (V : Fin n → ℕ) : ℝ :=
  (EEx (demand wt V m) (Xf i)).toReal

lemma Ef_zero (wt : Weights n) (i : Fin n) (V : Fin n → ℕ) : Ef wt i 0 V = 0 := by
  unfold Ef
  rw [demand_zero, EEx_pure]
  simp [Xf]

lemma Ef_nonneg (wt : Weights n) (i : Fin n) (m : ℕ) (V : Fin n → ℕ) : 0 ≤ Ef wt i m V :=
  ENNReal.toReal_nonneg

lemma Ef_succ (wt : Weights n) (hw : wt.Pos) (i : Fin n) (m : ℕ) (V : Fin n → ℕ) :
    Ef wt i (m + 1) V = ∑ c, (step wt V c).toReal *
      (Ef wt i m (sb1 V c) + if c = some i then 1 else 0) := by
  unfold Ef
  rw [EEx_succ_bwd]
  have hfin : ∀ c, EEx (demand wt (sb1 V c) m) (Xf i ∘ shf c) ≠ ⊤ := by
    intro c
    rw [Xf_shf, EEx_add, EEx_const']
    exact ENNReal.add_ne_top.2 ⟨EX_ne_top wt hw _ _ _, by split_ifs <;> simp⟩
  rw [ENNReal.toReal_sum (fun c _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hfin c))]
  apply Finset.sum_congr rfl
  intro c _
  rw [ENNReal.toReal_mul, Xf_shf, EEx_add, EEx_const',
    ENNReal.toReal_add (EX_ne_top wt hw _ _ _) (by split_ifs <;> simp)]
  split_ifs <;> simp

lemma q_eq (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (c : Option (Fin n)) :
    (step wt V c).toReal = qq wt V c / ∑ d, qq wt V d := by
  rw [step_eq wt hw, ENNReal.toReal_ofReal (div_nonneg (qq_nonneg wt hw V c) (Z_pos wt hw V).le)]

lemma q_sum (wt : Weights n) (V : Fin n → ℕ) : ∑ c, (step wt V c).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun c _ => PMF.apply_ne_top _ _), step_sum_one]
  simp

lemma sum_split_ite (q : Option (Fin n) → ℝ) (hq : ∑ c, q c = 1) (o : Option (Fin n)) (X Y : ℝ) :
    ∑ c, q c * (if c = o then X else Y) = Y + q o * (X - Y) := by
  have e : ∀ c, q c * (if c = o then X else Y) =
      q c * Y + (if c = o then q c * (X - Y) else 0) := by
    intro c
    split_ifs <;> ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hq, one_mul]
  simp

lemma Wtot_ge (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) :
    wt.wsum (inStock V) ≤ ∑ j, wt.w j := by
  unfold Weights.wsum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => (hw.2 j).le)

lemma wsum_nonneg (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) : 0 ≤ wt.wsum (inStock V) :=
  Finset.sum_nonneg (fun j _ => (hw.2 j).le)

lemma q_some (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (i : Fin n) (hV : 0 < V i) :
    (step wt V (some i)).toReal = wt.w i / (wt.w0 + wt.wsum (inStock V)) := by
  rw [q_eq wt hw, ZZ_eq]
  simp [qq, hV]

lemma q_some_zero (wt : Weights n) (hw : wt.Pos) (V : Fin n → ℕ) (i : Fin n) (hV : V i = 0) :
    (step wt V (some i)).toReal = 0 := by
  rw [q_eq wt hw]
  simp [qq, hV]

lemma E_upper (wt : Weights n) (hw : wt.Pos) (i : Fin n) (hp1 : wt.w i / wt.w0 ≤ 1) :
    ∀ m V, Ef wt i m V ≤ binMinExp (wt.w i / wt.w0) m (V i) := by
  have hp0 : 0 ≤ wt.w i / wt.w0 := div_nonneg (hw.2 i).le hw.1.le
  intro m
  induction m with
  | zero => intro V; rw [Ef_zero, bme_zero_m]
  | succ m ih =>
    intro V
    rw [Ef_succ wt hw]
    rcases Nat.eq_zero_or_pos (V i) with h0 | hpos
    · rw [h0, bme_zero_u]
      have hterm : ∀ c, (step wt V c).toReal * (Ef wt i m (sb1 V c) + if c = some i then 1 else 0)
          ≤ 0 := by
        intro c
        by_cases hc : c = some i
        · subst hc
          rw [q_some_zero wt hw V i h0, zero_mul]
        · rw [if_neg hc, add_zero]
          have hsb : (sb1 V c) i = 0 := by rw [sb1_apply, if_neg hc, h0]
          have := ih (sb1 V c)
          rw [hsb, bme_zero_u] at this
          exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg this
      calc _ ≤ ∑ _c : Option (Fin n), (0 : ℝ) := Finset.sum_le_sum fun c _ => hterm c
        _ = 0 := by simp
    · obtain ⟨u, hu⟩ : ∃ u, V i = u + 1 := ⟨V i - 1, by omega⟩
      rw [hu]
      have hZ0 : 0 ≤ wt.wsum (inStock V) := wsum_nonneg wt hw V
      have hq : (step wt V (some i)).toReal ≤ wt.w i / wt.w0 := by
        rw [q_some wt hw V i hpos]
        rw [div_le_div_iff₀ (by linarith [hw.1]) hw.1]
        nlinarith [hw.2 i]
      calc _ ≤ ∑ c, (step wt V c).toReal * (if c = some i then
              1 + binMinExp (wt.w i / wt.w0) m u else binMinExp (wt.w i / wt.w0) m (u + 1)) := by
            apply Finset.sum_le_sum
            intro c _
            apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
            by_cases hc : c = some i
            · rw [if_pos hc, if_pos hc]
              have := ih (sb1 V c)
              rw [sb1_apply, if_pos hc, hu] at this
              simp only [Nat.add_sub_cancel] at this
              linarith
            · rw [if_neg hc, if_neg hc, add_zero]
              have := ih (sb1 V c)
              rwa [sb1_apply, if_neg hc, Nat.sub_zero, hu] at this
        _ = binMinExp (wt.w i / wt.w0) m (u + 1) + (step wt V (some i)).toReal *
              (1 + binMinExp (wt.w i / wt.w0) m u - binMinExp (wt.w i / wt.w0) m (u + 1)) :=
            sum_split_ite _ (q_sum wt V) _ _ _
        _ ≤ binMinExp (wt.w i / wt.w0) m (u + 1) + (wt.w i / wt.w0) *
              (1 + binMinExp (wt.w i / wt.w0) m u - binMinExp (wt.w i / wt.w0) m (u + 1)) := by
            have hd := bme_succ_le hp0 hp1 m u
            have : 0 ≤ 1 + binMinExp (wt.w i / wt.w0) m u - binMinExp (wt.w i / wt.w0) m (u + 1) := by
              linarith
            nlinarith
        _ = binMinExp (wt.w i / wt.w0) (m + 1) (u + 1) := by rw [bme_succ]; ring

lemma E_lower (wt : Weights n) (hw : wt.Pos) (i : Fin n) :
    ∀ m V, binMinExp (wt.w i / (wt.w0 + ∑ j, wt.w j)) m (V i) ≤ Ef wt i m V := by
  have hW : 0 ≤ ∑ j, wt.w j := Finset.sum_nonneg fun j _ => (hw.2 j).le
  have hD : 0 < wt.w0 + ∑ j, wt.w j := by linarith [hw.1]
  have hp0 : 0 ≤ wt.w i / (wt.w0 + ∑ j, wt.w j) := div_nonneg (hw.2 i).le hD.le
  have hwi : wt.w i ≤ ∑ j, wt.w j :=
    Finset.single_le_sum (f := fun j => wt.w j) (fun j _ => (hw.2 j).le) (Finset.mem_univ i)
  have hp1 : wt.w i / (wt.w0 + ∑ j, wt.w j) ≤ 1 := by
    rw [div_le_one hD]
    linarith [hw.1]
  intro m
  induction m with
  | zero => intro V; rw [Ef_zero, bme_zero_m]
  | succ m ih =>
    intro V
    rw [Ef_succ wt hw]
    rcases Nat.eq_zero_or_pos (V i) with h0 | hpos
    · rw [h0, bme_zero_u]
      apply Finset.sum_nonneg
      intro c _
      exact mul_nonneg ENNReal.toReal_nonneg
        (add_nonneg (Ef_nonneg _ _ _ _) (by split_ifs <;> norm_num))
    · obtain ⟨u, hu⟩ : ∃ u, V i = u + 1 := ⟨V i - 1, by omega⟩
      rw [hu]
      have hZ0 : 0 ≤ wt.wsum (inStock V) := wsum_nonneg wt hw V
      have hZ1 := Wtot_ge wt hw V
      have hq : wt.w i / (wt.w0 + ∑ j, wt.w j) ≤ (step wt V (some i)).toReal := by
        rw [q_some wt hw V i hpos]
        rw [div_le_div_iff₀ hD (by linarith [hw.1])]
        nlinarith [hw.2 i]
      set p' := wt.w i / (wt.w0 + ∑ j, wt.w j) with hp'
      calc binMinExp p' (m + 1) (u + 1)
          = binMinExp p' m (u + 1) + p' * (1 + binMinExp p' m u - binMinExp p' m (u + 1)) := by
            rw [bme_succ]; ring
        _ ≤ binMinExp p' m (u + 1) + (step wt V (some i)).toReal *
              (1 + binMinExp p' m u - binMinExp p' m (u + 1)) := by
            have hd := bme_succ_le hp0 hp1 m u
            have : 0 ≤ 1 + binMinExp p' m u - binMinExp p' m (u + 1) := by linarith
            nlinarith
        _ = ∑ c, (step wt V c).toReal * (if c = some i then
              1 + binMinExp p' m u else binMinExp p' m (u + 1)) :=
            (sum_split_ite _ (q_sum wt V) _ _ _).symm
        _ ≤ _ := by
            apply Finset.sum_le_sum
            intro c _
            apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
            by_cases hc : c = some i
            · rw [if_pos hc, if_pos hc]
              have := ih (sb1 V c)
              rw [sb1_apply, if_pos hc, hu] at this
              simp only [Nat.add_sub_cancel] at this
              linarith
            · rw [if_neg hc, if_neg hc, add_zero]
              have := ih (sb1 V c)
              rwa [sb1_apply, if_neg hc, Nat.sub_zero, hu] at this

lemma le_wmax (wt : Weights n) (j : Fin n) : wt.w j ≤ wt.wmax := by
  unfold Weights.wmax
  have key : ∀ l : List ℝ, ∀ x ∈ l, x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; simp at hx
    | cons a l ih =>
      intro x hx
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hx with h | h
      · rw [h]; exact le_max_left _ _
      · exact (ih x h).trans (le_max_right _ _)
  exact key _ _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)

/-- The sandwich bound for one product and one number of customers. -/
lemma sand_im (wt : Weights n) (hw : wt.Pos) (hn : 1 ≤ n) (e : ℝ) (he0 : 0 < e) (he1 : e < 1)
    (hmax : wt.wmax ≤ e * wt.w0 / n) (i : Fin n) (m : ℕ) (U : Fin n → ℕ) :
    (1 - e) * binMinExp (wt.w i / wt.w0) m (U i) ≤ expXm wt U m i ∧
      expXm wt U m i ≤ binMinExp (wt.w i / wt.w0) m (U i) := by
  have hw0 := hw.1
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hW : ∑ j, wt.w j ≤ e * wt.w0 := by
    calc ∑ j, wt.w j ≤ ∑ _j : Fin n, wt.wmax := Finset.sum_le_sum fun j _ => le_wmax wt j
      _ = n * wt.wmax := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ n * (e * wt.w0 / n) := mul_le_mul_of_nonneg_left hmax (by linarith)
      _ = e * wt.w0 := by field_simp
  have hW0 : 0 ≤ ∑ j, wt.w j := Finset.sum_nonneg fun j _ => (hw.2 j).le
  have hp0 : 0 ≤ wt.w i / wt.w0 := div_nonneg (hw.2 i).le hw0.le
  have hwi : wt.w i ≤ ∑ j, wt.w j :=
    Finset.single_le_sum (f := fun j => wt.w j) (fun j _ => (hw.2 j).le) (Finset.mem_univ i)
  have hp1 : wt.w i / wt.w0 ≤ 1 := by
    rw [div_le_one hw0]
    nlinarith
  have hup := E_upper wt hw i hp1 m U
  have hlo := E_lower wt hw i m U
  set l := wt.w0 / (wt.w0 + ∑ j, wt.w j) with hl
  have hD : 0 < wt.w0 + ∑ j, wt.w j := by linarith
  have hl0 : 0 ≤ l := div_nonneg hw0.le hD.le
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hD]; linarith
  have hlp : l * (wt.w i / wt.w0) = wt.w i / (wt.w0 + ∑ j, wt.w j) := by
    rw [hl]
    field_simp
  have hthin := bme_thin hl0 hl1 hp0 hp1 m (U i)
  rw [hlp] at hthin
  have hle : 1 - e ≤ l := by
    rw [hl, le_div_iff₀ hD]
    nlinarith
  have hB0 := bme_nonneg hp0 hp1 m (U i)
  constructor
  · rw [expXm_eq]
    have : (1 - e) * binMinExp (wt.w i / wt.w0) m (U i) ≤ l * binMinExp (wt.w i / wt.w0) m (U i) :=
      mul_le_mul_of_nonneg_right hle hB0
    exact this.trans (hthin.trans hlo)
  · rw [expXm_eq]
    exact hup

theorem sandwich (wts : Weights n) (hw : wts.Pos) (hn : 1 ≤ n) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (e : ℝ) (he0 : 0 < e) (he1 : e < 1)
    (hmax : wts.wmax ≤ e * wts.w0 / n) (U : Fin n → ℕ) :
    (1 - e) * Gval wts r pM U ≤ expR wts r pM U ∧ expR wts r pM U ≤ Gval wts r pM U := by
  unfold Gval expR expX
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_assoc, mul_comm (1 - e) (r i), mul_assoc, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hr i)
    apply Finset.sum_le_sum
    intro m _
    rw [← mul_assoc, mul_comm (1 - e) (pM m), mul_assoc]
    exact mul_le_mul_of_nonneg_left (sand_im wts hw hn e he0 he1 hmax i m U).1 (hM.1 m)
  · apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hr i)
    apply Finset.sum_le_sum
    intro m _
    exact mul_le_mul_of_nonneg_left (sand_im wts hw hn e he0 he1 hmax i m U).2 (hM.1 m)

/-! ## Deterministic program semantics -/

def Det {α : Type} (p : Prog α) (a : α) (k : ℕ) : Prop := ∀ s, p.run s = PMF.pure (a, s + k)

def DetLe {α : Type} (p : Prog α) (a : α) (K : ℕ) : Prop := ∃ k ≤ K, Det p a k

lemma DetLe_pure {α : Type} (a : α) : DetLe (pure a : Prog α) a 0 := ⟨0, le_rfl, fun _ => rfl⟩

lemma DetLe_charge (k : ℕ) : DetLe (charge k) () k := ⟨k, le_rfl, fun _ => rfl⟩

lemma Det_bind {α β : Type} {p : Prog α} {f : α → Prog β} {a : α} {b : β} {k k' : ℕ}
    (hp : Det p a k) (hf : Det (f a) b k') : Det (p >>= f) b (k + k') := by
  intro s
  rw [StateT.run_bind, hp s]
  show PMF.bind (PMF.pure (a, s + k)) (fun q => (f q.1).run q.2) = _
  rw [PMF.pure_bind]
  show (f a).run (s + k) = _
  rw [hf, Nat.add_assoc]

lemma DetLe_bind {α β : Type} {p : Prog α} {f : α → Prog β} {a : α} {b : β} {K K' : ℕ}
    (hp : DetLe p a K) (hf : DetLe (f a) b K') : DetLe (p >>= f) b (K + K') := by
  obtain ⟨k, hk, hp⟩ := hp
  obtain ⟨k', hk', hf⟩ := hf
  exact ⟨k + k', Nat.add_le_add hk hk', Det_bind hp hf⟩

lemma DetLe_mono {α : Type} {p : Prog α} {a : α} {K K' : ℕ} (h : DetLe p a K) (hK : K ≤ K') :
    DetLe p a K' := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk.trans hK, h⟩

lemma DetLe_opn {α : Type} (k : ℕ) (a : α) : DetLe (opn k a) a k := by
  unfold opn
  exact DetLe_mono (DetLe_bind (DetLe_charge k) (DetLe_pure a)) (by simp)

lemma DetLe_foldP {α β : Type} (f : β → α → Prog β) (g : β → α → β) (K : α → ℕ)
    (Inv : List α → β → Prop) (hI : ∀ a l b, Inv (a :: l) b → Inv l (g b a))
    (hf : ∀ a l b, Inv (a :: l) b → DetLe (f b a) (g b a) (K a)) :
    ∀ (l : List α) (b : β), Inv l b →
      DetLe (foldP l f b) (l.foldl g b) ((l.map fun a => K a + 1).sum)
  | [], b, _ => DetLe_pure b
  | a :: l, b, h => by
    have h1 := DetLe_foldP f g K Inv hI hf l (g b a) (hI a l b h)
    refine DetLe_mono (DetLe_bind (DetLe_charge 1) (DetLe_bind (hf a l b h) h1)) ?_
    simp only [List.map_cons, List.sum_cons]
    omega

lemma DetLe_support {α : Type} {p : Prog α} {a : α} {K : ℕ} (h : DetLe p a K) :
    ∀ x ∈ (p.run 0).support, x.1 = a ∧ x.2 ≤ K := by
  obtain ⟨k, hk, hd⟩ := h
  intro x hx
  rw [hd 0, PMF.mem_support_pure_iff] at hx
  subst hx
  exact ⟨rfl, by simpa using hk⟩

/-! ## Values and costs of the subprograms -/

noncomputable def powB (m : ℕ) : ℕ := if m = 0 then 1 else 4 + 3 * Nat.log 2 m

lemma powP_det (x : ℝ) (m : ℕ) : DetLe (powP x m) (x ^ m) (powB m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [powP]
    by_cases hm : m = 0
    · subst hm
      rw [dif_pos rfl, pow_zero]
      exact DetLe_mono (DetLe_opn 1 1) (by simp [powB])
    · rw [dif_neg hm]
      have hx : x ^ m = (if m % 2 = 0 then x ^ (m / 2) * x ^ (m / 2)
          else x ^ (m / 2) * x ^ (m / 2) * x) := by
        split_ifs with h2
        · rw [← pow_add]
          congr 1
          omega
        · rw [← pow_add, ← pow_succ]
          congr 1
          omega
      rw [hx]
      refine DetLe_mono (DetLe_bind (ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm)
        (by norm_num))) (DetLe_opn 3 _)) ?_
      unfold powB
      rw [if_neg hm]
      by_cases h1 : m = 1
      · subst h1
        simp
      · have hm2 : 2 ≤ m := by omega
        have hlog := Nat.log_of_one_lt_of_le (by norm_num : 1 < 2) hm2
        rw [if_neg (by omega : m / 2 ≠ 0)]
        omega

noncomputable def binStep (p : ℝ) (m : ℕ) (acc : List ℝ × ℝ) (k : ℕ) : List ℝ × ℝ :=
  (acc.1 ++ [acc.2 * (((m : ℝ) - k) / (k + 1)) * (p / (1 - p))],
    acc.2 * (((m : ℝ) - k) / (k + 1)) * (p / (1 - p)))

noncomputable def binRowV (p : ℝ) (m C : ℕ) : List ℝ :=
  ((List.range C).foldl (binStep p m) ([(1 - p) ^ m], (1 - p) ^ m)).1

lemma binRow_det (p : ℝ) (m C : ℕ) :
    DetLe (binRow p m C) (binRowV p m C) (powB m + 3 + C * (C + 7)) := by
  unfold binRow
  refine DetLe_mono (DetLe_bind (powP_det (1 - p) m) (DetLe_bind (DetLe_opn 3 _)
    (DetLe_bind (DetLe_foldP _ (binStep p m) (fun _ => C + 6)
      (fun l acc => acc.1.length + l.length ≤ C + 1) ?_ ?_ (List.range C) _ ?_)
      (DetLe_pure _)))) ?_
  · intro a l acc h
    simp only [binStep, List.length_append, List.length_singleton, List.length_cons,
      List.length_nil] at h ⊢
    omega
  · intro a l acc h
    simp only [List.length_cons] at h
    exact DetLe_mono (DetLe_opn _ _) (by omega)
  · simp <;> omega
  · simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
    nlinarith

noncomputable def gStepV (p : ℝ) (pM : ℕ →₀ ℝ) (C : ℕ) (T : List ℝ) (m : ℕ) : List ℝ :=
  (List.range C).map fun j => T.getD j 0 + pM m * (1 - (((binRowV p m C).take (j + 1)).sum))

noncomputable def gRowV (p : ℝ) (pM : ℕ →₀ ℝ) (supp : List ℕ) (C : ℕ) : List ℝ :=
  (List.range (C + 1)).map fun u => ((supp.foldl (gStepV p pM C) (List.replicate C 0)).take u).sum

noncomputable def gB (C : ℕ) (supp : List ℕ) : ℕ :=
  (supp.map fun m => powB m + 3 + C * (C + 7) + (1 + 6 * (C + 1)) + 1).sum + 3 * (C + 1)

lemma gRow_det (p : ℝ) (pM : ℕ →₀ ℝ) (supp : List ℕ) (C : ℕ) :
    DetLe (gRow p pM supp C) (gRowV p pM supp C) (gB C supp) := by
  unfold gRow
  refine DetLe_mono (DetLe_bind (DetLe_foldP _ (gStepV p pM C)
    (fun m => powB m + 3 + C * (C + 7) + (1 + 6 * (C + 1))) (fun _ _ => True)
    (fun _ _ _ _ => trivial) ?_ supp _ trivial) (DetLe_opn _ _)) ?_
  · intro a l T _
    exact DetLe_bind (binRow_det p a C) (DetLe_bind (DetLe_opn 1 _) (DetLe_opn _ _))
  · exact le_rfl

noncomputable def bestStep (V : List ℝ) (ri : ℝ) (g : List ℝ) (c : ℕ) (b : Option (ℝ × ℕ))
    (u : ℕ) : Option (ℝ × ℕ) :=
  match b with
  | none => some (V.getD (c - u) 0 + ri * g.getD u 0, u)
  | some (bv, bu) => if bv < V.getD (c - u) 0 + ri * g.getD u 0 then
      some (V.getD (c - u) 0 + ri * g.getD u 0, u) else some (bv, bu)

noncomputable def rowStep (V : List ℝ) (ri : ℝ) (g : List ℝ) (acc : List ℝ × List ℕ) (c : ℕ) :
    List ℝ × List ℕ :=
  (acc.1 ++ [(((List.range (c + 1)).foldl (bestStep V ri g c) none).getD (0, 0)).1],
    acc.2 ++ [(((List.range (c + 1)).foldl (bestStep V ri g c) none).getD (0, 0)).2])

noncomputable def rowF (V : List ℝ) (ri : ℝ) (g : List ℝ) (C : ℕ) : List ℝ × List ℕ :=
  (List.range (C + 1)).foldl (rowStep V ri g) ([], [])

noncomputable def tabStep {n : ℕ} (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ)
    (supp : List ℕ) (C : ℕ) (st : List ℝ × List (List ℕ)) (i : Fin n) :
    List ℝ × List (List ℕ) :=
  ((rowF st.1 (r i) (gRowV (wts.w i / wts.w0) pM supp C) C).1,
    st.2 ++ [(rowF st.1 (r i) (gRowV (wts.w i / wts.w0) pM supp C) C).2])

noncomputable def btStep {n : ℕ} (tabs : List ℝ × List (List ℕ)) (acc : (Fin n → ℕ) × ℕ)
    (i : Fin n) : (Fin n → ℕ) × ℕ :=
  (Function.update acc.1 i ((tabs.2.getD i.val []).getD acc.2 0),
    acc.2 - (tabs.2.getD i.val []).getD acc.2 0)

noncomputable def tabsV {n : ℕ} (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (C : ℕ) :
    List ℝ × List (List ℕ) :=
  (List.finRange n).foldl (tabStep wts r pM (pM.support.sort (· ≤ ·)) C)
    (List.replicate (C + 1) 0, [])

noncomputable def dpV {n : ℕ} (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (C : ℕ) :
    Fin n → ℕ :=
  ((List.finRange n).reverse.foldl (btStep (tabsV wts r pM C)) (0, C)).1

def rowB (C : ℕ) : ℕ := ((List.range (C + 1)).map fun _ => 9 * (C + 1) + (2 * C + 2) + 1).sum

noncomputable def itemB (C : ℕ) (supp : List ℕ) : ℕ := 2 + (gB C supp + (1 + (rowB C + (C + 2))))

noncomputable def totB (n C : ℕ) (pM : ℕ →₀ ℝ) : ℕ :=
  pM.support.card + 1 + (((List.finRange n).map fun _ => itemB C (pM.support.sort (· ≤ ·)) + 1).sum +
    (((List.finRange n).reverse.map fun _ => 6 + 1).sum + 0))

lemma dp_det {n : ℕ} (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (C : ℕ) :
    DetLe (dpSolve wts r pM C) (dpV wts r pM C) (totB n C pM) := by
  unfold dpSolve
  refine DetLe_bind (DetLe_opn _ _) (DetLe_bind (DetLe_foldP _
    (tabStep wts r pM (pM.support.sort (· ≤ ·)) C) (fun _ => itemB C (pM.support.sort (· ≤ ·)))
    (fun _ _ => True) (fun _ _ _ _ => trivial) ?_ (List.finRange n) _ trivial)
    (DetLe_bind (DetLe_foldP _ (btStep (tabsV wts r pM C)) (fun _ => 6) (fun _ _ => True)
      (fun _ _ _ _ => trivial) ?_ _ _ trivial) (DetLe_pure _)))
  · intro i l st _
    refine DetLe_bind (DetLe_opn 2 _) (DetLe_bind (gRow_det _ pM _ C) (DetLe_bind (DetLe_opn 1 _)
      (DetLe_bind (DetLe_mono (DetLe_foldP _ (rowStep st.1 (r i)
        (gRowV (wts.w i / wts.w0) pM (pM.support.sort (· ≤ ·)) C)) (fun _ => 9 * (C + 1) + (2 * C + 2))
        (fun l acc => (∀ c ∈ l, c ≤ C) ∧ acc.1.length + l.length ≤ C + 1 ∧
          acc.2.length + l.length ≤ C + 1) ?_ ?_ (List.range (C + 1)) _ ?_) le_rfl)
        (DetLe_opn _ _))))
    · intro c l acc h
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨fun x hx => h1 x (List.mem_cons_of_mem _ hx), ?_, ?_⟩
      · simp only [rowStep, List.length_append, List.length_singleton, List.length_cons,
          List.length_nil] at h2 ⊢
        omega
      · simp only [rowStep, List.length_append, List.length_singleton, List.length_cons,
          List.length_nil] at h3 ⊢
        omega
    · intro c l acc h
      obtain ⟨h1, h2, h3⟩ := h
      have hc : c ≤ C := h1 c (List.mem_cons_self ..)
      simp only [List.length_cons] at h2 h3
      refine DetLe_mono (DetLe_bind (DetLe_foldP _ (bestStep st.1 (r i)
        (gRowV (wts.w i / wts.w0) pM (pM.support.sort (· ≤ ·)) C) c) (fun _ => 8) (fun _ _ => True)
        (fun _ _ _ _ => trivial) ?_ (List.range (c + 1)) none trivial)
        (DetLe_opn _ _)) ?_
      · intro _ _ _ _
        exact DetLe_opn _ _
      · simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
        omega
    · refine ⟨fun x hx => ?_, by simp, by simp⟩
      rw [List.mem_range] at hx
      omega
  · intro i l acc _
    exact DetLe_mono (DetLe_bind (DetLe_opn 3 _) (DetLe_opn 3 _)) (by norm_num)

/-! ## Cost bound -/

lemma powB_le (m : ℕ) : powB m ≤ 4 * (1 + Nat.log 2 (m + 1)) := by
  unfold powB
  split_ifs
  · omega
  · have := Nat.log_mono_right (b := 2) (show m ≤ m + 1 by omega)
    omega

lemma sum_sort_eq (pM : ℕ →₀ ℝ) (f : ℕ → ℕ) :
    ((pM.support.sort (· ≤ ·)).map f).sum = ∑ m ∈ pM.support, f m := by
  rw [← List.sum_toFinset f (Finset.sort_nodup _ _), Finset.sort_toFinset]

lemma totB_le (n C : ℕ) (pM : ℕ →₀ ℝ) (hC : 1 ≤ C) (hn : 1 ≤ n)
    (hL : 1 ≤ ∑ m ∈ pM.support, (1 + Nat.log 2 (m + 1))) :
    totB n C pM ≤ 1000 * n * C ^ 2 * ∑ m ∈ pM.support, (1 + Nat.log 2 (m + 1)) := by
  obtain ⟨L, hLdef⟩ : ∃ L, L = ∑ m ∈ pM.support, (1 + Nat.log 2 (m + 1)) := ⟨_, rfl⟩
  rw [← hLdef] at hL ⊢
  have hC2 : 1 ≤ C ^ 2 := Nat.one_le_pow _ _ hC
  have hCC : C ≤ C ^ 2 := by nlinarith
  have hcard : pM.support.card ≤ L := by
    rw [hLdef, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun m _ => by omega
  have hX : 1 ≤ C ^ 2 * L := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hg : gB C (pM.support.sort (· ≤ ·)) ≤ 35 * (C ^ 2 * L) := by
    unfold gB
    rw [sum_sort_eq pM (fun m => powB m + 3 + C * (C + 7) + (1 + 6 * (C + 1)) + 1)]
    have h1 : ∑ m ∈ pM.support, (powB m + 3 + C * (C + 7) + (1 + 6 * (C + 1)) + 1) ≤
        ∑ m ∈ pM.support, (1 + Nat.log 2 (m + 1)) * (29 * C ^ 2) := by
      apply Finset.sum_le_sum
      intro m _
      have hp := powB_le m
      obtain ⟨Lm, hLm⟩ : ∃ Lm, Lm = 1 + Nat.log 2 (m + 1) := ⟨_, rfl⟩
      rw [← hLm] at hp ⊢
      have hl : 1 ≤ Lm := by omega
      have e1 : C * (C + 7) + (1 + 6 * (C + 1)) + 1 + 3 ≤ 25 * C ^ 2 := by nlinarith
      have e2 : 25 * C ^ 2 ≤ Lm * (25 * C ^ 2) := Nat.le_mul_of_pos_left _ (by omega)
      have e3 : 4 * Lm ≤ Lm * (4 * C ^ 2) := by nlinarith
      nlinarith
    rw [← Finset.sum_mul, ← hLdef] at h1
    have e4 : 3 * (C + 1) ≤ 6 * (C ^ 2 * L) := by nlinarith
    nlinarith
  have hrow : rowB C ≤ 46 * C ^ 2 := by
    unfold rowB
    simp only [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
    nlinarith
  have hitem : itemB C (pM.support.sort (· ≤ ·)) + 1 ≤ 90 * (C ^ 2 * L) := by
    unfold itemB
    have e5 : 46 * C ^ 2 ≤ 46 * (C ^ 2 * L) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    have e6 : C + 6 ≤ 7 * (C ^ 2 * L) := by nlinarith
    omega
  unfold totB
  simp only [List.map_const', List.sum_replicate, List.length_finRange, List.length_reverse,
    smul_eq_mul]
  have h2 : n * (itemB C (pM.support.sort (· ≤ ·)) + 1) ≤ n * (90 * (C ^ 2 * L)) :=
    Nat.mul_le_mul_left n hitem
  have h3 : n ≤ n * (C ^ 2 * L) := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : C ^ 2 * L ≤ n * (C ^ 2 * L) := Nat.le_mul_of_pos_left _ (by omega)
  have h5 : 1000 * n * C ^ 2 * L = 1000 * (n * (C ^ 2 * L)) := by ring
  rw [h5]
  nlinarith

/-! ## Correctness of the pure DP values -/

lemma best_spec (V : List ℝ) (ri : ℝ) (g : List ℝ) (c : ℕ) : ∀ k, ∃ bv bu,
    (List.range (k + 1)).foldl (bestStep V ri g c) none = some (bv, bu) ∧ bu ≤ k ∧
      bv = V.getD (c - bu) 0 + ri * g.getD bu 0 ∧
      ∀ u ≤ k, V.getD (c - u) 0 + ri * g.getD u 0 ≤ bv := by
  intro k
  induction k with
  | zero =>
    refine ⟨_, 0, rfl, le_rfl, rfl, fun u hu => ?_⟩
    have : u = 0 := by omega
    subst this
    exact le_rfl
  | succ k ih =>
    obtain ⟨bv, bu, h1, h2, h3, h4⟩ := ih
    rw [show List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] from List.range_succ,
      List.foldl_append, h1]
    simp only [List.foldl_cons, List.foldl_nil, bestStep]
    split_ifs with hlt
    · refine ⟨_, k + 1, rfl, le_rfl, rfl, fun u hu => ?_⟩
      rcases Nat.lt_or_ge u (k + 1) with h | h
      · linarith [h4 u (by omega)]
      · have : u = k + 1 := by omega
        subst this
        exact le_rfl
    · push_neg at hlt
      refine ⟨bv, bu, rfl, by omega, h3, fun u hu => ?_⟩
      rcases Nat.lt_or_ge u (k + 1) with h | h
      · exact h4 u (by omega)
      · have : u = k + 1 := by omega
        subst this
        exact hlt

noncomputable def RA (V : List ℝ) (ri : ℝ) (g : List ℝ) (k : ℕ) : List ℝ × List ℕ :=
  (List.range k).foldl (rowStep V ri g) ([], [])

lemma row_spec (V : List ℝ) (ri : ℝ) (g : List ℝ) : ∀ k,
    (RA V ri g k).1.length = k ∧ (RA V ri g k).2.length = k ∧
    ∀ c < k, (RA V ri g k).2.getD c 0 ≤ c ∧
      (RA V ri g k).1.getD c 0 = V.getD (c - (RA V ri g k).2.getD c 0) 0 +
        ri * g.getD ((RA V ri g k).2.getD c 0) 0 ∧
      ∀ u ≤ c, V.getD (c - u) 0 + ri * g.getD u 0 ≤ (RA V ri g k).1.getD c 0 := by
  intro k
  induction k with
  | zero => exact ⟨rfl, rfl, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨l1, l2, H⟩ := ih
    obtain ⟨bv, bu, hb1, hb2, hb3, hb4⟩ := best_spec V ri g k k
    have e : RA V ri g (k + 1) = rowStep V ri g (RA V ri g k) k := by
      unfold RA
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e]
    unfold rowStep
    rw [hb1]
    simp only [Option.getD_some, List.length_append, List.length_singleton]
    refine ⟨by omega, by omega, fun c hc => ?_⟩
    rcases Nat.lt_or_ge c k with hck | hck
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact H c hck
    · have hc' : c = k := by omega
      subst hc'
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
        l1, l2, Nat.sub_self, List.getD_cons_zero, List.getD_cons_zero]
      exact ⟨hb2, hb3, hb4⟩

lemma rowF_eq (V : List ℝ) (ri : ℝ) (g : List ℝ) (C : ℕ) : rowF V ri g C = RA V ri g (C + 1) := rfl

section Table

variable (wts : Weights n) (r : Fin n → ℝ) (pM : ℕ →₀ ℝ) (C : ℕ)

noncomputable def gg (j : Fin n) : List ℝ := gRowV (wts.w j / wts.w0) pM (pM.support.sort (· ≤ ·)) C

noncomputable def DD (k : ℕ) : List ℝ × List (List ℕ) :=
  ((List.finRange n).take k).foldl (tabStep wts r pM (pM.support.sort (· ≤ ·)) C)
    (List.replicate (C + 1) 0, [])

lemma take_finRange_succ {k : ℕ} (hk : k < n) :
    (List.finRange n).take (k + 1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
  rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hk)]
  simp

lemma DD_succ {k : ℕ} (hk : k < n) :
    DD wts r pM C (k + 1) = tabStep wts r pM (pM.support.sort (· ≤ ·)) C (DD wts r pM C k) ⟨k, hk⟩ := by
  unfold DD
  rw [take_finRange_succ hk, List.foldl_append]
  rfl

lemma DD_len : ∀ k ≤ n, (DD wts r pM C k).1.length = C + 1 ∧ (DD wts r pM C k).2.length = k := by
  intro k
  induction k with
  | zero => intro _; simp [DD]
  | succ k ih =>
    intro hk
    rw [DD_succ wts r pM C (by omega)]
    have := ih (by omega)
    unfold tabStep
    rw [rowF_eq]
    have hr := row_spec (DD wts r pM C k).1 (r ⟨k, by omega⟩) (gg wts pM C ⟨k, by omega⟩) (C + 1)
    simp only [List.length_append, List.length_singleton]
    exact ⟨hr.1, by omega⟩

lemma filter_succ {k : ℕ} (hk : k < n) :
    Finset.univ.filter (fun j : Fin n => j.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun j : Fin n => j.val < k)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_or_ge j.val k with h' | h'
    · exact Or.inr h'
    · left
      ext
      simp
      omega
  · rintro (h | h)
    · subst h
      simp
    · omega

lemma not_mem_filter {k : ℕ} (hk : k < n) :
    (⟨k, hk⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val < k) := by
  simp

lemma DD_upper : ∀ k ≤ n, ∀ (U : Fin n → ℕ) (c : ℕ), c ≤ C →
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), U j) ≤ c →
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), r j * (gg wts pM C j).getD (U j) 0) ≤
      (DD wts r pM C k).1.getD c 0 := by
  intro k
  induction k with
  | zero =>
    intro _ U c hc _
    have : Finset.univ.filter (fun j : Fin n => j.val < 0) = ∅ := by
      ext j; simp
    rw [this, Finset.sum_empty]
    unfold DD
    simp only [List.take_zero, List.foldl_nil]
    rw [List.getD_replicate _ (by omega)]
  | succ k ih =>
    intro hk U c hc hsum
    have hk' : k < n := by omega
    rw [filter_succ hk', Finset.sum_insert (not_mem_filter hk')] at hsum ⊢
    have h1 := ih (by omega) U (c - U ⟨k, hk'⟩) (by omega) (by omega)
    rw [DD_succ wts r pM C hk']
    unfold tabStep
    rw [rowF_eq]
    have hr := (row_spec (DD wts r pM C k).1 (r ⟨k, hk'⟩) (gg wts pM C ⟨k, hk'⟩) (C + 1)).2.2 c
      (by omega)
    have h2 := hr.2.2 (U ⟨k, hk'⟩) (by omega)
    unfold gg at h2 h1 ⊢
    linarith

lemma DD_row : ∀ k (hkn : k ≤ n) j (hj : j < k),
    (DD wts r pM C k).2.getD j [] = (rowF (DD wts r pM C j).1 (r ⟨j, lt_of_lt_of_le hj hkn⟩)
      (gg wts pM C ⟨j, lt_of_lt_of_le hj hkn⟩) C).2 := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj
    have hk' : k < n := by omega
    have hl := (DD_len wts r pM C k (by omega)).2
    rw [DD_succ wts r pM C hk']
    unfold tabStep
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact ih (by omega) j hjk
    · have : j = k := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero]
      rfl

lemma DD_vals {k : ℕ} (hk : k < n) :
    (DD wts r pM C (k + 1)).1 = (rowF (DD wts r pM C k).1 (r ⟨k, hk⟩) (gg wts pM C ⟨k, hk⟩) C).1 := by
  rw [DD_succ wts r pM C hk]
  rfl

noncomputable def BT (k : ℕ) (x : Fin n → ℕ) (b : ℕ) : (Fin n → ℕ) × ℕ :=
  ((List.finRange n).take k).reverse.foldl (btStep (DD wts r pM C n)) (x, b)

def BTP (k : ℕ) : Prop := ∀ (x : Fin n → ℕ) (b : ℕ), (∀ j : Fin n, j.val < k → x j = 0) → b ≤ C →
    (∀ j : Fin n, k ≤ j.val → (BT wts r pM C k x b).1 j = x j) ∧
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
      r j * (gg wts pM C j).getD ((BT wts r pM C k x b).1 j) 0) =
      (DD wts r pM C k).1.getD b 0 ∧
    (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), (BT wts r pM C k x b).1 j) ≤ b

lemma bt_zero : BTP wts r pM C 0 := by
  intro x b _ hb
  have hf : Finset.univ.filter (fun j : Fin n => j.val < 0) = ∅ := by
    ext j
    simp
  have hB : BT wts r pM C 0 x b = (x, b) := by
    unfold BT
    simp
  rw [hB, hf, Finset.sum_empty, Finset.sum_empty]
  refine ⟨fun j _ => rfl, ?_, Nat.zero_le _⟩
  have hD : (DD wts r pM C 0).1 = List.replicate (C + 1) 0 := by
    unfold DD
    simp
  rw [hD, List.getD_replicate _ (show b < C + 1 by omega)]

lemma DD_row' {k : ℕ} (hk' : k < n) :
    (DD wts r pM C n).2.getD k [] =
      (RA (DD wts r pM C k).1 (r ⟨k, hk'⟩) (gg wts pM C ⟨k, hk'⟩) (C + 1)).2 :=
  DD_row wts r pM C n le_rfl k hk'

lemma DD_vals' {k : ℕ} (hk' : k < n) :
    (DD wts r pM C (k + 1)).1 =
      (RA (DD wts r pM C k).1 (r ⟨k, hk'⟩) (gg wts pM C ⟨k, hk'⟩) (C + 1)).1 :=
  DD_vals wts r pM C hk'

lemma row_at (V : List ℝ) (ri : ℝ) (g : List ℝ) (C b : ℕ) (hb : b < C + 1) :
    (RA V ri g (C + 1)).2.getD b 0 ≤ b ∧
    (RA V ri g (C + 1)).1.getD b 0 = V.getD (b - (RA V ri g (C + 1)).2.getD b 0) 0 +
      ri * g.getD ((RA V ri g (C + 1)).2.getD b 0) 0 := by
  have h := (row_spec V ri g (C + 1)).2.2 b hb
  exact ⟨h.1, h.2.1⟩

lemma bt_u {k : ℕ} (hk' : k < n) (b : ℕ) (hb : b ≤ C) :
    ((DD wts r pM C n).2.getD k []).getD b 0 ≤ b ∧
    (DD wts r pM C (k + 1)).1.getD b 0 =
      (DD wts r pM C k).1.getD (b - ((DD wts r pM C n).2.getD k []).getD b 0) 0 +
        r ⟨k, hk'⟩ * (gg wts pM C ⟨k, hk'⟩).getD (((DD wts r pM C n).2.getD k []).getD b 0) 0 := by
  rw [DD_row' wts r pM C hk', DD_vals' wts r pM C hk']
  exact row_at _ _ _ C b (by omega)

lemma bt_list {k : ℕ} (hk' : k < n) : ((List.finRange n).take (k + 1)).reverse =
    (⟨k, hk'⟩ : Fin n) :: ((List.finRange n).take k).reverse := by
  rw [take_finRange_succ hk']
  simp

lemma bt_BT {k : ℕ} (hk' : k < n) (x : Fin n → ℕ) (b : ℕ) :
    BT wts r pM C (k + 1) x b =
      BT wts r pM C k (Function.update x ⟨k, hk'⟩ (((DD wts r pM C n).2.getD k []).getD b 0))
        (b - ((DD wts r pM C n).2.getD k []).getD b 0) := by
  unfold BT
  rw [bt_list hk', List.foldl_cons]
  try rfl

lemma bt_succ {k : ℕ} (hk' : k < n) (ih : BTP wts r pM C k) : BTP wts r pM C (k + 1) := by
  intro x b hx hb
  obtain ⟨hub, hval⟩ := bt_u wts r pM C hk' b hb
  have hBT := bt_BT wts r pM C hk' x b
  generalize ((DD wts r pM C n).2.getD k []).getD b 0 = u at hub hval hBT
  have hxs : ∀ j : Fin n, j.val < k → Function.update x ⟨k, hk'⟩ u j = 0 := by
    intro j hj
    have hne : j ≠ ⟨k, hk'⟩ := by
      intro h
      apply absurd hj
      rw [h]
      exact lt_irrefl k
    rw [Function.update_of_ne hne]
    exact hx j (by omega)
  obtain ⟨IH1, IH2, IH3⟩ := ih (Function.update x ⟨k, hk'⟩ u) (b - u) hxs (by omega)
  rw [hBT]
  have hRk : (BT wts r pM C k (Function.update x ⟨k, hk'⟩ u) (b - u)).1 ⟨k, hk'⟩ = u := by
    rw [IH1 ⟨k, hk'⟩ (le_refl k)]
    exact Function.update_self _ _ _
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · have hne : j ≠ ⟨k, hk'⟩ := by
      intro h
      apply absurd hj
      rw [h]
      exact Nat.not_succ_le_self k
    rw [IH1 j (by omega), Function.update_of_ne hne]
  · rw [filter_succ hk', Finset.sum_insert (not_mem_filter hk'), hRk, IH2, hval]
    ring
  · rw [filter_succ hk', Finset.sum_insert (not_mem_filter hk'), hRk]
    omega

lemma bt_spec : ∀ k ≤ n, BTP wts r pM C k := by
  intro k
  induction k with
  | zero => intro _; exact bt_zero wts r pM C
  | succ k ih => intro hk; exact bt_succ wts r pM C (by omega) (ih (by omega))

lemma DD_n : DD wts r pM C n = tabsV wts r pM C := by
  unfold DD tabsV
  rw [List.take_of_length_le (by simp)]

lemma filter_all : Finset.univ.filter (fun j : Fin n => j.val < n) = Finset.univ := by
  ext j; simp

theorem dp_main :
    (∀ j, dpV wts r pM C j ≤ C) ∧ (∑ j, dpV wts r pM C j) ≤ C ∧
    (∀ U : Fin n → ℕ, (∑ j, U j) ≤ C →
      (∑ j, r j * (gg wts pM C j).getD (U j) 0) ≤ ∑ j, r j * (gg wts pM C j).getD (dpV wts r pM C j) 0) := by
  have hbt := bt_spec wts r pM C n le_rfl 0 C (fun _ _ => rfl) le_rfl
  have hdp : dpV wts r pM C = (BT wts r pM C n 0 C).1 := by
    unfold dpV BT
    rw [List.take_of_length_le (by simp), DD_n]
  rw [filter_all, DD_n, ← hdp] at hbt
  obtain ⟨_, hb2, hb3⟩ := hbt
  have hsum : (∑ j, dpV wts r pM C j) ≤ C := hb3
  refine ⟨fun j => ?_, hsum, fun U hU => ?_⟩
  · exact (Finset.single_le_sum (f := fun j => dpV wts r pM C j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans hsum
  · have hup := DD_upper wts r pM C n le_rfl U C le_rfl (by rw [filter_all]; exact hU)
    rw [filter_all, DD_n] at hup
    have : (∑ j, r j * (gg wts pM C j).getD (dpV wts r pM C j) 0) = (tabsV wts r pM C).1.getD C 0 :=
      hb2
    linarith

end Table

/-! ## The rows of binomial weights -/

lemma bk_ratio (p : ℝ) (hp : p ≠ 1) (m k : ℕ) :
    bk p m k * (((m : ℝ) - k) / (k + 1)) * (p / (1 - p)) = bk p m (k + 1) := by
  have h1p : (1 : ℝ) - p ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rcases Nat.lt_or_ge k m with hk | hk
  · unfold bk
    have hcR : (m.choose k : ℝ) * ((m : ℝ) - k) = (m.choose (k + 1) : ℝ) * (k + 1) := by
      have h := Nat.choose_succ_right_eq m k
      have h' : ((m.choose (k + 1) * (k + 1) : ℕ) : ℝ) = ((m.choose k * (m - k) : ℕ) : ℝ) := by
        rw [h]
      push_cast [Nat.cast_sub hk.le] at h'
      linarith
    have e2 : m - k = (m - (k + 1)) + 1 := by omega
    rw [e2]
    calc (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - (k + 1) + 1) * (((m : ℝ) - k) / (k + 1)) *
          (p / (1 - p))
        = ((m.choose k : ℝ) * ((m : ℝ) - k)) / (k + 1) * (p ^ k * p) * (1 - p) ^ (m - (k + 1)) *
            ((1 - p) / (1 - p)) := by ring
      _ = (m.choose (k + 1) : ℝ) * (k + 1) / (k + 1) * (p ^ k * p) * (1 - p) ^ (m - (k + 1)) * 1 := by
          rw [hcR, div_self h1p]
      _ = (m.choose (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (m - (k + 1)) := by
          rw [mul_div_assoc, div_self hk1, pow_succ]
          ring
  · rw [bk_zero_of_lt p (by omega : m < k + 1)]
    rcases Nat.eq_or_lt_of_le hk with h | h
    · rw [h]
      simp
    · rw [bk_zero_of_lt p h]
      simp

lemma binRowV_spec (p : ℝ) (hp : p ≠ 1) (m C : ℕ) :
    binRowV p m C = (List.range (C + 1)).map (bk p m) := by
  have key : ∀ k, (List.range k).foldl (binStep p m) ([(1 - p) ^ m], (1 - p) ^ m) =
      ((List.range (k + 1)).map (bk p m), bk p m k) := by
    intro k
    induction k with
    | zero =>
      simp [bk]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, binStep]
      rw [bk_ratio p hp m k]
      rw [show List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] from List.range_succ,
        List.map_append]
      rfl
  unfold binRowV
  rw [key]

lemma list_sum_range (f : ℕ → ℝ) (k : ℕ) : ((List.range k).map f).sum = ∑ j ∈ Finset.range k, f j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

lemma getD_map_range (f : ℕ → ℝ) {k j : ℕ} (hj : j < k) : ((List.range k).map f).getD j 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

lemma tail_sum (p : ℝ) (m : ℕ) : ∀ u, ∑ j ∈ Finset.range u,
    (1 - ∑ k ∈ Finset.range (j + 1), bk p m k) = binMinExp p m u := by
  intro u
  induction u with
  | zero => simp [bme_zero_u]
  | succ u ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : binMinExp p m (u + 1) - binMinExp p m u =
        ∑ k ∈ Finset.range (m + 1), bk p m k * (if u < k then 1 else 0) := by
      rw [bme_eq, bme_eq, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs with h
      · rw [show min (u + 1) k = min u k + 1 by omega]
        push_cast
        ring
      · rw [show min (u + 1) k = min u k by omega]
        ring
    have h2 : ∑ k ∈ Finset.range (m + 1), bk p m k * (if u < k then 1 else 0) +
        ∑ k ∈ Finset.range (m + 1), bk p m k * (if k ≤ u then 1 else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      refine (Finset.sum_congr rfl fun k _ => ?_).trans (bk_sum p m)
      split_ifs with ha hb hb <;> first | (exfalso; omega) | ring
    have h3 : ∑ k ∈ Finset.range (m + 1), bk p m k * (if k ≤ u then 1 else 0) =
        ∑ k ∈ Finset.range (u + 1), bk p m k := by
      have hA : ∑ k ∈ Finset.range (m + 1), bk p m k * (if k ≤ u then 1 else 0) =
          ∑ k ∈ Finset.range (m + 1 + u + 1), bk p m k * (if k ≤ u then 1 else 0) := by
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_range] at hk ⊢
          omega
        · intro k hk hk'
          simp only [Finset.mem_range] at hk hk'
          rw [bk_zero_of_lt p (by omega), zero_mul]
      have hB : ∑ k ∈ Finset.range (u + 1), bk p m k =
          ∑ k ∈ Finset.range (m + 1 + u + 1), bk p m k * (if k ≤ u then 1 else 0) := by
        apply Finset.sum_subset_zero_on_sdiff
        · intro k hk
          simp only [Finset.mem_range] at hk ⊢
          omega
        · intro k hk
          simp only [Finset.mem_sdiff, Finset.mem_range] at hk
          rw [if_neg (by omega), mul_zero]
        · intro k hk
          simp only [Finset.mem_range] at hk
          rw [if_pos (by omega), mul_one]
      rw [hA, hB]
    linarith

lemma gRow_spec (p : ℝ) (hp : p ≠ 1) (pM : ℕ →₀ ℝ) (C : ℕ) (u : ℕ) (hu : u ≤ C) :
    (gRowV p pM (pM.support.sort (· ≤ ·)) C).getD u 0 =
      ∑ m ∈ pM.support, pM m * binMinExp p m u := by
  have hT : ∀ (l : List ℕ) (T0 : List ℝ), T0.length = C →
      l.foldl (gStepV p pM C) T0 = (List.range C).map (fun j => T0.getD j 0 +
        (l.map fun m => pM m * (1 - ∑ k ∈ Finset.range (j + 1), bk p m k)).sum) := by
    intro l
    induction l with
    | nil =>
      intro T0 hT0
      simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
      apply List.ext_getElem
      · simp [hT0]
      · intro j h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [List.getD_eq_getElem _ _ h1]
    | cons m l ih =>
      intro T0 hT0
      rw [List.foldl_cons, ih (gStepV p pM C T0 m) (by simp [gStepV])]
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      unfold gStepV
      rw [getD_map_range _ hj, binRowV_spec p hp m C, ← List.map_take, List.take_range,
        list_sum_range, min_eq_left (by omega), List.map_cons, List.sum_cons]
      ring
  unfold gRowV
  rw [getD_map_range _ (by omega), hT _ _ (by simp)]
  rw [← List.map_take, List.take_range, min_eq_left hu, list_sum_range]
  have e1 : ∀ j ∈ Finset.range u, (List.replicate C (0 : ℝ)).getD j 0 +
      ((pM.support.sort (· ≤ ·)).map fun m => pM m * (1 - ∑ k ∈ Finset.range (j + 1), bk p m k)).sum =
      ∑ m ∈ pM.support, pM m * (1 - ∑ k ∈ Finset.range (j + 1), bk p m k) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [List.getD_replicate _ (by omega), zero_add, ← List.sum_toFinset _ (Finset.sort_nodup _ _),
      Finset.sort_toFinset]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.mul_sum, tail_sum]

lemma expR_nonneg (wts : Weights n) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (pM : ℕ →₀ ℝ)
    (hM : IsLaw pM) (U : Fin n → ℕ) : 0 ≤ expR wts r pM U := by
  unfold expR expX
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hr i)
    (Finset.sum_nonneg fun m _ => mul_nonneg (hM.1 m) ENNReal.toReal_nonneg)

end Aux_MNLS0

open Aux_MNLS0 in
theorem solution : ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (n : ℕ) (wts : MNLStability.Weights n), 1 ≤ n → wts.Pos → ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) →
    ∀ pM : ℕ →₀ ℝ, MNLStability.IsLaw pM → ∀ C : ℕ, 1 ≤ C → ∀ e : ℝ, 0 < e →
    wts.wmax ≤ e * wts.w0 / n →
      (e < 1 → ∀ U : Fin n → ℕ,
        (1 - e) * MNLStability.Gval wts r pM U ≤ MNLStability.expR wts r pM U ∧
          MNLStability.expR wts r pM U ≤ MNLStability.Gval wts r pM U) ∧
      ∀ x ∈ ((MNLStability.dpSolve wts r pM C).run 0).support,
        MNLStability.norm1 x.1 ≤ C ∧
          (1 - e) * MNLStability.opt ⟨wts, r, C, pM⟩ ≤ MNLStability.expR wts r pM x.1 ∧
        (e < 1 → ∀ U : Fin n → ℕ, MNLStability.norm1 U ≤ C →
          MNLStability.Gval wts r pM U ≤ MNLStability.Gval wts r pM x.1) ∧
        (x.2 : ℝ) ≤ c₁ * n * (C : ℝ) ^ 2 * MNLStability.LM pM := by
  refine ⟨1000, by norm_num, ?_⟩
  intro n wts hn hw r hr pM hM C hC e he hmax
  refine ⟨fun he1 U => sandwich wts hw hn r hr pM hM e he he1 hmax U, ?_⟩
  intro x hx
  obtain ⟨hx1, hx2⟩ := DetLe_support (dp_det wts r pM C) x hx
  obtain ⟨hmC, hsum, hopt⟩ := dp_main wts r pM C
  have hGg : (∀ j, wts.w j / wts.w0 ≠ 1) → ∀ U : Fin n → ℕ, (∀ j, U j ≤ C) →
      MNLStability.Gval wts r pM U = ∑ j, r j * (gg wts pM C j).getD (U j) 0 := by
    intro hp U hU
    unfold MNLStability.Gval
    apply Finset.sum_congr rfl
    intro j _
    unfold gg
    rw [gRow_spec _ (hp j) pM C (U j) (hU j)]
  have hpne : e < 1 → ∀ j, wts.w j / wts.w0 ≠ 1 := by
    intro he1 j hj
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : wts.w j ≤ e * wts.w0 / n := (le_wmax wts j).trans hmax
    have h2 : e * wts.w0 / n ≤ e * wts.w0 := div_le_self (by nlinarith [hw.1]) hnr
    rw [div_eq_one_iff_eq hw.1.ne'] at hj
    nlinarith [hw.1]
  have hGopt : e < 1 → ∀ U : Fin n → ℕ, MNLStability.norm1 U ≤ C →
      MNLStability.Gval wts r pM U ≤ MNLStability.Gval wts r pM x.1 := by
    intro he1 U hU
    have hUj : ∀ j, U j ≤ C := fun j =>
      (Finset.single_le_sum (f := U) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hU
    rw [hGg (hpne he1) U hUj, hx1, hGg (hpne he1) _ hmC]
    exact hopt U hU
  refine ⟨?_, ?_, hGopt, ?_⟩
  · unfold MNLStability.norm1
    rw [hx1]
    exact hsum
  · by_cases he1 : e < 1
    · have hopt_eq : MNLStability.opt ⟨wts, r, C, pM⟩ = (MNLStability.feasSet n C).sup'
          ⟨0, MNLStability.zero_mem_feasSet n C⟩ (MNLStability.expR wts r pM) := rfl
      obtain ⟨U, hUmem, hUeq⟩ := Finset.exists_mem_eq_sup' ⟨0, MNLStability.zero_mem_feasSet n C⟩
        (MNLStability.expR wts r pM)
      rw [hopt_eq, hUeq]
      have hUC : MNLStability.norm1 U ≤ C := by
        unfold MNLStability.feasSet at hUmem
        exact (Finset.mem_filter.1 hUmem).2
      have h1 := (sandwich wts hw hn r hr pM hM e he he1 hmax U).2
      have h2 := hGopt he1 U hUC
      have h3 := (sandwich wts hw hn r hr pM hM e he he1 hmax x.1).1
      have h0 : 0 ≤ 1 - e := by linarith
      have h4 := mul_le_mul_of_nonneg_left h1 h0
      have h5 := mul_le_mul_of_nonneg_left h2 h0
      linarith
    · have hopt0 : 0 ≤ MNLStability.opt ⟨wts, r, C, pM⟩ :=
        le_trans (expR_nonneg wts r hr pM hM 0)
          (Finset.le_sup' (MNLStability.expR wts r pM) (MNLStability.zero_mem_feasSet n C))
      have hx0 := expR_nonneg wts r hr pM hM x.1
      push_neg at he1
      nlinarith
  · have hne : pM.support.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have h2 := hM.2
      unfold Finsupp.sum at h2
      rw [h, Finset.sum_empty] at h2
      norm_num at h2
    obtain ⟨m0, hm0⟩ := hne
    have hL : 1 ≤ ∑ m ∈ pM.support, (1 + Nat.log 2 (m + 1)) :=
      le_trans (by omega) (Finset.single_le_sum (f := fun m => 1 + Nat.log 2 (m + 1))
        (fun _ _ => Nat.zero_le _) hm0)
    have hb := totB_le n C pM hC hn hL
    have hLM : MNLStability.LM pM = ((∑ m ∈ pM.support, (1 + Nat.log 2 (m + 1)) : ℕ) : ℝ) := by
      first
        | (unfold MNLStability.LM; push_cast; rfl)
        | (unfold MNLStability.LM; push_cast)
        | simp [MNLStability.LM]
    rw [hLM]
    calc (x.2 : ℝ) ≤ (totB n C pM : ℝ) := by exact_mod_cast hx2
      _ ≤ ((1000 * n * C ^ 2 * ∑ m ∈ pM.support, (1 + Nat.log 2 (m + 1)) : ℕ) : ℝ) := by
          exact_mod_cast hb
      _ = 1000 * n * (C : ℝ) ^ 2 * ((∑ m ∈ pM.support, (1 + Nat.log 2 (m + 1)) : ℕ) : ℝ) := by
          push_cast
          try ring
