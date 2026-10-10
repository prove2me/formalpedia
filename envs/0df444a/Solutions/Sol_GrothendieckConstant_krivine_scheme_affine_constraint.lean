-- Prove2me | solution 1 for GrothendieckConstant.krivine_scheme_affine_constraint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-09T23:08:40.276984+00:00
-- url     : https://prove2.me/submissions/4bb1a019-2909-4391-965d-5da5c087a75a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KrivineSchemeDefs
import Theorems.Thm_GrothendieckConstant_krivine_cubic_kernel_bound

namespace GrothendieckConstant

open MeasureTheory Real Filter Topology

namespace AffineAux

/-- The Gaussian pair density as a function of `a = |x|²`, `b = |y|²`, `s = ⟨x,y⟩`, `t`. -/
noncomputable def Psi (k : ℕ) (a b s t : ℝ) : ℝ :=
  (1 / (2 * π * Real.sqrt (1 - t ^ 2))) ^ k *
    Real.exp (-(a - 2 * t * s + b) / (2 * (1 - t ^ 2)))

/-- Logarithmic derivative of `Psi` in `t`. -/
noncomputable def L (k : ℕ) (a b s t : ℝ) : ℝ :=
  ((k : ℝ) * t + s) / (1 - t ^ 2) - t * (a + b - 2 * t * s) / (1 - t ^ 2) ^ 2

noncomputable def L1 (k : ℕ) (a b s t : ℝ) : ℝ :=
  (k : ℝ) / (1 - t ^ 2) + 2 * k * t ^ 2 / (1 - t ^ 2) ^ 2 + 4 * t * s / (1 - t ^ 2) ^ 2
    - (a + b - 2 * t * s) / (1 - t ^ 2) ^ 2 - 4 * t ^ 2 * (a + b - 2 * t * s) / (1 - t ^ 2) ^ 3

noncomputable def L2 (k : ℕ) (a b s t : ℝ) : ℝ :=
  6 * k * t / (1 - t ^ 2) ^ 2 + 8 * k * t ^ 3 / (1 - t ^ 2) ^ 3 + 6 * s / (1 - t ^ 2) ^ 2
    + 24 * t ^ 2 * s / (1 - t ^ 2) ^ 3 - 12 * t * (a + b - 2 * t * s) / (1 - t ^ 2) ^ 3
    - 24 * t ^ 3 * (a + b - 2 * t * s) / (1 - t ^ 2) ^ 4

/-- The `n`-th `t`-derivative of `Psi`, for `n ≤ 3`. -/
noncomputable def D (k : ℕ) (a b s : ℝ) : ℕ → ℝ → ℝ
  | 0, t => Psi k a b s t
  | 1, t => Psi k a b s t * L k a b s t
  | 2, t => Psi k a b s t * (L k a b s t ^ 2 + L1 k a b s t)
  | _, t => Psi k a b s t *
      (L k a b s t ^ 3 + 3 * L k a b s t * L1 k a b s t + L2 k a b s t)

lemma gaussianPairDensity_eq (k : ℕ) (t : ℝ) (x y : Fin k → ℝ) :
    gaussianPairDensity k t x y =
      Psi k (∑ i, x i ^ 2) (∑ i, y i ^ 2) (∑ i, x i * y i) t := by
  unfold gaussianPairDensity Psi
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  congr 1; ext i; ring

lemma hasDerivAt_congr' {f g : ℝ → ℝ} {f' g' x : ℝ} (h : HasDerivAt f f' x)
    (hfg : ∀ y, g y = f y) (h' : g' = f') : HasDerivAt g g' x := by
  have : g = f := funext hfg
  subst this; subst h'; exact h

lemma hasDerivAt_c (t : ℝ) (hu : 0 < 1 - t ^ 2) :
    HasDerivAt (fun t : ℝ => 1 / (2 * π * Real.sqrt (1 - t ^ 2)))
      (1 / (2 * π * Real.sqrt (1 - t ^ 2)) * (t / (1 - t ^ 2))) t := by
  have hsq : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hu
  have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_sub 1
  have h3 := (((h1.sqrt hu.ne').const_mul (2 * π)).inv (by positivity))
  refine hasDerivAt_congr' h3 (fun y => by simp [one_div]) ?_
  · have hs2 : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hu.le
    field_simp
    rw [hs2]

lemma hasDerivAt_Psi (k : ℕ) (a b s t : ℝ) (ht : |t| < 1) :
    HasDerivAt (Psi k a b s) (Psi k a b s t * L k a b s t) t := by
  have hu : 0 < 1 - t ^ 2 := by
    have : t ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    linarith
  have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_sub 1
  have h4 := (hasDerivAt_c t hu).pow k
  have h5 : HasDerivAt (fun t : ℝ => -(a - 2 * t * s + b) / (2 * (1 - t ^ 2)))
      (s / (1 - t^2) - t * (a + b - 2 * t * s) / (1 - t ^ 2) ^ 2) t := by
    have := ((((hasDerivAt_id t).const_mul (2 * s)).const_sub a).add_const b).neg.div
      (h1.const_mul 2) (by positivity)
    refine hasDerivAt_congr' this (fun y => by simp; ring) ?_
    simp only [Pi.neg_apply, id]; field_simp; ring
  have h6 := h4.mul h5.exp
  refine hasDerivAt_congr' h6 (fun y => rfl) ?_
  simp only [Psi, L, Pi.pow_apply]
  generalize 1 / (2 * π * Real.sqrt (1 - t ^ 2)) = c
  generalize rexp (-(a - 2 * t * s + b) / (2 * (1 - t ^ 2))) = E
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
    push_cast
    ring

lemma hasDerivAt_L (k : ℕ) (a b s t : ℝ) (ht : |t| < 1) :
    HasDerivAt (L k a b s) (L1 k a b s t) t := by
  have hu : 0 < 1 - t ^ 2 := by
    have : t ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    linarith
  have hT : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
  have hU : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_sub 1
  have hN : HasDerivAt (fun t : ℝ => a + b - 2 * t * s) (-(2 * s)) t := by
    have := ((hT.const_mul 2).mul_const s).const_sub (a + b)
    exact hasDerivAt_congr' this (fun y => by ring) (by ring)
  have := (((hT.const_mul (k:ℝ)).add_const s).div hU hu.ne').sub
    ((hT.mul hN).div (hU.pow 2) (pow_ne_zero _ hu.ne'))
  refine hasDerivAt_congr' this (fun y => rfl) ?_
  simp only [L1, Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

lemma hasDerivAt_L1 (k : ℕ) (a b s t : ℝ) (ht : |t| < 1) :
    HasDerivAt (L1 k a b s) (L2 k a b s t) t := by
  have hu : 0 < 1 - t ^ 2 := by
    have : t ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    linarith
  have hT : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
  have hU : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_sub 1
  have hN : HasDerivAt (fun t : ℝ => a + b - 2 * t * s) (-(2 * s)) t := by
    have := ((hT.const_mul 2).mul_const s).const_sub (a + b)
    exact hasDerivAt_congr' this (fun y => by ring) (by ring)
  have hT2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have := (((((hasDerivAt_const t (k:ℝ)).div hU hu.ne').add
    (((hT2.const_mul (2 * (k:ℝ))).div (hU.pow 2) (pow_ne_zero _ hu.ne')))).add
    (((hT.const_mul (4 * s)).div (hU.pow 2) (pow_ne_zero _ hu.ne')))).sub
    ((hN.div (hU.pow 2) (pow_ne_zero _ hu.ne')))).sub
    (((hT2.const_mul 4).mul hN).div (hU.pow 3) (pow_ne_zero _ hu.ne'))
  refine hasDerivAt_congr' this (fun y => by
    simp only [L1, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Pi.mul_apply]; ring) ?_
  simp only [L2, Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

lemma hasDerivAt_D (k : ℕ) (a b s t : ℝ) (ht : |t| < 1) (n : ℕ) (hn : n < 3) :
    HasDerivAt (D k a b s n) (D k a b s (n + 1) t) t := by
  have hP := hasDerivAt_Psi k a b s t ht
  have hL := hasDerivAt_L k a b s t ht
  have hL1 := hasDerivAt_L1 k a b s t ht
  interval_cases n
  · exact hP
  · show HasDerivAt (fun t => Psi k a b s t * L k a b s t) _ t
    exact hasDerivAt_congr' (hP.mul hL) (fun y => rfl) (by simp only [D]; ring)
  · show HasDerivAt (fun t => Psi k a b s t * (L k a b s t ^ 2 + L1 k a b s t)) _ t
    exact hasDerivAt_congr' (hP.mul ((hL.pow 2).add hL1)) (fun y => rfl)
      (by simp only [D, Pi.add_apply, Pi.pow_apply]; push_cast; ring)

lemma term_bound (c t v X α w : ℝ) (i j : ℕ) (ht : |t| ≤ 1) (hv0 : 0 ≤ v) (hv : v ≤ 2)
    (hX : |X| ≤ α * w) :
    |c * t ^ i * X * v ^ j| ≤ |c| * (α * w) * 2 ^ j := by
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hv0]
  have h1 : |t| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
  have h2 : v ^ j ≤ 2 ^ j := pow_le_pow_left₀ hv0 hv j
  have h3 : 0 ≤ |t| ^ i := by positivity
  have h4 : 0 ≤ v ^ j := by positivity
  have h5 : 0 ≤ α * w := le_trans (abs_nonneg _) hX
  calc |c| * |t| ^ i * |X| * v ^ j ≤ |c| * 1 * (α * w) * 2 ^ j := by gcongr
    _ = _ := by ring

lemma L_bounds (k : ℕ) (a b s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : |s| ≤ (a + b) / 2)
    (ht : |t| ≤ 1 / 2) :
    |L k a b s t| ≤ (100 * (k : ℝ) + 1200) * (1 + a + b) ∧
    |L1 k a b s t| ≤ (100 * (k : ℝ) + 1200) * (1 + a + b) ∧
    |L2 k a b s t| ≤ (100 * (k : ℝ) + 1200) * (1 + a + b) := by
  set w := 1 + a + b with hw
  have ht1 : |t| ≤ 1 := by linarith
  have hu : 3 / 4 ≤ 1 - t ^ 2 := by
    have : t ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
    linarith
  set v := 1 / (1 - t ^ 2) with hv
  have hv0 : 0 ≤ v := by positivity
  have hv2 : v ≤ 2 := by rw [hv, div_le_iff₀ (by linarith)]; linarith
  have h1 : |(1:ℝ)| ≤ 1 * w := by simp; linarith
  have hsw : |s| ≤ 1 * w := by linarith
  have hN : |a + b - 2 * t * s| ≤ 2 * w := by
    have : |2 * t * s| ≤ w := by
      rw [abs_mul, abs_mul]; norm_num
      nlinarith [abs_nonneg s, abs_nonneg t]
    have := abs_sub (a + b) (2 * t * s)
    rw [abs_of_nonneg (by linarith : 0 ≤ a + b)] at this
    linarith
  have hk : (0:ℝ) ≤ k := by positivity
  have hw0 : 0 ≤ w := by linarith
  have hkw : 0 ≤ (k:ℝ) * w := by positivity
  have hu0 : (1 - t ^ 2) ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have e : L k a b s t = (k:ℝ) * t ^ 1 * 1 * v ^ 1 + 1 * t ^ 0 * s * v ^ 1
        - 1 * t ^ 1 * (a + b - 2 * t * s) * v ^ 2 := by
      simp only [L, hv]; field_simp
    rw [e]
    have := term_bound (k:ℝ) t v 1 1 w 1 1 ht1 hv0 hv2 h1
    have := term_bound 1 t v s 1 w 0 1 ht1 hv0 hv2 hsw
    have := term_bound 1 t v _ 2 w 1 2 ht1 hv0 hv2 hN
    simp only [abs_one, abs_of_nonneg hk] at *
    rw [abs_le] at *
    constructor <;> linarith
  · have e : L1 k a b s t = (k:ℝ) * t ^ 0 * 1 * v ^ 1 + (2 * k) * t ^ 2 * 1 * v ^ 2
        + 4 * t ^ 1 * s * v ^ 2 - 1 * t ^ 0 * (a + b - 2 * t * s) * v ^ 2
        - 4 * t ^ 2 * (a + b - 2 * t * s) * v ^ 3 := by
      simp only [L1, hv]; field_simp
    rw [e]
    have := term_bound (k:ℝ) t v 1 1 w 0 1 ht1 hv0 hv2 h1
    have := term_bound (2 * k) t v 1 1 w 2 2 ht1 hv0 hv2 h1
    have := term_bound 4 t v s 1 w 1 2 ht1 hv0 hv2 hsw
    have := term_bound 1 t v _ 2 w 0 2 ht1 hv0 hv2 hN
    have := term_bound 4 t v _ 2 w 2 3 ht1 hv0 hv2 hN
    simp only [abs_one, abs_of_nonneg hk, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * k),
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at *
    rw [abs_le] at *
    constructor <;> linarith
  · have e : L2 k a b s t = (6 * k) * t ^ 1 * 1 * v ^ 2 + (8 * k) * t ^ 3 * 1 * v ^ 3
        + 6 * t ^ 0 * s * v ^ 2 + 24 * t ^ 2 * s * v ^ 3
        - 12 * t ^ 1 * (a + b - 2 * t * s) * v ^ 3
        - 24 * t ^ 3 * (a + b - 2 * t * s) * v ^ 4 := by
      simp only [L2, hv]; field_simp
    rw [e]
    have := term_bound (6 * k) t v 1 1 w 1 2 ht1 hv0 hv2 h1
    have := term_bound (8 * k) t v 1 1 w 3 3 ht1 hv0 hv2 h1
    have := term_bound 6 t v s 1 w 0 2 ht1 hv0 hv2 hsw
    have := term_bound 24 t v s 1 w 2 3 ht1 hv0 hv2 hsw
    have := term_bound 12 t v _ 2 w 1 3 ht1 hv0 hv2 hN
    have := term_bound 24 t v _ 2 w 3 4 ht1 hv0 hv2 hN
    simp only [abs_of_nonneg (by positivity : (0:ℝ) ≤ 6 * k),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 8 * k),
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 24),
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12)] at *
    rw [abs_le] at *
    constructor <;> linarith

lemma Psi_bounds (k : ℕ) (a b s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : |s| ≤ (a + b) / 2)
    (ht : |t| ≤ 1 / 2) :
    0 ≤ Psi k a b s t ∧ Psi k a b s t ≤ Real.exp (-(a + b) / 4) := by
  have hu : 3 / 4 ≤ 1 - t ^ 2 := by
    have : t ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
    linarith
  have hu1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  have hsq : 1 / 2 ≤ Real.sqrt (1 - t ^ 2) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hc0 : 0 ≤ 1 / (2 * π * Real.sqrt (1 - t ^ 2)) := by positivity
  have hc1 : 1 / (2 * π * Real.sqrt (1 - t ^ 2)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  unfold Psi
  refine ⟨by positivity, ?_⟩
  have hck : (1 / (2 * π * Real.sqrt (1 - t ^ 2))) ^ k ≤ 1 := pow_le_one₀ hc0 hc1
  have hexp : Real.exp (-(a - 2 * t * s + b) / (2 * (1 - t ^ 2))) ≤ Real.exp (-(a + b) / 4) := by
    apply Real.exp_le_exp.mpr
    have h2ts : |2 * t * s| ≤ (a + b) / 2 := by
      rw [abs_mul, abs_mul]; norm_num
      nlinarith [abs_nonneg s, abs_nonneg t]
    have hN : (a + b) / 2 ≤ a - 2 * t * s + b := by
      have := le_abs_self (2 * t * s); linarith
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  calc _ ≤ 1 * Real.exp (-(a + b) / 4) := by gcongr
    _ = _ := one_mul _

lemma cube_mul_exp_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 + a + b) ^ 3 * Real.exp (-(a + b) / 4) ≤ 3072 * Real.exp 1 * Real.exp (-(a + b) / 8) := by
  have h := Real.pow_div_factorial_le_exp ((1 + a + b) / 8) (by positivity) 3
  have h3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3, div_pow, div_div, div_le_iff₀ (by norm_num)] at h
  have hE : Real.exp ((1 + a + b) / 8) * Real.exp (-(a + b) / 4) ≤
      Real.exp 1 * Real.exp (-(a + b) / 8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr; linarith
  calc (1 + a + b) ^ 3 * Real.exp (-(a + b) / 4)
      ≤ (Real.exp ((1 + a + b) / 8) * (8 ^ 3 * 6)) * Real.exp (-(a + b) / 4) := by gcongr
    _ = 3072 * (Real.exp ((1 + a + b) / 8) * Real.exp (-(a + b) / 4)) := by ring
    _ ≤ 3072 * (Real.exp 1 * Real.exp (-(a + b) / 8)) := by gcongr
    _ = _ := by ring

/-- Uniform bound on `D` for `|t| ≤ 1/2`. -/
lemma abs_D_le (k : ℕ) (a b s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : |s| ≤ (a + b) / 2)
    (ht : |t| ≤ 1 / 2) (n : ℕ) :
    |D k a b s n t| ≤ (100 * (k : ℝ) + 1200) ^ 3 * 5 * 3072 * Real.exp 1 *
      Real.exp (-(a + b) / 8) := by
  obtain ⟨hL, hL1, hL2⟩ := L_bounds k a b s t ha hb hs ht
  obtain ⟨hP0, hP⟩ := Psi_bounds k a b s t ha hb hs ht
  set M : ℝ := 100 * (k : ℝ) + 1200 with hM
  set w : ℝ := 1 + a + b with hw
  have hM1 : 1 ≤ M := by have : (0:ℝ) ≤ k := by positivity
                         linarith
  have hw1 : 1 ≤ w := by linarith
  set m := M * w with hm
  have hm1 : 1 ≤ m := one_le_mul_of_one_le_of_one_le hM1 hw1
  have hpoly : |D k a b s n t| ≤ Psi k a b s t * (5 * m ^ 3) := by
    have hm2 : m ≤ m ^ 2 := by nlinarith
    have hm3 : m ^ 2 ≤ m ^ 3 := by nlinarith
    have key : ∀ X : ℝ, |X| ≤ 5 * m ^ 3 → |Psi k a b s t * X| ≤ Psi k a b s t * (5 * m ^ 3) := by
      intro X hX
      rw [abs_mul, abs_of_nonneg hP0]
      exact mul_le_mul_of_nonneg_left hX hP0
    rcases n with _ | _ | _ | n
    · simp only [D, abs_of_nonneg hP0]
      nlinarith
    · exact key _ (by linarith)
    · apply key
      calc |L k a b s t ^ 2 + L1 k a b s t| ≤ |L k a b s t| ^ 2 + |L1 k a b s t| := by
            rw [← abs_pow]; exact abs_add_le _ _
        _ ≤ m ^ 2 + m := by gcongr
        _ ≤ 5 * m ^ 3 := by linarith
    · apply key
      calc |L k a b s t ^ 3 + 3 * L k a b s t * L1 k a b s t + L2 k a b s t|
            ≤ |L k a b s t| ^ 3 + 3 * |L k a b s t| * |L1 k a b s t| + |L2 k a b s t| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            rw [abs_pow, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
        _ ≤ m ^ 3 + 3 * m * m + m := by gcongr
        _ ≤ 5 * m ^ 3 := by nlinarith
  have hcube := cube_mul_exp_le a b ha hb
  calc |D k a b s n t| ≤ Psi k a b s t * (5 * m ^ 3) := hpoly
    _ ≤ Real.exp (-(a + b) / 4) * (5 * m ^ 3) := by gcongr
    _ = M ^ 3 * 5 * (w ^ 3 * Real.exp (-(a + b) / 4)) := by rw [hm]; ring
    _ ≤ M ^ 3 * 5 * (3072 * Real.exp 1 * Real.exp (-(a + b) / 8)) := by gcongr
    _ = _ := by ring

lemma D_zero_one (k : ℕ) (a b s : ℝ) : D k a b s 1 0 = Psi k a b s 0 * s := by
  simp [D, L]

lemma D_zero_three (k : ℕ) (a b s : ℝ) :
    D k a b s 3 0 = Psi k a b s 0 * (s ^ 3 - 3 * s * (a + b) + (3 * k + 6) * s) := by
  simp only [D, L, L1, L2]; congr 1; norm_num; ring

section Integrals

variable {k : ℕ}

/-- `|x|²`, `|y|²`, `⟨x,y⟩` on the product space. -/
noncomputable def qA (z : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ := ∑ i, z.1 i ^ 2
noncomputable def qB (z : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ := ∑ i, z.2 i ^ 2
noncomputable def qC (z : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ := ∑ i, z.1 i * z.2 i

/-- The integrand of the `n`-th derivative of the correlation function. -/
noncomputable def Fint (S : KrivineScheme k) (n : ℕ) (t : ℝ)
    (z : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  S.f z.1 * S.g z.2 * D k (qA z) (qB z) (qC z) n t

/-- The common dominating constant. -/
noncomputable def Kc (k : ℕ) : ℝ := (100 * (k : ℝ) + 1200) ^ 3 * 5 * 3072 * Real.exp 1

noncomputable def bnd (k : ℕ) (z : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  Kc k * Real.exp (-(qA z + qB z) / 8)

lemma qA_nonneg (z : (Fin k → ℝ) × (Fin k → ℝ)) : 0 ≤ qA z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma qB_nonneg (z : (Fin k → ℝ) × (Fin k → ℝ)) : 0 ≤ qB z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma abs_qC_le (z : (Fin k → ℝ) × (Fin k → ℝ)) : |qC z| ≤ (qA z + qB z) / 2 := by
  unfold qA qB qC
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  nlinarith [sq_nonneg (|z.1 i| - |z.2 i|), sq_abs (z.1 i), sq_abs (z.2 i)]

lemma integrable_bnd : Integrable (bnd k) (volume : Measure ((Fin k → ℝ) × (Fin k → ℝ))) := by
  have h1 : Integrable (fun x : Fin k → ℝ => ∏ i, Real.exp (-(1 / 8 : ℝ) * x i ^ 2))
      (volume : Measure (Fin k → ℝ)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ x => Real.exp (-(1 / 8 : ℝ) * x ^ 2))
      fun _ => integrable_exp_neg_mul_sq (by norm_num)
  have h2 := (h1.mul_prod h1).const_mul (Kc k)
  rw [Measure.volume_eq_prod]
  refine h2.congr (ae_of_all _ fun z => ?_)
  simp only [bnd, qA, qB, ← Real.exp_sum, ← Real.exp_add]
  congr 2
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

lemma measurable_Fint (S : KrivineScheme k) (n : ℕ) (t : ℝ) : Measurable (Fint S n t) := by
  have hf : Measurable fun z : (Fin k → ℝ) × (Fin k → ℝ) => S.f z.1 :=
    S.measurable_f.comp measurable_fst
  have hg : Measurable fun z : (Fin k → ℝ) × (Fin k → ℝ) => S.g z.2 :=
    S.measurable_g.comp measurable_snd
  have hA : Measurable (qA (k := k)) := by unfold qA; fun_prop
  have hB : Measurable (qB (k := k)) := by unfold qB; fun_prop
  have hC : Measurable (qC (k := k)) := by unfold qC; fun_prop
  have hD : Measurable fun z : (Fin k → ℝ) × (Fin k → ℝ) => D k (qA z) (qB z) (qC z) n t := by
    rcases n with _ | _ | _ | n <;> simp only [D, Psi, L, L1, L2] <;> fun_prop
  exact (hf.mul hg).mul hD

lemma norm_Fint_le (S : KrivineScheme k) (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 2)
    (z : (Fin k → ℝ) × (Fin k → ℝ)) : ‖Fint S n t z‖ ≤ bnd k z := by
  have hf : |S.f z.1| = 1 := by rcases S.f_sign z.1 with h | h <;> simp [h]
  have hg : |S.g z.2| = 1 := by rcases S.g_sign z.2 with h | h <;> simp [h]
  rw [Real.norm_eq_abs, Fint, abs_mul, abs_mul, hf, hg, one_mul, one_mul]
  exact abs_D_le k _ _ _ t (qA_nonneg z) (qB_nonneg z) (abs_qC_le z) ht n

lemma integrable_Fint (S : KrivineScheme k) (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 2) :
    Integrable (Fint S n t) (volume : Measure ((Fin k → ℝ) × (Fin k → ℝ))) :=
  integrable_bnd.mono' (measurable_Fint S n t).aestronglyMeasurable
    (ae_of_all _ (norm_Fint_le S n t ht))

lemma hasDerivAt_integral_Fint (S : KrivineScheme k) (n : ℕ) (hn : n < 3) (t₀ : ℝ)
    (ht₀ : |t₀| < 1 / 4) :
    HasDerivAt (fun t => ∫ z, Fint S n t z) (∫ z, Fint S (n + 1) t₀ z) t₀ := by
  have hball : ∀ x ∈ Metric.ball t₀ (1 / 4), |x| < 1 / 2 := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have := abs_sub_abs_le_abs_sub x t₀
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bnd k)
    (Metric.ball_mem_nhds t₀ (by norm_num : (0:ℝ) < 1 / 4))
    (Eventually.of_forall fun t => (measurable_Fint S n t).aestronglyMeasurable)
    (integrable_Fint S n t₀ (by linarith))
    (measurable_Fint S (n + 1) t₀).aestronglyMeasurable
    (ae_of_all _ fun z x hx => norm_Fint_le S (n + 1) x (hball x hx).le z)
    integrable_bnd
    (ae_of_all _ fun z x hx => ?_)).2
  have hx1 : |x| < 1 := by linarith [hball x hx]
  exact (hasDerivAt_D k _ _ _ x hx1 n hn).const_mul _

lemma correlationFunction_eq (S : KrivineScheme k) (t : ℝ) (ht : |t| ≤ 1 / 2) :
    correlationFunction S t = π / 2 * ∫ z, Fint S 0 t z := by
  unfold correlationFunction
  congr 1
  rw [Measure.volume_eq_prod, integral_prod _ (by
    rw [← Measure.volume_eq_prod]; exact integrable_Fint S 0 t ht)]
  simp only [Fint, D, qA, qB, qC, gaussianPairDensity_eq]

end Integrals

end AffineAux

end GrothendieckConstant

open GrothendieckConstant GrothendieckConstant.AffineAux MeasureTheory Real Filter Topology

theorem solution (k : ℕ) (S : KrivineScheme k) :
    2 * coeffLinear S - 11 / 6 ≤ coeffCubic S := by
  set G : ℕ → ℝ → ℝ := fun n t => ∫ z, Fint S n t z with hG
  have hHG : ∀ t, |t| < 1 / 2 → correlationFunction S t = π / 2 * G 0 t :=
    fun t ht => correlationFunction_eq S t ht.le
  have hopen : ∀ t : ℝ, |t| < 1 / 2 → ∀ᶠ x : ℝ in 𝓝 t, |x| < 1 / 2 := by
    intro t ht
    exact (isOpen_lt continuous_abs continuous_const).mem_nhds ht
  have hopen' : ∀ t : ℝ, |t| < 1 / 4 → ∀ᶠ x : ℝ in 𝓝 t, |x| < 1 / 4 := by
    intro t ht
    exact (isOpen_lt continuous_abs continuous_const).mem_nhds ht
  have hd1 : ∀ t, |t| < 1 / 4 →
      HasDerivAt (correlationFunction S) (π / 2 * G 1 t) t := by
    intro t ht
    refine ((hasDerivAt_integral_Fint S 0 (by norm_num) t ht).const_mul (π / 2)).congr_of_eventuallyEq ?_
    filter_upwards [hopen t (by linarith)] with x hx
    exact hHG x hx
  have hd2 : ∀ t, |t| < 1 / 4 →
      HasDerivAt (deriv (correlationFunction S)) (π / 2 * G 2 t) t := by
    intro t ht
    refine ((hasDerivAt_integral_Fint S 1 (by norm_num) t ht).const_mul (π / 2)).congr_of_eventuallyEq ?_
    filter_upwards [hopen' t ht] with x hx
    exact (hd1 x hx).deriv
  have hd3 : HasDerivAt (deriv (deriv (correlationFunction S))) (π / 2 * G 3 0) 0 := by
    refine ((hasDerivAt_integral_Fint S 2 (by norm_num) 0 (by norm_num)).const_mul (π / 2)).congr_of_eventuallyEq ?_
    filter_upwards [hopen' 0 (by norm_num)] with x hx
    exact (hd2 x hx).deriv
  have hb1 : coeffLinear S = π / 2 * G 1 0 := (hd1 0 (by norm_num)).deriv
  have hb3 : coeffCubic S = π / 2 * G 3 0 / 6 := by
    unfold coeffCubic
    rw [iteratedDeriv_eq_iterate]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hd3.deriv]
  -- the child inequality, rewritten on the product space
  have hchild := krivine_cubic_kernel_bound k S
  have hint1 := integrable_Fint S 1 0 (by norm_num)
  have hint3 := integrable_Fint S 3 0 (by norm_num)
  have hkey : ∫ x : Fin k → ℝ, ∫ y : Fin k → ℝ,
      S.f x * S.g y *
        ((∑ i, x i * y i) ^ 3
          - 3 * (∑ i, x i * y i) * (∑ i, x i ^ 2 + ∑ i, y i ^ 2)
          + (3 * (k : ℝ) - 6) * (∑ i, x i * y i)) * gaussianPairDensity k 0 x y
      = G 3 0 - 12 * G 1 0 := by
    have h := hint3.sub (hint1.const_mul 12)
    rw [hG]
    simp only
    rw [← integral_const_mul, ← integral_sub hint3 (hint1.const_mul 12),
      Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact h)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [Fint, D_zero_one, D_zero_three, qA, qB, qC, gaussianPairDensity_eq]
    ring
  rw [hkey] at hchild
  rw [hb1, hb3]
  have hpi := Real.pi_pos
  have : -22 / π * π = -22 := by field_simp
  nlinarith

