-- Prove2me | solution 1 for OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:56:50.320626+00:00
-- url     : https://prove2.me/submissions/e6324f06-795f-4a85-bb4f-a7e510d9b9b6

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S011

section
-- module Solutions.OAIQ042_SS.StripMass_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory


theorem omega_nonneg (x : ℝ) : 0 ≤ omega x := by
  unfold omega
  positivity

theorem omega_pos {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 < omega x := by
  have hx0 := hx.1
  have hh : 1 < (1 + x) / (2 * x) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * x)).2
    linarith [hx.2]
  have hh' : 1 < Real.sqrt ((1 + x) / (2 * x)) := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hh
  unfold omega
  exact mul_pos (by norm_num) (Real.sqrt_pos.2 (sub_pos.2 hh'))

theorem omega_le_rpow {x : ℝ} (hx : x ∈ Ioo 0 1) :
    omega x ≤ x ^ (-(1 / 4 : ℝ)) := by
  have hx0 := hx.1
  have ha : (1 + x) / (2 * x) ≤ 1 / x := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * x) hx.1).2
    nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)]
  have hb : Real.sqrt ((1 + x) / (2 * x)) - 1 ≤ Real.sqrt (1 / x) :=
    (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.sqrt_le_sqrt ha)
  calc
    omega x ≤ Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1) := by
      unfold omega
      nlinarith [Real.sqrt_nonneg (Real.sqrt ((1 + x) / (2 * x)) - 1)]
    _ ≤ Real.sqrt (Real.sqrt (1 / x)) := Real.sqrt_le_sqrt hb
    _ = x ^ (-(1 / 4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (by positivity : 0 ≤ 1 / x)]
      norm_num only [one_div, show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
      rw [Real.inv_rpow hx.1.le, Real.rpow_neg hx.1.le]

theorem measurable_omega : Measurable omega := by
  unfold omega
  fun_prop

theorem integrableOn_omega : IntegrableOn omega (Ioo 0 1) := by
  have hh : IntegrableOn (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2
      (by norm_num)
  apply hh.mono' measurable_omega.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (omega_nonneg x)] using omega_le_rpow hx

theorem isOpen_orderedDomain (N : ℕ) : IsOpen (orderedDomain N) := by
  have heq : orderedDomain N =
      (⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i < j), {y | y i < y j}) ∩
      (⋂ i : Fin N, {y | y i ∈ Ioo (0 : ℝ) 1}) := by
    ext y
    simp only [orderedDomain, mem_ofPred_eq, mem_inter_iff, mem_iInter, StrictMono]
  rw [heq]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

 theorem orderedDomain_nonempty (N : ℕ) : (orderedDomain N).Nonempty := by
  refine ⟨fun i => ((i : ℕ) + 1 : ℝ) / (N + 1 : ℕ), ?_⟩
  constructor
  · intro i j hij
    apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < (N + 1 : ℕ))).2
    exact_mod_cast Nat.add_lt_add_right hij 1
  · intro i
    constructor
    · exact div_pos (by positivity) (by positivity)
    · apply (div_lt_one (by positivity : (0 : ℝ) < (N + 1 : ℕ))).2
      exact_mod_cast Nat.add_lt_add_right i.isLt 1

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeficitBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators

section CauchyAlternants
open _root_.Matrix


theorem det_cauchyMatrix_pos {n : ℕ} (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i) :
    0 < (cauchyMatrix x y).det := by
  induction n with
  | zero => simp [Matrix.det_isEmpty]
  | succ n ih =>
    let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := cauchyMatrix x y
    let B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
      Matrix.of fun i j => if i = 0 then A i j else A i j - (x 0 + y 0) / (x i + y 0) * A 0 j
    have hAB : A.det = B.det := by
      apply Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun i => if i = 0 then 0 else (x 0 + y 0) / (x i + y 0)) 0
      · simp
      · intro i j
        by_cases hi : i = 0
        · simp [hi, B]
        · simp only [B, Matrix.of_apply, hi, ite_false, ite_true]
          ring
    have hB0 (i : Fin n) : B i.succ 0 = 0 := by
      simp only [B, Matrix.of_apply, Fin.succ_ne_zero, ite_false, A, cauchyMatrix]
      have hsum (i j) : x i + y j ≠ 0 := (add_pos (hx0 i) (hy0 j)).ne'
      field_simp [hsum]
      ring
    let r : Fin n → ℝ := fun i => (x i.succ - x 0) / (x i.succ + y 0)
    let s : Fin n → ℝ := fun j => (y j.succ - y 0) / (x 0 + y j.succ)
    have htail : B.submatrix Fin.succ Fin.succ =
      Matrix.of (fun i j : Fin n => r i * (s j * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)) := by
      apply Matrix.ext
      intro i j
      change 1 / (x i.succ + y j.succ) -
        (x 0 + y 0) / (x i.succ + y 0) * (1 / (x 0 + y j.succ)) =
        ((x i.succ - x 0) / (x i.succ + y 0)) *
          (((y j.succ - y 0) / (x 0 + y j.succ)) * (1 / (x i.succ + y j.succ)))
      have hsum (i j) : x i + y j ≠ 0 := (add_pos (hx0 i) (hy0 j)).ne'
      field_simp [hsum]
      ring
    have hdetB : B.det = A 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      simp [hB0, show B 0 0 = A 0 0 by simp [B]]
    have hscale : (Matrix.of (fun i j : Fin n => r i * (s j * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j))).det =
        (∏ i, r i) * ((∏ j, s j) * (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det) := by
      calc
        _ = (∏ i, r i) * (Matrix.of (fun i j => s j * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)).det := by
          simpa only [Matrix.of_apply] using Matrix.det_mul_column r
            (Matrix.of fun i j => s j * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)
        _ = _ := by rw [Matrix.det_mul_row]
    change 0 < A.det
    rw [hAB, hdetB, htail, hscale]
    apply mul_pos
    · exact one_div_pos.2 (add_pos (hx0 _) (hy0 _))
    · apply mul_pos
      · exact Finset.prod_pos fun i _ => div_pos (sub_pos.2 (hx (Fin.succ_pos i))) (add_pos (hx0 _) (hy0 _))
      · apply mul_pos
        · exact Finset.prod_pos fun i _ => div_pos (sub_pos.2 (hy (Fin.succ_pos i))) (add_pos (hx0 _) (hy0 _))
        · exact ih _ _ (hx.comp (Fin.strictMono_succ)) (hy.comp (Fin.strictMono_succ))
            (fun i => hx0 i.succ) (fun i => hy0 i.succ)

theorem det_vandermonde_pos {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) :
    0 < (Matrix.vandermonde x).det := by
  rw [Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.2 (hx (Finset.mem_Ioi.1 hj))

 theorem cauchyAlternant_pos {n : ℕ} (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i) :
    0 < cauchyAlternant x y :=
  mul_pos (mul_pos (det_vandermonde_pos x hx) (det_cauchyMatrix_pos x y hx hy hx0 hy0))
    (det_vandermonde_pos y hy)

 theorem cauchyAlternant_permute {n : ℕ} (x y : Fin n → ℝ) (σ τ : Equiv.Perm (Fin n)) :
    cauchyAlternant (x ∘ σ) (y ∘ τ) = cauchyAlternant x y := by
  have hV (v : Fin n → ℝ) (p : Equiv.Perm (Fin n)) :
      (Matrix.vandermonde (v ∘ p)).det = (p.sign : ℝ) * (Matrix.vandermonde v).det := by
    have heq : Matrix.vandermonde (v ∘ p) = (Matrix.vandermonde v).submatrix p id := rfl
    rw [heq, Matrix.det_permute]
  have hC : cauchyMatrix (x ∘ σ) (y ∘ τ) = (cauchyMatrix x y).submatrix σ τ := rfl
  unfold cauchyAlternant
  rw [hV, hV, hC]
  have hCdet : ((cauchyMatrix x y).submatrix σ τ).det =
      (σ.sign : ℝ) * ((τ.sign : ℝ) * (cauchyMatrix x y).det) := by
    have heq : (cauchyMatrix x y).submatrix σ τ =
      ((cauchyMatrix x y).submatrix id τ).submatrix σ id := rfl
    rw [heq, Matrix.det_permute, Matrix.det_permute']
  rw [hCdet]
  have hs (p : Equiv.Perm (Fin n)) : (p.sign : ℝ) * (p.sign : ℝ) = 1 := by
    norm_cast
    simp [Int.units_mul_self]
  calc
    _ = ((σ.sign : ℝ) * (σ.sign : ℝ)) * ((τ.sign : ℝ) * (τ.sign : ℝ)) *
      ((Matrix.vandermonde x).det * (cauchyMatrix x y).det * (Matrix.vandermonde y).det) := by ring
    _ = _ := by rw [hs, hs]; ring

 theorem cauchyAlternant_nonneg {n : ℕ} (x y : Fin n → ℝ)
    (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i) : 0 ≤ cauchyAlternant x y := by
  by_cases hx : Function.Injective x
  · by_cases hy : Function.Injective y
    · have hxs : StrictMono (x ∘ Tuple.sort x) :=
        (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)
      have hys : StrictMono (y ∘ Tuple.sort y) :=
        (Tuple.monotone_sort y).strictMono_of_injective (hy.comp (Tuple.sort y).injective)
      rw [← cauchyAlternant_permute x y (Tuple.sort x) (Tuple.sort y)]
      exact (cauchyAlternant_pos _ _ hxs hys (fun i => hx0 _) (fun i => hy0 _)).le
    · have hz : (Matrix.vandermonde y).det = 0 := by
        by_contra h
        exact hy (Matrix.det_vandermonde_ne_zero_iff.1 h)
      simp [cauchyAlternant, hz]
  · have hz : (Matrix.vandermonde x).det = 0 := by
      by_contra h
      exact hx (Matrix.det_vandermonde_ne_zero_iff.1 h)
    simp [cauchyAlternant, hz]

end CauchyAlternants

section DeterminantIntegration
open MeasureTheory _root_.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]

 theorem integrable_det_columns (F : n → n → α → ℝ)
    (hF : ∀ i j, Integrable (F i j) μ) :
    Integrable (fun x : n → α => (Matrix.of fun i j => F i j (x j)).det) (Measure.pi fun _ => μ) := by
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  apply integrable_finsetSum
  intro σ _
  exact (Integrable.fintype_prod fun j => hF (σ j) j).const_mul _

 theorem integral_det_columns (F : n → n → α → ℝ)
    (hF : ∀ i j, Integrable (F i j) μ) :
    (∫ x : n → α, (Matrix.of fun i j => F i j (x j)).det ∂Measure.pi (fun _ => μ)) =
      (Matrix.of fun i j => ∫ t, F i j t ∂μ).det := by
  simp_rw [Matrix.det_apply', Matrix.of_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [integral_const_mul, integral_fintype_prod_eq_prod]
  · intro σ _
    exact (Integrable.fintype_prod fun j => hF (σ j) j).const_mul _

theorem integrable_det_mul_det (f g : n → α → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    Integrable (fun x : n → α => (Matrix.of fun i j => f i (x j)).det *
        (Matrix.of fun i j => g i (x j)).det) (Measure.pi fun _ => μ) := by
  classical
  let H : Equiv.Perm n → (n → α) → ℝ := fun σ x =>
    (Matrix.of fun i j => f (σ j) (x j) * g i (x j)).det
  have hH (σ : Equiv.Perm n) : Integrable (H σ) (Measure.pi fun _ => μ) := by
    exact integrable_det_columns (fun i j t => f (σ j) t * g i t) (fun i j => hfg _ _)
  have hexpand (x : n → α) :
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
      ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℝ) * H σ x := by
    rw [Matrix.det_apply', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [H]
    have hscale := Matrix.det_mul_row (fun j => f (σ j) (x j))
      (Matrix.of fun i j => g i (x j))
    simp only [Matrix.of_apply] at hscale
    rw [hscale, mul_assoc]
  simp_rw [hexpand]
  exact integrable_finsetSum _ fun σ _ => (hH σ).const_mul _

 

theorem integral_det_mul_det (f g : n → α → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    (∫ x : n → α, (Matrix.of fun i j => f i (x j)).det *
        (Matrix.of fun i j => g i (x j)).det ∂Measure.pi (fun _ => μ)) =
      (Fintype.card (Equiv.Perm n) : ℝ) *
        (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).det := by
  classical
  let H : Equiv.Perm n → (n → α) → ℝ := fun σ x =>
    (Matrix.of fun i j => f (σ j) (x j) * g i (x j)).det
  have hH (σ : Equiv.Perm n) : Integrable (H σ) (Measure.pi fun _ => μ) := by
    exact integrable_det_columns (fun i j t => f (σ j) t * g i t) (fun i j => hfg _ _)
  have hexpand (x : n → α) :
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
      ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℝ) * H σ x := by
    rw [Matrix.det_apply', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [H]
    have hscale := Matrix.det_mul_row (fun j => f (σ j) (x j))
      (Matrix.of fun i j => g i (x j))
    simp only [Matrix.of_apply] at hscale
    rw [hscale, mul_assoc]
  have hI (σ : Equiv.Perm n) :
      (∫ x, H σ x ∂Measure.pi (fun _ => μ)) =
      (Equiv.Perm.sign σ : ℝ) * (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).det := by
    rw [integral_det_columns _ (fun i j => hfg (σ j) i)]
    have hmat : (Matrix.of fun i j => ∫ t, f (σ j) t * g i t ∂μ) =
        (Matrix.of fun i j => ∫ t, f i t * g j t ∂μ).transpose.submatrix id σ := rfl
    rw [hmat, Matrix.det_permute', Matrix.det_transpose]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun σ _ => (hH σ).const_mul _)]
  simp_rw [integral_const_mul, hI, ← mul_assoc]
  have hsign (σ : Equiv.Perm n) : (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign σ : ℝ) = 1 := by
    norm_cast
    simp [Int.units_mul_self]
  simp_rw [hsign, one_mul]
  simp

end DeterminantIntegration

open Set MeasureTheory _root_.Matrix



theorem momentBasis_bounds (k : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 ≤ momentBasis k x ∧ momentBasis k x ≤ omega x := by
  constructor
  · exact mul_nonneg (pow_nonneg hx.1.le _) (omega_nonneg _)
  · exact mul_le_of_le_one_left (omega_nonneg _) (pow_le_one₀ hx.1.le hx.2.le)

theorem measurable_momentBasis (k : ℕ) : Measurable (momentBasis k) :=
  (measurable_id.pow_const k).mul measurable_omega

theorem integrableOn_momentBasis (k : ℕ) : IntegrableOn (momentBasis k) (Ioo 0 1) := by
  apply integrableOn_omega.mono' (measurable_momentBasis k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (momentBasis_bounds k hx).1] using
    (momentBasis_bounds k hx).2

theorem boundedCauchy_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < boundedCauchy x y ∧ boundedCauchy x y ≤ 1 := by
  constructor
  · exact div_pos hx (add_pos hx hy)
  · exact (div_le_one (add_pos hx hy)).2 (by linarith)

theorem integrableOn_boundedCauchy_basis (k : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y => boundedCauchy x y * momentBasis k y) (Ioo 0 1) := by
  have hm : Measurable (fun y => boundedCauchy x y * momentBasis k y) := by
    exact ((measurable_const.div (measurable_const.add measurable_id))).mul (measurable_momentBasis k)
  apply (integrableOn_momentBasis k).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hk := boundedCauchy_bounds hx hy.1
  have hb := momentBasis_bounds k hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk.1.le hb.1)]
  exact mul_le_of_le_one_left hb.1 hk.2

theorem transformedBasis_bounds (k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ transformedBasis k x ∧ transformedBasis k x ≤ ∫ y in Ioo (0 : ℝ) 1, omega y := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact mul_nonneg (boundedCauchy_bounds hx hy.1).1.le (momentBasis_bounds k hy).1
  · apply integral_mono_ae (integrableOn_boundedCauchy_basis k hx) integrableOn_omega
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (mul_le_of_le_one_left (momentBasis_bounds k hy).1
      (boundedCauchy_bounds hx hy.1).2).trans (momentBasis_bounds k hy).2

theorem measurable_transformedBasis (k : ℕ) : Measurable (transformedBasis k) := by
  have hm : StronglyMeasurable (Function.uncurry (fun x y => boundedCauchy x y * momentBasis k y)) := by
    exact ((measurable_fst.div (measurable_fst.add measurable_snd)).mul
      ((measurable_momentBasis k).comp measurable_snd)).stronglyMeasurable
  exact (hm.integral_prod_right (ν := volume.restrict (Ioo (0 : ℝ) 1))).measurable

theorem integrableOn_basis_transformedBasis (i j : ℕ) :
    IntegrableOn (fun x => momentBasis i x * transformedBasis j x) (Ioo 0 1) := by
  apply (integrableOn_omega.mul_const (∫ y in Ioo (0 : ℝ) 1, omega y)).mono'
    ((measurable_momentBasis i).mul (measurable_transformedBasis j)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hb := momentBasis_bounds i hx
  have ht := transformedBasis_bounds j hx.1
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 ht.1)]
  exact mul_le_mul hb.2 ht.2 ht.1 (omega_nonneg _)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CauchyMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
section DeterminantBounds
open scoped BigOperators
open Set MeasureTheory _root_.Matrix

 theorem basisDet_eq (N : ℕ) (x : Fin N → ℝ) :
    basisDet N x = (∏ i, omega (x i)) * (Matrix.vandermonde x).det := by
  have hscale := Matrix.det_mul_row (fun j => omega (x j)) (Matrix.vandermonde x).transpose
  have hm : (Matrix.of fun i j : Fin N => momentBasis i.val (x j)) =
      Matrix.of (fun i j : Fin N => omega (x j) * (Matrix.vandermonde x).transpose i j) := by
    ext i j
    exact mul_comm _ _
  unfold basisDet
  rw [hm, hscale, Matrix.det_transpose]

 theorem boundedCauchyMatrix_det (N : ℕ) (x y : Fin N → ℝ) :
    (boundedCauchyMatrix x y).det = (∏ i, x i) * (cauchyMatrix x y).det := by
  have hm : boundedCauchyMatrix x y = Matrix.of (fun i j => x i * cauchyMatrix x y i j) := by
    ext i j
    simp [boundedCauchyMatrix, boundedCauchy, cauchyMatrix, div_eq_mul_inv]
  rw [hm, Matrix.det_mul_column]

 theorem basis_cauchy_basis_eq (N : ℕ) (x y : Fin N → ℝ) :
    basisDet N x * (boundedCauchyMatrix x y).det * basisDet N y =
      ((∏ i, omega (x i)) * (∏ i, x i) * (∏ i, omega (y i))) * cauchyAlternant x y := by
  rw [basisDet_eq, basisDet_eq, boundedCauchyMatrix_det]
  unfold cauchyAlternant
  ring

 theorem basis_cauchy_basis_nonneg (N : ℕ) (x y : Fin N → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    0 ≤ basisDet N x * (boundedCauchyMatrix x y).det * basisDet N y := by
  rw [basis_cauchy_basis_eq]
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _ => omega_nonneg _))
      (Finset.prod_nonneg (fun i _ => (hx i).le))) (Finset.prod_nonneg (fun i _ => omega_nonneg _))
  · exact cauchyAlternant_nonneg x y hx hy

 theorem basis_cauchy_basis_pos {N : ℕ} {x y : Fin N → ℝ}
    (hx : x ∈ orderedDomain N) (hy : y ∈ orderedDomain N) :
    0 < basisDet N x * (boundedCauchyMatrix x y).det * basisDet N y := by
  rw [basis_cauchy_basis_eq]
  apply mul_pos
  · exact mul_pos (mul_pos (Finset.prod_pos (fun i _ => omega_pos (hx.2 i)))
      (Finset.prod_pos (fun i _ => (hx.2 i).1))) (Finset.prod_pos (fun i _ => omega_pos (hy.2 i)))
  · exact cauchyAlternant_pos x y hx.1 hy.1 (fun i => (hx.2 i).1) (fun i => (hy.2 i).1)

 theorem product_restrict_cube (N : ℕ) :
    Measure.pi (fun _ : Fin N => volume.restrict (Ioo (0 : ℝ) 1)) =
    volume.restrict (univ.pi (fun _ : Fin N => Ioo (0 : ℝ) 1)) := by
  rw [volume_pi, Measure.restrict_pi_pi]

 theorem integral_pos_on_cube {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    (hi : Integrable f (Measure.pi fun _ => volume.restrict (Ioo (0 : ℝ) 1)))
    (hn : ∀ x, (∀ i, x i ∈ Ioo 0 1) → 0 ≤ f x)
    (hp : ∀ x ∈ orderedDomain N, 0 < f x) :
    0 < ∫ x, f x ∂Measure.pi (fun _ => volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [product_restrict_cube] at hi ⊢
  have hc : MeasurableSet (univ.pi (fun _ : Fin N => Ioo (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)
  have hnn : 0 ≤ᵐ[volume.restrict (univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem hc] with x hx
    exact hn x (fun i => hx i (mem_univ _))
  apply (integral_pos_iff_support_of_nonneg_ae hnn hi).2
  have hs : orderedDomain N ⊆ Function.support f := fun x hx => (hp x hx).ne'
  have hsub : orderedDomain N ⊆ univ.pi (fun _ : Fin N => Ioo (0 : ℝ) 1) :=
    fun x hx i _ => hx.2 i
  calc
    0 < volume (orderedDomain N) :=
      (isOpen_orderedDomain N).measure_pos volume (orderedDomain_nonempty N)
    _ = (volume.restrict (univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1)) (orderedDomain N) := by
      rw [Measure.restrict_apply (isOpen_orderedDomain N).measurableSet, inter_eq_left.2 hsub]
    _ ≤ _ := measure_mono hs

 

theorem integral_cauchy_basis (N : ℕ) (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    (∫ y : Fin N → ℝ, (boundedCauchyMatrix x y).det * basisDet N y
      ∂Measure.pi (fun _ => volume.restrict (Ioo (0 : ℝ) 1))) =
      (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * transformedDet N x := by
  have h := integral_det_mul_det (fun i y => boundedCauchy (x i) y)
    (fun i : Fin N => momentBasis i.val)
    (fun i j => integrableOn_boundedCauchy_basis j.val (hx i))
  have hm : (Matrix.of fun i j : Fin N =>
      ∫ y in Ioo (0 : ℝ) 1, boundedCauchy (x i) y * momentBasis j.val y) =
      (Matrix.of fun i j : Fin N => transformedBasis i.val (x j)).transpose := rfl
  change _ = _ * (Matrix.of fun i j : Fin N => transformedBasis i.val (x j)).det
  simpa only [hm, Matrix.det_transpose, boundedCauchyMatrix, basisDet] using h

theorem integrable_cauchy_basis (N : ℕ) (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    Integrable (fun y => (boundedCauchyMatrix x y).det * basisDet N y)
      (Measure.pi fun _ => volume.restrict (Ioo (0 : ℝ) 1)) :=
  integrable_det_mul_det (fun i y => boundedCauchy (x i) y)
    (fun i : Fin N => momentBasis i.val)
    (fun i j => integrableOn_boundedCauchy_basis j.val (hx i))

theorem basis_transformed_nonneg (N : ℕ) (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    0 ≤ basisDet N x * transformedDet N x := by
  have hi : 0 ≤ ∫ y : Fin N → ℝ,
      basisDet N x * ((boundedCauchyMatrix x y).det * basisDet N y)
      ∂Measure.pi (fun _ => volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply integral_nonneg_of_ae
    rw [product_restrict_cube]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ : Fin N => measurableSet_Ioo)] with y hy
    simpa only [mul_assoc, Pi.zero_apply] using basis_cauchy_basis_nonneg N x y hx
      (fun i => (hy i (mem_univ _)).1)
  rw [integral_const_mul, integral_cauchy_basis N x hx] at hi
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by positivity
  nlinarith

theorem basis_transformed_pos {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ orderedDomain N) :
    0 < basisDet N x * transformedDet N x := by
  have hi := integral_pos_on_cube
    ((integrable_cauchy_basis N x (fun i => (hx.2 i).1)).const_mul (basisDet N x))
    (fun y hy => by
      simpa only [mul_assoc] using basis_cauchy_basis_nonneg N x y
        (fun i => (hx.2 i).1) (fun i => (hy i).1))
    (fun y hy => by simpa only [mul_assoc] using basis_cauchy_basis_pos hx hy)
  rw [integral_const_mul, integral_cauchy_basis N x (fun i => (hx.2 i).1)] at hi
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by positivity
  nlinarith

 

theorem det_momentMatrix_pos (N : ℕ) : 0 < (momentMatrix N).det := by
  have hi := integral_pos_on_cube
    (integrable_det_mul_det (fun i : Fin N => momentBasis i.val)
      (fun i : Fin N => transformedBasis i.val)
      (fun i j => integrableOn_basis_transformedBasis i.val j.val))
    (fun x hx => basis_transformed_nonneg N x (fun i => (hx i).1))
    (fun _ hx => basis_transformed_pos hx)
  rw [integral_det_mul_det (fun i : Fin N => momentBasis i.val)
    (fun i : Fin N => transformedBasis i.val)
    (fun i j => integrableOn_basis_transformedBasis i.val j.val)] at hi
  change 0 < (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * (momentMatrix N).det at hi
  exact (mul_pos_iff_of_pos_left (by positivity)).1 hi



theorem cauchyDefect_moment (N : ℕ) (D₀ : ℝ) (v : Fin N → ℝ) (j : Fin N) :
    (∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x * cauchyDefect N D₀ v x) =
      D₀ * (∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x) - (momentMatrix N *ᵥ v) j := by
  have heq : (fun x => momentBasis j.val x * cauchyDefect N D₀ v x) =
      fun x => D₀ * momentBasis j.val x -
        ∑ k : Fin N, v k * (momentBasis j.val x * transformedBasis k.val x) := by
    funext x
    simp only [cauchyDefect, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      ring
  rw [heq, integral_sub ((integrableOn_momentBasis j.val).const_mul D₀)
    (integrable_finsetSum _ fun k _ => (integrableOn_basis_transformedBasis j.val k.val).const_mul (v k)),
    integral_const_mul, integral_finsetSum]
  · simp only [integral_const_mul, Matrix.mulVec, dotProduct, momentMatrix, Matrix.of_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  · intro k _
    exact (integrableOn_basis_transformedBasis j.val k.val).const_mul (v k)

theorem cauchyMomentProblem_iff (N : ℕ) (D₀ : ℝ) (v : Fin N → ℝ) :
    CauchyMomentProblem N D₀ v ↔
      momentMatrix N *ᵥ v = fun j => D₀ * ∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x := by
  simp only [CauchyMomentProblem, cauchyDefect_moment, sub_eq_zero]
  exact ⟨fun h => funext fun j => (h j).symm, fun h j => (congrFun h j).symm⟩



theorem cauchyMomentProblem_zero {N : ℕ} {v : Fin N → ℝ}
    (hv : CauchyMomentProblem N 0 v) : v = 0 := by
  have hu : IsUnit (momentMatrix N) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_momentMatrix_pos N).ne')
  apply (Matrix.mulVec_injective_iff_isUnit.2 hu)
  rw [Matrix.mulVec_zero]
  exact ((cauchyMomentProblem_iff _ _ _).1 hv).trans (by ext j; simp)

end DeterminantBounds

 

open Set MeasureTheory Filter
open scoped Topology

theorem quarticDen_pos {r t : ℝ} (hr : 0 < r) : 0 < quarticDen r t := by
  unfold quarticDen
  positivity

theorem straightener_deriv {r t : ℝ} (ht : 0 < t) :
    HasDerivAt (straightener r) (1 + r / t ^ 2) t := by
  exact ((hasDerivAt_id t).sub ((hasDerivAt_const t r).div
    (hasDerivAt_id t) ht.ne')).congr_deriv (by simp; ring)

theorem straightener_inj {r : ℝ} (hr : 0 < r) :
    InjOn (straightener r) (Ioi 0) := by
  apply StrictMonoOn.injOn
  intro x hx y hy hxy
  dsimp [straightener]
  have hdiv : r / y < r / x := (div_lt_div_iff_of_pos_left hr hy hx).2 hxy
  linarith

theorem straightener_image {r : ℝ} (hr : 0 < r) :
    straightener r '' Ioi 0 = univ := by
  apply eq_univ_of_forall
  intro u
  let s := Real.sqrt (u ^ 2 + 4 * r)
  have hs : s ^ 2 = u ^ 2 + 4 * r := Real.sq_sqrt (by positivity)
  have hsn : 0 ≤ s := Real.sqrt_nonneg _
  have hsu : -u < s := by nlinarith
  have ht : 0 < (u + s) / 2 := by linarith
  refine ⟨(u + s) / 2, ht, ?_⟩
  dsimp [straightener]
  field_simp [show u + s ≠ 0 by linarith]
  nlinarith

theorem scaled_cauchy {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (a ^ 2 + x ^ 2)⁻¹) ∧
      (∫ x : ℝ, (a ^ 2 + x ^ 2)⁻¹) = Real.pi / a := by
  have heq : (fun x : ℝ => (a ^ 2 + x ^ 2)⁻¹) =
      fun x => (a ^ 2)⁻¹ * (1 + (x / a) ^ 2)⁻¹ := by
    funext x
    field_simp
  rw [heq]
  constructor
  · exact (integrable_inv_one_add_sq.comp_div ha.ne').const_mul _
  · rw [integral_const_mul, Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) a, integral_univ_inv_one_add_sq,
      abs_of_pos ha, smul_eq_mul]
    field_simp

theorem quartic_base_integral {r : ℝ} (hr : 0 < r) :
    IntegrableOn (quarticBase r) (Ioi 0) ∧
      (∫ t in Ioi 0, quarticBase r t) = Real.pi / Real.sqrt (2 + 2 * r) := by
  let a := Real.sqrt (2 + 2 * r)
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have ha2 : a ^ 2 = 2 + 2 * r := Real.sq_sqrt (by linarith)
  have heq : EqOn (fun t => |1 + r / t ^ 2| •
      (a ^ 2 + (straightener r t) ^ 2)⁻¹) (quarticBase r) (Ioi 0) := by
    intro t ht
    dsimp only
    rw [abs_of_pos (by positivity : 0 < 1 + r / t ^ 2), smul_eq_mul, ha2]
    dsimp [straightener, quarticBase, quarticDen]
    field_simp [show t ≠ 0 from ne_of_gt ht]
    ring_nf
    field_simp
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (straightener_deriv ht).hasDerivWithinAt)
    (straightener_inj hr) (fun u => (a ^ 2 + u ^ 2)⁻¹)
  rw [straightener_image hr, integrableOn_univ] at hi
  refine ⟨(hi.1 (scaled_cauchy ha).1).congr_fun heq measurableSet_Ioi, ?_⟩
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (straightener_deriv ht).hasDerivWithinAt)
    (straightener_inj hr) (fun u => (a ^ 2 + u ^ 2)⁻¹)
  rw [straightener_image hr, Measure.restrict_univ, (scaled_cauchy ha).2] at h
  exact (setIntegral_congr_fun measurableSet_Ioi heq).symm.trans h.symm

theorem integral_reciprocal {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) :
    (∫ t in Ioi 0, (r / t ^ 2) * g (r / t)) = ∫ t in Ioi 0, g t := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t => r / t)
      (-r / t ^ 2) (Ioi 0) t := by
    intro t ht
    exact (((hasDerivAt_const t r).div (hasDerivAt_id t) ht.ne').congr_deriv
      (by simp)).hasDerivWithinAt
  have hinj : InjOn (fun t => r / t) (Ioi 0) := by
    intro x hx y hy h
    have h' := (div_eq_div_iff hx.ne' hy.ne').1 h
    nlinarith
  have himage : (fun t => r / t) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hr hu
    · intro ht
      refine ⟨r / t, div_pos hr ht, ?_⟩
      field_simp
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g
  rw [himage] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [abs_of_neg (by exact div_neg_of_neg_of_pos (neg_neg_of_pos hr) (sq_pos_of_pos ht)),
    neg_div, neg_neg, smul_eq_mul]

theorem quartic_weighted_integral {r : ℝ} (hr : 0 < r) :
    IntegrableOn (quarticWeighted r) (Ioi 0) ∧
      (∫ t in Ioi 0, quarticWeighted r t) =
        Real.pi * (1 + r) / Real.sqrt (2 + 2 * r) := by
  have hbase := quartic_base_integral hr
  have hint : IntegrableOn (quarticWeighted r) (Ioi 0) := by
    apply (hbase.1.const_mul (2 * (1 + r))).mono'
    · apply Measurable.aestronglyMeasurable
      unfold quarticWeighted quarticDen
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hd := quarticDen_pos (t := t) hr
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold quarticWeighted; positivity)]
      unfold quarticWeighted quarticBase
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hd]
      nlinarith [sq_nonneg t]
  have heq : EqOn (fun t => quarticWeighted r t +
      (r / t ^ 2) * quarticWeighted r (r / t))
      (fun t => (2 * (1 + r)) * quarticBase r t) (Ioi 0) := by
    intro t ht
    dsimp [quarticWeighted, quarticBase, quarticDen]
    field_simp [show t ≠ 0 from ne_of_gt ht]
    ring
  have hi2 : IntegrableOn (fun t => (r / t ^ 2) * quarticWeighted r (r / t)) (Ioi 0) := by
    apply IntegrableOn.congr_fun ((hbase.1.const_mul (2 * (1 + r))).sub hint) _ measurableSet_Ioi
    intro t ht
    have h := heq ht
    dsimp only at h
    dsimp only [Pi.sub_apply]
    linarith
  have h := setIntegral_congr_fun (μ := volume) measurableSet_Ioi heq
  rw [integral_add hint hi2, integral_const_mul, integral_reciprocal hr,
    hbase.2] at h
  refine ⟨hint, ?_⟩
  linear_combination h / 2

theorem uniformDen_pos (t : ℝ) : 0 < uniformDen t := by
  unfold uniformDen
  positivity

theorem uniformizer_mem {t : ℝ} (ht : 0 < t) : uniformizer t ∈ Ioo 0 1 := by
  refine ⟨one_div_pos.2 (uniformDen_pos t), ?_⟩
  unfold uniformizer
  rw [div_lt_one (uniformDen_pos t)]
  unfold uniformDen
  have : 0 < t ^ 2 := sq_pos_of_pos ht
  nlinarith [sq_nonneg (t ^ 2)]

theorem uniformizer_deriv (t : ℝ) :
    HasDerivAt uniformizer (-8 * t * (t ^ 2 + 1) / (uniformDen t) ^ 2) t := by
  have hd : HasDerivAt uniformDen (8 * t * (t ^ 2 + 1)) t := by
    exact (((((hasDerivAt_id t).pow 4).const_mul (2 : ℝ)).add
      (((hasDerivAt_id t).pow 2).const_mul (4 : ℝ))).add_const 1).congr_deriv (by simp only [id_eq]; ring)
  have heq : uniformizer = uniformDen⁻¹ := by funext t; simp [uniformizer]
  rw [heq]
  exact (hd.inv (uniformDen_pos t).ne').congr_deriv (by ring)

theorem uniformizer_inj : InjOn uniformizer (Ioi 0) := by
  apply StrictAntiOn.injOn
  intro x hx y hy hxy
  unfold uniformizer
  apply one_div_lt_one_div_of_lt (uniformDen_pos x)
  unfold uniformDen
  gcongr <;> exact le_of_lt hx

theorem omega_uniformizer {t : ℝ} (ht : 0 < t) : omega (uniformizer t) = t / 2 := by
  have hinner : (1 + uniformizer t) / (2 * uniformizer t) = (t ^ 2 + 1) ^ 2 := by
    unfold uniformizer uniformDen
    field_simp
    ring
  unfold omega
  rw [hinner, Real.sqrt_sq (by positivity : 0 ≤ t ^ 2 + 1)]
  simp only [add_sub_cancel_right, Real.sqrt_sq ht.le]
  ring

theorem uniformizer_image : uniformizer '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact uniformizer_mem ht
  · intro hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    let w := Real.sqrt ((1 + x) / (2 * x))
    have hw2 : w ^ 2 = (1 + x) / (2 * x) := Real.sq_sqrt (by positivity)
    have hw : 1 < w := by
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2
      rw [one_pow, lt_div_iff₀ (by positivity : 0 < 2 * x)]
      linarith [hx.1, hx.2]
    let t := Real.sqrt (w - 1)
    have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
    have ht2 : t ^ 2 = w - 1 := Real.sq_sqrt (by linarith)
    refine ⟨t, ht, ?_⟩
    unfold uniformizer
    apply (div_eq_iff (uniformDen_pos t).ne').2
    have hd : uniformDen t = 2 * w ^ 2 - 1 := by
      unfold uniformDen
      calc
        _ = 2 * (t ^ 2) ^ 2 + 4 * t ^ 2 + 1 := by ring
        _ = _ := by rw [ht2]; ring
    rw [hd, hw2]
    field_simp [hx0.ne']
    ring

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

lemma top_wedge_determinant (n : ℕ) (v : Fin n → Vec n) :
    ExteriorAlgebra.ιMulti ℂ n v = (standardBasis n).det v • topWedge n := by
  have hf : ExteriorAlgebra.ιMulti ℂ n (M := Vec n) =
      ((standardBasis n).det).smulRight (topWedge n) := by
    apply (standardBasis n).ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change ExteriorAlgebra.ιMulti ℂ n ((standardBasis n) ∘ σ) =
      (((standardBasis n).det).smulRight (topWedge n)) ((standardBasis n) ∘ σ)
    simp [AlternatingMap.map_perm, topWedge, Module.Basis.det_self]
  exact DFunLike.congr_fun hf v

lemma generator_mem (n : ℕ) (i : Fin n) :
    generator n i ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ : Vec n →ₗ[ℂ] Grassmann n)) :=
  LinearMap.mem_range_self _ _

lemma twoForm_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    twoForm A ∈ ExteriorAlgebra.exteriorPower ℂ 2 (Vec n) := by
  unfold twoForm ExteriorAlgebra.exteriorPower
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  simpa only [pow_two] using Submodule.mul_mem_mul (generator_mem n i) (generator_mem n j)

lemma twoForm_pow_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    twoForm A ^ m ∈ ExteriorAlgebra.exteriorPower ℂ (2 * m) (Vec n) := by
  convert Submodule.pow_mem_pow _ (twoForm_mem A) m using 1
  all_goals try with_reducible_and_instances rfl
  exact pow_mul _ 2 m

lemma exteriorBasis_univ (n : ℕ) :
    (standardBasis n).ExteriorAlgebra Finset.univ = topWedge n := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (by simp : (Finset.univ : Finset (Fin n)).card = n)]
  unfold ExteriorAlgebra.ιMulti_family topWedge
  congr 1
  funext i
  simp only [Function.comp_apply]
  apply congrArg (standardBasis n)
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change Finset.univ.orderEmbOfFin (by simp) i = i
  exact congr_fun (Finset.orderEmbOfFin_unique (by simp)
    (fun x : Fin n => Finset.mem_univ x) (fun _ _ h => h)).symm i

@[simp] lemma topCoord_topWedge (n : ℕ) : topCoord n (topWedge n) = 1 := by
  rw [← exteriorBasis_univ]
  simp [topCoord, Module.Basis.coord_apply]

lemma topCoord_wedge (n : ℕ) (v : Fin n → Vec n) :
    topCoord n (ExteriorAlgebra.ιMulti ℂ n v) = (standardBasis n).det v := by
  rw [top_wedge_determinant, map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

lemma homogeneous_eq_coord_topWedge (n : ℕ) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    x = topCoord n x • topWedge n := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    rw [topCoord_wedge, top_wedge_determinant]
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add, add_smul, ← ihx, ← ihy]
  | smul r x hx ih =>
    rw [map_smul, smul_eq_mul, ← smul_smul, ← ih]

lemma topCoord_map (n : ℕ) (f : Vec n →ₗ[ℂ] Vec n) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord n (ExteriorAlgebra.map f x) = f.det * topCoord n x := by
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, map_smul]
  unfold topWedge
  rw [ExteriorAlgebra.map_apply_ιMulti, topCoord_wedge]
  have hd : (standardBasis n).det (f ∘ standardBasis n) = f.det := by
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hd, smul_eq_mul, mul_comm]

lemma generator_anticomm (n : ℕ) (i j : Fin n) :
    generator n i * generator n j = -(generator n j * generator n i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

lemma sum_symmetric_offdiag {n : ℕ} {E : Type*} [AddCommGroup E]
    (F : Fin n → Fin n → E) (hF : ∀ i j, F i j = F j i)
    (hzero : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 • (∑ i, ∑ j ∈ Finset.Ioi i, F i j) := by
  have hij (i j : Fin n) : F i j =
      (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hzero]
    · simp [h, not_lt_of_gt h, hF i j]
  have hsum (i : Fin n) : (∑ j, if i < j then F i j else 0) =
      ∑ j ∈ Finset.Ioi i, F i j := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  calc
    ∑ i, ∑ j, F i j =
        (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ i, ∑ j, if j < i then F j i else 0) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hij i j
    _ = (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ j, ∑ i, if j < i then F j i else 0) := by
      rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
    _ = 2 • (∑ i, ∑ j ∈ Finset.Ioi i, F i j) := by
      simp only [hsum, two_nsmul]

lemma twoForm_full {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    twoForm A = (1 / 2 : ℂ) • ∑ i, ∑ j, A i j • (generator n i * generator n j) := by
  have hs := sum_symmetric_offdiag
    (fun i j => A i j • (generator n i * generator n j))
    (fun i j => by rw [hA i j, generator_anticomm n j i, neg_smul, smul_neg, neg_neg])
    (fun i => by simp [generator])
  rw [hs]
  change twoForm A = (1 / 2 : ℂ) • (2 • twoForm A)
  rw [← Nat.cast_smul_eq_nsmul ℂ 2, smul_smul]
  norm_num

lemma permMap_det (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permMap n σ).det = (Equiv.Perm.sign σ : ℂ) := by
  have he : permMap n σ ∘ standardBasis n = standardBasis n ∘ σ := by
    funext i
    exact permMap_basis n σ i
  have hd := Module.Basis.det_comp (standardBasis n) (permMap n σ) (standardBasis n)
  rw [he, AlternatingMap.map_perm, Module.Basis.det_self, mul_one] at hd
  simpa [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul] using hd.symm

lemma twoForm_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (σ : Equiv.Perm (Fin n)) :
    ExteriorAlgebra.map (permMap n σ) (twoForm A) =
      twoForm (fun i j => A (σ.symm i) (σ.symm j)) := by
  rw [twoForm_full A hA, twoForm_full _ (fun i j => hA _ _)]
  simp only [map_smul, map_sum, map_mul, permMap_generator]
  congr 1
  apply Fintype.sum_equiv σ
  intro i
  simp only [Equiv.symm_apply_apply]
  apply Fintype.sum_equiv σ
  intro j
  simp

lemma pfaffian_perm (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (σ : Equiv.Perm (Fin n)) :
    pfaffian n (fun i j => A (σ.symm i) (σ.symm j)) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian n A := by
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) :=
    by simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  change topCoord n (twoForm _ ^ (n / 2)) / _ =
    (Equiv.Perm.sign σ : ℂ) * (topCoord n (twoForm A ^ (n / 2)) / _)
  rw [← twoForm_perm A hA σ, ← map_pow, topCoord_map n _ _ hhom, permMap_det]
  ring

lemma pfaffian_duplicate (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (i j : Fin n) (hij : i ≠ j)
    (hrow : ∀ k, A i k = A j k) : pfaffian n A = 0 := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  have hs_left (x y : Fin n) : A (σ x) y = A x y := by
    by_cases hxi : x = i
    · subst x
      simpa [σ] using (hrow y).symm
    by_cases hxj : x = j
    · subst x
      simpa [σ] using hrow y
    simp [σ, Equiv.swap_apply_of_ne_of_ne hxi hxj]
  have hs_right (x y : Fin n) : A x (σ y) = A x y := by
    rw [hA, hs_left, hA, neg_neg]
  have he : (fun x y => A (σ.symm x) (σ.symm y)) = A := by
    funext x y
    change A (Equiv.swap i j x) (Equiv.swap i j y) = A x y
    rw [show Equiv.swap i j = σ from rfl, hs_left, hs_right]
  have hp := pfaffian_perm n hn A hA σ
  rw [he] at hp
  have hsign : (Equiv.Perm.sign σ : ℂ) = -1 := by
    simp [σ, Equiv.Perm.sign_swap hij]
  rw [hsign, neg_one_mul] at hp
  linear_combination hp / 2

lemma wedge_anticomm {n : ℕ} (u v : Vec n) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v =
      -(ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ u) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

lemma wedge_commutes {n : ℕ} (u v : Vec n) (x : Grassmann n) :
    Commute (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact (Algebra.commutes r _).symm
  | ι w =>
    change (_ * _) * _ = _ * (_ * _)
    calc
      _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) :=
        mul_assoc _ _ _
      _ = -(ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
        rw [wedge_anticomm v w, mul_neg]
      _ = -((ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ v) := by
        rw [mul_assoc]
      _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ v := by
        rw [wedge_anticomm u w, neg_mul, neg_neg]
      _ = _ := mul_assoc _ _ _
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

lemma wedge_sq_zero {n : ℕ} (u v : Vec n) :
    (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v) ^ 2 = 0 := by
  rw [pow_two, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι ℂ v), wedge_anticomm v u,
    neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero]
  simp

lemma generator_expansion (n : ℕ) (u : Vec n) :
    (∑ i, u i • generator n i) = ExteriorAlgebra.ι ℂ u := by
  have h := congrArg (ExteriorAlgebra.ι ℂ) ((standardBasis n).sum_repr u)
  simpa [standardBasis, generator, map_sum, map_smul] using h

lemma pow_add_sq_zero {E : Type*} [Ring E] [Algebra ℂ E] (a b : E)
    (hab : Commute a b) (hb : b ^ 2 = 0) (m : ℕ) :
    (a + b) ^ (m + 1) = a ^ (m + 1) + (m + 1 : ℂ) • (a ^ m * b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (a + b), ih, add_mul, mul_add, mul_add,
      smul_mul_assoc, smul_mul_assoc]
    have hba : a ^ m * b * a = a ^ (m + 1) * b := by
      rw [mul_assoc, hab.eq.symm, ← mul_assoc, ← pow_succ]
    have hbb : a ^ m * b * b = 0 := by rw [mul_assoc, ← pow_two, hb, mul_zero]
    rw [hba, hbb, smul_zero, add_zero, ← pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    module

lemma high_degree_zero {n k : ℕ} (hk : n < k) (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ k (Vec n)) : x = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    apply AlternatingMap.map_linearDependent
    intro hv
    have h := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi] at h
    omega
  | zero => rfl
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul r x hx ih => simp [ih]

lemma border_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (i j : Fin (n + 1)) :
    border A u j i = -border A u i j := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [border_last_last, border_last_old, border_old_last, border_old_old,
      neg_zero, neg_neg]
  exact hA _ _

lemma twoForm_border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    twoForm (border A u) = ExteriorAlgebra.map (embedMap n) (twoForm A) +
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
  rw [twoForm_full _ (border_skew A hA u), twoForm_full A hA]
  simp only [map_smul, map_sum, map_mul, embedMap_generator]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc, border_old_old, border_old_last,
    border_last_old, border_last_last, zero_smul, add_zero, Finset.sum_add_distrib]
  have hu : (∑ i : Fin n, u i • generator (n + 1) i.castSucc) =
      ExteriorAlgebra.ι ℂ (embedMap n u) := by
    have h := congrArg (ExteriorAlgebra.map (embedMap n)) (generator_expansion n u)
    simpa using h
  have hp : (∑ i : Fin n, u i • (generator (n + 1) i.castSucc * generator (n + 1) (Fin.last n))) =
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
    rw [← hu, Finset.sum_mul]
    simp only [smul_mul_assoc]
  have hm : (∑ i : Fin n, -u i • (generator (n + 1) (Fin.last n) * generator (n + 1) i.castSucc)) =
      ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n) := by
    rw [← hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [generator_anticomm (n + 1) (Fin.last n), neg_smul, smul_neg, neg_neg]
  rw [hp, hm]
  module

lemma topWedge_snoc (n : ℕ) :
    topWedge (n + 1) = ExteriorAlgebra.map (embedMap n) (topWedge n) *
      generator (n + 1) (Fin.last n) := by
  unfold topWedge
  rw [ExteriorAlgebra.map_apply_ιMulti]
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Function.comp_apply, embedMap_basis, generator]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial
lemma pfaffian_border {n : ℕ} (hn : Odd n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    pfaffian (n + 1) (border A u) = borderLinear A u := by
  have hm : (n + 1) / 2 = n / 2 + 1 := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hz : twoForm A ^ (n / 2 + 1) = 0 :=
    high_degree_zero (by omega) _ (twoForm_pow_mem A (n / 2 + 1))
  have hcomm : Commute (ExteriorAlgebra.map (embedMap n) (twoForm A))
      (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n)) :=
    (wedge_commutes _ _ _).symm
  unfold pfaffian
  change topCoord (n + 1) _ / _ = _
  rw [twoForm_border A hA, hm, pow_add_sq_zero _ _ hcomm (wedge_sq_zero _ _) (n / 2),
    ← map_pow, hz, map_zero, zero_add, map_smul, smul_eq_mul]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm0 : (↑(n / 2) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n / 2)
  rw [mul_div_mul_left _ _ hm0]
  rfl

lemma topCoord_embed_twice {n : ℕ} (x : Grassmann n)
    (hx : x ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n)) :
    topCoord (n + 2)
      (ExteriorAlgebra.map (embedMap (n + 1)) (ExteriorAlgebra.map (embedMap n) x) *
        (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1)))) =
      topCoord n x := by
  have ht : ExteriorAlgebra.map (embedMap (n + 1))
        (ExteriorAlgebra.map (embedMap n) (topWedge n)) *
        (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1))) =
      topWedge (n + 2) := by
    rw [← embedMap_generator (n + 1) (Fin.last n), ← mul_assoc, ← map_mul,
      ← topWedge_snoc, ← topWedge_snoc]
  conv_lhs => rw [homogeneous_eq_coord_topWedge n x hx]
  rw [map_smul, map_smul, smul_mul_assoc, ht, map_smul, topCoord_topWedge, smul_eq_mul, mul_one]

lemma pfaffian_block_pair {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian (n + 2) (border (border A 0) (standardBasis (n + 1) (Fin.last n))) =
      pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have hm : (n + 1) / 2 = n / 2 := by obtain ⟨k, hk⟩ := hn; omega
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  rw [pfaffian_border hodd _ (border_skew A hA 0)]
  change topCoord (n + 2) _ / _ = _
  rw [twoForm_border A hA 0]
  simp only [map_zero, zero_mul, add_zero, embedMap_basis, hm, ← map_pow]
  change topCoord (n + 2)
    (ExteriorAlgebra.map (embedMap (n + 1)) (ExteriorAlgebra.map (embedMap n) (twoForm A ^ (n / 2))) *
      (generator (n + 2) (Fin.last n).castSucc * generator (n + 2) (Fin.last (n + 1)))) / _ = _
  rw [topCoord_embed_twice _ hhom]
  rfl

lemma borderLinear_column {n : ℕ} (hn : Odd n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (j : Fin n) :
    borderLinear A (fun i => A i j) = 0 := by
  rw [← pfaffian_border hn A hA]
  apply pfaffian_duplicate (n + 1) hn.add_one _ (border_skew A hA _)
    j.castSucc (Fin.last n) (Fin.castSucc_ne_last j)
  intro k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp only [border_old_last, border_last_last]
    have hj := hA j j
    linear_combination hj / 2
  · simp only [border_old_old, border_last_old]
    exact hA k j

lemma basis_last (n : ℕ) : standardBasis (n + 1) (Fin.last n) = Fin.snoc (fun _ => 0) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [standardBasis, Pi.basisFun_apply]

lemma pfaffian_zero_row (n : ℕ) (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (i : Fin n) (hrow : ∀ j, A i j = 0) :
    pfaffian n A = 0 := by
  let f : Vec n →ₗ[ℂ] Vec n :=
    (standardBasis n).constr ℂ (fun j => if j = i then 0 else standardBasis n j)
  have hf (j : Fin n) : f (standardBasis n j) = if j = i then 0 else standardBasis n j := by
    exact (standardBasis n).constr_basis ℂ _ j
  have hdet : f.det = 0 := by
    have hd := Module.Basis.det_comp (standardBasis n) f (standardBasis n)
    rw [Module.Basis.det_self, mul_one] at hd
    rw [← hd]
    exact (standardBasis n).det.map_coord_zero i (by simp [hf])
  have hcol (j : Fin n) : A j i = 0 := by rw [hA, hrow, neg_zero]
  have hform : ExteriorAlgebra.map f (twoForm A) = twoForm A := by
    unfold twoForm
    simp only [map_sum, map_smul, map_mul, generator, ExteriorAlgebra.map_apply_ι, hf]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hji : j = i
    · subst j
      simp [hrow]
    by_cases hki : k = i
    · subst k
      simp [hcol]
    simp [hji, hki]
  have hdeg : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hn)
  have hhom : twoForm A ^ (n / 2) ∈ ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hdeg] using twoForm_pow_mem A (n / 2)
  have htop := topCoord_map n f (twoForm A ^ (n / 2)) hhom
  rw [map_pow, hform, hdet, zero_mul] at htop
  change topCoord n (twoForm A ^ (n / 2)) / _ = 0
  rw [htop, zero_div]

lemma pfaffian_block_extra {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) (t : ℂ) :
    pfaffian (n + 2) (border (border A 0) (Fin.snoc u t)) = t * pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have he : Fin.snoc u t = Fin.snoc u 0 + t • standardBasis (n + 1) (Fin.last n) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [basis_last]
  have hz : borderLinear (border A 0) (Fin.snoc u 0) = 0 := by
    rw [← pfaffian_border hodd _ (border_skew A hA 0)]
    apply pfaffian_zero_row (n + 2) (hodd.add_one) _
      (border_skew _ (border_skew A hA 0) _) (Fin.last n).castSucc
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [pfaffian_border hodd _ (border_skew A hA 0), he, map_add, map_smul, hz, zero_add]
  rw [← pfaffian_border hodd _ (border_skew A hA 0), pfaffian_block_pair hn A hA, smul_eq_mul]

lemma border_swap_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u v : Vec n) (t : ℂ) :
    (fun i j => border (border A u) (Fin.snoc v t) ((lastSwap n).symm i) ((lastSwap n).symm j)) =
      border (border A v) (Fin.snoc u (-t)) := by
  funext i j
  simp only [lastSwap_symm]
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  · refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  · refine Fin.lastCases ?_ (fun i => ?_) i <;>
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma pfaffian_border_swap {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u v : Vec n) (t : ℂ) :
    pfaffian (n + 2) (border (border A v) (Fin.snoc u (-t))) =
      -pfaffian (n + 2) (border (border A u) (Fin.snoc v t)) := by
  have hp := pfaffian_perm (n + 2) (hn.add (by decide))
    (border (border A u) (Fin.snoc v t)) (border_skew _ (border_skew A hA u) _) (lastSwap n)
  rw [border_swap_matrix] at hp
  simpa [lastSwap, Equiv.Perm.sign_swap (Fin.castSucc_ne_last (Fin.last n))] using hp

lemma pfaffian_aug_pair {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (u : Vec n) :
    pfaffian (n + 2) (border (border A u) (standardBasis (n + 1) (Fin.last n))) =
      pfaffian n A := by
  rw [basis_last]
  have hp := pfaffian_border_swap hn A hA u 0 1
  rw [pfaffian_block_extra hn A hA, neg_one_mul] at hp
  exact neg_injective hp.symm

lemma borderLinear_aug_ones {n : ℕ} (hn : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    borderLinear (border A (fun _ => 1)) (fun _ => -1) = -pfaffian n A := by
  have hodd : Odd (n + 1) := hn.add_one
  have hz := borderLinear_column hodd (border A (fun _ => 1))
    (border_skew A hA _) (Fin.last n)
  have he : (fun _ : Fin (n + 1) => (-1 : ℂ)) =
      -(fun i => border A (fun _ => 1) i (Fin.last n)) - standardBasis (n + 1) (Fin.last n) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [basis_last]
  rw [he, map_sub, map_neg, hz, neg_zero, zero_sub]
  congr 1
  rw [← pfaffian_border hodd _ (border_skew A hA _), pfaffian_aug_pair hn A hA]

lemma D_symm (a b : ℂ) : D b a = D a b := by unfold D; ring
lemma kernel_skew (a b : ℂ) : kernel b a = -kernel a b := by
  unfold kernel
  rw [D_symm]
  ring

lemma kernelMatrix_skew (N : ℕ) (a : Fin N → ℂ) (i j : Fin N) :
    kernelMatrix N a j i = -kernelMatrix N a i j := kernel_skew _ _

lemma kernelMatrix_snoc (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    kernelMatrix (N + 1) (Fin.snoc a z) =
      border (kernelMatrix N a) (fun i => kernel (a i) z) := by
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [kernelMatrix]
  exact kernel_skew _ _

lemma augmentedKernel_skew (N : ℕ) (a : Fin N → ℂ) (i j : Fin (pfSize N)) :
    augmentedKernel N a j i = -augmentedKernel N a i j := by
  by_cases hi : i.val < N <;> by_cases hj : j.val < N <;>
    simp only [augmentedKernel, hi, hj, dite_true, dite_false, ite_true, ite_false, neg_neg, neg_zero]
  exact kernel_skew _ _

lemma pfaffian_cast {m n : ℕ} (h : m = n) (A : Matrix (Fin m) (Fin m) ℂ) :
    pfaffian m A = pfaffian n (fun i j => A (Fin.cast h.symm i) (Fin.cast h.symm j)) := by
  subst n
  rfl

lemma actualPf_even {N : ℕ} (hN : Even N) (a : Fin N → ℂ) :
    actualPf N a = pfaffian N (kernelMatrix N a) := by
  have hs : pfSize N = N := by obtain ⟨k, hk⟩ := hN; unfold pfSize; omega
  unfold actualPf
  rw [pfaffian_cast hs]
  congr 1
  funext i j
  simp [augmentedKernel, kernelMatrix, i.isLt, j.isLt]

lemma actualPf_odd {N : ℕ} (hN : Odd N) (a : Fin N → ℂ) :
    actualPf N a = pfaffian (N + 1) (border (kernelMatrix N a) (fun _ => 1)) := by
  have hs : pfSize N = N + 1 := by obtain ⟨k, hk⟩ := hN; unfold pfSize; omega
  unfold actualPf
  rw [pfaffian_cast hs]
  congr 1
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [augmentedKernel, kernelMatrix]

lemma actualPf_duplicate {N : ℕ} (a : Fin N → ℂ) (i j : Fin N)
    (hij : i ≠ j) (ha : a i = a j) : actualPf N a = 0 := by
  have hsize : N ≤ pfSize N := by unfold pfSize; omega
  let i' : Fin (pfSize N) := ⟨i.val, lt_of_lt_of_le i.isLt hsize⟩
  let j' : Fin (pfSize N) := ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩
  apply pfaffian_duplicate (pfSize N) (even_two_mul _) _ (augmentedKernel_skew N a) i' j'
  · intro h
    apply hij
    apply Fin.ext
    exact congrArg (fun k : Fin (pfSize N) => k.val) h
  · intro k
    simp only [augmentedKernel, i', j', i.isLt, j.isLt, dite_true]
    by_cases hk : k.val < N <;> simp [hk, ha]

lemma incrementLinear_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    incrementLinear N a (Fin.snoc (fun i => kernel (a i) z) 1) =
      actualPf (N + 1) (Fin.snoc a z) := by
  by_cases hodd : Odd N
  · rw [incrementLinear, ite_eq_left hodd, LinearMap.comp_apply, restrictMap_snoc,
      actualPf_even hodd.add_one, kernelMatrix_snoc,
      pfaffian_border hodd _ (kernelMatrix_skew N a)]
  · have heven : Even N := Nat.not_odd_iff_even.mp hodd
    rw [incrementLinear, ite_eq_right hodd, LinearMap.neg_apply, LinearMap.comp_apply, flipLastMap_snoc,
      actualPf_odd heven.add_one, kernelMatrix_snoc]
    have hone : (fun _ : Fin (N + 1) => (1 : ℂ)) = Fin.snoc (fun _ => 1) 1 := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [hone, ← pfaffian_border heven.add_one _ (border_skew _ (kernelMatrix_skew N a) _),
      pfaffian_border_swap heven _ (kernelMatrix_skew N a), neg_neg]

lemma incrementLinear_leading (N : ℕ) (a : Fin N → ℂ) :
    incrementLinear N a (Fin.snoc (fun _ => -1) 1) = (-1 : ℂ) ^ N * actualPf N a := by
  by_cases hodd : Odd N
  · rw [incrementLinear, ite_eq_left hodd, LinearMap.comp_apply, restrictMap_snoc,
      actualPf_odd hodd, pfaffian_border hodd _ (kernelMatrix_skew N a), hodd.neg_one_pow]
    have he : (fun _ : Fin N => (-1 : ℂ)) = -(fun _ => 1) := rfl
    rw [he, map_neg, neg_one_mul]
  · have heven : Even N := Nat.not_odd_iff_even.mp hodd
    rw [incrementLinear, ite_eq_right hodd, LinearMap.neg_apply, LinearMap.comp_apply, flipLastMap_snoc,
      heven.neg_one_pow, one_mul, actualPf_even heven]
    have he : (Fin.snoc (fun _ : Fin N => (-1 : ℂ)) (-1 : ℂ) : Vec (N + 1)) =
        (fun _ : Fin (N + 1) => (-1 : ℂ)) := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [he, borderLinear_aug_ones heven _ (kernelMatrix_skew N a), neg_neg]

lemma linear_basis_sum {n : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (v : Vec n) :
    (∑ i, L (standardBasis n i) * v i) = L v := by
  have h := congrArg L ((standardBasis n).sum_repr v)
  simpa [standardBasis, Pi.basisFun_repr, map_sum, map_smul, smul_eq_mul, mul_comm] using h

lemma polyLift_eval {n : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (f : Fin n → Polynomial ℂ) (z : ℂ) :
    (polyLift L f).eval z = L (fun i => (f i).eval z) := by
  simp only [polyLift, eval_finsetSum, eval_mul, eval_C]
  exact linear_basis_sum L _

lemma polyLift_coeff {n : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (f : Fin n → Polynomial ℂ) (k : ℕ) :
    (polyLift L f).coeff k = L (fun i => (f i).coeff k) := by
  simp only [polyLift, finsetSum_coeff, coeff_C_mul]
  exact linear_basis_sum L _

lemma polyLift_degree {n k : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (f : Fin n → Polynomial ℂ)
    (hf : ∀ i, (f i).natDegree ≤ k) : (polyLift L f).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans (hf i)

lemma Dpoly_degree (a : ℂ) : (Dpoly a).natDegree ≤ 2 := by unfold Dpoly; compute_degree!
lemma pairNumerator_degree (a : ℂ) : (pairNumerator a).natDegree ≤ 2 := by
  unfold pairNumerator
  compute_degree!

lemma denominatorPoly_degree (N : ℕ) (a : Fin N → ℂ) :
    (denominatorPoly N a).natDegree ≤ 2 * N := by
  apply (natDegree_prod_le _ _).trans
  calc ∑ i : Fin N, (Dpoly (a i)).natDegree ≤ ∑ _i : Fin N, 2 :=
        Finset.sum_le_sum (fun i _ => Dpoly_degree (a i))
    _ = 2 * N := by simp [mul_comm]

@[simp] lemma denominatorPoly_coeff (N : ℕ) (a : Fin N → ℂ) :
    (denominatorPoly N a).coeff (2 * N) = 1 := by
  have h := coeff_prod_of_natDegree_le (s := Finset.univ) (fun i => Dpoly (a i)) 2
    (fun i _ => Dpoly_degree (a i))
  simpa [denominatorPoly, mul_comm] using h

lemma deletedDenominator_degree (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    (deletedDenominator N a i).natDegree ≤ 2 * (N - 1) := by
  apply (natDegree_prod_le _ _).trans
  calc ∑ j ∈ Finset.univ.erase i, (Dpoly (a j)).natDegree ≤ ∑ _j ∈ Finset.univ.erase i, 2 :=
        Finset.sum_le_sum (fun j _ => Dpoly_degree (a j))
    _ = 2 * (N - 1) := by simp [mul_comm]

@[simp] lemma deletedDenominator_coeff (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    (deletedDenominator N a i).coeff (2 * (N - 1)) = 1 := by
  have h := coeff_prod_of_natDegree_le (s := Finset.univ.erase i) (fun j => Dpoly (a j)) 2
    (fun j _ => Dpoly_degree (a j))
  simpa [deletedDenominator, mul_comm] using h

lemma kernelNumerator_degree (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    (kernelNumerator N a i).natDegree ≤ 2 * N := by
  have h := natDegree_mul_le.trans (add_le_add (pairNumerator_degree (a i))
    (deletedDenominator_degree N a i))
  have hi := i.isLt
  have hn : 2 + 2 * (N - 1) = 2 * N := by omega
  simpa [kernelNumerator, hn] using h

@[simp] lemma kernelNumerator_coeff (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    (kernelNumerator N a i).coeff (2 * N) = -1 := by
  have h := coeff_mul_add_eq_of_natDegree_le (pairNumerator_degree (a i))
    (deletedDenominator_degree N a i)
  have hi := i.isLt
  have hn : 2 + 2 * (N - 1) = 2 * N := by omega
  simpa [kernelNumerator, hn] using h

lemma clearedPf_degree (N : ℕ) (a : Fin N → ℂ) : (clearedPf N a).natDegree ≤ 2 * N := by
  apply polyLift_degree
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using denominatorPoly_degree N a
  · simpa using kernelNumerator_degree N a j

lemma clearedPf_coeff (N : ℕ) (a : Fin N → ℂ) :
    (clearedPf N a).coeff (2 * N) = (-1 : ℂ) ^ N * actualPf N a := by
  rw [clearedPf, polyLift_coeff]
  convert incrementLinear_leading N a using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma denominatorPoly_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    (denominatorPoly N a).eval z = ∏ i, D (a i) z := by simp only [denominatorPoly, eval_prod, Dpoly_eval]

lemma deletedDenominator_mul (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    deletedDenominator N a i * Dpoly (a i) = denominatorPoly N a := by
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ i)

lemma kernelNumerator_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ)
    (hz : ∀ i, D (a i) z ≠ 0) (i : Fin N) :
    (kernelNumerator N a i).eval z = (denominatorPoly N a).eval z * kernel (a i) z := by
  have h := congrArg (Polynomial.eval z) (deletedDenominator_mul N a i)
  simp only [eval_mul, Dpoly_eval] at h
  simp only [kernelNumerator, pairNumerator, eval_mul, eval_sub, eval_add, eval_C, eval_X, kernel]
  rw [← h]
  field_simp [hz i]
  ring

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial
lemma clearedPf_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ)
    (hz : ∀ i, D (a i) z ≠ 0) :
    (clearedPf N a).eval z = (denominatorPoly N a).eval z * actualPf (N + 1) (Fin.snoc a z) := by
  rw [clearedPf, polyLift_eval]
  have he : (fun i : Fin (N + 1) => Polynomial.eval z ((Fin.snoc (kernelNumerator N a) (denominatorPoly N a) : Fin (N + 1) → Polynomial ℂ) i)) =
      (denominatorPoly N a).eval z • Fin.snoc (fun i => kernel (a i) z) 1 := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [kernelNumerator_eval N a z hz]
  rw [he, map_smul, incrementLinear_eval, smul_eq_mul]

lemma clearedPf_root (N : ℕ) (a : Fin N → ℂ)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0) (i : Fin N) :
    (clearedPf N a).eval (a i) = 0 := by
  by_cases hii : D (a i) (a i) = 0
  · have hH : (denominatorPoly N a).eval (a i) = 0 := by
      rw [denominatorPoly_eval]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hii
    have hK : ∀ j, (kernelNumerator N a j).eval (a i) = 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        simp [kernelNumerator, pairNumerator]
      · have hj : (deletedDenominator N a j).eval (a i) = 0 := by
          rw [deletedDenominator, eval_prod]
          apply Finset.prod_eq_zero (i := i)
          · simp [Ne.symm hji]
          · simpa using hii
        simp [kernelNumerator, hj]
    rw [clearedPf, polyLift_eval]
    convert (incrementLinear N a).map_zero using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [hH, hK]
  · have hz : ∀ j, D (a j) (a i) ≠ 0 := by
      intro j
      by_cases hji : j = i
      · simpa [hji] using hii
      · exact hD j i hji
    rw [clearedPf_eval N a (a i) hz]
    have hzero := actualPf_duplicate (Fin.snoc a (a i)) i.castSucc (Fin.last N)
      (by simp) (by simp)
    rw [hzero, mul_zero]

lemma nodalPoly_monic (N : ℕ) (a : Fin N → ℂ) : (nodalPoly N a).Monic :=
  monic_prod_X_sub_C a Finset.univ

lemma nodalPoly_degree (N : ℕ) (a : Fin N → ℂ) : (nodalPoly N a).natDegree = N := by
  rw [nodalPoly, natDegree_prod _ _ (fun i _ => (monic_X_sub_C (a i)).ne_zero)]
  simp

lemma nodalPoly_dvd (N : ℕ) (a : Fin N → ℂ) (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0) : nodalPoly N a ∣ clearedPf N a := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact pairwise_coprime_X_sub_C ha hij
  · intro i hi
    exact dvd_iff_isRoot.mpr (clearedPf_root N a hD i)

lemma normalized_cleared_monic (N : ℕ) (a : Fin N → ℂ) (hpf : actualPf N a ≠ 0) :
    let Q := C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a
    Q.Monic ∧ Q.natDegree = 2 * N := by
  dsimp only
  have hne : (-1 : ℂ) ^ N * actualPf N a ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hpf
  have hd : (C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a).natDegree ≤ 2 * N :=
    (natDegree_C_mul_le _ _).trans (clearedPf_degree N a)
  have hc : (C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a).coeff (2 * N) = 1 := by
    rw [coeff_C_mul, clearedPf_coeff, inv_mul_cancel₀ hne]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hd hc,
    natDegree_eq_of_le_of_coeff_ne_zero hd (by rw [hc]; exact one_ne_zero)⟩

lemma p_eq (N : ℕ) (a : Fin N → ℂ) : p N a = prefactor N a * actualPf N a := rfl

lemma prod_Ioi_castSucc {n : ℕ} (f : Fin (n + 1) → ℂ) (i : Fin n) :
    (∏ j ∈ Finset.Ioi i.castSucc, f j) = (∏ j ∈ Finset.Ioi i, f j.castSucc) * f (Fin.last n) := by
  have h1 : Finset.Ioi i.castSucc = Finset.univ.filter (fun j => i.castSucc < j) := by ext; simp
  have h2 : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext; simp
  rw [h1, h2, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp

lemma prod_Ioi_last {n : ℕ} (f : Fin (n + 1) → ℂ) :
    (∏ j ∈ Finset.Ioi (Fin.last n), f j) = 1 := by
  apply Finset.prod_eq_one
  intro j hj
  have h := Finset.mem_Ioi.mp hj
  have hj := j.isLt
  change n < j.val at h
  omega

lemma prefactor_snoc (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    prefactor (N + 1) (Fin.snoc a z) = prefactor N a * ∏ i, D (a i) z / (a i - z) := by
  unfold prefactor
  rw [Fin.prod_univ_castSucc, prod_Ioi_last, mul_one]
  simp_rw [prod_Ioi_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  exact Finset.prod_mul_distrib

lemma nodalPoly_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    (nodalPoly N a).eval z = ∏ i, (z - a i) := by
  simp only [nodalPoly, eval_prod, eval_sub, eval_X, eval_C]

lemma difference_prod (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    (∏ i, (a i - z)) = (-1 : ℂ) ^ N * (nodalPoly N a).eval z := by
  rw [nodalPoly_eval]
  calc (∏ i, (a i - z)) = ∏ i, ((-1 : ℂ) * (z - a i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
    _ = (-1 : ℂ) ^ N * ∏ i, (z - a i) := by rw [Finset.prod_mul_distrib]; simp

lemma generic_arch_quotient_factor (N : ℕ) (a : Fin N → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0)
    (hp : p N a ≠ 0) :
    ∃ g : Polynomial ℂ, g.Monic ∧ g.natDegree = N ∧
      nodalPoly N a * g = C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a ∧
      ∀ z : ℂ, (∀ i, z ≠ a i ∧ D (a i) z ≠ 0) →
        g.eval z = p (N + 1) (Fin.snoc a z) / p N a := by
  have hpre : prefactor N a ≠ 0 := left_ne_zero_of_mul (p_eq N a ▸ hp)
  have hpf : actualPf N a ≠ 0 := right_ne_zero_of_mul (p_eq N a ▸ hp)
  let Q := C (((-1 : ℂ) ^ N * actualPf N a)⁻¹) * clearedPf N a
  have hQ := normalized_cleared_monic N a hpf
  change Q.Monic ∧ Q.natDegree = 2 * N at hQ
  have hd : nodalPoly N a ∣ Q := dvd_mul_of_dvd_right (nodalPoly_dvd N a ha hD) _
  obtain ⟨g, hg⟩ := hd
  have hgm : g.Monic := (nodalPoly_monic N a).of_mul_monic_left (hg ▸ hQ.1)
  have hgn : g.natDegree = N := by
    have h := hQ.2
    rw [hg, (nodalPoly_monic N a).natDegree_mul hgm, nodalPoly_degree] at h
    omega
  refine ⟨g, hgm, hgn, hg.symm, ?_⟩
  intro z hz
  have hn : (nodalPoly N a).eval z ≠ 0 := by
    rw [nodalPoly_eval]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hz i).1)
  have hs : (-1 : ℂ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  have he := congrArg (Polynomial.eval z) hg
  dsimp only [Q] at he
  rw [eval_mul, eval_C, clearedPf_eval N a z (fun i => (hz i).2), eval_mul] at he
  rw [p_eq, prefactor_snoc, p_eq, Finset.prod_div_distrib, difference_prod,
    ← denominatorPoly_eval]
  apply (eq_div_iff (mul_ne_zero hpre hpf)).mpr
  have he' : ((-1 : ℂ) ^ N * actualPf N a)⁻¹ *
      ((denominatorPoly N a).eval z * actualPf (N + 1) (Fin.snoc a z)) =
      (nodalPoly N a).eval z * g.eval z := he
  field_simp [hs, hpf] at he'
  field_simp [hn, hs]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using he'.symm


end
noncomputable section
open Polynomial
open scoped BigOperators


lemma constant_relations : d ^ 2 = (1 / 2 : ℂ) ∧ flatC * rho = (1 / 2 : ℂ) ∧
    rho * (1 + 2 * d) = 2 * flatC * d := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 := Real.sq_sqrt (by positivity)
  have ht0 : Real.sqrt (2 + Real.sqrt 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hd : Real.cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
    rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have h1 : (Real.cos (2 * (Real.pi / 8))) ^ 2 = (1 / 2 : ℝ) := by rw [hd]; nlinarith
  have h2 : Real.cos (Real.pi / 8) * (1 / Real.sqrt (2 + Real.sqrt 2)) = (1 / 2 : ℝ) := by
    rw [Real.cos_pi_div_eight]
    field_simp
  have h3 : (1 / Real.sqrt (2 + Real.sqrt 2)) * (1 + 2 * Real.cos (2 * (Real.pi / 8))) =
      2 * Real.cos (Real.pi / 8) * Real.cos (2 * (Real.pi / 8)) := by
    rw [hd, Real.cos_pi_div_eight]
    field_simp
    nlinarith
  unfold d flatC rho
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg Complex.ofReal h1
  · simpa using congrArg Complex.ofReal h2
  · exact_mod_cast h3

lemma paired_invariant (a : ℂ) : Dpoly a * Epoly a = (invariantFactor a).comp harmonicPoly := by
  have hd : 2 * d ^ 2 = (1 : ℂ) := by rw [constant_relations.1]; norm_num
  have hc := congrArg (Polynomial.C : ℂ → Polynomial ℂ) hd
  simp only [map_mul, map_pow, map_ofNat, map_one] at hc
  simp only [Dpoly, Epoly, invariantFactor, harmonicPoly, sub_comp, C_comp, X_comp,
    pow_comp, map_mul, map_sub, map_pow, map_ofNat]
  linear_combination -(2 * Polynomial.C a ^ 2 + 1) * X ^ 2 * hc

lemma kernel_projection_identity (a : ℂ) :
    (X - C flatC) * pairNumerator a * Epoly a =
      (kernelProjectP a).comp harmonicPoly + X * (kernelProjectJ a).comp harmonicPoly +
        X ^ 2 * (kernelProjectE a).comp harmonicPoly := by
  have hc : a * rho * (1 + 2 * d) + d ^ 2 - flatC * (2 * d * a - rho) - 1 = 0 := by
    calc a * rho * (1 + 2 * d) + d ^ 2 - flatC * (2 * d * a - rho) - 1 =
        a * (rho * (1 + 2 * d) - 2 * flatC * d) + d ^ 2 + flatC * rho - 1 := by ring
      _ = 0 := by rw [constant_relations.2.2, constant_relations.1, constant_relations.2.1]; ring
  calc (X - C flatC) * pairNumerator a * Epoly a =
      (kernelProjectP a).comp harmonicPoly + X * (kernelProjectJ a).comp harmonicPoly +
        X ^ 2 * (kernelProjectE a).comp harmonicPoly +
          C (a * rho * (1 + 2 * d) + d ^ 2 - flatC * (2 * d * a - rho) - 1) * X ^ 3 := by
        simp only [pairNumerator, Epoly, kernelProjectP, kernelProjectJ, kernelProjectE,
          harmonicPoly, sub_comp, add_comp, mul_comp, C_comp, X_comp,
          pow_comp, neg_comp, ofNat_comp, one_comp,
          map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_one]
        ring
    _ = _ := by rw [hc]; simp

lemma HasProjectionC.zero (N : ℕ) : HasProjectionC N 0 := by
  refine ⟨0, 0, 0, ?_, ?_, ?_, ?_⟩ <;> simp

lemma HasProjectionC.add {N : ℕ} {Q R : Polynomial ℂ}
    (hQ : HasProjectionC N Q) (hR : HasProjectionC N R) : HasProjectionC N (Q + R) := by
  obtain ⟨P, J, E, hp, hj, he, rfl⟩ := hQ
  obtain ⟨P', J', E', hp', hj', he', rfl⟩ := hR
  refine ⟨P + P', J + J', E + E', (natDegree_add_le _ _).trans (max_le hp hp'),
    (natDegree_add_le _ _).trans (max_le hj hj'),
    (degree_add_le _ _).trans_lt (max_lt he he'), ?_⟩
  simp only [add_comp]
  ring

lemma HasProjectionC.const_mul {N : ℕ} {Q : Polynomial ℂ}
    (hQ : HasProjectionC N Q) (t : ℂ) : HasProjectionC N (C t * Q) := by
  obtain ⟨P, J, E, hp, hj, he, rfl⟩ := hQ
  refine ⟨C t * P, C t * J, C t * E, (natDegree_C_mul_le _ _).trans hp,
    (natDegree_C_mul_le _ _).trans hj, ?_, ?_⟩
  · by_cases ht : t = 0
    · simp [ht]
    · rw [degree_C_mul ht]
      exact he
  · simp only [mul_comp, C_comp]
    ring

lemma HasProjectionC.mul_comp {N M : ℕ} {Q R : Polynomial ℂ}
    (hQ : HasProjectionC N Q) (hR : R.natDegree ≤ M) :
    HasProjectionC (N + M) (Q * R.comp harmonicPoly) := by
  obtain ⟨P, J, E, hp, hj, he, rfl⟩ := hQ
  refine ⟨P * R, J * R, E * R, natDegree_mul_le.trans (add_le_add hp hR),
    natDegree_mul_le.trans (add_le_add hj hR), ?_, ?_⟩
  · by_cases hE : E = 0
    · simp [hE]
    · rw [degree_eq_natDegree hE] at he
      have hE' : E.natDegree < N := by exact_mod_cast he
      exact degree_le_natDegree.trans_lt (by exact_mod_cast
        ((natDegree_mul_le : (E * R).natDegree ≤ E.natDegree + R.natDegree).trans_lt
          (Nat.add_lt_add_of_lt_of_le hE' hR)))
  · simp only [Polynomial.mul_comp]
    ring

lemma HasProjectionC.sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ)
    (hf : ∀ i ∈ s, HasProjectionC N (f i)) : HasProjectionC N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasProjectionC.zero N
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma base_projected : HasProjectionC 0 (X - C flatC) := by
  refine ⟨C (-flatC), 1, 0, ?_, ?_, ?_, ?_⟩ <;> simp; ring

lemma kernel_projected (a : ℂ) : HasProjectionC 1 ((X - C flatC) * pairNumerator a * Epoly a) := by
  refine ⟨kernelProjectP a, kernelProjectJ a, kernelProjectE a, ?_, ?_, ?_, kernel_projection_identity a⟩
  · unfold kernelProjectP; compute_degree!
  · unfold kernelProjectJ; compute_degree!
  · unfold kernelProjectE; compute_degree!

lemma invariant_product_degree {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    (∏ i ∈ s, invariantFactor (a i)).natDegree ≤ s.card := by
  apply (natDegree_prod_le _ _).trans
  calc ∑ i ∈ s, (invariantFactor (a i)).natDegree ≤ ∑ _i ∈ s, 1 := by
          apply Finset.sum_le_sum
          intro i hi
          unfold invariantFactor
          compute_degree!
    _ = s.card := by simp

lemma paired_product {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    (∏ i ∈ s, Dpoly (a i)) * (∏ i ∈ s, Epoly (a i)) =
      (∏ i ∈ s, invariantFactor (a i)).comp harmonicPoly := by
  rw [← Finset.prod_mul_distrib]
  simp_rw [paired_invariant]
  exact (Polynomial.prod_comp _ _ _).symm

lemma denominator_projected (N : ℕ) (a : Fin N → ℂ) :
    HasProjectionC N ((X - C flatC) * denominatorPoly N a * ∏ i, Epoly (a i)) := by
  have h := base_projected.mul_comp (invariant_product_degree Finset.univ a)
  simpa only [zero_add, Finset.card_univ, Fintype.card_fin, ← paired_product,
    ← mul_assoc, denominatorPoly] using h

lemma numerator_projected (N : ℕ) (a : Fin N → ℂ) (i : Fin N) :
    HasProjectionC N ((X - C flatC) * kernelNumerator N a i * ∏ j, Epoly (a j)) := by
  have h := (kernel_projected (a i)).mul_comp
    (invariant_product_degree (Finset.univ.erase i) a)
  have hcard : 1 + (Finset.univ.erase i).card = N := by
    have hi := i.isLt
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcard, ← paired_product] at h
  rw [← Finset.mul_prod_erase Finset.univ (fun j => Epoly (a j)) (Finset.mem_univ i)]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold kernelNumerator deletedDenominator
  ring

lemma polyLift_projected {n M : ℕ} (L : Vec n →ₗ[ℂ] ℂ)
    (f : Fin n → Polynomial ℂ) (Q R : Polynomial ℂ)
    (hf : ∀ i, HasProjectionC M (Q * f i * R)) :
    HasProjectionC M (Q * polyLift L f * R) := by
  have h := HasProjectionC.sum Finset.univ
    (fun i => C (L (standardBasis n i)) * (Q * f i * R))
    (fun i _ => (hf i).const_mul (L (standardBasis n i)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [polyLift, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma cleared_projected (N : ℕ) (a : Fin N → ℂ) :
    HasProjectionC N ((X - C flatC) * clearedPf N a * ∏ i, Epoly (a i)) := by
  apply polyLift_projected
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using denominator_projected N a
  · simpa only [Fin.snoc_castSucc] using numerator_projected N a j

 
theorem generic_pfaffian_projection (N : ℕ) (a : Fin N → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0)
    (hp : p N a ≠ 0) :
    ∃ g : Polynomial ℂ, g.Monic ∧ g.natDegree = N ∧
      HasProjectionC N (perturbedRootC a * g) ∧
      ∀ z : ℂ, (∀ i, z ≠ a i ∧ D (a i) z ≠ 0) →
        g.eval z = p (N + 1) (Fin.snoc a z) / p N a := by
  obtain ⟨g, hgm, hgn, hgf, hg⟩ := generic_arch_quotient_factor N a ha hD hp
  refine ⟨g, hgm, hgn, ?_, hg⟩
  have h := (cleared_projected N a).const_mul (((-1 : ℂ) ^ N * actualPf N a)⁻¹)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold perturbedRootC
  rw [Finset.prod_mul_distrib]
  change (X - C flatC) * (nodalPoly N a * ∏ i, Epoly (a i)) * g = _
  calc (X - C flatC) * (nodalPoly N a * ∏ i, Epoly (a i)) * g =
      (X - C flatC) * (nodalPoly N a * g) * ∏ i, Epoly (a i) := by ring
    _ = _ := by rw [hgf]; ring

end
end StripPfaffian

namespace StripComplexification
noncomputable section
open Polynomial
open scoped BigOperators

lemma component_real_mul (l : ℂ →ₗ[ℝ] ℝ) (q : Polynomial ℝ) (p : Polynomial ℂ) :
    component l (q.map Complex.ofRealHom * p) = q * component l p := by
  ext n
  simp only [component_coeff, coeff_mul, map_sum, coeff_map, Complex.ofRealHom_eq_coe]
  apply Finset.sum_congr rfl
  intro ij hij
  exact l.map_smul (q.coeff ij.1) (p.coeff ij.2)

end
end StripComplexification

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_QuarticIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
theorem quartic_weighted_integral_sqrt {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi 0, quarticWeighted r t) = Real.pi * Real.sqrt ((1 + r) / 2) := by
  rw [(quartic_weighted_integral hr).2]
  have hs : Real.sqrt (2 + 2 * r) = 2 * Real.sqrt ((1 + r) / 2) := by
    rw [show 2 + 2 * r = 4 * ((1 + r) / 2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hs]
  apply (div_eq_iff (by positivity : 2 * Real.sqrt ((1 + r) / 2) ≠ 0)).2
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + r) / 2)
  linear_combination -2 * Real.pi * hsq

theorem minusBranch_zero : minusBranch 0 = Real.cos (Real.pi / 8) := by
  rw [Real.cos_pi_div_eight]
  have h : Real.sqrt ((1 + (0 : ℝ)) / 2) = Real.sqrt 2 / 2 := by
    have ha := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (1 + 0) / 2)
    have hb := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hna := Real.sqrt_nonneg ((1 + (0 : ℝ)) / 2)
    have hnb := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  unfold minusBranch
  rw [h]
  have ha := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt 2 / 2) / 2)
  have hb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt 2)
  have hna := Real.sqrt_nonneg ((1 + Real.sqrt 2 / 2) / 2)
  have hnb := Real.sqrt_nonneg (2 + Real.sqrt 2)
  nlinarith

theorem transformed_omega {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |(-8 * t * (t ^ 2 + 1) / uniformDen t ^ 2)| •
        (s * omega (uniformizer t) / (1 + s * uniformizer t)) =
      quarticWeighted (Real.sqrt ((1 + s) / 2)) t -
        quarticWeighted (Real.sqrt (1 / 2)) t := by
  rw [omega_uniformizer ht, abs_of_neg (by
    exact div_neg_of_neg_of_pos (by nlinarith [sq_nonneg t])
      (sq_pos_of_pos (uniformDen_pos t))), smul_eq_mul]
  unfold quarticWeighted quarticDen
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + s) / 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  unfold uniformizer uniformDen
  field_simp
  ring

theorem omega_resolvent {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x => s * omega x / (1 + s * x)) (Ioo 0 1) ∧
      (∫ x in Ioo 0 1, s * omega x / (1 + s * x)) =
        Real.pi * (minusBranch s - minusBranch 0) := by
  have hr : 0 < Real.sqrt ((1 + s) / 2) := by positivity
  have hr0 : 0 < Real.sqrt ((1 : ℝ) / 2) := by positivity
  have hint := (quartic_weighted_integral hr).1.sub (quartic_weighted_integral hr0).1
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (uniformizer_deriv t).hasDerivWithinAt) uniformizer_inj
    (fun x => s * omega x / (1 + s * x))
  rw [uniformizer_image] at hi
  constructor
  · apply hi.2
    exact IntegrableOn.congr_fun hint (fun t ht => (transformed_omega hs ht).symm)
      measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (uniformizer_deriv t).hasDerivWithinAt) uniformizer_inj
      (fun x => s * omega x / (1 + s * x))
    rw [uniformizer_image] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht => transformed_omega hs ht),
      integral_sub (quartic_weighted_integral hr).1 (quartic_weighted_integral hr0).1,
      quartic_weighted_integral_sqrt hr, quartic_weighted_integral_sqrt hr0]
    simp only [minusBranch, add_zero]
    ring

 

theorem stieltjes_omega {z : ℝ} (hz : z < 0) :
    Real.sqrt ((1 + Real.sqrt ((1 - 1 / z) / 2)) / 2) =
      Real.cos (Real.pi / 8) + (1 / Real.pi) *
        ∫ x in Ioo (0 : ℝ) 1, omega x / (x - z) := by
  have hs : 0 < -1 / z := div_pos_of_neg_of_neg (by norm_num) hz
  have heq : EqOn (fun x => (-1 / z) * omega x / (1 + (-1 / z) * x))
      (fun x => omega x / (x - z)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    have ha : 1 + (-1 / z) * x ≠ 0 := ne_of_gt (by have := hx.1; positivity)
    have hb : x - z ≠ 0 := by linarith [hx.1]
    apply (div_eq_div_iff ha hb).2
    field_simp [hz.ne]
    ring
  have h := (omega_resolvent hs).2
  rw [setIntegral_congr_fun measurableSet_Ioo heq, minusBranch_zero] at h
  have he : minusBranch (-1 / z) =
      Real.sqrt ((1 + Real.sqrt ((1 - 1 / z) / 2)) / 2) := by
    unfold minusBranch
    congr 4
    ring
  rw [he] at h
  rw [h]
  field_simp
  ring

theorem stieltjes_lBranch {z : ℝ} (hz : 0 < z) :
    lBranch z = Real.sqrt 2 * Real.cos (Real.pi / 8) +
      (Real.sqrt 2 / Real.pi) * ∫ x in Ioo (0 : ℝ) 1, omega x / (x + z) := by
  have h := stieltjes_omega (neg_neg_of_pos hz)
  have heq : lBranch z = Real.sqrt 2 *
      Real.sqrt ((1 + Real.sqrt ((1 - 1 / (-z)) / 2)) / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    unfold lBranch
    congr 2
    field_simp
    ring_nf
  rw [heq, h]
  simp only [sub_neg_eq_add]
  ring

theorem lBranch_mul_omega {x : ℝ} (hx : x ∈ Ioo 0 1) :
    lBranch x * omega x = squareWeight x := by
  have hx0 : 0 < x := hx.1
  have heq : (1 + 1 / x) / 2 = (1 + x) / (2 * x) := by
    field_simp [hx0.ne']
    ring
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + x) / (2 * x))
  have hp : (1 + Real.sqrt ((1 + x) / (2 * x))) *
      (Real.sqrt ((1 + x) / (2 * x)) - 1) = (1 - x) / (2 * x) := by
    calc
      _ = (1 + x) / (2 * x) - 1 := by nlinarith
      _ = _ := by field_simp [hx0.ne']; ring
  unfold lBranch omega squareWeight
  rw [heq, ← mul_assoc, mul_comm (Real.sqrt _) (1 / 2 : ℝ), mul_assoc,
    ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 + Real.sqrt ((1 + x) / (2 * x))), hp]
  have heq2 : (1 - x) / (8 * x) = (1 / 4) * ((1 - x) / (2 * x)) := by ring
  rw [heq2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  norm_num

theorem scaled_cauchy_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), (a ^ 2 + t ^ 2)⁻¹) = Real.pi / (2 * a) := by
  have heq : (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) =
      fun t => (a ^ 2)⁻¹ * (1 + (a⁻¹ * t) ^ 2)⁻¹ := by
    funext t
    field_simp
  rw [heq, integral_const_mul, integral_comp_mul_left_Ioi (fun t : ℝ => (1 + t ^ 2)⁻¹) 0 (inv_pos.2 ha)]
  simp only [mul_zero, inv_inv, smul_eq_mul, integral_Ioi_inv_one_add_sq,
    Real.arctan_zero, sub_zero]
  field_simp

theorem squareUniformizer_deriv (t : ℝ) :
    HasDerivAt squareUniformizer (-2 * t / (1 + t ^ 2) ^ 2) t := by
  have hd : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_add 1
  change HasDerivAt (fun t : ℝ => 1 / (1 + t ^ 2)) _ t
  exact (((hasDerivAt_const t (1 : ℝ)).div hd
    (show 1 + t ^ 2 ≠ 0 by positivity))).congr_deriv (by ring)

theorem squareUniformizer_inj : InjOn squareUniformizer (Ioi 0) := by
  apply StrictAntiOn.injOn
  intro x hx y hy hxy
  unfold squareUniformizer
  apply one_div_lt_one_div_of_lt (by positivity)
  gcongr
  exact le_of_lt hx

theorem squareUniformizer_image : squareUniformizer '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨by unfold squareUniformizer; positivity, ?_⟩
    unfold squareUniformizer
    rw [div_lt_one (by positivity)]
    exact lt_add_of_pos_right 1 (sq_pos_of_pos ht)
  · intro hx
    have hpos : 0 < 1 / x - 1 := by
      rw [sub_pos, one_lt_div hx.1]
      exact hx.2
    have hs := Real.sq_sqrt hpos.le
    refine ⟨Real.sqrt (1 / x - 1), Real.sqrt_pos.2 hpos, ?_⟩
    unfold squareUniformizer
    rw [hs]
    field_simp [hx.1.ne']
    ring

theorem squareWeight_uniformizer {t : ℝ} (ht : 0 < t) :
    squareWeight (squareUniformizer t) = t / (2 * Real.sqrt 2) := by
  have heq : (1 - squareUniformizer t) / (8 * squareUniformizer t) = t ^ 2 / 8 := by
    unfold squareUniformizer
    field_simp
    ring
  unfold squareWeight
  rw [heq, Real.sqrt_div (sq_nonneg t), Real.sqrt_sq ht.le]
  congr 1
  rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem transformed_squareWeight {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |(-2 * t / (1 + t ^ 2) ^ 2)| •
        (s * squareWeight (squareUniformizer t) / (1 + s * squareUniformizer t)) =
      (1 / Real.sqrt 2) * ((1 + s) * ((1 + s) + t ^ 2)⁻¹ - (1 + t ^ 2)⁻¹) := by
  rw [squareWeight_uniformizer ht, abs_of_neg (by
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)), smul_eq_mul]
  unfold squareUniformizer
  field_simp
  ring

theorem squareWeight_resolvent {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun x => s * squareWeight x / (1 + s * x)) (Ioo 0 1) ∧
      (∫ x in Ioo 0 1, s * squareWeight x / (1 + s * x)) =
        (Real.pi / (2 * Real.sqrt 2)) * (Real.sqrt (1 + s) - 1) := by
  let a := Real.sqrt (1 + s)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a ^ 2 = 1 + s := Real.sq_sqrt (by positivity)
  have hint1 : IntegrableOn (fun t : ℝ => ((1 + s) + t ^ 2)⁻¹) (Ioi 0) := by
    rw [← ha2]
    exact (scaled_cauchy ha).1.integrableOn
  have hint0 : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hint := ((hint1.const_mul (1 + s)).sub hint0).const_mul (1 / Real.sqrt 2)
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (squareUniformizer_deriv t).hasDerivWithinAt) squareUniformizer_inj
    (fun x => s * squareWeight x / (1 + s * x))
  rw [squareUniformizer_image] at hi
  constructor
  · apply hi.2
    exact IntegrableOn.congr_fun hint (fun t ht => (transformed_squareWeight hs ht).symm)
      measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (squareUniformizer_deriv t).hasDerivWithinAt) squareUniformizer_inj
      (fun x => s * squareWeight x / (1 + s * x))
    rw [squareUniformizer_image] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht => transformed_squareWeight hs ht),
      integral_const_mul, integral_sub (hint1.const_mul (1 + s)) hint0,
      integral_const_mul, ← ha2, scaled_cauchy_Ioi ha, integral_Ioi_inv_one_add_sq,
      Real.arctan_zero, sub_zero]
    rw [Real.sqrt_sq ha.le]
    field_simp

theorem stieltjes_omega_square {z : ℝ} (hz : z < 0) :
    (Real.sqrt ((1 + Real.sqrt ((1 - 1 / z) / 2)) / 2)) ^ 2 =
      (Real.cos (Real.pi / 8)) ^ 2 + (1 / Real.pi) *
        ∫ x in Ioo (0 : ℝ) 1, lBranch x * omega x / (x - z) := by
  have hs : 0 < -1 / z := div_pos_of_neg_of_neg (by norm_num) hz
  have heq : EqOn (fun x => (-1 / z) * squareWeight x / (1 + (-1 / z) * x))
      (fun x => lBranch x * omega x / (x - z)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    rw [lBranch_mul_omega hx]
    have ha : 1 + (-1 / z) * x ≠ 0 := ne_of_gt (by have := hx.1; positivity)
    have hb : x - z ≠ 0 := by linarith [hx.1]
    apply (div_eq_div_iff ha hb).2
    field_simp [hz.ne]
    ring
  have h := (squareWeight_resolvent hs).2
  rw [setIntegral_congr_fun measurableSet_Ioo heq] at h
  have hC : (Real.cos (Real.pi / 8)) ^ 2 = (1 + Real.sqrt (1 / 2)) / 2 := by
    rw [← minusBranch_zero]
    unfold minusBranch
    simp only [add_zero]
    exact Real.sq_sqrt (by positivity)
  rw [h, hC, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt ((1 - 1 / z) / 2)) / 2)]
  have heq' : 1 - 1 / z = 1 + -1 / z := by ring
  rw [heq', Real.sqrt_div (by linarith : (0 : ℝ) ≤ 1 + -1 / z),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  field_simp
  ring

 

theorem integrableOn_lBranch_omega :
    IntegrableOn (fun x => lBranch x * omega x) (Ioo (0 : ℝ) 1) := by
  have hint := ((squareWeight_resolvent (by norm_num : (0 : ℝ) < 1)).1).const_mul 2
  apply hint.mono'
  · apply Measurable.aestronglyMeasurable
    unfold lBranch omega
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, lBranch_mul_omega hx, abs_of_nonneg (show 0 ≤ squareWeight x from Real.sqrt_nonneg _)]
    simp only [one_mul]
    have hd : 0 < 1 + x := by linarith [hx.1]
    have hw : 0 ≤ squareWeight x := Real.sqrt_nonneg _
    rw [← mul_div_assoc, le_div_iff₀ hd]
    nlinarith [hx.2]


 


theorem integrableOn_continuous_mul {w g : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (hg : ContinuousOn g (Icc 0 1)) :
    IntegrableOn (fun x => g x * w x) (Ioo (0 : ℝ) 1) := by
  have hc : IntegrableOn w (Icc (0 : ℝ) 1) := (integrableOn_Icc_iff_integrableOn_Ioo (f := w) (μ := volume)).2 hw
  have h := (hc.mul_continuousOn hg isCompact_Icc).mono_set Ioo_subset_Icc_self
  simpa only [mul_comm] using h


theorem integrableOn_stieltjes {a z : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (hz : offCut a z) :
    IntegrableOn (fun x => w x / (z - a * x)) (Ioo (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun x : ℝ => (z - a * x)⁻¹) (Icc 0 1) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn.inv₀ hz
  simpa only [div_eq_mul_inv, mul_comm] using integrableOn_continuous_mul hw hc

theorem integrableOn_polynomial_weight {a : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (p : Polynomial ℝ) :
    IntegrableOn (fun x => p.eval (a * x) * w x) (Ioo (0 : ℝ) 1) :=
  integrableOn_continuous_mul hw (p.continuous.comp (continuous_const.mul continuous_id)).continuousOn

theorem realStieltjes_const_mul (a z c : ℝ) (w : ℝ → ℝ) :
    realStieltjes a (fun x => c * w x) z = c * realStieltjes a w z := by
  unfold realStieltjes
  simp only [mul_div_assoc, integral_const_mul]

theorem realStieltjes_add {a z : ℝ} {w v : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (hv : IntegrableOn v (Ioo (0 : ℝ) 1))
    (hz : offCut a z) :
    realStieltjes a (fun x => w x + v x) z = realStieltjes a w z + realStieltjes a v z := by
  unfold realStieltjes
  simp only [add_div]
  exact integral_add (integrableOn_stieltjes hw hz) (integrableOn_stieltjes hv hz)

theorem realStieltjes_mul_variable {a z : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (hz : offCut a z) :
    z * realStieltjes a w z = realStieltjes a (fun x => a * x * w x) z +
      ∫ x in Ioo (0 : ℝ) 1, w x := by
  have hi : IntegrableOn (fun x => a * x * w x) (Ioo (0 : ℝ) 1) :=
    integrableOn_continuous_mul hw (continuous_const.mul continuous_id).continuousOn
  unfold realStieltjes
  rw [← integral_const_mul, ← integral_add (integrableOn_stieltjes hi hz) hw]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hne := hz x ⟨hx.1.le, hx.2.le⟩
  dsimp only
  field_simp
  ring

 

theorem polynomial_mul_realStieltjes {a : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (p : Polynomial ℝ) :
    ∃ R : Polynomial ℝ, ∀ z : ℝ, offCut a z →
      p.eval z * realStieltjes a w z =
        realStieltjes a (fun x => p.eval (a * x) * w x) z + R.eval z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨R, hR⟩ := hp
      obtain ⟨S, hS⟩ := hq
      refine ⟨R + S, fun z hz => ?_⟩
      simp only [Polynomial.eval_add, add_mul]
      rw [realStieltjes_add (integrableOn_polynomial_weight hw p)
        (integrableOn_polynomial_weight hw q) hz, hR z hz, hS z hz]
      ring
  | monomial n c =>
      induction n with
      | zero =>
          refine ⟨0, fun z hz => ?_⟩
          simp [realStieltjes_const_mul]
      | succ n ih =>
          obtain ⟨R, hR⟩ := ih
          let v : ℝ → ℝ := fun x => c * (a * x) ^ n * w x
          have hv : IntegrableOn v (Ioo (0 : ℝ) 1) := by
            simpa [v] using integrableOn_polynomial_weight hw (Polynomial.monomial n c)
          refine ⟨Polynomial.X * R + Polynomial.C (∫ x in Ioo (0 : ℝ) 1, v x), fun z hz => ?_⟩
          have hrec := realStieltjes_mul_variable hv hz
          have hpoly := hR z hz
          simp only [Polynomial.eval_monomial] at hpoly ⊢
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
            Polynomial.eval_C]
          have heq : (fun x => a * x * v x) = fun x => c * (a * x) ^ (n + 1) * w x := by
            funext x
            simp only [v, pow_succ]
            ring
          rw [heq] at hrec
          change c * z ^ n * realStieltjes a w z = realStieltjes a v z + R.eval z at hpoly
          rw [pow_succ]
          linear_combination z * hpoly + hrec

theorem abs_mul_le_one {a x : ℝ} (ha : |a| ≤ 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    |a * x| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg hx.1]
  nlinarith [abs_nonneg a, hx.1, hx.2]

theorem offCut_of_abs_large {a z : ℝ} (ha : |a| ≤ 1) (hz : 2 ≤ |z|) :
    offCut a z := by
  intro x hx heq
  have h := abs_mul_le_one ha hx
  have hzx : z = a * x := sub_eq_zero.1 heq
  rw [hzx] at hz
  linarith

theorem norm_realStieltjes_le {a z : ℝ} {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (ha : |a| ≤ 1) (hz : 2 ≤ |z|) :
    ‖realStieltjes a w z‖ ≤ (∫ x in Ioo (0 : ℝ) 1, ‖w x‖) / (|z| - 1) := by
  have hd : 0 < |z| - 1 := by linarith
  have hi := hw.norm.div_const (|z| - 1)
  have hbound : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖w x / (z - a * x)‖ ≤ ‖w x‖ / (|z| - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hax := abs_mul_le_one ha ⟨hx.1.le, hx.2.le⟩
    have hden : |z| - 1 ≤ |z - a * x| := by
      have h := abs_sub_abs_le_abs_sub z (a * x)
      linarith
    rw [norm_div, Real.norm_eq_abs (z - a * x)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hd hden
  have h := norm_integral_le_of_norm_le hi hbound
  simpa only [realStieltjes, integral_div] using h

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StieltjesLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
theorem tendsto_realStieltjes_zero {α : Type*} {l : Filter α} {z : α → ℝ}
    {a : ℝ} {w : ℝ → ℝ} (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (ha : |a| ≤ 1)
    (hz : Tendsto (fun t => ‖z t‖) l atTop) :
    Tendsto (fun t => realStieltjes a w (z t)) l (𝓝 0) := by
  have hz' : Tendsto (fun t => |z t|) l atTop := by simpa only [Real.norm_eq_abs] using hz
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((hz'.eventually_ge_atTop 2).mono fun _ ht => norm_realStieltjes_le hw ha ht)
  exact tendsto_const_nhds.div_atTop (by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1) hz')

 
theorem polynomial_constant_of_limit {α : Type*} {l : Filter α} [l.NeBot]
    {z : α → ℝ} (hz : Tendsto (fun t => ‖z t‖) l atTop)
    (p : Polynomial ℝ) {L : ℝ} (hp : Tendsto (fun t => p.eval (z t)) l (𝓝 L)) :
    p = Polynomial.C L := by
  have hd : p.degree ≤ 0 := by
    by_contra h
    have htop := p.tendsto_norm_atTop (lt_of_not_ge h) hz
    exact not_tendsto_nhds_of_tendsto_atTop htop ‖L‖ hp.norm
  have heq := Polynomial.eq_C_of_degree_le_zero hd
  have hL : p.coeff 0 = L := by
    have hc : Tendsto (fun _ : α => p.coeff 0) l (𝓝 L) := by
      apply hp.congr'
      exact Eventually.of_forall fun t =>
        (congrArg (fun q : Polynomial ℝ => q.eval (z t)) heq).trans (Polynomial.eval_C)
    exact tendsto_nhds_unique tendsto_const_nhds hc
  rw [heq, hL]

 

theorem moments_zero_of_stieltjes_decay {α : Type*} {l : Filter α} [l.NeBot]
    {z : α → ℝ} (hz : Tendsto (fun t => ‖z t‖) l atTop) (N : ℕ)
    {w : ℝ → ℝ} (hw : IntegrableOn w (Ioo (0 : ℝ) 1))
    (hdecay : ∀ j : ℕ, j < N → Tendsto
      (fun t => z t ^ (j + 1) * realStieltjes 1 w (z t)) l (𝓝 0)) :
    ∀ j : ℕ, j < N → ∫ x in Ioo (0 : ℝ) 1, x ^ j * w x = 0 := by
  induction N generalizing w with
  | zero => simp
  | succ N ih =>
      let v : ℝ → ℝ := fun x => x * w x
      have hv : IntegrableOn v (Ioo (0 : ℝ) 1) :=
        integrableOn_continuous_mul hw continuous_id.continuousOn
      have hevent : ∀ᶠ t in l, offCut 1 (z t) := by
        filter_upwards [hz.eventually_ge_atTop 2] with t ht
        exact offCut_of_abs_large (by norm_num) (by simpa only [Real.norm_eq_abs] using ht)
      have hrec : ∀ᶠ t in l, z t * realStieltjes 1 w (z t) =
          realStieltjes 1 v (z t) + ∫ x in Ioo (0 : ℝ) 1, w x := by
        filter_upwards [hevent] with t ht
        simpa only [one_mul] using realStieltjes_mul_variable hw ht
      have hlim : Tendsto (fun t => z t * realStieltjes 1 w (z t)) l
          (𝓝 (∫ x in Ioo (0 : ℝ) 1, w x)) := by
        have h := (tendsto_realStieltjes_zero hv (by norm_num : |(1 : ℝ)| ≤ 1) hz).add_const
          (∫ x in Ioo (0 : ℝ) 1, w x)
        simpa only [zero_add] using h.congr' (hrec.mono fun _ ht => ht.symm)
      have hm : (∫ x in Ioo (0 : ℝ) 1, w x) = 0 := by
        apply tendsto_nhds_unique hlim
        simpa only [zero_add, pow_one] using hdecay 0 (Nat.succ_pos N)
      have hdecayv : ∀ j : ℕ, j < N → Tendsto
          (fun t => z t ^ (j + 1) * realStieltjes 1 v (z t)) l (𝓝 0) := by
        intro j hj
        apply (hdecay (j + 1) (Nat.succ_lt_succ hj)).congr'
        filter_upwards [hrec] with t ht
        rw [hm, add_zero] at ht
        rw [← ht, pow_succ]
        ring
      intro j hj
      cases j with
      | zero => simpa using hm
      | succ j =>
          have hj' : j < N := Nat.lt_of_succ_lt_succ hj
          have h := ih hv hdecayv j hj'
          convert h using 1
          all_goals try with_reducible_and_instances rfl
          apply setIntegral_congr_fun measurableSet_Ioo
          intro x _
          dsimp [v]
          rw [pow_succ]
          ring




theorem integrableOn_omega_projection : IntegrableOn omega (Ioo (0 : ℝ) 1) := by
  have hi := ((omega_resolvent (by norm_num : (0 : ℝ) < 1)).1).const_mul 2
  apply hi.mono'
  · apply Measurable.aestronglyMeasurable
    unfold omega
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold omega; positivity)]
    simp only [one_mul]
    have hd : 0 < 1 + x := by linarith [hx.1]
    rw [← mul_div_assoc, le_div_iff₀ hd]
    have hw : 0 ≤ omega x := by unfold omega; positivity
    nlinarith [hx.2]

theorem offCut_one_neg {z : ℝ} (hz : z < 0) : offCut 1 z := by
  intro x hx
  simp only [one_mul]
  linarith [hx.1]

theorem offCut_neg_one_pos {z : ℝ} (hz : 0 < z) : offCut (-1) z := by
  intro x hx
  simp only [neg_one_mul, sub_neg_eq_add]
  linarith [hx.1]

theorem integrableOn_projection_weight (J E : Polynomial ℝ) :
    IntegrableOn (fun x => projectionD J E x * omega x) (Ioo (0 : ℝ) 1) := by
  have hj := integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_omega_projection J
  have he := integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_lBranch_omega E
  have heq : (fun x => projectionD J E x * omega x) =
      fun x => J.eval (1 * x) * omega x + E.eval (1 * x) * (lBranch x * omega x) := by
    funext x
    simp only [one_mul, projectionD]
    ring
  rw [heq]
  exact hj.add he

theorem fBranch_transform {z : ℝ} (hz : z < 0) :
    fBranch z = Real.cos (Real.pi / 8) -
      (1 / Real.pi) * realStieltjes 1 omega z := by
  have h := stieltjes_omega hz
  have heq : (∫ x in Ioo (0 : ℝ) 1, omega x / (x - z)) = -realStieltjes 1 omega z := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [one_mul]
    rw [show x - z = -(z - x) by ring, div_neg]
  simpa only [fBranch, heq, mul_neg, ← sub_eq_add_neg] using h

theorem fBranch_square_transform {z : ℝ} (hz : z < 0) :
    fBranch z ^ 2 = Real.cos (Real.pi / 8) ^ 2 -
      (1 / Real.pi) * realStieltjes 1 (fun x => lBranch x * omega x) z := by
  have h := stieltjes_omega_square hz
  have heq : (∫ x in Ioo (0 : ℝ) 1, lBranch x * omega x / (x - z)) =
      -realStieltjes 1 (fun x => lBranch x * omega x) z := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [one_mul]
    rw [show x - z = -(z - x) by ring, div_neg]
  simpa only [fBranch, heq, mul_neg, ← sub_eq_add_neg] using h

 
theorem projectionF_polynomial (P J E : Polynomial ℝ) :
    ∃ R : Polynomial ℝ, ∀ z : ℝ, z < 0 →
      projectionF P J E z = R.eval z - (1 / Real.pi) *
        realStieltjes 1 (fun x => projectionD J E x * omega x) z := by
  obtain ⟨Rj, hRj⟩ := polynomial_mul_realStieltjes (a := (1 : ℝ)) integrableOn_omega_projection J
  obtain ⟨Re, hRe⟩ := polynomial_mul_realStieltjes (a := (1 : ℝ)) integrableOn_lBranch_omega E
  refine ⟨P + Polynomial.C (Real.cos (Real.pi / 8)) * J +
    Polynomial.C (Real.cos (Real.pi / 8) ^ 2) * E -
    Polynomial.C (1 / Real.pi) * (Rj + Re), ?_⟩
  intro z hz
  have hj := hRj z (offCut_one_neg hz)
  have he := hRe z (offCut_one_neg hz)
  have hsum := realStieltjes_add
    (integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_omega_projection J)
    (integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_lBranch_omega E)
    (offCut_one_neg hz)
  have hw : (fun x => J.eval (1 * x) * omega x + E.eval (1 * x) * (lBranch x * omega x)) =
      fun x => projectionD J E x * omega x := by
    funext x
    simp only [one_mul, projectionD]
    ring
  rw [hw] at hsum
  simp only [one_mul] at hj he hsum
  rw [projectionF, fBranch_square_transform hz, fBranch_transform hz, hsum]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination -(1 / Real.pi) * hj - (1 / Real.pi) * he

theorem norm_neg_atTop : Tendsto (fun z : ℝ => ‖-z‖) atTop atTop := by
  simpa only [norm_neg] using (tendsto_norm_atTop_atTop : Tendsto (fun z : ℝ => ‖z‖) atTop atTop)

 

theorem projectionF_cauchy (P J E : Polynomial ℝ)
    (hF : Tendsto (fun t : ℝ => projectionF P J E (-t)) atTop (𝓝 0)) :
    ∀ z : ℝ, z < 0 → projectionF P J E z = -(1 / Real.pi) *
      realStieltjes 1 (fun x => projectionD J E x * omega x) z := by
  obtain ⟨R, hR⟩ := projectionF_polynomial P J E
  have hlim := hF.add ((tendsto_realStieltjes_zero (integrableOn_projection_weight J E)
    (by norm_num : |(1 : ℝ)| ≤ 1) norm_neg_atTop).const_mul (1 / Real.pi))
  have hRlim : Tendsto (fun t : ℝ => R.eval (-t)) atTop (𝓝 0) := by
    have hlim' : Tendsto (fun t : ℝ => projectionF P J E (-t) + (1 / Real.pi) *
        realStieltjes 1 (fun x => projectionD J E x * omega x) (-t)) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using hlim
    apply hlim'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := hR (-t) (neg_neg_of_pos ht)
    linarith
  have hR0 := polynomial_constant_of_limit norm_neg_atTop R hRlim
  intro z hz
  simpa only [hR0, Polynomial.eval_C, zero_sub, neg_mul] using hR z hz

 

theorem projection_moments_of_decay (N : ℕ) (P J E : Polynomial ℝ)
    (hF : ∀ j : ℕ, j ≤ N → Tendsto
      (fun t : ℝ => (-t) ^ j * projectionF P J E (-t)) atTop (𝓝 0)) :
    ∀ j : ℕ, j < N → ∫ x in Ioo (0 : ℝ) 1,
      x ^ j * (projectionD J E x * omega x) = 0 := by
  have hFc := projectionF_cauchy P J E (by simpa using hF 0 (Nat.zero_le N))
  apply moments_zero_of_stieltjes_decay norm_neg_atTop N (integrableOn_projection_weight J E)
  intro j hj
  apply (show Tendsto (fun t : ℝ => (-Real.pi) *
      ((-t) ^ (j + 1) * projectionF P J E (-t))) atTop (𝓝 0) from
    by simpa using (hF (j + 1) (Nat.succ_le_of_lt hj)).const_mul (-Real.pi)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [hFc (-t) (neg_neg_of_pos ht)]
  field_simp [Real.pi_ne_zero]

 

theorem projectionD_cauchy (J e : Polynomial ℝ) {L : ℝ}
    (hD : Tendsto (fun z : ℝ => projectionD J (Polynomial.X * e) z) atTop (𝓝 L)) :
    ∀ z : ℝ, 0 < z → projectionD J (Polynomial.X * e) z = J.eval 0 +
      (Real.sqrt 2 / Real.pi) * z * realStieltjes (-1)
        (fun x => e.eval (-x) * omega x) z := by
  obtain ⟨R, hR⟩ := polynomial_mul_realStieltjes (a := (-1 : ℝ)) integrableOn_omega_projection e
  let v : ℝ → ℝ := fun x => e.eval (-x) * omega x
  let S : Polynomial ℝ := J + Polynomial.C (Real.sqrt 2 * Real.cos (Real.pi / 8)) *
      (Polynomial.X * e) + Polynomial.C (Real.sqrt 2 / Real.pi) * (Polynomial.X * R)
  have hv : IntegrableOn v (Ioo (0 : ℝ) 1) := by
    simpa only [neg_one_mul] using integrableOn_polynomial_weight (a := (-1 : ℝ))
      integrableOn_omega_projection e
  have hEq : ∀ z : ℝ, 0 < z → projectionD J (Polynomial.X * e) z = S.eval z +
      (Real.sqrt 2 / Real.pi) * z * realStieltjes (-1) v z := by
    intro z hz
    have hl := stieltjes_lBranch hz
    have he := hR z (offCut_neg_one_pos hz)
    simp only [neg_one_mul] at he
    change e.eval z * realStieltjes (-1) omega z = realStieltjes (-1) v z + R.eval z at he
    have ht : (∫ x in Ioo (0 : ℝ) 1, omega x / (x + z)) = realStieltjes (-1) omega z := by
      simp [realStieltjes, add_comm]
    rw [ht] at hl
    simp only [projectionD, Polynomial.eval_mul, Polynomial.eval_X, hl, S,
      Polynomial.eval_add, Polynomial.eval_C]
    linear_combination (Real.sqrt 2 / Real.pi) * z * he
  have hnorm : Tendsto (fun z : ℝ => ‖z‖) atTop atTop := tendsto_norm_atTop_atTop
  have hzT : Tendsto (fun z : ℝ => z * realStieltjes (-1) v z) atTop
      (𝓝 (∫ x in Ioo (0 : ℝ) 1, v x)) := by
    have hweight : IntegrableOn (fun x => (-1 : ℝ) * x * v x) (Ioo (0 : ℝ) 1) :=
      integrableOn_continuous_mul hv (continuous_const.mul continuous_id).continuousOn
    have ht := (tendsto_realStieltjes_zero hweight (by norm_num : |(-1 : ℝ)| ≤ 1) hnorm).add_const
      (∫ x in Ioo (0 : ℝ) 1, v x)
    have ht' : Tendsto (fun z : ℝ => realStieltjes (-1) (fun x => (-1 : ℝ) * x * v x) z +
        ∫ x in Ioo (0 : ℝ) 1, v x) atTop (𝓝 (∫ x in Ioo (0 : ℝ) 1, v x)) := by
      simpa only [zero_add] using ht
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact (realStieltjes_mul_variable hv (offCut_neg_one_pos hz)).symm
  have hSlim : Tendsto (fun z : ℝ => S.eval z) atTop
      (𝓝 (L - (Real.sqrt 2 / Real.pi) * ∫ x in Ioo (0 : ℝ) 1, v x)) := by
    apply (hD.sub (hzT.const_mul (Real.sqrt 2 / Real.pi))).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [hEq z hz]
    ring
  have hS := polynomial_constant_of_limit hnorm S hSlim
  have hS0 : S.eval 0 = J.eval 0 := by simp [S]
  have hSc : ∀ z : ℝ, S.eval z = J.eval 0 := by
    intro z
    calc S.eval z = S.eval 0 := by rw [hS]; simp
         _ = J.eval 0 := hS0
  intro z hz
  simpa only [hSc] using hEq z hz

end

 

noncomputable section
open Polynomial Set Filter
open scoped Topology


theorem affine_natDegree :
    (Polynomial.C (1 / 8 : ℝ) * (1 + X)).natDegree = 1 := by
  compute_degree
  norm_num

theorem tildePoly_natDegree_le (N : ℕ) {p : Polynomial ℝ} (hp : p.natDegree ≤ N) :
    (tildePoly N p).natDegree ≤ N := by
  apply le_trans natDegree_reflect_le
  rw [natDegree_comp, affine_natDegree, mul_one, max_eq_left hp]

theorem tildePoly_eval (N : ℕ) {p : Polynomial ℝ} (hp : p.natDegree ≤ N)
    {z : ℝ} (hz : z ≠ 0) :
    (tildePoly N p).eval z = z ^ N * p.eval ((1 + 1 / z) / 8) := by
  let : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have hdeg : (p.comp (Polynomial.C (1 / 8) * (1 + X))).natDegree ≤ N := by
    rw [natDegree_comp, affine_natDegree, mul_one]
    exact hp
  have h := eval₂_reflect_mul_pow (RingHom.id ℝ) z⁻¹ N
    (p.comp (Polynomial.C (1 / 8) * (1 + X))) hdeg
  simp only [invOf_eq_inv, inv_inv, eval₂_id, eval_comp, eval_mul, eval_C, eval_add,
    eval_one, eval_X] at h
  change (tildePoly N p).eval z * (z⁻¹) ^ N = p.eval ((1 / 8) * (1 + z⁻¹)) at h
  have heq : (1 / 8 : ℝ) * (1 + z⁻¹) = (1 + 1 / z) / 8 := by ring
  rw [heq] at h
  have h' := congrArg (fun x : ℝ => x * z ^ N) h
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one] at h'
  exact h'.trans (mul_comm _ _)

theorem tildePoly_eq_zero_iff (N : ℕ) (p : Polynomial ℝ) : tildePoly N p = 0 ↔ p = 0 := by
  rw [tildePoly, reflect_eq_zero_iff]
  rw [comp_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | ⟨_, h⟩
    · exact h
    · have hd := congrArg Polynomial.natDegree h
      rw [affine_natDegree, natDegree_C] at hd
      contradiction
  · exact Or.inl

theorem tildePoly_zero_of_degree_lt (N : ℕ) {p : Polynomial ℝ}
    (hp : p.degree < (N : WithBot ℕ)) : (tildePoly N p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, tildePoly, coeff_reflect, revAt_zero]
  apply coeff_eq_zero_of_degree_lt
  have hq : (Polynomial.C (1 / 8 : ℝ) * (1 + X)).degree = 1 := by
    rw [degree_eq_natDegree (p := Polynomial.C (1 / 8 : ℝ) * (1 + X)) (by
      intro h; have hd := affine_natDegree; rw [h, natDegree_zero] at hd; contradiction),
      affine_natDegree]
    rfl
  rw [degree_comp (by rw [hq]; norm_num), hq, mul_one]
  exact hp


theorem sqrt_half : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
  have h1 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn1 := Real.sqrt_nonneg (1 / 2 : ℝ)
  have hn2 := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem highBranch_zero : highBranch 0 = C := by
  rw [C, lambda, Real.cos_pi_div_eight]
  unfold highBranch
  simp only [sub_zero, sqrt_half]
  have ha := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt 2 / 2) / 2)
  have hb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt 2)
  have hna := Real.sqrt_nonneg ((1 + Real.sqrt 2 / 2) / 2)
  have hnb := Real.sqrt_nonneg (2 + Real.sqrt 2)
  nlinarith

theorem lowBranch_zero : lowBranch 0 = c := by
  have hc : c = Real.sin (Real.pi / 8) := by
    rw [c, show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub]
  rw [hc, Real.sin_pi_div_eight]
  unfold lowBranch
  simp only [sub_zero, sqrt_half]
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ (1 - Real.sqrt 2 / 2) / 2 by linarith [sqrt_two_lt_two])
  have hb := Real.sq_sqrt (show (0 : ℝ) ≤ 2 - Real.sqrt 2 by linarith [sqrt_two_lt_two])
  have hna := Real.sqrt_nonneg ((1 - Real.sqrt 2 / 2) / 2)
  have hnb := Real.sqrt_nonneg (2 - Real.sqrt 2)
  nlinarith

theorem highBranch_continuous : Continuous highBranch := by unfold highBranch; fun_prop
theorem lowBranch_continuous : Continuous lowBranch := by unfold lowBranch; fun_prop

theorem branches_sq {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    highBranch u ^ 2 = (1 + Real.sqrt ((1 - u) / 2)) / 2 ∧
    lowBranch u ^ 2 = (1 - Real.sqrt ((1 - u) / 2)) / 2 ∧
    Real.sqrt ((1 - u) / 2) ^ 2 = (1 - u) / 2 := by
  have hd : 0 ≤ (1 - u) / 2 := by linarith [hu.2]
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg ((1 - u) / 2)
  have hlt : Real.sqrt ((1 - u) / 2) < 1 := by nlinarith [hu.1]
  exact ⟨Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith), hs⟩

theorem branches_harmonic {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    harmonicCoordinate.eval (highBranch u) = (1 + u) / 8 ∧
    harmonicCoordinate.eval (lowBranch u) = (1 + u) / 8 := by
  obtain ⟨hh, hl, hs⟩ := branches_sq hu
  simp only [harmonicCoordinate, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  constructor <;> nlinarith

theorem branches_sum {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    highBranch u + lowBranch u = Real.sqrt (1 + Real.sqrt ((1 + u) / 2)) := by
  obtain ⟨hh, hl, hs⟩ := branches_sq hu
  have ha : 0 ≤ highBranch u := Real.sqrt_nonneg _
  have hb : 0 ≤ lowBranch u := Real.sqrt_nonneg _
  have hs' := Real.sq_sqrt (show 0 ≤ (1 + u) / 2 by linarith [hu.1])
  have hn' := Real.sqrt_nonneg ((1 + u) / 2)
  have hp : 2 * highBranch u * lowBranch u = Real.sqrt ((1 + u) / 2) := by
    have hprod : (highBranch u * lowBranch u) ^ 2 = (1 + u) / 8 := by
      rw [mul_pow, hh, hl]
      nlinarith
    nlinarith [mul_nonneg ha hb]
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + Real.sqrt ((1 + u) / 2) by positivity)
  have hn := Real.sqrt_nonneg (1 + Real.sqrt ((1 + u) / 2))
  nlinarith

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_Trigonometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Polynomial Set Filter
open scoped Topology
theorem C_c_facts : 0 < c ∧ c < C ∧ C ^ 2 + c ^ 2 = 1 ∧
    C ^ 2 * (1 - C ^ 2) = 1 / 8 ∧ c ^ 2 * (1 - c ^ 2) = 1 / 8 ∧
    1 - 2 * C ^ 2 ≠ 0 ∧ 1 - 2 * c ^ 2 ≠ 0 := by
  have hh := branches_sq (u := (0 : ℝ)) (by constructor <;> norm_num)
  rw [highBranch_zero, lowBranch_zero] at hh
  simp only [sub_zero, sqrt_half] at hh
  have hC : 0 ≤ C := by rw [← highBranch_zero]; exact Real.sqrt_nonneg _
  have hc : 0 ≤ c := by rw [← lowBranch_zero]; exact Real.sqrt_nonneg _
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [sqrt_two_lt_two, hh.1, hh.2.1]

theorem harmonic_eval (b : ℝ) : harmonicCoordinate.eval b = b ^ 2 * (1 - b ^ 2) := by
  simp [harmonicCoordinate]

 

theorem branch_rescaled_tendsto {α : Type*} {l : Filter α} {z b : α → ℝ} {r : ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hb : Tendsto b l (𝓝 r))
    (hh : ∀ᶠ t in l, harmonicCoordinate.eval (b t) = (1 + 1 / z t) / 8)
    (hr : r ^ 2 * (1 - r ^ 2) = 1 / 8) (hrn : r ≠ 0) (hrd : 1 - 2 * r ^ 2 ≠ 0) :
    Tendsto (fun t => z t * (b t - r)) l (𝓝 ((1 / 8) / ((2 * r) * (1 - 2 * r ^ 2)))) := by
  have hd := (hb.add_const r).mul (((hb.pow 2).const_sub 1).sub_const (r ^ 2))
  have hdn : (r + r) * (1 - r ^ 2 - r ^ 2) ≠ 0 := by
    convert mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hrn) hrd using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have ht := (tendsto_const_nhds : Tendsto (fun _ : α => (1 / 8 : ℝ)) l (𝓝 (1 / 8))).div hd hdn
  have hs : (r + r) * (1 - r ^ 2 - r ^ 2) = (2 * r) * (1 - 2 * r ^ 2) := by ring
  rw [hs] at ht
  apply ht.congr'
  filter_upwards [hz, hh, hd.eventually_ne hdn] with t hzt hht hdt
  simp only [harmonic_eval] at hht
  apply (div_eq_iff hdt).2
  have hbase : (b t - r) * (b t + r) * (1 - b t ^ 2 - r ^ 2) = (1 / z t) / 8 := by
    nlinarith [hht, hr]
  calc (1 / 8 : ℝ) = z t * ((1 / z t) / 8) := by field_simp
       _ = z t * ((b t - r) * (b t + r) * (1 - b t ^ 2 - r ^ 2)) := by rw [hbase]
       _ = z t * (b t - r) * ((b t + r) * (1 - b t ^ 2 - r ^ 2)) := by ring

theorem eventually_small_inverse {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : Tendsto (fun t => 1 / z t) l (𝓝 0)) :
    ∀ᶠ t in l, 1 / z t ∈ Ioo (-1 : ℝ) 1 :=
  hz.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))

theorem highBranch_rescaled {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0)) :
    Tendsto (fun t => z t * (highBranch (1 / z t) - C)) l
      (𝓝 ((1 / 8) / ((2 * C) * (1 - 2 * C ^ 2)))) := by
  have hf := C_c_facts
  apply branch_rescaled_tendsto hz
    (by simpa only [highBranch_zero, Function.comp_def] using highBranch_continuous.continuousAt.tendsto.comp hi)
    ((eventually_small_inverse hi).mono fun _ ht => (branches_harmonic ht).1)
    hf.2.2.2.1 (ne_of_gt (lt_trans hf.1 hf.2.1)) hf.2.2.2.2.2.1

theorem lowBranch_rescaled {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0)) :
    Tendsto (fun t => z t * (lowBranch (1 / z t) - c)) l
      (𝓝 ((1 / 8) / ((2 * c) * (1 - 2 * c ^ 2)))) := by
  have hf := C_c_facts
  apply branch_rescaled_tendsto hz
    (by simpa only [lowBranch_zero, Function.comp_def] using lowBranch_continuous.continuousAt.tendsto.comp hi)
    ((eventually_small_inverse hi).mono fun _ ht => (branches_harmonic ht).2)
    hf.2.2.2.2.1 (ne_of_gt hf.1) hf.2.2.2.2.2.2

 
theorem lower_rescaling_zero {α : Type*} {l : Filter α} {z v : α → ℝ} {L : ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0))
    {k m : ℕ} (hkm : k < m) (hv : Tendsto (fun t => z t ^ m * v t) l (𝓝 L)) :
    Tendsto (fun t => z t ^ k * v t) l (𝓝 0) := by
  have hp := (hi.pow (m - k)).mul hv
  have hmk : m - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hkm)
  simp only [zero_pow hmk, zero_mul] at hp
  apply hp.congr'
  filter_upwards [hz] with t ht
  rw [one_div, inv_pow, pow_sub₀ (z t) ht hkm.le]
  field_simp

 

theorem homogeneousQ_high_decay {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0))
    (N : ℕ) (g : Polynomial ℝ) (k : ℕ) (hk : k < 2 * N + 1) :
    Tendsto (fun t => z t ^ k * (homogeneousQ N g).eval (highBranch (1 / z t))) l (𝓝 0) := by
  have hb : Tendsto (fun t => highBranch (1 / z t)) l (𝓝 C) := by
    simpa only [highBranch_zero, Function.comp_def] using highBranch_continuous.continuousAt.tendsto.comp hi
  have hscale := ((highBranch_rescaled hz hi).pow (2 * N + 1)).mul
    (((hb.sub_const c).pow N).mul (g.continuous.continuousAt.tendsto.comp hb))
  have hlim : Tendsto (fun t => z t ^ (2 * N + 1) *
      (homogeneousQ N g).eval (highBranch (1 / z t))) l
      (𝓝 (((1 / 8) / ((2 * C) * (1 - 2 * C ^ 2))) ^ (2 * N + 1) *
        ((C - c) ^ N * g.eval C))) := by
    apply hscale.congr'
    exact Eventually.of_forall fun t => by
      simp only [homogeneousQ, eval_mul, eval_pow, eval_sub, eval_C, eval_X, Function.comp_def, mul_pow]
      ring
  exact lower_rescaling_zero hz hi hk hlim

theorem homogeneousQ_low_limit {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0))
    (N : ℕ) (g : Polynomial ℝ) :
    ∃ L : ℝ, Tendsto (fun t => z t ^ N * (homogeneousQ N g).eval (lowBranch (1 / z t))) l (𝓝 L) := by
  have hb : Tendsto (fun t => lowBranch (1 / z t)) l (𝓝 c) := by
    simpa only [lowBranch_zero, Function.comp_def] using lowBranch_continuous.continuousAt.tendsto.comp hi
  have hscale := ((hb.sub_const C).pow (2 * N + 1)).mul
    (((lowBranch_rescaled hz hi).pow N).mul (g.continuous.continuousAt.tendsto.comp hb))
  refine ⟨_, hscale.congr' ?_⟩
  exact Eventually.of_forall fun t => by
    simp only [homogeneousQ, eval_mul, eval_pow, eval_sub, eval_C, eval_X, Function.comp_def, mul_pow]
    ring

 

theorem tilde_projection_eval (N : ℕ) (P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.natDegree ≤ N)
    {z b : ℝ} (hz : z ≠ 0) (hb : harmonicCoordinate.eval b = (1 + 1 / z) / 8) :
    (tildePoly N P).eval z + b * (tildePoly N J).eval z + b ^ 2 * (tildePoly N E).eval z =
      z ^ N * (P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
        X ^ 2 * E.comp harmonicCoordinate).eval b := by
  rw [tildePoly_eval N hP hz, tildePoly_eval N hJ hz, tildePoly_eval N hE hz]
  simp only [eval_add, eval_mul, eval_comp, eval_pow, eval_X, hb]
  ring

 

theorem tilde_F_decay (N : ℕ) (g P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.natDegree ≤ N)
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate) (j : ℕ) (hj : j ≤ N) :
    Tendsto (fun t : ℝ => (-t) ^ j * ((tildePoly N P).eval (-t) +
      highBranch (1 / (-t)) * (tildePoly N J).eval (-t) +
      highBranch (1 / (-t)) ^ 2 * (tildePoly N E).eval (-t))) atTop (𝓝 0) := by
  have hz : ∀ᶠ t : ℝ in atTop, -t ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact neg_ne_zero.mpr ht.ne'
  have hi : Tendsto (fun t : ℝ => 1 / (-t)) atTop (𝓝 0) := by
    simpa only [one_div, inv_neg, neg_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).neg
  apply (homogeneousQ_high_decay hz hi N g (N + j) (by omega)).congr'
  filter_upwards [hz, eventually_small_inverse hi] with t ht hs
  have he := tilde_projection_eval N P J E hP hJ hE ht (branches_harmonic hs).1
  rw [← hQ] at he
  rw [he, pow_add]
  ring

 
theorem tilde_D_limit (N : ℕ) (g P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.natDegree ≤ N)
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate) :
    ∃ L : ℝ, Tendsto (fun z : ℝ => (tildePoly N J).eval z +
      Real.sqrt (1 + Real.sqrt ((1 + 1 / z) / 2)) * (tildePoly N E).eval z) atTop (𝓝 L) := by
  have hz : ∀ᶠ z : ℝ in atTop, z ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact hz.ne'
  have hi : Tendsto (fun z : ℝ => 1 / z) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0))
  have hh : Tendsto (fun z : ℝ => highBranch (1 / z)) atTop (𝓝 C) := by
    simpa only [highBranch_zero, Function.comp_def] using highBranch_continuous.continuousAt.tendsto.comp hi
  have hl : Tendsto (fun z : ℝ => lowBranch (1 / z)) atTop (𝓝 c) := by
    simpa only [lowBranch_zero, Function.comp_def] using lowBranch_continuous.continuousAt.tendsto.comp hi
  have hdiff := hh.sub hl
  have hne : C - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt C_c_facts.2.1)
  obtain ⟨L, hL⟩ := homogeneousQ_low_limit hz hi N g
  have hhigh := homogeneousQ_high_decay hz hi N g N (by omega)
  refine ⟨(0 - L) / (C - c), ((hhigh.sub hL).div hdiff hne).congr' ?_⟩
  filter_upwards [hz, eventually_small_inverse hi, hdiff.eventually_ne hne] with z hzt hs hd
  apply (div_eq_iff hd).2
  rw [← branches_sum hs]
  have heh := tilde_projection_eval N P J E hP hJ hE hzt (branches_harmonic hs).1
  have hel := tilde_projection_eval N P J E hP hJ hE hzt (branches_harmonic hs).2
  rw [← hQ] at heh hel
  linear_combination -heh + hel

theorem harmonic_natDegree : harmonicCoordinate.natDegree = 4 := by
  unfold harmonicCoordinate
  compute_degree <;> norm_num

theorem degree_lt_natDegree_le_pred {N : ℕ} {p : Polynomial ℝ}
    (hN : 1 ≤ N) (hp : p.degree < (N : WithBot ℕ)) : p.natDegree ≤ N - 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have h : p.natDegree < N := (natDegree_lt_iff_degree_lt hp0).2 hp
  omega

 
theorem projection_natDegree_le (N : ℕ) (hN : 1 ≤ N) (P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ)) :
    (P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate).natDegree ≤ 4 * N + 1 := by
  have he := degree_lt_natDegree_le_pred hN hE
  have hp' : (P.comp harmonicCoordinate).natDegree ≤ 4 * N + 1 := by
    rw [natDegree_comp, harmonic_natDegree]
    omega
  have hj' : (X * J.comp harmonicCoordinate).natDegree ≤ 4 * N + 1 := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X, natDegree_comp, harmonic_natDegree]
    omega
  have he' : (X ^ 2 * E.comp harmonicCoordinate).natDegree ≤ 4 * N + 1 := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X_pow, natDegree_comp, harmonic_natDegree]
    omega
  exact le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _) (max_le hp' hj')) he')

 

theorem projection_J_degree_lt (N : ℕ) (hN : 1 ≤ N) (P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : (P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate).natDegree ≤ 4 * N) :
    J.degree < (N : WithBot ℕ) := by
  by_cases hJ0 : J = 0
  · simp [hJ0]
  apply (natDegree_lt_iff_degree_lt hJ0).1
  by_contra hj
  have hjN : J.natDegree = N := by omega
  have he := degree_lt_natDegree_le_pred hN hE
  let A : Polynomial ℝ := P.comp harmonicCoordinate + X ^ 2 * E.comp harmonicCoordinate
  have hp' : (P.comp harmonicCoordinate).natDegree ≤ 4 * N := by
    rw [natDegree_comp, harmonic_natDegree]
    omega
  have he' : (X ^ 2 * E.comp harmonicCoordinate).natDegree ≤ 4 * N := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X_pow, natDegree_comp, harmonic_natDegree]
    omega
  have ha : A.natDegree ≤ 4 * N := le_trans (natDegree_add_le _ _) (max_le hp' he')
  have hjcomp : J.comp harmonicCoordinate ≠ 0 := by
    intro h
    have hd := natDegree_comp (p := J) (q := harmonicCoordinate)
    rw [h, natDegree_zero, hjN, harmonic_natDegree] at hd
    omega
  have hb : (X * J.comp harmonicCoordinate).natDegree = 4 * N + 1 := by
    rw [natDegree_X_mul hjcomp, natDegree_comp, hjN, harmonic_natDegree]
    omega
  have hsum :
      (P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
        X ^ 2 * E.comp harmonicCoordinate).natDegree = 4 * N + 1 := by
    have heq : P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
        X ^ 2 * E.comp harmonicCoordinate = A + X * J.comp harmonicCoordinate := by
      dsimp [A]
      ring
    rw [heq, natDegree_add_eq_right_of_natDegree_lt (by rw [hb]; omega), hb]
  omega

theorem homogeneousQ_lower_degree (N : ℕ) (hN : 1 ≤ N) {g : Polynomial ℝ}
    (hg : g.degree < (N : WithBot ℕ)) : (homogeneousQ N g).natDegree ≤ 4 * N := by
  have hg' := degree_lt_natDegree_le_pred hN hg
  have h := natDegree_mul_le (p := (X - Polynomial.C C) ^ (2 * N + 1) *
    (X - Polynomial.C c) ^ N) (q := g)
  have h' := natDegree_mul_le (p := (X - Polynomial.C C) ^ (2 * N + 1))
    (q := (X - Polynomial.C c) ^ N)
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one] at h'
  exact le_trans h (by omega)

end

noncomputable section
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators

 
theorem stieltjes_polynomial_basis (N : ℕ) (e : Polynomial ℝ) (he : e.natDegree < N)
    {z : ℝ} (hz : 0 < z) :
    z * realStieltjes (-1) (fun y => e.eval (-y) * omega y) z =
      ∑ k : Fin N, (e.coeff k.val * (-1) ^ k.val) * transformedBasis k.val z := by
  have hev (y : ℝ) : e.eval (-y) =
      ∑ k : Fin N, (e.coeff k.val * (-1) ^ k.val) * y ^ k.val := by
    rw [eval_eq_sum_range' he, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  have heq : (fun y => z * (e.eval (-y) * omega y / (z - (-1) * y))) =
      fun y => ∑ k : Fin N, (e.coeff k.val * (-1) ^ k.val) *
        (boundedCauchy z y * momentBasis k.val y) := by
    funext y
    rw [hev]
    simp only [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold boundedCauchy momentBasis
    ring
  rw [realStieltjes, ← integral_const_mul, heq, integral_finsetSum]
  · simp only [integral_const_mul, transformedBasis]
  · intro k _
    exact (integrableOn_boundedCauchy_basis k.val hz).const_mul _

 

theorem homogeneous_projection_zero (N : ℕ) (hN : 1 ≤ N) (g P J E : Polynomial ℝ)
    (hg : g.degree < (N : WithBot ℕ))
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate) :
    P = 0 ∧ J = 0 ∧ E = 0 ∧ g = 0 := by
  have hEn : E.natDegree ≤ N := (degree_lt_natDegree_le_pred hN hE).trans (Nat.sub_le _ _)
  have hJl : J.degree < (N : WithBot ℕ) := projection_J_degree_lt N hN P J E hP hJ hE
    (by rw [← hQ]; exact homogeneousQ_lower_degree N hN hg)
  have htJ0 := tildePoly_zero_of_degree_lt N hJl
  have htE0 := tildePoly_zero_of_degree_lt N hE
  have hdiv : X ∣ tildePoly N E := X_dvd_iff.2 (by simpa only [coeff_zero_eq_eval_zero] using htE0)
  obtain ⟨e, he⟩ := hdiv
  have hen : e.natDegree < N := by
    by_cases he0 : e = 0
    · simp [he0]; omega
    have hb := tildePoly_natDegree_le N hEn
    rw [he, natDegree_X_mul he0] at hb
    omega
  have hF : ∀ j : ℕ, j ≤ N → Tendsto
      (fun t : ℝ => (-t) ^ j * projectionF (tildePoly N P) (tildePoly N J) (tildePoly N E) (-t))
      atTop (𝓝 0) := by
    intro j hj
    exact tilde_F_decay N g P J E hP hJ hEn hQ j hj
  obtain ⟨L, hD⟩ := tilde_D_limit N g P J E hP hJ hEn hQ
  change Tendsto (fun z : ℝ => projectionD (tildePoly N J) (tildePoly N E) z) atTop (𝓝 L) at hD
  have hDc := projectionD_cauchy (tildePoly N J) e (by simpa only [← he] using hD)
  have hm := projection_moments_of_decay N (tildePoly N P) (tildePoly N J) (tildePoly N E) hF
  let v : Fin N → ℝ := fun k => -(Real.sqrt 2 / Real.pi) * (e.coeff k.val * (-1) ^ k.val)
  have hDv {z : ℝ} (hz : 0 < z) :
      projectionD (tildePoly N J) (tildePoly N E) z = cauchyDefect N 0 v z := by
    rw [he, hDc z hz, htJ0, zero_add, mul_assoc, stieltjes_polynomial_basis N e hen hz]
    simp only [cauchyDefect, zero_sub, v, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, neg_neg]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hv : CauchyMomentProblem N 0 v := by
    intro j
    calc
      (∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x * cauchyDefect N 0 v x) =
          ∫ x in Ioo (0 : ℝ) 1, x ^ j.val * (projectionD (tildePoly N J) (tildePoly N E) x * omega x) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx
        dsimp only
        rw [hDv hx.1]
        unfold momentBasis
        ring
      _ = 0 := hm j.val j.isLt
  have hv0 := cauchyMomentProblem_zero hv
  have he0 : e = 0 := by
    ext k
    rw [coeff_zero]
    by_cases hk : k < N
    · have hvk := congrFun hv0 (⟨k, hk⟩ : Fin N)
      dsimp [v] at hvk
      have hs : -(Real.sqrt 2 / Real.pi) ≠ 0 := neg_ne_zero.mpr
        (div_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)) Real.pi_ne_zero)
      have hc := (mul_eq_zero.mp hvk).resolve_left hs
      exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ (by norm_num))
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hE0 : E = 0 := (tildePoly_eq_zero_iff N E).1 (by simpa only [he0, mul_zero] using he)
  have htE : tildePoly N E = 0 := (tildePoly_eq_zero_iff N E).2 hE0
  have htJ : tildePoly N J = 0 := by
    have hJlim : Tendsto (fun z : ℝ => (tildePoly N J).eval z) atTop (𝓝 L) := by
      simpa only [htE, projectionD, eval_zero, mul_zero, add_zero] using hD
    have hc := polynomial_constant_of_limit tendsto_norm_atTop_atTop (tildePoly N J) hJlim
    have hL : L = 0 := by simpa only [hc, eval_C] using htJ0
    simpa only [hL, C_0] using hc
  have htP : tildePoly N P = 0 := by
    have hPlim : Tendsto (fun t : ℝ => (tildePoly N P).eval (-t)) atTop (𝓝 0) := by
      simpa only [htJ, htE, projectionF, eval_zero, mul_zero, add_zero, pow_zero, one_mul] using hF 0 (Nat.zero_le N)
    simpa only [C_0] using polynomial_constant_of_limit norm_neg_atTop (tildePoly N P) hPlim
  have hP0 := (tildePoly_eq_zero_iff N P).1 htP
  have hJ0 := (tildePoly_eq_zero_iff N J).1 htJ
  refine ⟨hP0, hJ0, hE0, ?_⟩
  have hQ0 : homogeneousQ N g = 0 := by simp [hQ, hP0, hJ0, hE0]
  have hroot : (X - Polynomial.C C) ^ (2 * N + 1) * (X - Polynomial.C c) ^ N ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _))
  exact (mul_eq_zero.1 hQ0).resolve_left hroot



theorem projectionSpace_finrank (N : ℕ) : Module.finrank ℝ (ProjectionSpace N) = 3 * N + 2 := by
  simp only [ProjectionSpace, Module.finrank_prod,
    Module.finrank_eq_card_basis (degreeLT.basis ℝ (N + 1)),
    Module.finrank_eq_card_basis (degreeLT.basis ℝ N), Fintype.card_fin]
  omega

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PolynomialDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/

namespace CriticalStrip
noncomputable section
section ProjectionAlgebra
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators
theorem natDegree_le_of_mem_degreeLT {N : ℕ} {p : Polynomial ℝ}
    (hp : p ∈ degreeLT ℝ (N + 1)) : p.natDegree ≤ N := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact Nat.lt_succ_iff.1 ((natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp))

 

theorem homogeneous_exists_degree (N : ℕ) (hN : 1 ≤ N) :
    ∃ g : Polynomial ℝ, g ≠ 0 ∧ g.natDegree = N ∧ HasProjection N (homogeneousQ N g) := by
  have hdim : Module.finrank ℝ (degreeLT ℝ (3 * N + 1)) < Module.finrank ℝ (ProjectionSpace N) := by
    rw [Module.finrank_eq_card_basis (degreeLT.basis ℝ (3 * N + 1)), Fintype.card_fin,
      projectionSpace_finrank]
    omega
  obtain ⟨t, ht, htne⟩ := (Submodule.ne_bot_iff _).1
    (LinearMap.ker_ne_bot_of_finrank_lt (f := projectionRemainder N) hdim)
  have ht0 : projectionMap N t %ₘ rootPolynomial N = 0 := by
    have hv := congrArg Subtype.val (LinearMap.mem_ker.1 ht)
    exact hv
  obtain ⟨g, hg⟩ := (modByMonic_eq_zero_iff_dvd (rootPolynomial_monic N)).1 ht0
  have hP : t.1.val.natDegree ≤ N := natDegree_le_of_mem_degreeLT t.1.property
  have hJ : t.2.1.val.natDegree ≤ N := natDegree_le_of_mem_degreeLT t.2.1.property
  have hE : t.2.2.val.degree < (N : WithBot ℕ) := mem_degreeLT.1 t.2.2.property
  have hQ : homogeneousQ N g = t.1.val.comp harmonicCoordinate + X * t.2.1.val.comp harmonicCoordinate +
      X ^ 2 * t.2.2.val.comp harmonicCoordinate := hg.symm
  have hg0 : g ≠ 0 := by
    intro hzero
    have hz := homogeneous_projection_zero N hN g t.1.val t.2.1.val t.2.2.val
      (by simp [hzero]) hP hJ hE hQ
    apply htne
    apply Prod.ext
    · exact Subtype.ext hz.1
    · exact Prod.ext (Subtype.ext hz.2.1) (Subtype.ext hz.2.2.1)
  have hgn : g.natDegree ≤ N := by
    have hd := projection_natDegree_le N hN t.1.val t.2.1.val t.2.2.val hP hJ hE
    rw [← hQ] at hd
    change (rootPolynomial N * g).natDegree ≤ 4 * N + 1 at hd
    rw [natDegree_mul (rootPolynomial_monic N).ne_zero hg0, rootPolynomial_natDegree] at hd
    omega
  have hgeq : g.natDegree = N := by
    by_contra hne
    have hgl : g.degree < (N : WithBot ℕ) := (natDegree_lt_iff_degree_lt hg0).1 (by omega)
    exact hg0 (homogeneous_projection_zero N hN g t.1.val t.2.1.val t.2.2.val
      hgl hP hJ hE hQ).2.2.2
  exact ⟨g, hg0, hgeq, ⟨t.1.val, t.2.1.val, t.2.2.val, hP, hJ, hE, hQ⟩⟩



 theorem HasProjection.smul {N : ℕ} {Q : Polynomial ℝ} (hQ : HasProjection N Q) (a : ℝ) :
    HasProjection N (a • Q) := by
  obtain ⟨P, J, E, hP, hJ, hE, he⟩ := hQ
  refine ⟨a • P, a • J, a • E, ?_, ?_, (degree_smul_le a E).trans_lt hE, ?_⟩
  · exact (natDegree_smul_le a P).trans hP
  · exact (natDegree_smul_le a J).trans hJ
  · simp only [he, smul_add, smul_comp, mul_smul_comm]

 theorem HasProjection.sub {N : ℕ} {Q R : Polynomial ℝ}
    (hQ : HasProjection N Q) (hR : HasProjection N R) : HasProjection N (Q - R) := by
  obtain ⟨P, J, E, hP, hJ, hE, he⟩ := hQ
  obtain ⟨P', J', E', hP', hJ', hE', he'⟩ := hR
  refine ⟨P-P', J-J', E-E', (natDegree_sub_le _ _).trans (max_le hP hP'),
    (natDegree_sub_le _ _).trans (max_le hJ hJ'),
    (degree_sub_le _ _).trans_lt (max_lt hE hE'), ?_⟩
  simp only [he, he', sub_comp]
  ring

 

theorem homogeneous_monic_unique (N : ℕ) (hN : 1 ≤ N) :
    ∃! g : Polynomial ℝ, MonicProblem N g := by
  obtain ⟨q, hq0, hqn, hqproj⟩ := homogeneous_exists_degree N hN
  let g := q.leadingCoeff⁻¹ • q
  have hgmonic : g.Monic := by
    simpa only [g, smul_eq_C_mul, mul_comm] using monic_mul_leadingCoeff_inv hq0
  have hgdeg : g.natDegree = N := by
    change (q.leadingCoeff⁻¹ • q).natDegree = N
    rw [natDegree_smul q (inv_ne_zero (leadingCoeff_ne_zero.mpr hq0)), hqn]
  have hgproj : HasProjection N (homogeneousQ N g) := by
    convert hqproj.smul q.leadingCoeff⁻¹ using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g, homogeneousQ, mul_smul_comm]
  have hg : MonicProblem N g := ⟨hgmonic, hgdeg, hgproj⟩
  refine ⟨g, hg, ?_⟩
  intro p hp
  have hd : p.degree = (N : WithBot ℕ) := by rw [degree_eq_natDegree hp.1.ne_zero, hp.2.1]
  have hdg : g.degree = (N : WithBot ℕ) := by rw [degree_eq_natDegree hgmonic.ne_zero, hgdeg]
  have hl : (p - g).degree < (N : WithBot ℕ) := by
    simpa only [hd] using degree_sub_lt_left (hd.trans hdg.symm) hp.1.ne_zero (hp.1.trans hgmonic.symm)
  have hproj : HasProjection N (homogeneousQ N (p - g)) := by
    simpa only [homogeneousQ, mul_sub] using hp.2.2.sub hgproj
  obtain ⟨P, J, E, hP, hJ, hE, hQ⟩ := hproj
  exact sub_eq_zero.mp (homogeneous_projection_zero N hN (p - g) P J E hl hP hJ hE hQ).2.2.2

end ProjectionAlgebra

open Polynomial Set MeasureTheory Filter _root_.Matrix
open scoped Topology BigOperators



theorem paired_homogeneous :
    X^2 - Polynomial.C (2*d*C)*X + Polynomial.C (C^2-d^2) =
      (X - Polynomial.C C)*(X-Polynomial.C c) := by
  have ha := Real.cos_add (2*lambda) lambda
  have hs := Real.cos_sub (2*lambda) lambda
  rw [show 2*lambda+lambda=3*Real.pi/8 by unfold lambda; ring] at ha
  rw [show 2*lambda-lambda=lambda by ring] at hs
  change c = d*C - Real.sin (2*lambda)*Real.sin lambda at ha
  change C = d*C + Real.sin (2*lambda)*Real.sin lambda at hs
  have hc : c+C=2*d*C := by linarith
  have hd : d = Real.sqrt 2 / 2 := by
    rw [d, lambda, show 2*(Real.pi/8)=Real.pi/4 by ring, Real.cos_pi_div_four]
  have hd2 : d^2 = 1/2 := by rw [hd]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hC2 : C^2=(1+d)/2 := by
    have hh := Real.cos_two_mul lambda
    change d = 2*C^2-1 at hh
    linarith
  have hprod : C^2-d^2=C*c := by
    have hh : c=(2*d-1)*C := by nlinarith [hc]
    rw [hh]
    nlinarith [hC2, hd2, mul_assoc d (C^2) 2]
  rw [← hc, hprod, map_add, map_mul]
  ring

 theorem perturbedRoot_homogeneous (N : ℕ) :
    perturbedRoot (fun _ : Fin N => C) = rootPolynomial N := by
  simp only [perturbedRoot, paired_homogeneous, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [rootPolynomial, mul_pow, mul_pow]
  rw [show 2*N+1=N+N+1 by omega, pow_add, pow_add]
  ring

end
end CriticalStrip


end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SpectralComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripComplexification
noncomputable section
open Polynomial
open scoped BigOperators
lemma component_comp (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) (q : Polynomial ℝ) :
    component l (p.comp (q.map Complex.ofRealHom)) = (component l p).comp q := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [add_comp, component_add, hp, hr]
  | monomial n c =>
      have hm : (monomial n c : Polynomial ℂ) = C c * X ^ n := C_mul_X_pow_eq_monomial.symm
      rw [hm, mul_comp, C_comp, pow_comp, X_comp]
      rw [mul_comm, ← Polynomial.map_pow, component_real_mul, component_C]
      have hX : (X ^ n : Polynomial ℂ) = (X ^ n : Polynomial ℝ).map Complex.ofRealHom := by simp
      rw [mul_comm (C c), hX, component_real_mul, component_C]
      simp only [mul_comp, pow_comp, X_comp, C_comp]

lemma component_projection (l : ℂ →ₗ[ℝ] ℝ) (P J E : Polynomial ℂ) (h : Polynomial ℝ) :
    component l (P.comp (h.map Complex.ofRealHom) + X * J.comp (h.map Complex.ofRealHom) +
      X ^ 2 * E.comp (h.map Complex.ofRealHom)) =
    (component l P).comp h + X * (component l J).comp h +
      X ^ 2 * (component l E).comp h := by
  rw [component_add, component_add, component_comp]
  have hx : (X : Polynomial ℂ) = (X : Polynomial ℝ).map Complex.ofRealHom := by simp
  have hx2 : (X ^ 2 : Polynomial ℂ) = (X ^ 2 : Polynomial ℝ).map Complex.ofRealHom := by simp
  rw [hx2, component_real_mul, component_comp, hx, component_real_mul, component_comp]

lemma component_degree_le (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) :
    (component l p).degree ≤ p.degree := by
  apply (degree_le_iff_coeff_zero _ _).2
  intro n hn
  simp [coeff_eq_zero_of_degree_lt hn]

lemma component_natDegree_le (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) :
    (component l p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.2
  intro n hn
  simp [coeff_eq_zero_of_natDegree_lt hn]

lemma component_zero_iff (p : Polynomial ℂ)
    (hr : component Complex.reLm p = 0) (hi : component Complex.imLm p = 0) : p = 0 := by
  ext n
  apply Complex.ext
  · simpa using congrArg (fun q : Polynomial ℝ => q.coeff n) hr
  · simpa using congrArg (fun q : Polynomial ℝ => q.coeff n) hi

end
end StripComplexification

namespace StripPfaffian
noncomputable section
open Polynomial Set MeasureTheory Filter _root_.Matrix StripComplexification
open scoped Topology BigOperators

lemma map_harmonic : CriticalStrip.harmonicCoordinate.map Complex.ofRealHom = harmonicPoly := by
  simp [CriticalStrip.harmonicCoordinate, harmonicPoly]

lemma map_perturbedRoot {N : ℕ} (a : Fin N → ℝ) :
    (CriticalStrip.perturbedRoot a).map Complex.ofRealHom =
      perturbedRootC (fun i => (a i : ℂ)) := by
  simp [CriticalStrip.perturbedRoot, perturbedRootC, Epoly, Polynomial.map_prod,
    CriticalStrip.C, CriticalStrip.d, CriticalStrip.lambda, flatC, d]

lemma perturbedRoot_homogeneous (N : ℕ) : perturbedRootC (fun _ : Fin N => flatC) = rootPolynomialC N := by
  change perturbedRootC (fun _ : Fin N => (CriticalStrip.C : ℂ)) = _
  rw [← map_perturbedRoot, CriticalStrip.perturbedRoot_homogeneous]
  rfl

lemma homogeneous_projection_zero_complex (N : ℕ) (hN : 1 ≤ N) (g P J E : Polynomial ℂ)
    (hg : g.degree < (N : WithBot ℕ))
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : homogeneousQC N g = P.comp harmonicPoly + X * J.comp harmonicPoly +
      X ^ 2 * E.comp harmonicPoly) :
    P = 0 ∧ J = 0 ∧ E = 0 ∧ g = 0 := by
  have hl (l : ℂ →ₗ[ℝ] ℝ) : component l P = 0 ∧ component l J = 0 ∧
      component l E = 0 ∧ component l g = 0 := by
    apply CriticalStrip.homogeneous_projection_zero N hN
      (component l g) (component l P) (component l J) (component l E)
      ((component_degree_le l g).trans_lt hg)
      ((component_natDegree_le l P).trans hP)
      ((component_natDegree_le l J).trans hJ)
      ((component_degree_le l E).trans_lt hE)
    have he := congrArg (component l) hQ
    rw [homogeneousQC, rootPolynomialC, component_real_mul, ← map_harmonic,
      component_projection] at he
    exact he
  have hr := hl Complex.reLm
  have hi := hl Complex.imLm
  exact ⟨component_zero_iff P hr.1 hi.1,
    component_zero_iff J hr.2.1 hi.2.1,
    component_zero_iff E hr.2.2.1 hi.2.2.1,
    component_zero_iff g hr.2.2.2 hi.2.2.2⟩

theorem homogeneous_system_injective (N : ℕ) (hN : 1 ≤ N) :
    Function.Injective (perturbedSystem hN (fun _ => flatC)) := by
  apply (LinearMap.ker_eq_bot).1
  apply LinearMap.ker_eq_bot'.2
  intro t ht
  have he : homogeneousQC N t.2.val = projectionMap N t.1 := by
    have he := congrArg Subtype.val ht
    change projectionMap N t.1 - perturbedRootC (fun _ => flatC)*t.2.val=0 at he
    rw [perturbedRoot_homogeneous] at he
    exact (sub_eq_zero.mp he).symm
  have hz := homogeneous_projection_zero_complex N hN t.2.val t.1.1.val t.1.2.1.val t.1.2.2.val
    (mem_degreeLT.1 t.2.property) (natDegree_le_of_mem_degreeLT t.1.1.property)
    (natDegree_le_of_mem_degreeLT t.1.2.1.property) (mem_degreeLT.1 t.1.2.2.property) he
  exact Prod.ext (Prod.ext (Subtype.ext hz.1) (Prod.ext (Subtype.ext hz.2.1) (Subtype.ext hz.2.2.1)))
    (Subtype.ext hz.2.2.2)

theorem CoeffContinuous.const {A : Type*} [TopologicalSpace A] (p : Polynomial ℂ) :
    CoeffContinuous (fun _ : A => p) := fun _ => continuous_const
theorem CoeffContinuous.C {A : Type*} [TopologicalSpace A] {f : A → ℂ} (hf : Continuous f) :
    CoeffContinuous (fun a => Polynomial.C (f a)) := by
  intro k
  simp only [coeff_C]
  split_ifs <;> fun_prop
theorem CoeffContinuous.add {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℂ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a+q a) := by
  intro k
  simp only [coeff_add]
  exact (hp k).add (hq k)
theorem CoeffContinuous.sub {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℂ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a-q a) := by
  intro k
  simp only [coeff_sub]
  exact (hp k).sub (hq k)
theorem CoeffContinuous.mul {A : Type*} [TopologicalSpace A] {p q : A → Polynomial ℂ}
    (hp : CoeffContinuous p) (hq : CoeffContinuous q) : CoeffContinuous (fun a => p a*q a) := by
  intro k
  simp only [coeff_mul]
  exact continuous_finsetSum _ (fun ij _ => (hp ij.1).mul (hq ij.2))
theorem CoeffContinuous.prod {A I : Type*} [TopologicalSpace A] (s : Finset I)
    {p : I → A → Polynomial ℂ} (hp : ∀ i ∈ s, CoeffContinuous (p i)) :
    CoeffContinuous (fun a => ∏ i ∈ s, p i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffContinuous.const (1 : Polynomial ℂ)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))
theorem perturbedRootC_continuous (N : ℕ) : CoeffContinuous (@perturbedRootC N) := by
  apply (CoeffContinuous.const (X-Polynomial.C flatC)).mul
  apply CoeffContinuous.prod
  intro i _
  apply ((CoeffContinuous.const X).sub (CoeffContinuous.C (continuous_apply i))).mul
  apply CoeffContinuous.add
  · exact (CoeffContinuous.const (X^2)).sub ((CoeffContinuous.C (by fun_prop)).mul (CoeffContinuous.const X))
  · exact CoeffContinuous.C (by fun_prop)

theorem target_repr (N : ℕ) (p : degreeLT ℂ (4*N+2)) (i : SystemIndex N) :
    (targetBasis N).repr p i = p.val.coeff (systemIndexEquiv N i) := by
  simp only [targetBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm, degreeLT.basis_repr]
theorem systemMatrix_continuous {N : ℕ} (hN : 1 ≤ N) : Continuous (systemMatrix hN) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [systemMatrix, LinearMap.toMatrix_apply, target_repr]
  exact ((CoeffContinuous.const (projectionMap N (systemBasis N j).1)).sub
    ((perturbedRootC_continuous N).mul (CoeffContinuous.const (systemBasis N j).2.val))) _

theorem systemMatrix_homogeneous_unit {N : ℕ} (hN : 1 ≤ N) :
    IsUnit (systemMatrix hN (fun _ => flatC)).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).1
  apply Matrix.mulVec_injective_iff_isUnit.1
  intro v w he
  let b := systemBasis N
  let bv := b.equivFun.symm v
  let bw := b.equivFun.symm w
  have hrepr (x : SystemSpace N) : systemMatrix hN (fun _ => flatC) *ᵥ b.equivFun x =
      (targetBasis N).equivFun (perturbedSystem hN (fun _ => flatC) x) :=
    LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hve : b.equivFun bv = v := b.equivFun.apply_symm_apply v
  have hwe : b.equivFun bw = w := b.equivFun.apply_symm_apply w
  rw [← hve, ← hwe, hrepr, hrepr] at he
  have heq := (homogeneous_system_injective N hN) ((targetBasis N).equivFun.injective he)
  exact hve.symm.trans ((congrArg b.equivFun heq).trans hwe)

theorem rhsVector_continuous (N : ℕ) : Continuous (@rhsVector N) := by
  apply continuous_pi
  intro i
  simp only [rhsVector, Module.Basis.equivFun_apply, target_repr]
  exact ((perturbedRootC_continuous N).mul (CoeffContinuous.const (X^N))) _

theorem solutionVector_continuousAt {N : ℕ} (hN : 1 ≤ N) :
    ContinuousAt (solutionVector hN) (fun _ => flatC) := by
  have hd := isUnit_iff_ne_zero.1 (systemMatrix_homogeneous_unit hN)
  have hi : ContinuousAt (fun a => (systemMatrix hN a)⁻¹) (fun _ => flatC) := by
    apply ContinuousAt.comp ?_ (systemMatrix_continuous hN).continuousAt
    apply continuousAt_matrix_inv
    simpa only [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext Ring.inverse_eq_inv] using continuousAt_inv₀ hd
  apply continuousAt_pi.2
  intro i
  change ContinuousAt (fun a => ∑ j, (systemMatrix hN a)⁻¹ i j * rhsVector a j) _
  apply tendsto_finsetSum
  intro j _
  exact (((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hi))).mul
    ((continuous_apply j).continuousAt.comp (rhsVector_continuous N).continuousAt)

theorem confluentPolynomial_continuousAt {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ContinuousAt (fun a => (confluentPolynomial hN a).coeff k) (fun _ => flatC) := by
  simp only [confluentPolynomial, solutionTuple, Module.Basis.equivFun_symm_apply,
    Prod.snd_sum, Prod.smul_snd, Submodule.coe_sum, Submodule.coe_smul, coeff_add, finsetSum_coeff, coeff_smul, smul_eq_mul]
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro i _
  exact ((continuous_apply i).continuousAt.comp (solutionVector_continuousAt hN)).mul continuousAt_const

theorem solutionTuple_spec {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ)
    (ha : IsUnit (systemMatrix hN a).det) :
    perturbedSystem hN a (solutionTuple hN a) = systemRHS a := by
  apply (targetBasis N).equivFun.injective
  simp only [Module.Basis.equivFun_apply]
  rw [← LinearMap.toMatrix_mulVec_repr (systemBasis N) (targetBasis N) (perturbedSystem hN a)]
  change systemMatrix hN a *ᵥ (systemBasis N).equivFun (solutionTuple hN a) = rhsVector a
  rw [solutionTuple, LinearEquiv.apply_symm_apply]
  rw [solutionVector, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ha, Matrix.one_mulVec]

theorem confluentPolynomial_spec {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ)
    (ha : IsUnit (systemMatrix hN a).det) : PerturbedMonicProblemC a (confluentPolynomial hN a) := by
  let t := solutionTuple hN a
  have hlow : t.2.val.degree < (N : WithBot ℕ) := mem_degreeLT.1 t.2.property
  refine ⟨monic_X_pow_add hlow, ?_, ?_⟩
  · apply natDegree_eq_of_degree_eq_some
    simpa only [degree_X_pow, confluentPolynomial, t] using degree_add_eq_left_of_degree_lt (p := (X : Polynomial ℂ)^N) (q := t.2.val)
      (by simpa only [degree_X_pow] using hlow)
  · refine ⟨t.1.1.val, t.1.2.1.val, t.1.2.2.val,
      natDegree_le_of_mem_degreeLT t.1.1.property, natDegree_le_of_mem_degreeLT t.1.2.1.property,
      mem_degreeLT.1 t.1.2.2.property, ?_⟩
    have he := congrArg Subtype.val (solutionTuple_spec hN a ha)
    change projectionMap N t.1-perturbedRootC a*t.2.val=perturbedRootC a*X^N at he
    change perturbedRootC a*(X^N+t.2.val)=projectionMap N t.1
    linear_combination -he

theorem perturbed_unique {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ)
    (ha : IsUnit (systemMatrix hN a).det) (p : Polynomial ℂ) (hp : PerturbedMonicProblemC a p) :
    p = confluentPolynomial hN a := by
  obtain ⟨hpmonic, hpN, P,J,E,hP,hJ,hE,hQ⟩ := hp
  have hpdeg : p.degree = (N : WithBot ℕ) := by rw [degree_eq_natDegree hpmonic.ne_zero, hpN]
  have hlow : (p-X^N).degree < (N : WithBot ℕ) := by
    simpa only [hpdeg] using degree_sub_lt_left
      (p := p) (q := (X : Polynomial ℂ)^N) (by simpa only [degree_X_pow] using hpdeg)
      hpmonic.ne_zero (hpmonic.trans (monic_X_pow N).symm)
  let t : SystemSpace N := ((⟨P,mem_degreeLT.2 (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hP))⟩,
    ⟨J,mem_degreeLT.2 (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hJ))⟩,
    ⟨E,mem_degreeLT.2 hE⟩), ⟨p-X^N,mem_degreeLT.2 hlow⟩)
  have he : perturbedSystem hN a t = systemRHS a := by
    apply Subtype.ext
    change P.comp harmonicPoly+X*J.comp harmonicPoly+X^2*E.comp harmonicPoly-
      perturbedRootC a*(p-X^N)=perturbedRootC a*X^N
    linear_combination -hQ
  have hinj : Function.Injective (perturbedSystem hN a) := by
    intro x y hxy
    apply (systemBasis N).equivFun.injective
    apply (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 ha))
    change systemMatrix hN a *ᵥ (systemBasis N).repr x = systemMatrix hN a *ᵥ (systemBasis N).repr y
    rw [systemMatrix, LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_mulVec_repr, hxy]
  have ht : t=solutionTuple hN a := hinj (he.trans (solutionTuple_spec hN a ha).symm)
  have hlast := congrArg (fun t : SystemSpace N => t.2.val) ht
  change p-X^N=(solutionTuple hN a).2.val at hlast
  rw [confluentPolynomial, ← hlast]
  ring

lemma real_monic_problem_map {N : ℕ} {g : Polynomial ℝ}
    (hg : CriticalStrip.MonicProblem N g) :
    PerturbedMonicProblemC (fun _ : Fin N => flatC) (g.map Complex.ofRealHom) := by
  obtain ⟨hgm,hgn,P,J,E,hP,hJ,hE,hQ⟩ := hg
  refine ⟨hgm.map _, ?_, P.map Complex.ofRealHom, J.map Complex.ofRealHom,
    E.map Complex.ofRealHom, natDegree_map_le.trans hP, natDegree_map_le.trans hJ,
    degree_map_le.trans_lt hE, ?_⟩
  · rw [natDegree_map_of_leadingCoeff_ne_zero _ (by rw [hgm]; simp), hgn]
  · have he := congrArg (Polynomial.map Complex.ofRealHom) hQ
    rw [CriticalStrip.homogeneousQ] at he
    rw [perturbedRoot_homogeneous, rootPolynomialC, CriticalStrip.rootPolynomial]
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, Polynomial.map_add, Polynomial.map_comp,
      map_harmonic] using he

 

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianConfluentLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open Polynomial Set MeasureTheory Filter _root_.Matrix StripComplexification
open scoped Topology BigOperators
theorem pfaffian_confluent_limit (N : ℕ) (hN : 1 ≤ N) :
    ∃ g₀ : Polynomial ℝ, CriticalStrip.MonicProblem N g₀ ∧
      (∀ p, CriticalStrip.MonicProblem N p → p = g₀) ∧
      ∃ g : (Fin N → ℂ) → Polynomial ℂ,
        g (fun _ => flatC) = g₀.map Complex.ofRealHom ∧
        (∀ k : ℕ, ContinuousAt (fun a => (g a).coeff k) (fun _ => flatC)) ∧
        ∀ᶠ a in 𝓝 (fun _ : Fin N => flatC),
          (g a).Monic ∧ (g a).natDegree = N ∧
          ∀ (_ : Function.Injective a)
            (_ : ∀ i j, i ≠ j → D (a i) (a j) ≠ 0)
            (_ : p N a ≠ 0) (z : ℂ),
            (∀ i, z ≠ a i ∧ D (a i) z ≠ 0) →
              (g a).eval z = p (N + 1) (Fin.snoc a z) / p N a := by
  obtain ⟨g₀, hg₀, huniq⟩ := CriticalStrip.homogeneous_monic_unique N hN
  refine ⟨g₀,hg₀,huniq,confluentPolynomial hN, ?_,
    confluentPolynomial_continuousAt hN, ?_⟩
  · exact (perturbed_unique hN _ (systemMatrix_homogeneous_unit hN) _
      (real_monic_problem_map hg₀)).symm
  · have hd := (systemMatrix_continuous hN).matrix_det.continuousAt.eventually_ne
      (isUnit_iff_ne_zero.1 (systemMatrix_homogeneous_unit hN))
    filter_upwards [hd] with a ha
    have hu := isUnit_iff_ne_zero.2 ha
    have hg := confluentPolynomial_spec hN a hu
    refine ⟨hg.1,hg.2.1, ?_⟩
    intro hinj hD hp z hz
    obtain ⟨g,hgm,hgn,hproj,hge⟩ := generic_pfaffian_projection N a hinj hD hp
    have he := perturbed_unique hN a hu g ⟨hgm,hgn,hproj⟩
    rw [← he]
    exact hge z hz

end
end StripPfaffian


end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InverseIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace StripPfaffian

noncomputable section
open scoped BigOperators

@[simp] lemma pfaffian_empty (A : Matrix (Fin 0) (Fin 0) ℂ) : pfaffian 0 A = 1 := by
  have h := topCoord_topWedge 0
  simpa [topCoord, topWedge, ExteriorAlgebra.ιMulti_zero_apply, pfaffian,
    Module.Basis.coord_apply] using h


end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SchurIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma sum_pow_list {ι E : Type*} [Fintype ι] [Semiring E] (f : ι → E) (m : ℕ) :
    (∑ i, f i) ^ m = ∑ v : Fin m → ι, (List.ofFn (fun j => f (v j))).prod := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih, Finset.mul_sum]
    conv_lhs => simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← Fintype.sum_prod_type (f := fun p : ι × (Fin m → ι) =>
      f p.1 * (List.ofFn (fun j => f (p.2 j))).prod)]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => ι))
    intro p
    simp [List.ofFn_succ, Fin.consEquiv]

lemma ofFn_smul_prod {n m : ℕ} (s : Fin m → ℂ) (v : Fin m → Grassmann n) :
    (List.ofFn (fun i => s i • v i)).prod =
      (∏ i, s i) • (List.ofFn v).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [ih, smul_mul_smul_comm]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma pair_wedge_product {n m : ℕ} (v : Fin (m*2) → Vec n) :
    (List.ofFn (fun i : Fin m => ExteriorAlgebra.ι ℂ (v (pairLeft i)) *
      ExteriorAlgebra.ι ℂ (v (pairRight i)))).prod = ExteriorAlgebra.ιMulti ℂ (m*2) v := by
  rw [ExteriorAlgebra.ιMulti_apply, List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 2
  funext i
  simp [List.ofFn_succ, pairLeft, pairRight, finProdFinEquiv, mul_comm, add_comm]

lemma twoForm_pow_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A j i = -A i j) (m : ℕ) :
    twoForm A ^ m = (1/2:ℂ)^m • ∑ v : Fin (m*2) → Fin n,
      (∏ k : Fin m, A (v (pairLeft k)) (v (pairRight k))) •
        ExteriorAlgebra.ιMulti ℂ (m*2) (standardBasis n ∘ v) := by
  rw [twoForm_full A hA, smul_pow]
  congr 1
  rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n =>
    A p.1 p.2 • (generator n p.1 * generator n p.2)), sum_pow_list]
  simp_rw [ofFn_smul_prod]
  apply Fintype.sum_equiv (pairArrayEquiv (Fin n) m).symm
  intro p
  have hp : pairArrayEquiv (Fin n) m ((pairArrayEquiv (Fin n) m).symm p) = p :=
    Equiv.apply_symm_apply _ p
  conv_lhs => rw [← hp]
  simp only [pairArrayEquiv_apply, generator]
  congr 1
  exact pair_wedge_product (standardBasis n ∘ (pairArrayEquiv (Fin n) m).symm p)

lemma sum_basis_determinant (n : ℕ) (w : (Fin n → Fin n) → ℂ) :
    (∑ v : Fin n → Fin n, w v * (standardBasis n).det (standardBasis n ∘ v)) =
      ∑ σ : Equiv.Perm (Fin n), w σ * (Equiv.Perm.sign σ : ℂ) := by
  classical
  have hz : (∑ v : {f : Fin n → Fin n // ¬Function.Injective f},
      w v.val * (standardBasis n).det (standardBasis n ∘ v.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hd : (standardBasis n).det (standardBasis n ∘ v.val) = 0 := by
      apply AlternatingMap.map_eq_zero_of_not_injective
      intro hi
      exact v.property (fun a b hab => hi (by simp only [Function.comp_apply, hab]))
    rw [hd, mul_zero]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun v : Fin n → Fin n => Function.Injective v),
    hz, add_zero]
  apply Fintype.sum_equiv (permInjectiveEquiv n).symm
  intro v
  let σ := (permInjectiveEquiv n).symm v
  change w σ * (standardBasis n).det (standardBasis n ∘ σ) = w σ * _
  rw [AlternatingMap.map_perm, Module.Basis.det_self]
  simp [σ, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]



theorem pfaffian_permutation_expansion (m : ℕ)
    (A : Matrix (Fin (m*2)) (Fin (m*2)) ℂ) (hA : ∀ i j, A j i = -A i j) :
    pfaffian (m*2) A = ((1/2:ℂ)^m / m.factorial) *
      ∑ σ : Equiv.Perm (Fin (m*2)), (Equiv.Perm.sign σ : ℂ) *
        pairEntries (fun i j => A (σ i) (σ j)) := by
  change topCoord (m*2) (twoForm A ^ ((m*2)/2)) / _ = _
  rw [Nat.mul_div_cancel m (by norm_num : 0 < 2), twoForm_pow_expansion A hA,
    map_smul, map_sum]
  simp only [map_smul, topCoord_wedge, smul_eq_mul]
  rw [sum_basis_determinant]
  unfold pairEntries
  simp only [mul_comm (∏ i : Fin m, _) (Equiv.Perm.sign _ : ℂ)]
  ring

end



end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReflectionIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip



noncomputable section
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators

lemma eta_pos : 0 < eta := by
  have hd : d = Real.sqrt 2 / 2 := by
    rw [d, lambda, show 2*(Real.pi/8)=Real.pi/4 by ring, Real.cos_pi_div_four]
  have hs : 1 < Real.sqrt 2 := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)<2)
  unfold eta
  rw [hd]
  linarith

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

 

theorem pfaffian_eq_exterior (m : ℕ) (A : Matrix (Fin (m*2)) (Fin (m*2)) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian A = StripPfaffian.pfaffian (m*2) A := by
  rw [StripPfaffian.pfaffian_permutation_expansion m A hA]
  unfold pfaffian
  simp only [Nat.mul_div_cancel m (by omega : 0<2)]
  have hc : ((2:ℂ)^m * (m.factorial:ℂ))⁻¹ = (1/2:ℂ)^m / m.factorial := by
    simp [mul_inv_rev, div_eq_mul_inv, mul_comm]
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  unfold StripPfaffian.pairEntries
  apply Fintype.prod_equiv (finCongr (Nat.mul_div_cancel m (by norm_num : 0 < 2)))
  intro i
  congr 2 <;> apply Fin.ext <;>
    simp [pairFirst,pairSecond,StripPfaffian.pairLeft,StripPfaffian.pairRight,
      finProdFinEquiv,mul_comm,add_comm]

lemma augmentedKernel_skew_complex {n : ℕ} (a : Fin n → ℂ) :
    ∀ i j, augmentedKernel (d:ℂ) (rho:ℂ) a j i =
      -augmentedKernel (d:ℂ) (rho:ℂ) a i j := by
  intro i j
  by_cases hi : i.val<n <;> by_cases hj : j.val<n
  all_goals simp only [augmentedKernel,hi,hj,↓reduceDIte,↓reduceIte]
  · have hd : discriminant (d:ℂ) (a ⟨j.val,hj⟩) (a ⟨i.val,hi⟩) =
        discriminant (d:ℂ) (a ⟨i.val,hi⟩) (a ⟨j.val,hj⟩) := by
      unfold discriminant; ring
    rw [hd,←neg_div]
    congr 1
    ring
  all_goals ring

lemma scalarNormalization_eq_exterior {n : ℕ} (a : Fin n → ℂ) :
    scalarNormalization (d:ℂ) (rho:ℂ) a=StripPfaffian.p n a := by
  have he : n+n%2=((n+1)/2)*2 := by omega
  unfold scalarNormalization StripPfaffian.p
  congr 1
  let A := augmentedKernel (d:ℂ) (rho:ℂ) a
  let A' : Matrix (Fin (((n+1)/2)*2)) (Fin (((n+1)/2)*2)) ℂ :=
    fun i j =>A (i.cast he.symm) (j.cast he.symm)
  calc
    pfaffian A = pfaffian A' := (pfaffian_cast he A).symm
    _ = StripPfaffian.pfaffian (((n+1)/2)*2) A' :=
      pfaffian_eq_exterior _ _ (fun i j =>augmentedKernel_skew_complex a _ _)
    _ = StripPfaffian.pfaffian (StripPfaffian.pfSize n)
        (StripPfaffian.augmentedKernel n a) := by
      have he' : ((n+1)/2)*2=StripPfaffian.pfSize n := by
        unfold StripPfaffian.pfSize; omega
      have hcast {u v:ℕ} (h:u=v) (M:Matrix (Fin u) (Fin u) ℂ) :
          StripPfaffian.pfaffian v (fun i j=>M (i.cast h.symm) (j.cast h.symm)) =
            StripPfaffian.pfaffian u M := by subst v; rfl
      rw [←hcast he' A']
      congr 1

end

noncomputable section
open scoped Classical BigOperators
open Filter Topology

lemma scalarValue_eq_exterior {n : ℕ} (a : Fin n → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → StripPfaffian.D (a i) (a j) ≠ 0) :
    scalarValue (RingHom.id ℂ) a=StripPfaffian.p n a := by
  have hD' : ∀ i j, i≠j → discriminant ((RingHom.id ℂ) (d:ℂ)) (a i) (a j)≠0 := hD
  rw [scalarValue, scalarPolynomial_eval (RingHom.id ℂ) n (d:ℂ) (rho:ℂ) _ a ha hD']
  exact scalarNormalization_eq_exterior a



lemma nextScalar_eval {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    (nextScalar (RingHom.id ℂ) a).eval z = scalarValue (RingHom.id ℂ) (Fin.snoc a z) := by
  rw [scalarValue_snoc]
  exact eval_firstScalarHom _ _ _ _

lemma archPolynomialAt_eval_quotient {n : ℕ} (a : Fin n → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i≠j → StripPfaffian.D (a i) (a j)≠0) (z : ℂ)
    (hz : ∀ i, z≠a i ∧ StripPfaffian.D (a i) z≠0) :
    (archPolynomialAt a).eval z = StripPfaffian.p (n+1) (Fin.snoc a z) / StripPfaffian.p n a := by
  have hi : Function.Injective (Fin.snoc a z) :=
    Fin.snoc_injective_of_injective ha (by rintro ⟨i,hi⟩; exact (hz i).1 hi.symm)
  have hs : ∀ i j : Fin (n+1), i≠j → StripPfaffian.D ((Fin.snoc a z : Fin (n+1) → ℂ) i) ((Fin.snoc a z : Fin (n+1) → ℂ) j)≠0 := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j =>
        simpa [StripPfaffian.D,add_comm,add_left_comm,mul_comm,mul_left_comm] using (hz j).2
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa using (hz i).2
      | cast j => simpa using hD i j (fun he => hij (congrArg Fin.castSucc he))
  rw [archPolynomialAt,Polynomial.eval_mul,Polynomial.eval_C,nextScalar_eval,
    scalarValue_eq_exterior a ha hD,scalarValue_eq_exterior _ hi hs,div_eq_mul_inv,mul_comm]

lemma infinitely_many_regular_arguments {n : ℕ} (a : Fin n → ℂ) :
    Set.Infinite {z : ℂ | ∀ i, z≠a i ∧ StripPfaffian.D (a i) z≠0} := by
  let bad : Set ℂ := Set.range a ∪ ⋃ i, {z : ℂ | (StripPfaffian.Dpoly (a i)).IsRoot z}
  have hb : bad.Finite := (Set.finite_range a).union (Set.finite_iUnion (fun i =>
    Polynomial.finite_setOfPred_isRoot (by
      intro he
      have hh := StripPfaffian.Dpoly_coeff (a i)
      rw [he,Polynomial.coeff_zero] at hh
      exact zero_ne_one hh)))
  have h : badᶜ = {z : ℂ | ∀ i, z≠a i ∧ StripPfaffian.D (a i) z≠0} := by
    ext z
    simp only [bad,Set.mem_compl_iff,Set.mem_union,Set.mem_range,Set.mem_iUnion,
      Set.mem_ofPred_eq,not_or,not_exists,Polynomial.IsRoot,StripPfaffian.Dpoly_eval]
    exact ⟨fun h i => ⟨Ne.symm (h.1 i),h.2 i⟩,fun h => ⟨fun i => (h i).1.symm,fun i => (h i).2⟩⟩
  rw [←h]
  exact hb.infinite_compl

 

theorem archPolynomialAt_confluent (n : ℕ) (hn : 1≤n) :
    ∃ g₀ : Polynomial ℝ, MonicProblem n g₀ ∧
      (∀ q, MonicProblem n q → q=g₀) ∧
      ∃ g : (Fin n → ℂ) → Polynomial ℂ,
        g (fun _ => (C:ℂ))=g₀.map Complex.ofRealHom ∧
        (∀ k, ContinuousAt (fun a => (g a).coeff k) (fun _ => (C:ℂ))) ∧
        ∀ᶠ a in 𝓝 (fun _ : Fin n => (C:ℂ)),
          (g a).Monic ∧ (g a).natDegree=n ∧
            ∀ (_ha : Function.Injective a)
            (_hD : ∀ i j, i≠j → StripPfaffian.D (a i) (a j)≠0)
            (_hp : scalarValue (RingHom.id ℂ) a≠0),
              archPolynomialAt a=g a := by
  obtain ⟨g₀,hg₀,hu,g,hg,hgc,hgreg⟩ := StripPfaffian.pfaffian_confluent_limit n hn
  refine ⟨g₀,hg₀,hu,g,hg,hgc,?_⟩
  filter_upwards [hgreg] with a ha
  refine ⟨ha.1,ha.2.1,?_⟩
  intro hinj hD hp
  apply Polynomial.eq_of_infinite_eval_eq
  apply (infinitely_many_regular_arguments a).mono
  intro z hz
  have hpn : StripPfaffian.p n a≠0 := by rwa [←scalarValue_eq_exterior a hinj hD]
  exact (archPolynomialAt_eval_quotient a hinj hD z hz).trans (ha.2.2 hinj hD hpn z hz).symm

end
end CriticalStrip.Diagram




end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MonicPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram
noncomputable section
open Filter Polynomial
open scoped Topology BigOperators Classical

lemma scalarValue_continuous (n : ℕ) :
    Continuous (fun a : Fin n → ℂ => scalarValue (RingHom.id ℂ) a) := by
  simpa only [scalarValue, MvPolynomial.eval₂Hom, MvPolynomial.eval] using
    (MvPolynomial.continuous_eval (scalarPolynomial n (d:ℂ) rho (by exact_mod_cast d_ne_zero)))

lemma homogeneous_discriminant_ne_zero : StripPfaffian.D (C:ℂ) (C:ℂ) ≠ 0 := by
  have hc := C_c_facts
  have hCp : 0<C := hc.1.trans hc.2.1
  have hd : 0<d := by have he:=eta_pos; change 0<2*d-1 at he; linarith
  have hsum : C^2+CriticalStrip.c^2=1 := C_c_facts.2.2.1
  have hcp : 0<CriticalStrip.c := C_c_facts.1
  have hclt : CriticalStrip.c<C := C_c_facts.2.1
  have hp : 0<C^2+C^2+2*d*C*C-d^2 := by
    nlinarith [d_sq, mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hd) hCp) hCp,
      mul_pos (sub_pos.mpr hclt) (add_pos hCp hcp)]
  change (C:ℂ)^2+(C:ℂ)^2+2*(d:ℂ)*(C:ℂ)*(C:ℂ)-(d:ℂ)^2≠0
  exact_mod_cast hp.ne'


lemma separatedHomogeneous_injective (n m : ℕ) : Function.Injective (separatedHomogeneous n m) := by
  intro i j he
  have hn : (m:ℂ)+1≠0 := by exact_mod_cast (by positivity : (m:ℝ)+1≠0)
  have ht : (1/((m:ℂ)+1))≠0 := one_div_ne_zero hn
  apply Fin.ext
  apply Nat.cast_injective (R:=ℂ)
  exact mul_right_cancel₀ ht (add_left_cancel he)

lemma separatedHomogeneous_tendsto (n : ℕ) :
    Tendsto (separatedHomogeneous n) atTop (𝓝 (fun _ => (C:ℂ))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  simpa only [mul_zero,add_zero,separatedHomogeneous] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℂ)).const_mul (i.val:ℂ) |>.const_add (C:ℂ)

lemma separatedHomogeneous_discriminants (n : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ i j : Fin n,
      StripPfaffian.D (separatedHomogeneous n m i) (separatedHomogeneous n m j) ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  have ht := separatedHomogeneous_tendsto n
  have hD : Continuous (fun a : Fin n → ℂ => StripPfaffian.D (a i) (a j)) := by
    unfold StripPfaffian.D; fun_prop
  exact (hD.continuousAt.tendsto.comp ht).eventually_ne homogeneous_discriminant_ne_zero

lemma polynomial_eval_limit_of_coeff {α : Type*} {l : Filter α} {P : α → Polynomial ℂ}
    {g : Polynomial ℂ} {n : ℕ} (hdeg : ∀ᶠ x in l, (P x).natDegree≤n) (hg : g.natDegree≤n)
    (ht : ∀ i, Tendsto (fun x => (P x).coeff i) l (𝓝 (g.coeff i))) (z : ℂ) :
    Tendsto (fun x => (P x).eval z) l (𝓝 (g.eval z)) := by
  rw [Polynomial.eval_eq_sum_range' (show g.natDegree<n+1 by omega)]
  apply (tendsto_finsetSum (Finset.range (n+1)) (fun i _ => (ht i).mul_const (z^i))).congr'
  filter_upwards [hdeg] with x hx
  exact (Polynomial.eval_eq_sum_range' (show (P x).natDegree<n+1 by omega) z).symm

 

theorem archPolynomialAt_homogeneous_of_ne {n : ℕ} (hn : 1≤n)
    (hp : scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      archPolynomialAt (fun _ : Fin n => (C:ℂ))=g.map Complex.ofRealHom := by
  obtain ⟨g₀,hg₀,hu,g,hg,hgc,hgreg⟩ := archPolynomialAt_confluent n hn
  refine ⟨g₀,hg₀,?_⟩
  apply Polynomial.funext
  intro z
  have ht := separatedHomogeneous_tendsto n
  have hreg := ht.eventually hgreg
  have hpn : ∀ᶠ m in atTop, scalarValue (RingHom.id ℂ) (separatedHomogeneous n m)≠0 :=
    ((scalarValue_continuous n).continuousAt.tendsto.comp ht).eventually_ne hp
  have hgg : Tendsto (fun m => (g (separatedHomogeneous n m)).eval z) atTop
      (𝓝 ((g₀.map Complex.ofRealHom).eval z)) := by
    apply polynomial_eval_limit_of_coeff (n:=n)
      (hreg.mono fun _ h => h.2.1.le)
      ((Polynomial.natDegree_map_le).trans hg₀.2.1.le)
    intro i
    have hh := (hgc i).tendsto.comp ht
    simpa only [hg,Function.comp_def] using hh
  have hal : ∀ a : Fin n → ℂ, (archPolynomialAt a).eval z =
      scalarValue (RingHom.id ℂ) (Fin.snoc a z) / scalarValue (RingHom.id ℂ) a := by
    intro a
    simp only [archPolynomialAt,Polynomial.eval_mul,Polynomial.eval_C,nextScalar_eval]
    ring
  have hcont : Continuous (fun a : Fin n → ℂ => scalarValue (RingHom.id ℂ) (Fin.snoc a z)) := by
    apply (scalarValue_continuous (n+1)).comp
    apply continuous_pi
    intro i
    induction i using Fin.lastCases <;> simp only [Fin.snoc_last,Fin.snoc_castSucc] <;> fun_prop
  have hfrac := ((hcont.continuousAt.tendsto.comp ht).div
    ((scalarValue_continuous n).continuousAt.tendsto.comp ht) hp)
  have hh : Tendsto (fun m => (g (separatedHomogeneous n m)).eval z) atTop
      (𝓝 ((archPolynomialAt (fun _ : Fin n => (C:ℂ))).eval z)) := by
    rw [hal]
    apply hfrac.congr'
    filter_upwards [hreg,hpn,separatedHomogeneous_discriminants n] with m hm hpm hDm
    change scalarValue (RingHom.id ℂ) (Fin.snoc (separatedHomogeneous n m) z) /
      scalarValue (RingHom.id ℂ) (separatedHomogeneous n m)=_
    rw [←hal,hm.2.2 (separatedHomogeneous_injective n m) (fun i j _ => hDm i j) hpm]
  exact tendsto_nhds_unique hh hgg

lemma nextScalar_homogeneous_of_ne_oai {n : ℕ} (hn : 1≤n)
    (hp : scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      nextScalar (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))=
        Polynomial.C (scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))) * g.map Complex.ofRealHom := by
  obtain ⟨g,hg,he⟩:=archPolynomialAt_homogeneous_of_ne hn hp
  refine ⟨g,hg,?_⟩
  rw [←he,archPolynomialAt,←mul_assoc,←Polynomial.C_mul,mul_inv_cancel₀ hp,Polynomial.C_1,one_mul]



end
end CriticalStrip.Diagram





end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne_oai := @OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne_oai
