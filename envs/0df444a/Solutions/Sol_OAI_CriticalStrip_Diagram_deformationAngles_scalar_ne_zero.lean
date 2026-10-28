-- Prove2me | solution 1 for OAI.CriticalStrip.Diagram.deformationAngles_scalar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:24:36.196928+00:00
-- url     : https://prove2.me/submissions/9c83be7d-272e-42a8-93a3-0ac3e181a050

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S015
import Theorems.Thm_OAI_CriticalStrip_Diagram_nextScalar_homogeneous_of_ne
import Theorems.Thm_OAI_CriticalStrip_Diagram_scalarValue_homogeneous_ne_zero

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

theorem pairKernel_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    0 < pairKernel x y := by
  unfold pairKernel
  exact div_pos (sq_pos_of_pos (sub_pos.2 hxy)) (by linarith)

theorem pairKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ pairKernel x y := by
  unfold pairKernel
  positivity

theorem pairKernel_le_one {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    pairKernel x y ≤ 1 := by
  unfold pairKernel
  apply (div_le_one (by linarith [hx.1, hy.1] : 0 < y + x)).2
  have hxx : x ^ 2 ≤ x := by nlinarith [hx.1, hx.2]
  have hyy : y ^ 2 ≤ y := by nlinarith [hy.1, hy.2]
  nlinarith [mul_pos hx.1 hy.1]

theorem density_pos {N : ℕ} {y : Fin N → ℝ} (hy : y ∈ orderedDomain N) :
    0 < density N y := by
  apply mul_pos
  · exact Finset.prod_pos fun i _ => omega_pos (hy.2 i)
  · apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    exact pairKernel_pos (hy.2 i).1 (hy.1 (Finset.mem_Ioi.1 hj))

theorem density_le_product {N : ℕ} {y : Fin N → ℝ} (hy : y ∈ orderedDomain N) :
    density N y ≤ ∏ i, omega (y i) := by
  have h0 : 0 ≤ ∏ i : Fin N, omega (y i) :=
    Finset.prod_nonneg fun _ _ => omega_nonneg _
  suffices hh : (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, pairKernel (y i) (y j)) ≤ 1 by
    simpa only [density, mul_one] using mul_le_mul_of_nonneg_left hh h0
  apply Finset.prod_le_one
  · intro i _
    exact Finset.prod_nonneg fun j _ => pairKernel_nonneg (hy.2 i).1.le (hy.2 j).1.le
  · intro i _
    exact Finset.prod_le_one
      (fun j _ => pairKernel_nonneg (hy.2 i).1.le (hy.2 j).1.le)
      (fun j _ => pairKernel_le_one (hy.2 i) (hy.2 j))

theorem measurable_density (N : ℕ) : Measurable (density N) := by
  unfold density pairKernel
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i _ => measurable_omega.comp (measurable_pi_apply i)
  · apply Finset.measurable_prod
    intro i _
    apply Finset.measurable_prod
    intro j _
    fun_prop

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

theorem integrableOn_density (N : ℕ) : IntegrableOn (density N) (orderedDomain N) := by
  have hi : IntegrableOn (fun y : Fin N → ℝ => ∏ i, omega (y i))
      (Set.univ.pi fun _ : Fin N => Ioo (0 : ℝ) 1) := by
    unfold IntegrableOn
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun _ => integrableOn_omega
  have his : IntegrableOn (fun y : Fin N → ℝ => ∏ i, omega (y i)) (orderedDomain N) :=
    hi.mono_set (fun _ hy => fun i _ => hy.2 i)
  apply his.mono' (measurable_density N).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  simpa only [Real.norm_eq_abs, abs_of_pos (density_pos hy)] using density_le_product hy

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

theorem normalizer_pos (N : ℕ) : 0 < normalizer N := by
  have hpos : 0 ≤ᵐ[volume.restrict (orderedDomain N)] density N := by
    filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
    exact (density_pos hy).le
  apply (integral_pos_iff_support_of_nonneg_ae hpos (integrableOn_density N)).2
  have hs : orderedDomain N ⊆ Function.support (density N) :=
    fun y hy => (density_pos hy).ne'
  have hm := (isOpen_orderedDomain N).measure_pos volume (orderedDomain_nonempty N)
  calc
    0 < volume (orderedDomain N) := hm
    _ = (volume.restrict (orderedDomain N)) (orderedDomain N) :=
      (Measure.restrict_apply_self _ _).symm
    _ ≤ (volume.restrict (orderedDomain N)) (Function.support (density N)) := measure_mono hs


theorem abs_reflectionFactor_le_one {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    |(y - x) / (y + x)| ≤ 1 := by
  apply abs_le.2
  have hxy : 0 < y + x := by linarith
  constructor
  · apply (le_div_iff₀ hxy).2
    linarith
  · apply (div_le_iff₀ hxy).2
    linarith

theorem abs_reflectionProduct_le_one {N : ℕ} {y : Fin N → ℝ}
    (hy : y ∈ orderedDomain N) {x : ℝ} (hx : 0 ≤ x) : |reflectionProduct N x y| ≤ 1 := by
  rw [reflectionProduct, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ =>
    abs_reflectionFactor_le_one hx (hy.2 i).1)

theorem measurable_reflectionProduct (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => reflectionProduct N p.1 p.2) := by
  unfold reflectionProduct
  apply Finset.measurable_prod
  intro i _
  fun_prop

theorem integrableOn_reflectionProduct_density (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun y => reflectionProduct N x y * density N y) (orderedDomain N) := by
  have hm : Measurable (fun y => reflectionProduct N x y * density N y) :=
    ((measurable_reflectionProduct N).comp (measurable_const.prodMk measurable_id)).mul (measurable_density N)
  apply (integrableOn_density N).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (density_pos hy)]
  exact (mul_le_mul_of_nonneg_right (abs_reflectionProduct_le_one hy hx) (density_pos hy).le).trans_eq (one_mul _)

theorem expectation_nonneg (N : ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : ∀ y ∈ orderedDomain N, 0 ≤ f y) : 0 ≤ expectation N f := by
  apply div_nonneg _ (normalizer_pos N).le
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (isOpen_orderedDomain N).measurableSet] with y hy
  exact mul_nonneg (hf y hy) (density_pos hy).le

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

 

theorem existsUnique_cauchyMomentProblem (N : ℕ) (D₀ : ℝ) :
    ∃! v : Fin N → ℝ, CauchyMomentProblem N D₀ v := by
  have hu : IsUnit (momentMatrix N) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_momentMatrix_pos N).ne')
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.2 hu)
    (fun j => D₀ * ∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x)
  refine ⟨v, (cauchyMomentProblem_iff _ _ _).2 hv, ?_⟩
  intro w hw
  exact (Matrix.mulVec_injective_iff_isUnit.2 hu)
    (((cauchyMomentProblem_iff _ _ _).1 hw).trans hv.symm)

 

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



end
end CriticalStrip


end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchIntegrals
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

theorem expectation_const_mul (N : ℕ) (a : ℝ) (f : (Fin N → ℝ) → ℝ) :
    expectation N (fun y => a * f y) = a * expectation N f := by
  simp only [expectation, mul_assoc, integral_const_mul, mul_div_assoc]



end


end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma polynomialVacuumVector_eval (n:ℕ) (p:Pairing n) :
    evalLaurent (polynomialVacuumVector n p)=rationalVacuum n p := by
  cases n with
  | zero =>rw [rationalVacuum_zero]; exact map_one _
  | succ n =>exact (vacuumData n).eval_P p

end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram




noncomputable section
open scoped Classical BigOperators



lemma map_scalarValue {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    g (scalarValue f a) = scalarValue (g.comp f) (g ∘ a) := by
  exact MvPolynomial.map_eval₂Hom _ _ _ _

lemma rowCosineL_map {n : ℕ} (i : Fin n) : evalLaurent (rowCosineL i)=spectralA i := by
  rw [rowCosineL,cosineL_map _ _ (inv_ne_zero (pow_ne_zero _ phase_ne_zero)),map_monomialL_two_variable]
  simp only [constF,map_inv₀,map_pow]
  congr 1
  simp [constF,div_eq_mul_inv,mul_comm]

lemma rowCosineL_algebraMap {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowCosineL i)=spectralA i := rowCosineL_map i

lemma evalLaurent_constant_comp (n : ℕ) :
    (algebraMap (SpectralRing n) (SpectralField n)).comp (constantL n) =
      algebraMap ℂ (SpectralField n) := by
  ext z
  exact map_constantL n z

lemma scalarValue_rowCosine (n : ℕ) :
    scalarValue (constantL n) rowCosineL = polynomialVacuumVector n (empty n) := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  rw [show algebraMap (SpectralRing n) (SpectralField n) _ = _ from
    map_scalarValue _ (constantL n) rowCosineL]
  simp only [evalLaurent_constant_comp,Function.comp_def,rowCosineL_algebraMap]
  change scalarValue _ spectralA = evalLaurent (polynomialVacuumVector n (empty n))
  rw [polynomialVacuumVector_eval,rationalVacuum_empty]
  exact scalarPolynomial_eval_spectral n

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TailIntegrals
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



theorem pairProduct_cons {n : ℕ} (x : ℝ) (r : Fin n → ℝ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
      pairKernel ((Fin.cons x r : Fin (n + 1) → ℝ) i) ((Fin.cons x r : Fin (n + 1) → ℝ) j)) =
      (∏ j, pairKernel x (r j)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j) := by
  classical
  have he {m : ℕ} (s : Fin m → ℝ) :
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, pairKernel (s i) (s j)) =
        ∏ i : Fin m, ∏ j : Fin m, if i < j then pairKernel (s i) (s j) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, he]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    ↓reduceIte, Fin.succ_pos, Fin.not_lt_zero, Fin.succ_lt_succ_iff, one_mul]

end
end CriticalStrip

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
open MeasureTheory Set

lemma piCongrLeft_const_apply {α : Type*} [MeasurableSpace α] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => α) σ) x = x ∘ σ.symm := by
  ext i
  obtain ⟨j, rfl⟩ := σ.surjective i
  simp [MeasurableEquiv.coe_piCongrLeft]

end
end StripPfaffian

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
open Filter Topology

lemma nextScalar_eval {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    (nextScalar (RingHom.id ℂ) a).eval z = scalarValue (RingHom.id ℂ) (Fin.snoc a z) := by
  rw [scalarValue_snoc]
  exact eval_firstScalarHom _ _ _ _

end
end CriticalStrip.Diagram




end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RealEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset

lemma anglePhase_add (u v : ℝ) : anglePhase (u+v)=anglePhase u*anglePhase v := by
  simp only [anglePhase,Complex.ofReal_add,add_mul,Complex.exp_add]
lemma anglePhase_neg (u : ℝ) : anglePhase (-u)=(anglePhase u)⁻¹ := by
  simp [anglePhase,Complex.exp_neg]
lemma anglePhase_sub (u v : ℝ) : anglePhase (u-v)=anglePhase u/anglePhase v := by
  simp only [sub_eq_add_neg,anglePhase_add,anglePhase_neg,div_eq_mul_inv]
lemma anglePhase_nat_mul (k : ℕ) (u : ℝ) : anglePhase ((k:ℝ)*u)=anglePhase u^k := by
  simp only [anglePhase,Complex.ofReal_mul,Complex.ofReal_natCast,←Complex.exp_nat_mul,mul_assoc]
lemma anglePhase_cosine (u : ℝ) : (anglePhase u+(anglePhase u)⁻¹)/2=(Real.cos u:ℂ) := by
  rw [anglePhase,Complex.ofReal_cos,Complex.cos,←Complex.exp_neg]
  simp only [neg_mul]

lemma rationalAt_const_complex {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) (z : ℂ) :
    RationalAt φ.toRingHom (constF n z) z := by
  have hh:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField n) (constantL n z)
  rw [map_constantL] at hh
  have he : φ (constantL n z)=z := φ.commutes z
  simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,he] using hh

lemma rationalAt_angle_variable {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    RationalAt (angleEvaluation u).toRingHom (variableF i) (anglePhase (u i)) := by
  have hh:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n)
    (monomialL (variableExponent i) 1)
  change RationalAt (angleEvaluation u).toRingHom (variableF i)
    (angleEvaluation u (monomialL (variableExponent i) 1)) at hh
  simpa only [angleEvaluation_variable] using hh

lemma rationalAt_angle_cos {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) :
    RationalAt φ.toRingHom (torusCos x) (Real.cos u:ℂ) := by
  rw [←anglePhase_cosine]
  exact (h.add (h.inv (anglePhase_ne_zero _))).div (RationalAt.natCast 2) (by norm_num)

lemma rationalAt_angle_spectralA {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    RationalAt (angleEvaluation u).toRingHom (spectralA i) (Real.cos (2*u i-3*lambda):ℂ) := by
  apply rationalAt_angle_cos
  rw [anglePhase_sub,show anglePhase (2*u i)=anglePhase (u i)^2 from anglePhase_nat_mul 2 _,
    show anglePhase (3*lambda)=phase^3 from anglePhase_nat_mul 3 _]
  exact
    ((rationalAt_angle_variable u i).pow 2).div
      ((rationalAt_const_complex (angleEvaluation u) phase).pow 3) (pow_ne_zero _ phase_ne_zero)

lemma angleEvaluation_rowCosine {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    angleEvaluation u (rowCosineL i)=(Real.cos (2*u i-3*lambda):ℂ) := by
  have hh:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n) (rowCosineL i)
  rw [rowCosineL_algebraMap] at hh
  exact hh.unique (rationalAt_angle_spectralA u i)

lemma angleEvaluation_scalar {n : ℕ} (u : Fin n → ℝ) :
    angleEvaluation u (polynomialVacuumVector n (empty n))=
      scalarValue (RingHom.id ℂ) (fun i=>(Real.cos (2*u i-3*lambda):ℂ)) := by
  rw [←scalarValue_rowCosine]
  have hh:=map_scalarValue (angleEvaluation u).toRingHom (constantL n) rowCosineL
  have hc : (angleEvaluation u).toRingHom.comp (constantL n)=RingHom.id ℂ := by ext z; simp
  rw [hc] at hh
  have hf : (angleEvaluation u).toRingHom ∘ rowCosineL=fun i=>(Real.cos (2*u i-3*lambda):ℂ) := by
    funext i
    exact angleEvaluation_rowCosine u i
  rw [hf] at hh
  exact hh

end
end CriticalStrip.Diagram







end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MomentGrowth
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





lemma pairKernel_symm (x y : ℝ) : pairKernel x y = pairKernel y x := by
  unfold pairKernel
  rw [add_comm x y]
  congr 1
  ring

lemma prod_upper_square {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, g i j = g j i) :
    (∏ i, ∏ j ∈ Finset.Ioi i, g i j)^2 =
      ∏ i, ∏ j, if i = j then 1 else g i j := by
  classical
  have he : (∏ i, ∏ j ∈ Finset.Ioi i, g i j) =
      ∏ i, ∏ j, if i < j then g i j else 1 := by
    congr 1
    ext i
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  rw [he, pow_two]
  conv_lhs => rhs; rw [Finset.prod_comm]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le, h.ne]
  · simp
  · simp [h, not_lt.mpr h.le, h.ne', hsym]

lemma prod_upper_perm {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, g i j = g j i) (hpos : ∀ i j, 0 ≤ g i j)
    (σ : Equiv.Perm (Fin n)) :
    (∏ i, ∏ j ∈ Finset.Ioi i, g (σ i) (σ j)) =
      ∏ i, ∏ j ∈ Finset.Ioi i, g i j := by
  classical
  have ha : 0 ≤ ∏ i, ∏ j ∈ Finset.Ioi i, g (σ i) (σ j) :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hpos _ _
  have hb : 0 ≤ ∏ i, ∏ j ∈ Finset.Ioi i, g i j :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hpos _ _
  have he : (∏ i, ∏ j ∈ Finset.Ioi i, g (σ i) (σ j))^2 =
      (∏ i, ∏ j ∈ Finset.Ioi i, g i j)^2 := by
    rw [prod_upper_square _ (fun i j => hsym _ _), prod_upper_square g hsym]
    apply Fintype.prod_equiv σ
    intro i
    apply Fintype.prod_equiv σ
    intro j
    simp
  nlinarith

lemma density_perm_of_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i)
    (σ : Equiv.Perm (Fin n)) : density n (x ∘ σ) = density n x := by
  unfold density
  congr 1
  · exact Fintype.prod_equiv σ _ _ (fun _ => rfl)
  · exact prod_upper_perm _ (fun i j => pairKernel_symm _ _)
      (fun i j => pairKernel_nonneg (hx i) (hx j)) σ

lemma density_zero_of_not_injective {n : ℕ} {x : Fin n → ℝ}
    (hx : ¬ Function.Injective x) : density n x = 0 := by
  classical
  obtain ⟨i, j, he, hne⟩ : ∃ i j, x i = x j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, exists_prop] using hx
  suffices (∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (x i) (x j)) = 0 by
    simp [density, this]
  rcases hne.lt_or_gt with h | h
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_Ioi.mpr h)
    simp [pairKernel, he]
  · apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply Finset.prod_eq_zero (Finset.mem_Ioi.mpr h)
    simp [pairKernel, he]

lemma ae_unitCube (n : ℕ) :
    ∀ᵐ x ∂unitCubeMeasure n, ∀ i, x i ∈ Ioo (0:ℝ) 1 := by
  rw [unitCubeMeasure, ← Measure.restrict_pi_pi, ← volume_pi]
  exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)).mono
    fun _ hx i => hx i (mem_univ i)

lemma unitCube_restrict_ordered (n : ℕ) :
    (unitCubeMeasure n).restrict (orderedDomain n) = volume.restrict (orderedDomain n) := by
  rw [unitCubeMeasure, ← Measure.restrict_pi_pi, ← volume_pi,
    Measure.restrict_restrict (isOpen_orderedDomain n).measurableSet]
  congr 1
  exact inter_eq_left.mpr (fun _ hx i _ => hx.2 i)

lemma integral_symmetric_unitCube {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∀ x, (∀ i, x i ∈ Ioo (0:ℝ) 1) → F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬Function.Injective x → F x = 0)
    (hint : IntegrableOn F (orderedDomain n)) :
    (∫ x, F x ∂unitCubeMeasure n) =
      (n.factorial : ℝ) * ∫ x in orderedDomain n, F x := by
  classical
  let G := (orderedDomain n).indicator F
  have hi : Integrable G (unitCubeMeasure n) := by
    rw [integrable_indicator_iff (isOpen_orderedDomain n).measurableSet]
    simpa only [IntegrableOn, unitCube_restrict_ordered] using hint
  have his (σ : Equiv.Perm (Fin n)) :
      Integrable (fun x => G (x ∘ σ)) (unitCubeMeasure n) := by
    simpa only [Function.comp_def, StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin n => volume.restrict (Ioo (0:ℝ) 1)) σ.symm).integrable_comp_of_integrable hi
  have heq (σ : Equiv.Perm (Fin n)) :
      (∫ x, G (x ∘ σ) ∂unitCubeMeasure n) = ∫ x in orderedDomain n, F x := by
    have he := (measurePreserving_piCongrLeft
      (fun _ : Fin n => volume.restrict (Ioo (0:ℝ) 1)) σ.symm).integral_comp' G
    simp only [StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] at he
    rw [he, integral_indicator (isOpen_orderedDomain n).measurableSet, unitCube_restrict_ordered]
  have hs (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Ioo (0:ℝ) 1) :
      ∑ σ : Equiv.Perm (Fin n), G (x ∘ σ) = F x := by
    by_cases hinj : Function.Injective x
    · have hsort : x ∘ Tuple.sort x ∈ orderedDomain n :=
        ⟨(Tuple.monotone_sort x).strictMono_of_injective (hinj.comp (Tuple.sort x).injective),
          fun i => hx _⟩
      rw [Finset.sum_eq_single (Tuple.sort x)]
      · exact (indicator_of_mem hsort F).trans (hperm _ _ hx)
      · intro σ _ hne
        apply indicator_of_notMem
        intro hσ
        apply hne
        apply Equiv.ext
        intro i
        exact hinj (congrFun (Tuple.unique_monotone hσ.1.monotone (Tuple.monotone_sort x)) i)
      · simp
    · rw [hzero x hinj]
      apply Finset.sum_eq_zero
      intro σ _
      by_cases hm : x ∘ σ ∈ orderedDomain n
      · exact (indicator_of_mem hm F).trans ((hperm _ _ hx).trans (hzero x hinj))
      · exact indicator_of_notMem hm _
  calc
    _ = ∫ x, ∑ σ : Equiv.Perm (Fin n), G (x ∘ σ) ∂unitCubeMeasure n :=
      integral_congr_ae ((ae_unitCube n).mono fun x hx => (hs x hx).symm)
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ x, G (x ∘ σ) ∂unitCubeMeasure n :=
      integral_finsetSum _ (fun σ _ => his σ)
    _ = _ := by simp only [heq, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

lemma integral_density_unitCube (n : ℕ) :
    (∫ x, density n x ∂unitCubeMeasure n) = (n.factorial:ℝ) * normalizer n := by
  exact integral_symmetric_unitCube _
    (fun σ x hx => density_perm_of_nonneg (fun i => (hx i).1.le) σ)
    (fun _ hx => density_zero_of_not_injective hx) (integrableOn_density n)

lemma density_cons (n : ℕ) (x : ℝ) (y : Fin n → ℝ) :
    density (n+1) (Fin.cons x y) =
      omega x * density n y * ∏ i, pairKernel x (y i) := by
  rw [density, Fin.prod_univ_succ, pairProduct_cons]
  simp only [Fin.cons_zero, Fin.cons_succ, density]
  ring

lemma density_nonneg_of_nonneg {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, 0 ≤ y i) :
    0 ≤ density n y := by
  unfold density
  apply mul_nonneg (Finset.prod_nonneg fun _ _ => omega_nonneg _)
  exact Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => pairKernel_nonneg (hy i) (hy j)

lemma density_cube_le_product {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, y i ∈ Ioo (0:ℝ) 1) :
    density n y ≤ ∏ i, omega (y i) := by
  have h0 : 0 ≤ ∏ i : Fin n, omega (y i) := Finset.prod_nonneg fun _ _ => omega_nonneg _
  unfold density
  apply (mul_le_mul_of_nonneg_left _ h0).trans_eq (mul_one _)
  exact Finset.prod_le_one
    (fun i _ => Finset.prod_nonneg fun j _ => pairKernel_nonneg (hy i).1.le (hy j).1.le)
    (fun i _ => Finset.prod_le_one
      (fun j _ => pairKernel_nonneg (hy i).1.le (hy j).1.le)
      (fun j _ => pairKernel_le_one (hy i) (hy j)))

lemma integrable_density_unitCube (n : ℕ) : Integrable (density n) (unitCubeMeasure n) := by
  apply (Integrable.fintype_prod (fun _ : Fin n => integrableOn_omega)).mono'
    (measurable_density n).aestronglyMeasurable
  filter_upwards [ae_unitCube n] with y hy
  simpa only [Real.norm_eq_abs, abs_of_nonneg (density_nonneg_of_nonneg (fun i => (hy i).1.le))]
    using density_cube_le_product hy

lemma integrable_cube_mul_density {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : Measurable g)
    {b : ℝ} (hbd : ∀ y, (∀ i, y i ∈ Ioo (0:ℝ) 1) → |g y| ≤ b) :
    Integrable (fun y => g y * density n y) (unitCubeMeasure n) := by
  apply ((integrable_density_unitCube n).const_mul b).mono'
    (hg.mul (measurable_density n)).aestronglyMeasurable
  filter_upwards [ae_unitCube n] with y hy
  change ‖g y * density n y‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg_of_nonneg (fun i => (hy i).1.le))]
  exact mul_le_mul_of_nonneg_right (hbd y hy) (density_nonneg_of_nonneg (fun i => (hy i).1.le))

lemma reflectionProduct_perm {n : ℕ} (x : ℝ) (y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    reflectionProduct n x (y ∘ σ) = reflectionProduct n x y := by
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

lemma expectation_reflection_unitCube (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    expectation n (reflectionProduct n x) =
      (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n) /
        (∫ y, density n y ∂unitCubeMeasure n) := by
  rw [integral_symmetric_unitCube _
    (fun σ y hy => by rw [reflectionProduct_perm, density_perm_of_nonneg (fun i => (hy i).1.le)])
    (fun y hy => by rw [density_zero_of_not_injective hy, mul_zero])
    (integrableOn_reflectionProduct_density n hx), integral_density_unitCube]
  rw [mul_div_mul_left _ _ (by exact_mod_cast (Nat.factorial_ne_zero n))]
  rfl

lemma reflectionResidue_perm {n : ℕ} (y : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reflectionResidue n (y ∘ σ) i = reflectionResidue n y (σ i) := by
  classical
  unfold reflectionResidue
  congr 1
  apply Finset.prod_equiv σ
  · intro j
    simp
  · intro j hj
    rfl

lemma reflectionResidue_zero_cons {n : ℕ} (x : ℝ) (y : Fin n → ℝ) :
    reflectionResidue (n+1) (Fin.cons x y) 0 = 2 * ∏ j, (y j+x)/(y j-x) := by
  classical
  unfold reflectionResidue
  congr 1
  have he : (Finset.univ.erase (0 : Fin (n+1))) = Finset.univ.filter (fun i => i ≠ 0) := by ext; simp
  rw [he, Finset.prod_filter, Fin.prod_univ_succ]
  simp

lemma reflectionResidue_density_cons {n : ℕ} {x : ℝ} {y : Fin n → ℝ}
    (hx : 0 < x) (hy : ∀ i, 0 < y i) :
    reflectionResidue (n+1) (Fin.cons x y) 0 * density (n+1) (Fin.cons x y) =
      2 * omega x * density n y * ∏ i, (y i-x) := by
  rw [reflectionResidue_zero_cons, density_cons]
  have hprod : (∏ i, (y i+x)/(y i-x)) * (∏ i, pairKernel x (y i)) = ∏ i, (y i-x) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    unfold pairKernel
    by_cases hi : y i = x
    · simp [hi]
    · field_simp [(add_pos (hy i) hx).ne', sub_ne_zero.mpr hi]
  calc
    _ = 2 * omega x * density n y *
        ((∏ i, (y i+x)/(y i-x)) * (∏ i, pairKernel x (y i))) := by ring
    _ = _ := by rw [hprod]

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReflectionFractions
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
lemma reflection_partialFractions_distinct {n : ℕ} (hn : 0 < n) {y : Fin n → ℝ}
    (hy : ∀ i, 0 < y i) (hinj : Function.Injective y) {x : ℝ} (hx : 0 ≤ x) :
    reflectionProduct n x y = 1 - x * ∑ i, reflectionResidue n y i / (x+y i) := by
  classical
  let P : Polynomial ℝ := ∏ i, (Polynomial.C (y i) - Polynomial.X)
  let Q : Polynomial ℝ := ∏ i, (Polynomial.C (y i) + Polynomial.X)
  let R : Fin n → Polynomial ℝ := fun i => ∏ j ∈ Finset.univ.erase i, (Polynomial.C (y j)+Polynomial.X)
  let T : Polynomial ℝ := Q - Polynomial.X * ∑ i, Polynomial.C (reflectionResidue n y i) * R i
  have hlin (a : ℝ) : (Polynomial.C a + Polynomial.X).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (by simp)
  have hR (i : Fin n) : (R i).natDegree ≤ n-1 := by
    apply (Polynomial.natDegree_prod_le (Finset.univ.erase i)
      (fun j => Polynomial.C (y j) + Polynomial.X)).trans
    calc
      ∑ j ∈ Finset.univ.erase i, (Polynomial.C (y j)+Polynomial.X).natDegree ≤
          ∑ _j ∈ Finset.univ.erase i, 1 := by
        apply Finset.sum_le_sum
        intro j _
        exact hlin (y j)
      _ = n-1 := by simp
  have hP : P.natDegree ≤ n := by
    apply (Polynomial.natDegree_prod_le Finset.univ
      (fun i => Polynomial.C (y i) - Polynomial.X)).trans
    calc
      ∑ i : Fin n, (Polynomial.C (y i)-Polynomial.X).natDegree ≤ ∑ _i : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro i _
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
      _ = n := by simp
  have hQ : Q.natDegree ≤ n := by
    apply (Polynomial.natDegree_prod_le Finset.univ
      (fun i => Polynomial.C (y i) + Polynomial.X)).trans
    calc
      ∑ i : Fin n, (Polynomial.C (y i)+Polynomial.X).natDegree ≤ ∑ _i : Fin n, 1 :=
        by
          apply Finset.sum_le_sum
          intro i _
          exact hlin (y i)
      _ = n := by simp
  have hT : T.natDegree ≤ n := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le hQ
    apply (Polynomial.natDegree_mul_le).trans
    have hh : (∑ i, Polynomial.C (reflectionResidue n y i) * R i).natDegree ≤ n-1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i _
      exact (Polynomial.natDegree_C_mul_le _ _).trans (hR i)
    simpa only [Polynomial.natDegree_X] using (add_le_add_right hh 1 |>.trans (by omega : 1+(n-1) ≤ n))
  have hnode : Function.Injective (Fin.cons (0:ℝ) (fun i => -y i)) := by
    rw [Fin.cons_injective_iff]
    refine ⟨?_, fun i j h => hinj (neg_injective h)⟩
    rintro ⟨i, hi⟩
    exact (hy i).ne' (neg_eq_zero.mp hi)
  have he : P = T := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (s := Finset.univ) (v := Fin.cons (0:ℝ) (fun i => -y i))
      (hnode.injOn)
      ((Polynomial.degree_le_of_natDegree_le hP).trans_lt (by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact_mod_cast Nat.lt_succ_self n))
      ((Polynomial.degree_le_of_natDegree_le hT).trans_lt (by
        simp only [Finset.card_univ, Fintype.card_fin]
        exact_mod_cast Nat.lt_succ_self n))
    intro i _
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [P, Q, T, Polynomial.eval_prod]
    · have hQ0 : Q.eval (-y i) = 0 := by
        simp only [Q, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
      have hsum : (∑ j, Polynomial.C (reflectionResidue n y j) * R j).eval (-y i) =
          reflectionResidue n y i * ∏ j ∈ Finset.univ.erase i, (y j-y i) := by
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
        rw [Finset.sum_eq_single i]
        · simp [R, Polynomial.eval_prod, sub_eq_add_neg]
        · intro j _ hji
          have hz : (R j).eval (-y i) = 0 := by
            simp only [R, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
            exact Finset.prod_eq_zero (show i ∈ Finset.univ.erase j from by simp [hji.symm]) (by ring)
          rw [hz, mul_zero]
        · simp
      have hres : reflectionResidue n y i * ∏ j ∈ Finset.univ.erase i, (y j-y i) =
          2 * ∏ j ∈ Finset.univ.erase i, (y j+y i) := by
        rw [reflectionResidue, Finset.prod_div_distrib, mul_assoc, div_mul_cancel₀]
        exact Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hinj.ne (Finset.mem_erase.mp hj).1)
      have hPm : P.eval (-y i) = (2*y i) * ∏ j ∈ Finset.univ.erase i, (y j+y i) := by
        simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, sub_neg_eq_add]
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        ring
      simp only [Fin.cons_succ, T, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        hQ0, hsum, hres, hPm]
      ring
  have heval := congrArg (Polynomial.eval x) he
  simp only [P, Q, T, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_finsetSum, R] at heval
  have hden : (∏ i, (y i+x)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (add_pos_of_pos_of_nonneg (hy i) hx).ne'
  have hi (i : Fin n) : (∏ j ∈ Finset.univ.erase i, (y j+x))/(∏ j, (y j+x)) = (x+y i)⁻¹ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    rw [mul_comm (y i+x), div_mul_cancel_left₀]
    · rw [add_comm]
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => (add_pos_of_pos_of_nonneg (hy j) hx).ne'
  rw [reflectionProduct, Finset.prod_div_distrib, heval, sub_div, div_self hden,
    mul_div_assoc, Finset.sum_div]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc, hi, div_eq_mul_inv]

lemma integral_unitCube_cons (n : ℕ) (f : (Fin (n+1) → ℝ) → ℝ) :
    (∫ z, f z ∂unitCubeMeasure (n+1)) =
      ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2)
        ∂(volume.restrict (Ioo 0 1)).prod (unitCubeMeasure n) := by
  symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((measurePreserving_piFinSuccAbove
      (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1)) 0).symm).integral_comp' f

lemma integrable_unitCube_cons {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Integrable f (unitCubeMeasure (n+1))) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((volume.restrict (Ioo 0 1)).prod (unitCubeMeasure n)) := by
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    ((measurePreserving_piFinSuccAbove
      (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1)) 0).symm).integrable_comp_of_integrable hf

lemma integrable_unitCube_of_abs_le_weights {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) {b : ℝ}
    (hbd : ∀ z, (∀ i, z i ∈ Ioo (0:ℝ) 1) → |f z| ≤ b * ∏ i, omega (z i)) :
    Integrable f (unitCubeMeasure n) := by
  apply ((Integrable.fintype_prod (fun _ : Fin n => integrableOn_omega)).const_mul b).mono'
    hf.aestronglyMeasurable
  filter_upwards [ae_unitCube n] with z hz
  exact hbd z hz

lemma reflection_with_density_cons {n : ℕ} {x : ℝ} {y : Fin n → ℝ}
    (_hx : 0 < x) (_hy : ∀ i, 0 < y i) :
    omega x * reflectionProduct n x y * density n y =
      density (n+1) (Fin.cons x y) / ∏ j, (y j-x) := by
  rw [density_cons, mul_div_assoc, ← Finset.prod_div_distrib]
  have he : ∏ j, pairKernel x (y j) / (y j-x) = reflectionProduct n x y := by
    apply Finset.prod_congr rfl
    intro j _
    unfold pairKernel
    by_cases h : y j = x
    · simp [h]
    · field_simp [sub_ne_zero.mpr h]
  rw [he]
  ring

lemma lagrange_reverse_denominator_sum {n k : ℕ} (hk : k < n) {z : Fin (n+1) → ℝ}
    (hz : Function.Injective z) :
    ∑ i, z i ^ k / ∏ j ∈ Finset.univ.erase i, (z j-z i) = 0 := by
  classical
  have hd : (Polynomial.X ^ k : Polynomial ℝ).degree <
      ((Finset.univ : Finset (Fin (n+1))).card : WithBot ℕ) := by
    simp only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (by omega : k < n+1)
  have H := Lagrange.coeff_eq_sum hz.injOn hd
  simp only [Polynomial.coeff_X_pow, Finset.card_univ, Fintype.card_fin,
    Nat.add_sub_cancel, ite_eq_right (by omega : n ≠ k), Polynomial.eval_pow,
    Polynomial.eval_X] at H
  have he (i : Fin (n+1)) :
      (∏ j ∈ Finset.univ.erase i, (z j-z i)) =
        (-1:ℝ)^n * ∏ j ∈ Finset.univ.erase i, (z i-z j) := by
    simp_rw [show ∀ j, z j-z i = (-1:ℝ)*(z i-z j) from fun j => by ring]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [he, mul_comm ((-1:ℝ)^n), div_mul_eq_div_mul_one_div]
  rw [← Finset.sum_mul, ← H, zero_mul]



lemma measurable_reflectionMomentKernel (n k : ℕ) : Measurable (reflectionMomentKernel n k) := by
  have ht : Measurable (fun z : Fin (n+1) → ℝ => Fin.tail z) :=
    Measurable.of_eval (fun i => measurable_pi_apply i.succ)
  exact ((((measurable_pi_apply 0).pow_const k).mul (measurable_omega.comp (measurable_pi_apply 0))).mul
    ((measurable_reflectionProduct n).comp ((measurable_pi_apply 0).prodMk ht))).mul
    ((measurable_density n).comp ht)

lemma abs_reflectionMomentKernel_le_weights {n k : ℕ} {z : Fin (n+1) → ℝ}
    (hz : ∀ i, z i ∈ Ioo (0:ℝ) 1) :
    |reflectionMomentKernel n k z| ≤ ∏ i, omega (z i) := by
  have ht : ∀ i, Fin.tail z i ∈ Ioo (0:ℝ) 1 := fun i => hz i.succ
  have hpow : (z 0)^k ≤ 1 := pow_le_one₀ (hz 0).1.le (hz 0).2.le
  have hrefl : |reflectionProduct n (z 0) (Fin.tail z)| ≤ 1 := by
    rw [reflectionProduct, Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun i _ => abs_reflectionFactor_le_one (hz 0).1.le (ht i).1)
  rw [reflectionMomentKernel, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (hz 0).1.le _), abs_of_nonneg (omega_nonneg _),
    abs_of_nonneg (density_nonneg_of_nonneg (fun i => (ht i).1.le)), Fin.prod_univ_succ]
  calc
    _ ≤ 1 * omega (z 0) * 1 * (∏ i, omega (Fin.tail z i)) := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hpow (omega_nonneg _)) hrefl
          (abs_nonneg _) (by positivity [omega_nonneg (z 0)])
      · exact density_cube_le_product ht
      · exact density_nonneg_of_nonneg (fun i => (ht i).1.le)
      · positivity [omega_nonneg (z 0)]
    _ = _ := by simp [Fin.tail_def]

lemma integrable_reflectionMomentKernel (n k : ℕ) :
    Integrable (reflectionMomentKernel n k) (unitCubeMeasure (n+1)) := by
  apply integrable_unitCube_of_abs_le_weights (measurable_reflectionMomentKernel n k) (b := 1)
  intro z hz
  simpa only [one_mul] using abs_reflectionMomentKernel_le_weights (k := k) hz

lemma reflectionMomentKernel_sum_swaps {n k : ℕ} (hk : k < n)
    {z : Fin (n+1) → ℝ} (hz : ∀ i, 0 < z i) :
    ∑ i : Fin (n+1), reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) = 0 := by
  classical
  have he (i : Fin (n+1)) : reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) =
      density (n+1) z * (z i ^ k / ∏ j ∈ Finset.univ.erase i, (z j-z i)) := by
    have hx : 0 < (z ∘ Equiv.swap 0 i) 0 := hz _
    have hy : ∀ j, 0 < Fin.tail (z ∘ Equiv.swap 0 i) j := fun j => hz _
    unfold reflectionMomentKernel
    rw [mul_assoc ((z ∘ Equiv.swap 0 i) 0 ^ k), mul_assoc,
      reflection_with_density_cons hx hy, Fin.cons_self_tail,
      density_perm_of_nonneg (fun i => (hz i).le)]
    have hp : (∏ j, (Fin.tail (z ∘ Equiv.swap 0 i) j - (z ∘ Equiv.swap 0 i) 0)) =
        ∏ j ∈ Finset.univ.erase i, (z j-z i) := by
      have he0 : (∏ j, (Fin.tail (z ∘ Equiv.swap 0 i) j - (z ∘ Equiv.swap 0 i) 0)) =
          ∏ j ∈ Finset.univ.erase (0 : Fin (n+1)), ((z ∘ Equiv.swap 0 i) j - z i) := by
        have he0 : (Finset.univ.erase (0 : Fin (n+1))) =
            Finset.univ.filter (fun j => j ≠ 0) := by ext; simp
        rw [he0, Finset.prod_filter, Fin.prod_univ_succ]
        simp [Fin.tail_def]
      have hs : ∏ j ∈ Finset.univ.erase (0 : Fin (n+1)), ((z ∘ Equiv.swap 0 i) j - z i) =
          ∏ j ∈ Finset.univ.erase i, (z j-z i) := by
        apply Finset.prod_equiv (Equiv.swap 0 i)
        · intro j
          simp [Equiv.swap_apply_eq_iff]
        · intro j hj
          rfl
      exact he0.trans hs
    rw [hp]
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    ring
  simp_rw [he, ← Finset.mul_sum]
  by_cases hi : Function.Injective z
  · rw [lagrange_reverse_denominator_sum hk hi, mul_zero]
  · rw [density_zero_of_not_injective hi, zero_mul]

lemma integral_reflectionMomentKernel_zero {n k : ℕ} (hk : k < n) :
    (∫ z, reflectionMomentKernel n k z ∂unitCubeMeasure (n+1)) = 0 := by
  classical
  have his (i : Fin (n+1)) : Integrable
      (fun z => reflectionMomentKernel n k (z ∘ Equiv.swap 0 i)) (unitCubeMeasure (n+1)) := by
    simpa only [Function.comp_def, StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
        (Equiv.swap 0 i).symm).integrable_comp_of_integrable (integrable_reflectionMomentKernel n k)
  have he (i : Fin (n+1)) :
      (∫ z, reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1)) =
        ∫ z, reflectionMomentKernel n k z ∂unitCubeMeasure (n+1) := by
    simpa only [StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
        (Equiv.swap 0 i).symm).integral_comp' (reflectionMomentKernel n k)
  have hsum : ((n:ℝ)+1) * (∫ z, reflectionMomentKernel n k z ∂unitCubeMeasure (n+1)) = 0 := by
    calc
      _ = ∑ i : Fin (n+1), ∫ z, reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1) := by
        simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      _ = ∫ z, ∑ i : Fin (n+1), reflectionMomentKernel n k (z ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1) :=
        (integral_finsetSum _ (fun i _ => his i)).symm
      _ = ∫ _z, (0 : ℝ) ∂unitCubeMeasure (n+1) := by
        apply integral_congr_ae
        filter_upwards [ae_unitCube (n+1)] with z hz
        exact reflectionMomentKernel_sum_swaps hk (fun i => (hz i).1)
      _ = 0 := integral_zero _ _
  exact (mul_eq_zero.mp hsum).resolve_left (by positivity)

 

theorem reflection_expectation_moments {n k : ℕ} (hk : k < n) :
    (∫ x in Ioo (0:ℝ) 1, momentBasis k x * expectation n (reflectionProduct n x)) = 0 := by
  have hF := integral_reflectionMomentKernel_zero hk
  rw [integral_unitCube_cons, integral_prod _ (integrable_unitCube_cons (integrable_reflectionMomentKernel n k))] at hF
  have he (x : ℝ) : (∫ y, reflectionMomentKernel n k (Fin.cons x y) ∂unitCubeMeasure n) =
      momentBasis k x * (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n) := by
    simp only [reflectionMomentKernel, Fin.cons_zero, Fin.tail_cons, momentBasis,
      mul_assoc, integral_const_mul]
  simp_rw [he] at hF
  calc
    _ = ∫ x in Ioo (0:ℝ) 1,
        (momentBasis k x * (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n)) /
          (∫ y, density n y ∂unitCubeMeasure n) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [expectation_reflection_unitCube n hx.1.le, mul_div_assoc]
    _ = 0 := by rw [integral_div, hF, zero_div]



lemma integrable_coordinateProduct_density {n : ℕ} (s : Finset (Fin n)) :
    Integrable (fun y => (∏ j ∈ s, y j) * density n y) (unitCubeMeasure n) := by
  apply integrable_cube_mul_density (by fun_prop) (b := 1)
  intro y hy
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => by rw [abs_of_pos (hy j).1]; exact (hy j).2.le)

lemma meanCharacteristic_eval (n : ℕ) (x : ℝ) :
    (meanCharacteristic n).eval x = ∫ y, (∏ j, (y j-x)) * density n y ∂unitCubeMeasure n := by
  classical
  have he (y : Fin n → ℝ) : (∏ j, (y j-x)) * density n y =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : ℝ)^s.card * x^s.card) * ((∏ j ∈ Finset.univ \ s, y j) * density n y) := by
    rw [Finset.prod_sub, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Finset.prod_const]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun s _ => (integrable_coordinateProduct_density _).const_mul _)]
  simp only [meanCharacteristic, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, integral_const_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma meanCharacteristic_natDegree (n : ℕ) : (meanCharacteristic n).natDegree ≤ n := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  apply (Polynomial.natDegree_mul_le).trans
  simpa only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add, Finset.card_univ,
    Fintype.card_fin] using (Finset.card_le_card (Finset.mem_powerset.mp hs))

lemma polynomial_transformedBasis (n : ℕ) (p : Polynomial ℝ) (hp : p.natDegree < n)
    {x : ℝ} (hx : 0 < x) :
    x * (∫ y in Ioo (0:ℝ) 1, p.eval y * omega y / (x+y)) =
      ∑ k : Fin n, p.coeff k.val * transformedBasis k.val x := by
  have hev (y : ℝ) : p.eval y = ∑ k : Fin n, p.coeff k.val * y^k.val := by
    rw [Polynomial.eval_eq_sum_range' hp, ← Fin.sum_univ_eq_sum_range]
  have heq : (fun y => x * (p.eval y * omega y / (x+y))) =
      fun y => ∑ k : Fin n, p.coeff k.val * (boundedCauchy x y * momentBasis k.val y) := by
    funext y
    rw [hev]
    simp only [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold boundedCauchy momentBasis
    ring
  rw [← integral_const_mul, heq,
    integral_finsetSum _ (fun k _ => (integrableOn_boundedCauchy_basis k.val hx).const_mul _)]
  simp only [integral_const_mul, transformedBasis]


lemma measurable_reflectionResidueKernel (n : ℕ) (x : ℝ) (i : Fin n) :
    Measurable (reflectionResidueKernel n x i) := by
  unfold reflectionResidueKernel reflectionResidue
  apply Measurable.div
  · apply Measurable.mul _ (measurable_density n)
    fun_prop
  · fun_prop

lemma reflectionResidueKernel_perm {n : ℕ} (x : ℝ) {y : Fin n → ℝ}
    (hy : ∀ i, 0 ≤ y i) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reflectionResidueKernel n x i (y ∘ σ) = reflectionResidueKernel n x (σ i) y := by
  unfold reflectionResidueKernel
  rw [reflectionResidue_perm, density_perm_of_nonneg hy]
  rfl

lemma reflectionResidueKernel_cons {n : ℕ} (x : ℝ) {u : ℝ} {y : Fin n → ℝ}
    (hu : 0 < u) (hy : ∀ i, 0 < y i) :
    reflectionResidueKernel (n+1) x 0 (Fin.cons u y) =
      2 * omega u / (x+u) * ((∏ j, (y j-u)) * density n y) := by
  rw [reflectionResidueKernel, reflectionResidue_density_cons hu hy, Fin.cons_zero]
  ring

lemma abs_reflectionResidueKernel_zero_le {n : ℕ} {x : ℝ} (hx : 0 < x)
    {z : Fin (n+1) → ℝ} (hz : ∀ i, z i ∈ Ioo (0:ℝ) 1) :
    |reflectionResidueKernel (n+1) x 0 z| ≤ (2/x) * ∏ i, omega (z i) := by
  have hprod : |∏ j : Fin n, (Fin.tail z j-z 0)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => by
      rw [abs_le]; constructor <;> dsimp [Fin.tail_def] <;> linarith [(hz j.succ).1, (hz j.succ).2, (hz 0).1, (hz 0).2])
  have hd : 0 ≤ density n (Fin.tail z) := density_nonneg_of_nonneg fun j => (hz j.succ).1.le
  have hω := omega_nonneg (z 0)
  have hz0 : 0 < z 0 := (hz 0).1
  have he := reflectionResidueKernel_cons (y := Fin.tail z) x (hz 0).1 (fun j => (hz j.succ).1)
  change reflectionResidueKernel (n+1) x 0 (Fin.cons (z 0) (Fin.tail z)) = _ at he
  rw [Fin.cons_self_tail] at he
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*omega (z 0)/(x+z 0)), abs_mul, abs_of_nonneg hd]
  calc
    _ ≤ (2*omega (z 0)/(x+z 0)) * (1 * density n (Fin.tail z)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hd) (by positivity [ (hz 0).1 ])
    _ ≤ (2*omega (z 0)/x) * density n (Fin.tail z) := by
      rw [one_mul]
      apply mul_le_mul_of_nonneg_right _ hd
      exact div_le_div_of_nonneg_left (by positivity) hx (le_add_of_nonneg_right (hz 0).1.le)
    _ ≤ (2*omega (z 0)/x) * ∏ j : Fin n, omega (Fin.tail z j) :=
      mul_le_mul_of_nonneg_left (density_cube_le_product (fun j => hz j.succ)) (by positivity)
    _ = _ := by rw [Fin.prod_univ_succ]; simp only [Fin.tail_def]; ring

lemma abs_reflectionResidueKernel_le {n : ℕ} {x : ℝ} (hx : 0 < x)
    (i : Fin (n+1)) {z : Fin (n+1) → ℝ} (hz : ∀ i, z i ∈ Ioo (0:ℝ) 1) :
    |reflectionResidueKernel (n+1) x i z| ≤ (2/x) * ∏ j, omega (z j) := by
  have he : reflectionResidueKernel (n+1) x 0 (z ∘ Equiv.swap 0 i) =
      reflectionResidueKernel (n+1) x i z := by
    rw [reflectionResidueKernel_perm _ (fun i => (hz i).1.le), Equiv.swap_apply_left]
  have h := abs_reflectionResidueKernel_zero_le (z := z ∘ Equiv.swap 0 i) hx (fun j => hz (Equiv.swap 0 i j))
  rw [he] at h
  apply h.trans_eq
  congr 1
  exact Fintype.prod_equiv (Equiv.swap 0 i) _ _ (fun _ => rfl)

lemma integrable_reflectionResidueKernel {n : ℕ} {x : ℝ} (hx : 0 < x) (i : Fin (n+1)) :
    Integrable (reflectionResidueKernel (n+1) x i) (unitCubeMeasure (n+1)) := by
  exact integrable_unitCube_of_abs_le_weights (measurable_reflectionResidueKernel _ _ _)
    (fun _ hz => abs_reflectionResidueKernel_le hx i hz)

end
end CriticalStrip

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
open scoped BigOperators
open Set MeasureTheory
lemma integral_reflectionResidueKernel_eq_zero_index {n : ℕ} {x : ℝ}
    (i : Fin (n+1)) :
    (∫ z, reflectionResidueKernel (n+1) x i z ∂unitCubeMeasure (n+1)) =
      ∫ z, reflectionResidueKernel (n+1) x 0 z ∂unitCubeMeasure (n+1) := by
  have he := (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
    (Equiv.swap 0 i).symm).integral_comp' (reflectionResidueKernel (n+1) x 0)
  simp only [StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] at he
  refine (integral_congr_ae ?_).trans he
  filter_upwards [ae_unitCube (n+1)] with z hz
  rw [reflectionResidueKernel_perm x (fun i => (hz i).1.le), Equiv.swap_apply_left]

lemma integral_reflectionResidueKernel_zero_index {n : ℕ} {x : ℝ} (hx : 0 < x) :
    (∫ z, reflectionResidueKernel (n+1) x 0 z ∂unitCubeMeasure (n+1)) =
      2 * ∫ u in Ioo (0:ℝ) 1, (meanCharacteristic n).eval u * omega u / (x+u) := by
  rw [integral_unitCube_cons, integral_prod _ (integrable_unitCube_cons (integrable_reflectionResidueKernel hx 0)),
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  calc
    _ = ∫ y, 2*omega u/(x+u)*((∏ j, (y j-u))*density n y) ∂unitCubeMeasure n := by
      apply integral_congr_ae
      filter_upwards [ae_unitCube n] with y hy
      exact reflectionResidueKernel_cons x hu.1 (fun i => (hy i).1)
    _ = _ := by rw [integral_const_mul, ← meanCharacteristic_eval]; ring

lemma reflection_partialFractions_density {n : ℕ} {y : Fin (n+1) → ℝ}
    (hy : ∀ i, 0 < y i) {x : ℝ} (hx : 0 ≤ x) :
    reflectionProduct (n+1) x y * density (n+1) y =
      density (n+1) y - x * ∑ i, reflectionResidueKernel (n+1) x i y := by
  by_cases hi : Function.Injective y
  · rw [reflection_partialFractions_distinct (Nat.succ_pos n) hy hi hx, sub_mul,
      one_mul, mul_assoc, Finset.sum_mul]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold reflectionResidueKernel
    ring
  · simp only [density_zero_of_not_injective hi, reflectionResidueKernel,
      mul_zero, zero_div, Finset.sum_const_zero, sub_self]

lemma expectation_reflection_cauchy (n : ℕ) {x : ℝ} (hx : 0 < x) :
    expectation (n+1) (reflectionProduct (n+1) x) =
      1 - (2*((n:ℝ)+1)/(∫ z, density (n+1) z ∂unitCubeMeasure (n+1))) *
        ∑ k : Fin (n+1), (meanCharacteristic n).coeff k.val * transformedBasis k.val x := by
  have hD : (∫z, density (n+1) z ∂unitCubeMeasure (n+1)) ≠ 0 := by
    rw [integral_density_unitCube]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (n+1)) (normalizer_pos _).ne'
  rw [expectation_reflection_unitCube (n+1) hx.le]
  have he : (∫ y, reflectionProduct (n+1) x y * density (n+1) y ∂unitCubeMeasure (n+1)) =
      (∫ y, density (n+1) y ∂unitCubeMeasure (n+1)) -
        x * ((n:ℝ)+1) * (2 * ∫ u in Ioo (0:ℝ) 1, (meanCharacteristic n).eval u * omega u / (x+u)) := by
    calc
      _ = ∫ y, density (n+1) y - x * ∑ i, reflectionResidueKernel (n+1) x i y ∂unitCubeMeasure (n+1) := by
        apply integral_congr_ae
        filter_upwards [ae_unitCube (n+1)] with y hy
        exact reflection_partialFractions_density (fun i => (hy i).1) hx.le
      _ = _ := by
        rw [integral_sub (integrable_density_unitCube (n+1))
          ((integrable_finsetSum _ (fun i _ => integrable_reflectionResidueKernel hx i)).const_mul x),
          integral_const_mul, integral_finsetSum _ (fun i _ => integrable_reflectionResidueKernel hx i)]
        simp only [integral_reflectionResidueKernel_eq_zero_index, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
          integral_reflectionResidueKernel_zero_index hx, mul_assoc]
  rw [he, ← polynomial_transformedBasis (n+1) (meanCharacteristic n) (by have := meanCharacteristic_natDegree n; omega) hx]
  field_simp

 

theorem reflection_expectation_cauchyMomentProblem (n : ℕ) :
    ∃ v : Fin (n+1) → ℝ, CauchyMomentProblem (n+1) 1 v ∧
      ∀ x : ℝ, 0 < x → expectation (n+1) (reflectionProduct (n+1) x) = cauchyDefect (n+1) 1 v x := by
  let v : Fin (n+1) → ℝ := fun k =>
    (2*((n:ℝ)+1)/(∫z, density (n+1) z ∂unitCubeMeasure (n+1))) * (meanCharacteristic n).coeff k.val
  have he (x : ℝ) (hx : 0 < x) : expectation (n+1) (reflectionProduct (n+1) x) =
      cauchyDefect (n+1) 1 v x := by
    rw [expectation_reflection_cauchy n hx]
    simp only [cauchyDefect, v, Finset.mul_sum, mul_assoc]
  refine ⟨v, ?_, he⟩
  intro j
  calc
    _ = ∫ x in Ioo (0:ℝ) 1, momentBasis j.val x * expectation (n+1) (reflectionProduct (n+1) x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [he x hx.1]
    _ = 0 := reflection_expectation_moments j.isLt

end

 

noncomputable section
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators

lemma harmonicCoordinate_natDegree : harmonicCoordinate.natDegree = 4 := by
  unfold harmonicCoordinate
  compute_degree <;> norm_num

lemma harmonicCoordinate_leadingCoeff : harmonicCoordinate.leadingCoeff = -1 := by
  rw [leadingCoeff, harmonicCoordinate_natDegree]
  have he : harmonicCoordinate = (X^2-X^4 : Polynomial ℝ) := by unfold harmonicCoordinate; ring
  rw [he]
  norm_num

lemma degree_lt_implies_natDegree_lt {N : ℕ} (hN : 0 < N) {p : Polynomial ℝ}
    (hp : p.degree < (N : WithBot ℕ)) : p.natDegree < N := by
  by_cases h : p = 0
  · simpa [h] using hN
  · exact (natDegree_lt_iff_degree_lt h).mpr hp

lemma coeff_comp_top_of_le {p q : Polynomial ℝ} {N : ℕ} (hp : p.natDegree ≤ N)
    (hq : q.natDegree ≠ 0) :
    (p.comp q).coeff (N*q.natDegree) = p.coeff N * q.leadingCoeff^N := by
  rcases hp.eq_or_lt with he | he
  · rw [← he]
    exact coeff_comp_degree_mul_degree hq
  · rw [coeff_eq_zero_of_natDegree_lt he, zero_mul]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_comp]
    exact Nat.mul_lt_mul_of_pos_right he (Nat.pos_of_ne_zero hq)

lemma tildePoly_eval_zero (N : ℕ) {p : Polynomial ℝ} (hp : p.natDegree ≤ N) :
    (tildePoly N p).eval 0 = p.coeff N * (1/8:ℝ)^N := by
  have hq : (Polynomial.C (1/8:ℝ)*(1+X)).natDegree = 1 := by compute_degree; norm_num
  have hqL : (Polynomial.C (1/8:ℝ)*(1+X)).leadingCoeff = 1/8 := by
    rw [leadingCoeff, hq]
    norm_num [coeff_C_mul, coeff_add, coeff_one]
  rw [← coeff_zero_eq_eval_zero, tildePoly, coeff_reflect, revAt_zero]
  convert coeff_comp_top_of_le hp (by rw [hq]; norm_num) using 1 <;> simp only [hq, mul_one, hqL]

lemma comp_harmonic_odd (p : Polynomial ℝ) (n : ℕ) :
    (p.comp harmonicCoordinate).coeff (2*n+1) = 0 := by
  have he : harmonicCoordinate = (X*(1-X) : Polynomial ℝ).comp (X^2) := by
    simp only [mul_comp, sub_comp, X_comp, one_comp]
    rfl
  rw [he, ← comp_assoc, ← expand_eq_comp_X_pow, coeff_expand (by norm_num)]
  simp

lemma projection_top_coefficients (N : ℕ) (hN : 1 ≤ N) (P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ)) :
    let Q := P.comp harmonicCoordinate + X * J.comp harmonicCoordinate + X^2 * E.comp harmonicCoordinate
    Q.coeff (4*N+1) = (-8:ℝ)^N * (tildePoly N J).eval 0 ∧
      Q.coeff (4*N) = (-8:ℝ)^N * (tildePoly N P).eval 0 := by
  have hn : 0 < N := by omega
  have hen := degree_lt_implies_natDegree_lt hn hE
  have he : (X^2*E.comp harmonicCoordinate).natDegree < 4*N := by
    exact natDegree_mul_le.trans_lt (by rw [natDegree_X_pow, natDegree_comp, harmonicCoordinate_natDegree]; omega)
  have hpcomp : (P.comp harmonicCoordinate).natDegree ≤ 4*N := by
    rw [natDegree_comp, harmonicCoordinate_natDegree]; omega
  have hjN : (J.comp harmonicCoordinate).coeff (4*N) = J.coeff N * (-1:ℝ)^N := by
    simpa only [harmonicCoordinate_natDegree, harmonicCoordinate_leadingCoeff, mul_comm] using
      coeff_comp_top_of_le (q := harmonicCoordinate) hJ (by rw [harmonicCoordinate_natDegree]; norm_num)
  have hpN : (P.comp harmonicCoordinate).coeff (4*N) = P.coeff N * (-1:ℝ)^N := by
    simpa only [harmonicCoordinate_natDegree, harmonicCoordinate_leadingCoeff, mul_comm] using
      coeff_comp_top_of_le (q := harmonicCoordinate) hP (by rw [harmonicCoordinate_natDegree]; norm_num)
  have hjOdd : (X*J.comp harmonicCoordinate).coeff (4*N) = 0 := by
    have ha : 4*N = (4*N-1)+1 := by omega
    rw [ha, coeff_X_mul]
    have hb : 4*N-1 = 2*(2*N-1)+1 := by omega
    rw [hb, comp_harmonic_odd]
  have hscalar (a : ℝ) : a*(-1:ℝ)^N = (-8:ℝ)^N*(a*(1/8:ℝ)^N) := by
    rw [mul_left_comm, ← mul_pow]
    norm_num
  dsimp only
  constructor
  · rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt (by omega : (P.comp harmonicCoordinate).natDegree < 4*N+1),
      coeff_eq_zero_of_natDegree_lt (he.trans_le (by omega)), coeff_X_mul,
      zero_add, add_zero, hjN, tildePoly_eval_zero N hJ]
    exact hscalar _
  · rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt he, add_zero, hjOdd, add_zero,
      hpN, tildePoly_eval_zero N hP]
    exact hscalar _

lemma homogeneousQ_monic {N : ℕ} {g : Polynomial ℝ} (hg : g.Monic) :
    (homogeneousQ N g).Monic := by
  exact (((monic_X_sub_C C).pow _).mul ((monic_X_sub_C c).pow _)).mul hg

lemma homogeneousQ_natDegree {N : ℕ} {g : Polynomial ℝ} (hg : g.Monic) (hd : g.natDegree = N) :
    (homogeneousQ N g).natDegree = 4*N+1 := by
  rw [homogeneousQ, (((monic_X_sub_C C).pow _).mul ((monic_X_sub_C c).pow _)).natDegree_mul hg,
    ((monic_X_sub_C C).pow _).natDegree_mul ((monic_X_sub_C c).pow _)]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one, hd]
  omega

lemma projectionD_expectation (N : ℕ) (hN : 1 ≤ N) (g P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    ∀ x : ℝ, 0 < x → projectionD (tildePoly N J) (tildePoly N E) x =
      (tildePoly N J).eval 0 * expectation N (reflectionProduct N x) := by
  have hEn : E.natDegree < N := degree_lt_implies_natDegree_lt (by omega) hE
  have hdiv : X ∣ tildePoly N E := X_dvd_iff.2 (by
    simpa only [coeff_zero_eq_eval_zero] using tildePoly_zero_of_degree_lt N hE)
  obtain ⟨e, he⟩ := hdiv
  have hen : e.natDegree < N := by
    by_cases he0 : e = 0
    · simp [he0]; omega
    have hb := tildePoly_natDegree_le N hEn.le
    rw [he, natDegree_X_mul he0] at hb
    omega
  have hF : ∀ j : ℕ, j ≤ N → Tendsto
      (fun t : ℝ => (-t)^j * projectionF (tildePoly N P) (tildePoly N J) (tildePoly N E) (-t))
      atTop (𝓝 0) := fun j hj => tilde_F_decay N g P J E hP hJ hEn.le hQ j hj
  obtain ⟨L, hD⟩ := tilde_D_limit N g P J E hP hJ hEn.le hQ
  change Tendsto (fun z : ℝ => projectionD (tildePoly N J) (tildePoly N E) z) atTop (𝓝 L) at hD
  have hDc := projectionD_cauchy (tildePoly N J) e (by simpa only [← he] using hD)
  have hm := projection_moments_of_decay N (tildePoly N P) (tildePoly N J) (tildePoly N E) hF
  let D₀ := (tildePoly N J).eval 0
  let v : Fin N → ℝ := fun k => -(Real.sqrt 2 / Real.pi) * (e.coeff k.val * (-1)^k.val)
  have hev {x : ℝ} (hx : 0 < x) :
      projectionD (tildePoly N J) (tildePoly N E) x = cauchyDefect N D₀ v x := by
    rw [he, hDc x hx, mul_assoc, stieltjes_polynomial_basis N e hen hx]
    simp only [cauchyDefect, v, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add, D₀]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hv : CauchyMomentProblem N D₀ v := by
    intro j
    calc
      _ = ∫ x in Ioo (0:ℝ) 1, x^j.val * (projectionD (tildePoly N J) (tildePoly N E) x * omega x) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx
        dsimp only
        rw [hev hx.1]
        unfold momentBasis
        ring
      _ = 0 := hm j.val j.isLt
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  obtain ⟨w, hw, hew⟩ := reflection_expectation_cauchyMomentProblem n
  let w' : Fin (n+1) → ℝ := fun i => D₀ * w i
  have bew (x : ℝ) : cauchyDefect (n+1) D₀ w' x = D₀ * cauchyDefect (n+1) 1 w x := by
    simp only [cauchyDefect, w', mul_sub, mul_one, Finset.mul_sum, mul_assoc]
  have hw' : CauchyMomentProblem (n+1) D₀ w' := by
    intro j
    simp_rw [bew]
    have eq : (fun x => momentBasis j.val x * (D₀ * cauchyDefect (n+1) 1 w x)) =
        fun x => D₀ * (momentBasis j.val x * cauchyDefect (n+1) 1 w x) := by funext x; ring
    rw [eq, integral_const_mul, hw j, mul_zero]
  have huniq : v = w' := (existsUnique_cauchyMomentProblem (n+1) D₀).unique hv hw'
  intro x hx
  rw [hev hx, huniq, bew, ← hew x hx]

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RightStieltjes
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

lemma transformed_omega_extended {s t : ℝ} (hs : -1 < s) (ht : 0 < t) :
    |(-8 * t * (t ^ 2 + 1) / uniformDen t ^ 2)| •
        (s * omega (uniformizer t) / (1 + s * uniformizer t)) =
      quarticWeighted (Real.sqrt ((1 + s) / 2)) t -
        quarticWeighted (Real.sqrt (1 / 2)) t := by
  rw [omega_uniformizer ht, abs_of_neg (by
    exact div_neg_of_neg_of_pos (by nlinarith [sq_nonneg t])
      (sq_pos_of_pos (uniformDen_pos t))), smul_eq_mul]
  unfold quarticWeighted quarticDen
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (1 + s) / 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  unfold uniformizer uniformDen
  have hd : 1 + t^2*4 + t^4*2 + s ≠ 0 := by nlinarith [sq_nonneg t,sq_nonneg (t^2)]
  field_simp
  ring_nf
  field_simp [hd]
  ring

lemma omega_resolvent_extended {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x => s * omega x / (1 + s * x)) (Ioo 0 1) ∧
      (∫ x in Ioo 0 1, s * omega x / (1 + s * x)) =
        Real.pi * (minusBranch s - minusBranch 0) := by
  have hr : 0 < Real.sqrt ((1 + s) / 2) := Real.sqrt_pos.mpr (by linarith)
  have hr0 : 0 < Real.sqrt ((1 : ℝ) / 2) := by positivity
  have hint := (quartic_weighted_integral hr).1.sub (quartic_weighted_integral hr0).1
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (uniformizer_deriv t).hasDerivWithinAt) uniformizer_inj
    (fun x => s * omega x / (1 + s * x))
  rw [uniformizer_image] at hi
  constructor
  · apply hi.2
    exact IntegrableOn.congr_fun hint (fun t ht => (transformed_omega_extended hs ht).symm)
      measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (uniformizer_deriv t).hasDerivWithinAt) uniformizer_inj
      (fun x => s * omega x / (1 + s * x))
    rw [uniformizer_image] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht => transformed_omega_extended hs ht),
      integral_sub (quartic_weighted_integral hr).1 (quartic_weighted_integral hr0).1,
      quartic_weighted_integral_sqrt hr, quartic_weighted_integral_sqrt hr0]
    simp only [minusBranch, add_zero]
    ring

 
lemma stieltjes_omega_right {z : ℝ} (hz : 1 < z) :
    fBranch z = C + (1 / Real.pi) *
        ∫ x in Ioo (0 : ℝ) 1, omega x / (x - z) := by
  have hz0 : 0 < z := by linarith
  have hs : -1 < -1 / z := by rw [lt_div_iff₀ hz0]; linarith
  have heq : EqOn (fun x => (-1 / z) * omega x / (1 + (-1 / z) * x))
      (fun x => omega x / (x - z)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    have ha : 1 + (-1 / z) * x ≠ 0 := by
      have he : 1 + (-1 / z) * x = (z-x)/z := by field_simp; ring
      rw [he]; exact div_ne_zero (by linarith [hx.2]) hz0.ne'
    have hb : x - z ≠ 0 := by linarith [hx.2]
    apply (div_eq_div_iff ha hb).2
    field_simp
    ring
  have h := (omega_resolvent_extended hs).2
  rw [setIntegral_congr_fun measurableSet_Ioo heq, minusBranch_zero] at h
  have he : minusBranch (-1 / z) = fBranch z := by
    unfold minusBranch fBranch
    congr 4
    ring
  rw [he] at h
  change fBranch z = C + (1 / Real.pi) * _
  change _ = Real.pi * (fBranch z - C) at h
  rw [h]
  field_simp
  ring

lemma transformed_squareWeight_extended {s t : ℝ} (hs : -1 < s) (ht : 0 < t) :
    |(-2 * t / (1 + t ^ 2) ^ 2)| •
        (s * squareWeight (squareUniformizer t) / (1 + s * squareUniformizer t)) =
      (1 / Real.sqrt 2) * ((1 + s) * ((1 + s) + t ^ 2)⁻¹ - (1 + t ^ 2)⁻¹) := by
  rw [squareWeight_uniformizer ht, abs_of_neg (by
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)), smul_eq_mul]
  unfold squareUniformizer
  have hd : 1 + t^2 + s ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp
  ring_nf
  field_simp [hd]
  ring

lemma squareWeight_resolvent_extended {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x => s * squareWeight x / (1 + s * x)) (Ioo 0 1) ∧
      (∫ x in Ioo 0 1, s * squareWeight x / (1 + s * x)) =
        (Real.pi / (2 * Real.sqrt 2)) * (Real.sqrt (1 + s) - 1) := by
  let a := Real.sqrt (1 + s)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = 1 + s := Real.sq_sqrt (by linarith)
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
    exact IntegrableOn.congr_fun hint (fun t ht => (transformed_squareWeight_extended hs ht).symm)
      measurableSet_Ioi
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (squareUniformizer_deriv t).hasDerivWithinAt) squareUniformizer_inj
      (fun x => s * squareWeight x / (1 + s * x))
    rw [squareUniformizer_image] at h
    rw [h, setIntegral_congr_fun measurableSet_Ioi (fun t ht => transformed_squareWeight_extended hs ht),
      integral_const_mul, integral_sub (hint1.const_mul (1 + s)) hint0,
      integral_const_mul, ← ha2, scaled_cauchy_Ioi ha, integral_Ioi_inv_one_add_sq,
      Real.arctan_zero, sub_zero]
    rw [Real.sqrt_sq ha.le]
    field_simp

lemma stieltjes_omega_square_right {z : ℝ} (hz : 1 < z) :
    fBranch z ^ 2 = C ^ 2 + (1 / Real.pi) *
        ∫ x in Ioo (0 : ℝ) 1, lBranch x * omega x / (x - z) := by
  have hz0 : 0 < z := by linarith
  have hs : -1 < -1 / z := by rw [lt_div_iff₀ hz0]; linarith
  have heq : EqOn (fun x => (-1 / z) * squareWeight x / (1 + (-1 / z) * x))
      (fun x => lBranch x * omega x / (x - z)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    rw [lBranch_mul_omega hx]
    have ha : 1 + (-1 / z) * x ≠ 0 := by
      have he : 1 + (-1 / z) * x = (z-x)/z := by field_simp; ring
      rw [he]; exact div_ne_zero (by linarith [hx.2]) hz0.ne'
    have hb : x - z ≠ 0 := by linarith [hx.2]
    apply (div_eq_div_iff ha hb).2
    field_simp
    ring
  have h := (squareWeight_resolvent_extended hs).2
  rw [setIntegral_congr_fun measurableSet_Ioo heq] at h
  have hC : C ^ 2 = (1 + Real.sqrt (1 / 2)) / 2 := by
    change (Real.cos (Real.pi/8))^2 = _
    rw [← minusBranch_zero]
    unfold minusBranch
    simp only [add_zero]
    exact Real.sq_sqrt (by positivity)
  rw [h, hC, fBranch, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt ((1 - 1 / z) / 2)) / 2)]
  have heq' : 1 - 1 / z = 1 + -1 / z := by ring
  rw [heq', Real.sqrt_div (by linarith : (0 : ℝ) ≤ 1 + -1 / z),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  field_simp
  ring



lemma offCut_of_outside {z : ℝ} (hz : z < 0 ∨ 1 < z) : offCut 1 z := by
  intro x hx
  simp only [one_mul]
  rcases hz with hz | hz <;> linarith [hx.1,hx.2]

lemma fBranch_transform_outside {z : ℝ} (hz : z < 0 ∨ 1 < z) :
    fBranch z = C - (1 / Real.pi) * realStieltjes 1 omega z := by
  have h : fBranch z = C + (1 / Real.pi) * ∫ x in Ioo (0:ℝ) 1, omega x/(x-z) := by
    rcases hz with hz | hz
    · exact stieltjes_omega hz
    · exact stieltjes_omega_right hz
  have heq : (∫ x in Ioo (0 : ℝ) 1, omega x / (x - z)) = -realStieltjes 1 omega z := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [one_mul]
    rw [show x - z = -(z - x) by ring, div_neg]
  simpa only [heq, mul_neg, ← sub_eq_add_neg] using h

lemma fBranch_square_transform_outside {z : ℝ} (hz : z < 0 ∨ 1 < z) :
    fBranch z ^ 2 = C ^ 2 -
      (1 / Real.pi) * realStieltjes 1 (fun x => lBranch x * omega x) z := by
  have h : fBranch z ^ 2 = C ^ 2 + (1 / Real.pi) *
      ∫ x in Ioo (0:ℝ) 1, lBranch x * omega x/(x-z) := by
    rcases hz with hz | hz
    · exact stieltjes_omega_square hz
    · exact stieltjes_omega_square_right hz
  have heq : (∫ x in Ioo (0 : ℝ) 1, lBranch x * omega x / (x - z)) =
      -realStieltjes 1 (fun x => lBranch x * omega x) z := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [one_mul]
    rw [show x - z = -(z - x) by ring, div_neg]
  simpa only [heq, mul_neg, ← sub_eq_add_neg] using h

 
lemma projectionF_polynomial_outside (P J E : Polynomial ℝ) :
    ∃ R : Polynomial ℝ, ∀ z : ℝ, z < 0 ∨ 1 < z →
      projectionF P J E z = R.eval z - (1 / Real.pi) *
        realStieltjes 1 (fun x => projectionD J E x * omega x) z := by
  obtain ⟨Rj, hRj⟩ := polynomial_mul_realStieltjes (a := (1 : ℝ)) integrableOn_omega J
  obtain ⟨Re, hRe⟩ := polynomial_mul_realStieltjes (a := (1 : ℝ)) integrableOn_lBranch_omega E
  refine ⟨P + Polynomial.C C * J + Polynomial.C (C ^ 2) * E -
    Polynomial.C (1 / Real.pi) * (Rj + Re), ?_⟩
  intro z hz
  have hj := hRj z (offCut_of_outside hz)
  have he := hRe z (offCut_of_outside hz)
  have hsum := realStieltjes_add
    (integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_omega J)
    (integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_lBranch_omega E)
    (offCut_of_outside hz)
  have hw : (fun x => J.eval (1 * x) * omega x + E.eval (1 * x) * (lBranch x * omega x)) =
      fun x => projectionD J E x * omega x := by
    funext x
    simp only [one_mul, projectionD]
    ring
  rw [hw] at hsum
  simp only [one_mul] at hj he hsum
  rw [projectionF, fBranch_square_transform_outside hz, fBranch_transform_outside hz, hsum]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination -(1 / Real.pi) * hj - (1 / Real.pi) * he

 
lemma projectionF_cauchy_outside (P J E : Polynomial ℝ)
    (hF : Tendsto (fun t : ℝ => projectionF P J E (-t)) atTop (𝓝 0)) :
    ∀ z : ℝ, z < 0 ∨ 1 < z → projectionF P J E z = -(1 / Real.pi) *
      realStieltjes 1 (fun x => projectionD J E x * omega x) z := by
  obtain ⟨R, hR⟩ := projectionF_polynomial_outside P J E
  have hz : Tendsto (fun t : ℝ => ‖-t‖) atTop atTop := by
    simpa only [norm_neg] using (tendsto_norm_atTop_atTop : Tendsto (fun t : ℝ => ‖t‖) atTop atTop)
  have hlim := hF.add ((tendsto_realStieltjes_zero (integrableOn_projection_weight J E)
    (by norm_num : |(1 : ℝ)| ≤ 1) hz).const_mul (1 / Real.pi))
  have hRlim : Tendsto (fun t : ℝ => R.eval (-t)) atTop (𝓝 0) := by
    have hlim' : Tendsto (fun t : ℝ => projectionF P J E (-t) + (1 / Real.pi) *
        realStieltjes 1 (fun x => projectionD J E x * omega x) (-t)) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using hlim
    apply hlim'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := hR (-t) (Or.inl (neg_neg_of_pos ht))
    linarith
  have hR0 := polynomial_constant_of_limit hz R hRlim
  intro z hz
  simpa only [hR0, Polynomial.eval_C, zero_sub, neg_mul] using hR z hz

end

 

 

noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators Classical

 

lemma lagrange_reverse_cauchy_sum {n : ℕ} {y : Fin (n+1) → ℝ}
    (hy : Function.Injective y) {z : ℝ} (hz : ∀ i, z ≠ y i) :
    ∑ i, 1 / ((z-y i) * ∏ j ∈ Finset.univ.erase i, (y j-y i)) =
      (-1:ℝ)^n / ∏ i, (z-y i) := by
  have H := congrArg (Polynomial.eval z) (Lagrange.sum_basis hy.injOn
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n+1))).Nonempty))
  simp only [eval_finsetSum, eval_one] at H
  have hb (i : Fin (n+1)) := Lagrange.eval_basis_not_at_node (Finset.mem_univ i) (hz i)
  simp only [Lagrange.eval_nodal, Lagrange.nodalWeight, Finset.prod_inv_distrib] at hb
  have he (i : Fin (n+1)) :
      (∏ j ∈ Finset.univ.erase i, (y j-y i)) =
        (-1:ℝ)^n * ∏ j ∈ Finset.univ.erase i, (y i-y j) := by
    simp_rw [show ∀ j, y j-y i = (-1:ℝ)*(y i-y j) from fun j => by ring]
    rw [Finset.prod_mul_distrib]
    simp
  have he' (i : Fin (n+1)) :
      1 / ((z-y i) * ∏ j ∈ Finset.univ.erase i, (y j-y i)) =
        (-1:ℝ)^n * (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ * (z-y i)⁻¹ := by
    rw [he, one_div, mul_inv, mul_inv]
    ring_nf
    simp only [inv_neg, inv_one]
    ring
  simp_rw [he']
  have hh : (∏ i, (z-y i)) *
      (∑ i, (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ * (z-y i)⁻¹) = 1 := by
    simpa only [hb, ← Finset.mul_sum] using H
  have hd : (∏ i, (z-y i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hz i)
  have hh' : (∑ i, (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ * (z-y i)⁻¹) =
      1/(∏ i, (z-y i)) := (eq_div_iff hd).mpr (by simpa only [mul_comm] using hh)
  calc
    _ = (-1:ℝ)^n * (∑ i, (∏ j ∈ Finset.univ.erase i, (y i-y j))⁻¹ * (z-y i)⁻¹) := by
      simp_rw [mul_assoc]; rw [Finset.mul_sum]
    _ = _ := by rw [hh']; ring

lemma measurable_reflectionCauchyKernel (n : ℕ) (z : ℝ) :
    Measurable (reflectionCauchyKernel n z) :=
  (measurable_reflectionMomentKernel n 0).div (measurable_const.sub (measurable_pi_apply 0))

lemma integrable_reflectionCauchyKernel (n : ℕ) {z : ℝ} (hz : 1 < z) :
    Integrable (reflectionCauchyKernel n z) (unitCubeMeasure (n+1)) := by
  apply integrable_unitCube_of_abs_le_weights (measurable_reflectionCauchyKernel n z)
    (b := (z-1)⁻¹)
  intro y hy
  rw [reflectionCauchyKernel, abs_div, abs_of_pos (by linarith [(hy 0).2] : 0 < z-y 0)]
  calc
    _ ≤ (∏ i, omega (y i))/(z-1) := div_le_div₀
      (Finset.prod_nonneg fun i _ => omega_nonneg _) (abs_reflectionMomentKernel_le_weights hy)
      (by linarith) (by linarith [(hy 0).2])
    _ = _ := by ring

lemma reflectionCauchyKernel_sum_swaps (n : ℕ) {z : ℝ} {y : Fin (n+1) → ℝ}
    (hy : ∀ i, 0 < y i) (hz : ∀ i, z ≠ y i) :
    ∑ i, reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) =
      (-1:ℝ)^n * (density (n+1) y / ∏ i, (z-y i)) := by
  have he (i : Fin (n+1)) : reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) =
      density (n+1) y * (1 / ((z-y i) * ∏ j ∈ Finset.univ.erase i, (y j-y i))) := by
    have hx : 0 < (y ∘ Equiv.swap 0 i) 0 := hy _
    have ht : ∀ j, 0 < Fin.tail (y ∘ Equiv.swap 0 i) j := fun j => hy _
    unfold reflectionCauchyKernel reflectionMomentKernel
    rw [pow_zero, one_mul, reflection_with_density_cons hx ht,
      Fin.cons_self_tail, density_perm_of_nonneg (fun i => (hy i).le)]
    have hp : (∏ j, (Fin.tail (y ∘ Equiv.swap 0 i) j - (y ∘ Equiv.swap 0 i) 0)) =
        ∏ j ∈ Finset.univ.erase i, (y j-y i) := by
      have he0 : (∏ j, (Fin.tail (y ∘ Equiv.swap 0 i) j - (y ∘ Equiv.swap 0 i) 0)) =
          ∏ j ∈ Finset.univ.erase (0 : Fin (n+1)), ((y ∘ Equiv.swap 0 i) j - y i) := by
        have he0 : (Finset.univ.erase (0 : Fin (n+1))) =
            Finset.univ.filter (fun j => j ≠ 0) := by ext; simp
        rw [he0, Finset.prod_filter, Fin.prod_univ_succ]
        simp [Fin.tail_def]
      have hs : ∏ j ∈ Finset.univ.erase (0 : Fin (n+1)), ((y ∘ Equiv.swap 0 i) j - y i) =
          ∏ j ∈ Finset.univ.erase i, (y j-y i) := by
        apply Finset.prod_equiv (Equiv.swap 0 i)
        · intro j
          simp [Equiv.swap_apply_eq_iff]
        · intro j hj
          rfl
      exact he0.trans hs
    rw [hp]
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    rw [one_div, mul_inv]
    ring
  simp_rw [he, ← Finset.mul_sum]
  by_cases hi : Function.Injective y
  · rw [lagrange_reverse_cauchy_sum hi hz]
    ring
  · rw [density_zero_of_not_injective hi, zero_mul, zero_div, mul_zero]


lemma integrable_cauchyDensity (n : ℕ) {z : ℝ} (hz : 1 < z) :
    Integrable (cauchyDensity n z) (unitCubeMeasure n) := by
  have hi : Integrable (fun y : Fin n → ℝ => (∏ i, (z-y i))⁻¹ * density n y)
      (unitCubeMeasure n) := by
    apply integrable_cube_mul_density (by fun_prop) (b := ((z-1)⁻¹)^n)
    intro y hy
    rw [abs_inv, Finset.abs_prod, ← Finset.prod_inv_distrib]
    have hh (i : Fin n) : |z-y i|⁻¹ ≤ (z-1)⁻¹ := by
      rw [abs_of_pos (by linarith [(hy i).2] : 0 < z-y i)]
      exact inv_anti₀ (by linarith) (by linarith [(hy i).2])
    calc
      _ ≤ ∏ _ : Fin n, (z-1)⁻¹ := Finset.prod_le_prod
        (fun i _ => inv_nonneg.mpr (abs_nonneg _)) (fun i _ => hh i)
      _ = _ := by simp
  exact hi.congr (Filter.Eventually.of_forall fun y => by dsimp [cauchyDensity]; ring)

lemma integral_cauchyDensity_pos (n : ℕ) {z : ℝ} (hz : 1 < z) :
    0 < ∫ y, cauchyDensity n z y ∂unitCubeMeasure n := by
  apply integral_pos_on_cube (integrable_cauchyDensity n hz)
  · intro y hy
    exact div_nonneg (density_nonneg_of_nonneg fun i => (hy i).1.le)
      (Finset.prod_nonneg fun i _ => by linarith [(hy i).2])
  · intro y hy
    exact div_pos (density_pos hy) (Finset.prod_pos fun i _ => by linarith [(hy.2 i).2])

lemma integral_reflectionCauchyKernel (n : ℕ) {z : ℝ} (hz : 1 < z) :
    ((n:ℝ)+1) * (∫ y, reflectionCauchyKernel n z y ∂unitCubeMeasure (n+1)) =
      (-1:ℝ)^n * ∫ y, cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1) := by
  have his (i : Fin (n+1)) : Integrable
      (fun y => reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i)) (unitCubeMeasure (n+1)) := by
    simpa only [Function.comp_def, StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
        (Equiv.swap 0 i).symm).integrable_comp_of_integrable (integrable_reflectionCauchyKernel n hz)
  have he (i : Fin (n+1)) :
      (∫ y, reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1)) =
        ∫ y, reflectionCauchyKernel n z y ∂unitCubeMeasure (n+1) := by
    simpa only [StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
        (Equiv.swap 0 i).symm).integral_comp' (reflectionCauchyKernel n z)
  calc
    _ = ∑ i : Fin (n+1), ∫ y, reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1) := by
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ = ∫ y, ∑ i : Fin (n+1), reflectionCauchyKernel n z (y ∘ Equiv.swap 0 i) ∂unitCubeMeasure (n+1) :=
      (integral_finsetSum _ (fun i _ => his i)).symm
    _ = ∫ y, (-1:ℝ)^n * cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1) := by
      apply integral_congr_ae
      filter_upwards [ae_unitCube (n+1)] with y hy
      exact reflectionCauchyKernel_sum_swaps n (fun i => (hy i).1) (fun i => by linarith [(hy i).2])
    _ = _ := integral_const_mul _ _

lemma integral_density_unitCube_positive (n : ℕ) :
    0 < ∫ y, density n y ∂unitCubeMeasure n := by
  rw [integral_density_unitCube]
  exact mul_pos (by exact_mod_cast Nat.factorial_pos n) (normalizer_pos n)

lemma reflection_expectation_cauchy (n : ℕ) {z : ℝ} (hz : 1 < z) :
    realStieltjes 1 (fun x => expectation n (reflectionProduct n x) * omega x) z =
      ((-1:ℝ)^n * ∫ y, cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1)) /
        (((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n) := by
  have hF := integral_reflectionCauchyKernel n hz
  rw [integral_unitCube_cons,
    integral_prod _ (integrable_unitCube_cons (integrable_reflectionCauchyKernel n hz))] at hF
  have he (x : ℝ) : (∫ y, reflectionCauchyKernel n z (Fin.cons x y) ∂unitCubeMeasure n) =
      (omega x / (z-x)) * (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n) := by
    simp only [reflectionCauchyKernel, reflectionMomentKernel, pow_zero, one_mul,
      Fin.cons_zero, Fin.tail_cons]
    simp_rw [show ∀ y : Fin n → ℝ, omega x * reflectionProduct n x y * density n y / (z-x) =
      (omega x/(z-x)) * (reflectionProduct n x y * density n y) from fun y => by ring]
    rw [integral_const_mul]
  simp_rw [he] at hF
  have hh : (∫ x in Ioo (0:ℝ) 1, (omega x / (z-x)) *
      (∫ y, reflectionProduct n x y * density n y ∂unitCubeMeasure n)) =
      (∫ y, density n y ∂unitCubeMeasure n) *
        realStieltjes 1 (fun x => expectation n (reflectionProduct n x) * omega x) z := by
    rw [realStieltjes, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    rw [expectation_reflection_unitCube n hx.1.le, one_mul]
    field_simp [integral_density_unitCube_positive n |>.ne']
  rw [hh] at hF
  exact (eq_div_iff (mul_ne_zero (by positivity) (integral_density_unitCube_positive n).ne')).mpr
    (by nlinarith [hF])


 

 


lemma projection_initial_monic {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = n)
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    (tildePoly n J).eval 0 = ((-8:ℝ)^n)⁻¹ := by
  have ht := (projection_top_coefficients n hn P J E hP hJ hE).1
  rw [← hQ, ← homogeneousQ_natDegree hg hd, (homogeneousQ_monic hg).coeff_natDegree] at ht
  apply (mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-8:ℝ) ≠ 0)))
  rw [mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (-8:ℝ) ≠ 0))]
  exact ht.symm

lemma projectionF_positive_cauchy {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = n)
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) {z : ℝ} (hz : 1 < z) :
    projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z =
      - (∫ y, cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1)) /
        (Real.pi * (8:ℝ)^n * ((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n) := by
  have hD := projectionD_expectation n hn g P J E hP hJ hE hQ
  have hF : Tendsto (fun t : ℝ => projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) (-t))
      atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul, projectionF, fBranch, highBranch] using tilde_F_decay n g P J E hP hJ
      (degree_lt_implies_natDegree_lt (by omega) hE).le hQ 0 (Nat.zero_le n)
  rw [projectionF_cauchy_outside _ _ _ hF z (Or.inr hz)]
  have he : realStieltjes 1 (fun x => projectionD (tildePoly n J) (tildePoly n E) x * omega x) z =
      (tildePoly n J).eval 0 * realStieltjes 1 (fun x => expectation n (reflectionProduct n x) * omega x) z := by
    rw [realStieltjes, realStieltjes, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    rw [hD x hx.1]
    ring
  rw [he, projection_initial_monic hn hg hd hP hJ hE hQ, reflection_expectation_cauchy n hz]
  have hs : (-8:ℝ)^n * (-1:ℝ)^n = (8:ℝ)^n := by rw [← mul_pow]; norm_num
  have hs' : ((-8:ℝ)^n)⁻¹ * (-1:ℝ)^n = ((8:ℝ)^n)⁻¹ := by
    have hp : (-1:ℝ)^n * (-1:ℝ)^n=1 := by rw [←mul_pow]; norm_num
    apply (mul_left_cancel₀ (by positivity : (8:ℝ)^n≠0))
    rw [mul_inv_cancel₀ (by positivity : (8:ℝ)^n≠0),←hs]
    calc
      _ = ((-8:ℝ)^n * ((-8:ℝ)^n)⁻¹) * ((-1:ℝ)^n * (-1:ℝ)^n) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (-8:ℝ)≠0)),hp,one_mul]
  calc
    _ = -(1/Real.pi) * (((-8:ℝ)^n)⁻¹ * (-1:ℝ)^n) *
        (∫ y, cauchyDensity (n+1) z y ∂unitCubeMeasure (n+1)) /
        (((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n) := by ring
    _ = _ := by rw [hs']; simp only [div_eq_mul_inv, mul_inv]; ring

lemma projectionF_neg {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = n)
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) {z : ℝ} (hz : 1 < z) :
    projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z < 0 := by
  rw [projectionF_positive_cauchy hn hg hd hP hJ hE hQ hz]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (integral_cauchyDensity_pos _ hz))
    (by have hp := Real.pi_pos; have hi := integral_density_unitCube_positive n; positivity)


 

 


lemma scaled_cauchyDensity (n : ℕ) {z : ℝ} (hz : z ≠ 0) (y : Fin n → ℝ) :
    z^n * cauchyDensity n z y = (∏ i, (1-y i/z)⁻¹) * density n y := by
  have he (i : Fin n) : (1-y i/z)⁻¹ = z / (z-y i) := by
    rw [show 1-y i/z = (z-y i)/z by field_simp, inv_div]
  simp_rw [he]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,cauchyDensity]
  ring

lemma scaled_cauchyDensity_bound {n : ℕ} {z : ℝ} (hz : 2 ≤ z) {y : Fin n → ℝ}
    (hy : ∀ i, y i ∈ Ioo (0:ℝ) 1) :
    ‖(∏ i, (1-y i/z)⁻¹) * density n y‖ ≤ (2:ℝ)^n * density n y := by
  have hd i : 1/2 ≤ 1-y i/z := by
    have hdiv : y i/z ≤ 1/2 := (div_le_iff₀ (by linarith : 0<z)).mpr (by linarith [(hy i).2])
    linarith
  have hn i : 0 ≤ (1-y i/z)⁻¹ := inv_nonneg.mpr (by linarith [hd i])
  rw [Real.norm_eq_abs,abs_of_nonneg
    (mul_nonneg (Finset.prod_nonneg fun i _ => hn i)
      (density_nonneg_of_nonneg fun i => (hy i).1.le))]
  apply mul_le_mul_of_nonneg_right _ (density_nonneg_of_nonneg fun i => (hy i).1.le)
  calc
    _ ≤ ∏ _ : Fin n, (2:ℝ) := Finset.prod_le_prod (fun i _ => hn i) (fun i _ => by
      have hh := inv_anti₀ (by norm_num : (0:ℝ)<1/2) (hd i)
      norm_num at hh
      exact hh)
    _ = _ := by simp

lemma cauchyDensity_limit (n : ℕ) :
    Tendsto (fun z : ℝ => z^n * ∫ y, cauchyDensity n z y ∂unitCubeMeasure n)
      atTop (𝓝 (∫ y, density n y ∂unitCubeMeasure n)) := by
  have hi : Tendsto (fun z : ℝ => ∫ y, (∏ i, (1-y i/z)⁻¹) * density n y ∂unitCubeMeasure n)
      atTop (𝓝 (∫ y, density n y ∂unitCubeMeasure n)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y => (2:ℝ)^n * density n y)
    · exact Filter.Eventually.of_forall fun z => ((by fun_prop : Measurable
        (fun y : Fin n → ℝ => (∏ i, (1-y i/z)⁻¹))).mul (measurable_density n)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (2:ℝ)] with z hz
      filter_upwards [ae_unitCube n] with y hy
      exact scaled_cauchyDensity_bound hz hy
    · exact (integrable_density_unitCube n).const_mul _
    · exact Filter.Eventually.of_forall fun y => by
        have ht (i : Fin n) : Tendsto (fun z : ℝ => (1-y i/z)⁻¹) atTop (𝓝 1) := by
          have hh : Tendsto (fun z : ℝ => 1-y i/z) atTop (𝓝 1) := by
            simpa only [mul_zero,sub_zero,div_eq_mul_inv] using
              ((tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0)).const_mul (y i)).const_sub 1
          simpa only [inv_one] using hh.inv₀ (by norm_num : (1:ℝ)≠0)
        simpa using (tendsto_finsetProd Finset.univ (fun i _ => ht i)).mul_const (density n y)
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with z hz
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => (scaled_cauchyDensity n hz.ne' y).symm

end
end CriticalStrip

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


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators Classical

lemma projectionF_high_scaled_limit {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    Tendsto (fun z : ℝ => z^(n+1) *
        projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z) atTop
      (𝓝 (((1/8) / ((2*C)*(1-2*C^2)))^(2*n+1) * ((C-c)^n * g.eval C))) := by
  have hz : ∀ᶠ z : ℝ in atTop, z ≠ 0 := eventually_ne_atTop 0
  have hi : Tendsto (fun z : ℝ => 1/z) atTop (𝓝 0) := by simpa only [one_div] using tendsto_inv_atTop_zero
  have hb : Tendsto (fun z : ℝ => highBranch (1/z)) atTop (𝓝 C) := by
    simpa only [highBranch_zero, Function.comp_def] using highBranch_continuous.continuousAt.tendsto.comp hi
  have hscale := ((highBranch_rescaled hz hi).pow (2*n+1)).mul
    (((hb.sub_const c).pow n).mul (g.continuous.continuousAt.tendsto.comp hb))
  apply hscale.congr'
  filter_upwards [hz,hi.eventually (Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1))] with z hz hs
  have he := tilde_projection_eval n P J E hP hJ
    (degree_lt_implies_natDegree_lt (by omega) hE).le hz (branches_harmonic hs).1
  rw [←hQ] at he
  change _ = z^(n+1) * ((tildePoly n P).eval z + highBranch (1/z) * (tildePoly n J).eval z +
    highBranch (1/z)^2 * (tildePoly n E).eval z)
  rw [he]
  simp only [homogeneousQ, eval_mul, eval_pow, eval_sub, eval_C, eval_X, mul_pow, Function.comp_def]
  ring

lemma projectionF_cauchy_scaled_limit {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = n)
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    Tendsto (fun z : ℝ => z^(n+1) *
        projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z) atTop
      (𝓝 (-(∫ y, density (n+1) y ∂unitCubeMeasure (n+1)) /
        (Real.pi * (8:ℝ)^n * ((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n))) := by
  apply ((cauchyDensity_limit (n+1)).neg.div_const _).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with z hz
  rw [projectionF_positive_cauchy hn hg hd hP hJ hE hQ hz]
  ring

 

theorem MonicProblem.eval_C_pos {n : ℕ} (hn : 1 ≤ n) {g : Polynomial ℝ}
    (hg : MonicProblem n g) : 0 < g.eval C := by
  obtain ⟨hgm,hgd,P,J,E,hP,hJ,hE,hQ⟩ := hg
  have he := tendsto_nhds_unique
    (projectionF_high_scaled_limit hn hP hJ hE hQ)
    (projectionF_cauchy_scaled_limit hn hgm hgd hP hJ hE hQ)
  have hpos : 0 < Real.pi * (8:ℝ)^n * ((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n := by
    have hi := integral_density_unitCube_positive n
    have hp := Real.pi_pos
    positivity
  have hneg := div_neg_of_neg_of_pos
    (neg_neg_of_pos (integral_density_unitCube_positive (n+1))) hpos
  rw [←he] at hneg
  have hC := C_c_facts
  have hCp : 0<C := hC.1.trans hC.2.1
  have hk : (1/8:ℝ)/((2*C)*(1-2*C^2))<0 :=
    div_neg_of_pos_of_neg (by norm_num) (mul_neg_of_pos_of_neg (by linarith) (by
      nlinarith [sq_nonneg (C-c)]))
  have hp : ((1/8:ℝ)/((2*C)*(1-2*C^2)))^(2*n+1)<0 := (odd_two_mul_add_one n).pow_neg hk
  have hd : 0<(C-c)^n := pow_pos (sub_pos.mpr hC.2.1) n
  have hm : 0 < (C-c)^n * g.eval C := ((mul_neg_iff.mp hneg).resolve_left (by rintro ⟨hn,_⟩; linarith)).2
  exact (mul_pos_iff.mp hm).resolve_right (by rintro ⟨hf,_⟩; linarith) |>.2

end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open Filter Polynomial
open scoped Topology BigOperators Classical



theorem scalarValue_homogeneous_positive (n : ℕ) :
    ∃ x : ℝ, 0<x ∧ scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))=(x:ℂ) := by
  induction n with
  | zero => exact ⟨1,by norm_num,by simp only [scalarValue_zero,Complex.ofReal_one]⟩
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      exact ⟨1,by norm_num,by simp only [scalarValue_one,Complex.ofReal_one]⟩
    obtain ⟨x,hx,he⟩:=ih
    have hp : scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0 := by
      rw [he]; exact_mod_cast hx.ne'
    obtain ⟨g,hg,hnext⟩:=nextScalar_homogeneous_of_ne (by omega) hp
    refine ⟨x*g.eval C,mul_pos hx (hg.eval_C_pos (by omega)),?_⟩
    have hh:=congrArg (Polynomial.eval (C:ℂ)) hnext
    rw [nextScalar_eval,Polynomial.eval_mul,Polynomial.eval_C,he] at hh
    have hs : (Fin.snoc (fun _ : Fin n => (C:ℂ)) (C:ℂ) : Fin (n+1) → ℂ)=(fun _ => (C:ℂ)) := by
      funext i
      induction i using Fin.lastCases <;> simp
    have hm : Polynomial.eval₂ Complex.ofRealHom (C:ℂ) g=(↑(g.eval (CriticalStrip.C:ℝ)):ℂ) :=
      Polynomial.eval₂_at_apply Complex.ofRealHom C
    rw [hs,Polynomial.eval_map,hm] at hh
    exact hh.trans (Complex.ofReal_mul _ _).symm

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators Classical

lemma projectionD_nonneg_right {n : ℕ} (hn : 1≤n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree=n)
    (hP : P.natDegree≤n) (hJ : J.natDegree≤n) (hE : E.degree<(n:WithBot ℕ))
    (hQ : homogeneousQ n g=P.comp harmonicCoordinate+X*J.comp harmonicCoordinate+
      X^2*E.comp harmonicCoordinate) {z : ℝ} (hz : 1≤z) :
    0≤projectionD (tildePoly n J) (tildePoly n E) z := by
  rw [projectionD_expectation n hn g P J E hP hJ hE hQ z (by linarith),
    projection_initial_monic hn hg hd hP hJ hE hQ,←expectation_const_mul]
  apply expectation_nonneg
  intro y hy
  have he : ((-8:ℝ)^n)⁻¹*reflectionProduct n z y=
      ∏ i,((-8:ℝ)⁻¹*((y i-z)/(y i+z))) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,inv_pow,reflectionProduct]
  rw [he]
  apply Finset.prod_nonneg
  intro i _
  apply mul_nonneg_of_nonpos_of_nonpos (by norm_num)
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [(hy.2 i).2]) (by linarith [(hy.2 i).1])

lemma integral_cauchyDensity_lower (n : ℕ) {z : ℝ} (hz : 1<z) (hz₂ : z≤2) :
    (∫ y, density n y ∂unitCubeMeasure n)/(2:ℝ)^n ≤
      ∫ y, cauchyDensity n z y ∂unitCubeMeasure n := by
  rw [←integral_div]
  apply integral_mono_ae ((integrable_density_unitCube n).div_const _) (integrable_cauchyDensity n hz)
  filter_upwards [ae_unitCube n] with y hy
  apply div_le_div₀ (density_nonneg_of_nonneg fun i => (hy i).1.le) le_rfl
    (Finset.prod_pos fun i _ => by linarith [(hy i).2])
  calc
    (∏ i, (z-y i)) ≤ ∏ _ : Fin n, (2:ℝ) := Finset.prod_le_prod
      (fun i _ => by linarith [(hy i).2]) (fun i _ => by linarith [(hy i).1])
    _ = _ := by simp

lemma projectionF_continuousAt (P J E : Polynomial ℝ) {z : ℝ} (hz : z≠0) :
    ContinuousAt (projectionF P J E) z := by
  change ContinuousAt (fun z : ℝ => P.eval z + Real.sqrt ((1+Real.sqrt ((1-1/z)/2))/2)*J.eval z +
    Real.sqrt ((1+Real.sqrt ((1-1/z)/2))/2)^2*E.eval z) z
  fun_prop (disch := assumption)

 
lemma projectionF_one_neg {n : ℕ} (hn : 1≤n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree=n)
    (hP : P.natDegree≤n) (hJ : J.natDegree≤n) (hE : E.degree<(n:WithBot ℕ))
    (hQ : homogeneousQ n g=P.comp harmonicCoordinate+X*J.comp harmonicCoordinate+
      X^2*E.comp harmonicCoordinate) :
    projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) 1<0 := by
  let b : ℝ := (∫ y, density (n+1) y ∂unitCubeMeasure (n+1)) /
    ((2:ℝ)^(n+1)*(Real.pi*8^n*((n:ℝ)+1)*∫ y, density n y ∂unitCubeMeasure n))
  have hb : 0<b := by
    dsimp [b]
    exact div_pos (integral_density_unitCube_positive (n+1)) (by
      have hp:=Real.pi_pos; have hi:=integral_density_unitCube_positive n; positivity)
  have hden : 0<Real.pi*(8:ℝ)^n*((n:ℝ)+1)*∫ y, density n y ∂unitCubeMeasure n := by
    have hp:=Real.pi_pos; have hi:=integral_density_unitCube_positive n; positivity
  have ht := (projectionF_continuousAt (tildePoly n P) (tildePoly n J) (tildePoly n E)
    (by norm_num : (1:ℝ)≠0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (1:ℝ)))
  have hbnd : ∀ᶠ z in 𝓝[>] (1:ℝ),
      projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z≤ -b := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1:ℝ)<2))] with z hz hz₂
    rw [projectionF_positive_cauchy hn hg hd hP hJ hE hQ hz]
    have hi:=div_le_div_of_nonneg_right (integral_cauchyDensity_lower (n+1) hz hz₂.le) hden.le
    dsimp [b]
    calc
      _ ≤ -( (∫ y, density (n+1) y ∂unitCubeMeasure (n+1))/(2:ℝ)^(n+1) /
        (Real.pi*8^n*((n:ℝ)+1)*∫ y, density n y ∂unitCubeMeasure n)) := by simpa only [neg_div] using neg_le_neg hi
      _ = _ := by rw [div_div]
  exact (le_of_tendsto ht hbnd).trans_lt (neg_neg_of_pos hb)

lemma branches_inverse {x : ℝ} (hx : x∈Ioo c C) :
    let u:=8*x^2*(1-x^2)-1
    0<u ∧ u≤1 ∧ (x=highBranch u ∨ x=lowBranch u) := by
  dsimp only
  have hp : 0<x := C_c_facts.1.trans hx.1
  have hCp : 0<C := C_c_facts.1.trans C_c_facts.2.1
  have hcq : c^2<x^2 := by nlinarith [mul_pos (sub_pos.mpr hx.1) (add_pos hp C_c_facts.1)]
  have hCq : x^2<C^2 := by nlinarith [mul_pos (sub_pos.mpr hx.2) (add_pos hCp hp)]
  have hsum := C_c_facts.2.2.1
  have hprod : C^2*c^2=1/8 := by nlinarith [C_c_facts.2.2.2.1]
  have hfact : 8*x^2*(1-x^2)-1=8*(x^2-c^2)*(C^2-x^2) := by
    nlinarith [hsum,hprod]
  refine ⟨by rw [hfact]; positivity, by nlinarith [sq_nonneg (2*x^2-1)],?_⟩
  have hs : Real.sqrt ((1-(8*x^2*(1-x^2)-1))/2)=|2*x^2-1| := by
    rw [show (1-(8*x^2*(1-x^2)-1))/2=(2*x^2-1)^2 by ring,Real.sqrt_sq_eq_abs]
  by_cases hm : 0≤2*x^2-1
  · left
    rw [highBranch,hs,abs_of_nonneg hm,
      show (1+(2*x^2-1))/2=x^2 by ring,Real.sqrt_sq hp.le]
  · right
    rw [lowBranch,hs,abs_of_neg (lt_of_not_ge hm),
      show (1- -(2*x^2-1))/2=x^2 by ring,Real.sqrt_sq hp.le]

lemma branches_order (u : ℝ) : lowBranch u≤highBranch u := by
  apply Real.sqrt_le_sqrt
  linarith [Real.sqrt_nonneg ((1-u)/2)]

lemma projection_low_difference {n : ℕ} {P J E : Polynomial ℝ}
    (hP : P.natDegree≤n) (hJ : J.natDegree≤n) (hE : E.natDegree≤n)
    {z : ℝ} (hz : 1<z) :
    z^n*(P.comp harmonicCoordinate+X*J.comp harmonicCoordinate+X^2*E.comp harmonicCoordinate).eval (lowBranch (1/z))=
      projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z -
      (highBranch (1/z)-lowBranch (1/z))*projectionD (tildePoly n J) (tildePoly n E) z := by
  have hs : 1/z∈Ioo (-1:ℝ) 1 := ⟨lt_trans (by norm_num) (one_div_pos.mpr (by linarith)), (div_lt_one (by linarith)).mpr hz⟩
  rw [←tilde_projection_eval n P J E hP hJ hE (by linarith : z≠0) (branches_harmonic hs).2]
  have hsum := branches_sum hs
  change highBranch (1/z)+lowBranch (1/z)=lBranch z at hsum
  dsimp only [projectionF,projectionD]
  change _ = (tildePoly n P).eval z+highBranch (1/z)*(tildePoly n J).eval z+
    highBranch (1/z)^2*(tildePoly n E).eval z -
    (highBranch (1/z)-lowBranch (1/z))*((tildePoly n J).eval z+lBranch z*(tildePoly n E).eval z)
  rw [←hsum]
  ring

 

theorem MonicProblem.eval_pos_between {n : ℕ} (hn : 1≤n) {g : Polynomial ℝ}
    (hg : MonicProblem n g) {x : ℝ} (hx : x∈Ioo c C) : 0<g.eval x := by
  obtain ⟨hgm,hgd,P,J,E,hP,hJ,hE,hQ⟩:=hg
  obtain ⟨hu,hu₁,he⟩:=branches_inverse hx
  let u:=8*x^2*(1-x^2)-1
  have hEn : E.natDegree≤n := (degree_lt_implies_natDegree_lt (by omega) hE).le
  have hQneg : (homogeneousQ n g).eval x<0 := by
    by_cases huc : u=1
    · have heh : highBranch 1=lowBranch 1 := by norm_num [highBranch,lowBranch]
      have hex : x=highBranch 1 := by
        rcases he with he | he
        · simpa only [show 8*x^2*(1-x^2)-1=1 from huc] using he
        · simpa only [show 8*x^2*(1-x^2)-1=1 from huc,←heh] using he
      have hh:=tilde_projection_eval n P J E hP hJ hEn (by norm_num : (1:ℝ)≠0)
        (b:=highBranch 1) (by
          norm_num [harmonicCoordinate,highBranch])
      rw [←hQ,one_pow,one_mul] at hh
      rw [hex]
      have hh' : projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) 1=
          (homogeneousQ n g).eval (highBranch 1) := by simpa only [projectionF,fBranch,highBranch,div_one] using hh
      rw [←hh']
      exact projectionF_one_neg hn hgm hgd hP hJ hE hQ
    · have hu' : u<1 := lt_of_le_of_ne hu₁ huc
      have hz : 1<1/u := (lt_div_iff₀ hu).mpr (by linarith)
      have hs : u∈Ioo (-1:ℝ) 1 := ⟨by linarith,hu'⟩
      have hzn : 0<(1/u)^n := pow_pos (by positivity) n
      rcases he with he | he
      · have hh:=tilde_projection_eval n P J E hP hJ hEn (by positivity : 1/u≠0)
          (b:=highBranch u) (by simpa only [one_div_one_div] using (branches_harmonic hs).1)
        rw [←hQ] at hh
        have hh' : projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) (1/u)=
            (1/u)^n*(homogeneousQ n g).eval (highBranch u) := by
          simpa only [projectionF,fBranch,highBranch,one_div_one_div] using hh
        have ht:=projectionF_neg hn hgm hgd hP hJ hE hQ hz
        rw [hh',←he] at ht
        exact ((mul_neg_iff.mp ht).resolve_right (by rintro ⟨h,_⟩; linarith)).2
      · have hh:=projection_low_difference hP hJ hEn hz
        rw [←hQ,one_div_one_div,←he] at hh
        have hfn:=projectionF_neg hn hgm hgd hP hJ hE hQ hz
        have hdpos:=mul_nonneg (sub_nonneg.mpr (branches_order u))
          (projectionD_nonneg_right hn hgm hgd hP hJ hE hQ hz.le)
        have hhneg : projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) (1/u) -
            (highBranch u-lowBranch u)*projectionD (tildePoly n J) (tildePoly n E) (1/u)<0 := by
          linarith
        rw [←he] at hhneg
        rw [←hh] at hhneg
        exact ((mul_neg_iff.mp hhneg).resolve_right (by rintro ⟨h,_⟩; linarith)).2
  simp only [homogeneousQ,eval_mul,eval_pow,eval_sub,eval_X,eval_C] at hQneg
  have hp : (x-C)^(2*n+1)*(x-c)^n<0 := mul_neg_of_neg_of_pos
    ((odd_two_mul_add_one n).pow_neg (sub_neg.mpr hx.2)) (pow_pos (sub_pos.mpr hx.1) n)
  exact ((mul_neg_iff.mp hQneg).resolve_left (by rintro ⟨h,_⟩; linarith)).2

end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open Set Polynomial
open scoped BigOperators Classical

lemma c_eq_critical : c=CriticalStrip.c := by
  unfold c lambda CriticalStrip.c
  congr 1
  ring

lemma nextScalar_homogeneous {n : ℕ} (hn : 1≤n) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      nextScalar (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))=
        Polynomial.C (scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))) * g.map Complex.ofRealHom :=
  nextScalar_homogeneous_of_ne hn (scalarValue_homogeneous_ne_zero n)

end
end CriticalStrip.Diagram

namespace CriticalStrip
noncomputable section
open Set Polynomial
open scoped BigOperators Classical

lemma MonicProblem.eval_c {n : ℕ} (hn : 1≤n) {g : Polynomial ℝ}
    (hg : MonicProblem n g) : g.eval c=(2*C)^n := by
  obtain ⟨g₀,hg₀,hnext⟩:=Diagram.nextScalar_homogeneous hn
  have heq : g=g₀ := (homogeneous_monic_unique n hn).unique hg hg₀
  subst g₀
  apply Complex.ofReal_injective
  have hh:=congrArg (Polynomial.eval (c:ℂ)) hnext
  rw [Diagram.nextScalar_eval,Diagram.scalarValue_snoc,←Diagram.c_eq_critical] at hh
  have hflat:=Diagram.scalarValue_flat (RingHom.id ℂ) (fun _ : Fin n => (Diagram.C:ℂ))
  simp only [RingHom.id_apply] at hflat
  rw [hflat] at hh
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map] at hh
  have hm : Polynomial.eval₂ Complex.ofRealHom (Diagram.c:ℂ) g = (↑(g.eval (c:ℝ)):ℂ) := by
    rw [Diagram.c_eq_critical]
    exact Polynomial.eval₂_at_apply Complex.ofRealHom c
  rw [hm] at hh
  have hv := mul_left_cancel₀ (Diagram.scalarValue_homogeneous_ne_zero n)
    (hh.symm.trans (mul_comm _ _))
  simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,two_mul,Diagram.C,Diagram.lambda,C,lambda,Complex.ofReal_add] using hv

 
theorem MonicProblem.eval_pos_Icc {n : ℕ} (hn : 1≤n) {g : Polynomial ℝ}
    (hg : MonicProblem n g) {x : ℝ} (hx : x∈Icc c C) : 0<g.eval x := by
  rcases hx with ⟨hcx,hxC⟩
  rcases eq_or_lt_of_le hcx with rfl | hc
  · rw [hg.eval_c hn]
    exact pow_pos (mul_pos (by norm_num) (C_c_facts.1.trans C_c_facts.2.1)) n
  rcases eq_or_lt_of_le hxC with rfl | hC
  · exact hg.eval_C_pos hn
  · exact hg.eval_pos_between hn ⟨hc,hC⟩

end
end CriticalStrip

namespace CriticalStrip.Diagram
noncomputable section
open Set Polynomial
open scoped BigOperators Classical

 

theorem scalarValue_deformation_positive (n : ℕ) {x : ℝ}
    (hx : x∈Icc c C) :
    ∃ y : ℝ, 0<y ∧
      scalarValue (RingHom.id ℂ) (Fin.snoc (fun _ : Fin n => (C:ℂ)) (x:ℂ))=(y:ℂ) := by
  by_cases hn : n=0
  · subst n
    refine ⟨1,by norm_num,?_⟩
    have he : (Fin.snoc (fun _ : Fin 0 => (C:ℂ)) (x:ℂ) : Fin 1 → ℂ)=fun _ => (x:ℂ) := by
      funext i; fin_cases i; rfl
    rw [he,scalarValue_one,Complex.ofReal_one]
  obtain ⟨p,hp,he⟩:=scalarValue_homogeneous_positive n
  obtain ⟨g,hg,hnext⟩:=nextScalar_homogeneous (by omega : 1≤n)
  refine ⟨p*g.eval x,mul_pos hp (hg.eval_pos_Icc (by omega) (by simpa only [c_eq_critical,C,lambda,CriticalStrip.C,CriticalStrip.lambda] using hx)),?_⟩
  have hh:=congrArg (Polynomial.eval (x:ℂ)) hnext
  have hm : Polynomial.eval₂ Complex.ofRealHom (x:ℂ) g = (↑(g.eval x):ℂ) :=
    Polynomial.eval₂_at_apply Complex.ofRealHom x
  rw [nextScalar_eval,Polynomial.eval_mul,Polynomial.eval_C,he,Polynomial.eval_map,hm] at hh
  exact hh.trans (Complex.ofReal_mul _ _).symm

lemma scalarValue_deformation_ne_zero (n : ℕ) {x : ℝ} (hx : x∈Icc c C) :
    scalarValue (RingHom.id ℂ) (Fin.snoc (fun _ : Fin n => (C:ℂ)) (x:ℂ))≠0 := by
  obtain ⟨y,hy,he⟩:=scalarValue_deformation_positive n hx
  rw [he]
  exact_mod_cast hy.ne'

lemma cosine_deformation {u : ℝ} (hu : u∈Icc 0 lambda) :
    Real.cos (2*u-3*lambda)∈Icc c C := by
  have hl : 0<lambda := by unfold lambda; positivity
  have hπ : 3*lambda<Real.pi := by unfold lambda; linarith [Real.pi_pos]
  have harg : lambda≤3*lambda-2*u ∧ 3*lambda-2*u≤3*lambda := by constructor <;> linarith [hu.1,hu.2]
  rw [show 2*u-3*lambda= -(3*lambda-2*u) by ring,Real.cos_neg]
  exact ⟨Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hπ.le harg.2,
    Real.cos_le_cos_of_nonneg_of_le_pi hl.le (harg.2.trans hπ.le) harg.1⟩

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeformationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix Set
open scoped BigOperators Classical

lemma deformationAngles_scalar_ne_zero_oai (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    angleScalar (deformationAngles n t)≠0 := by
  rw [angleScalar,angleEvaluation_scalar]
  have he : (fun i=>(Real.cos (2*deformationAngles n t i-3*lambda):ℂ))=
      Fin.cons (Real.cos (2*t-3*lambda):ℂ) (fun _ : Fin n=>(C:ℂ)) := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · simp only [deformationAngles,Fin.cons_succ,show 2*lambda-3*lambda= -lambda by ring,Real.cos_neg,C]
  rw [he]
  have hg:=scalarValue_extract (RingHom.id ℂ)
    (Fin.snoc (fun _ : Fin n=>(C:ℂ)) (Real.cos (2*t-3*lambda):ℂ)) (Fin.last n)
  simp only [Fin.snoc_last,Fin.succAbove_last,Fin.snoc_castSucc] at hg
  rw [←hg]
  exact scalarValue_deformation_ne_zero n (cosine_deformation ht)

end
end CriticalStrip.Diagram





end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.Diagram.deformationAngles_scalar_ne_zero_oai := @OAI.CriticalStrip.Diagram.deformationAngles_scalar_ne_zero_oai
