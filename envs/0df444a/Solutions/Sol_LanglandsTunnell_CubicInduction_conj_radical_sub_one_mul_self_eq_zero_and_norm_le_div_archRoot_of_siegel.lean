-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bc21ebab-bb00-5d6f-826d-1686ef458e26

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_NumberField_AdelicVolume
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {A : Type*} [CommRing A]

private theorem radicalP21_mul_upperUnipotent3 (v : Fin 2 → A) (x y z : A) :
    radicalP21 v * upperUnipotent3 x y z = upperUnipotent3 x y z * radicalP21 ![v 0 - x * v 1, v 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP21, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem radicalP12_mul_upperUnipotent3 (v : Fin 2 → A) (x y z : A) :
    radicalP12 v * upperUnipotent3 x y z = upperUnipotent3 x y z * radicalP12 ![v 0, v 1 + y * v 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalP12, upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem inv_mul_radicalP21_mul_upperUnipotent3 (v : Fin 2 → A) (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ * radicalP21 v * upperUnipotent3 x y z = radicalP21 ![v 0 - x * v 1, v 1] := by
  rw [mul_assoc, radicalP21_mul_upperUnipotent3, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem inv_mul_radicalP12_mul_upperUnipotent3 (v : Fin 2 → A) (x y z : A) :
    (upperUnipotent3 x y z)⁻¹ * radicalP12 v * upperUnipotent3 x y z = radicalP12 ![v 0, v 1 + y * v 0] := by
  rw [mul_assoc, radicalP12_mul_upperUnipotent3, ← mul_assoc, inv_mul_cancel, one_mul]

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {A : Type*} [CommRing A]

private theorem radicalP21_mul_of_coe_eq_diagonal (v : Fin 2 → A) (t : GL (Fin 3) A) (d : Fin 3 → Aˣ)
    (hdiag : (t : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun i => (d i : A)) :
    radicalP21 v * t =
      t * radicalP21 ![((d 0)⁻¹ : Aˣ) * (v 0 * (d 2 : A)), ((d 1)⁻¹ : Aˣ) * (v 1 * (d 2 : A))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem radicalP12_mul_of_coe_eq_diagonal (v : Fin 2 → A) (t : GL (Fin 3) A) (d : Fin 3 → Aˣ)
    (hdiag : (t : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun i => (d i : A)) :
    radicalP12 v * t =
      t * radicalP12 ![((d 0)⁻¹ : Aˣ) * (v 0 * (d 1 : A)), ((d 0)⁻¹ : Aˣ) * (v 1 * (d 2 : A))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem inv_mul_radicalP21_mul_of_coe_eq_diagonal (v : Fin 2 → A) (t : GL (Fin 3) A) (d : Fin 3 → Aˣ)
    (hdiag : (t : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun i => (d i : A)) :
    t⁻¹ * radicalP21 v * t =
      radicalP21 ![((d 0)⁻¹ : Aˣ) * (v 0 * (d 2 : A)), ((d 1)⁻¹ : Aˣ) * (v 1 * (d 2 : A))] := by
  rw [mul_assoc, radicalP21_mul_of_coe_eq_diagonal v t d hdiag, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem inv_mul_radicalP12_mul_of_coe_eq_diagonal (v : Fin 2 → A) (t : GL (Fin 3) A) (d : Fin 3 → Aˣ)
    (hdiag : (t : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun i => (d i : A)) :
    t⁻¹ * radicalP12 v * t =
      radicalP12 ![((d 0)⁻¹ : Aˣ) * (v 0 * (d 1 : A)), ((d 0)⁻¹ : Aˣ) * (v 1 * (d 2 : A))] := by
  rw [mul_assoc, radicalP12_mul_of_coe_eq_diagonal v t d hdiag, ← mul_assoc, inv_mul_cancel, one_mul]

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Generic

variable {L : Type*} [NormedField L]

private def conjDisplacement (s u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L :=
  ((s⁻¹ * u * s : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) - 1

private theorem radicalP21_sub_one_mul_self (w : Fin 2 → L) :
    ((radicalP21 w : Matrix (Fin 3) (Fin 3) L) - 1) * ((radicalP21 w : Matrix (Fin 3) (Fin 3) L) - 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

private theorem sum_norm_radicalP21_sub_one_apply (w : Fin 2 → L) :
    (∑ m : Fin 3, ∑ l : Fin 3, ‖((radicalP21 w : Matrix (Fin 3) (Fin 3) L) - 1) l m‖) = ‖w 0‖ + ‖w 1‖ := by
  simp [Fin.sum_univ_three, Matrix.one_apply]

private theorem norm_mul_mul_apply_le (A X B : Matrix (Fin 3) (Fin 3) L) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (i j : Fin 3) : ‖(A * X * B) i j‖ ≤ ∑ m : Fin 3, ∑ l : Fin 3, ‖X l m‖ := by
  calc ‖(A * X * B) i j‖ = ‖∑ m : Fin 3, (∑ l : Fin 3, A i l * X l m) * B m j‖ := by
        simp only [Matrix.mul_apply]
    _ ≤ ∑ m : Fin 3, ‖(∑ l : Fin 3, A i l * X l m) * B m j‖ := norm_sum_le _ _
    _ ≤ ∑ m : Fin 3, ∑ l : Fin 3, ‖X l m‖ := by
        refine Finset.sum_le_sum fun m _ => ?_
        calc ‖(∑ l : Fin 3, A i l * X l m) * B m j‖ = ‖∑ l : Fin 3, A i l * X l m‖ * ‖B m j‖ := norm_mul _ _
          _ ≤ (∑ l : Fin 3, ‖A i l * X l m‖) * 1 :=
              mul_le_mul (norm_sum_le _ _) (hB m j) (norm_nonneg _)
                (Finset.sum_nonneg fun _ _ => norm_nonneg _)
          _ = ∑ l : Fin 3, ‖A i l‖ * ‖X l m‖ := by
              rw [mul_one]
              simp only [norm_mul]
          _ ≤ ∑ l : Fin 3, 1 * ‖X l m‖ :=
              Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hA i l) (norm_nonneg _)
          _ = ∑ l : Fin 3, ‖X l m‖ := by simp only [one_mul]

private theorem conj_mul_self_eq_zero (k : GL (Fin 3) L) (X : Matrix (Fin 3) (Fin 3) L) (hX : X * X = 0) :
    ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * X * (k : Matrix (Fin 3) (Fin 3) L) *
        (((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * X * (k : Matrix (Fin 3) (Fin 3) L)) = 0 := by
  calc ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * X * (k : Matrix (Fin 3) (Fin 3) L) *
          (((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * X * (k : Matrix (Fin 3) (Fin 3) L)) =
        ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * X *
          ((k : Matrix (Fin 3) (Fin 3) L) * ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) * X *
            (k : Matrix (Fin 3) (Fin 3) L) := by
        simp only [Matrix.mul_assoc]
    _ = ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * (X * X) * (k : Matrix (Fin 3) (Fin 3) L) := by
        rw [Units.mul_inv, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hX, Matrix.mul_zero, Matrix.zero_mul]

private theorem exists_conjDisplacement_eq (x y z : L) {C : ℝ} (hx : ‖x‖ ≤ C) (t : GL (Fin 3) L) (d : Fin 3 → Lˣ)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) (k : GL (Fin 3) L)
    (v : Fin 2 → L) {M' : ℝ} (hv0 : ‖v 0‖ ≤ M') (hv1 : ‖v 1‖ ≤ M') :
    ∃ w : Fin 2 → L, ‖w 0‖ ≤ (1 + C) * M' * (‖(d 2 : L)‖ / ‖(d 0 : L)‖) ∧
      ‖w 1‖ ≤ M' * (‖(d 2 : L)‖ / ‖(d 1 : L)‖) ∧
      conjDisplacement (upperUnipotent3 x y z * t * k) (radicalP21 v) =
        ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((radicalP21 w : Matrix (Fin 3) (Fin 3) L) - 1) *
          (k : Matrix (Fin 3) (Fin 3) L) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hx

  set v' : Fin 2 → L := ![v 0 - x * v 1, v 1] with hv'
  have hv'0 : ‖v' 0‖ ≤ (1 + C) * M' := by
    have h : ‖v 0 - x * v 1‖ ≤ M' + C * M' :=
      (norm_sub_le _ _).trans (add_le_add hv0 (by rw [norm_mul]; exact mul_le_mul hx hv1 (norm_nonneg _) hC))
    simpa [hv', add_mul, one_mul] using h
  have hv'1 : ‖v' 1‖ ≤ M' := by simpa [hv'] using hv1

  refine ⟨![((d 0)⁻¹ : Lˣ) * (v' 0 * (d 2 : L)), ((d 1)⁻¹ : Lˣ) * (v' 1 * (d 2 : L))], ?_, ?_, ?_⟩
  · have h : ‖(((d 0)⁻¹ : Lˣ) : L) * (v' 0 * (d 2 : L))‖ = ‖(d 0 : L)‖⁻¹ * (‖v' 0‖ * ‖(d 2 : L)‖) := by
      rw [Units.val_inv_eq_inv_val, norm_mul, norm_inv, norm_mul]
    simp only [Matrix.cons_val_zero]
    rw [h, div_eq_inv_mul]
    calc ‖(d 0 : L)‖⁻¹ * (‖v' 0‖ * ‖(d 2 : L)‖) ≤ ‖(d 0 : L)‖⁻¹ * ((1 + C) * M' * ‖(d 2 : L)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv'0 (norm_nonneg _)) (inv_nonneg.2 (norm_nonneg _))
      _ = (1 + C) * M' * (‖(d 0 : L)‖⁻¹ * ‖(d 2 : L)‖) := by ring
  · have h : ‖(((d 1)⁻¹ : Lˣ) : L) * (v' 1 * (d 2 : L))‖ = ‖(d 1 : L)‖⁻¹ * (‖v' 1‖ * ‖(d 2 : L)‖) := by
      rw [Units.val_inv_eq_inv_val, norm_mul, norm_inv, norm_mul]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h, div_eq_inv_mul]
    calc ‖(d 1 : L)‖⁻¹ * (‖v' 1‖ * ‖(d 2 : L)‖) ≤ ‖(d 1 : L)‖⁻¹ * (M' * ‖(d 2 : L)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv'1 (norm_nonneg _)) (inv_nonneg.2 (norm_nonneg _))
      _ = M' * (‖(d 1 : L)‖⁻¹ * ‖(d 2 : L)‖) := by ring
  ·
    have hgroup : (upperUnipotent3 x y z * t * k)⁻¹ * radicalP21 v * (upperUnipotent3 x y z * t * k) =
        k⁻¹ * (t⁻¹ * ((upperUnipotent3 x y z)⁻¹ * radicalP21 v * upperUnipotent3 x y z) * t) * k := by
      simp only [_root_.mul_inv_rev, mul_assoc]
    have h1 := inv_mul_radicalP21_mul_upperUnipotent3 v x y z
    rw [← hv'] at h1
    have h2 := inv_mul_radicalP21_mul_of_coe_eq_diagonal v' t d ht
    unfold conjDisplacement
    rw [hgroup, h1, h2, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Units.inv_mul]

private theorem conjDisplacement_radicalP21_bound (x y z : L) {C : ℝ} (hx : ‖x‖ ≤ C) (t : GL (Fin 3) L)
    (d : Fin 3 → Lˣ) (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) (k : GL (Fin 3) L)
    (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) (v : Fin 2 → L) {M' : ℝ}
    (hv0 : ‖v 0‖ ≤ M') (hv1 : ‖v 1‖ ≤ M') :
    conjDisplacement (upperUnipotent3 x y z * t * k) (radicalP21 v) *
        conjDisplacement (upperUnipotent3 x y z * t * k) (radicalP21 v) = 0 ∧
      ∀ i j, ‖conjDisplacement (upperUnipotent3 x y z * t * k) (radicalP21 v) i j‖ ≤
        (1 + C) * M' * (‖(d 2 : L)‖ / ‖(d 0 : L)‖) + M' * (‖(d 2 : L)‖ / ‖(d 1 : L)‖) := by
  obtain ⟨w, hw0, hw1, hY⟩ := exists_conjDisplacement_eq x y z hx t d ht k v hv0 hv1
  rw [hY]
  refine ⟨conj_mul_self_eq_zero k _ (radicalP21_sub_one_mul_self w), fun i j => ?_⟩
  calc ‖(((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((radicalP21 w : Matrix (Fin 3) (Fin 3) L) - 1) *
          (k : Matrix (Fin 3) (Fin 3) L)) i j‖
        ≤ ∑ m : Fin 3, ∑ l : Fin 3, ‖((radicalP21 w : Matrix (Fin 3) (Fin 3) L) - 1) l m‖ :=
        norm_mul_mul_apply_le _ _ _ hk' hk i j
    _ = ‖w 0‖ + ‖w 1‖ := sum_norm_radicalP21_sub_one_apply w
    _ ≤ (1 + C) * M' * (‖(d 2 : L)‖ / ‖(d 0 : L)‖) + M' * (‖(d 2 : L)‖ / ‖(d 1 : L)‖) := add_le_add hw0 hw1

end Generic

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Generic

variable {L : Type*} [NormedField L]

private theorem radicalP12_sub_one_mul_self (w : Fin 2 → L) :
    ((radicalP12 w : Matrix (Fin 3) (Fin 3) L) - 1) * ((radicalP12 w : Matrix (Fin 3) (Fin 3) L) - 1) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

private theorem sum_norm_radicalP12_sub_one_apply (w : Fin 2 → L) :
    (∑ m : Fin 3, ∑ l : Fin 3, ‖((radicalP12 w : Matrix (Fin 3) (Fin 3) L) - 1) l m‖) = ‖w 0‖ + ‖w 1‖ := by
  simp [Fin.sum_univ_three, Matrix.one_apply]

private theorem exists_conjDisplacement_radicalP12_eq (x y z : L) {C : ℝ} (hy : ‖y‖ ≤ C) (t : GL (Fin 3) L)
    (d : Fin 3 → Lˣ) (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) (k : GL (Fin 3) L)
    (v : Fin 2 → L) {M' : ℝ} (hv0 : ‖v 0‖ ≤ M') (hv1 : ‖v 1‖ ≤ M') :
    ∃ w : Fin 2 → L, ‖w 0‖ ≤ M' * (‖(d 1 : L)‖ / ‖(d 0 : L)‖) ∧
      ‖w 1‖ ≤ (1 + C) * M' * (‖(d 2 : L)‖ / ‖(d 0 : L)‖) ∧
      conjDisplacement (upperUnipotent3 x y z * t * k) (radicalP12 v) =
        ((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((radicalP12 w : Matrix (Fin 3) (Fin 3) L) - 1) *
          (k : Matrix (Fin 3) (Fin 3) L) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hy

  set v' : Fin 2 → L := ![v 0, v 1 + y * v 0] with hv'
  have hv'0 : ‖v' 0‖ ≤ M' := by simpa [hv'] using hv0
  have hv'1 : ‖v' 1‖ ≤ (1 + C) * M' := by
    have h : ‖v 1 + y * v 0‖ ≤ M' + C * M' :=
      (norm_add_le _ _).trans (add_le_add hv1 (by rw [norm_mul]; exact mul_le_mul hy hv0 (norm_nonneg _) hC))
    simpa [hv', add_mul, one_mul] using h

  refine ⟨![((d 0)⁻¹ : Lˣ) * (v' 0 * (d 1 : L)), ((d 0)⁻¹ : Lˣ) * (v' 1 * (d 2 : L))], ?_, ?_, ?_⟩
  · have h : ‖(((d 0)⁻¹ : Lˣ) : L) * (v' 0 * (d 1 : L))‖ = ‖(d 0 : L)‖⁻¹ * (‖v' 0‖ * ‖(d 1 : L)‖) := by
      rw [Units.val_inv_eq_inv_val, norm_mul, norm_inv, norm_mul]
    simp only [Matrix.cons_val_zero]
    rw [h, div_eq_inv_mul]
    calc ‖(d 0 : L)‖⁻¹ * (‖v' 0‖ * ‖(d 1 : L)‖) ≤ ‖(d 0 : L)‖⁻¹ * (M' * ‖(d 1 : L)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv'0 (norm_nonneg _)) (inv_nonneg.2 (norm_nonneg _))
      _ = M' * (‖(d 0 : L)‖⁻¹ * ‖(d 1 : L)‖) := by ring
  · have h : ‖(((d 0)⁻¹ : Lˣ) : L) * (v' 1 * (d 2 : L))‖ = ‖(d 0 : L)‖⁻¹ * (‖v' 1‖ * ‖(d 2 : L)‖) := by
      rw [Units.val_inv_eq_inv_val, norm_mul, norm_inv, norm_mul]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h, div_eq_inv_mul]
    calc ‖(d 0 : L)‖⁻¹ * (‖v' 1‖ * ‖(d 2 : L)‖) ≤ ‖(d 0 : L)‖⁻¹ * ((1 + C) * M' * ‖(d 2 : L)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv'1 (norm_nonneg _)) (inv_nonneg.2 (norm_nonneg _))
      _ = (1 + C) * M' * (‖(d 0 : L)‖⁻¹ * ‖(d 2 : L)‖) := by ring
  ·
    have hgroup : (upperUnipotent3 x y z * t * k)⁻¹ * radicalP12 v * (upperUnipotent3 x y z * t * k) =
        k⁻¹ * (t⁻¹ * ((upperUnipotent3 x y z)⁻¹ * radicalP12 v * upperUnipotent3 x y z) * t) * k := by
      simp only [_root_.mul_inv_rev, mul_assoc]
    have h1 := inv_mul_radicalP12_mul_upperUnipotent3 v x y z
    rw [← hv'] at h1
    have h2 := inv_mul_radicalP12_mul_of_coe_eq_diagonal v' t d ht
    unfold conjDisplacement
    rw [hgroup, h1, h2, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Units.inv_mul]

private theorem conjDisplacement_radicalP12_bound (x y z : L) {C : ℝ} (hy : ‖y‖ ≤ C) (t : GL (Fin 3) L)
    (d : Fin 3 → Lˣ) (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) (k : GL (Fin 3) L)
    (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) (v : Fin 2 → L) {M' : ℝ}
    (hv0 : ‖v 0‖ ≤ M') (hv1 : ‖v 1‖ ≤ M') :
    conjDisplacement (upperUnipotent3 x y z * t * k) (radicalP12 v) *
        conjDisplacement (upperUnipotent3 x y z * t * k) (radicalP12 v) = 0 ∧
      ∀ i j, ‖conjDisplacement (upperUnipotent3 x y z * t * k) (radicalP12 v) i j‖ ≤
        M' * (‖(d 1 : L)‖ / ‖(d 0 : L)‖) + (1 + C) * M' * (‖(d 2 : L)‖ / ‖(d 0 : L)‖) := by
  obtain ⟨w, hw0, hw1, hY⟩ := exists_conjDisplacement_radicalP12_eq x y z hy t d ht k v hv0 hv1
  rw [hY]
  refine ⟨conj_mul_self_eq_zero k _ (radicalP12_sub_one_mul_self w), fun i j => ?_⟩
  calc ‖(((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((radicalP12 w : Matrix (Fin 3) (Fin 3) L) - 1) *
          (k : Matrix (Fin 3) (Fin 3) L)) i j‖
        ≤ ∑ m : Fin 3, ∑ l : Fin 3, ‖((radicalP12 w : Matrix (Fin 3) (Fin 3) L) - 1) l m‖ :=
        norm_mul_mul_apply_le _ _ _ hk' hk i j
    _ = ‖w 0‖ + ‖w 1‖ := sum_norm_radicalP12_sub_one_apply w
    _ ≤ M' * (‖(d 1 : L)‖ / ‖(d 0 : L)‖) + (1 + C) * M' * (‖(d 2 : L)‖ / ‖(d 0 : L)‖) := add_le_add hw0 hw1

end Generic

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Real

private theorem abs_apply_le_one_of_transpose_mul_self (k : Matrix (Fin 3) (Fin 3) ℝ) (hk : k.transpose * k = 1)
    (i j : Fin 3) : |k i j| ≤ 1 := by
  have hdiag : (∑ l : Fin 3, k l j * k l j) = 1 := by
    have h := congrFun (congrFun hk j) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using h
  have hle : k i j * k i j ≤ ∑ l : Fin 3, k l j * k l j :=
    Finset.single_le_sum (f := fun l => k l j * k l j) (fun l _ => mul_self_nonneg (k l j)) (Finset.mem_univ i)
  rw [hdiag] at hle
  exact abs_le_one_iff_mul_self_le_one.2 hle

end Real

section Generic

variable {A : Type*} [CommRing A]

private theorem inv_coe_eq_transpose_of_transpose_mul_self (k : GL (Fin 3) A)
    (hk : (k : Matrix (Fin 3) (Fin 3) A).transpose * (k : Matrix (Fin 3) (Fin 3) A) = 1) :
    ((k⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = (k : Matrix (Fin 3) (Fin 3) A).transpose :=
  Units.inv_eq_of_mul_eq_one_right (_root_.mul_eq_one_comm.1 hk)

variable {L : Type*} [NormedField L] (ψ : L →+* ℝ) (hψ : ∀ a : L, ‖a‖ = |ψ a|)
include hψ

private theorem norm_apply_le_one_of_transpose_mul_self (k : Matrix (Fin 3) (Fin 3) L) (hk : k.transpose * k = 1)
    (i j : Fin 3) : ‖k i j‖ ≤ 1 := by
  have hmap : (k.map ψ).transpose * k.map ψ = 1 := by
    have h1 : (k.map ψ).transpose * k.map ψ = (k.transpose * k).map ψ := by
      simp [Matrix.map_mul, Matrix.transpose_map]
    rw [h1, hk]
    exact Matrix.map_one _ (map_zero ψ) (map_one ψ)
  have h := abs_apply_le_one_of_transpose_mul_self (k.map ψ) hmap i j
  rw [Matrix.map_apply] at h
  rw [hψ]
  exact h

private theorem norm_inv_apply_le_one_of_transpose_mul_self (k : GL (Fin 3) L)
    (hk : (k : Matrix (Fin 3) (Fin 3) L).transpose * (k : Matrix (Fin 3) (Fin 3) L) = 1) (i j : Fin 3) :
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1 := by
  rw [inv_coe_eq_transpose_of_transpose_mul_self k hk, Matrix.transpose_apply]
  exact norm_apply_le_one_of_transpose_mul_self ψ hψ _ hk j i

end Generic

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {L : Type*} [NormedField L]

private theorem norm_apply_le_matrixSupSize (h : GL (Fin 3) L) (i j : Fin 3) :
    ‖(h : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ ((matrixSupSize h : NNReal) : ℝ) := by
  have h1 : ‖(h : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize h :=
    (le_max_left _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
      max ‖(h : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
        ‖((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) (Finset.mem_univ (i, j)))
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [coe_nnnorm] at h2

private theorem norm_inv_apply_le_matrixSupSize (h : GL (Fin 3) L) (i j : Fin 3) :
    ‖((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ ((matrixSupSize h : NNReal) : ℝ) := by
  have h1 : ‖((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖₊ ≤ matrixSupSize h :=
    (le_max_right _ _).trans (Finset.le_sup (f := fun ij : Fin 3 × Fin 3 =>
      max ‖(h : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
        ‖((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊) (Finset.mem_univ (i, j)))
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [coe_nnnorm] at h2

private theorem norm_mul_apply_le_sum_mul (M N : Matrix (Fin 3) (Fin 3) L) {S : ℝ} (hN : ∀ i j, ‖N i j‖ ≤ S)
    (i j : Fin 3) : ‖(M * N) i j‖ ≤ (∑ l : Fin 3, ‖M i l‖) * S := by
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hN l j) (norm_nonneg _)

private theorem norm_mul_apply_le_mul_sum (M N : Matrix (Fin 3) (Fin 3) L) {S : ℝ} (hM : ∀ i j, ‖M i j‖ ≤ S)
    (i j : Fin 3) : ‖(M * N) i j‖ ≤ S * ∑ l : Fin 3, ‖N l j‖ := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM i l) (norm_nonneg _)

private theorem matrixSize_mul_le (k h : GL (Fin 3) L) :
    matrixSize (k * h) ≤ 3 * ((matrixSupSize h : NNReal) : ℝ) * matrixSize k := by
  have hentry : ∀ i j : Fin 3, ‖((k * h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤
      (∑ l : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) i l‖) * ((matrixSupSize h : NNReal) : ℝ) := by
    intro i j
    rw [Units.val_mul]
    exact norm_mul_apply_le_sum_mul _ _ (norm_apply_le_matrixSupSize h) i j
  have hentry' : ∀ i j : Fin 3, ‖(((k * h)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤
      ((matrixSupSize h : NNReal) : ℝ) * ∑ l : Fin 3, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) l j‖ := by
    intro i j
    rw [_root_.mul_inv_rev, Units.val_mul]
    exact norm_mul_apply_le_mul_sum _ _ (norm_inv_apply_le_matrixSupSize h) i j
  calc matrixSize (k * h)
      = ∑ i : Fin 3, ∑ j : Fin 3, (‖((k * h : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ +
          ‖(((k * h)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖) := rfl
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ((∑ l : Fin 3, ‖(k : Matrix (Fin 3) (Fin 3) L) i l‖) *
          ((matrixSupSize h : NNReal) : ℝ) +
        ((matrixSupSize h : NNReal) : ℝ) * ∑ l : Fin 3, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) l j‖) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => add_le_add (hentry i j) (hentry' i j)
    _ = 3 * ((matrixSupSize h : NNReal) : ℝ) * matrixSize k := by
        simp only [matrixSize, Fin.sum_univ_three]
        ring

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (F : Type) [Field F] [NumberField F]

private theorem finGauge3_mul_of_componentAt3_eq_one (g h : AdelicGL 3 (𝓞 F) F)
    (hfin : ∀ p : HeightOneSpectrum (𝓞 F), componentAt3 (𝓞 F) F p h = 1) :
    finGauge3 F (g * h) = finGauge3 F g := by
  unfold finGauge3
  exact finprod_congr fun p => by simp only [map_mul, hfin p, mul_one]

private theorem finGauge3_nonneg (g : AdelicGL 3 (𝓞 F) F) : 0 ≤ finGauge3 F g := by
  unfold finGauge3
  exact finprod_nonneg fun _ => NNReal.coe_nonneg _

private theorem archGauge3_mul_le (g h : AdelicGL 3 (𝓞 F) F) {S : ℝ}
    (hS : ∀ w : InfinitePlace F, ((matrixSupSize (archPlaceComponent3 F w h) : NNReal) : ℝ) ≤ S) :
    archGauge3 F (g * h) ≤ max 1 (3 * S) * archGauge3 F g := by
  have hA1 : (1 : ℝ) ≤ max 1 (3 * S) := le_max_left _ _
  have hterm : ∀ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w (g * h)) ≤
      max 1 (3 * S) * matrixSize (archPlaceComponent3 F w g) := by
    intro w
    rw [map_mul]
    refine (matrixSize_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (matrixSize_nonneg _))
    calc 3 * ((matrixSupSize (archPlaceComponent3 F w h) : NNReal) : ℝ) ≤ 3 * S :=
          mul_le_mul_of_nonneg_left (hS w) (by norm_num)
      _ ≤ max 1 (3 * S) := le_max_right _ _
  unfold archGauge3
  calc 1 + ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w (g * h))
      ≤ max 1 (3 * S) + ∑ w : InfinitePlace F, max 1 (3 * S) * matrixSize (archPlaceComponent3 F w g) :=
        add_le_add hA1 (Finset.sum_le_sum fun w _ => hterm w)
    _ = max 1 (3 * S) * (1 + ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w g)) := by
        rw [mul_add, mul_one, Finset.mul_sum]

private theorem gauge3_mul_le_of_componentAt3_eq_one (g h : AdelicGL 3 (𝓞 F) F)
    (hfin : ∀ p : HeightOneSpectrum (𝓞 F), componentAt3 (𝓞 F) F p h = 1) {S : ℝ}
    (hS : ∀ w : InfinitePlace F, ((matrixSupSize (archPlaceComponent3 F w h) : NNReal) : ℝ) ≤ S) :
    gauge3 F (g * h) ≤ max 1 (3 * S) * gauge3 F g := by
  have hA1 : (1 : ℝ) ≤ max 1 (3 * S) := le_max_left _ _
  have hA0 : (0 : ℝ) ≤ max 1 (3 * S) := zero_le_one.trans hA1
  have harch := archGauge3_mul_le F g h hS
  have hfin0 := finGauge3_nonneg F g
  unfold gauge3
  rw [finGauge3_mul_of_componentAt3_eq_one F g h hfin]
  refine max_le ?_ ?_
  · calc (1 : ℝ) ≤ max 1 (3 * S) := hA1
      _ = max 1 (3 * S) * 1 := (mul_one _).symm
      _ ≤ max 1 (3 * S) * max 1 (archGauge3 F g * finGauge3 F g) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hA0
  · calc archGauge3 F (g * h) * finGauge3 F g ≤ max 1 (3 * S) * archGauge3 F g * finGauge3 F g :=
          mul_le_mul_of_nonneg_right harch hfin0
      _ = max 1 (3 * S) * (archGauge3 F g * finGauge3 F g) := mul_assoc _ _ _
      _ ≤ max 1 (3 * S) * max 1 (archGauge3 F g * finGauge3 F g) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hA0

private theorem norm_apply_mul_le_of_forall_norm_le {f : AdelicGL 3 (𝓞 F) F → ℂ} {C : ℝ} {N : ℕ}
    (hf : ∀ g, ‖f g‖ ≤ C * gauge3 F g ^ N) (hC : 0 ≤ C) (g h : AdelicGL 3 (𝓞 F) F)
    (hfin : ∀ p : HeightOneSpectrum (𝓞 F), componentAt3 (𝓞 F) F p h = 1) {S : ℝ}
    (hS : ∀ w : InfinitePlace F, ((matrixSupSize (archPlaceComponent3 F w h) : NNReal) : ℝ) ≤ S) :
    ‖f (g * h)‖ ≤ C * max 1 (3 * S) ^ N * gauge3 F g ^ N := by
  calc ‖f (g * h)‖ ≤ C * gauge3 F (g * h) ^ N := hf _
    _ ≤ C * (max 1 (3 * S) * gauge3 F g) ^ N :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (gauge3_pos F _).le (gauge3_mul_le_of_componentAt3_eq_one F g h hfin hS) N) hC
    _ = C * max 1 (3 * S) ^ N * gauge3 F g ^ N := by rw [mul_pow, mul_assoc]

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Unipotent

variable {A : Type*} [CommRing A]

private theorem eq_upperUnipotent3_of_coe (n : GL (Fin 3) A) (hdiag : ∀ i, (n : Matrix (Fin 3) (Fin 3) A) i i = 1)
    (hlow : ∀ i j : Fin 3, j < i → (n : Matrix (Fin 3) (Fin 3) A) i j = 0) :
    n = upperUnipotent3 ((n : Matrix (Fin 3) (Fin 3) A) 0 1) ((n : Matrix (Fin 3) (Fin 3) A) 1 2)
      ((n : Matrix (Fin 3) (Fin 3) A) 0 2) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hdiag, hlow]

end Unipotent

section Diagonal

variable {F : Type*} [Field F]

private theorem exists_coe_eq_diagonal (t : GL (Fin 3) F)
    (hoff : ∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    ∃ d : Fin 3 → Fˣ, (t : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal fun i => (d i : F) := by
  have hdiagm : (t : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal fun i => (t : Matrix (Fin 3) (Fin 3) F) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hoff i j hij
  have hdet : IsUnit (t : Matrix (Fin 3) (Fin 3) F).det := (Matrix.isUnit_iff_isUnit_det _).1 t.isUnit
  rw [hdiagm, Matrix.det_diagonal] at hdet
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin 3)), (t : Matrix (Fin 3) (Fin 3) F) i i ≠ 0 :=
    Finset.prod_ne_zero_iff.1 hdet.ne_zero
  exact ⟨fun i => Units.mk0 _ (hne i (Finset.mem_univ i)), hdiagm⟩

end Diagonal

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private noncomputable def windowBoundK (c a b K : ℝ) : ℝ :=
  max (max 1 (b / (c * c * c))) (max 1 a⁻¹) * (K * K * K * K * K * K)

private noncomputable def windowBound (c a b : ℝ) : ℝ := windowBoundK c a b (max 1 c⁻¹)

section Core

variable {c a b K r₁ r₂ τ : ℝ}

private theorem window_le_max_one_cube {x : ℝ} (hx : 0 ≤ x) : x ≤ max 1 (x * x * x) := by
  by_cases h : x ≤ 1
  · exact h.trans (le_max_left _ _)
  · have h1 : 1 ≤ x * x := one_le_mul_of_one_le_of_one_le (not_le.mp h).le (not_le.mp h).le
    have h2 : x ≤ x * x * x := by
      calc x = 1 * x := (one_mul x).symm
        _ ≤ x * x * x := mul_le_mul_of_nonneg_right h1 hx
    exact h2.trans (le_max_right _ _)

private theorem window_one_le_K (hc : 0 < c) : 1 ≤ max 1 c⁻¹ ∧ 1 ≤ max 1 c⁻¹ * c :=
  ⟨le_max_left _ _, by
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ max 1 c⁻¹ * c := mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le⟩

private theorem window_Q_facts (hc : 0 < c) (hK : 1 ≤ K) (hKc : 1 ≤ K * c) (h₁ : c ≤ r₁) (h₂ : c ≤ r₂) :
    1 ≤ K * K * (r₁ * r₂) ∧ r₁ * r₂ ≤ K * K * (r₁ * r₂) ∧ r₂ ≤ K * K * (r₁ * r₂) ∧
      r₂⁻¹ ≤ K ∧ (r₁ * r₂)⁻¹ ≤ K * K := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hr₁ : 0 < r₁ := hc.trans_le h₁
  have hr₂ : 0 < r₂ := hc.trans_le h₂
  have hP : 0 < r₁ * r₂ := mul_pos hr₁ hr₂
  have hKr₁ : 1 ≤ K * r₁ := hKc.trans (mul_le_mul_of_nonneg_left h₁ hK0)
  have hKr₂ : 1 ≤ K * r₂ := hKc.trans (mul_le_mul_of_nonneg_left h₂ hK0)
  have hKK : 1 ≤ K * K := one_le_mul_of_one_le_of_one_le hK hK
  have hQ : 1 ≤ K * K * (r₁ * r₂) := by
    calc (1 : ℝ) ≤ (K * r₁) * (K * r₂) := one_le_mul_of_one_le_of_one_le hKr₁ hKr₂
      _ = K * K * (r₁ * r₂) := by ring
  refine ⟨hQ, le_mul_of_one_le_left hP.le hKK, ?_, ?_, ?_⟩
  · have h : 1 ≤ K * (K * r₁) := one_le_mul_of_one_le_of_one_le hK hKr₁
    calc r₂ = 1 * r₂ := (one_mul _).symm
      _ ≤ (K * (K * r₁)) * r₂ := mul_le_mul_of_nonneg_right h hr₂.le
      _ = K * K * (r₁ * r₂) := by ring
  · calc r₂⁻¹ = r₂⁻¹ * 1 := (mul_one _).symm
      _ ≤ r₂⁻¹ * (K * r₂) := mul_le_mul_of_nonneg_left hKr₂ (inv_nonneg.2 hr₂.le)
      _ = K * (r₂⁻¹ * r₂) := by ring
      _ = K := by rw [inv_mul_cancel₀ hr₂.ne', mul_one]
  · calc (r₁ * r₂)⁻¹ = (r₁ * r₂)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (r₁ * r₂)⁻¹ * (K * K * (r₁ * r₂)) := mul_le_mul_of_nonneg_left hQ (inv_nonneg.2 hP.le)
      _ = K * K * ((r₁ * r₂)⁻¹ * (r₁ * r₂)) := by ring
      _ = K * K := by rw [inv_mul_cancel₀ hP.ne', mul_one]

private theorem window_tau_le (hc : 0 < c) (h₁ : c ≤ r₁) (h₂ : c ≤ r₂) (hτ : 0 ≤ τ)
    (hb : r₁ * r₂ * r₂ * (τ * τ * τ) ≤ b) : τ ≤ max 1 (b / (c * c * c)) := by
  have hccc : 0 < c * c * c := mul_pos (mul_pos hc hc) hc
  have hr₁ : 0 ≤ r₁ := hc.le.trans h₁
  have hr₂ : 0 ≤ r₂ := hc.le.trans h₂
  have hcr : c * c * c ≤ r₁ * r₂ * r₂ := by
    have h12 : c * c ≤ r₁ * r₂ := mul_le_mul h₁ h₂ hc.le hr₁
    exact mul_le_mul h12 h₂ hc.le (mul_nonneg hr₁ hr₂)
  have hτ3 : 0 ≤ τ * τ * τ := mul_nonneg (mul_nonneg hτ hτ) hτ
  have hcube : τ * τ * τ ≤ b / (c * c * c) := by
    rw [le_div_iff₀ hccc]
    calc τ * τ * τ * (c * c * c) = c * c * c * (τ * τ * τ) := by ring
      _ ≤ r₁ * r₂ * r₂ * (τ * τ * τ) := mul_le_mul_of_nonneg_right hcr hτ3
      _ ≤ b := hb
  exact (window_le_max_one_cube hτ).trans (max_le_max le_rfl hcube)

private theorem window_inv_tau_le (hc : 0 < c) (hK : 1 ≤ K) (hKc : 1 ≤ K * c) (h₁ : c ≤ r₁) (h₂ : c ≤ r₂)
    (hτ : 0 < τ) (ha0 : 0 < a) (ha : a ≤ r₁ * r₂ * r₂ * (τ * τ * τ)) :
    τ⁻¹ ≤ max 1 a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) := by
  obtain ⟨hQ1, hPQ, hr₂Q, -, -⟩ := window_Q_facts hc hK hKc h₁ h₂
  have hQ0 : 0 ≤ K * K * (r₁ * r₂) := zero_le_one.trans hQ1
  have hQQ1 : 1 ≤ K * K * (r₁ * r₂) * (K * K * (r₁ * r₂)) := one_le_mul_of_one_le_of_one_le hQ1 hQ1
  have hQQ0 : 0 ≤ K * K * (r₁ * r₂) * (K * K * (r₁ * r₂)) := zero_le_one.trans hQQ1
  have hr₂ : 0 ≤ r₂ := hc.le.trans h₂
  have hT : 0 < τ * τ * τ := mul_pos (mul_pos hτ hτ) hτ
  have hX : r₁ * r₂ * r₂ ≤ K * K * (r₁ * r₂) * (K * K * (r₁ * r₂)) := mul_le_mul hPQ hr₂Q hr₂ hQ0
  have hinv3 : (τ * τ * τ)⁻¹ ≤ r₁ * r₂ * r₂ / a := by
    rw [le_div_iff₀ ha0]
    calc (τ * τ * τ)⁻¹ * a ≤ (τ * τ * τ)⁻¹ * (r₁ * r₂ * r₂ * (τ * τ * τ)) :=
          mul_le_mul_of_nonneg_left ha (inv_nonneg.2 hT.le)
      _ = r₁ * r₂ * r₂ * ((τ * τ * τ)⁻¹ * (τ * τ * τ)) := by ring
      _ = r₁ * r₂ * r₂ := by rw [inv_mul_cancel₀ hT.ne', mul_one]
  have hsplit : τ⁻¹ * τ⁻¹ * τ⁻¹ = (τ * τ * τ)⁻¹ := by rw [mul_inv, mul_inv]
  have hstep : τ⁻¹ * τ⁻¹ * τ⁻¹ ≤ a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) := by
    rw [hsplit]
    calc (τ * τ * τ)⁻¹ ≤ r₁ * r₂ * r₂ / a := hinv3
      _ = a⁻¹ * (r₁ * r₂ * r₂) := by rw [div_eq_inv_mul]
      _ ≤ a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) :=
          mul_le_mul_of_nonneg_left hX (inv_nonneg.2 ha0.le)
  calc τ⁻¹ ≤ max 1 (τ⁻¹ * τ⁻¹ * τ⁻¹) := window_le_max_one_cube (inv_nonneg.2 hτ.le)
    _ ≤ max 1 a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) :=
        max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hQQ1)
          (hstep.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hQQ0))

private theorem window_le_bound_of_le {x N M P : ℝ} (hM : M = max (max 1 (b / (c * c * c))) (max 1 a⁻¹))
    (hx : x ≤ N * (K * K * P * (K * K * P))) (hN : N ≤ M * (K * K)) (hK0 : 0 ≤ K) (hP : 0 ≤ P) :
    x ≤ windowBoundK c a b K * (P * P) := by
  subst hM
  have hQ0 : 0 ≤ K * K * P := mul_nonneg (mul_nonneg hK0 hK0) hP
  calc x ≤ N * (K * K * P * (K * K * P)) := hx
    _ ≤ max (max 1 (b / (c * c * c))) (max 1 a⁻¹) * (K * K) * (K * K * P * (K * K * P)) :=
        mul_le_mul_of_nonneg_right hN (mul_nonneg hQ0 hQ0)
    _ = windowBoundK c a b K * (P * P) := by unfold windowBoundK; ring

private theorem window_sizes_le_core (hc : 0 < c) (hK : 1 ≤ K) (hKc : 1 ≤ K * c) (h₁ : c ≤ r₁) (h₂ : c ≤ r₂)
    (hτ : 0 < τ) (ha0 : 0 < a) (ha : a ≤ r₁ * r₂ * r₂ * (τ * τ * τ)) (hb : r₁ * r₂ * r₂ * (τ * τ * τ) ≤ b) :
    r₁ * r₂ * τ ≤ windowBoundK c a b K * (r₁ * r₂ * (r₁ * r₂)) ∧
      r₂ * τ ≤ windowBoundK c a b K * (r₁ * r₂ * (r₁ * r₂)) ∧
      τ ≤ windowBoundK c a b K * (r₁ * r₂ * (r₁ * r₂)) ∧
      (r₁ * r₂ * τ)⁻¹ ≤ windowBoundK c a b K * (r₁ * r₂ * (r₁ * r₂)) ∧
      (r₂ * τ)⁻¹ ≤ windowBoundK c a b K * (r₁ * r₂ * (r₁ * r₂)) ∧
      τ⁻¹ ≤ windowBoundK c a b K * (r₁ * r₂ * (r₁ * r₂)) := by
  obtain ⟨hQ1, hPQ, hr₂Q, hinvr₂, hinvP⟩ := window_Q_facts hc hK hKc h₁ h₂
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max (max 1 (b / (c * c * c))) (max 1 a⁻¹) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKK : 1 ≤ K * K := one_le_mul_of_one_le_of_one_le hK hK
  have hKK0 : 0 ≤ K * K := zero_le_one.trans hKK
  have hP0 : 0 ≤ r₁ * r₂ := mul_nonneg (hc.le.trans h₁) (hc.le.trans h₂)
  have hQ0 : 0 ≤ K * K * (r₁ * r₂) := zero_le_one.trans hQ1
  have hQQ1 : 1 ≤ K * K * (r₁ * r₂) * (K * K * (r₁ * r₂)) := one_le_mul_of_one_le_of_one_le hQ1 hQ1
  have hU0 : 0 ≤ max 1 (b / (c * c * c)) := zero_le_one.trans (le_max_left _ _)
  have hτU : τ ≤ max 1 (b / (c * c * c)) := window_tau_le hc h₁ h₂ hτ.le hb
  have hτV : τ⁻¹ ≤ max 1 a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) :=
    window_inv_tau_le hc hK hKc h₁ h₂ hτ ha0 ha

  have hUM : max 1 (b / (c * c * c)) ≤ M := by rw [hM]; exact le_max_left _ _
  have hVM : max 1 a⁻¹ ≤ M := by rw [hM]; exact le_max_right _ _
  have hM0 : 0 ≤ M := hU0.trans hUM
  have hMKK : M ≤ M * (K * K) := le_mul_of_one_le_right hM0 hKK
  have hMU : max 1 (b / (c * c * c)) ≤ M * (K * K) := hUM.trans hMKK
  have hMV : max 1 a⁻¹ ≤ M * (K * K) := hVM.trans hMKK
  have hMKV : K * max 1 a⁻¹ ≤ M * (K * K) := by
    calc K * max 1 a⁻¹ ≤ K * M := mul_le_mul_of_nonneg_left hVM hK0
      _ = M * (K * 1) := by ring
      _ ≤ M * (K * K) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hK0) hM0
  have hMKKV : K * K * max 1 a⁻¹ ≤ M * (K * K) := by
    calc K * K * max 1 a⁻¹ ≤ K * K * M := mul_le_mul_of_nonneg_left hVM hKK0
      _ = M * (K * K) := by ring

  have hQU : ∀ {y : ℝ}, y ≤ K * K * (r₁ * r₂) * max 1 (b / (c * c * c)) →
      y ≤ max 1 (b / (c * c * c)) * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) := fun hy =>
    hy.trans (by
      calc K * K * (r₁ * r₂) * max 1 (b / (c * c * c))
          = max 1 (b / (c * c * c)) * (K * K * (r₁ * r₂) * 1) := by ring
        _ ≤ max 1 (b / (c * c * c)) * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ1 hQ0) hU0)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact window_le_bound_of_le hM (hQU (mul_le_mul hPQ hτU hτ.le hQ0)) hMU hK0 hP0
  · exact window_le_bound_of_le hM (hQU (mul_le_mul hr₂Q hτU hτ.le hQ0)) hMU hK0 hP0
  · refine window_le_bound_of_le hM ?_ hMU hK0 hP0
    calc τ ≤ max 1 (b / (c * c * c)) := hτU
      _ = max 1 (b / (c * c * c)) * 1 := (mul_one _).symm
      _ ≤ max 1 (b / (c * c * c)) * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) :=
          mul_le_mul_of_nonneg_left hQQ1 hU0
  · refine window_le_bound_of_le hM ?_ hMKKV hK0 hP0
    rw [mul_inv]
    calc (r₁ * r₂)⁻¹ * τ⁻¹ ≤ K * K * (max 1 a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂)))) :=
          mul_le_mul hinvP hτV (inv_nonneg.2 hτ.le) hKK0
      _ = K * K * max 1 a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) := by ring
  · refine window_le_bound_of_le hM ?_ hMKV hK0 hP0
    rw [mul_inv]
    calc r₂⁻¹ * τ⁻¹ ≤ K * (max 1 a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂)))) :=
          mul_le_mul hinvr₂ hτV (inv_nonneg.2 hτ.le) hK0
      _ = K * max 1 a⁻¹ * (K * K * (r₁ * r₂) * (K * K * (r₁ * r₂))) := by ring
  · exact window_le_bound_of_le hM hτV hMV hK0 hP0

end Core

section Entries

variable {c a b : ℝ}

private theorem window_sizes_le (e : Fin 3 → ℝ) (he : ∀ i, 0 < e i) (hc : 0 < c) (h₁ : c ≤ e 0 / e 1)
    (h₂ : c ≤ e 1 / e 2) (ha0 : 0 < a) (ha : a ≤ e 0 * e 1 * e 2) (hb : e 0 * e 1 * e 2 ≤ b) :
    (∀ i, e i ≤ windowBound c a b * (e 0 / e 1 * (e 1 / e 2) * (e 0 / e 1 * (e 1 / e 2)))) ∧
      ∀ i, (e i)⁻¹ ≤ windowBound c a b * (e 0 / e 1 * (e 1 / e 2) * (e 0 / e 1 * (e 1 / e 2))) := by
  unfold windowBound
  obtain ⟨hK, hKc⟩ := window_one_le_K hc
  have he1 : e 1 ≠ 0 := (he 1).ne'
  have hr₂e : e 1 / e 2 * e 2 = e 1 := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (he 2).ne', mul_one]
  have hr₁r₂e : e 0 / e 1 * (e 1 / e 2) * e 2 = e 0 := by
    rw [mul_assoc, hr₂e, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ he1, mul_one]
  have hprod : e 0 / e 1 * (e 1 / e 2) * (e 1 / e 2) * (e 2 * e 2 * e 2) = e 0 * e 1 * e 2 := by
    calc e 0 / e 1 * (e 1 / e 2) * (e 1 / e 2) * (e 2 * e 2 * e 2)
        = e 0 / e 1 * (e 1 / e 2) * e 2 * (e 1 / e 2 * e 2) * e 2 := by ring
      _ = e 0 * e 1 * e 2 := by rw [hr₁r₂e, hr₂e]
  rw [← hprod] at ha hb
  obtain ⟨b0, b1, b2, b0', b1', b2'⟩ := window_sizes_le_core hc hK hKc h₁ h₂ (he 2) ha0 ha hb
  rw [hr₁r₂e] at b0 b0'
  rw [hr₂e] at b1 b1'
  exact ⟨fun i => match i with | 0 => b0 | 1 => b1 | 2 => b2,
    fun i => match i with | 0 => b0' | 1 => b1' | 2 => b2'⟩

end Entries

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem div_le_max_one_inv_of_le_div {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (h : c ≤ x / y) :
    y / x ≤ max 1 c⁻¹ := by
  have hKc : 1 ≤ max 1 c⁻¹ * c := by
    calc (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ max 1 c⁻¹ * c := mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le
  have hK0 : 0 ≤ max 1 c⁻¹ := zero_le_one.trans (le_max_left _ _)
  have hcy : c * y ≤ x := (le_div_iff₀ hy).mp h
  rw [div_le_iff₀ hx]
  calc y = 1 * y := (one_mul y).symm
    _ ≤ max 1 c⁻¹ * c * y := mul_le_mul_of_nonneg_right hKc hy.le
    _ = max 1 c⁻¹ * (c * y) := by ring
    _ ≤ max 1 c⁻¹ * x := mul_le_mul_of_nonneg_left hcy hK0

private theorem displacementBound_P21_le {C c M' e₀ e₁ e₂ : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hM : 0 ≤ M') (he₀ : 0 < e₀)
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) (h₁ : c ≤ e₀ / e₁) :
    (1 + C) * M' * (e₂ / e₀) + M' * (e₂ / e₁) ≤ 2 * (1 + C) * max 1 c⁻¹ * M' / (e₁ / e₂) := by
  have hq : e₁ / e₀ ≤ max 1 c⁻¹ := div_le_max_one_inv_of_le_div hc he₀ he₁ h₁
  have hA : e₂ / e₀ * (e₁ / e₂) = e₁ / e₀ := by
    rw [div_mul_div_comm, mul_comm e₂ e₁, mul_div_mul_right _ _ he₂.ne']
  have hB : e₂ / e₁ * (e₁ / e₂) = 1 := by
    rw [div_mul_div_comm, mul_comm e₂ e₁, div_self (mul_ne_zero he₁.ne' he₂.ne')]
  rw [le_div_iff₀ (div_pos he₁ he₂)]
  have hexp : ((1 + C) * M' * (e₂ / e₀) + M' * (e₂ / e₁)) * (e₁ / e₂) =
      (1 + C) * M' * (e₂ / e₀ * (e₁ / e₂)) + M' * (e₂ / e₁ * (e₁ / e₂)) := by ring
  rw [hexp, hA, hB, mul_one]
  have h1 : (1 + C) * M' * (e₁ / e₀) ≤ (1 + C) * M' * max 1 c⁻¹ :=
    mul_le_mul_of_nonneg_left hq (mul_nonneg (by linarith) hM)
  have h2 : M' ≤ (1 + C) * max 1 c⁻¹ * M' := by
    have h : 1 ≤ (1 + C) * max 1 c⁻¹ := one_le_mul_of_one_le_of_one_le (by linarith) (le_max_left _ _)
    calc M' = 1 * M' := (one_mul M').symm
      _ ≤ (1 + C) * max 1 c⁻¹ * M' := mul_le_mul_of_nonneg_right h hM
  linarith

private theorem displacementBound_P12_le {C c M' e₀ e₁ e₂ : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hM : 0 ≤ M') (he₀ : 0 < e₀)
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) (h₂ : c ≤ e₁ / e₂) :
    M' * (e₁ / e₀) + (1 + C) * M' * (e₂ / e₀) ≤ 2 * (1 + C) * max 1 c⁻¹ * M' / (e₀ / e₁) := by
  have hq : e₂ / e₁ ≤ max 1 c⁻¹ := div_le_max_one_inv_of_le_div hc he₁ he₂ h₂
  have hA : e₁ / e₀ * (e₀ / e₁) = 1 := by
    rw [div_mul_div_comm, mul_comm e₁ e₀, div_self (mul_ne_zero he₀.ne' he₁.ne')]
  have hB : e₂ / e₀ * (e₀ / e₁) = e₂ / e₁ := by
    rw [div_mul_div_comm, mul_comm e₀ e₁, mul_div_mul_right _ _ he₀.ne']
  rw [le_div_iff₀ (div_pos he₀ he₁)]
  have hexp : (M' * (e₁ / e₀) + (1 + C) * M' * (e₂ / e₀)) * (e₀ / e₁) =
      M' * (e₁ / e₀ * (e₀ / e₁)) + (1 + C) * M' * (e₂ / e₀ * (e₀ / e₁)) := by ring
  rw [hexp, hA, hB, mul_one]
  have h1 : (1 + C) * M' * (e₂ / e₁) ≤ (1 + C) * M' * max 1 c⁻¹ :=
    mul_le_mul_of_nonneg_left hq (mul_nonneg (by linarith) hM)
  have h2 : M' ≤ (1 + C) * max 1 c⁻¹ * M' := by
    have h : 1 ≤ (1 + C) * max 1 c⁻¹ := one_le_mul_of_one_le_of_one_le (by linarith) (le_max_left _ _)
    calc M' = 1 * M' := (one_mul M').symm
      _ ≤ (1 + C) * max 1 c⁻¹ * M' := mul_le_mul_of_nonneg_right h hM
  linarith

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Generic

variable {A B : Type*} [CommRing A] [CommRing B]

private theorem map_upperUnipotent3 (f : A →+* B) (x y z : A) :
    Matrix.GeneralLinearGroup.map f (upperUnipotent3 x y z) = upperUnipotent3 (f x) (f y) (f z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]

private theorem map_radicalP21 (f : A →+* B) (v : Fin 2 → A) :
    Matrix.GeneralLinearGroup.map f (radicalP21 v) = radicalP21 fun i => f (v i) := by
  simp [radicalP21, map_upperUnipotent3]

private theorem map_radicalP12 (f : A →+* B) (v : Fin 2 → A) :
    Matrix.GeneralLinearGroup.map f (radicalP12 v) = radicalP12 fun i => f (v i) := by
  simp [radicalP12, map_upperUnipotent3]

end Generic

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem componentAt3_radicalP21 (v : HeightOneSpectrum R) (u : Fin 2 → AdeleRing R K) :
    componentAt3 R K v (radicalP21 u) =
      radicalP21 fun i => AdelicLevel.finAdeleEval R K v (AdelicLevel.adeleFin R K (u i)) := by
  unfold componentAt3 componentAtN
  exact map_radicalP21 _ u

private theorem componentAt3_radicalP12 (v : HeightOneSpectrum R) (u : Fin 2 → AdeleRing R K) :
    componentAt3 R K v (radicalP12 u) =
      radicalP12 fun i => AdelicLevel.finAdeleEval R K v (AdelicLevel.adeleFin R K (u i)) := by
  unfold componentAt3 componentAtN
  exact map_radicalP12 _ u

end Finite

section Arch

variable (F : Type) [Field F] [NumberField F]

private theorem archPlaceComponent3_radicalP21 (w : InfinitePlace F) (u : Fin 2 → AdeleRing (𝓞 F) F) :
    archPlaceComponent3 F w (radicalP21 u) =
      radicalP21 fun i => AdelicLevel.archEval F w (AdelicLevel.adeleArch (𝓞 F) F (u i)) := by
  unfold archPlaceComponent3 archComponent3 archComponentN
  rw [MonoidHom.comp_apply, map_radicalP21, map_radicalP21]

private theorem archPlaceComponent3_radicalP12 (w : InfinitePlace F) (u : Fin 2 → AdeleRing (𝓞 F) F) :
    archPlaceComponent3 F w (radicalP12 u) =
      radicalP12 fun i => AdelicLevel.archEval F w (AdelicLevel.adeleArch (𝓞 F) F (u i)) := by
  unfold archPlaceComponent3 archComponent3 archComponentN
  rw [MonoidHom.comp_apply, map_radicalP12, map_radicalP12]

end Arch

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem norm_eq_abs_extensionEmbeddingOfIsReal {K : Type*} [Field K] {v : NumberField.InfinitePlace K}
    (hv : v.IsReal) (a : v.Completion) :
    ‖a‖ = |NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv a| := by
  rw [← Real.norm_eq_abs,
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
      (map_zero _)]

private theorem isReal_of_infinitePlace_rat (w : NumberField.InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private theorem norm_eq_abs_ratRealCoordinate (a : (Rat.infinitePlace).Completion) :
    ‖a‖ = |NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace a| :=
  norm_eq_abs_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace a

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Unipotent

variable {A : Type*} [CommRing A]

private theorem upperUnipotent3_inv_coe (x y z : A) :
    (((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl

private theorem inv_coe_of_coe_eq_diagonal (t : GL (Fin 3) A) (d : Fin 3 → Aˣ)
    (ht : (t : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun i => (d i : A)) :
    ((t⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = Matrix.diagonal fun i => (((d i)⁻¹ : Aˣ) : A) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact Units.mul_inv (d i)

end Unipotent

section Sizes

variable {L : Type*} [NormedField L]

private theorem matrixSize_upperUnipotent3_le {x y z : L} {C : ℝ} (hC : 0 ≤ C) (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C)
    (hz : ‖z‖ ≤ C) : matrixSize (upperUnipotent3 x y z) ≤ 6 + 6 * C + C ^ 2 := by
  have hxy : ‖x * y - z‖ ≤ C ^ 2 + C := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ hz)
    rw [norm_mul, pow_two]
    exact mul_le_mul hx hy (norm_nonneg _) hC
  have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have h1 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  simp only [matrixSize, upperUnipotent3_inv_coe]
  simp [Fin.sum_univ_three]
  linarith

private theorem matrixSupSize_le_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → Lˣ)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) {B : ℝ}
    (hB : ∀ i, ‖(d i : L)‖ ≤ B) (hB' : ∀ i, ‖(d i : L)‖⁻¹ ≤ B) :
    ((matrixSupSize t : NNReal) : ℝ) ≤ B := by
  have hBnn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hinv := inv_coe_of_coe_eq_diagonal t d ht
  have hentry : ∀ i j : Fin 3, ‖(t : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ B := by
    intro i j
    rw [ht]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hB i
    · rw [Matrix.diagonal_apply_ne _ hij, norm_zero]
      exact hBnn
  have hentry' : ∀ i j : Fin 3, ‖((t⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ B := by
    intro i j
    rw [hinv]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Units.val_inv_eq_inv_val, norm_inv]
      exact hB' i
    · rw [Matrix.diagonal_apply_ne _ hij, norm_zero]
      exact hBnn
  have hsize : matrixSupSize t ≤ ⟨B, hBnn⟩ := by
    unfold matrixSupSize
    refine Finset.sup_le fun ij _ => max_le ?_ ?_
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hentry ij.1 ij.2
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hentry' ij.1 ij.2
  exact NNReal.coe_le_coe.mpr hsize

end Sizes

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Generic

variable {L : Type*} [NormedField L]

private theorem matrixSupSize_le_of_forall_norm_le (h : GL (Fin 3) L) {B : ℝ} (hB0 : 0 ≤ B)
    (h1 : ∀ i j, ‖(h : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ B)
    (h2 : ∀ i j, ‖((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ B) :
    ((matrixSupSize h : NNReal) : ℝ) ≤ B := by
  have hsize : matrixSupSize h ≤ ⟨B, hB0⟩ := by
    unfold matrixSupSize
    refine Finset.sup_le fun ij _ => max_le ?_ ?_
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact h1 ij.1 ij.2
    · rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact h2 ij.1 ij.2
  exact NNReal.coe_le_coe.mpr hsize

private theorem matrixSize_mul_mul_le_of_le (n t k : GL (Fin 3) L) {N T : ℝ} (hn : matrixSize n ≤ N)
    (ht : ((matrixSupSize t : NNReal) : ℝ) ≤ T) (hk : ((matrixSupSize k : NNReal) : ℝ) ≤ 1) :
    matrixSize (n * t * k) ≤ 9 * T * N := by
  have hN0 : 0 ≤ matrixSize n := matrixSize_nonneg n
  have hT0 : 0 ≤ T := (NNReal.coe_nonneg _).trans ht
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hnt : matrixSize (n * t) ≤ 3 * T * N :=
    calc matrixSize (n * t) ≤ 3 * ((matrixSupSize t : NNReal) : ℝ) * matrixSize n := matrixSize_mul_le n t
      _ ≤ 3 * T * N := mul_le_mul (mul_le_mul_of_nonneg_left ht h3) hn hN0 (mul_nonneg h3 hT0)
  calc matrixSize (n * t * k) ≤ 3 * ((matrixSupSize k : NNReal) : ℝ) * matrixSize (n * t) :=
        matrixSize_mul_le (n * t) k
    _ ≤ 3 * 1 * (3 * T * N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hk h3) hnt (matrixSize_nonneg _) (by norm_num)
    _ = 9 * T * N := by ring

private theorem matrixSize_unipotent_mul_diagonal_mul_le {C c a b : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (ha0 : 0 < a)
    {x y z : L} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) (hz : ‖z‖ ≤ C) (t : GL (Fin 3) L) (d : Fin 3 → Lˣ)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L))
    (h₁ : c ≤ ‖(d 0 : L)‖ / ‖(d 1 : L)‖) (h₂ : c ≤ ‖(d 1 : L)‖ / ‖(d 2 : L)‖)
    (ha : a ≤ ‖(d 0 : L)‖ * ‖(d 1 : L)‖ * ‖(d 2 : L)‖) (hb : ‖(d 0 : L)‖ * ‖(d 1 : L)‖ * ‖(d 2 : L)‖ ≤ b)
    (k : GL (Fin 3) L) (hk : ∀ i j, ‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ 1) :
    matrixSize (upperUnipotent3 x y z * t * k) ≤
      9 * (windowBound c a b *
          (‖(d 0 : L)‖ / ‖(d 1 : L)‖ * (‖(d 1 : L)‖ / ‖(d 2 : L)‖) *
            (‖(d 0 : L)‖ / ‖(d 1 : L)‖ * (‖(d 1 : L)‖ / ‖(d 2 : L)‖)))) *
        (6 + 6 * C + C ^ 2) := by
  have he : ∀ i : Fin 3, 0 < ‖(d i : L)‖ := fun i => norm_pos_iff.mpr (d i).ne_zero
  obtain ⟨hB, hB'⟩ := window_sizes_le (fun i => ‖(d i : L)‖) he hc h₁ h₂ ha0 ha hb
  exact matrixSize_mul_mul_le_of_le _ t k (matrixSize_upperUnipotent3_le hC hx hy hz)
    (matrixSupSize_le_of_coe_eq_diagonal t d ht hB hB') (matrixSupSize_le_of_forall_norm_le k zero_le_one hk hk')

end Generic

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Sizes

variable {L : Type*} [NormedField L]

private theorem add_norm_apply_nonneg (h : GL (Fin 3) L) (i j : Fin 3) :
    0 ≤ ‖(h : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem norm_apply_le_matrixSize (h : GL (Fin 3) L) (i j : Fin 3) :
    ‖(h : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ matrixSize h := by
  unfold matrixSize
  refine le_trans ?_ (Finset.single_le_sum
    (fun i' _ => Finset.sum_nonneg fun j' _ => add_norm_apply_nonneg h i' j') (Finset.mem_univ i))
  refine le_trans ?_ (Finset.single_le_sum (fun j' _ => add_norm_apply_nonneg h i j') (Finset.mem_univ j))
  exact le_add_of_nonneg_right (norm_nonneg _)

private theorem norm_inv_apply_le_matrixSize (h : GL (Fin 3) L) (i j : Fin 3) :
    ‖((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ matrixSize h := by
  unfold matrixSize
  refine le_trans ?_ (Finset.single_le_sum
    (fun i' _ => Finset.sum_nonneg fun j' _ => add_norm_apply_nonneg h i' j') (Finset.mem_univ i))
  refine le_trans ?_ (Finset.single_le_sum (fun j' _ => add_norm_apply_nonneg h i j') (Finset.mem_univ j))
  exact le_add_of_nonneg_left (norm_nonneg _)

end Sizes

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Generic

variable {L : Type*} [NormedField L]

private theorem coe_matrixSupSize_mul_le (g h : GL (Fin 3) L) :
    ((matrixSupSize (g * h) : NNReal) : ℝ) ≤
      3 * ((matrixSupSize g : NNReal) : ℝ) * ((matrixSupSize h : NNReal) : ℝ) := by
  have hg3 : ∀ i : Fin 3,
      (∑ l : Fin 3, ‖(g : Matrix (Fin 3) (Fin 3) L) i l‖) ≤ 3 * ((matrixSupSize g : NNReal) : ℝ) := by
    intro i
    rw [Fin.sum_univ_three]
    linarith [norm_apply_le_matrixSupSize g i 0, norm_apply_le_matrixSupSize g i 1, norm_apply_le_matrixSupSize g i 2]
  have hg3' : ∀ j : Fin 3,
      (∑ l : Fin 3, ‖((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) l j‖) ≤
        3 * ((matrixSupSize g : NNReal) : ℝ) := by
    intro j
    rw [Fin.sum_univ_three]
    linarith [norm_inv_apply_le_matrixSupSize g 0 j, norm_inv_apply_le_matrixSupSize g 1 j,
      norm_inv_apply_le_matrixSupSize g 2 j]
  have hh0 : (0 : ℝ) ≤ ((matrixSupSize h : NNReal) : ℝ) := NNReal.coe_nonneg _
  have hB0 : (0 : ℝ) ≤ 3 * ((matrixSupSize g : NNReal) : ℝ) * ((matrixSupSize h : NNReal) : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) hh0
  refine matrixSupSize_le_of_forall_norm_le (g * h) hB0 (fun i j => ?_) (fun i j => ?_)
  · rw [Units.val_mul]
    calc ‖((g : Matrix (Fin 3) (Fin 3) L) * (h : Matrix (Fin 3) (Fin 3) L)) i j‖
        ≤ (∑ l : Fin 3, ‖(g : Matrix (Fin 3) (Fin 3) L) i l‖) * ((matrixSupSize h : NNReal) : ℝ) :=
          norm_mul_apply_le_sum_mul (g : Matrix (Fin 3) (Fin 3) L) (h : Matrix (Fin 3) (Fin 3) L)
            (norm_apply_le_matrixSupSize h) i j
      _ ≤ 3 * ((matrixSupSize g : NNReal) : ℝ) * ((matrixSupSize h : NNReal) : ℝ) :=
          mul_le_mul_of_nonneg_right (hg3 i) hh0
  · rw [_root_.mul_inv_rev, Units.val_mul]
    calc ‖(((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) * ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) i j‖
        ≤ ((matrixSupSize h : NNReal) : ℝ) * ∑ l : Fin 3, ‖((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) l j‖ :=
          norm_mul_apply_le_mul_sum ((h⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
            ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) (norm_inv_apply_le_matrixSupSize h) i j
      _ ≤ ((matrixSupSize h : NNReal) : ℝ) * (3 * ((matrixSupSize g : NNReal) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hg3' j) hh0
      _ = 3 * ((matrixSupSize g : NNReal) : ℝ) * ((matrixSupSize h : NNReal) : ℝ) := by ring

end Generic

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem valued_mul_apply_le3_left {C : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)} {i j : Fin 3} (ha : ∀ l, Valued.v (a i l) ≤ 1)
    (hb : ∀ l, Valued.v (b l j) ≤ C) : Valued.v ((a * b) i j) ≤ C := by
  have e : (a * b) i j = (b.transpose * a.transpose) j i := by
    rw [← Matrix.transpose_mul, Matrix.transpose_apply]
  rw [e]
  exact valued_mul_apply_le3 (𝓞 F) F v (fun l => by rw [Matrix.transpose_apply]; exact hb l)
    (fun l => by rw [Matrix.transpose_apply]; exact ha l)

private theorem coe_matrixSupSize_mul_le_of_mem_localMaximalCompact3 (g : GL (Fin 3) (v.adicCompletion F))
    {k : GL (Fin 3) (v.adicCompletion F)} (hk : k ∈ localMaximalCompact3 (𝓞 F) F v) :
    ((matrixSupSize (g * k) : NNReal) : ℝ) ≤ ((matrixSupSize g : NNReal) : ℝ) := by
  obtain ⟨hk1, hk2⟩ := (mem_localMaximalCompact3_iff (𝓞 F) F v).1 hk
  refine matrixSupSize_le_of_forall_norm_le (g * k) (NNReal.coe_nonneg _) (fun i j => ?_) (fun i j => ?_)
  · rw [Units.val_mul]
    obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ
      (fun l => Valued.v ((g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i l)) Finset.univ_nonempty
    have h1 : Valued.v (((g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) *
          (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion F))) i j) ≤
        Valued.v ((g : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i l₀) :=
      valued_mul_apply_le3 (𝓞 F) F v (fun l => hl₀ l (Finset.mem_univ l)) (fun l => hk1 l j)
    exact (Valued.toNormedField.norm_le_iff.2 h1).trans (norm_apply_le_matrixSupSize g i l₀)
  · rw [_root_.mul_inv_rev, Units.val_mul]
    obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ
      (fun l => Valued.v (((g⁻¹ : GL (Fin 3) (v.adicCompletion F)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) l j))
      Finset.univ_nonempty
    have h1 : Valued.v ((((k⁻¹ : GL (Fin 3) (v.adicCompletion F)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) *
          ((g⁻¹ : GL (Fin 3) (v.adicCompletion F)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion F))) i j) ≤
        Valued.v (((g⁻¹ : GL (Fin 3) (v.adicCompletion F)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) l₀ j) :=
      valued_mul_apply_le3_left (fun l => hk2 i l) (fun l => hl₀ l (Finset.mem_univ l))
    exact (Valued.toNormedField.norm_le_iff.2 h1).trans (norm_inv_apply_le_matrixSupSize g l₀ j)

private theorem coe_matrixSupSize_mul_of_mem_localMaximalCompact3 (g : GL (Fin 3) (v.adicCompletion F))
    {k : GL (Fin 3) (v.adicCompletion F)} (hk : k ∈ localMaximalCompact3 (𝓞 F) F v) :
    ((matrixSupSize (g * k) : NNReal) : ℝ) = ((matrixSupSize g : NNReal) : ℝ) := by
  refine le_antisymm (coe_matrixSupSize_mul_le_of_mem_localMaximalCompact3 g hk) ?_
  have h := coe_matrixSupSize_mul_le_of_mem_localMaximalCompact3 (g * k) ((localMaximalCompact3 (𝓞 F) F v).inv_mem hk)
  rwa [mul_inv_cancel_right] at h

end Local

section Finprod

variable {ι : Type*}

private theorem finprod_le_pow_card_mul_finprod (a b : ι → ℝ) (S : Finset ι) {K : ℝ} (hK : 1 ≤ K) (ha0 : ∀ p, 0 ≤ a p)
    (hb0 : ∀ p, 0 ≤ b p) (hS : ∀ p, p ∈ S → a p ≤ K * b p) (hout : ∀ p, p ∉ S → a p = b p) :
    ∏ᶠ p, a p ≤ K ^ S.card * ∏ᶠ p, b p := by
  classical
  by_cases hb : (Function.mulSupport b).Finite
  · have hbT : Function.mulSupport b ⊆ ↑(hb.toFinset ∪ S) := fun p hp =>
      Finset.mem_coe.2 (Finset.mem_union.2 (Or.inl (hb.mem_toFinset.2 hp)))
    have haT : Function.mulSupport a ⊆ ↑(hb.toFinset ∪ S) := by
      intro p hp
      refine Finset.mem_coe.2 (Finset.mem_union.2 ?_)
      by_cases hpS : p ∈ S
      · exact Or.inr hpS
      · refine Or.inl (hb.mem_toFinset.2 ?_)
        show b p ≠ 1
        rw [← hout p hpS]
        exact hp
    rw [finprod_eq_prod_of_mulSupport_subset a haT, finprod_eq_prod_of_mulSupport_subset b hbT]
    have hpt : ∀ p ∈ hb.toFinset ∪ S, a p ≤ (if p ∈ S then K else 1) * b p := by
      intro p _
      by_cases hpS : p ∈ S
      · rw [if_pos hpS]
        exact hS p hpS
      · rw [if_neg hpS, one_mul]
        exact (hout p hpS).le
    calc ∏ p ∈ hb.toFinset ∪ S, a p
        ≤ ∏ p ∈ hb.toFinset ∪ S, (if p ∈ S then K else 1) * b p := Finset.prod_le_prod (fun p _ => ha0 p) hpt
      _ = (∏ p ∈ hb.toFinset ∪ S, (if p ∈ S then K else 1)) * ∏ p ∈ hb.toFinset ∪ S, b p := Finset.prod_mul_distrib
      _ = K ^ ((hb.toFinset ∪ S) ∩ S).card * ∏ p ∈ hb.toFinset ∪ S, b p := by
          simp only [Finset.prod_ite_mem, Finset.prod_const]
      _ ≤ K ^ S.card * ∏ p ∈ hb.toFinset ∪ S, b p :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (Finset.card_le_card Finset.inter_subset_right))
            (Finset.prod_nonneg fun p _ => hb0 p)
  · have ha : ¬ (Function.mulSupport a).Finite := by
      intro ha
      refine hb ((ha.union S.finite_toSet).subset ?_)
      intro p hp
      by_cases hpS : p ∈ S
      · exact Or.inr (Finset.mem_coe.2 hpS)
      · refine Or.inl ?_
        show a p ≠ 1
        rw [hout p hpS]
        exact hp
    rw [finprod_of_infinite_mulSupport ha, finprod_of_infinite_mulSupport hb, mul_one]
    exact one_le_pow₀ hK

end Finprod

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem archGauge3_mul_of_archPlaceComponent3_eq_one (g h : AdelicGL 3 (𝓞 F) F)
    (harch : ∀ w : InfinitePlace F, archPlaceComponent3 F w h = 1) : archGauge3 F (g * h) = archGauge3 F g := by
  unfold archGauge3
  congr 1
  exact Finset.sum_congr rfl fun w _ => by rw [map_mul, harch w, mul_one]

private theorem finGauge3_mul_le_of_forall_mem_localMaximalCompact3 (g h : AdelicGL 3 (𝓞 F) F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) {B : ℝ}
    (hS : ∀ p, p ∈ S → ((matrixSupSize (componentAt3 (𝓞 F) F p h) : NNReal) : ℝ) ≤ B)
    (hout : ∀ p, p ∉ S → componentAt3 (𝓞 F) F p h ∈ localMaximalCompact3 (𝓞 F) F p) :
    finGauge3 F (g * h) ≤ max 1 (3 * B) ^ S.card * finGauge3 F g := by
  unfold finGauge3
  refine finprod_le_pow_card_mul_finprod _ _ S (le_max_left 1 (3 * B)) (fun p => NNReal.coe_nonneg _)
    (fun p => NNReal.coe_nonneg _) (fun p hp => ?_) (fun p hp => ?_)
  · show ((matrixSupSize (componentAt3 (𝓞 F) F p (g * h)) : NNReal) : ℝ) ≤
      max 1 (3 * B) * ((matrixSupSize (componentAt3 (𝓞 F) F p g) : NNReal) : ℝ)
    rw [map_mul]
    calc ((matrixSupSize (componentAt3 (𝓞 F) F p g * componentAt3 (𝓞 F) F p h) : NNReal) : ℝ)
        ≤ 3 * ((matrixSupSize (componentAt3 (𝓞 F) F p g) : NNReal) : ℝ) *
            ((matrixSupSize (componentAt3 (𝓞 F) F p h) : NNReal) : ℝ) := coe_matrixSupSize_mul_le _ _
      _ ≤ 3 * ((matrixSupSize (componentAt3 (𝓞 F) F p g) : NNReal) : ℝ) * B :=
          mul_le_mul_of_nonneg_left (hS p hp) (mul_nonneg (by norm_num) (NNReal.coe_nonneg _))
      _ = 3 * B * ((matrixSupSize (componentAt3 (𝓞 F) F p g) : NNReal) : ℝ) := by ring
      _ ≤ max 1 (3 * B) * ((matrixSupSize (componentAt3 (𝓞 F) F p g) : NNReal) : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (NNReal.coe_nonneg _)
  · show ((matrixSupSize (componentAt3 (𝓞 F) F p (g * h)) : NNReal) : ℝ) =
      ((matrixSupSize (componentAt3 (𝓞 F) F p g) : NNReal) : ℝ)
    rw [map_mul]
    exact coe_matrixSupSize_mul_of_mem_localMaximalCompact3 _ (hout p hp)

private theorem gauge3_mul_le_of_forall_mem_localMaximalCompact3 (g h : AdelicGL 3 (𝓞 F) F)
    (harch : ∀ w : InfinitePlace F, archPlaceComponent3 F w h = 1) (S : Finset (HeightOneSpectrum (𝓞 F))) {B : ℝ}
    (hS : ∀ p, p ∈ S → ((matrixSupSize (componentAt3 (𝓞 F) F p h) : NNReal) : ℝ) ≤ B)
    (hout : ∀ p, p ∉ S → componentAt3 (𝓞 F) F p h ∈ localMaximalCompact3 (𝓞 F) F p) :
    gauge3 F (g * h) ≤ max 1 (3 * B) ^ S.card * gauge3 F g := by
  have hK1 : (1 : ℝ) ≤ max 1 (3 * B) ^ S.card := one_le_pow₀ (le_max_left _ _)
  have hK0 : (0 : ℝ) ≤ max 1 (3 * B) ^ S.card := zero_le_one.trans hK1
  have hfin := finGauge3_mul_le_of_forall_mem_localMaximalCompact3 F g h S hS hout
  have harch0 : (0 : ℝ) ≤ archGauge3 F g := zero_le_one.trans (one_le_archGauge3 F g)
  unfold gauge3
  rw [archGauge3_mul_of_archPlaceComponent3_eq_one F g h harch]
  refine max_le ?_ ?_
  · calc (1 : ℝ) ≤ max 1 (3 * B) ^ S.card := hK1
      _ = max 1 (3 * B) ^ S.card * 1 := (mul_one _).symm
      _ ≤ max 1 (3 * B) ^ S.card * max 1 (archGauge3 F g * finGauge3 F g) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hK0
  · calc archGauge3 F g * finGauge3 F (g * h)
        ≤ archGauge3 F g * (max 1 (3 * B) ^ S.card * finGauge3 F g) := mul_le_mul_of_nonneg_left hfin harch0
      _ = max 1 (3 * B) ^ S.card * (archGauge3 F g * finGauge3 F g) := by ring
      _ ≤ max 1 (3 * B) ^ S.card * max 1 (archGauge3 F g * finGauge3 F g) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hK0

private theorem norm_apply_mul_le_of_forall_mem_localMaximalCompact3 {f : AdelicGL 3 (𝓞 F) F → ℂ} {C : ℝ} {N : ℕ}
    (hf : ∀ g, ‖f g‖ ≤ C * gauge3 F g ^ N) (hC : 0 ≤ C) (g h : AdelicGL 3 (𝓞 F) F)
    (harch : ∀ w : InfinitePlace F, archPlaceComponent3 F w h = 1) (S : Finset (HeightOneSpectrum (𝓞 F))) {B : ℝ}
    (hS : ∀ p, p ∈ S → ((matrixSupSize (componentAt3 (𝓞 F) F p h) : NNReal) : ℝ) ≤ B)
    (hout : ∀ p, p ∉ S → componentAt3 (𝓞 F) F p h ∈ localMaximalCompact3 (𝓞 F) F p) :
    ‖f (g * h)‖ ≤ C * (max 1 (3 * B) ^ S.card) ^ N * gauge3 F g ^ N := by
  calc ‖f (g * h)‖ ≤ C * gauge3 F (g * h) ^ N := hf _
    _ ≤ C * (max 1 (3 * B) ^ S.card * gauge3 F g) ^ N :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (gauge3_pos F _).le
            (gauge3_mul_le_of_forall_mem_localMaximalCompact3 F g h harch S hS hout) N) hC
    _ = C * (max 1 (3 * B) ^ S.card) ^ N * gauge3 F g ^ N := by rw [mul_pow, mul_assoc]

end Adelic

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem exists_algebraMap_eq_coe_principalSubgroup (q : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :
    ∃ r : ℚ, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r = (q : AdeleRing (𝓞 ℚ) ℚ) := by
  exact RingHom.mem_range.mp (Subring.mem_toAddSubgroup.mp q.2)

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  have h : (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ : Set (AdeleRing (𝓞 ℚ) ℚ)).Countable :=
    Set.Countable.mono (fun x hx => by simpa [Subring.mem_toAddSubgroup, RingHom.mem_range] using hx)
      (Set.countable_range (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))
  exact h.to_subtype

private theorem globalPointsGL_radicalP21 (v : Fin 2 → ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (radicalP21 v) = radicalP21 fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v i) :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [globalPointsGL, Matrix.GeneralLinearGroup.map_apply, radicalP21, upperUnipotent3]

private theorem globalPointsGL_radicalP12 (v : Fin 2 → ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (radicalP12 v) = radicalP12 fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (v i) :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [globalPointsGL, Matrix.GeneralLinearGroup.map_apply, radicalP12, upperUnipotent3]

private theorem radicalP21_algebraMap_add_left (r : ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ) :
    radicalP21 ![algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r + x, y] =
      globalPointsGL 3 (𝓞 ℚ) ℚ (radicalP21 ![r, 0]) * radicalP21 ![x, y] := by
  rw [globalPointsGL_radicalP21, ← radicalP21_add]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem radicalP21_algebraMap_add_right (r : ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ) :
    radicalP21 ![x, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r + y] =
      globalPointsGL 3 (𝓞 ℚ) ℚ (radicalP21 ![0, r]) * radicalP21 ![x, y] := by
  rw [globalPointsGL_radicalP21, ← radicalP21_add]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem radicalP12_algebraMap_add_left (r : ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ) :
    radicalP12 ![algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r + x, y] =
      globalPointsGL 3 (𝓞 ℚ) ℚ (radicalP12 ![r, 0]) * radicalP12 ![x, y] := by
  rw [globalPointsGL_radicalP12, ← radicalP12_add]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem radicalP12_algebraMap_add_right (r : ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ) :
    radicalP12 ![x, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r + y] =
      globalPointsGL 3 (𝓞 ℚ) ℚ (radicalP12 ![0, r]) * radicalP12 ![x, y] := by
  rw [globalPointsGL_radicalP12, ← radicalP12_add]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem integral_cond_eq_of_isAddFundamentalDomain {B B' : Set (AdeleRing (𝓞 ℚ) ℚ)}
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) B (adelicAddHaar (𝓞 ℚ) ℚ))
    (hB' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) B' (adelicAddHaar (𝓞 ℚ) ℚ))
    (f : AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hf : ∀ (q : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ),
      f ((q : AdeleRing (𝓞 ℚ) ℚ) + x) = f x) :
    ∫ x, f x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B) =
      ∫ x, f x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B') := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := countable_principalSubgroup
  simp only [ProbabilityTheory.cond, integral_smul_measure]
  rw [hB.measure_eq hB', hB.setIntegral_eq hB' (f := f) fun q x => hf q x]

private theorem integral₂_cond_eq_of_isAddFundamentalDomain {B B' : Set (AdeleRing (𝓞 ℚ) ℚ)}
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) B (adelicAddHaar (𝓞 ℚ) ℚ))
    (hB' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) B' (adelicAddHaar (𝓞 ℚ) ℚ))
    (φ : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ)
    (hx : ∀ (q : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ),
      φ ((q : AdeleRing (𝓞 ℚ) ℚ) + x) y = φ x y)
    (hy : ∀ (q : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ),
      φ x ((q : AdeleRing (𝓞 ℚ) ℚ) + y) = φ x y) :
    (∫ x, ∫ y, φ x y ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)) =
      ∫ x, ∫ y, φ x y ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B')
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B') := by
  have h1 : ∀ x, (∫ y, φ x y ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)) =
      ∫ y, φ x y ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B') :=
    fun x => integral_cond_eq_of_isAddFundamentalDomain hB hB' (φ x) fun q y => hy q x y
  simp_rw [h1]
  exact integral_cond_eq_of_isAddFundamentalDomain hB hB'
    (fun x => ∫ y, φ x y ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B')) fun q x => by simp only [hx]

private theorem isCuspidalAlongP21_productionPinsOf_congr (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    {B B' : Set (AdeleRing (𝓞 ℚ) ℚ)}
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) B (adelicAddHaar (𝓞 ℚ) ℚ))
    (hB' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) B' (adelicAddHaar (𝓞 ℚ) ℚ))
    {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hΦ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g) :
    IsCuspidalAlongP21 (productionPinsOf ℚ D U gen B) Φ ↔ IsCuspidalAlongP21 (productionPinsOf ℚ D U gen B') Φ := by
  show (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∫ x, ∫ y, Φ (radicalP21 ![x, y] * g)
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)) = 0) ↔
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∫ x, ∫ y, Φ (radicalP21 ![x, y] * g)
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B') ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B')) = 0
  refine forall_congr' fun g => ?_
  rw [integral₂_cond_eq_of_isAddFundamentalDomain hB hB' (fun x y => Φ (radicalP21 ![x, y] * g))]
  · intro q x y
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_coe_principalSubgroup q
    rw [← hr, radicalP21_algebraMap_add_left, mul_assoc, hΦ]
  · intro q x y
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_coe_principalSubgroup q
    rw [← hr, radicalP21_algebraMap_add_right, mul_assoc, hΦ]

private theorem isCuspidalAlongP12_productionPinsOf_congr (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    {B B' : Set (AdeleRing (𝓞 ℚ) ℚ)}
    (hB : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) B (adelicAddHaar (𝓞 ℚ) ℚ))
    (hB' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) B' (adelicAddHaar (𝓞 ℚ) ℚ))
    {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hΦ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g) :
    IsCuspidalAlongP12 (productionPinsOf ℚ D U gen B) Φ ↔ IsCuspidalAlongP12 (productionPinsOf ℚ D U gen B') Φ := by
  show (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∫ x, ∫ y, Φ (radicalP12 ![x, y] * g)
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)) = 0) ↔
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∫ x, ∫ y, Φ (radicalP12 ![x, y] * g)
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B') ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B')) = 0
  refine forall_congr' fun g => ?_
  rw [integral₂_cond_eq_of_isAddFundamentalDomain hB hB' (fun x y => Φ (radicalP12 ![x, y] * g))]
  · intro q x y
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_coe_principalSubgroup q
    rw [← hr, radicalP12_algebraMap_add_left, mul_assoc, hΦ]
  · intro q x y
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_coe_principalSubgroup q
    rw [← hr, radicalP12_algebraMap_add_right, mul_assoc, hΦ]

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem isAddFundamentalDomain_principalSubgroup_of_existsUnique {S : Set (AdeleRing (𝓞 ℚ) ℚ)}
    (hS : MeasurableSet S) (h : ∀ x : AdeleRing (𝓞 ℚ) ℚ, ∃! r : ℚ, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r + x ∈ S)
    (μ : Measure (AdeleRing (𝓞 ℚ) ℚ)) : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) S μ := by
  refine IsAddFundamentalDomain.mk' hS.nullMeasurableSet fun x => ?_
  obtain ⟨r, hr, huniq⟩ := h x
  refine ⟨⟨algebraMap ℚ _ r, r, rfl⟩, ?_, ?_⟩
  · show algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r + x ∈ S
    exact hr
  · rintro ⟨_, r', rfl⟩ hr'
    have : r' = r := huniq r' hr'
    subst this
    rfl

private theorem countable_principalSubgroup' : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  have h : (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ : Set (AdeleRing (𝓞 ℚ) ℚ)).Countable :=
    Set.Countable.mono (fun x hx => by simpa [Subring.mem_toAddSubgroup, RingHom.mem_range] using hx)
      (Set.countable_range (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))
  exact h.to_subtype

private def scaledBox (m : ℚ) : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  {x | algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) m⁻¹ * x ∈ adelicBox ℚ}

private theorem mem_scaledBox {m : ℚ} {x : AdeleRing (𝓞 ℚ) ℚ} :
    x ∈ scaledBox m ↔ algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) m⁻¹ * x ∈ adelicBox ℚ :=
  Iff.rfl

private theorem measurableSet_scaledBox (m : ℚ) : MeasurableSet (scaledBox m) :=
  (measurableSet_adelicBox ℚ).preimage (measurable_id.const_mul _)

private theorem existsUnique_algebraMap_add_mem_scaledBox {m : ℚ} (hm : m ≠ 0) (x : AdeleRing (𝓞 ℚ) ℚ) :
    ∃! r : ℚ, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r + x ∈ scaledBox m := by
  obtain ⟨r₀, hr₀, huniq⟩ :=
    existsUnique_algebraMap_add_mem_adelicBox ℚ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) m⁻¹ * x)
  have key : ∀ r : ℚ, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) r + x ∈ scaledBox m ↔
      algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (m⁻¹ * r) + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) m⁻¹ * x ∈ adelicBox ℚ := by
    intro r
    rw [mem_scaledBox, mul_add, map_mul]
  refine ⟨m * r₀, ?_, ?_⟩
  · show algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (m * r₀) + x ∈ scaledBox m
    rw [key, inv_mul_cancel_left₀ hm]
    exact hr₀
  · intro r hr
    have h : m⁻¹ * r = r₀ := huniq (m⁻¹ * r) ((key r).1 hr)
    rw [← h, mul_inv_cancel_left₀ hm]

private theorem isAddFundamentalDomain_scaledBox {m : ℚ} (hm : m ≠ 0) (μ : Measure (AdeleRing (𝓞 ℚ) ℚ)) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (scaledBox m) μ :=
  isAddFundamentalDomain_principalSubgroup_of_existsUnique (measurableSet_scaledBox m)
    (existsUnique_algebraMap_add_mem_scaledBox hm) μ

private theorem adelicAddHaar_scaledBox {m : ℚ} (hm : m ≠ 0) :
    adelicAddHaar (𝓞 ℚ) ℚ (scaledBox m) = adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  haveI := countable_principalSubgroup'
  exact (isAddFundamentalDomain_scaledBox hm _).measure_eq (isAddFundamentalDomain_adelicBox_adelicAddHaar ℚ)

private theorem adelicAddHaar_scaledBox_pos {m : ℚ} (hm : m ≠ 0) : 0 < adelicAddHaar (𝓞 ℚ) ℚ (scaledBox m) := by
  rw [adelicAddHaar_scaledBox hm]
  exact adelicAddHaar_adelicBox_pos ℚ

private theorem adelicAddHaar_scaledBox_lt_top {m : ℚ} (hm : m ≠ 0) : adelicAddHaar (𝓞 ℚ) ℚ (scaledBox m) < ⊤ := by
  rw [adelicAddHaar_scaledBox hm]
  exact adelicAddHaar_adelicBox_lt_top ℚ

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicHaar AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem isProbabilityMeasure_cond_adelicAddHaar {B : Set (AdeleRing (𝓞 ℚ) ℚ)} (hB0 : adelicAddHaar (𝓞 ℚ) ℚ B ≠ 0)
    (hBtop : adelicAddHaar (𝓞 ℚ) ℚ B ≠ ⊤) :
    IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite hB0 hBtop

private theorem ae_mem_cond_adelicAddHaar {B : Set (AdeleRing (𝓞 ℚ) ℚ)} (hBm : MeasurableSet B) :
    ∀ᵐ z ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B), z ∈ B := by
  show ∀ᵐ z ∂((adelicAddHaar (𝓞 ℚ) ℚ B)⁻¹ • (adelicAddHaar (𝓞 ℚ) ℚ).restrict B), z ∈ B
  exact MeasureTheory.Measure.ae_smul_measure (ae_restrict_mem hBm) _

private theorem norm_le_of_integral₂_cond_eq_zero {B : Set (AdeleRing (𝓞 ℚ) ℚ)} (hBm : MeasurableSet B)
    (hB0 : adelicAddHaar (𝓞 ℚ) ℚ B ≠ 0) (hBtop : adelicAddHaar (𝓞 ℚ) ℚ B ≠ ⊤)
    {φ : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ} {a : ℂ}
    (h0 : (∫ x, ∫ y, φ x y ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)) = 0)
    (hint : ∀ x, Integrable (φ x) (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
    (hint₂ : Integrable (fun x => ∫ y, φ x y ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
    {R : ℝ} (hR : ∀ x ∈ B, ∀ y ∈ B, ‖a - φ x y‖ ≤ R) : ‖a‖ ≤ R := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B) :=
    isProbabilityMeasure_cond_adelicAddHaar hB0 hBtop
  have hmem := ae_mem_cond_adelicAddHaar hBm
  have h1 : ∀ x, (∫ y, (a - φ x y) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)) =
      a - ∫ y, φ x y ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B) := fun x => by
    rw [integral_sub (integrable_const a) (hint x)]
    simp
  have hrep : a = ∫ x, ∫ y, (a - φ x y) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B) := by
    simp_rw [h1]
    rw [integral_sub (integrable_const a) hint₂, h0, sub_zero]
    simp
  have hinner : ∀ x ∈ B,
      ‖∫ y, (a - φ x y) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B)‖ ≤ R := fun x hx => by
    have h := norm_integral_le_of_norm_le_const (hmem.mono fun y hy => hR x hx y hy)
    simpa using h
  rw [hrep]
  have h := norm_integral_le_of_norm_le_const (hmem.mono fun x hx => hinner x hx)
  simpa using h

private theorem norm_le_of_isCuspidalAlongP21 (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) {B : Set (AdeleRing (𝓞 ℚ) ℚ)} (hBm : MeasurableSet B)
    (hB0 : adelicAddHaar (𝓞 ℚ) ℚ B ≠ 0) (hBtop : adelicAddHaar (𝓞 ℚ) ℚ B ≠ ⊤) {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hΦ : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen B) Φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hint : ∀ x, Integrable (fun y => Φ (radicalP21 ![x, y] * g)) (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
    (hint₂ : Integrable (fun x => ∫ y, Φ (radicalP21 ![x, y] * g) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
    {R : ℝ} (hR : ∀ x ∈ B, ∀ y ∈ B, ‖Φ g - Φ (radicalP21 ![x, y] * g)‖ ≤ R) : ‖Φ g‖ ≤ R :=
  norm_le_of_integral₂_cond_eq_zero hBm hB0 hBtop (φ := fun x y => Φ (radicalP21 ![x, y] * g)) (hΦ g) hint hint₂ hR

private theorem norm_le_of_isCuspidalAlongP12 (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) {B : Set (AdeleRing (𝓞 ℚ) ℚ)} (hBm : MeasurableSet B)
    (hB0 : adelicAddHaar (𝓞 ℚ) ℚ B ≠ 0) (hBtop : adelicAddHaar (𝓞 ℚ) ℚ B ≠ ⊤) {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hΦ : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen B) Φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hint : ∀ x, Integrable (fun y => Φ (radicalP12 ![x, y] * g)) (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
    (hint₂ : Integrable (fun x => ∫ y, Φ (radicalP12 ![x, y] * g) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) B))
    {R : ℝ} (hR : ∀ x ∈ B, ∀ y ∈ B, ‖Φ g - Φ (radicalP12 ![x, y] * g)‖ ≤ R) : ‖Φ g‖ ≤ R :=
  norm_le_of_integral₂_cond_eq_zero hBm hB0 hBtop (φ := fun x y => Φ (radicalP12 ![x, y] * g)) (hΦ g) hint hint₂ hR

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private def unitAdeles : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  {a | a.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ ∧ ∀ w : InfinitePlace ℚ, ‖a.1 w‖ ≤ 1}

private theorem isCompact_unitAdeles : IsCompact unitAdeles :=
  AutomorphicForm.isCompact_setOf_integral_and_norm_le_one ℚ

private def unitEntryMatrices : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {k | (∀ i j, (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j ∈ unitAdeles) ∧
    ∀ i j, ((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j ∈ unitAdeles}

private theorem isCompact_unitEntryMatrices : IsCompact unitEntryMatrices := by
  set C : Set (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := {m | ∀ i j, m i j ∈ unitAdeles} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => unitAdeles := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_unitAdeles
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : unitEntryMatrices = (Units.embedProduct (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C)) := by
    ext k
    simp only [unitEntryMatrices, hC_def, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
      Set.mem_prod, Set.mem_image, MulOpposite.op_inj, exists_eq_right]
  rw [heq]
  exact hK

private theorem snd_entry_mem_integralFiniteAdeles {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (i j : Fin 3) :
    ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  fun p => (hk p).1 i j

private theorem snd_entry_inv_mem_integralFiniteAdeles {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (i j : Fin 3) :
    (((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈
      AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  snd_entry_mem_integralFiniteAdeles
    (fun p => by rw [map_inv]; exact (localMaximalCompact3 (𝓞 ℚ) ℚ p).inv_mem (hk p)) i j

private theorem archPlaceComponent3_coe_apply (w : InfinitePlace ℚ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) i j =
      ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 w :=
  rfl

private theorem mem_unitEntryMatrices {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (harch : ∀ (w : InfinitePlace ℚ) (i j : Fin 3),
      ‖(archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ 1)
    (harch' : ∀ (w : InfinitePlace ℚ) (i j : Fin 3),
      ‖(archPlaceComponent3 ℚ w k⁻¹ : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ 1) :
    k ∈ unitEntryMatrices :=
  ⟨fun i j => ⟨snd_entry_mem_integralFiniteAdeles hfin i j, fun w => harch w i j⟩,
    fun i j => ⟨snd_entry_inv_mem_integralFiniteAdeles hfin i j, fun w => harch' w i j⟩⟩

private theorem setOf_maximalCompactClauses_subset :
    {k : AdelicGL 3 (𝓞 ℚ) ℚ |
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      (∀ (w : InfinitePlace ℚ) (i j : Fin 3),
        ‖(archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ 1) ∧
      ∀ (w : InfinitePlace ℚ) (i j : Fin 3),
        ‖(archPlaceComponent3 ℚ w k⁻¹ : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ 1} ⊆ unitEntryMatrices :=
  fun _ hk => mem_unitEntryMatrices hk.1 hk.2.1 hk.2.2

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem isCompact_setOf_norm_le_completion (w : InfinitePlace ℚ) (R : ℝ) :
    IsCompact {x : w.Completion | ‖x‖ ≤ R} := by
  have hiso := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have hce : Topology.IsClosedEmbedding (NumberField.InfinitePlace.Completion.extensionEmbedding w) :=
    hiso.isClosedEmbedding
  have hnorm : ∀ x : w.Completion, ‖NumberField.InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
    hiso.norm_map_of_map_zero (map_zero _)
  have heq : {x : w.Completion | ‖x‖ ≤ R} =
      (NumberField.InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, hnorm]
  rw [heq]
  exact hce.isCompact_preimage (isCompact_closedBall 0 R)

private def boundedAdeles (R : ℝ) : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  {a | a.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ ∧ ∀ w : InfinitePlace ℚ, ‖a.1 w‖ ≤ R}

private theorem boundedAdeles_mono {R R' : ℝ} (h : R ≤ R') : boundedAdeles R ⊆ boundedAdeles R' :=
  fun _ ha => ⟨ha.1, fun w => (ha.2 w).trans h⟩

private theorem isCompact_boundedAdeles (R : ℝ) : IsCompact (boundedAdeles R) := by
  have h : boundedAdeles R = (Set.pi Set.univ fun w : InfinitePlace ℚ => {x : w.Completion | ‖x‖ ≤ R}) ×ˢ
      AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
    ext a
    constructor
    · rintro ⟨h2, h1⟩
      exact ⟨Set.mem_univ_pi.mpr h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, Set.mem_univ_pi.mp h1⟩
  rw [h]
  exact (isCompact_univ_pi fun w => isCompact_setOf_norm_le_completion w R).prod
    (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 ℚ) ℚ)

private def boundedEntryMatrices (R : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {k | (∀ i j, (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j ∈ boundedAdeles R) ∧
    ∀ i j, ((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j ∈ boundedAdeles R}

private theorem boundedEntryMatrices_mono {R R' : ℝ} (h : R ≤ R') : boundedEntryMatrices R ⊆ boundedEntryMatrices R' :=
  fun _ hk => ⟨fun i j => boundedAdeles_mono h (hk.1 i j), fun i j => boundedAdeles_mono h (hk.2 i j)⟩

private theorem isCompact_boundedEntryMatrices (R : ℝ) : IsCompact (boundedEntryMatrices R) := by
  set C : Set (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := {m | ∀ i j, m i j ∈ boundedAdeles R} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => boundedAdeles R := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_boundedAdeles R
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : boundedEntryMatrices R = (Units.embedProduct (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C)) := by
    ext k
    simp only [boundedEntryMatrices, hC_def, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
      Set.mem_prod, Set.mem_image, MulOpposite.op_inj, exists_eq_right]
  rw [heq]
  exact hK

private theorem exists_isCompact_superset_of_forall_mem_boundedEntryMatrices {S : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} {R : ℝ}
    (hS : ∀ k ∈ S, k ∈ boundedEntryMatrices R) : ∃ T, IsCompact T ∧ S ⊆ T :=
  ⟨boundedEntryMatrices R, isCompact_boundedEntryMatrices R, hS⟩

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private def siegelSet (c C : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
    ∀ w : InfinitePlace ℚ,
      (∀ i j : Fin 3,
        (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
        (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
        ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
      (∀ i j : Fin 3, i ≠ j →
        (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
      c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
      (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1}

private def detSlab (a b : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

private def cappedSiegelSet (c d C : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
    (∀ w : InfinitePlace ℚ,
      (∀ i j : Fin 3,
        (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
        (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
        ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
      (∀ i j : Fin 3, i ≠ j →
        (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
      c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
      (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1) ∧
    ∀ w : InfinitePlace ℚ, archRoot₁ ℚ w t ≤ d ∧ archRoot₂ ℚ w t ≤ d}

private theorem cappedSiegelSet_subset (c d C : ℝ) : cappedSiegelSet c d C ⊆ siegelSet c C := by
  rintro g ⟨n, t, k, hg, hn, ht, hk, hw, -⟩
  exact ⟨n, t, k, hg, hn, ht, hk, hw⟩

private def siegelBlock (c d C a b : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  cappedSiegelSet c d C ∩ detSlab a b

private theorem siegelBlock_subset (c d C a b : ℝ) : siegelBlock c d C a b ⊆ siegelSet c C ∩ detSlab a b :=
  Set.inter_subset_inter_left _ (cappedSiegelSet_subset c d C)

private theorem siegelBlock_mono_slab {c d C a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    siegelBlock c d C a b ⊆ siegelBlock c d C a' b' := by
  rintro g ⟨hg, h₁, h₂⟩
  exact ⟨hg, ha.trans h₁, h₂.trans hb⟩

private theorem componentAt3_mul_mul_of_eq_one {n t : AdelicGL 3 (𝓞 ℚ) ℚ} (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hn : componentAt3 (𝓞 ℚ) ℚ p n = 1) (ht : componentAt3 (𝓞 ℚ) ℚ p t = 1) :
    componentAt3 (𝓞 ℚ) ℚ p (n * t * k) = componentAt3 (𝓞 ℚ) ℚ p k := by
  rw [map_mul, map_mul, hn, ht, one_mul, one_mul]

private theorem componentAt3_mem_localMaximalCompact3_of_mem_siegelSet {c C : ℝ} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : g ∈ siegelSet c C) (p : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  obtain ⟨n, t, k, rfl, hn, ht, hk, -⟩ := hg
  rw [componentAt3_mul_mul_of_eq_one k (hn p) (ht p)]
  exact hk p

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem snd_det_apply (g : AdelicGL 3 (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 p =
      ((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det := by
  have h := RingHom.map_det ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
    (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact h

private theorem snd_det_eq_one {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g = 1) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
  ext p
  rw [snd_det_apply, hg p, Units.val_one, Matrix.det_one]
  rfl

private theorem valued_det_le_one {p : HeightOneSpectrum (𝓞 ℚ)} {A : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) : Valued.v A.det ≤ 1 := by
  have hm : ∀ i₁ j₁ i₂ j₂ i₃ j₃ : Fin 3, Valued.v (A i₁ j₁ * A i₂ j₂ * A i₃ j₃) ≤ 1 := by
    intro i₁ j₁ i₂ j₂ i₃ j₃
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' (hA i₁ j₁) (hA i₂ j₂)) (hA i₃ j₃)
  rw [Matrix.det_fin_three]
  refine Valuation.map_sub_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _
    (Valuation.map_sub_le _ (hm _ _ _ _ _ _) (hm _ _ _ _ _ _)) (hm _ _ _ _ _ _)) (hm _ _ _ _ _ _)) (hm _ _ _ _ _ _))
    (hm _ _ _ _ _ _)

private theorem valued_det_le_one_of_mem_localMaximalCompact3 {p : HeightOneSpectrum (𝓞 ℚ)}
    {x : GL (Fin 3) (p.adicCompletion ℚ)} (hx : x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    Valued.v ((x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det) ≤ 1 ∧
      Valued.v (((x⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det) ≤ 1 :=
  ⟨valued_det_le_one hx.1, valued_det_le_one hx.2⟩

private theorem finitePartUnits_det_mem_unitIdeles {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det k) ∈
      FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ := by
  rw [FiniteAdeleRing.mem_unitIdeles_iff]
  refine ⟨fun p => ?_, fun p => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, NumberField.AdeleRing.val_finitePartUnits, snd_det_apply]
    exact (valued_det_le_one_of_mem_localMaximalCompact3 (hk p)).1
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← map_inv, ← map_inv,
      NumberField.AdeleRing.val_finitePartUnits, snd_det_apply, map_inv]
    exact (valued_det_le_one_of_mem_localMaximalCompact3 (hk p)).2

private theorem det_eq_one_of_unipotent {L : Type*} [CommRing L] {N : Matrix (Fin 3) (Fin 3) L}
    (hdiag : ∀ i, N i i = 1) (hlow : ∀ i j, j < i → N i j = 0) : N.det = 1 := by
  rw [Matrix.det_fin_three, hdiag 0, hdiag 1, hdiag 2, hlow 1 0 (by decide), hlow 2 0 (by decide),
    hlow 2 1 (by decide)]
  ring

private theorem norm_det_eq_one_of_transpose_mul_self {L : Type*} [NormedField L] {K : Matrix (Fin 3) (Fin 3) L}
    (hK : Kᵀ * K = 1) : ‖K.det‖ = 1 := by
  have h : K.det * K.det = 1 := by
    have := congrArg Matrix.det hK
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hn : ‖K.det‖ * ‖K.det‖ = 1 := by rw [← norm_mul, h, norm_one]
  exact (mul_self_eq_one_iff.1 hn).resolve_right fun h1 => by linarith [norm_nonneg K.det]

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem archPlaceComponent3_coe_eq (w : InfinitePlace ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (archPlaceComponent3 ℚ w g : Matrix (Fin 3) (Fin 3) w.Completion) =
      ((AdelicLevel.archEval ℚ w).comp (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)).mapMatrix
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rfl

private theorem fst_det_apply (g : AdelicGL 3 (𝓞 ℚ) ℚ) (w : InfinitePlace ℚ) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w =
      (archPlaceComponent3 ℚ w g : Matrix (Fin 3) (Fin 3) w.Completion).det := by
  rw [archPlaceComponent3_coe_eq, ← RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

private theorem prod_infinitePlace_rat_pow_mult (f : InfinitePlace ℚ → ℝ) (w₀ : InfinitePlace ℚ) :
    ∏ w : InfinitePlace ℚ, f w ^ w.mult = f w₀ := by
  have hm : ∀ w : InfinitePlace ℚ, w.mult = 1 := by
    intro w
    have hw : w.IsReal := by
      rw [Subsingleton.elim w Rat.infinitePlace]
      exact Rat.isReal_infinitePlace
    exact InfinitePlace.mult_isReal ⟨w, hw⟩
  rw [Fintype.prod_unique, hm, pow_one]
  exact congrArg f (Subsingleton.elim _ _)

private theorem norm_det_of_coe_eq_diagonal {L : Type*} [NormedField L] (t : Matrix.GeneralLinearGroup (Fin 3) L)
    (d : Fin 3 → Lˣ) (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) :
    ‖(t : Matrix (Fin 3) (Fin 3) L).det‖ = ‖(d 0 : L)‖ * ‖(d 1 : L)‖ * ‖(d 2 : L)‖ := by
  rw [ht, Matrix.det_diagonal, Fin.prod_univ_three, norm_mul, norm_mul]

private noncomputable def archPartIdele (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  NumberField.TateGlobal.archUnitHom Rat.infinitePlace
    (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 ℚ) ℚ Rat.infinitePlace x)

private theorem snd_archPartIdele (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((archPartIdele x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
  unfold archPartIdele
  rw [NumberField.TateGlobal.archUnitHom_apply]
  exact NumberField.AdelicVolume.archCentralUnit_snd _ _

private theorem fst_archPartIdele (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((archPartIdele x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace =
      (x : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace := by
  unfold archPartIdele
  rw [NumberField.TateGlobal.archUnitHom_apply, NumberField.AdelicVolume.archCentralUnit_fst_self]
  exact NumberField.AdeleRing.val_infiniteUnitsComponent _ _

private theorem finitePartUnits_archPartIdele (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ (archPartIdele x) = 1 := by
  apply Units.ext
  rw [NumberField.AdeleRing.val_finitePartUnits, Units.val_one]
  exact snd_archPartIdele x

private theorem fst_inv_archPartIdele_mul (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (((archPartIdele x)⁻¹ * x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
  have h : NumberField.AdeleRing.infiniteUnitsComponent (𝓞 ℚ) ℚ Rat.infinitePlace ((archPartIdele x)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    rw [NumberField.AdeleRing.val_infiniteUnitsComponent, NumberField.AdeleRing.val_infiniteUnitsComponent]
    exact fst_archPartIdele x
  have h' := congrArg Units.val h
  rw [NumberField.AdeleRing.val_infiniteUnitsComponent, Units.val_one] at h'
  funext w
  have hw : w = Rat.infinitePlace := Subsingleton.elim _ _
  subst hw
  exact h'

private theorem ideleNorm_eq_ideleNorm_archPartIdele_of_finitePartUnits_mem_unitIdeles (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hx : NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ x ∈ FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) :
    NumberField.TateGlobal.ideleNorm ℚ x = NumberField.TateGlobal.ideleNorm ℚ (archPartIdele x) := by
  have hfin : NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ ((archPartIdele x)⁻¹ * x) ∈
      FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ := by
    rwa [map_mul, map_inv, finitePartUnits_archPartIdele, inv_one, one_mul]
  have hone := NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ
    ((archPartIdele x)⁻¹ * x) (fst_inv_archPartIdele_mul x) hfin
  calc NumberField.TateGlobal.ideleNorm ℚ x
      = NumberField.TateGlobal.ideleNorm ℚ (archPartIdele x * ((archPartIdele x)⁻¹ * x)) := by
        rw [mul_inv_cancel_left]
    _ = NumberField.TateGlobal.ideleNorm ℚ (archPartIdele x) := by
        rw [NumberField.TateGlobal.ideleNorm_mul, hone, mul_one]

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem ideleNorm_eq_norm_of_snd_eq_one (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (ha : (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1) :
    NumberField.TateGlobal.ideleNorm ℚ a = ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace‖ := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one ℚ a ha]
  exact prod_infinitePlace_rat_pow_mult _ _

private theorem ideleNorm_det_of_componentAt3_eq_one {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g = 1) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) =
      ‖(archPlaceComponent3 ℚ Rat.infinitePlace g :
        Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion).det‖ := by
  rw [ideleNorm_eq_norm_of_snd_eq_one _ (snd_det_eq_one hg), fst_det_apply]

private theorem ideleNorm_det_eq_one_of_unipotent {n : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hn : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1)
    (hdiag : ∀ i : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1)
    (hlow : ∀ i j : Fin 3, j < i →
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det n) = 1 := by
  rw [ideleNorm_det_of_componentAt3_eq_one hn, det_eq_one_of_unipotent hdiag hlow, norm_one]

private theorem ideleNorm_det_of_coe_eq_diagonal {t : AdelicGL 3 (𝓞 ℚ) ℚ}
    (ht : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) (d : Fin 3 → Rat.infinitePlace.Completionˣ)
    (hd : (archPlaceComponent3 ℚ Rat.infinitePlace t : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) =
      Matrix.diagonal fun i => (d i : Rat.infinitePlace.Completion)) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det t) =
      ‖(d 0 : Rat.infinitePlace.Completion)‖ * ‖(d 1 : Rat.infinitePlace.Completion)‖ *
        ‖(d 2 : Rat.infinitePlace.Completion)‖ := by
  rw [ideleNorm_det_of_componentAt3_eq_one ht, norm_det_of_coe_eq_diagonal _ d hd]

private theorem ideleNorm_det_eq_one_of_mem_localMaximalCompact3_of_transpose_mul_self {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hK : (archPlaceComponent3 ℚ Rat.infinitePlace k :
        Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion).transpose *
      (archPlaceComponent3 ℚ Rat.infinitePlace k : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) = 1) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det k) = 1 := by
  rw [ideleNorm_eq_ideleNorm_archPartIdele_of_finitePartUnits_mem_unitIdeles _ (finitePartUnits_det_mem_unitIdeles hk),
    ideleNorm_eq_norm_of_snd_eq_one _ (snd_archPartIdele (Matrix.GeneralLinearGroup.det k)), fst_archPartIdele,
    fst_det_apply, norm_det_eq_one_of_transpose_mul_self hK]

private theorem ideleNorm_det_mul_mul_of_coe_eq_diagonal {n t k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hn : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1)
    (hdiag : ∀ i : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1)
    (hlow : ∀ i j : Fin 3, j < i →
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0)
    (ht : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) (d : Fin 3 → Rat.infinitePlace.Completionˣ)
    (hd : (archPlaceComponent3 ℚ Rat.infinitePlace t : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) =
      Matrix.diagonal fun i => (d i : Rat.infinitePlace.Completion))
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hK : (archPlaceComponent3 ℚ Rat.infinitePlace k :
        Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion).transpose *
      (archPlaceComponent3 ℚ Rat.infinitePlace k : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) = 1) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (n * t * k)) =
      ‖(d 0 : Rat.infinitePlace.Completion)‖ * ‖(d 1 : Rat.infinitePlace.Completion)‖ *
        ‖(d 2 : Rat.infinitePlace.Completion)‖ := by
  rw [map_mul, map_mul, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul,
    ideleNorm_det_eq_one_of_unipotent hn hdiag hlow, ideleNorm_det_of_coe_eq_diagonal ht d hd,
    ideleNorm_det_eq_one_of_mem_localMaximalCompact3_of_transpose_mul_self hk hK, one_mul, mul_one]

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Sizes

variable {L : Type*} [NormedField L]

private theorem lastRowEucl_of_coe_eq_diagonal (k : GL (Fin 3) L) (d : Fin 3 → Lˣ)
    (hk : (k : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) :
    lastRowEucl k = ‖(d 2 : L)‖ := by
  have h : lastRowEucl k = Real.sqrt (‖(d 2 : L)‖ ^ 2) := by
    simp [lastRowEucl, hk]
  rw [h, Real.sqrt_sq (norm_nonneg _)]

private theorem minorEucl_of_coe_eq_diagonal (k : GL (Fin 3) L) (d : Fin 3 → Lˣ)
    (hk : (k : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) :
    minorEucl k = ‖(d 1 : L)‖ * ‖(d 2 : L)‖ := by
  have h : minorEucl k = Real.sqrt ((‖(d 1 : L)‖ * ‖(d 2 : L)‖) ^ 2) := by
    simp [minorEucl, bottomMinor, hk, norm_mul]
  rw [h, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

private theorem detSize_of_coe_eq_diagonal (k : GL (Fin 3) L) (d : Fin 3 → Lˣ)
    (hk : (k : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) :
    detSize k = ‖(d 0 : L)‖ * ‖(d 1 : L)‖ * ‖(d 2 : L)‖ := by
  simp [detSize, hk, Matrix.det_diagonal, Fin.prod_univ_three, norm_mul]

private theorem root₁_eucl_of_coe_eq_diagonal (k : GL (Fin 3) L) (d : Fin 3 → Lˣ)
    (hk : (k : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) :
    detSize k * lastRowEucl k / minorEucl k ^ 2 = ‖(d 0 : L)‖ / ‖(d 1 : L)‖ := by
  have h1 : ‖(d 1 : L)‖ ≠ 0 := norm_ne_zero_iff.mpr (d 1).ne_zero
  have h2 : ‖(d 2 : L)‖ ≠ 0 := norm_ne_zero_iff.mpr (d 2).ne_zero
  rw [detSize_of_coe_eq_diagonal k d hk, lastRowEucl_of_coe_eq_diagonal k d hk,
    minorEucl_of_coe_eq_diagonal k d hk, div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero h1 h2)) h1]
  ring

private theorem root₂_eucl_of_coe_eq_diagonal (k : GL (Fin 3) L) (d : Fin 3 → Lˣ)
    (hk : (k : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal fun i => (d i : L)) :
    minorEucl k / lastRowEucl k ^ 2 = ‖(d 1 : L)‖ / ‖(d 2 : L)‖ := by
  have h2 : ‖(d 2 : L)‖ ≠ 0 := norm_ne_zero_iff.mpr (d 2).ne_zero
  rw [lastRowEucl_of_coe_eq_diagonal k d hk, minorEucl_of_coe_eq_diagonal k d hk, pow_two,
    mul_div_mul_right _ _ h2]

end Sizes

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem archRoot₁_of_coe_eq_diagonal (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) (d : Fin 3 → w.Completionˣ)
    (hg : (archPlaceComponent3 F w g : Matrix (Fin 3) (Fin 3) w.Completion) =
      Matrix.diagonal fun i => (d i : w.Completion)) :
    archRoot₁ F w g = ‖(d 0 : w.Completion)‖ / ‖(d 1 : w.Completion)‖ :=
  root₁_eucl_of_coe_eq_diagonal _ d hg

private theorem archRoot₂_of_coe_eq_diagonal (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) (d : Fin 3 → w.Completionˣ)
    (hg : (archPlaceComponent3 F w g : Matrix (Fin 3) (Fin 3) w.Completion) =
      Matrix.diagonal fun i => (d i : w.Completion)) :
    archRoot₂ F w g = ‖(d 1 : w.Completion)‖ / ‖(d 2 : w.Completion)‖ :=
  root₂_eucl_of_coe_eq_diagonal _ d hg

end Adelic

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem matrixSupSize_le_one_of_mem_localMaximalCompact3 {k : GL (Fin 3) (v.adicCompletion F)}
    (hk : k ∈ localMaximalCompact3 (𝓞 F) F v) : matrixSupSize k ≤ 1 := by
  obtain ⟨h1, h2⟩ := (mem_localMaximalCompact3_iff (𝓞 F) F v).1 hk
  unfold matrixSupSize
  refine Finset.sup_le fun ij _ => max_le ?_ ?_
  · rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact Valued.toNormedField.norm_le_one_iff.2 (h1 ij.1 ij.2)
  · rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
    exact Valued.toNormedField.norm_le_one_iff.2 (h2 ij.1 ij.2)

end Local

section Finprod

private theorem finprod_le_one_of_le_one {ι : Type*} (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) :
    ∏ᶠ i, f i ≤ 1 := by
  by_cases hf : (Function.mulSupport f).Finite
  · exact (finprod_eq_prod f hf).le.trans (Finset.prod_le_one (fun i _ => h0 i) fun i _ => h1 i)
  · exact (finprod_of_infinite_mulSupport hf).le

end Finprod

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem finGauge3_le_one_of_forall_mem_localMaximalCompact3 (g : AdelicGL 3 (𝓞 F) F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), componentAt3 (𝓞 F) F v g ∈ localMaximalCompact3 (𝓞 F) F v) :
    finGauge3 F g ≤ 1 := by
  unfold finGauge3
  refine finprod_le_one_of_le_one _ (fun v => NNReal.coe_nonneg _) fun v => ?_
  rw [← NNReal.coe_one, NNReal.coe_le_coe]
  exact matrixSupSize_le_one_of_mem_localMaximalCompact3 (hg v)

private theorem gauge3_le_archGauge3_of_forall_mem_localMaximalCompact3 (g : AdelicGL 3 (𝓞 F) F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), componentAt3 (𝓞 F) F v g ∈ localMaximalCompact3 (𝓞 F) F v) :
    gauge3 F g ≤ archGauge3 F g := by
  have hA : 1 ≤ archGauge3 F g := one_le_archGauge3 F g
  have hF := finGauge3_le_one_of_forall_mem_localMaximalCompact3 F g hg
  unfold gauge3
  refine max_le hA ?_
  calc archGauge3 F g * finGauge3 F g ≤ archGauge3 F g * 1 :=
        mul_le_mul_of_nonneg_left hF (zero_le_one.trans hA)
    _ = archGauge3 F g := mul_one _

end Adelic

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private noncomputable def blockEntryBound (c d C a b : ℝ) : ℝ :=
  9 * (windowBound c a b * (d * d * (d * d))) * (6 + 6 * C + C ^ 2)

private theorem windowBound_nonneg (c a b : ℝ) : 0 ≤ windowBound c a b := by
  unfold windowBound windowBoundK
  positivity

private theorem matrixSize_archPlaceComponent3_le_of_mem_siegelBlock {c d C a b : ℝ} (hc : 0 < c) (ha : 0 < a)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : g ∈ siegelBlock c d C a b) :
    matrixSize (archPlaceComponent3 ℚ Rat.infinitePlace g) ≤ blockEntryBound c d C a b := by
  obtain ⟨⟨n, t, k, rfl, hn, ht, hk, hw, hcap⟩, hslab⟩ := hg
  obtain ⟨hnw, htw, hr₁, hr₂, hK⟩ := hw Rat.infinitePlace
  obtain ⟨hcap₁, hcap₂⟩ := hcap Rat.infinitePlace

  have hdiag : ∀ i : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 :=
    fun i => (hnw i i).1
  have hlow : ∀ i j : Fin 3, j < i →
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0 :=
    fun i j hij => (hnw i j).2.1 hij
  have hnu := eq_upperUnipotent3_of_coe (archPlaceComponent3 ℚ Rat.infinitePlace n) hdiag hlow
  have hC : 0 ≤ C := by
    have h := (hnw 0 0).2.2
    rw [hdiag 0, norm_one] at h
    exact zero_le_one.trans h

  obtain ⟨e, he⟩ := exists_coe_eq_diagonal (archPlaceComponent3 ℚ Rat.infinitePlace t) htw
  rw [archRoot₁_of_coe_eq_diagonal ℚ Rat.infinitePlace t e he] at hr₁ hcap₁
  rw [archRoot₂_of_coe_eq_diagonal ℚ Rat.infinitePlace t e he] at hr₂ hcap₂
  obtain ⟨hwa, hwb⟩ : a ≤ ‖(e 0 : Rat.infinitePlace.Completion)‖ * ‖(e 1 : Rat.infinitePlace.Completion)‖ *
        ‖(e 2 : Rat.infinitePlace.Completion)‖ ∧
      ‖(e 0 : Rat.infinitePlace.Completion)‖ * ‖(e 1 : Rat.infinitePlace.Completion)‖ *
        ‖(e 2 : Rat.infinitePlace.Completion)‖ ≤ b := by
    rw [← ideleNorm_det_mul_mul_of_coe_eq_diagonal hn hdiag hlow ht e he hk hK]
    exact hslab

  have hkent := norm_apply_le_one_of_transpose_mul_self
    (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
    norm_eq_abs_ratRealCoordinate
    (archPlaceComponent3 ℚ Rat.infinitePlace k : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) hK
  have hkinv := norm_inv_apply_le_one_of_transpose_mul_self
    (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
    norm_eq_abs_ratRealCoordinate
    (archPlaceComponent3 ℚ Rat.infinitePlace k) hK

  have hsize := matrixSize_unipotent_mul_diagonal_mul_le hC hc ha (hnw 0 1).2.2 (hnw 1 2).2.2 (hnw 0 2).2.2
    (archPlaceComponent3 ℚ Rat.infinitePlace t) e he hr₁ hr₂ hwa hwb (archPlaceComponent3 ℚ Rat.infinitePlace k)
    hkent hkinv
  rw [← hnu] at hsize
  rw [map_mul, map_mul]
  refine hsize.trans ?_
  unfold blockEntryBound
  have hq₁ : 0 ≤ ‖(e 0 : Rat.infinitePlace.Completion)‖ / ‖(e 1 : Rat.infinitePlace.Completion)‖ := hc.le.trans hr₁
  have hq₂ : 0 ≤ ‖(e 1 : Rat.infinitePlace.Completion)‖ / ‖(e 2 : Rat.infinitePlace.Completion)‖ := hc.le.trans hr₂
  have hd : 0 ≤ d := hq₁.trans hcap₁
  have hp : ‖(e 0 : Rat.infinitePlace.Completion)‖ / ‖(e 1 : Rat.infinitePlace.Completion)‖ *
      (‖(e 1 : Rat.infinitePlace.Completion)‖ / ‖(e 2 : Rat.infinitePlace.Completion)‖) ≤ d * d :=
    mul_le_mul hcap₁ hcap₂ hq₂ hd
  have hpp := mul_le_mul hp hp (mul_nonneg hq₁ hq₂) (mul_nonneg hd hd)
  have hE : 0 ≤ 6 + 6 * C + C ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpp (windowBound_nonneg c a b)) (by norm_num)) hE

private theorem siegelBlock_subset_boundedEntryMatrices {c d C a b : ℝ} (hc : 0 < c) (ha : 0 < a) :
    siegelBlock c d C a b ⊆ boundedEntryMatrices (blockEntryBound c d C a b) := by
  intro g hg
  have hsize := matrixSize_archPlaceComponent3_le_of_mem_siegelBlock hc ha hg
  have hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p :=
    componentAt3_mem_localMaximalCompact3_of_mem_siegelSet (cappedSiegelSet_subset c d C hg.1)
  refine ⟨fun i j => ⟨snd_entry_mem_integralFiniteAdeles hfin i j, fun w => ?_⟩,
    fun i j => ⟨snd_entry_inv_mem_integralFiniteAdeles hfin i j, fun w => ?_⟩⟩
  · have hw : w = Rat.infinitePlace := Subsingleton.elim _ _
    subst hw
    rw [← archPlaceComponent3_coe_apply]
    exact (norm_apply_le_matrixSize _ i j).trans hsize
  · have hw : w = Rat.infinitePlace := Subsingleton.elim _ _
    subst hw
    rw [← archPlaceComponent3_coe_apply, map_inv]
    exact (norm_inv_apply_le_matrixSize _ i j).trans hsize

private theorem exists_isCompact_siegelBlock_subset {c d C a b : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∃ T : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact T ∧ siegelBlock c d C a b ⊆ T :=
  ⟨boundedEntryMatrices (blockEntryBound c d C a b), isCompact_boundedEntryMatrices _,
    siegelBlock_subset_boundedEntryMatrices hc ha⟩

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem componentAt3_inv_mul_mul_eq_one (s u : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hu : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p u = 1) (p : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (s⁻¹ * u * s) = 1 := by
  rw [map_mul, map_mul, hu p, mul_one, map_inv, inv_mul_cancel]

private theorem archPlaceComponent3_conj_radicalP21_bound {c C M' : ℝ} (hc : 0 < c) {n t k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hnw : ∀ i j : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 ∧
      (j < i →
        (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0) ∧
      ‖(archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j‖ ≤ C)
    (htw : ∀ i j : Fin 3, i ≠ j →
      (archPlaceComponent3 ℚ Rat.infinitePlace t : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0)
    (hr₁ : c ≤ archRoot₁ ℚ Rat.infinitePlace t)
    (hK : (archPlaceComponent3 ℚ Rat.infinitePlace k :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion).transpose *
        (archPlaceComponent3 ℚ Rat.infinitePlace k : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) = 1)
    (v : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)
    (hv : ∀ i : Fin 2, ‖AdelicLevel.archEval ℚ Rat.infinitePlace (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (v i))‖ ≤ M') :
    ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) *
        ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) = 0 ∧
      ∀ i j : Fin 3,
        ‖((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) i j‖ ≤
          2 * (1 + C) * max 1 c⁻¹ * M' / archRoot₂ ℚ Rat.infinitePlace t := by

  have hdiag : ∀ i : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 :=
    fun i => (hnw i i).1
  have hlow : ∀ i j : Fin 3, j < i →
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0 :=
    fun i j hij => (hnw i j).2.1 hij
  have hC : 0 ≤ C := (norm_nonneg _).trans (hnw 0 0).2.2
  have hM : 0 ≤ M' := (norm_nonneg _).trans (hv 0)
  have hnu := eq_upperUnipotent3_of_coe (archPlaceComponent3 ℚ Rat.infinitePlace n) hdiag hlow
  obtain ⟨d, hd⟩ := exists_coe_eq_diagonal (archPlaceComponent3 ℚ Rat.infinitePlace t) htw
  have hR₁ := archRoot₁_of_coe_eq_diagonal ℚ Rat.infinitePlace t d hd
  have hR₂ := archRoot₂_of_coe_eq_diagonal ℚ Rat.infinitePlace t d hd
  rw [hR₁] at hr₁

  have hk1 := norm_apply_le_one_of_transpose_mul_self _ norm_eq_abs_ratRealCoordinate _ hK
  have hk2 := norm_inv_apply_le_one_of_transpose_mul_self _ norm_eq_abs_ratRealCoordinate
    (archPlaceComponent3 ℚ Rat.infinitePlace k) hK

  have hb := conjDisplacement_radicalP21_bound
    ((archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) 0 1)
    ((archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) 1 2)
    ((archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) 0 2)
    (hnw 0 1).2.2 (archPlaceComponent3 ℚ Rat.infinitePlace t) d hd (archPlaceComponent3 ℚ Rat.infinitePlace k)
    hk1 hk2 (fun i => AdelicLevel.archEval ℚ Rat.infinitePlace (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (v i))) (hv 0) (hv 1)
  unfold conjDisplacement at hb

  have he : ∀ i : Fin 3, 0 < ‖(d i : Rat.infinitePlace.Completion)‖ := fun i => norm_pos_iff.mpr (d i).ne_zero
  have hc₀ := displacementBound_P21_le hC hc hM (he 0) (he 1) (he 2) hr₁

  simp only [map_mul, map_inv]
  rw [hnu, archPlaceComponent3_radicalP21, hR₂]
  exact ⟨hb.1, fun i j => (hb.2 i j).trans hc₀⟩

private theorem archPlaceComponent3_conj_radicalP12_bound {c C M' : ℝ} (hc : 0 < c) {n t k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hnw : ∀ i j : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 ∧
      (j < i →
        (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0) ∧
      ‖(archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j‖ ≤ C)
    (htw : ∀ i j : Fin 3, i ≠ j →
      (archPlaceComponent3 ℚ Rat.infinitePlace t : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0)
    (hr₂ : c ≤ archRoot₂ ℚ Rat.infinitePlace t)
    (hK : (archPlaceComponent3 ℚ Rat.infinitePlace k :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion).transpose *
        (archPlaceComponent3 ℚ Rat.infinitePlace k : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) = 1)
    (v : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)
    (hv : ∀ i : Fin 2, ‖AdelicLevel.archEval ℚ Rat.infinitePlace (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (v i))‖ ≤ M') :
    ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) *
        ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) = 0 ∧
      ∀ i j : Fin 3,
        ‖((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) i j‖ ≤
          2 * (1 + C) * max 1 c⁻¹ * M' / archRoot₁ ℚ Rat.infinitePlace t := by
  have hdiag : ∀ i : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 :=
    fun i => (hnw i i).1
  have hlow : ∀ i j : Fin 3, j < i →
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0 :=
    fun i j hij => (hnw i j).2.1 hij
  have hC : 0 ≤ C := (norm_nonneg _).trans (hnw 0 0).2.2
  have hM : 0 ≤ M' := (norm_nonneg _).trans (hv 0)
  have hnu := eq_upperUnipotent3_of_coe (archPlaceComponent3 ℚ Rat.infinitePlace n) hdiag hlow
  obtain ⟨d, hd⟩ := exists_coe_eq_diagonal (archPlaceComponent3 ℚ Rat.infinitePlace t) htw
  have hR₁ := archRoot₁_of_coe_eq_diagonal ℚ Rat.infinitePlace t d hd
  have hR₂ := archRoot₂_of_coe_eq_diagonal ℚ Rat.infinitePlace t d hd
  rw [hR₂] at hr₂
  have hk1 := norm_apply_le_one_of_transpose_mul_self _ norm_eq_abs_ratRealCoordinate _ hK
  have hk2 := norm_inv_apply_le_one_of_transpose_mul_self _ norm_eq_abs_ratRealCoordinate
    (archPlaceComponent3 ℚ Rat.infinitePlace k) hK
  have hb := conjDisplacement_radicalP12_bound
    ((archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) 0 1)
    ((archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) 1 2)
    ((archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) 0 2)
    (hnw 1 2).2.2 (archPlaceComponent3 ℚ Rat.infinitePlace t) d hd (archPlaceComponent3 ℚ Rat.infinitePlace k)
    hk1 hk2 (fun i => AdelicLevel.archEval ℚ Rat.infinitePlace (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (v i))) (hv 0) (hv 1)
  unfold conjDisplacement at hb
  have he : ∀ i : Fin 3, 0 < ‖(d i : Rat.infinitePlace.Completion)‖ := fun i => norm_pos_iff.mpr (d i).ne_zero
  have hc₀ := displacementBound_P12_le hC hc hM (he 0) (he 1) (he 2) hr₂
  simp only [map_mul, map_inv]
  rw [hnu, archPlaceComponent3_radicalP12, hR₁]
  exact ⟨hb.1, fun i j => (hb.2 i j).trans hc₀⟩

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL upperUnipotent3 radicalP21 radicalP12 radicalP21_add radicalP12_add valued_mul_apply_le3 localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN archComponentN componentAt3 archComponent3 IsCuspidalAlongP21 IsCuspidalAlongP12 archPlaceComponent3 matrixSize matrixSize_nonneg matrixSupSize archGauge3 finGauge3 gauge3 gauge3_pos one_le_archGauge3 bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private noncomputable def gaugeWindowConst (c C a b : ℝ) : ℝ :=
  9 * (6 + 6 * C + C ^ 2) * windowBound c a b + max 1 c⁻¹ ^ 4

private theorem gauge3_le_of_siegel_of_ideleNorm_det_mem_Icc {c C a b : ℝ} (hc : 0 < c) (ha0 : 0 < a)
    {n t k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hn : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1)
    (ht : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1)
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hnw : ∀ i j : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 ∧
      (j < i →
        (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0) ∧
      ‖(archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j‖ ≤ C)
    (htw : ∀ i j : Fin 3, i ≠ j →
      (archPlaceComponent3 ℚ Rat.infinitePlace t : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0)
    (hr₁ : c ≤ archRoot₁ ℚ Rat.infinitePlace t) (hr₂ : c ≤ archRoot₂ ℚ Rat.infinitePlace t)
    (hK : (archPlaceComponent3 ℚ Rat.infinitePlace k :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion).transpose *
        (archPlaceComponent3 ℚ Rat.infinitePlace k : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) = 1)
    (hwin : NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (n * t * k)) ∈ Set.Icc a b) :
    gauge3 ℚ (n * t * k) ≤
      gaugeWindowConst c C a b * (archRoot₁ ℚ Rat.infinitePlace t * archRoot₂ ℚ Rat.infinitePlace t) ^ 2 := by

  have hdiag : ∀ i : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 :=
    fun i => (hnw i i).1
  have hlow : ∀ i j : Fin 3, j < i →
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0 :=
    fun i j hij => (hnw i j).2.1 hij
  have hC : 0 ≤ C := (norm_nonneg _).trans (hnw 0 0).2.2
  have hnu := eq_upperUnipotent3_of_coe (archPlaceComponent3 ℚ Rat.infinitePlace n) hdiag hlow
  obtain ⟨d, hd⟩ := exists_coe_eq_diagonal (archPlaceComponent3 ℚ Rat.infinitePlace t) htw
  have hR₁ := archRoot₁_of_coe_eq_diagonal ℚ Rat.infinitePlace t d hd
  have hR₂ := archRoot₂_of_coe_eq_diagonal ℚ Rat.infinitePlace t d hd
  rw [hR₁] at hr₁
  rw [hR₂] at hr₂

  rw [ideleNorm_det_mul_mul_of_coe_eq_diagonal hn hdiag hlow ht d hd hk hK] at hwin
  obtain ⟨ha, hb⟩ := Set.mem_Icc.mp hwin

  have hk1 := norm_apply_le_one_of_transpose_mul_self _ norm_eq_abs_ratRealCoordinate _ hK
  have hk2 := norm_inv_apply_le_one_of_transpose_mul_self _ norm_eq_abs_ratRealCoordinate
    (archPlaceComponent3 ℚ Rat.infinitePlace k) hK

  have hm : matrixSize (archPlaceComponent3 ℚ Rat.infinitePlace (n * t * k)) ≤
      9 * (windowBound c a b *
          (‖(d 0 : Rat.infinitePlace.Completion)‖ / ‖(d 1 : Rat.infinitePlace.Completion)‖ *
              (‖(d 1 : Rat.infinitePlace.Completion)‖ / ‖(d 2 : Rat.infinitePlace.Completion)‖) *
            (‖(d 0 : Rat.infinitePlace.Completion)‖ / ‖(d 1 : Rat.infinitePlace.Completion)‖ *
              (‖(d 1 : Rat.infinitePlace.Completion)‖ / ‖(d 2 : Rat.infinitePlace.Completion)‖)))) *
        (6 + 6 * C + C ^ 2) := by
    rw [map_mul, map_mul, hnu]
    exact matrixSize_unipotent_mul_diagonal_mul_le hC hc ha0 (hnw 0 1).2.2 (hnw 1 2).2.2 (hnw 0 2).2.2 _ d hd hr₁
      hr₂ ha hb _ hk1 hk2

  have hfinK : ∀ p : HeightOneSpectrum (𝓞 ℚ),
      componentAt3 (𝓞 ℚ) ℚ p (n * t * k) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
    intro p
    rw [map_mul, map_mul, hn p, ht p, one_mul, one_mul]
    exact hk p
  have harch : archGauge3 ℚ (n * t * k) = 1 + matrixSize (archPlaceComponent3 ℚ Rat.infinitePlace (n * t * k)) := by
    unfold archGauge3
    rw [Fintype.sum_subsingleton _ Rat.infinitePlace]
  have hgauge := (gauge3_le_archGauge3_of_forall_mem_localMaximalCompact3 ℚ (n * t * k) hfinK).trans harch.le

  obtain ⟨hK1, hKc⟩ := window_one_le_K hc
  obtain ⟨hQ, -, -, -, -⟩ := window_Q_facts hc hK1 hKc hr₁ hr₂
  have hQQ := one_le_mul_of_one_le_of_one_le hQ hQ
  rw [hR₁, hR₂]
  unfold gaugeWindowConst
  linarith

end LanglandsTunnell.CubicInduction

open Matrix IsDedekindDomain NumberField AutomorphicForm
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel.LanglandsTunnell.CubicInduction"

theorem solution
    {c C M' : ℝ} (hc : 0 < c) {n t k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hnw : ∀ i j : Fin 3,
      (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i i = 1 ∧
      (j < i →
        (archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0) ∧
      ‖(archPlaceComponent3 ℚ Rat.infinitePlace n : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j‖ ≤ C)
    (htw : ∀ i j : Fin 3, i ≠ j →
      (archPlaceComponent3 ℚ Rat.infinitePlace t : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) i j = 0)
    (hr₁ : c ≤ archRoot₁ ℚ Rat.infinitePlace t) (hr₂ : c ≤ archRoot₂ ℚ Rat.infinitePlace t)
    (hK : (archPlaceComponent3 ℚ Rat.infinitePlace k :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion)ᵀ *
        (archPlaceComponent3 ℚ Rat.infinitePlace k : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) = 1)
    (v : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)
    (hv : ∀ i : Fin 2, ‖AdelicLevel.archEval ℚ Rat.infinitePlace (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (v i))‖ ≤ M') :
    (((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) *
          ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) = 0 ∧
        ∀ i j : Fin 3,
          ‖((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP21 v * (n * t * k)) :
              Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) i j‖ ≤
            2 * (1 + C) * max 1 c⁻¹ * M' / archRoot₂ ℚ Rat.infinitePlace t) ∧
    (((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) *
          ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
            Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) = 0 ∧
        ∀ i j : Fin 3,
          ‖((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * radicalP12 v * (n * t * k)) :
              Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) i j‖ ≤
            2 * (1 + C) * max 1 c⁻¹ * M' / archRoot₁ ℚ Rat.infinitePlace t) :=
  ⟨LanglandsTunnell.CubicInduction.archPlaceComponent3_conj_radicalP21_bound hc hnw htw hr₁ hK v hv,
    LanglandsTunnell.CubicInduction.archPlaceComponent3_conj_radicalP12_bound hc hnw htw hr₂ hK v hv⟩

end S_LanglandsTunnell_CubicInduction_conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel (solution)
