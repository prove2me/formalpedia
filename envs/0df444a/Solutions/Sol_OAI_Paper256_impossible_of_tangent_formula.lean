-- Prove2me | solution 1 for OAI.Paper256.impossible_of_tangent_formula
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:07:12.691877+00:00
-- url     : https://prove2.me/submissions/5a0a94e4-16e2-4122-abca-9b1644cfd8a7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/TangentRigidity.lean:L14-L45
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.impossible_of_tangent_formula. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic
import Theorems.Thm_OAI_Paper256_tangent_coordinates_isomorphism

-- ---- from OAI.Analysis.HyperbolicCones.FormBasic ----
namespace OAI

/-! Exact identities for the Choi–Lam form. -/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem choiLam_expand {R : Type u} [CommRing R] (z y : Fin 3 → R) :
    choiLam z y =
      z 0 ^ 2 * y 0 ^ 2 + z 1 ^ 2 * y 1 ^ 2 + z 2 ^ 2 * y 2 ^ 2 -
      2 * (z 0 * y 0 * z 1 * y 1 + z 0 * y 0 * z 2 * y 2 +
        z 1 * y 1 * z 2 * y 2) +
      (z 0 ^ 2 * y 1 ^ 2 + z 1 ^ 2 * y 2 ^ 2 + z 2 ^ 2 * y 0 ^ 2) := by
  simp [choiLam, Fin.sum_univ_succ]
  ring

theorem choiLam_nonzero :
    choiLam (![1, 0, 0] : Fin 3 → ℝ) (![1, 0, 0] : Fin 3 → ℝ) = 1 := by
  simp [choiLam_expand, Matrix.cons_val]

theorem choiLam_cyclic_zero (i : Fin 3) :
    choiLam (Pi.single i 1 : Fin 3 → ℝ) (Pi.single (i + 2) 1) = 0 := by
  fin_cases i <;> simp [choiLam_expand, Fin.reduceAdd, Fin.reduceEq]

theorem choiLam_curve (i : Fin 3) (s : ℝ) :
    choiLam ((Pi.single i 1 : Fin 3 → ℝ) + s • Pi.single (i + 2) 1)
      (Pi.single (i + 2) 1 + s • Pi.single i 1) = s ^ 4 := by
  fin_cases i <;> simp [choiLam_expand, Fin.reduceAdd, Fin.reduceEq] <;> ring

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.OperatorEntries ----
namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem operatorNorm_eq_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    operatorNorm A = ‖A‖ := rfl

theorem abs_entry_le_operatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) : |A i j| ≤ operatorNorm A := by
  let f := A.toEuclideanLin.toContinuousLinearMap
  have he : f (PiLp.single 2 j 1) i = A i j := by
    simp [f, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_single]
  have h₁ := PiLp.norm_apply_le (f (PiLp.single 2 j 1)) i
  have h₂ := f.unit_le_opNorm (PiLp.single 2 j 1)
    (by rw [PiLp.norm_single]; norm_num : ‖(PiLp.single 2 j (1 : ℝ) : Vec n)‖ ≤ 1)
  simpa only [he, Real.norm_eq_abs] using! h₁.trans h₂

theorem entry_sq_le_operatorNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) : (A i j) ^ 2 ≤ operatorNorm A ^ 2 := by
  have h := abs_entry_le_operatorNorm A i j
  have hn : 0 ≤ operatorNorm A := norm_nonneg _
  nlinarith [sq_abs (A i j), abs_nonneg (A i j)]

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.FormRigidity ----
namespace OAI

/-! A bilinear square dominated by the Choi--Lam form vanishes. -/

noncomputable section

open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem form_linear_coordinates {W : Type u} [AddCommGroup W] [Module ℝ W]
    (f : (Fin 3 → ℝ) →ₗ[ℝ] W) (x : Fin 3 → ℝ) :
    f x = ∑ i, x i • f (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin 3 → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp

theorem form_bilinear_coordinates
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (z y : Fin 3 → ℝ) :
    l z y = ∑ i, ∑ j, (z i * y j) * l (Pi.single i 1) (Pi.single j 1) := by
  rw [form_linear_coordinates l z]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [form_linear_coordinates (l (Pi.single i 1)) y]
  simp [Finset.mul_sum, mul_assoc]

theorem dominated_form_vanishes_at_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y)
    (z y : Fin 3 → ℝ) (hz : choiLam z y = 0) : l z y = 0 := by
  have hh := h z y
  rw [hz] at hh
  nlinarith [sq_nonneg (l z y)]

theorem dominated_form_cyclic_coefficient
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i : Fin 3) :
    l (Pi.single i 1) (Pi.single (i + 2) 1) = 0 :=
  dominated_form_vanishes_at_zero l h _ _ (choiLam_cyclic_zero i)

theorem dominated_form_symmetric_coefficients
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) :
    (l (Pi.single 0 1) (Pi.single 1 1) + l (Pi.single 1 1) (Pi.single 0 1) = 0) ∧
    (l (Pi.single 0 1) (Pi.single 2 1) + l (Pi.single 2 1) (Pi.single 0 1) = 0) ∧
    (l (Pi.single 1 1) (Pi.single 2 1) + l (Pi.single 2 1) (Pi.single 1 1) = 0) := by
  have h0 := dominated_form_vanishes_at_zero l h ![1, 1, 1] ![1, 1, 1]
    (by simp [choiLam_expand, Matrix.cons_val]; norm_num)
  have h1 := dominated_form_vanishes_at_zero l h ![1, 1, -1] ![1, 1, -1]
    (by simp [choiLam_expand, Matrix.cons_val]; norm_num)
  have h2 := dominated_form_vanishes_at_zero l h ![1, -1, 1] ![1, -1, 1]
    (by simp [choiLam_expand, Matrix.cons_val]; norm_num)
  have h3 := dominated_form_vanishes_at_zero l h ![-1, 1, 1] ![-1, 1, 1]
    (by simp [choiLam_expand, Matrix.cons_val]; norm_num)
  rw [form_bilinear_coordinates] at h0 h1 h2 h3
  simp [Fin.sum_univ_succ] at h0 h1 h2 h3
  constructor
  · linarith
  constructor <;> linarith

theorem dominated_form_off_diagonal
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i j : Fin 3) (hij : i ≠ j) :
    l (Pi.single i 1) (Pi.single j 1) = 0 := by
  obtain ⟨h01, h02, h12⟩ := dominated_form_symmetric_coefficients l h
  have h20 := dominated_form_cyclic_coefficient l h 0
  have h10 := dominated_form_cyclic_coefficient l h 1
  have h21 := dominated_form_cyclic_coefficient l h 2
  simp only [Fin.reduceAdd] at h20 h10 h21
  fin_cases i <;> fin_cases j <;> simp_all [Fin.reduceEq]

theorem form_curve_of_off_diagonal
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (hoff : ∀ i j : Fin 3, i ≠ j → l (Pi.single i 1) (Pi.single j 1) = 0)
    (i : Fin 3) (s : ℝ) :
    l ((Pi.single i 1 : Fin 3 → ℝ) + s • Pi.single (i + 2) 1)
      (Pi.single (i + 2) 1 + s • Pi.single i 1) =
      s * (l (Pi.single i 1) (Pi.single i 1) +
        l (Pi.single (i + 2) 1) (Pi.single (i + 2) 1)) := by
  have hi : i ≠ i + 2 := by fin_cases i <;> decide
  simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hoff i (i + 2) hi, hoff (i + 2) i hi.symm]
  ring

theorem dominated_form_diagonal_pair_bound
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i : Fin 3) (s : ℝ) (hs : s ≠ 0) :
    (l (Pi.single i 1) (Pi.single i 1) +
      l (Pi.single (i + 2) 1) (Pi.single (i + 2) 1)) ^ 2 ≤ s ^ 2 := by
  have hh := h ((Pi.single i 1 : Fin 3 → ℝ) + s • Pi.single (i + 2) 1)
    (Pi.single (i + 2) 1 + s • Pi.single i 1)
  rw [choiLam_curve, form_curve_of_off_diagonal l (dominated_form_off_diagonal l h)] at hh
  apply le_of_mul_le_mul_left (a := s ^ 2) _ (sq_pos_of_ne_zero hs)
  nlinarith only [hh]

theorem dominated_form_diagonal_pair_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i : Fin 3) :
    l (Pi.single i 1) (Pi.single i 1) +
      l (Pi.single (i + 2) 1) (Pi.single (i + 2) 1) = 0 := by
  let c := l (Pi.single i 1) (Pi.single i 1) +
    l (Pi.single (i + 2) 1) (Pi.single (i + 2) 1)
  change c = 0
  by_contra hc
  have hh := dominated_form_diagonal_pair_bound l h i (c / 2) (div_ne_zero hc (by norm_num))
  change c ^ 2 ≤ (c / 2) ^ 2 at hh
  nlinarith [sq_pos_of_ne_zero hc]

theorem dominated_form_diagonal_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i : Fin 3) :
    l (Pi.single i 1) (Pi.single i 1) = 0 := by
  have h0 := dominated_form_diagonal_pair_zero l h 0
  have h1 := dominated_form_diagonal_pair_zero l h 1
  have h2 := dominated_form_diagonal_pair_zero l h 2
  simp only [Fin.reduceAdd] at h0 h1 h2
  fin_cases i <;> simp only [Fin.reduceFinMk] <;> linarith

theorem dominated_form_coefficient_zero
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) (i j : Fin 3) :
    l (Pi.single i 1) (Pi.single j 1) = 0 := by
  by_cases hij : i = j
  · subst j
    exact dominated_form_diagonal_zero l h i
  · exact dominated_form_off_diagonal l h i j hij

theorem choiLam_no_dominated_square
    (l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ z y, (l z y) ^ 2 ≤ choiLam z y) : l = 0 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro y
  change l z y = 0
  rw [form_bilinear_coordinates]
  simp [dominated_form_coefficient_zero l h]

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.TangentRigidity ----
namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

namespace Paper256

theorem impossible_of_tangent_formula (P : NormalizedPencil)
    (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat P.c ℝ)
    (hv : ‖v‖ = 1) (hv0 : v 0 ≠ 0)
    (hformula : ∀ h : Vec 4, inner ℝ v h = 0 → ∀ y : Fin 3 → ℝ,
      choiLam (wedgeCoordinates v h) y =
        operatorNorm (P.leftProjection v * P.B y * T h) ^ 2) : False := by
  obtain ⟨J, hJ⟩ := tangent_coordinates_isomorphism v hv hv0
  let D : (Fin 3 → ℝ) →ₗ[ℝ] Mat P.c ℝ :=
    T.comp ((tangentSpace v).subtype.comp J.symm.toLinearMap)
  let C : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin P.a) (Fin P.c) ℝ :=
    (mulLeftLinearMap (Fin P.c) ℝ (P.leftProjection v)).comp P.B
  let b : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin P.a) (Fin P.c) ℝ :=
    (mulLinearMap ℝ).flip.compl₁₂ D C
  have hb (z y : Fin 3 → ℝ) : choiLam z y = operatorNorm (b z y) ^ 2 := by
    have ht : inner ℝ v (J.symm z).val = 0 := (J.symm z).property
    have hj : wedgeCoordinates v (J.symm z).val = z := by
      rw [← hJ, J.apply_symm_apply]
    change choiLam z y = operatorNorm (P.leftProjection v * P.B y * T (J.symm z).val) ^ 2
    simpa only [hj] using hformula (J.symm z).val ht y
  have hz (z y : Fin 3 → ℝ) : b z y = 0 := by
    ext i j
    let l : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
      b.compr₂ (Matrix.entryLinearMap ℝ ℝ i j)
    have hl : l = 0 := choiLam_no_dominated_square l (fun z y => by
      change (b z y i j) ^ 2 ≤ choiLam z y
      rw [hb]
      exact entry_sq_le_operatorNorm_sq (b z y) i j)
    have he := LinearMap.congr_fun (LinearMap.congr_fun hl z) y
    exact he
  have hc := hb ![1, 0, 0] ![1, 0, 0]
  rw [choiLam_nonzero, hz, operatorNorm_eq_norm, norm_zero, zero_pow (by decide)] at hc
  exact one_ne_zero hc

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix


theorem solution : type_of% @_root_.OAI.Paper256.impossible_of_tangent_formula := @_root_.OAI.Paper256.impossible_of_tangent_formula
