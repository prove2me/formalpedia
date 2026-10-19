-- Prove2me | solution 1 for OAI.EuclideanRamsey.sphere_field_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:09:09.503341+00:00
-- url     : https://prove2.me/submissions/14c6bd48-de94-43f0-8ae2-1ade622612f8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Quadratic.lean:L117-L166
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.sphere_field_quadratic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Quadratic

-- ---- from OAI.Combinatorics.EuclideanRamsey.Quadratic ----
namespace OAI

/-! Quadratic row independence gives a tensor lift and the Ramsey property. -/

noncomputable section
open scoped TensorProduct BigOperators RealInnerProductSpace Matrix

namespace EuclideanRamsey.Quadratic

end EuclideanRamsey.Quadratic

namespace EuclideanRamsey

theorem sphere_field_quadratic {s d : ℕ} (a : Fin s → Space d)
    (hsphere : ∃ c : Space d, ∃ r : ℝ, ∀ i, dist (a i) c = r) :
    ∃ h : QuadraticIndex d → Coeff a,
      augmentedQuadraticRows a *ᵥ h = 0 ∧
      ∀ j k : Fin d, h (some j, some k) = if j = k then 1 else 0 := by
  classical
  obtain ⟨c, r, hr⟩ := hsphere
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (Coeff a)
    (one_ne_zero : (1 : ℝ) ≠ 0)
  have hfix (x : Coeff a) : φ (x : ℝ) = x := by
    have ht := φ.map_smul x (1 : ℝ)
    simpa [Algebra.smul_def, hφ] using ht
  have hmul (x : Coeff a) (t : ℝ) : φ ((x : ℝ) * t) = x * φ t := by
    simpa [Algebra.smul_def] using φ.map_smul x t
  let C : ℝ := (∑ j, (c j)^2) - r^2
  let h : QuadraticIndex d → Coeff a := fun q =>
    match q.1, q.2 with
    | none, none => φ C
    | none, some j => φ (-2 * c j)
    | some _, none => 0
    | some j, some k => if j = k then 1 else 0
  refine ⟨h, ?_, fun _ _ => rfl⟩
  funext i
  have hreal : C + (∑ j, a i j * (-2 * c j)) + (∑ j, (a i j)^2) = 0 := by
    have hdist : (∑ j, (a i j - c j)^2) = r^2 := by
      calc
        (∑ j, (a i j - c j)^2) = dist (a i) c ^ 2 := by
          simpa only [Real.dist_eq, sq_abs] using
            (EuclideanSpace.dist_sq_eq (a i) c).symm
        _ = r^2 := congrArg (fun x : ℝ => x^2) (hr i)
    have hexpand : (∑ j, (a i j - c j)^2) =
        (∑ j, (a i j)^2) + (∑ j, a i j * (-2*c j)) + (∑ j, (c j)^2) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    dsimp [C]
    linarith
  have hdesc := congrArg φ hreal
  simp only [map_add, map_sum, map_zero] at hdesc
  have hlinear (j : Fin d) : φ (a i j * (-2*c j)) =
      coordinate a i j * φ (-2*c j) := hmul (coordinate a i j) _
  have hsquare (j : Fin d) : φ ((a i j)^2) = (coordinate a i j)^2 := by
    change φ (((coordinate a i j)^2 : Coeff a) : ℝ) = (coordinate a i j)^2
    exact hfix _
  simp only [hlinear, hsquare] at hdesc
  change (∑ q : QuadraticIndex d, augmentedQuadraticRows a i q * h q) = 0
  simpa [augmentedQuadraticRows, Fintype.sum_prod_type, Fintype.sum_option,
    augmented, h, mul_ite, ite_mul, pow_two, mul_comm, mul_left_comm,
    mul_assoc] using hdesc

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct BigOperators RealInnerProductSpace Matrix


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.sphere_field_quadratic := @_root_.OAI.EuclideanRamsey.sphere_field_quadratic
