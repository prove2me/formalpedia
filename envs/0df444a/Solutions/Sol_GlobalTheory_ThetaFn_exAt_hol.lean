-- Prove2me | solution 1 for GlobalTheory.ThetaFn.exAt_hol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:01:27.474557+00:00
-- url     : https://prove2.me/submissions/ce840398-f7c3-47f3-9254-83fcc934e461

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Theorems.Thm_GlobalTheory_ThetaFn_ex_fibreIncl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
namespace GlobalTheory.ThetaFn
theorem _root_.solution (U : (T ⊗ A).left.Opens) (f : Γ((T ⊗ A).left, U)) :
    IsOpen {z | ⊤ ≤ exAt u p z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (exAt u p z) U f) {z | ⊤ ≤ exAt u p z ⁻¹ᵁ U} := by
  have h := u.hol ((fibreIncl A p).left ⁻¹ᵁ U) (((fibreIncl A p).left.app U).hom f)
  simp only [← ex_fibreIncl]
  refine ⟨h.1, h.2.congr fun z _ => ?_⟩
  exact (valAt'_app (u.ex z).left (fibreIncl A p).left U f).symm
end GlobalTheory.ThetaFn
