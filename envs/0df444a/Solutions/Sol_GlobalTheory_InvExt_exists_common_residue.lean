-- Prove2me | solution 1 for GlobalTheory.InvExt.exists_common_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:56.752953+00:00
-- url     : https://prove2.me/submissions/104859e9-f5d1-4e0f-addf-cce768b25efb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
import Theorems.Thm_GlobalTheory_InvExt_exists_common
import Theorems.Thm_GlobalTheory_InvExt_rPt_apply
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.InvExt
variable (C : Core)
variable {C}
namespace GlobalTheory.InvExt
theorem _root_.solution {X : Scheme.{0}} {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (α : Sp (OO p) ⟶ X) (β : Sp (OO q) ⟶ X) (h : α (cPt p) = β (cPt q)) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (v : Sp K ⟶ Sp (kb p)) (v' : Sp K ⟶ Sp (kb q)),
      v ≫ rPt p ≫ α = v' ≫ rPt q ≫ β := by
  obtain ⟨x⟩ : Nonempty (Sp (kb p)) := inferInstance
  obtain ⟨x'⟩ : Nonempty (Sp (kb q)) := inferInstance
  refine exists_common _ _ x x' ?_
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, rPt_apply, rPt_apply, h]
end GlobalTheory.InvExt
