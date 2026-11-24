-- Prove2me | solution 1 for GlobalTheory.VVRank.exists_gen_pullTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:07:09.462387+00:00
-- url     : https://prove2.me/submissions/5559975c-b8ae-4a11-aa03-0cdd94aaab3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_pullGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.VVRank
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J),
      Good L z J → val t' r z J = val t (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨LB.pullGen L φ ε t h, LB.isGen_pullGen L φ ε t ht h, fun Z r z J hJ => val_pull hJ t h r⟩
end GlobalTheory.VVRank
