-- Prove2me | solution 1 for GlobalTheory.SS.StalkDer.gmDual_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:20:35.896203+00:00
-- url     : https://prove2.me/submissions/62709c51-3fca-4a6a-866d-c49ac24ac4c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Theorems.Thm_GlobalTheory_SS_StalkDer_germ_appLE

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}
namespace GlobalTheory.SS.StalkDer
theorem _root_.solution (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V)
    (c : Γ(Sp K, ⊤)) :
    gmDual D f z V hz ((X.hom.appLE ⊤ V le_top).hom c) =
      TrivSqZeroExt.inl ((P.presheaf.germ ⊤ z trivial).hom (((f ≫ X.hom).appLE ⊤ ⊤ le_top).hom c)) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show gm f z V hz _ = (P.presheaf.germ ⊤ z trivial).hom _
    rw [← germ_appLE f z V _ le_rfl hz,
      ← TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)) z hz]
    congr 1
    have e1 := Scheme.Hom.appLE_comp_appLE f X.hom ⊤ V (f ⁻¹ᵁ V) le_top le_rfl
    have e2 := (f ≫ X.hom).appLE_map (U := ⊤) (V := ⊤) le_top (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op
    exact congrArg (fun φ => φ.hom c) (e1.trans e2.symm)
  · show gm f z V hz (D.D V _) = 0
    have e : (X.hom.appLE ⊤ V le_top).hom c =
        cstK X V ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom c) := by
      show _ = (X.hom.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom _)
      congr 1
      exact (congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id).symm
    rw [e, D.const, map_zero]
end GlobalTheory.SS.StalkDer
