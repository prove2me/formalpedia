-- Prove2me | solution 1 for GlobalTheory.SS.FrobSub.Raises.of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:10.833011+00:00
-- url     : https://prove2.me/submissions/e69983ba-f6a9-4cf1-8edf-6be43646ae3f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGPowAndClosedSubgroup

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobSub
namespace GlobalTheory.SS.FrobSub
namespace Raises
theorem _root_.solution {X : Scheme.{0}} {φ : X ⟶ X} {a : ℕ} {U : X.Opens} {f : Γ(X, U)} {I : Type}
    (V : I → X.Opens) (hV : ∀ i, V i ≤ U) (hU : U ≤ iSup V)
    (h : ∀ i, Raises φ a (V i) ((X.presheaf.map (homOfLE (hV i)).op).hom f)) : Raises φ a U f := by
  have hU' : U = iSup V := le_antisymm hU (iSup_le hV)
  have e : U = φ ⁻¹ᵁ U := by
    rw [hU', Scheme.Hom.preimage_iSup]
    exact iSup_congr fun i => (h i).1
  refine ⟨e, ?_⟩
  refine X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hV i)) hU _ _ fun i => ?_
  obtain ⟨e', p⟩ := h i
  have k2 : φ.appLE U U e.le ≫ X.presheaf.map (homOfLE (hV i)).op =
      X.presheaf.map (homOfLE (hV i)).op ≫ φ.appLE _ _ e'.le := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have := congrArg (fun t => t.hom f) k2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.trans (p.trans (map_pow _ _ _).symm)
end Raises
end GlobalTheory.SS.FrobSub
