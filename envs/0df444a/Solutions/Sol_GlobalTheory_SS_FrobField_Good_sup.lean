-- Prove2me | solution 1 for GlobalTheory.SS.FrobField.Good.sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:45.881328+00:00
-- url     : https://prove2.me/submissions/ad14f2fd-01c2-4104-99d9-951ebd6e228d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField
namespace GlobalTheory.SS.FrobField
namespace Good
theorem _root_.solution {X : Scheme.{0}} {F : End X} {q : ℕ} {U V W : X.Opens} (f : Γ(X, W))
    (hU : U ≤ W) (hV : V ≤ W) (hW : W = U ⊔ V)
    (a : Good F q U ((X.presheaf.map (homOfLE hU).op).hom f))
    (b : Good F q V ((X.presheaf.map (homOfLE hV).op).hom f)) : Good F q W f := by
  obtain ⟨m, hm, ⟨h, e⟩, ⟨h', e'⟩⟩ := a.two b
  have hh : W = (show X ⟶ X from F ^ m) ⁻¹ᵁ W := by
    rw [hW, Scheme.Hom.preimage_sup, ← h, ← h']
  refine ⟨m, hm, hh, ?_⟩
  refine X.sheaf.eq_of_locally_eq₂ (homOfLE hU) (homOfLE hV) hW.le _ _ ?_ ?_
  · change (X.presheaf.map (homOfLE hU).op).hom _ = (X.presheaf.map (homOfLE hU).op).hom _
    rw [map_pow, ← e, ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · change (X.presheaf.map (homOfLE hV).op).hom _ = (X.presheaf.map (homOfLE hV).op).hom _
    rw [map_pow, ← e', ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
end Good
end GlobalTheory.SS.FrobField
