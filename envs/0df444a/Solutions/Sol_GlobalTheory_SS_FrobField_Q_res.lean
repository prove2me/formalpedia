-- Prove2me | solution 1 for GlobalTheory.SS.FrobField.Q.res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:05:24.557796+00:00
-- url     : https://prove2.me/submissions/38438fe0-2053-41e5-9ead-6e98249e1653

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
namespace Q
theorem _root_.solution {X : Scheme.{0}} {φ : X ⟶ X} {n : ℕ} {U V : X.Opens} {f : Γ(X, U)}
    (a : Q φ n U f) (i : V ≤ U) (h : V = φ ⁻¹ᵁ V) : Q φ n V ((X.presheaf.map (homOfLE i).op).hom f) := by
  obtain ⟨h', e⟩ := a
  refine ⟨h, ?_⟩
  rw [← map_pow, ← e, ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
end Q
end GlobalTheory.SS.FrobField
