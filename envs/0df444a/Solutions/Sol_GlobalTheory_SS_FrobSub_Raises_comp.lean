-- Prove2me | solution 1 for GlobalTheory.SS.FrobSub.Raises.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:10.063728+00:00
-- url     : https://prove2.me/submissions/852556f0-330e-473c-b610-ea22bc9fce46

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
theorem _root_.solution {X : Scheme.{0}} {φ ψ : X ⟶ X} {a b : ℕ} {U : X.Opens} {f : Γ(X, U)}
    (h₁ : Raises φ a U f) (h₂ : Raises ψ b U f) : Raises (φ ≫ ψ) (a * b) U f := by
  obtain ⟨e₁, p₁⟩ := h₁
  obtain ⟨e₂, p₂⟩ := h₂
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← e₂, ← e₁], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U e₂.le e₁.le, CommRingCat.hom_comp, RingHom.comp_apply, p₂,
    map_pow, p₁, ← pow_mul]
end Raises
end GlobalTheory.SS.FrobSub
