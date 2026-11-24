-- Prove2me | solution 1 for GlobalTheory.GlueModels.model_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:53.125476+00:00
-- url     : https://prove2.me/submissions/48c1ccb5-31b5-46a8-8d06-ca5927ebf3fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield

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
open GlobalTheory GlobalTheory.GlueModels
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GlueModels
theorem _root_.solution {k K : Type} [Field k] [Field K] (β : k →+* K) {U W : Over (Sp K)} (p : W ⟶ U)
    [IsOpenImmersion p.left] {U₀ W₀ : Over (Sp k)} {φU : U.left ⟶ U₀.left} {φW : W.left ⟶ W₀.left}
    (hU : IsPullback φU U.hom U₀.hom (spMap β)) (hW : IsPullback φW W.hom W₀.hom (spMap β))
    (p₀ : W₀ ⟶ U₀) (hp : φW ≫ p₀.left = p.left ≫ φU) :
    IsPullback φW p.left p₀.left φU ∧ IsOpenImmersion p₀.left := by
  have H : IsPullback φW p.left p₀.left φU := by
    refine IsPullback.of_bot ?_ hp hU
    rwa [Over.w p, Over.w p₀]
  refine ⟨H, ?_⟩
  have hβ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap β) := by
    refine ⟨⟨⟨fun x => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩, ?_⟩,
      inferInstanceAs (QuasiCompact (spMap β))⟩
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [β]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat k K))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip (MorphismProperty.of_isPullback hU.flip hβ) ‹_›
end GlobalTheory.GlueModels
