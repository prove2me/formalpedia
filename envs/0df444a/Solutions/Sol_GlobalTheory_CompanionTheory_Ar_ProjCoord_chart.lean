-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:33:58.902942+00:00
-- url     : https://prove2.me/submissions/b9f44202-7afe-493e-8a8c-2fd7fcddc502

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_regAt_push
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_genMap_push_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_specializes_of_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_mem_regAt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (ξ : Spec (CommRingCat.of Ω) ⟶ X) (φ : A →+* Ω) (hφ : Function.Injective φ)
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f] (e : ξ = CptModel.pt φ ≫ f)
    (q : Spec (CommRingCat.of A)) :
    ∃ h : genPt ξ ⤳ f q, Function.Injective (genMap ξ ⟨f q, h⟩) ∧
      ∀ c : Ω, c ∈ regAt ξ ⟨f q, h⟩ ↔ ∃ a s : A, s ∉ q.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a := by
  subst e
  let p : Cpt (CptModel.pt φ) := ⟨q, specializes_of_injective φ hφ q⟩
  refine ⟨(push _ f p).2, genMap_push_injective _ f p (CptModel.genMap_injective φ hφ p), fun c => ?_⟩
  exact (congrArg (c ∈ ·) (regAt_push _ f p)).to_iff.trans (CptModel.mem_regAt_iff φ p c)
end GlobalTheory.CompanionTheory.Ar.ProjCoord
