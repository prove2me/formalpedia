-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.isLocR_Ainf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:49:13.694808+00:00
-- url     : https://prove2.me/submissions/8f4321a6-39f0-4dee-9122-ee6f65aa4d72

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInf_isOpen_posU
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInf_isOpenEmbedding_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory.CompanionTheory.SW.LocInf
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → IsLocR (Ainf F) := by
  intro F _ _ h
  have hT2 : T2Space (Ainf F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
  have hSC : SecondCountableTopology (Ainf F) := (hInf F h).secondCountableTopology
  have hArt : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ w : InfinitePlace F, w.Completion))
  have hRed : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ w : InfinitePlace F, w.Completion))
  have hval : IsOpenEmbedding (Units.val : (Ainf F)ˣ → Ainf F) := by
    have h1 : IsOpenEmbedding (Units.val : (InfinitePlace F → ℝ)ˣ → (InfinitePlace F → ℝ)) :=
      Units.isOpenEmbedding_val
    have h2 := ((hInf F h).symm.isOpenEmbedding.comp h1).comp (uInf F h).isOpenEmbedding
    convert h2 using 1
    funext u
    exact ((eInf F h).symm_apply_apply _).symm
  refine ⟨inferInstance, inferInstance, hSC, hT2, hArt, hRed, hval,
    (posU (InfinitePlace F)).comap (Units.map (eInf F h).toMonoidHom), ?_, ?_⟩
  · exact (isOpen_posU (InfinitePlace F)).preimage (uInf F h).continuous
  · let S := (posU (InfinitePlace F)).comap (Units.map (eInf F h).toMonoidHom)
    let T : S ≃ₜ posU (InfinitePlace F) :=
      (uInf F h).subtype (fun x => Iff.rfl)
    have h2 := ((uInf F h).symm.isOpenEmbedding.comp (isOpenEmbedding_sq (InfinitePlace F))).comp
      T.isOpenEmbedding
    convert h2 using 1
    funext u
    apply (uInf F h).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact map_pow (Units.map (eInf F h).toMonoidHom) (u : (Ainf F)ˣ) 2
end GlobalTheory.CompanionTheory.SW
