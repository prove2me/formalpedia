-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:28:07.793932+00:00
-- url     : https://prove2.me/submissions/0e59b522-6ab7-4627-94b5-e60ff7ca43db

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceFormInvarianceUnderUnitary
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_isometry_map_ringHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x)
    (hB : ∀ h : HA (AF F) σ J, (gmat (AF F) σ J b h)ᵀ * B.map (algebraMap F (AF F)) *
      gmat (AF F) σ J b h = B.map (algebraMap F (AF F))) :
    (∀ ω w, (ginf e σ J b ω w)ᵀ * B.map (ρ w) * ginf e σ J b ω w = B.map (ρ w)) ∧
      ∀ ω, (gfin σ J b ω)ᵀ * B.map (algebraMap F (Af F)) * gfin σ J b ω =
        B.map (algebraMap F (Af F)) := by
  refine ⟨fun ω w => ?_, fun ω => ?_⟩
  · exact isometry_map_ringHom
      ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
        ((e : Ainf F →+* (InfinitePlace F → ℝ)).comp (fstA F : AF F →+* Ainf F)))
      (algebraMap F (AF F)) (ρ w)
      (fun x => by
        have h1 : fstA F (algebraMap F (AF F) x) = algebraMap F (Ainf F) x :=
          (fstA F).commutes x
        simpa [h1] using he x w)
      (gmat (AF F) σ J b ω⁻¹) B (hB ω⁻¹)
  · exact isometry_map_ringHom (sndA F : AF F →+* Af F)
      (algebraMap F (AF F)) (algebraMap F (Af F))
      (fun x => (sndA F).commutes x)
      (gmat (AF F) σ J b ω⁻¹) B (hB ω⁻¹)
end GlobalTheory.CompanionTheory.SW.BB
