-- Prove2me | solution 1 for GlobalTheory.T.trace_form_invariance_under_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:25:29.485306+00:00
-- url     : https://prove2.me/submissions/b83dee81-80de-4bec-9cdf-bb42e1e66863

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceFormInvarianceUnderUnitary
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceFormInvarianceUnderUnitaryStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_ginf_gfin_isometry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ h : HA (AF F) σ J, (gmat (AF F) σ J b h)ᵀ * B.map (algebraMap F (AF F)) * gmat (AF F) σ J b h = B.map (algebraMap F (AF F))) → (∀ ω w, (ginf e σ J b ω w)ᵀ * B.map (ρ w) * ginf e σ J b ω w = B.map (ρ w)) ∧ ∀ ω, (gfin σ J b ω)ᵀ * B.map (algebraMap F (Af F)) * gfin σ J b ω = B.map (algebraMap F (Af F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry | exact GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_isometry <;> assumption)
end _root_.GlobalTheory.T
