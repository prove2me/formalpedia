-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.gramB_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:10.835907+00:00
-- url     : https://prove2.me/submissions/3eaf4027-8a00-4deb-ae0b-8a872c511273

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_sig_sig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).IsSymm := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  ext p q
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  change Algebra.trace F E (σ (b q.2) * J q.1 p.1 * b p.2) =
    Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)
  rw [← Algebra.trace_eq_of_algEquiv e (σ (b q.2) * J q.1 p.1 * b p.2)]
  congr 1
  change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
  rw [map_mul, map_mul, sig_sig σ hσ, hJ.1 p.1 q.1]
  ring
end GlobalTheory.CompanionTheory.SW.TraceCoord
