-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CoordMat.traceGram_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:13:49.180567+00:00
-- url     : https://prove2.me/submissions/c878cd54-7631-464c-a01c-52603a3e9723

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CoordMat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.CoordMat
theorem _root_.solution [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j) (b : Module.Basis (Fin d) F E) :
    (traceGram σ J b).IsSymm := by
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ
    ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩
  refine Matrix.IsSymm.ext fun p q => ?_
  simp only [traceGram]
  have hm : e (σ (b q.2) * J q.1 p.1 * b p.2) = σ (b p.2) * J p.1 q.1 * b q.2 := by
    change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
    rw [map_mul, map_mul, hσ, hJ]
    ring
  exact (Algebra.trace_eq_of_algEquiv e _).symm.trans (congrArg _ hm)
end GlobalTheory.CompanionTheory.SW.CoordMat
