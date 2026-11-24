-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.consTup_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:50:29.52899+00:00
-- url     : https://prove2.me/submissions/bce07712-1770-4bbd-bb30-fc61106bd181

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_one_mem_latR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.LatRat
theorem _root_.solution {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ k, algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro hX a i k
    simpa [consTup] using hX a.succ i.succ k
  · intro hX a
    refine Fin.cases ?_ (fun a => ?_) a
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro k
        simpa [consTup] using one_mem_latR h k
      · simp [consTup]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consTup]
      · simpa [consTup] using hX a i
end GlobalTheory.CompanionTheory.SW.LatRat
