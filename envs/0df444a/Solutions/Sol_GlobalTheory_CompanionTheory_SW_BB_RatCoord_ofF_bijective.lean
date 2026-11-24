-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.RatCoord.ofF_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:10:44.3683+00:00
-- url     : https://prove2.me/submissions/0d6531cd-9fb6-401c-aeab-2fdb924b27ac

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_repr_ofF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) := by
  constructor
  · intro x y hxy
    funext p
    obtain ⟨i, k⟩ := p
    rw [← repr_ofF b x 0 i k, ← repr_ofF b y 0 i k, hxy]
  · intro Y
    refine ⟨fun p => b.repr (Y 0 p.1) p.2, ?_⟩
    funext u i
    obtain rfl : u = 0 := Subsingleton.elim _ _
    exact b.sum_repr (Y 0 i)
end GlobalTheory.CompanionTheory.SW.BB.RatCoord
