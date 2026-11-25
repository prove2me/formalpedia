-- Prove2me | solution 1 for GlobalTheory.DetBound.exists_wedge_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:39:40.911803+00:00
-- url     : https://prove2.me/submissions/560171fe-d38a-4e38-a308-d1043f12e17d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
import Theorems.Thm_P2M_GlobalTheory_DetBound__Multi_eq_det_smul_70a319abcdeb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Module.Free O M]
    [Module.Finite O M] {n : ℕ} (hn : Module.finrank O M = n) : ∃ ω : ⋀[O]^n M, O ∙ ω = ⊤ := by
  let b := Module.finBasisOfFinrankEq O M hn
  refine ⟨exteriorPower.ιMulti O n b, ?_⟩
  rw [eq_top_iff, ← exteriorPower.ιMulti_span O n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  rw [ιMulti_eq_det_smul b v]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
end GlobalTheory.DetBound
