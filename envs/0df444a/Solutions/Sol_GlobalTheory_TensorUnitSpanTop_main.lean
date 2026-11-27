-- Prove2me | solution 1 for GlobalTheory.TensorUnitSpanTop.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:27.363027+00:00
-- url     : https://prove2.me/submissions/9f16eb1d-37ce-45c1-a411-847b9f2ae73b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanOneTmulEqTop
import Theorems.Thm_GlobalTheory_TensorUnitSpanTop_span_one_tmul_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorUnitSpanTop
open TensorProduct
namespace GlobalTheory.TensorUnitSpanTop
theorem _root_.solution : ∀ {R M : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : AddCommGroup M] [inst_3 : Module R M] {ι : Type} (f : ι → M), Submodule.span R (Set.range f) = ⊤ → Submodule.span (IsLocalRing.ResidueField R) (Set.range fun (i : ι) ↦ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ :=
  fun f hf => span_one_tmul_eq_top f hf
end GlobalTheory.TensorUnitSpanTop
