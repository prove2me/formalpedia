-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.not_isIntegral_inv_smul_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:51:56.697717+00:00
-- url     : https://prove2.me/submissions/4cd37c20-5d11-4d36-8890-f16065e95a3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_exists_bound
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_trace_mem_of_isIntegral
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_trace_ne_zero_of_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution {a : K.O} (ha : K.Small a) {f : B.A} (hf : IsIdempotentElem f)
    (h0 : f ≠ 0) : ¬ IsIntegral K.O (al K a ^ (-1 : ℤ) • f) := by
  intro hint
  obtain ⟨C, hC⟩ := exists_bound ha (trace_ne_zero_of_idem B hf h0)
  have hpow : (al K a ^ (-1 : ℤ) • f) ^ (C + 1) = al K a ^ (-((C + 1 : ℕ) : ℤ)) • f := by
    rw [_root_.smul_pow, hf.pow_succ_eq, ← zpow_natCast, ← zpow_mul]; congr 2; push_cast; ring
  have ht := trace_mem_of_isIntegral B (hint.pow (C + 1))
  rw [hpow, LinearMap.map_smul, smul_eq_mul] at ht
  have := hC _ ht
  push_cast at this
  omega
end GlobalTheory.UnitLemma.Desc.Window
