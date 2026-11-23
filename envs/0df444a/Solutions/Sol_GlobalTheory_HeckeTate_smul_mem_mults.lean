-- Prove2me | solution 1 for GlobalTheory.HeckeTate.smul_mem_mults
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:34.289934+00:00
-- url     : https://prove2.me/submissions/143937d5-ca29-42a5-98a2-821880f85c2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_mem_mults

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
namespace GlobalTheory.HeckeTate
theorem _root_.solution {N r : R} (h : N ∣ r) (x : M) : r • x ∈ mults M N := by
  obtain ⟨c, rfl⟩ := h
  exact mem_mults.2 ⟨c • x, mul_smul _ _ _⟩
end GlobalTheory.HeckeTate
