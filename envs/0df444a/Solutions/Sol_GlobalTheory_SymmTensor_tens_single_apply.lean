-- Prove2me | solution 1 for GlobalTheory.SymmTensor.tens_single_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:47.147742+00:00
-- url     : https://prove2.me/submissions/f61c666c-909a-4f95-b17b-1ec43b08d420

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SymmTensor
variable {n d : ℕ}
namespace GlobalTheory.SymmTensor
theorem _root_.solution (p : Fin d) (Y : Matrix (Fin n) (Fin n) ℂ) (I K : Fin d → Fin n) :
    tens (Pi.mulSingle p Y) I K = if ∀ q, q ≠ p → I q = K q then Y (I p) (K p) else 0 := by
  simp only [tens, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Pi.mulSingle_eq_same]
  have : ∀ q ∈ Finset.univ.erase p, (Pi.mulSingle p Y : Fin d → Matrix (Fin n) (Fin n) ℂ) q (I q) (K q)
      = if I q = K q then 1 else 0 := fun q hq => by
    rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hq), Matrix.one_apply]
  rw [Finset.prod_congr rfl this, Finset.prod_ite_zero]
  simp
end GlobalTheory.SymmTensor
