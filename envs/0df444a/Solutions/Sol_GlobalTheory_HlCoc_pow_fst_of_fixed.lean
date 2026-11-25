-- Prove2me | solution 1 for GlobalTheory.HlCoc.pow_fst_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:30.601698+00:00
-- url     : https://prove2.me/submissions/3199e047-5705-4cec-89f3-9f9496aca53d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueCocycle
import Theorems.Thm_GlobalTheory_HlCoc_sndHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HlCoc.sndHom_apply

set_option autoImplicit false
open GlobalTheory GlobalTheory.HlCoc
open Topology
variable {G M : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]
namespace GlobalTheory.HlCoc
theorem _root_.solution (p : SD M G) (h : p.2 • p.1 = p.1) (n : ℕ) :
    (p ^ n).1 = n • p.1 := by
  have hs : ∀ k : ℕ, (p ^ k).2 = p.2 ^ k := fun k => by
    simpa using map_pow (sndHom : SD M G →* G) p k
  have hf : ∀ k : ℕ, p.2 ^ k • p.1 = p.1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, h, ih]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_fst, ih, hs, hf, succ_nsmul]
end GlobalTheory.HlCoc
