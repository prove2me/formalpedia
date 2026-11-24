-- Prove2me | solution 1 for GlobalTheory.perfLevelOp_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:28:17.691853+00:00
-- url     : https://prove2.me/submissions/e7d6663a-1370-479e-8f2c-81cb7018236a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq
import Theorems.Thm_GlobalTheory_perfLevelOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (x : ι → Perfection S p) :
    (fun i => Perfection.coeff S p n ((x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k))) i))
      = (fun i => Perfection.coeff S p n (x i))
        - perfLevelOp p S Q n (fun i => Perfection.coeff S p n (x i)) := by
  ext i
  simp only [Pi.sub_apply, map_sub, perfLevelOp_apply]
  congr 1
  rw [RingHom.map_mulVec]
  have hc : (Perfection.coeff S p n) ∘ (fun k => frobenius (Perfection S p) p (x k))
      = fun k => frobenius S p (Perfection.coeff S p n (x k)) := by
    funext k
    simp [frobenius_def, map_pow]
  rw [hc]
end GlobalTheory
