-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.sum_out_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:40.573158+00:00
-- url     : https://prove2.me/submissions/859b4b12-b924-40a4-9cf3-ab8f8c648f1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {H V : Type} [Group H] [AddCommGroup V]
namespace GlobalTheory.CompanionTheory.TwistedAverage
theorem _root_.solution (N : Subgroup H) [N.Normal] [Fintype (H ⧸ N)] (f : H → V)
    (hf : ∀ x, ∀ k ∈ N, f (x * k) = f x) (l : H) :
    ∑ q : H ⧸ N, f (q.out * l) = ∑ q : H ⧸ N, f q.out := by
  have h1 : ∀ q : H ⧸ N, f (q.out * l) = f (q * (QuotientGroup.mk l : H ⧸ N)).out := by
    intro q
    have hq : q * (QuotientGroup.mk l : H ⧸ N) = QuotientGroup.mk (q.out * l) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (q.out * l)
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f (q.out * l)
      = ∑ q : H ⧸ N, f (q * (QuotientGroup.mk l : H ⧸ N)).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ q : H ⧸ N, f q.out :=
        Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk l : H ⧸ N)) (fun q => f q.out)
end GlobalTheory.CompanionTheory.TwistedAverage
