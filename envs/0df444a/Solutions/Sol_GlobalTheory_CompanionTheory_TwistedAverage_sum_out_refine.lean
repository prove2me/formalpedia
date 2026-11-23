-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.sum_out_refine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:14.0598+00:00
-- url     : https://prove2.me/submissions/6d137c5a-c483-4a10-ba77-13efda8d6758

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
theorem _root_.solution {N K : Subgroup H} (hNK : N ≤ K) [Fintype (H ⧸ N)] [Fintype (H ⧸ K)]
    [Fintype (K ⧸ N.subgroupOf K)] (f : H → V) (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ q : H ⧸ N, f q.out = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
  have h1 : ∀ q : H ⧸ N, f q.out = f ((Subgroup.quotientEquivProdOfLE hNK q).1).out := by
    intro q
    have hq : (Subgroup.quotientEquivProdOfLE hNK q).1 = (QuotientGroup.mk q.out : H ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K q.out
    rw [hh, hf _ _ h.2]
  calc ∑ q : H ⧸ N, f q.out
      = ∑ q : H ⧸ N, f ((Subgroup.quotientEquivProdOfLE hNK q).1).out :=
        Finset.sum_congr rfl fun q _ => h1 q
    _ = ∑ p : (H ⧸ K) × (K ⧸ N.subgroupOf K), f p.1.out :=
        Equiv.sum_comp (Subgroup.quotientEquivProdOfLE hNK) (fun p => f p.1.out)
    _ = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ]
        rw [Finset.smul_sum]
end GlobalTheory.CompanionTheory.TwistedAverage
