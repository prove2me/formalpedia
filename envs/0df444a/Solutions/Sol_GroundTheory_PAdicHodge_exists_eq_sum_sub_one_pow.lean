-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_eq_sum_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:50.781824+00:00
-- url     : https://prove2.me/submissions/76a2ae4b-387d-4de1-a532-e3d74961b37f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
import Theorems.Thm_GroundTheory_PAdicHodge_adjoin_sub_one_eq_cycl
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_cycl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {x : PadicAlgCl p} (hx : x ∈ cycl p n) :
    ∃ a : ℕ → ℚ_[p], x = ∑ i ∈ Finset.range (Nat.totient (p ^ n)),
      algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ i := by
  have hint : IsIntegral ℚ_[p] (ζ - 1) := Algebra.IsIntegral.isIntegral _
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = Nat.totient (p ^ n) := by
    rw [IntermediateField.adjoin.powerBasis_dim, ← IntermediateField.adjoin.finrank hint,
      adjoin_sub_one_eq_cycl hζ, finrank_cycl]
  have hx' : x ∈ ℚ_[p]⟮ζ - 1⟯ := by rw [adjoin_sub_one_eq_cycl hζ]; exact hx
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨x, hx'⟩
  refine ⟨fun i => f.coeff i, ?_⟩
  have h1 : x = aeval (ζ - 1) f := by
    have := congrArg (algebraMap (ℚ_[p]⟮ζ - 1⟯) (PadicAlgCl p)) hf
    rw [IntermediateField.adjoin.powerBasis_gen, ← aeval_algebraMap_apply] at this
    exact this
  rw [h1, aeval_eq_sum_range' (hfdeg.trans_eq hdim)]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]
end GroundTheory.PAdicHodge
