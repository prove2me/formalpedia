-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_eq_sum_pow_of_adjoin_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:53.044682+00:00
-- url     : https://prove2.me/submissions/3fd6df3a-6c86-49e8-938b-3b1ac9983a7b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_natDegree_minpoly_cycl_of_adjoin_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {y : PadicAlgCl p}
    (hy : ℚ_[p]⟮y⟯ = cycl p (k + 1)) {x : PadicAlgCl p} (hx : x ∈ cycl p (k + 1)) :
    ∃ b : ℕ → PadicAlgCl p, (∀ i, b i ∈ cycl p k) ∧ x = ∑ i ∈ Finset.range p, b i * y ^ i := by
  have hint : IsIntegral (cycl p k) y :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = p := by
    rw [IntermediateField.adjoin.powerBasis_dim, natDegree_minpoly_cycl_of_adjoin_eq hk hy]
  have hx' : x ∈ (cycl p k)⟮y⟯ := by
    have : cycl p (k + 1) ≤ ((cycl p k)⟮y⟯).restrictScalars ℚ_[p] := by
      rw [← hy, adjoin_simple_le_iff, mem_restrictScalars]
      exact mem_adjoin_simple_self _ y
    exact this hx
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨x, hx'⟩
  refine ⟨fun i => algebraMap (cycl p k) (PadicAlgCl p) (f.coeff i), fun i => (f.coeff i).2, ?_⟩
  have h1 : x = aeval y f := by
    have := congrArg (algebraMap ((cycl p k)⟮y⟯) (PadicAlgCl p)) hf
    rw [IntermediateField.adjoin.powerBasis_gen, ← aeval_algebraMap_apply] at this
    exact this
  rw [h1, aeval_eq_sum_range' (hfdeg.trans_eq hdim)]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]
end GroundTheory.PAdicHodge
