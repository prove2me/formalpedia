-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_sub_one_pow_totient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:58.282931+00:00
-- url     : https://prove2.me/submissions/72ebfef9-bf35-4b92-bea3-e0d3f8b331d3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_prime
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_eq_of_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
import Theorems.Thm_UpperTheory_Reformulated_B_CapelliMiscellany_norm_natCast_prime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ζ : PadicAlgCl p} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    ‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1)) = (p : ℝ)⁻¹ := by
  have hpos : 0 < p ^ (k + 1) := pow_pos (Fact.out : p.Prime).pos _
  have h1 := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
  rw [eval_one_cyclotomic_prime_pow, eval_prod] at h1
  simp only [eval_sub, eval_X, eval_C] at h1
  rw [← norm_natCast_prime]
  calc ‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1))
      = ∏ _μ ∈ primitiveRoots (p ^ (k + 1)) (PadicAlgCl p), ‖ζ - 1‖ := by
        rw [Finset.prod_const, hζ.card_primitiveRoots]
    _ = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) (PadicAlgCl p), ‖1 - μ‖ :=
        Finset.prod_congr rfl fun μ hμ => by
          rw [norm_sub_rev 1 μ]
          exact (norm_sub_one_eq_of_isPrimitiveRoot hpos.ne' hζ
            ((mem_primitiveRoots hpos).1 hμ)).symm
    _ = _ := by rw [h1, norm_prod]
end GroundTheory.PAdicHodge
