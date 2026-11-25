-- Prove2me | solution 1 for GroundTheory.PAdicHodge.inv_p_le_norm_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:09.766875+00:00
-- url     : https://prove2.me/submissions/a1ee31de-ee2e-4717-ae42-ed57d4da7eaa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_totient
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_le_one

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
theorem _root_.solution {ε : PadicAlgCl p} (hε : ε ^ p = 1) (hε1 : ε ≠ 1) {i : ℕ}
    (hi0 : 1 ≤ i) (hip : i < p) : (p : ℝ)⁻¹ ≤ ‖ε ^ i - 1‖ := by
  have hpr := (Fact.out : p.Prime)
  have hprim : IsPrimitiveRoot ε p := by
    have := IsPrimitiveRoot.orderOf ε
    rwa [orderOf_eq_prime hε hε1] at this
  have hcop : i.Coprime p :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpr).2 fun h => by
      have := Nat.le_of_dvd (by omega) h; omega)
  have hprim' : IsPrimitiveRoot (ε ^ i) (p ^ (0 + 1)) := by
    rw [zero_add, pow_one]; exact hprim.pow_of_coprime i hcop
  have h := norm_sub_one_pow_totient hprim'
  rw [← h]
  exact pow_le_of_le_one (norm_nonneg _)
    (norm_sub_one_le_one (pow_ne_zero _ hpr.ne_zero) hprim'.pow_eq_one)
    (Nat.totient_pos.2 (pow_pos hpr.pos _)).ne'
end GroundTheory.PAdicHodge
