-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.mem_acrisZero_of_forall_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:53:49.540918+00:00
-- url     : https://prove2.me/submissions/9c3ce67d-983a-4c60-a4f2-512531ff8cbe

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj

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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution {z : 𝔸}
    (h : ∀ m : ℕ, ∃ s ∈ ACrisZero K p, algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) ∣ z - s) :
    z ∈ ACrisZero K p := by
  obtain ⟨N, w, hwN⟩ := IsLocalization.Away.surj (p : AInf K p) z
  rw [map_natCast] at hwN
  set m := p ^ N with hm
  have hm0 : m ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  obtain ⟨s, hs, r, hr⟩ := h m
  obtain ⟨s', hs', w', r', hw', hr'⟩ := exists_decomp ker_eq_span_xiGen m hs
  set ξm := algebraMap (AInf K p) 𝔸 (xiGen K p ^ m)
  have hz : z = s' + ξm * (r + r') := by
    rw [show z = s + (z - s) by ring, hr, hr']; ring
  have hfac : ((m.factorial : ℕ) : 𝔸) = (p : 𝔸) ^ N * ((m - 1).factorial : 𝔸) := by
    rw [← Nat.mul_factorial_pred hm0, Nat.cast_mul, hm, Nat.cast_pow]

  have hW : ξm * ((m.factorial : 𝔸) * (r + r')) =
      algebraMap (AInf K p) 𝔸 (((m - 1).factorial : AInf K p) * w - (p : AInf K p) ^ N * w') := by
    have e1 : ξm * (r + r') = z - s' := by rw [hz]; ring
    rw [map_sub, map_mul, map_mul, map_pow, map_natCast, map_natCast, ← hw', ← hwN, hfac]
    linear_combination ((p : 𝔸) ^ N * ((m - 1).factorial : 𝔸)) * e1
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 ((algebraMap_dvd_iff m _).1 ⟨_, hW.symm⟩)
  have hnz : xiGen K p ^ m ∈ nonZeroDivisors (AInf K p) :=
    pow_mem (IsPerfectoidField.mem_nonZeroDivisors_of_ker_eq_span ker_eq_span_xiGen) m
  have hR : (m.factorial : 𝔸) * (r + r') = algebraMap (AInf K p) 𝔸 d := by
    have h0 : algebraMap (AInf K p) 𝔸 (xiGen K p ^ m) * ((m.factorial : 𝔸) * (r + r') -
        algebraMap (AInf K p) 𝔸 d) = 0 := by
      rw [mul_sub, hW, ← map_mul, ← hd, mul_comm, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_algebraMap_mul_eq_zero hnz h0)
  have hxi : ξm * (r + r') = dpow m (xiGen K p) * algebraMap (AInf K p) 𝔸 d := by
    rw [← hR, ← mul_assoc, mul_comm (dpow m (xiGen K p)), factorial_mul_dpow, ← map_pow]
  have hξmem : xiGen K p ∈ RingHom.ker θ := by
    rw [ker_eq_span_xiGen]; exact Ideal.mem_span_singleton_self _
  rw [hz, hxi]
  exact add_mem hs' (Subalgebra.mul_mem _ (dpow_mem hξmem m) (Subalgebra.algebraMap_mem _ d))
end GroundTheory.PAdicHodge.ACris
