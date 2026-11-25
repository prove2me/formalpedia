-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_eq_of_pow_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:26.915225+00:00
-- url     : https://prove2.me/submissions/2b5cdfb2-2edc-4166-8c35-d623aa14748e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Theorems.Thm_GroundTheory_PAdicHodge_mem_unramifiedClosure_of_pow_eq_one

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
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ω : ℂ_[p]} {r : ℕ} (hr : 1 ≤ r) (h : ω ^ p ^ r = ω) :
    ∃ u ∈ unramifiedClosure p, (u : ℂ_[p]) = ω := by
  by_cases h0 : ω = 0
  · exact ⟨0, zero_mem _, by rw [h0]; rfl⟩
  set n := p ^ r - 1 with hn
  have hq : 2 ≤ p ^ r := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
  have hnpos : 0 < n := by omega
  have hqn : p ^ r = n + 1 := by omega
  have hω : ω ^ n = 1 := by
    rw [hqn, pow_succ] at h
    exact (mul_eq_right₀ h0).1 h
  have hcop : n.Coprime p := by
    have h1 : n.Coprime (n + 1) := Nat.coprime_self_add_right.2 (Nat.coprime_one_right n)
    rw [← hqn] at h1
    exact h1.coprime_dvd_right (dvd_pow_self p (by omega))

  set P : (PadicAlgCl p)[X] := X ^ n - 1
  have hmon : P.Monic := monic_X_pow_sub_C 1 (by omega)
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hP := hsplit.eq_prod_roots_of_monic hmon
  have hev : (P.map (algebraMap (PadicAlgCl p) ℂ_[p])).eval ω = 0 := by
    simp [P, hω]
  rw [hP] at hev
  simp only [Polynomial.map_multiset_prod, eval_multiset_prod, Multiset.map_map] at hev
  obtain ⟨x, hx, ha0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 hev)
  simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub,
    eval_X, eval_C] at ha0
  have hxroot : x ^ n = 1 := by
    have := (mem_roots hmon.ne_zero).1 hx
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at this
    exact this
  exact ⟨x, mem_unramifiedClosure_of_pow_eq_one hnpos hcop hxroot, (sub_eq_zero.1 ha0).symm⟩
end GroundTheory.PAdicHodge
