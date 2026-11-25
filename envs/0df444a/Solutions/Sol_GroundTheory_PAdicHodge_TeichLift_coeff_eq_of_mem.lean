-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.coeff_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:23.971834+00:00
-- url     : https://prove2.me/submissions/29a802b4-b63a-43ec-8304-5a5fede647af

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_red___ee117558e102
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_mem_span_pow_of___mul_3e1ac1a2d1bc
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_succ
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_finSum_succ__591efcd7936f
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_red_finSum

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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {n : ℕ} {x : Γ} {a : ℕ → L}
    (h : x - T.finSum a (n + 1) ∈ Ideal.span {T.π ^ (n + 1)}) : ∀ m ≤ n, T.coeff x m = a m := by
  induction n generalizing x a with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := by omega
    obtain ⟨y, hy⟩ := T.mem_span_pow.1 h
    have := congrArg T.red hy
    rw [map_sub, red_finSum, map_mul, map_pow, red_π, zero_pow (by norm_num), zero_mul,
      sub_eq_zero] at this
    simpa using this
  | succ n ih =>
    have h0 : T.red x = a 0 := by
      obtain ⟨y, hy⟩ := T.mem_span_pow.1 h
      have := congrArg T.red hy
      rw [map_sub, red_finSum, map_mul, map_pow, red_π, zero_pow (by norm_num), zero_mul,
        sub_eq_zero] at this
      exact this
    have h1 : T.tail x - T.finSum (fun i => a (i + 1)) (n + 1) ∈ Ideal.span {T.π ^ (n + 1)} := by
      refine T.mem_span_pow_of_π_mul ?_
      have : x - T.finSum a (n + 1 + 1) = T.π * (T.tail x - T.finSum (fun i => a (i + 1)) (n + 1)) := by
        rw [T.finSum_succ' a (n + 1), ← h0]
        calc x - (T.teich (T.red x) + T.π * T.finSum (fun i => a (i + 1)) (n + 1))
            = (x - T.teich (T.red x)) - T.π * T.finSum (fun i => a (i + 1)) (n + 1) := by ring
          _ = T.π * T.tail x - T.π * T.finSum (fun i => a (i + 1)) (n + 1) := by
            rw [T.sub_teich_eq_π_mul_tail]
          _ = _ := by ring
      rw [← this]; exact h
    intro m hm
    rcases m with _ | m
    · simpa using h0
    · rw [coeff_succ]; exact ih h1 m (by omega)
end GroundTheory.PAdicHodge.TeichLift
