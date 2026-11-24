-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coeff_monicOfCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:22.593122+00:00
-- url     : https://prove2.me/submissions/dace6af2-528f-4434-87f2-0e3cfb2c4c95

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (e : ℕ) (a : ℕ → 𝒪C♭) (m : ℕ) :
    (monicOfCoeffs e a).coeff m = if m = e then 1 else if m < e then a m else 0 := by
  simp only [monicOfCoeffs, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with h1 h2
  · subst h1
    rw [Finset.sum_eq_zero fun i hi => if_neg (by have := Finset.mem_range.1 hi; omega), add_zero]
  · rw [Finset.sum_eq_single m (fun i _ hi => if_neg (Ne.symm hi)) (fun h => absurd
      (Finset.mem_range.2 h2) h), if_pos rfl, zero_add]
  · rw [zero_add, Finset.sum_eq_zero fun i hi => if_neg (by
      have := Finset.mem_range.1 hi; omega)]
end GroundTheory.PAdicHodge
