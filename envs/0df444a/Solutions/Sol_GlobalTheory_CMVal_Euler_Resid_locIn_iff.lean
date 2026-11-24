-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.Resid.locIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:04:01.240043+00:00
-- url     : https://prove2.me/submissions/3fb5e64f-8612-40c0-a529-3c48566a6753

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitRepresentativesSplitPrime
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_le_exp_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_val_iota_lt_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_val_iota_eq_one
import Theorems.Thm_GlobalTheory_CMVal_Euler_inv_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_mul
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_sub
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_sub_coord
import Theorems.Thm_GlobalTheory_CMVal_suppAt_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.Resid
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler.Resid
theorem _root_.solution {q : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P q) (hP' : Over P' q)
    (hne : P' ≠ P) (hall : ∀ R, Over R q → R = P ∨ R = P') (y : (Af E)ˣ) {a b t : OF E}
    (ha : Valued.v ((y : Af E) P' - iota a P') < 1) (hb : Valued.v ((y : Af E) P - iota b P) < 1)
    (ht : t ∉ q.asIdeal) (r : (P.adicCompletion E)ˣ) (hr : (r : P.adicCompletion E) = iota t P) :
    LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) ↔ b - t * a ∈ q.asIdeal := by
  have e1 : (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) P = (iota t P)⁻¹ * (y : Af E) P := by
    rw [Units.val_mul, mul_coord, inv_coord, single_self, hr]
  have e2 : (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) P' = (y : Af E) P' := by
    rw [Units.val_mul, mul_coord, inv_coord, suppAt_single P r P' hne, inv_one, one_mul]
  have hv := val_iota_eq_one hP ht
  have h0 : iota t P ≠ 0 := hr ▸ r.ne_zero
  constructor
  · rintro ⟨d, hd⟩
    have h1 := (le_exp_iff _).1 (hd P hP)
    have h2 := (le_exp_iff _).1 (hd P' hP')
    rw [e1] at h1
    rw [e2] at h2
    have h3 : d - a ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP', iota_sub, sub_coord]
      have := Valuation.map_sub_lt _ ha h2
      rwa [sub_sub_sub_cancel_left] at this
    have h4 : b - t * d ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP, iota_sub, iota_mul, sub_coord, mul_coord]
      have : iota b P - iota t P * iota d P =
          iota t P * ((iota t P)⁻¹ * (y : Af E) P - iota d P) - ((y : Af E) P - iota b P) := by
        rw [mul_sub, mul_inv_cancel_left₀ h0]; ring
      rw [this]
      refine Valuation.map_sub_lt _ ?_ hb
      rwa [map_mul, hv, one_mul]
    have := add_mem h4 (q.asIdeal.mul_mem_left t h3)
    convert this using 1
    ring
  · intro h
    refine ⟨a, fun R hR => (le_exp_iff _).2 ?_⟩
    rcases hall R hR with rfl | rfl
    · rw [← val_iota_lt_iff hP, iota_sub, iota_mul, sub_coord, mul_coord] at h
      have : (iota t R)⁻¹ * (y : Af E) R - iota a R =
          (iota t R)⁻¹ * (((y : Af E) R - iota b R) + (iota b R - iota t R * iota a R)) := by
        rw [sub_add_sub_cancel, mul_sub, inv_mul_cancel_left₀ h0]
      rw [e1, this, map_mul, map_inv₀, hv, inv_one, one_mul]
      exact Valuation.map_add_lt _ hb h
    · rwa [e2]
end GlobalTheory.CMVal.Euler.Resid
