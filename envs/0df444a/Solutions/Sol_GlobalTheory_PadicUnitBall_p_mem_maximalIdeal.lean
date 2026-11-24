-- Prove2me | solution 1 for GlobalTheory.PadicUnitBall.p_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:34:02.69264+00:00
-- url     : https://prove2.me/submissions/e5a80cd4-cd48-4a34-b204-9b0657f8edf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl
import Theorems.Thm_GlobalTheory_PadicUnitBall_norm_natCast_p

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicUnitBall
variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}
namespace GlobalTheory.PadicUnitBall
theorem _root_.solution
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ((p : ℕ) : V) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h1 : ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ ≤ 1 := (hV _).2 ⟨_, rfl⟩
  have h2 : κ (algebraMap V (FractionRing V) ((p : ℕ) : V)) *
      κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)) = 1 := by
    rw [← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one, map_natCast, map_natCast, norm_natCast_p] at h3
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (p : ℝ)⁻¹ * ‖κ (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) h1) (inv_lt_one_of_one_lt₀ hp)
  linarith
end GlobalTheory.PadicUnitBall
