-- Prove2me | solution 1 for GlobalTheory.Klein.half_mem_intAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:57:05.852914+00:00
-- url     : https://prove2.me/submissions/d1b3a8ca-b73a-42b7-a65c-4b3929628f34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
import Theorems.Thm_GlobalTheory_Klein_mem_intAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
theorem _root_.solution (ι : ℂ ≃+* ℂ_[p]) (hp : p ≠ 2) : (2⁻¹ : ℂ) ∈ intAt ι := by
  have hc : Nat.Coprime p 2 := (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hc
  have h2 : ‖((2 : ℕ) : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', h]
  have h3 : ι 2 = ((2 : ℕ) : ℂ_[p]) := by
    rw [← map_natCast ι]; simp
  rw [mem_intAt, map_inv₀, norm_inv, h3, h2]; simp
end GlobalTheory.Klein
