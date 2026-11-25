-- Prove2me | solution 1 for GlobalTheory.Klein.DiffUnit.norm_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:01:53.547532+00:00
-- url     : https://prove2.me/submissions/9ec898c9-c1dc-4c0e-a185-676b13c90a02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne

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
open GlobalTheory GlobalTheory.Klein GlobalTheory.Klein.DiffUnit
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein.DiffUnit
theorem _root_.solution (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h1 : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have h2 : (2 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := by
    rw [map_natCast]; norm_num
  rw [h2, norm_algebraMap', h1]
end GlobalTheory.Klein.DiffUnit
