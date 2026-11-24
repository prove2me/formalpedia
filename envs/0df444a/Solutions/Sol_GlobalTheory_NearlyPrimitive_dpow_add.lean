-- Prove2me | solution 1 for GlobalTheory.NearlyPrimitive.dpow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:49.547123+00:00
-- url     : https://prove2.me/submissions/b8c9a16e-e1e0-4d7e-ba2b-f8fdb27165da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
namespace GlobalTheory.NearlyPrimitive
theorem _root_.solution {C : Type} [Field C] [CharZero C] {B : Type} [CommRing B] [Algebra C B]
    (n : ℕ) (x y : B) :
    dpow C n (x + y) = ∑ m ∈ antidiagonal n, dpow C m.1 x * dpow C m.2 y := by
  unfold dpow
  rw [(Commute.all x y).add_pow', Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.HasAntidiagonal.mem_antidiagonal.mp hm
  rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul C, smul_smul]
  congr 1
  have h := Nat.choose_mul_factorial_mul_factorial (n := n) (k := m.1) (by omega)
  rw [show n - m.1 = m.2 by omega] at h
  have h' : (n.choose m.1 : C) * m.1.factorial * m.2.factorial = n.factorial := by
    exact_mod_cast h
  have h1 : (m.1.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (m.2.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : (n.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  linear_combination h'
end GlobalTheory.NearlyPrimitive
