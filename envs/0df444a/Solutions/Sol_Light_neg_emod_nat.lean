-- Prove2me | solution 1 for Light.neg_emod_nat
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:33:52.10205+00:00
-- url     : https://prove2.me/submissions/4d8a4665-08d9-42d5-8b1d-e5fba3dd2802

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}
namespace Emod










end Emod
























































/-- The remainder of a negative number. -/
theorem neg_emod_nat_sourceProof (a M : ℕ) (hM : 1 ≤ M) :
    (-(a : ℤ)) % (M : ℤ) = if a % M = 0 then 0 else (M : ℤ) - ((a % M : ℕ) : ℤ) := by
  have h : (a : ℤ) = (M : ℤ) * ((a / M : ℕ) : ℤ) + ((a % M : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod a M).symm
  have hlt : a % M < M := Nat.mod_lt _ (by omega)
  split_ifs with h0
  · rw [h0] at h
    rw [h, Nat.cast_zero, add_zero, ← mul_neg]
    exact Int.mul_emod_right _ _
  · have e : -(a : ℤ) = ((M : ℤ) - ((a % M : ℕ) : ℤ)) + (M : ℤ) * (-((a / M : ℕ) : ℤ) - 1) := by
      rw [h]
      push_cast
      ring
    rw [e, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
namespace Emod













variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}










































































































































end Emod

end Light

end
end


theorem solution : ∀ (a M : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @Eq.{1} Int
      (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
        (@Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt a)) (@Nat.cast.{0} Int instNatCastInt M))
      (@ite.{1} Int
        (@Eq.{1} Nat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a M)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (instDecidableEqNat (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a M)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) (@Nat.cast.{0} Int instNatCastInt M)
          (@Nat.cast.{0} Int instNatCastInt (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a M)))) := by
  exact @Light.neg_emod_nat_sourceProof

#print axioms solution
