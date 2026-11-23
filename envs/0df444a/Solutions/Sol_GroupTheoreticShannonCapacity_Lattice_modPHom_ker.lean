-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.modPHom_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:16.818451+00:00
-- url     : https://prove2.me/submissions/5d459ec4-b489-49a1-99f7-6f5ebc8fae3d

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (n : ℕ) (p : ℕ) [NeZero p] :
    (modPHom n p).ker = pZn n p := by
  ext v
  simp only [AddMonoidHom.mem_ker, modPHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · intro hv
    -- v i ≡ 0 (mod p) for all i, so p divides v i
    use fun i => v i / p
    ext i
    have h : (v i : ZMod p) = 0 := congrFun hv i
    have hdiv : (p : ℤ) ∣ v i := ZMod.intCast_zmod_eq_zero_iff_dvd (v i) p |>.mp h
    have heq := Int.ediv_mul_cancel hdiv
    linarith
  · intro ⟨x, hv⟩
    ext i
    rw [hv, Pi.zero_apply]
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
end GroupTheoreticShannonCapacity.Lattice
