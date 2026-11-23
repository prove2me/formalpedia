-- Prove2me | solution 1 for GlobalTheory.BadShare.eq_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:47.039871+00:00
-- url     : https://prove2.me/submissions/06d46c09-562e-4d53-8e50-12a9ae7651cc

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
example : BB 7 1 3 := bb_of_dvd (d := 1) (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num)
example : ¬ BB 7 1 6 := by
  rw [bb_iff]; norm_num
section part
variable {k : Type} [Field k] {l : ℕ}
open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem pow_eq_pow_of_modEq_orderOf' {G : Type*} [Monoid G] {x : G} {a b : ℕ}
    (h : a ≡ b [MOD orderOf x]) : x ^ a = x ^ b := by
  rw [← pow_mod_orderOf, show a % orderOf x = b % orderOf x from h, pow_mod_orderOf]
end part
variable {g}
example : torusCard g X = g - 1 := by rw [torusCard_irreducible irreducible_X]; simp
end GlobalTheory.BadShare
end
end

set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {k : Type} [Field k] {l : ℕ}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {k : Type} [Field k] {l : ℕ}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution {M a : ℕ} (hM : M.Coprime l) {x y : k} (hx : x ^ M = 1)
    (hy : y ^ M = 1) (hM0 : M ≠ 0) (h : x ^ (l ^ a) = y ^ (l ^ a)) : x = y := by
  haveI : NeZero M := ⟨hM0⟩
  have hs : l ^ a * ((l ^ a : ℕ) : ZMod M)⁻¹.val ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (hM.symm.pow_left a)
  have key : ∀ z : k, z ^ M = 1 → (z ^ (l ^ a)) ^ ((l ^ a : ℕ) : ZMod M)⁻¹.val = z := by
    intro z hz
    rw [← pow_mul]
    conv_rhs => rw [← pow_one z]
    exact pow_eq_pow_of_modEq_orderOf' (hs.of_dvd (orderOf_dvd_of_pow_eq_one hz))
  rw [← key x hx, ← key y hy, h]
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
