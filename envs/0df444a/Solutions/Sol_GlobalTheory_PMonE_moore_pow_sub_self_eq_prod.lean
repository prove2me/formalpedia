-- Prove2me | solution 1 for GlobalTheory.PMonE.moore_pow_sub_self_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:40.006186+00:00
-- url     : https://prove2.me/submissions/0d65e36e-9d81-4e9e-806b-54ea3855acad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Polynomial
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (x : F) :
    x ^ p - x = ∏ c : ZMod p, (x - ((c.val : ℕ) : F)) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast hp
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hroots, hdeg]; simp)
  rw [hroots] at h
  have h2 : (X ^ p - X : (ZMod p)[X]) = ∏ c : ZMod p, (X - C c) := by
    rw [← h]; rfl
  have h3 := congrArg (Polynomial.aeval x) h2
  simp only [map_sub, map_pow, aeval_X, map_prod, aeval_C] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 1
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [map_natCast]
end GlobalTheory.PMonE
