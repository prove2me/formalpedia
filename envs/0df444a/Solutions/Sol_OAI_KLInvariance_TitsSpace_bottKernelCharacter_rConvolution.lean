-- Prove2me | solution 1 for OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:24:11.369169+00:00
-- url     : https://prove2.me/submissions/15e71c87-4529-494c-acf2-7fb4c1333eab

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K023
import Theorems.Thm_OAI_KLInvariance_TitsSpace_bottStalkCharacter_ascent
import Theorems.Thm_OAI_KLInvariance_TitsSpace_bottStalkCharacter_descent
import Theorems.Thm_OAI_KLInvariance_TitsSpace_bottStalkCharacter_nil

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Hecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hecke and Laurent actions, braid independence, bar involution, triangular support and inverse coefficients.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


namespace Hecke

variable {C : Type*} [CommRing C]

theorem simple_mul_le_ascent (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatLE cs x y) (hy : cs.length y < cs.length (cs.simple i * y)) :
    BruhatLE cs (cs.simple i * x) (cs.simple i * y) := by
  have hx := le_upperSimple cs i (cs.simple i * x)
  rw [upperSimple_mul] at hx
  have hm := upperSimple_mono cs i hxy
  simp only [upperSimple, ite_eq_right (show ¬cs.length (cs.simple i * y) < cs.length y by omega)] at hm
  exact hx.trans hm


end Hecke


namespace HeckeQ

open Hecke (Space basis end_ext)
variable {C : Type*} [CommRing C]

theorem left_right_commute (cs : CoxeterSystem M W) (q : C) (i j : B) :
    Commute (left cs q i) (right cs q j) := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, right_basis, left_basis]
  by_cases heq : cs.simple i * w = w * cs.simple j
  · have heq' : cs.simple i * (w * cs.simple j) = w := by rw [← heq]; simp
    have heq'' : cs.simple i * w * cs.simple j = w := by simpa [mul_assoc] using heq'
    by_cases h : cs.length (cs.simple i * w) < cs.length w
    · have h' : cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      have hn : ¬cs.length w < cs.length (cs.simple i * w) := by omega
      have hn' : ¬cs.length w < cs.length (w * cs.simple j) := heq ▸ hn
      simp [h', map_add, map_smul, heq', hn', heq]
    · have h' : ¬cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      have hl : cs.length w < cs.length (cs.simple i * w) := by
        have := cs.length_simple_mul w i; omega
      have hl' : cs.length w < cs.length (w * cs.simple j) := heq ▸ hl
      simp [h', heq', hl', heq]
  · have hl := left_descent_mul_simple_iff cs i j w heq
    have hr := right_descent_simple_mul_iff cs i j w heq
    have hr' : cs.length (cs.simple i * (w * cs.simple j)) <
        cs.length (cs.simple i * w) ↔ cs.length (w * cs.simple j) < cs.length w := by
      simpa only [mul_assoc] using hr
    by_cases hi : cs.length (cs.simple i * w) < cs.length w <;>
      by_cases hj : cs.length (w * cs.simple j) < cs.length w <;>
      simp only [hi, hj, ite_true, if_true, ite_false, if_false, map_add, map_smul,
        left_basis, right_basis, hl, hr', mul_assoc, smul_add, smul_smul] ;
      module

/-- Acting on the identity along q reduced word gives exactly its standard
basis element. -/
theorem leftWord_one (cs : CoxeterSystem M W) (q : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    leftWord cs q ω (basis 1) = basis (cs.wordProd ω) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : ¬cs.length (cs.simple i * cs.wordProd ω) < cs.length (cs.wordProd ω) := by
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    simp [Module.End.mul_apply, ih hω', hasc, cs.wordProd_cons]

theorem rightWord_one (cs : CoxeterSystem M W) (q : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    rightWord cs q ω (basis 1) = basis (cs.wordProd ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hlen : cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) =
        cs.length (cs.simple i * cs.wordProd ω) := by
      rw [← cs.length_inv (cs.simple i * cs.wordProd ω)]
      simp [mul_inv_rev]
    have hasc : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω)⁻¹ := by
      rw [hlen, cs.length_inv]
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hasc' : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω) := by simpa using hasc
    simp [Module.End.mul_apply, ih hω', hasc', cs.wordProd_cons, mul_inv_rev]

theorem commute_rightWord (cs : CoxeterSystem M W) (q : C)
    {f : Module.End C (Space W C)} (h : ∀ i, Commute f (right cs q i)) (ω : List B) :
    Commute f (rightWord cs q ω) := by
  apply Commute.list_prod_right
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact h i

/-- The regular right action is cyclic, with cyclic vector the identity. -/
theorem commuting_ext (cs : CoxeterSystem M W) (q : C)
    {f g : Module.End C (Space W C)}
    (hf : ∀ i, Commute f (right cs q i))
    (hg : ∀ i, Commute g (right cs q i))
    (h : f (basis 1) = g (basis 1)) : f = g := by
  apply end_ext
  intro w
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced w⁻¹
  have hw : rightWord cs q ω (basis 1) = basis w := by
    rw [rightWord_one cs q hω, ← heq, inv_inv]
  rw [← hw]
  have hf' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs q hf ω).eq
  have hg' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs q hg ω).eq
  simp only [Module.End.mul_apply] at hf' hg'
  rw [h] at hf'
  exact hf'.trans hg'.symm

theorem leftWord_commute_right (cs : CoxeterSystem M W) (q : C) (ω : List B) (i : B) :
    Commute (leftWord cs q ω) (right cs q i) := by
  apply Commute.list_prod_left
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact left_right_commute cs q j i


theorem leftWord_independent (cs : CoxeterSystem M W) (q : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    leftWord cs q ω = leftWord cs q η := by
  apply commuting_ext cs q (leftWord_commute_right cs q ω)
    (leftWord_commute_right cs q η)
  rw [leftWord_one cs q hω, leftWord_one cs q hη, heq]

theorem wordUnit_independent (cs : CoxeterSystem M W) (q : Cˣ) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    wordUnit cs q ω = wordUnit cs q η := by
  apply Units.ext
  simpa using leftWord_independent cs (q : C) hω hη heq

theorem standardUnit_word (cs : CoxeterSystem M W) (q : Cˣ) {ω : List B}
    (hω : cs.IsReduced ω) :
    standardUnit cs q (cs.wordProd ω) = wordUnit cs q ω := by
  apply wordUnit_independent cs q (Classical.choose_spec (cs.exists_isReduced _)).1 hω
  exact (Classical.choose_spec (cs.exists_isReduced _)).2.symm

@[simp] theorem standardUnit_one (cs : CoxeterSystem M W) (q : Cˣ) :
    standardUnit cs q 1 = 1 := by
  have h := standardUnit_word cs q (ω := []) (by simp [CoxeterSystem.IsReduced])
  simpa [wordUnit] using h

@[simp] theorem standardUnit_basis_one (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    (standardUnit cs q w).val (basis 1) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [standardUnit_word cs q hω, wordUnit_val, leftWord_one cs (q : C) hω]


theorem standardUnit_mul_simple (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W)
    (hasc : cs.length w < cs.length (w * cs.simple i)) :
    standardUnit cs q (w * cs.simple i) = standardUnit cs q w * unit cs q i := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (ω ++ [i]) := by
    unfold CoxeterSystem.IsReduced
    have := cs.length_mul_simple (cs.wordProd ω) i
    simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
      List.length_singleton]
    rw [← hω.eq]
    omega
  rw [← cs.wordProd_singleton i, ← cs.wordProd_append, standardUnit_word cs q hred,
    standardUnit_word cs q hω]
  simp [wordUnit, List.map_append, List.prod_append]

@[simp] theorem barBasis_one (cs : CoxeterSystem M W) (q : Cˣ) :
    barBasis cs q 1 = basis 1 := by simp [barBasis]

theorem barBasis_simple_mul_ascent (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W)
    (hasc : cs.length w < cs.length (cs.simple i * w)) :
    barBasis cs q (cs.simple i * w) = leftInv cs q i (barBasis cs q w) := by
  have hasc' : cs.length w⁻¹ < cs.length (w⁻¹ * cs.simple i) := by
    have hlen : cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
      rw [← cs.length_inv (cs.simple i * w)]
      simp [mul_inv_rev]
    simpa [hlen] using hasc
  simp only [barBasis, mul_inv_rev, cs.inv_simple,
    standardUnit_mul_simple cs q i w⁻¹ hasc', Units.val_mul,
    Module.End.mul_apply]
  rfl


theorem leftInv_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W) :
    leftInv cs q i (barBasis cs q w) =
      if cs.length (cs.simple i * w) < cs.length w then
        (↑q⁻¹ : C) • barBasis cs q (cs.simple i * w) +
          ((↑q⁻¹ : C) - 1) • barBasis cs q w
      else barBasis cs q (cs.simple i * w) := by
  by_cases h : cs.length (cs.simple i * w) < cs.length w
  · have hasc : cs.length (cs.simple i * w) <
        cs.length (cs.simple i * (cs.simple i * w)) := by simpa using h
    have hb := barBasis_simple_mul_ascent cs q i (cs.simple i * w) hasc
    simp only [cs.simple_mul_simple_cancel_left] at hb
    have hl : left cs (q : C) i (barBasis cs q w) = barBasis cs q (cs.simple i * w) := by
      rw [hb, ← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
    rw [ite_eq_left h, leftInv_apply, hl, smul_sub, smul_smul]
    have hscalar : (↑q⁻¹ : C) * ((q : C) - 1) = 1 - (↑q⁻¹ : C) := by
      rw [mul_sub, q.inv_mul, mul_one]
    rw [hscalar, sub_smul, one_smul]
    module
  · have hasc : cs.length w < cs.length (cs.simple i * w) := by
      have := cs.length_simple_mul w i
      omega
    rw [ite_eq_right h, barBasis_simple_mul_ascent cs q i w hasc]

/-- Linear intertwining, before specializing coefficients to a Laurent ring. -/
theorem barLinear_left (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    barLinear cs q * left cs (↑q⁻¹ : C) i = leftInv cs q i * barLinear cs q := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, left_basis, leftInv_barBasis, barLinear_basis]
  split_ifs <;> simp

theorem leftInv_coeff (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (v : Space W C) (x : W) :
    leftInv cs q i v x =
      if cs.length (cs.simple i * x) < cs.length x then (↑q⁻¹ : C) * v (cs.simple i * x)
      else v (cs.simple i * x) + ((↑q⁻¹ : C) - 1) * v x := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add, Finsupp.add_apply, hv, hv']
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c = c • (basis w : Space W C) := by
      simp [basis, Finsupp.smul_single]
    rw [hc, map_smul, leftInv_basis]
    by_cases h : w = cs.simple i * x
    · subst w
      have hd : cs.length (cs.simple i * (cs.simple i * x)) < cs.length (cs.simple i * x) ↔
          ¬ cs.length (cs.simple i * x) < cs.length x := by
        simp only [cs.simple_mul_simple_cancel_left]
        have := cs.length_simple_mul x i
        omega
      have hn : cs.simple i * x ≠ x := by
        intro he
        have := cs.length_simple_mul x i
        rw [he] at this
        omega
      simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
        cs.simple_mul_simple_cancel_left, hn, ite_false, if_false]
      have hlength := cs.length_simple_mul x i
      split_ifs <;> try omega
      all_goals simp [Ne.symm hn] <;> try ring
    · have hn : cs.simple i * w ≠ x := by
        intro he
        apply h
        rw [← he]
        simp
      by_cases hw : w = x
      · subst w
        simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
          Ne.symm hn, ite_false, if_false, ]
        split_ifs <;> simp [Ne.symm hn] ; try ring
      · simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
          h, hw, ite_false, if_false]
        split_ifs <;> simp [hn, hw]

/-- Triangularity in the actual Bruhat order. -/
theorem barBasis_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (hxy : ¬BruhatLE cs x y) : barBasis cs q y x = 0 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω generalizing x with
  | nil =>
    have hx : x ≠ 1 := fun h => hxy (h ▸ bruhat_refl cs 1)
    simp [basis, Ne.symm hx]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hle : BruhatLE cs (cs.wordProd ω) (cs.simple i * cs.wordProd ω) :=
      Relation.ReflTransGen.single ⟨hasc, cs.simple i, cs.isReflection_simple i, rfl⟩
    have hn : ¬BruhatLE cs x (cs.wordProd ω) := fun h => hxy (h.trans hle)
    have hn' : ¬BruhatLE cs (cs.simple i * x) (cs.wordProd ω) := by
      intro h
      have := Hecke.simple_mul_le_ascent cs i h hasc
      simp only [cs.simple_mul_simple_cancel_left] at this
      exact hxy this
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q i _ hasc, leftInv_coeff,
      ih x hω' hn, ih (cs.simple i * x) hω' hn']
    split_ifs <;> simp

@[simp] theorem barBasis_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (y : W) :
    barBasis cs q y y = (↑q⁻¹ : C) ^ cs.length y := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω with
  | nil => simp [basis]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hlen : cs.length (cs.simple i * cs.wordProd ω) = cs.length (cs.wordProd ω) + 1 := by
      have := cs.length_simple_mul (cs.wordProd ω) i
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q i _ hasc, leftInv_coeff]
    rw [cs.simple_mul_simple_cancel_left, ite_eq_left hasc, ih hω', hlen, pow_succ]
    ring

@[simp] theorem rValue_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (x : W) :
    rValue cs q x x = 1 := by
  rw [rValue, barBasis_diagonal, ← mul_pow, ← mul_pow]
  simp

theorem rValue_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (hxy : ¬BruhatLE cs x y) : rValue cs q x y = 0 := by
  rw [rValue, barBasis_zero cs q x y hxy, mul_zero]

/-- The classical R recursion holds for *every* left descent, by Hecke
operator independence. This is the consistency obligation for actual R. -/
theorem rValue_recursion (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    rValue cs q x y =
      if cs.length (cs.simple i * x) < cs.length x then
        rValue cs q (cs.simple i * x) (cs.simple i * y)
      else ((q : C) - 1) * rValue cs q x (cs.simple i * y) +
        (q : C) * rValue cs q (cs.simple i * x) (cs.simple i * y) := by
  have hasc : cs.length (cs.simple i * y) <
      cs.length (cs.simple i * (cs.simple i * y)) := by simpa using hy
  have hb := barBasis_simple_mul_ascent cs q i (cs.simple i * y) hasc
  simp only [cs.simple_mul_simple_cancel_left] at hb
  have hylen : cs.length y = cs.length (cs.simple i * y) + 1 := by
    have := cs.length_simple_mul y i
    omega
  have hu : (q : C) * (↑q⁻¹ : C) = 1 := q.val_inv
  by_cases hx : cs.length (cs.simple i * x) < cs.length x
  · have hxlen : cs.length x = cs.length (cs.simple i * x) + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [ite_eq_left hx]
    simp only [rValue, hb, leftInv_coeff, ite_eq_left hx]
    rw [hxlen, hylen]
    simp only [pow_succ]
    linear_combination ((-1 : C) ^ cs.length (cs.simple i * x) *
      (-(q : C)) ^ cs.length (cs.simple i * y) *
      barBasis cs q (cs.simple i * y) (cs.simple i * x)) * hu
  · have hxlen : cs.length (cs.simple i * x) = cs.length x + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [ite_eq_right hx]
    simp only [rValue, hb, leftInv_coeff, ite_eq_right hx]
    rw [hxlen, hylen]
    simp only [pow_succ]
    linear_combination -((-1 : C) ^ cs.length x *
      (-(q : C)) ^ cs.length (cs.simple i * y) *
      barBasis cs q (cs.simple i * y) x) * hu

end HeckeQ

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions
/-- Reflection of a bounded-degree polynomial evaluated at an actual unit. -/
theorem eval₂_reflect_unit {C : Type*} [CommRing C] (q : Cˣ)
    (p : ℤ[X]) (d : ℕ) (hp : p.natDegree ≤ d) :
    Polynomial.eval₂ (Int.castRingHom C) (q : C) (reflect d p) =
      (q : C) ^ d * Polynomial.eval₂ (Int.castRingHom C) (↑q⁻¹ : C) p := by
  let := q⁻¹.invertible
  have h := Polynomial.eval₂_reflect_mul_pow (Int.castRingHom C) (↑q⁻¹ : C) d p hp
  simp only [invOf_units, inv_inv] at h
  have h' := congrArg (fun a : C => a * (q : C) ^ d) h
  calc
    _ = Polynomial.eval₂ (Int.castRingHom C) (↑q⁻¹ : C) p * (q : C) ^ d := by
      simpa only [mul_assoc, ← mul_pow, q.inv_mul, one_pow, mul_one] using h'
    _ = _ := mul_comm _ _


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_OrdinaryR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Construction of ordinary R-polynomials, left-simple recursion, degree bounds and inverse kernels.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

namespace OrdinaryR

open LaurentPolynomial

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_1
/-- Polynomiality of the R-values is proved from the Hecke-derived recursion. -/
theorem rValue_polynomial (cs : CoxeterSystem M W) (x y : W) :
    ∃ p : ℤ[X], p.toLaurent = HeckeQ.rValue cs variableUnit x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      ∃ p : ℤ[X], p.toLaurent = HeckeQ.rValue cs variableUnit x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x
        exact ⟨1, by simp⟩
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        exact ⟨0, by rw [HeckeQ.rValue_zero cs _ _ _ hn]; simp⟩
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      obtain ⟨p, hp⟩ := ih _ hlt _ rfl x
      obtain ⟨r, hr⟩ := ih _ hlt _ rfl (cs.simple i * x)
      rw [HeckeQ.rValue_recursion cs variableUnit x y i hi]
      split_ifs
      · exact ⟨r, hr⟩
      · refine ⟨(X - 1) * p + X * r, ?_⟩
        simp [hp, hr]

@[simp] theorem toLaurent_polynomial (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).toLaurent = HeckeQ.rValue cs variableUnit x y := by
  obtain ⟨p, hp⟩ := rValue_polynomial cs x y
  rw [polynomial, ← hp, Polynomial.trunc_toLaurent]

@[simp] theorem polynomial_diagonal (cs : CoxeterSystem M W) (x : W) :
    polynomial cs x x = 1 := by
  apply Polynomial.toLaurent_injective
  simp

theorem polynomial_zero (cs : CoxeterSystem M W) (x y : W)
    (hxy : ¬ BruhatLE cs x y) : polynomial cs x y = 0 := by
  apply Polynomial.toLaurent_injective
  simp [HeckeQ.rValue_zero cs _ x y hxy]

theorem polynomial_recursion (cs : CoxeterSystem M W) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    polynomial cs x y =
      if cs.length (cs.simple i * x) < cs.length x then
        polynomial cs (cs.simple i * x) (cs.simple i * y)
      else (X - 1) * polynomial cs x (cs.simple i * y) +
        X * polynomial cs (cs.simple i * x) (cs.simple i * y) := by
  apply Polynomial.toLaurent_injective
  rw [toLaurent_polynomial, HeckeQ.rValue_recursion cs variableUnit x y i hy]
  split_ifs <;> simp

/-- Specializing the honest integral polynomial recovers the Hecke R-value
at every unit parameter, not just the Laurent indeterminate. -/
theorem polynomial_eval {C : Type*} [CommRing C] (cs : CoxeterSystem M W)
    (q : Cˣ) (x y : W) :
    Polynomial.eval₂ (Int.castRingHom C) (q : C) (polynomial cs x y) =
      HeckeQ.rValue cs q x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      Polynomial.eval₂ (Int.castRingHom C) (q : C) (polynomial cs x y) =
        HeckeQ.rValue cs q x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x; simp
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [polynomial_zero cs _ _ hn, HeckeQ.rValue_zero cs _ _ _ hn]
        simp
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [polynomial_recursion cs x y i hi, HeckeQ.rValue_recursion cs q x y i hi]
      split_ifs
      · exact ih _ hlt _ rfl (cs.simple i * x)
      · simp [ih _ hlt _ rfl x, ih _ hlt _ rfl (cs.simple i * x)]

end OrdinaryR


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Dihedral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Interval restrictions, dihedral Coxeter and Hecke calculations, and the genuine square-parameter R normalization.
-/

section

namespace KLInvariance.HeckeQ

universe uR vR
variable {B : Type uR} {W : Type vR} [Group W] {M : CoxeterMatrix B}
variable {C : Type*} [CommRing C]

@[simp] theorem dualR_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (x : W) :
    dualR cs q x x = 1 := by
  rw [dualR, rValue_diagonal, mul_one, ← mul_pow]
  simp

theorem dualR_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (h : ¬BruhatLE cs x y) : dualR cs q x y = 0 := by
  simp [dualR, rValue_zero cs q⁻¹ x y h]

theorem dualR_recursion (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    dualR cs q x y =
      if cs.length (cs.simple i * x) < cs.length x then
        dualR cs q (cs.simple i * x) (cs.simple i * y)
      else ((q : C) - 1) * dualR cs q x (cs.simple i * y) +
        (q : C) * dualR cs q (cs.simple i * x) (cs.simple i * y) := by
  have hyl : cs.length y = cs.length (cs.simple i * y) + 1 := by
    have := cs.length_simple_mul y i
    omega
  unfold dualR
  rw [rValue_recursion cs q⁻¹ x y i hy]
  split_ifs with hx
  · have hxl : cs.length x = cs.length (cs.simple i * x) + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [hyl, hxl, pow_succ, pow_succ]
    calc
      _ = (-(q:C)) ^ cs.length (cs.simple i * y) *
          (-(↑q⁻¹:C)) ^ cs.length (cs.simple i * x) *
          rValue cs q⁻¹ (cs.simple i * x) (cs.simple i * y) *
          ((q:C) * (↑q⁻¹:C)) := by ring
      _ = _ := by rw [q.mul_inv, mul_one]
  · have hxl : cs.length (cs.simple i * x) = cs.length x + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [hyl, hxl, pow_succ, pow_succ]
    have hq : (-(q:C)) * ((↑q⁻¹:C) - 1) = (q:C) - 1 := by
      rw [mul_sub, neg_mul, q.mul_inv, mul_one]
      ring
    calc
      _ = (-(q:C)) ^ cs.length (cs.simple i * y) *
          (-(↑q⁻¹:C)) ^ cs.length x *
          ((-(q:C)) * ((↑q⁻¹:C) - 1)) * rValue cs q⁻¹ x (cs.simple i * y) +
          (q:C) * ((-(q:C)) ^ cs.length (cs.simple i * y) *
          ((-(↑q⁻¹:C)) ^ cs.length x * (-(↑q⁻¹:C))) *
          rValue cs q⁻¹ (cs.simple i * x) (cs.simple i * y)) := by ring
      _ = _ := by rw [hq]; ring

/-- Signed inversion symmetry of actual equal-parameter R-values, proved
from all-descent recurrence, not imposed as an additional normalization. -/
theorem rValue_eq_dualR (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    rValue cs q x y = dualR cs q x y := by
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      rValue cs q x y = dualR cs q x y by
    exact this _ y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases hy1 : y = 1
    · subst y
      by_cases hx1 : x = 1
      · subst x
        simp
      · have hnot : ¬BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hl0 : cs.length x = 0 := by simpa using hl
          exact hx1 (cs.length_eq_zero_iff.mp hl0)
        rw [rValue_zero cs q x 1 hnot, dualR_zero cs q x 1 hnot]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hy1
      have hsmall : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [rValue_recursion cs q x y i hi, dualR_recursion cs q x y i hi,
        ih _ hsmall _ rfl x, ih _ hsmall _ rfl (cs.simple i * x)]

/-- R at the inverse parameter is exactly the corresponding bar coefficient
with the bottom q-power. This is the coefficient form used below. -/
theorem rValue_inverse_eq_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    rValue cs q⁻¹ x y = (q:C) ^ cs.length x * barBasis cs q y x := by
  rw [rValue_eq_dualR cs q⁻¹, dualR, inv_inv, rValue]
  simp only [neg_pow (↑q⁻¹:C), neg_pow (q:C)]
  have hsign (n : ℕ) : (-1:C)^n * (-1:C)^n = 1 := by
    rw [← mul_pow]; simp
  calc
    _ = ((-1:C)^cs.length y * (-1:C)^cs.length y) *
        ((-1:C)^cs.length x * (-1:C)^cs.length x) *
        (((↑q⁻¹:C) * (q:C)) ^ cs.length y) *
        (q:C)^cs.length x * barBasis cs q y x := by ring
    _ = _ := by rw [hsign, hsign, q.inv_mul]; simp

end KLInvariance.HeckeQ

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_HilbertSeries
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.Graded.piPiece_finite _root_.OAI.KLInvariance.Graded.subPiece_finite _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert series of graded modules and boundary sheaves, positivity and strict detection.
-/

section

namespace KLInvariance.Hilbert

/-- Sum over all monomials in finitely many variables, before grouping by degree. -/
theorem hasSum_monomials (σ : Type*) [Fintype σ] {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ) := by
  classical
  apply Fintype.induction_empty_option (P := fun σ _ =>
    HasSum (fun d : σ → ℕ => q ^ (∑ i, d i)) ((1-q)⁻¹ ^ Fintype.card σ))
  · intro α β _ e ih
    let : Fintype α := Fintype.ofEquiv β e.symm
    rw [← Fintype.card_congr e]
    apply (Equiv.piCongrLeft (fun _ : β => ℕ) e).hasSum_iff.mp
    convert ih using 1
    all_goals try with_reducible_and_instances rfl
    ext d
    simp only [Function.comp_apply, Equiv.piCongrLeft_apply]
    congr 1
    simpa using e.symm.sum_comp d
  · simp
  · intro α _ ih
    have hg := hasSum_geometric_of_lt_one hq hq1
    have hs := hg.summable.mul_of_nonneg ih.summable
      (fun _ => pow_nonneg hq _) (fun _ => pow_nonneg hq _)
    have hh := hg.mul ih hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hh
    simpa [Function.comp_def, Fintype.sum_option, pow_add, pow_succ, mul_comm] using he


lemma intWeight_eq_natWeight {σ : Type*} (d : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d =
      (Finsupp.weight (fun _ : σ => (1 : ℕ)) d : ℕ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]

lemma polynomialGrading_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Graded.polynomialGrading k σ n =
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => (1 : ℕ)) n := by
  ext p
  change (∀ d, p.coeff d ≠ 0 →
    Finsupp.weight (fun _ : σ => (1 : ℤ)) d = (n : ℤ)) ↔ _
  simp only [intWeight_eq_natWeight, Nat.cast_inj]
  rfl

instance polynomialPiece_finite (k : Type*) [Field k] (σ : Type*) [Finite σ] (n : ℤ) :
    Module.Finite k (Graded.polynomialGrading k σ n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [polynomialGrading_nat]
    exact Module.Finite.iff_fg.mpr
      (MvPolynomial.weightedHomogeneousSubmodule_fg k (fun _ : σ => 1) (by simp) m)
  · rw [Graded.polynomialGrading_negative k σ n (lt_of_not_ge hn)]
    infer_instance

lemma polynomial_finrank_nat (k : Type*) [Field k] (σ : Type*) (n : ℕ) :
    Module.finrank k (Graded.polynomialGrading k σ n) =
      Nat.card {d : σ →₀ ℕ // Finsupp.weight (fun _ => (1 : ℕ)) d = n} := by
  rw [polynomialGrading_nat, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport k _)

lemma hasSum_finsupp_monomials (σ : Type*) [Fintype σ] {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun d : σ →₀ ℕ => q ^ Finsupp.weight (fun _ => (1 : ℕ)) d)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).hasSum_iff.mpr
    (hasSum_monomials σ hq hq1)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext d
  congr 1
  simp only [Finsupp.weight_apply, smul_eq_mul, mul_one]
  exact Finsupp.sum_fintype d _ (by simp)

/-- The actual finite polynomial ring has Hilbert series `(1-q)⁻ᴺ`. -/
theorem hasSum_polynomial_nat (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  have h := (hasSum_finsupp_monomials σ hq hq1).tsum_fiberwise
    (Finsupp.weight (fun _ : σ => (1 : ℕ)))
  apply h.congr_fun
  intro n
  rw [polynomial_finrank_nat]
  have hf : (fun d : ↑((Finsupp.weight (R := ℕ) (fun _ : σ => (1 : ℕ))) ⁻¹' {n}) =>
      q ^ (Finsupp.weight (fun _ : σ => (1 : ℕ))) d.val) = fun _ => q^n := by
    funext d
    rw [show Finsupp.weight (fun _ : σ => (1 : ℕ)) d.val = n from d.property]
  rw [hf, tsum_const, nsmul_eq_mul]
  simp only [Set.preimage, Set.mem_singleton_iff]
  rfl


/-- Integer-indexed grading, including its zero negative pieces. -/
theorem hasSum_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ n) : ℝ) * q^n)
      ((1-q)⁻¹ ^ Fintype.card σ) := by
  apply ((Nat.cast_injective : Function.Injective ((↑) : ℕ → ℤ)).hasSum_iff ?_).mp
  · simpa only [Function.comp_def, zpow_natCast] using hasSum_polynomial_nat k σ hq hq1
  · intro n hn
    have hn' : n < 0 := by
      by_contra h
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt h)
      exact hn ⟨m, rfl⟩
    rw [Graded.polynomialGrading_negative k σ n hn']
    simp

end KLInvariance.Hilbert


end


section

namespace KLInvariance.Hilbert
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

lemma shiftedPiece_finrank {ι : Type ui} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) [∀ n, Module.Finite k (𝓐 n)] (d : ι → ℤ) (n : ℤ) :
    Module.finrank k (Graded.shiftedPiece 𝓐 d n) = ∑ i, Module.finrank k (𝓐 (n-d i)) := by
  rw [(shiftedPieceEquiv 𝓐 d n).finrank_eq, Module.finrank_pi_fintype]

lemma hasSum_shifted_polynomial (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    (d : ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (Graded.polynomialGrading k σ (n-d)) : ℝ) * q^n)
      (q^d * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (Equiv.addRight d).hasSum_iff.mp
  have h := (hasSum_polynomial k σ hq.le hq1).mul_left (q^d)
  apply h.congr_fun
  intro n
  change (Module.finrank k (Graded.polynomialGrading k σ (n+d-d)) : ℝ) * q^(n+d) = _
  rw [add_sub_cancel_right, zpow_add₀ hq.ne']
  ring

/-- Convergent Hilbert series and its normalization for the actual shifted free module. -/
theorem hasSum_shiftedFree (k : Type*) [Field k] (σ : Type*) [Fintype σ]
    {ι : Type*} [Fintype ι] (d : ι → ℤ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ =>
      (Module.finrank k (Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) : ℝ) * q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  have h := hasSum_sum (s := Finset.univ)
    (fun i _ => hasSum_shifted_polynomial k σ (d i) hq hq1)
  rw [← Finset.sum_mul] at h
  apply h.congr_fun
  intro n
  rw [shiftedPiece_finrank, Nat.cast_sum, Finset.sum_mul]


section FiniteModule
variable {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

lemma degreeMap_surjective
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (hs : Function.Surjective f) (n : ℤ) : Function.Surjective (degreeMap 𝓜 𝓝 f hf n) := by
  intro m
  obtain ⟨v,hv⟩ := hs m.val
  refine ⟨DirectSum.decompose 𝓜 v n, ?_⟩
  apply Subtype.ext
  change f (Graded.component 𝓜 n v) = m.val
  have h := Graded.map_component 𝓜 𝓝 f 0 (by simpa using hf) n v
  rw [sub_zero, hv] at h
  exact h.symm.trans (DirectSum.decompose_of_mem_same 𝓝 m.property)
end FiniteModule

section HomogeneousBasis
variable {σ : Type ua} [Fintype σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (Graded.polynomialGrading k σ) 𝓜]
  {ι : Type ui} [Fintype ι] (b : Module.Basis ι (MvPolynomial σ k) M)
  (d : ι → ℤ) (hd : ∀ i, b i ∈ 𝓜 (d i))

include hd

omit [Fintype σ] [IsScalarTower k (MvPolynomial σ k) M] [DirectSum.Decomposition 𝓜] in
lemma basis_equivFun_symm_graded (n : ℤ) (v : ι → MvPolynomial σ k)
    (hv : v ∈ Graded.shiftedPiece (Graded.polynomialGrading k σ) d n) :
    b.equivFun.symm v ∈ 𝓜 n := by
  rw [b.equivFun_symm_apply]
  apply Submodule.sum_mem
  intro i _
  simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i)

lemma finrank_homogeneous_basis (n : ℤ) :
    Module.finrank k (𝓜 n) =
      ∑ i, Module.finrank k (Graded.polynomialGrading k σ (n-d i)) := by
  let : DirectSum.Decomposition (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) :=
    (Graded.shifted_isInternal (Graded.polynomialGrading k σ) d).chooseDecomposition
  let f := degreeMap (Graded.shiftedPiece (Graded.polynomialGrading k σ) d) 𝓜
    b.equivFun.symm.toLinearMap (basis_equivFun_symm_graded 𝓜 b d hd) n
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply b.equivFun.symm.injective
      exact congrArg Subtype.val h
    · exact degreeMap_surjective _ _ b.equivFun.symm.toLinearMap
        (basis_equivFun_symm_graded 𝓜 b d hd) b.equivFun.symm.surjective n
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  exact shiftedPiece_finrank _ d n

/-- The precise Hilbert normalization for a finite homogeneous basis, with the source's
convention that a generator in degree `d` contributes `q^d`. -/
theorem hasSum_homogeneous_basis {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      ((∑ i, q^(d i)) * (1-q)⁻¹ ^ Fintype.card σ) := by
  apply (hasSum_shiftedFree k σ d hq hq1).congr_fun
  intro n
  rw [finrank_homogeneous_basis 𝓜 b d hd, shiftedPiece_finrank]
end HomogeneousBasis


end KLInvariance.Hilbert


end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottPolynomialStalkFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/

section

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M : Type um} [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (polynomialGrading k σ) 𝓜]

attribute [instance] NonnegativeBasis.finite

namespace NonnegativeBasis
variable {𝓜} (b : NonnegativeBasis (σ := σ) 𝓜)

omit [Finite σ] [IsScalarTower k (MvPolynomial σ k) M]
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul (polynomialGrading k σ) 𝓜] in
lemma eval₂_eq (q : ℝ) : Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial =
    ∑ i, q ^ b.degree i := by
  change (Polynomial.eval₂RingHom (Int.castRingHom ℝ) q) (∑ i, X ^ b.degree i) = _
  simp

omit [Finite σ] in
lemma hasSum [Fintype σ] {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℤ => (Module.finrank k (𝓜 n) : ℝ)*q^n)
      (Polynomial.eval₂ (Int.castRingHom ℝ) q b.polynomial * (1-q)⁻¹ ^ Fintype.card σ) := by
  rw [b.eval₂_eq]
  convert Hilbert.hasSum_homogeneous_basis 𝓜 b.basis (fun i => (b.degree i : ℤ))
    b.homogeneous hq hq1 using 1
  all_goals try with_reducible_and_instances rfl
  simp

lemma polynomial_eq (c : NonnegativeBasis (σ := σ) 𝓜) : b.polynomial = c.polynomial := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {q | Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))} := by
    intro q hq
    have h := (b.hasSum hq.1 hq.2).unique (c.hasSum hq.1 hq.2)
    have hne : (1-q)⁻¹ ^ Fintype.card σ ≠ 0 := pow_ne_zero _ (inv_ne_zero (sub_ne_zero.mpr (ne_of_gt hq.2)))
    change Polynomial.eval q (b.polynomial.map (Int.castRingHom ℝ)) =
      Polynomial.eval q (c.polynomial.map (Int.castRingHom ℝ))
    simpa only [Polynomial.eval_map] using mul_right_cancel₀ hne h
  exact Set.Infinite.mono hsub (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num))

end NonnegativeBasis

lemma character_eq [Module.Free (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M] (hneg : ∀ n < 0, 𝓜 n = ⊥)
    (b : NonnegativeBasis (σ := σ) 𝓜) : character (σ := σ) 𝓜 hneg = b.polynomial :=
  (exists_nonnegativeBasis (σ := σ) 𝓜 hneg).some.polynomial_eq b

end KLInvariance.Graded

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! The genuine Bott--Samelson stalk Hilbert coefficients satisfy the simple
reflection ascent recurrence. Both exactness and the degree-one kernel shift
were constructed integrally above; no KL character theorem is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 instance symmetricGrading_finite (n : ℤ) : Module.Finite ℝ (symmetricGrading basis n) :=
  inferInstanceAs (Module.Finite ℝ ((polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap))

 instance bottCoordinatePiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottCoordinatePiece cs basis l x n) := by
  classical
  exact piPiece_finite _ n

 instance bottStalkPiece_finite (l : List I) (x : W) (n : ℤ) :
    Module.Finite ℝ (bottStalkPiece cs basis l x n) :=
  inferInstanceAs (Module.Finite ℝ (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x) n))

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

/-! The honest unnormalized Hecke word (T_s+1)...(T_t+1), including exact
coefficient recurrence over a general commutative ring, without invertibility
of q or any KL/BMP character assertion. -/
namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem left_coeff (cs : CoxeterSystem M W) (q : C) (i : I) (v : Space W C) (x : W) :
    left cs q i v x =
      if cs.length (cs.simple i*x) < cs.length x then v (cs.simple i*x)+(q-1)*v x
      else q*v (cs.simple i*x) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add,Finsupp.add_apply,hv,hv']
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c=c • (basis w : Space W C) := by
      simp [basis,Finsupp.smul_single]
    rw [hc,map_smul,left_basis]
    by_cases h : w=cs.simple i*x
    · subst w
      have hd : cs.length (cs.simple i*(cs.simple i*x)) < cs.length (cs.simple i*x) ↔
          ¬cs.length (cs.simple i*x) < cs.length x := by
        simp only [cs.simple_mul_simple_cancel_left]
        have := cs.length_simple_mul x i
        omega
      have hn : cs.simple i*x≠x := by
        intro he
        have := cs.length_simple_mul x i
        rw [he] at this
        omega
      simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
        cs.simple_mul_simple_cancel_left,hn,ite_false, if_false]
      have hlength := cs.length_simple_mul x i
      split_ifs <;> try omega
      all_goals simp [Ne.symm hn] <;> try ring
    · have hn : cs.simple i*w≠x := by
        intro he
        apply h
        rw [←he]
        simp
      by_cases hw : w=x
      · subst w
        simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
          Ne.symm hn,ite_false, if_false]
        split_ifs <;> simp [Ne.symm hn] ; try ring
      · simp only [Finsupp.smul_apply,smul_eq_mul,basis,Finsupp.single_apply,
          h,hw,ite_false, if_false]
        split_ifs <;> simp [hn,hw]

 theorem left_plus_coeff (cs : CoxeterSystem M W) (q : C) (i : I)
    (v : Space W C) (x : W) :
    (v+left cs q i v) x = if cs.length (cs.simple i*x) < cs.length x then
      v (cs.simple i*x)+q*v x else v x+q*v (cs.simple i*x) := by
  rw [Finsupp.add_apply,left_coeff]
  split_ifs <;> ring

 theorem positiveWord_cons_coeff (cs : CoxeterSystem M W) (q : C) (i : I)
    (l : List I) (x : W) :
    positiveWord cs q (i::l) x = if cs.length (cs.simple i*x) < cs.length x then
      positiveWord cs q l (cs.simple i*x)+q*positiveWord cs q l x
      else positiveWord cs q l x+q*positiveWord cs q l (cs.simple i*x) :=
  left_plus_coeff cs q i (positiveWord cs q l) x

end
end KLInvariance.HeckeQ

end


section

/-! Genuine word stalk normalization and identification with the honest
Hecke word. This does not identify the indecomposable BMP character with KL. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_7
theorem bottStalkCharacter_eq_heckeWord (l : List I) (x : W) :
    bottStalkCharacter cs basis l x=HeckeQ.positiveWord cs (Polynomial.X : Polynomial ℤ) l x := by
  classical
  induction l generalizing x with
  | nil => simp only [bottStalkCharacter_nil,HeckeQ.positiveWord_nil,Hecke.basis,
      Finsupp.single_apply]; split_ifs <;> simp_all
  | cons i l ih =>
    rw [HeckeQ.positiveWord_cons_coeff]
    by_cases hd : cs.length (cs.simple i*x) < cs.length x
    · rw [ite_eq_left hd,bottStalkCharacter_descent cs basis i l x hd,ih,ih]
    · have ha : cs.length x < cs.length (cs.simple i*x) := by
        have := cs.length_simple_mul x i
        omega
      rw [ite_eq_right hd,bottStalkCharacter_ascent cs basis i l x ha,ih,ih]

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

/-! Genuine polynomial reflection from a homogeneous perfect duality. The
nonnegative lattice supplies a weak degree bound, not the strict KL bound. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 theorem char_of_dual_equiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N]
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l)) :
    N.char=Polynomial.reflect l M.char := by
  classical
  let c := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ (M.reflectedBasis N e l he c),char,character_eq _ _ c]
  change (∑ i : c.index, (X : Polynomial ℤ)^(l-c.degree i))=
    Polynomial.reflect l (∑ i : c.index, X^c.degree i)
  have hs (s : Finset c.index) : Polynomial.reflect l (∑ i∈s, (X : Polynomial ℤ)^c.degree i)=
      ∑ i∈s, Polynomial.reflect l (X^c.degree i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha,ih]
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.reflect_monomial,Polynomial.revAt_le (M.degree_le_of_dual_equiv N e l he c i)]

end
end KLInvariance.Graded.ModuleData

end


section


namespace KLInvariance.MomentGraph.GradedSheaf
open Module _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐]
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E] [DecidableEq V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)
  [IsNoetherianRing A] [IsDomain A]
  [∀ x, Module.IsTorsionFree A (B.forget.vertex x)]
  (α : E → A) (hα : ∀ e, α e ≠ 0) (ha : ∀ e (v : B.edge e), α e • v = 0)
  (p : B.forget.sections Set.univ ≃ₗ[A] Dual A (B.forget.sections Set.univ))
  (hbalanced : ∀ x m n,
    p (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x m) n =
    p m (IntegralSupport.cut (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha)) x n))
noncomputable section

 theorem dualToSupport_homogeneous (l : ℤ)
    (hp : ∀ i j (m n : B.sections Set.univ),
      m ∈ (B.sections Set.univ).piece i → n ∈ (B.sections Set.univ).piece j →
      p m n ∈ 𝓐 (i+j-l))
    (x : V) (r : ℤ) (lam : Dual A (B.vertex x))
    (hlam : ∀ j (v : B.vertex x), v ∈ (B.vertex x).piece j → lam v ∈ 𝓐 (j+r)) :
    (IntegralSupport.dualToSupport (B.forget.sections Set.univ) (Sheaf.labelProduct α)
      (B.forget.scaled_single_section (B.forget.labelProduct_annihilates α ha))
      (Sheaf.labelProduct_ne_zero α hα) p hbalanced x lam).val ∈
        (B.sections Set.univ).piece (r+l) := by
  apply perfect_inverse_of_homogeneous_functional 𝓐 (B.sections Set.univ).piece p l hp r
  intro j n hn
  exact hlam j (n.val x) (hn x (Set.mem_univ x))

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]

/-- Cancellation of an injective homogeneous scalar action includes the
inverse grading shift. It does not require the scalar to be a unit. -/
 theorem mem_of_homogeneous_smul (d : ℤ) (a : A) (ha : a ∈ 𝓐 d)
    (hinj : Function.Injective (fun m : M => a • m))
    (n : ℤ) (m : M) (hm : a • m ∈ 𝓜 n) : m ∈ 𝓜 (n-d) := by
  have hc : component 𝓜 (n-d) m = m := by
    apply hinj
    change a • component 𝓜 (n-d) m = a • m
    rw [← component_homogeneous_smul 𝓐 𝓜 d a ha]
    exact DirectSum.decompose_of_mem_same 𝓜 hm
  rw [← hc]
  exact (DirectSum.decompose 𝓜 m (n-d)).property

end KLInvariance.Graded

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [Fintype (Interval cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

omit [Fintype (Interval cs u b)] in
 theorem incomingProduct_homogeneous (x : Interval cs u b) :
    Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x ∈
      polynomialGrading ℝ σ ((Sheaf.incoming (G := graph cs u b) x).card : ℤ) := by
  simpa only [Sheaf.incomingProduct,Finset.sum_const,Int.natCast_one,mul_one,nsmul_eq_mul] using
    SetLike.prod_mem_graded (polynomialGrading ℝ σ) (fun _ : Edge cs u b => (1 : ℤ))
      (polynomialLabel cs u b basis)
      (F := Sheaf.incoming (G := graph cs u b) x)
      (fun e _ => polynomialLabel_homogeneous cs u b basis e)

end
end KLInvariance.BruhatGraph

end


section

/-! The degree of the actual incoming root product on [1,b].  This is not
asserted for truncated intervals with arbitrary bottom. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (b : W)
noncomputable section

 theorem incoming_card [Fintype (Edge cs 1 b)] [DecidableEq (Interval cs 1 b)]
    (x : Interval cs 1 b) : (Sheaf.incoming (G := graph cs 1 b) x).card = cs.length x.val := by
  classical
  calc
    _ = Nat.card {e : Edge cs 1 b // target cs 1 b e = x} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rfl
    _ = Nat.card {t : W // cs.IsLeftInversion x.val t} := Nat.card_congr (incomingEquivInversions cs b x)
    _ = Nat.card (RootInversions M cs x.val) := Nat.card_congr (rootInversionEquiv M cs x.val).symm
    _ = cs.length x.val := card_rootInversions M cs x.val

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! Integral costalk duality only uses free stalks, the genuine edge quotients,
generation and a perfect support-orthogonal section form. No top/minimality or
KL character assumption is needed. This extension applies to genuine words. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))

namespace FreeSheaf
variable (B : FreeSheaf cs u b basis)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section

 variable [Fintype σ] [Fintype (Interval cs u b)]

omit [Fintype σ] [Fintype (Interval cs u b)] in
 theorem kernelEquivSingleSupport_apply (x : Interval cs u b)
    (v : LinearMap.ker (B.sheaf.forget.stalkMap x)) :
    ((kernelEquivSingleSupport cs u b basis B x) v).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val := by
  change (Pi.single x
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x • v.val) :
      B.sheaf.forget.Assignment) x = _
  exact Pi.single_eq_same _ _

 theorem costalkEquivDual_inverse_homogeneous
    (d : SectionDuality cs u b basis B) (l : ℤ)
    (hd : ∀ i j (m n : B.sheaf.sections Set.univ),
      m ∈ (B.sheaf.sections Set.univ).piece i → n ∈ (B.sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-l))
    (x : Interval cs u b) (r : ℤ) (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v ∈ (B.sheaf.vertex x).piece j →
      lam v ∈ polynomialGrading ℝ σ (j+r)) :
    ((costalkEquivDual cs u b basis B d x).symm lam).val ∈
      (B.sheaf.vertex x).piece
        (r+l-(Sheaf.incoming (G := graph cs u b) x).card) := by
  let _ (y : Interval cs u b) : Module.Free (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := B.free y
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  let S := B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
    (polynomialLabel_ne_zero cs u b basis)
    (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
    d.pairing d.balanced B.generated x
  have hs : (S.symm lam).val ∈ (B.sheaf.sections Set.univ).piece (r+l) := by
    exact B.sheaf.dualToSupport_homogeneous (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced l hd x r lam hlam
  have hv := hs x (Set.mem_univ x)
  have he : (S.symm lam).val.val x =
      Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x •
      ((costalkEquivDual cs u b basis B d x).symm lam).val := by
    rw [← kernelEquivSingleSupport_apply cs u b basis B x]
    change (S.symm lam).val.val x =
      ((kernelEquivSingleSupport cs u b basis B x)
        ((kernelEquivSingleSupport cs u b basis B x).symm (S.symm lam))).val.val x
    rw [LinearEquiv.apply_symm_apply]
  change (S.symm lam).val.val x ∈ (B.sheaf.vertex x).piece (r+l) at hv
  rw [he] at hv
  apply mem_of_homogeneous_smul (polynomialGrading ℝ σ) (B.sheaf.vertex x).piece
    ((Sheaf.incoming (G := graph cs u b) x).card : ℤ)
    (Sheaf.incomingProduct (G := graph cs u b) (polynomialLabel cs u b basis) x)
    (incomingProduct_homogeneous cs u b basis x) _ (r+l) _ hv
  let _ := B.free x
  exact smul_right_injective _ (Sheaf.incomingProduct_ne_zero
    (polynomialLabel cs u b basis) (polynomialLabel_prime cs u b basis) x)

end
end FreeSheaf
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph.FreeSheaf
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (B : FreeSheaf cs 1 b basis)
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 theorem kernelDual_homogeneous (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (x : Interval cs 1 b) (hn : cs.length x.val≤n) (r : ℤ)
    (lam : Dual (Coefficient (σ := σ)) (B.sheaf.vertex x))
    (hlam : ∀ j (v : B.sheaf.vertex x), v∈(B.sheaf.vertex x).piece j →
      lam v∈polynomialGrading ℝ σ (j+r)) :
    kernelDual cs b basis B d x lam∈(GradedSheaf.kernelData B.sheaf x).piece
      (r+(n-cs.length x.val : ℕ)) := by
  have h := costalkEquivDual_inverse_homogeneous cs 1 b basis B d n hd x r lam hlam
  rw [incoming_card] at h
  change ((costalkEquivDual cs 1 b basis B d x).symm lam).val∈
    (B.sheaf.vertex x).piece (r+↑(n-cs.length x.val))
  have he : r+(n:ℤ)-cs.length x.val=r+↑(n-cs.length x.val) := by omega
  rwa [he] at h

 theorem kernel_character (d : SectionDuality cs 1 b basis B) (n : ℕ)
    (hd : ∀ i j (m a : B.sheaf.sections Set.univ),
      m∈(B.sheaf.sections Set.univ).piece i → a∈(B.sheaf.sections Set.univ).piece j →
      d.pairing m a∈polynomialGrading ℝ σ (i+j-(n:ℤ)))
    (hn : cs.length b≤n) (x : Interval cs 1 b) :
    GradedSheaf.freeKernelChar B.sheaf (kernel_free cs b basis B d) x=
      Polynomial.reflect (n-cs.length x.val) (GradedSheaf.freeStalkChar B.sheaf B.free x) := by
  let := B.free x
  let := kernel_free cs b basis B d x
  exact ModuleData.char_of_dual_equiv _ _ (kernelDual cs b basis B d x) _
    (kernelDual_homogeneous cs b basis B d n hd x ((length_le_of_bruhat cs x.property.2).trans hn))

end
end KLInvariance.BruhatGraph.FreeSheaf

end


section

/-! Genuine word costalk character from the integral word pairing, transported
along the fixed symmetric-algebra coordinate isomorphism. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.TitsSpace.finiteEdges
attribute [local instance] OAI.KLInvariance.TitsSpace.charDecEqA
theorem bottKernelCharacter (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] (x : Interval cs 1 (cs.wordProd l)) :
    GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
      (bottKernelFree cs basis l hl) x=Polynomial.reflect (rankDifference cs x.val (cs.wordProd l))
        (bottStalkCharacter cs basis l x.val) := by
  have he : cs.length (cs.wordProd l)=l.length := hl
  change _=Polynomial.reflect (cs.length (cs.wordProd l)-cs.length x.val) _
  rw [he]
  apply FreeSheaf.kernel_character cs (cs.wordProd l) basis _ (bottFreeDuality cs basis l hl)
    l.length _ he.le x
  intro i j m a hm ha
  exact (bottPolynomialPerfectPairing cs basis l hl).homogeneous i j m a
    (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

end
end KLInvariance.TitsSpace

end


section

/-! Bar and the exact R-convolution for genuine positive Hecke words.
No KL character or degree estimate is assumed. -/
namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem one_add_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : I) (v : Space W C) :
    v+leftInv cs q i v=(↑q⁻¹:C) • (v+left cs (q:C) i v) := by
  rw [leftInv_apply,smul_sub,smul_smul,smul_add]
  have h : (↑q⁻¹:C)*((q:C)-1)=1-(↑q⁻¹:C) := by rw [mul_sub,q.inv_mul,mul_one]
  rw [h,sub_smul,one_smul]
  module

 theorem barLinear_positiveWord (cs : CoxeterSystem M W) (q : Cˣ) (l : List I) :
    barLinear cs q (positiveWord cs (↑q⁻¹:C) l)=
      (↑q⁻¹:C)^l.length • positiveWord cs (q:C) l := by
  induction l with
  | nil => simp [barBasis_one]
  | cons i l ih =>
    simp only [positiveWord,map_add]
    have h := congrArg (fun f : Module.End C (Space W C) => f (positiveWord cs (↑q⁻¹:C) l))
      (barLinear_left cs q i)
    simp only [Module.End.mul_apply] at h
    rw [h,ih,map_smul,← smul_add,one_add_leftInv,smul_smul,List.length_cons,pow_succ]

 theorem positiveWord_support (cs : CoxeterSystem M W) (q : C) (l : List I)
    (hl : cs.IsReduced l) : (positiveWord cs q l).support ⊆ lowerFinset cs (cs.wordProd l) := by
  classical
  induction l with
  | nil => simpa [positiveWord,Hecke.basis,lowerFinset] using
      (show (Finsupp.single 1 (1:C)).support ⊆ lowerFinset cs 1 by
        intro x hx
        by_cases h : x=1
        · subst x; exact (mem_lowerFinset cs 1 1).mpr .refl
        · simp [Finsupp.mem_support_iff,Ne.symm h] at hx)
  | cons i l ih =>
    have ht : cs.IsReduced l := by simpa using hl.drop 1
    have ha : ¬cs.length (cs.simple i*cs.wordProd l) < cs.length (cs.wordProd l) := by
      have h := hl.eq
      simp only [cs.wordProd_cons,List.length_cons,←ht.eq] at h
      omega
    intro x hx
    apply (mem_lowerFinset cs (cs.wordProd (i::l)) x).mpr
    have step (y : W) (hy : BruhatLE cs y (cs.wordProd l)) :
        BruhatLE cs (upperSimple cs i y) (cs.wordProd (i::l)) := by
      simpa only [upperSimple,ite_eq_right ha,cs.wordProd_cons] using upperSimple_mono cs i hy
    have h : positiveWord cs q l x≠0 ∨ positiveWord cs q l (cs.simple i*x)≠0 := by
      by_contra hn
      push Not at hn
      rw [Finsupp.mem_support_iff,positiveWord_cons_coeff,hn.1,hn.2] at hx
      split_ifs at hx <;> simp_all
    rcases h with h|h
    · exact (le_upperSimple cs i x).trans
        (step x ((mem_lowerFinset cs _ _).mp (ih ht (Finsupp.mem_support_iff.mpr h))))
    · have hh := step (cs.simple i*x)
        ((mem_lowerFinset cs _ _).mp (ih ht (Finsupp.mem_support_iff.mpr h)))
      rw [upperSimple_mul] at hh
      exact (le_upperSimple cs i x).trans hh

 theorem positiveWord_rValue (cs : CoxeterSystem M W) (q : Cˣ) (l : List I)
    (hl : cs.IsReduced l) (x : W) :
    ∑ z ∈ lowerFinset cs (cs.wordProd l), rValue cs q x z * positiveWord cs (q:C) l z=
      (↑q⁻¹:C)^cs.length x * (q:C)^l.length * positiveWord cs (↑q⁻¹:C) l x := by
  classical
  have h := congrArg (fun v : Space W C => v x) (barLinear_positiveWord cs q⁻¹ l)
  simp only [inv_inv] at h
  rw [barLinear,Finsupp.linearCombination_apply,Finsupp.sum_apply,
    Finsupp.sum_of_support_subset _ (positiveWord_support cs (q:C) l hl) _ (by simp)] at h
  simp only [Finsupp.smul_apply,smul_eq_mul] at h
  have hr (z : W) : rValue cs q x z=(↑q⁻¹:C)^cs.length x * barBasis cs q⁻¹ z x := by
    simpa using rValue_inverse_eq_barBasis cs q⁻¹ x z
  simp only [hr,mul_assoc,←Finset.mul_sum]
  rw [show (∑ z ∈ lowerFinset cs (cs.wordProd l), barBasis cs q⁻¹ z x * positiveWord cs (q:C) l z)=
      (q:C)^l.length * positiveWord cs (↑q⁻¹:C) l x by
    simpa only [mul_comm] using h]

end
end KLInvariance.HeckeQ

end


section

namespace KLInvariance.HeckeQ
open Hecke (Space basis)
variable {I W C : Type*} [Group W] {M : CoxeterMatrix I} [CommRing C]
noncomputable section

 theorem eval_positiveWord (cs : CoxeterSystem M W) (q : C) (l : List I) (x : W) :
    Polynomial.eval₂ (Int.castRingHom C) q
      (positiveWord cs (Polynomial.X : Polynomial ℤ) l x)=positiveWord cs q l x := by
  classical
  induction l generalizing x with
  | nil => simp only [positiveWord_nil,Hecke.basis,Finsupp.single_apply]; split_ifs <;> simp
  | cons i l ih =>
    rw [positiveWord_cons_coeff,positiveWord_cons_coeff]
    split_ifs <;> simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,
      Polynomial.eval₂_X,ih]

end
end KLInvariance.HeckeQ

end


section

namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 theorem char_natDegree_le_of_dual_equiv [Module.Free (MvPolynomial σ k) M]
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l)) :
    M.char.natDegree≤l := by
  classical
  let c := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [char,character_eq _ _ c]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  simpa only [Polynomial.natDegree_X_pow] using M.degree_le_of_dual_equiv N e l he c i

end
end KLInvariance.Graded.ModuleData

end


section

/-! Genuine word stalk-to-costalk R-convolution, derived from the Hecke bar
and the constructed integral perfect word pairing. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 local instance charDecEqB_r77304d_1 (a : Type*) : DecidableEq a := Classical.decEq a
local instance rWordEdges_r77304d_1 (l : List I) : Fintype (Edge cs 1 (cs.wordProd l)) := Fintype.ofFinite _
attribute [local instance] OAI.KLInvariance.TitsSpace.rWordInterval
theorem bottStalkCharacter_natDegree_le (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    (bottStalkCharacter cs basis l x.val).natDegree ≤ rankDifference cs x.val (cs.wordProd l) := by
  let B := bottFreeSheaf cs basis l
  let := B.free x
  change (B.sheaf.vertex x).char.natDegree ≤ rankDifference cs x.val (cs.wordProd l)
  apply ModuleData.char_natDegree_le_of_dual_equiv _ _
    (FreeSheaf.kernelDual cs (cs.wordProd l) basis B (bottFreeDuality cs basis l hl) x)
    (rankDifference cs x.val (cs.wordProd l))
  have hd := (bottPolynomialPerfectPairing cs basis l hl).homogeneous
  have he : cs.length (cs.wordProd l)=l.length := hl
  apply FreeSheaf.kernelDual_homogeneous cs (cs.wordProd l) basis B (bottFreeDuality cs basis l hl)
    (cs.length (cs.wordProd l)) _ x (length_le_of_bruhat cs x.property.2)
  intro i j m a hm ha
  rw [he]
  exact hd i j m a (fun x => hm x (Set.mem_univ x)) (fun x => ha x (Set.mem_univ x))

 theorem bottStalkCharacter_reciprocity (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    Polynomial.reflect (rankDifference cs x.val (cs.wordProd l)) (bottStalkCharacter cs basis l x.val)=
      ∑ z ∈ lowerFinset cs (cs.wordProd l),
        OrdinaryR.polynomial cs x.val z*bottStalkCharacter cs basis l z := by
  apply Polynomial.toLaurent_injective
  let q := OrdinaryR.variableUnit
  have h := HeckeQ.positiveWord_rValue cs q l hl x.val
  have hlen : cs.length x.val≤l.length := hl ▸ length_le_of_bruhat cs x.property.2
  have hp : (↑q⁻¹ : LaurentPolynomial ℤ)^cs.length x.val * (q:LaurentPolynomial ℤ)^l.length=
      (q:LaurentPolynomial ℤ)^(rankDifference cs x.val (cs.wordProd l)) := by
    have he : cs.length (cs.wordProd l)=l.length := hl
    rw [rankDifference,he,← Nat.sub_add_cancel hlen,pow_add]
    calc
      _ = ((↑q⁻¹:LaurentPolynomial ℤ)*(q:LaurentPolynomial ℤ))^cs.length x.val *
          (q:LaurentPolynomial ℤ)^(l.length-cs.length x.val) := by rw [mul_pow]; ring
      _ = _ := by rw [q.inv_mul]; simp
  rw [hp] at h
  have hv (p : Polynomial ℤ) : Polynomial.toLaurent p=
      Polynomial.eval₂ (Int.castRingHom (LaurentPolynomial ℤ)) (q:LaurentPolynomial ℤ) p := by
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simp only [map_add,Polynomial.eval₂_add,hp,hr]
    | monomial n a => simp [q,Polynomial.toLaurent_C_mul_T]
  rw [hv,eval₂_reflect_unit q _ _ (bottStalkCharacter_natDegree_le cs basis l hl x)]
  rw [hv]
  simp only [Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,OrdinaryR.polynomial_eval,
    bottStalkCharacter_eq_heckeWord,HeckeQ.eval_positiveWord]
  exact h.symm

 theorem bottKernelCharacter_rConvolution_oai (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
      (bottKernelFree cs basis l hl) x=
      ∑ z : Interval cs 1 (cs.wordProd l),
        OrdinaryR.polynomial cs x.val z.val*bottStalkCharacter cs basis l z.val := by
  rw [bottKernelCharacter cs basis l hl x,bottStalkCharacter_reciprocity cs basis l hl x]
  exact Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs 1 (cs.wordProd l))))
    (lowerFinset cs (cs.wordProd l))
    (fun z => by simp only [mem_lowerFinset]; exact ⟨fun h => ⟨one_bruhat cs z,h⟩,And.right⟩)
    (fun z => OrdinaryR.polynomial cs x.val z*bottStalkCharacter cs basis l z)

end
end KLInvariance.TitsSpace

end


end OAI
end

theorem solution.{u} : type_of% @OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution_oai.{u} := @OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution_oai.{u}
