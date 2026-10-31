-- Prove2me | solution 1 for OAI.KLInvariance.combinatorial_invariance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:56:07.47526+00:00
-- url     : https://prove2.me/submissions/36b55fae-1189-4aa1-a61e-50f2dd229504

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K015
import Theorems.Thm_OAI_KLInvariance_BruhatGraph_actual_comparison_of_upper_freeness
import Theorems.Thm_OAI_KLInvariance_BruhatGraph_actual_freeSuffixes_of_rTilde_eq
import Theorems.Thm_OAI_KLInvariance_BruhatGraph_scaledStalk_reciprocity_upper

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Comparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Reciprocal low-degree rigidity and positive elementary sheaf-transfer inequalities.
-/

section


/-! The closing algebra of the admitted main proof, source §6. These are
necessary dependencies, not a substitute (conditional or special-case) main
invariance theorem. The sheaf edge-image comparison is NOT assumed as an
instance or asserted here. -/

namespace KLInvariance.Comparison

open Polynomial

/-- A polynomial supported strictly below the middle cannot equal its
reciprocal on an open real interval. This discharges the final rigidity
step after the source's two comparison inequalities have been combined. -/
theorem low_degree_zero_of_eval_reciprocal (p : ℝ[X]) (d : ℕ)
    (hp : 2 * p.natDegree < d)
    (h : ∀ q : ℝ, 0 < q → q < 1 → p.eval q = q ^ d * p.eval q⁻¹) : p = 0 := by
  have heq : p = reflect d p := by
    apply p.eq_of_infinite_eval_eq
    apply (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).mono
    intro q hq
    change p.eval q = (reflect d p).eval q
    let : Invertible q⁻¹ := invertibleOfNonzero (inv_ne_zero (ne_of_gt hq.1))
    have hr := eval₂_reflect_mul_pow (RingHom.id ℝ) q⁻¹ d p (by omega)
    simp only [eval₂_id, invOf_eq_inv, inv_inv] at hr
    have hr' := congrArg (fun z : ℝ => z * q ^ d) hr
    have hq0 : q ≠ 0 := ne_of_gt hq.1
    simp only [mul_assoc, ← mul_pow, inv_mul_cancel₀ hq0, one_pow, mul_one] at hr'
    calc
      p.eval q = q ^ d * p.eval q⁻¹ := h q hq.1 hq.2
      _ = (reflect d p).eval q := by
        simpa only [mul_comm] using hr'.symm
  by_contra hp0
  have hc := congrArg (fun f : ℝ[X] => f.coeff p.natDegree) heq.symm
  rw [coeff_reflect, revAt_le (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
    coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr hp0) hc.symm

/-- The exact polynomial conclusion from reciprocal difference equality,
without assuming positivity of KL coefficients. -/
theorem eq_of_eval_difference_reciprocal (p p' : ℤ[X]) (d : ℕ)
    (hp : 2 * p.natDegree < d) (hp' : 2 * p'.natDegree < d)
    (h : ∀ q : ℝ, 0 < q → q < 1 →
      p.eval₂ (Int.castRingHom ℝ) q - p'.eval₂ (Int.castRingHom ℝ) q =
      q ^ d * (p.eval₂ (Int.castRingHom ℝ) q⁻¹ -
        p'.eval₂ (Int.castRingHom ℝ) q⁻¹)) : p = p' := by
  apply sub_eq_zero.mp
  apply Polynomial.map_injective (f := Int.castRingHom ℝ) Int.cast_injective
  rw [Polynomial.map_zero]
  apply low_degree_zero_of_eval_reciprocal ((p - p').map (Int.castRingHom ℝ)) d
  · have hdeg := Polynomial.natDegree_map_le (f := Int.castRingHom ℝ) (p := p - p')
    have hsub := Polynomial.natDegree_sub_le p p'
    omega
  · intro q hq hq'
    simpa only [eval_map, eval₂_sub] using h q hq hq'

end KLInvariance.Comparison

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Bruhat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Strong Bruhat order, subwords, length, finite lower ideals and arbitrary finite intervals; the selected R family.
-/

section


namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


/-- The exact R recursion determines at most one R family. -/
theorem normalized_R_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP.1 = SQ.1 := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x, RP.1 x y = SQ.1 x y by
    funext x y
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x
        rw [hRP.R_diagonal, hSQ.R_diagonal]
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [hRP.R_zero _ _ hn, hSQ.R_zero _ _ hn]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [hRP.R_recursion x y i hi, hSQ.R_recursion x y i hi]
      rw [ih _ hlt _ rfl x, ih _ hlt _ rfl (cs.simple i * x)]

/-- The degree/reciprocity rigidity used both by normalization uniqueness and
by the final main-theorem induction: no polynomial supported strictly below
the midpoint can be self-reciprocal about that midpoint. -/
theorem low_degree_reflect_eq_self (f : ℤ[X]) (d : ℕ)
    (hd : 2 * f.natDegree < d) (hself : reflect d f = f) : f = 0 := by
  by_contra hn
  have hc := congrArg (fun p : ℤ[X] => p.coeff f.natDegree) hself
  rw [coeff_reflect, revAt_le (by omega)] at hc
  rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr hn) hc.symm

/-- The polynomial part of the manuscript's normalization is unique; the
proof uses the actual finite strong-Bruhat intervals, not extra assumptions. -/
theorem normalized_P_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP.2 = SQ.2 := by
  classical
  have hR := normalized_R_unique cs hRP hSQ
  suffices ∀ n : ℕ, ∀ x y : W, rankDifference cs x y = n → RP.2 x y = SQ.2 x y by
    funext x y
    exact this (rankDifference cs x y) x y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hxy
    by_cases hcomp : BruhatLE cs x y
    · by_cases heq : x = y
      · subst y
        rw [hRP.P_diagonal, hSQ.P_diagonal]
      · let : Finite (Interval cs x y) := interval_finite cs x y
        let : Fintype (Interval cs x y) := Fintype.ofFinite _
        let bottom : Interval cs x y := ⟨x, bruhat_refl cs x, hcomp⟩
        have hsum : (∑ z : Interval cs x y,
            RP.1 x z.val * (RP.2 z.val y - SQ.2 z.val y)) = RP.2 x y - SQ.2 x y := by
          rw [Finset.sum_eq_single bottom]
          · simp [bottom, hRP.R_diagonal]
          · intro z _ hz
            have hxz : x ≠ z.val := by
              intro hc
              apply hz
              exact Subtype.ext hc.symm
            have hlt := length_lt_of_bruhat_ne cs z.property.1 hxz
            have hle := length_le_of_bruhat cs z.property.2
            have hdiff : rankDifference cs z.val y < n := by
              dsimp [rankDifference] at hxy ⊢
              omega
            rw [ih _ hdiff z.val y rfl, sub_self, mul_zero]
          · simp
        have href : reflect (rankDifference cs x y) (RP.2 x y - SQ.2 x y) =
            RP.2 x y - SQ.2 x y := by
          rw [reflect_sub, hRP.reciprocity x y hcomp, hSQ.reciprocity x y hcomp,
            finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_sub_distrib]
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro z _
          rw [← hR, mul_sub]
        have hd1 := hRP.P_degree x y hcomp heq
        have hd2 := hSQ.P_degree x y hcomp heq
        have hdeg := natDegree_sub_le (RP.2 x y) (SQ.2 x y)
        have hzero := low_degree_reflect_eq_self (RP.2 x y - SQ.2 x y)
          (rankDifference cs x y) (by omega) href
        exact sub_eq_zero.mp hzero
    · rw [hRP.P_zero _ _ hcomp, hSQ.P_zero _ _ hcomp]

/-- Unique existence is still a separate obligation: this proves its
uniqueness half only, without postulating a normalized family. -/
theorem normalizedKL_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP = SQ :=
  Prod.ext (normalized_R_unique cs hRP hSQ) (normalized_P_unique cs hRP hSQ)


/-! Exchange consequences required for the source's finite-rank reduction
and for consistency of the equal-parameter Hecke recursion. -/


/-- The standard lifting property, now for the actual strong order. -/
theorem bruhat_lifting (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatLE cs x y) (i : B)
    (hx : cs.length x < cs.length (cs.simple i * x))
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    BruhatLE cs x (cs.simple i * y) ∧ BruhatLE cs (cs.simple i * x) y := by
  have hx' : ¬cs.length (cs.simple i * x) < cs.length x := by omega
  constructor
  · simpa only [lowerSimple, ite_eq_right hx', ite_eq_left hy] using lowerSimple_mono cs i hxy
  · simpa only [upperSimple, ite_eq_right hx', ite_eq_left hy] using upperSimple_mono cs i hxy


end KLInvariance
end

end OAI
end

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

theorem left_right_commute (cs : CoxeterSystem M W) (a : C) (i j : B) :
    Commute (left cs a i) (right cs a j) := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, right_basis, left_basis, map_add]
  by_cases heq : cs.simple i * w = w * cs.simple j
  · have heq' : cs.simple i * (w * cs.simple j) = w := by rw [← heq]; simp
    have heq'' : cs.simple i * w * cs.simple j = w := by simpa [mul_assoc] using heq'
    rw [heq', heq'']
    by_cases h : cs.length (cs.simple i * w) < cs.length w
    · have h' : cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      simp only [map_smul, right_basis, left_basis,
        heq, ite_eq_left h']
    · have h' : ¬cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      simp only [ite_eq_right h', map_zero, add_zero, heq]
  · have hl := left_descent_mul_simple_iff cs i j w heq
    have hr := right_descent_simple_mul_iff cs i j w heq
    simp only [hl, hr]
    by_cases hi : cs.length (cs.simple i * w) < cs.length w <;>
      by_cases hj : cs.length (w * cs.simple j) < cs.length w <;>
      simp only [hi, hj, ite_true, if_true, ite_false, if_false, map_zero, add_zero, map_smul,
        left_basis, right_basis, smul_add, smul_smul, mul_assoc] ;
      abel

/-- Acting on the identity along a reduced word gives exactly its standard
basis element. -/
theorem leftWord_one (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    leftWord cs a ω (basis 1) = basis (cs.wordProd ω) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : ¬cs.length (cs.simple i * cs.wordProd ω) < cs.length (cs.wordProd ω) := by
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    simp [Module.End.mul_apply, ih hω', hasc, cs.wordProd_cons]

theorem rightWord_one (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    rightWord cs a ω (basis 1) = basis (cs.wordProd ω)⁻¹ := by
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

theorem commute_rightWord (cs : CoxeterSystem M W) (a : C)
    {f : Module.End C (Space W C)} (h : ∀ i, Commute f (right cs a i)) (ω : List B) :
    Commute f (rightWord cs a ω) := by
  apply Commute.list_prod_right
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact h i

/-- The regular right action is cyclic, with cyclic vector the identity. -/
theorem commuting_ext (cs : CoxeterSystem M W) (a : C)
    {f g : Module.End C (Space W C)}
    (hf : ∀ i, Commute f (right cs a i))
    (hg : ∀ i, Commute g (right cs a i))
    (h : f (basis 1) = g (basis 1)) : f = g := by
  apply end_ext
  intro w
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced w⁻¹
  have hw : rightWord cs a ω (basis 1) = basis w := by
    rw [rightWord_one cs a hω, ← heq, inv_inv]
  rw [← hw]
  have hf' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs a hf ω).eq
  have hg' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs a hg ω).eq
  simp only [Module.End.mul_apply] at hf' hg'
  rw [h] at hf'
  exact hf'.trans hg'.symm

theorem leftWord_commute_right (cs : CoxeterSystem M W) (a : C) (ω : List B) (i : B) :
    Commute (leftWord cs a ω) (right cs a i) := by
  apply Commute.list_prod_left
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact left_right_commute cs a j i


theorem leftWord_independent (cs : CoxeterSystem M W) (a : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    leftWord cs a ω = leftWord cs a η := by
  apply commuting_ext cs a (leftWord_commute_right cs a ω)
    (leftWord_commute_right cs a η)
  rw [leftWord_one cs a hω, leftWord_one cs a hη, heq]

theorem wordUnit_independent (cs : CoxeterSystem M W) (a : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    wordUnit cs a ω = wordUnit cs a η := by
  apply Units.ext
  simpa using leftWord_independent cs a hω hη heq

theorem standardUnit_word (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    standardUnit cs a (cs.wordProd ω) = wordUnit cs a ω := by
  apply wordUnit_independent cs a (Classical.choose_spec (cs.exists_isReduced _)).1 hω
  exact (Classical.choose_spec (cs.exists_isReduced _)).2.symm

@[simp] theorem standardUnit_one (cs : CoxeterSystem M W) (a : C) :
    standardUnit cs a 1 = 1 := by
  have h := standardUnit_word cs a (ω := []) (by simp [CoxeterSystem.IsReduced])
  simpa [wordUnit] using h

@[simp] theorem standardUnit_basis_one (cs : CoxeterSystem M W) (a : C) (w : W) :
    (standardUnit cs a w).val (basis 1) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [standardUnit_word cs a hω, wordUnit_val, leftWord_one cs a hω]


theorem standardUnit_mul_simple (cs : CoxeterSystem M W) (a : C) (i : B) (w : W)
    (hasc : cs.length w < cs.length (w * cs.simple i)) :
    standardUnit cs a (w * cs.simple i) = standardUnit cs a w * unit cs a i := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (ω ++ [i]) := by
    unfold CoxeterSystem.IsReduced
    have := cs.length_mul_simple (cs.wordProd ω) i
    simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
      List.length_singleton]
    rw [← hω.eq]
    omega
  rw [← cs.wordProd_singleton i, ← cs.wordProd_append, standardUnit_word cs a hred,
    standardUnit_word cs a hω]
  simp [wordUnit, List.map_append, List.prod_append]

@[simp] theorem barBasis_one (cs : CoxeterSystem M W) (a : C) :
    barBasis cs a 1 = basis 1 := by simp [barBasis]

theorem barBasis_simple_mul_ascent (cs : CoxeterSystem M W) (a : C) (i : B) (w : W)
    (hasc : cs.length w < cs.length (cs.simple i * w)) :
    barBasis cs a (cs.simple i * w) = leftInv cs a i (barBasis cs a w) := by
  have hasc' : cs.length w⁻¹ < cs.length (w⁻¹ * cs.simple i) := by
    have hlen : cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
      rw [← cs.length_inv (cs.simple i * w)]
      simp [mul_inv_rev]
    simpa [hlen] using hasc
  simp only [barBasis, mul_inv_rev, cs.inv_simple,
    standardUnit_mul_simple cs a i w⁻¹ hasc', Units.val_mul,
    Module.End.mul_apply]
  rfl

theorem left_coeff (cs : CoxeterSystem M W) (a : C) (i : B) (v : Space W C) (x : W) :
    (left cs a i v) x = v (cs.simple i * x) +
      if cs.length (cs.simple i * x) < cs.length x then a * v x else 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add, Finsupp.add_apply, hv, hv', mul_add]
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c = c • (basis w : Space W C) := by
      simp [basis, Finsupp.smul_single]
    rw [hc, map_smul, left_basis]
    have heq : cs.simple i * w = x ↔ w = cs.simple i * x := by
      constructor <;> intro h
      · rw [← h]; simp
      · rw [h]; simp
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply, basis,
      Finsupp.single_apply, heq]
    by_cases h : w = x
    · subst w
      split_ifs <;> try contradiction
      all_goals simp only [Finsupp.single_eq_same, Finsupp.zero_apply,
        Finsupp.smul_apply, smul_eq_mul, mul_one, mul_zero] ; ring
    · simp only [h, ite_false, if_false, mul_zero]
      by_cases hd : cs.length (cs.simple i * w) < cs.length w <;>
        by_cases hd' : cs.length (cs.simple i * x) < cs.length x <;>
        simp [hd, hd', h]

theorem leftInv_coeff (cs : CoxeterSystem M W) (a : C) (i : B) (v : Space W C) (x : W) :
    (leftInv cs a i v) x = v (cs.simple i * x) -
      if cs.length (cs.simple i * x) < cs.length x then 0 else a * v x := by
  simp only [leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, left_coeff]
  split_ifs <;> ring

theorem simple_mul_le_ascent (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatLE cs x y) (hy : cs.length y < cs.length (cs.simple i * y)) :
    BruhatLE cs (cs.simple i * x) (cs.simple i * y) := by
  have hx := le_upperSimple cs i (cs.simple i * x)
  rw [upperSimple_mul] at hx
  have hm := upperSimple_mono cs i hxy
  simp only [upperSimple, ite_eq_right (show ¬cs.length (cs.simple i * y) < cs.length y by omega)] at hm
  exact hx.trans hm

/-- Triangularity for the genuine reflection-generated order. -/
theorem barBasis_zero (cs : CoxeterSystem M W) (a : C) (x y : W)
    (hxy : ¬BruhatLE cs x y) : barBasis cs a y x = 0 := by
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
      have := simple_mul_le_ascent cs i h hasc
      simp only [cs.simple_mul_simple_cancel_left] at this
      exact hxy this
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs a i _ hasc, leftInv_coeff,
      ih x hω' hn, ih (cs.simple i * x) hω' hn']
    split_ifs <;> simp

@[simp] theorem barBasis_diagonal (cs : CoxeterSystem M W) (a : C) (y : W) :
    barBasis cs a y y = 1 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω with
  | nil => simp [basis]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs a i _ hasc, leftInv_coeff]
    simpa [hasc] using ih hω'

@[simp] theorem rTilde_diagonal (cs : CoxeterSystem M W) (x : W) :
    rTilde cs x x = 1 := barBasis_diagonal cs (-X) x

theorem rTilde_zero (cs : CoxeterSystem M W) (x y : W) (h : ¬BruhatLE cs x y) :
    rTilde cs x y = 0 := barBasis_zero cs (-X) x y h

theorem rTilde_recursion (cs : CoxeterSystem M W) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    rTilde cs x y = if cs.length (cs.simple i * x) < cs.length x then
      rTilde cs (cs.simple i * x) (cs.simple i * y)
      else rTilde cs (cs.simple i * x) (cs.simple i * y) + X * rTilde cs x (cs.simple i * y) := by
  have hasc : cs.length (cs.simple i * y) <
      cs.length (cs.simple i * (cs.simple i * y)) := by simpa using hy
  have hb := barBasis_simple_mul_ascent cs (-X : ℤ[X]) i (cs.simple i * y) hasc
  simp only [cs.simple_mul_simple_cancel_left] at hb
  unfold rTilde
  rw [hb, leftInv_coeff]
  split_ifs <;> ring


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

theorem barLinear_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (v : Space W C) :
    barLinear cs q (leftInv cs q⁻¹ i v) = left cs (q : C) i (barLinear cs q v) := by
  have h := congrArg (fun f : Module.End C (Space W C) => f (leftInv cs q⁻¹ i v))
    (barLinear_left cs q i)
  simp only [Module.End.mul_apply] at h
  have hv : left cs (↑q⁻¹ : C) i (leftInv cs q⁻¹ i v) = v := by
    rw [← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
  rw [hv] at h
  have h' := congrArg (left cs (q : C) i) h
  have hl (t : Space W C) : left cs (q : C) i (leftInv cs q i t) = t := by
    rw [← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
  simpa only [hl] using h'.symm

/-- Applying coefficient inversion and the Hecke bar twice is the identity. -/
theorem barLinear_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    barLinear cs q (barBasis cs q⁻¹ w) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q⁻¹ i _ hasc,
      barLinear_leftInv, ih hω', left_basis, ite_eq_right (by omega)]

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

namespace HeckeQ

open Hecke (Space basis)
variable {C : Type*} [CommRing C]

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions
theorem bar_coeff_inverse (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    ∑ z ∈ lowerFinset cs y, barBasis cs q z x * barBasis cs q⁻¹ y z =
      if x = y then 1 else 0 := by
  classical
  have h := congrArg (fun v : Space W C => v x) (barLinear_barBasis cs q y)
  rw [barLinear, Finsupp.linearCombination_apply, Finsupp.sum_apply] at h
  have hs : (barBasis cs q⁻¹ y).support ⊆ lowerFinset cs y := by
    intro z hz
    apply (mem_lowerFinset cs y z).mpr
    by_contra hn
    exact Finsupp.mem_support_iff.mp hz (barBasis_zero cs _ _ _ hn)
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp), basis, Finsupp.single_apply] at h
  simpa only [Finsupp.smul_apply, smul_eq_mul, mul_comm, eq_comm] using h

theorem rValue_inverse_factor (cs : CoxeterSystem M W) (q : Cˣ) (x z y : W) :
    rValue cs q x z * (q : C) ^ cs.length y * (↑q⁻¹ : C) ^ cs.length z *
        rValue cs q⁻¹ z y =
      ((-1 : C) ^ cs.length x * (-1 : C) ^ cs.length y) *
        (barBasis cs q z x * barBasis cs q⁻¹ y z) := by
  simp only [rValue]
  rw [neg_pow (q : C), neg_pow (↑q⁻¹ : C)]
  calc
    _ = ((-1 : C) ^ cs.length x * (-1 : C) ^ cs.length y) *
        (((-1 : C) * (-1)) ^ cs.length z *
          ((q : C) * (↑q⁻¹ : C)) ^ cs.length z *
          ((q : C) * (↑q⁻¹ : C)) ^ cs.length y) *
        (barBasis cs q z x * barBasis cs q⁻¹ y z) := by simp only [mul_pow]; ring
    _ = _ := by simp

/-- The exact R-kernel identity, before specialization to polynomials. -/
theorem rValue_inverse (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      rValue cs q x z * (q : C) ^ cs.length y * (↑q⁻¹ : C) ^ cs.length z *
        rValue cs q⁻¹ z y = if x = y then 1 else 0 := by
  classical
  simp_rw [rValue_inverse_factor]
  rw [← Finset.mul_sum, bar_coeff_inverse]
  split_ifs with h
  · subst y
    rw [← mul_pow]
    simp
  · simp

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

/-- The degree bound needed for the classical polynomial reciprocity. -/
theorem polynomial_degree (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).natDegree ≤ rankDifference cs x y := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
      (polynomial cs x y).natDegree ≤ rankDifference cs x y by
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases hxy : BruhatLE cs x y
    · by_cases heq : x = y
      · subst x; simp [rankDifference]
      · have hlen := length_lt_of_bruhat_ne cs hxy heq
        have hone : y ≠ 1 := by
          intro h; subst y; simp at hlen
        obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hone
        have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
        have hylen : cs.length y = cs.length (cs.simple i * y) + 1 := by
          have := cs.length_simple_mul y i
          omega
        rw [polynomial_recursion cs x y i hi]
        by_cases hx : cs.length (cs.simple i * x) < cs.length x
        · rw [ite_eq_left hx]
          have hxlen : cs.length x = cs.length (cs.simple i * x) + 1 := by
            have := cs.length_simple_mul x i
            omega
          have hn := ih _ hlt _ rfl (cs.simple i * x)
          simpa [rankDifference, hylen, hxlen] using hn
        · rw [ite_eq_right hx]
          have hxlen : cs.length (cs.simple i * x) = cs.length x + 1 := by
            have := cs.length_simple_mul x i
            omega
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · have hn := ih _ hlt _ rfl x
            have hp : (X - 1 : ℤ[X]).natDegree ≤ 1 := by
              exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
            refine Polynomial.natDegree_mul_le.trans ?_
            dsimp [rankDifference] at hn ⊢
            omega
          · by_cases hsy : BruhatLE cs (cs.simple i * x) (cs.simple i * y)
            · have hl := length_le_of_bruhat cs hsy
              have hn := ih _ hlt _ rfl (cs.simple i * x)
              refine Polynomial.natDegree_mul_le.trans ?_
              simp only [Polynomial.natDegree_X]
              dsimp [rankDifference] at hn ⊢
              omega
            · rw [polynomial_zero cs _ _ hsy, mul_zero]
              simp
    · rw [polynomial_zero cs _ _ hxy]
      simp

/-- Polynomial R is a kernel for the length-reflection involution. -/
theorem polynomial_kernel (cs : CoxeterSystem M W) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y) =
      if x = y then 1 else 0 := by
  classical
  apply Polynomial.toLaurent_injective
  rw [map_sum]
  have h := HeckeQ.rValue_inverse cs variableUnit x y
  have heq : ∀ z ∈ lowerFinset cs y,
      (polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y)).toLaurent =
      HeckeQ.rValue cs variableUnit x z *
        (variableUnit : LaurentPolynomial ℤ) ^ cs.length y *
        (↑variableUnit⁻¹ : LaurentPolynomial ℤ) ^ cs.length z *
        HeckeQ.rValue cs variableUnit⁻¹ z y := by
    intro z hz
    have hle := length_le_of_bruhat cs ((mem_lowerFinset cs y z).mp hz)
    rw [map_mul, toLaurent_polynomial, ← eval_variableUnit,
      eval₂_reflect_unit _ _ _ (polynomial_degree cs z y), polynomial_eval]
    have hlen : cs.length y = rankDifference cs z y + cs.length z := by
      dsimp [rankDifference]; omega
    rw [hlen, pow_add]
    simp only [mul_assoc]
    rw [← mul_assoc ((variableUnit : LaurentPolynomial ℤ) ^ cs.length z),
      ← mul_pow, Units.mul_inv, one_pow, one_mul]
  rw [Finset.sum_congr rfl heq, h]
  split_ifs <;> simp

end OrdinaryR

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_1
theorem rankDifference_add (cs : CoxeterSystem M W) {x z y : W}
    (hxz : BruhatLE cs x z) (hzy : BruhatLE cs z y) :
    rankDifference cs x y = rankDifference cs x z + rankDifference cs z y := by
  have := length_le_of_bruhat cs hxz
  have := length_le_of_bruhat cs hzy
  dsimp [rankDifference]
  omega

theorem reflect_finset_sum {A : Type*} (s : Finset A) (d : ℕ) (f : A → ℤ[X]) :
    reflect d (∑ a ∈ s, f a) = ∑ a ∈ s, reflect d (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, reflect_add, ih]

namespace OrdinaryR

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_1
theorem polynomial_kernel_reverse (cs : CoxeterSystem M W) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      reflect (rankDifference cs x z) (polynomial cs x z) * polynomial cs z y =
      if x = y then 1 else 0 := by
  classical
  by_cases hxy : BruhatLE cs x y
  · have h := congrArg (reflect (rankDifference cs x y)) (polynomial_kernel cs x y)
    rw [reflect_finset_sum] at h
    have heq : ∀ z ∈ lowerFinset cs y,
        reflect (rankDifference cs x y)
          (polynomial cs x z * reflect (rankDifference cs z y) (polynomial cs z y)) =
        reflect (rankDifference cs x z) (polynomial cs x z) * polynomial cs z y := by
      intro z hz
      by_cases hxz : BruhatLE cs x z
      · rw [rankDifference_add cs hxz ((mem_lowerFinset cs y z).mp hz),
          reflect_mul _ _ (polynomial_degree cs x z)
            (Polynomial.natDegree_reflect_le.trans (max_le le_rfl (polynomial_degree cs z y))), reflect_reflect]
      · rw [polynomial_zero cs x z hxz, zero_mul, reflect_zero, reflect_zero, zero_mul]
    rw [Finset.sum_congr rfl heq] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    split_ifs with he
    · subst y
      simp [rankDifference]
    · simp
  · rw [ite_eq_right (by intro he; subst y; exact hxy (bruhat_refl cs x))]
    apply Finset.sum_eq_zero
    intro z hz
    have hxz : ¬BruhatLE cs x z := fun hxz =>
      hxy (bruhat_trans cs hxz ((mem_lowerFinset cs y z).mp hz))
    rw [polynomial_zero cs x z hxz, reflect_zero, zero_mul]

end OrdinaryR

theorem sum_proper_eq_sub (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (f : W → ℤ[X])
    (hzero : ∀ z, ¬BruhatLE cs x z → f z = 0) :
    ∑ z ∈ properIntervalFinset cs x y, f z =
      (∑ z ∈ lowerFinset cs y, f z) - f x := by
  classical
  rw [← Finset.sum_erase_eq_sub ((mem_lowerFinset cs y x).mpr hxy)]
  apply Finset.sum_subset
  · intro z hz
    have hz := (mem_properIntervalFinset cs x y z).mp hz
    exact Finset.mem_erase.mpr ⟨Ne.symm hz.2.2, (mem_lowerFinset cs y z).mpr hz.1⟩
  · intro z hz hnot
    apply hzero
    intro hxz
    have hz := Finset.mem_erase.mp hz
    exact hnot ((mem_properIntervalFinset cs x y z).mpr
      ⟨(mem_lowerFinset cs y z).mp hz.2, hxz, Ne.symm hz.1⟩)


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CanonicalKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical low-part construction, strict halfdegree, reciprocity and uniqueness; certification of the selected polynomials and interval ranks.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

namespace CanonicalP

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_2
theorem lowPart_degree (d : ℕ) (p : ℤ[X]) (hd : 0 < d) :
    2 * (lowPart d p).natDegree < d := by
  have h : (lowPart d p).natDegree ≤ (d - 1) / 2 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_lowPart, ite_eq_right (by omega)]
  omega

/-- Solve the anti-reciprocal defect with the required strict degree bound. -/
theorem lowPart_solution (d : ℕ) (p : ℤ[X]) (hanti : reflect d p = -p) :
    reflect d (-lowPart d p) = -lowPart d p + p := by
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun f : ℤ[X] => f.coeff n) hanti
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg] at hc
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg, Polynomial.coeff_add,
    coeff_lowPart]
  by_cases hn : n ≤ d
  · rw [Polynomial.revAt_le hn] at hc ⊢
    by_cases hlow : 2 * n < d
    · rw [ite_eq_left hlow, ite_eq_right (by omega)]
      ring
    · rw [ite_eq_right hlow]
      by_cases hmid : 2 * n = d
      · have hm : d - n = n := by omega
        rw [hm, ite_eq_right hlow]
        rw [hm] at hc
        linarith
      · rw [ite_eq_left (by omega)]
        linarith
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)] at hc ⊢
    rw [ite_eq_right (by omega)]
    linarith

theorem polynomial_zero (cs : CoxeterSystem M W) (x y : W)
    (hxy : ¬BruhatLE cs x y) : polynomial cs x y = 0 := by
  rw [polynomial, ite_eq_right hxy]

theorem polynomial_recursion (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (hne : x ≠ y) :
    polynomial cs x y = -lowPart (rankDifference cs x y) (defect cs x y) := by
  rw [polynomial, ite_eq_left hxy, ite_eq_right hne]
  rw [Finset.sum_attach _ (fun z => OrdinaryR.polynomial cs x z * polynomial cs z y), defect]

theorem polynomial_strict_degree (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (hne : x ≠ y) :
    2 * (polynomial cs x y).natDegree < rankDifference cs x y := by
  rw [polynomial_recursion cs x y hxy hne, Polynomial.natDegree_neg]
  apply lowPart_degree
  have := length_lt_of_bruhat_ne cs hxy hne
  dsimp [rankDifference]
  omega

theorem polynomial_degree (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).natDegree ≤ rankDifference cs x y := by
  by_cases hxy : BruhatLE cs x y
  · by_cases hne : x = y
    · subst y
      simp
    · have := polynomial_strict_degree cs x y hxy hne
      omega
  · rw [polynomial_zero cs x y hxy]
    simp

theorem defect_full_sum (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) :
    defect cs x y = (∑ z ∈ lowerFinset cs y,
      OrdinaryR.polynomial cs x z * polynomial cs z y) - polynomial cs x y := by
  rw [defect, sum_proper_eq_sub cs x y hxy]
  · simp
  · intro z hz
    rw [OrdinaryR.polynomial_zero cs x z hz, zero_mul]

theorem reversed_kernel_on_lower (cs : CoxeterSystem M W) (x y t : W)
    (hty : BruhatLE cs t y) :
    ∑ z ∈ lowerFinset cs y,
      reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
        OrdinaryR.polynomial cs z t = if x = t then 1 else 0 := by
  classical
  rw [← OrdinaryR.polynomial_kernel_reverse cs x t]
  symm
  apply Finset.sum_subset
  · intro z hz
    exact (mem_lowerFinset cs y z).mpr
      (bruhat_trans cs ((mem_lowerFinset cs t z).mp hz) hty)
  · intro z hz hnt
    have hzt : ¬BruhatLE cs z t := fun h => hnt ((mem_lowerFinset cs t z).mpr h)
    rw [OrdinaryR.polynomial_zero cs z t hzt, mul_zero]

theorem reversed_kernel_on_proper (cs : CoxeterSystem M W) (x y t : W)
    (hxy : BruhatLE cs x y) (hty : BruhatLE cs t y) :
    ∑ z ∈ properIntervalFinset cs x y,
      reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
        OrdinaryR.polynomial cs z t =
      (if x = t then 1 else 0) - OrdinaryR.polynomial cs x t := by
  rw [sum_proper_eq_sub cs x y hxy]
  · rw [reversed_kernel_on_lower cs x y t hty]
    simp [rankDifference]
  · intro z hz
    rw [OrdinaryR.polynomial_zero cs x z hz, reflect_zero, zero_mul]

/-- The reciprocity equation is a theorem of the lower-half construction. -/
theorem polynomial_reciprocity (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) :
    reflect (rankDifference cs x y) (polynomial cs x y) =
      ∑ z ∈ lowerFinset cs y, OrdinaryR.polynomial cs x z * polynomial cs z y := by
  classical
  suffices ∀ n : ℕ, ∀ x y : W, rankDifference cs x y = n → BruhatLE cs x y →
      reflect (rankDifference cs x y) (polynomial cs x y) =
        ∑ z ∈ lowerFinset cs y, OrdinaryR.polynomial cs x z * polynomial cs z y by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hxy
    by_cases hne : x = y
    · subst y
      rw [polynomial_diagonal]
      simp only [rankDifference, Nat.sub_self, Polynomial.reflect_one, pow_zero]
      symm
      rw [Finset.sum_eq_single x]
      · simp
      · intro z hz hzx
        have hnxz : ¬BruhatLE cs x z := fun hxz =>
          hzx (bruhat_antisymm cs ((mem_lowerFinset cs x z).mp hz) hxz)
        rw [OrdinaryR.polynomial_zero cs x z hnxz, zero_mul]
      · intro hmiss
        exact (hmiss ((mem_lowerFinset cs x x).mpr (bruhat_refl cs x))).elim
    · have hanti : reflect (rankDifference cs x y) (defect cs x y) = -defect cs x y := by
        rw [defect, reflect_finset_sum]
        have heq : ∀ z ∈ properIntervalFinset cs x y,
            reflect (rankDifference cs x y)
              (OrdinaryR.polynomial cs x z * polynomial cs z y) =
            reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
              (∑ t ∈ lowerFinset cs y, OrdinaryR.polynomial cs z t * polynomial cs t y) := by
          intro z hz
          have hz := (mem_properIntervalFinset cs x y z).mp hz
          have hlt : rankDifference cs z y < n := by
            have := length_lt_of_bruhat_ne cs hz.2.1 hz.2.2
            have := length_le_of_bruhat cs hz.1
            dsimp [rankDifference] at hn ⊢
            omega
          rw [rankDifference_add cs hz.2.1 hz.1,
            reflect_mul _ _ (OrdinaryR.polynomial_degree cs x z) (polynomial_degree cs z y),
            ih _ hlt z y rfl hz.1]
        rw [Finset.sum_congr rfl heq]
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul]
        have hkernel : ∀ t ∈ lowerFinset cs y,
            (∑ z ∈ properIntervalFinset cs x y,
              reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
                OrdinaryR.polynomial cs z t) * polynomial cs t y =
            ((if x = t then 1 else 0) - OrdinaryR.polynomial cs x t) * polynomial cs t y := by
          intro t ht
          rw [reversed_kernel_on_proper cs x y t hxy ((mem_lowerFinset cs y t).mp ht)]
        rw [Finset.sum_congr rfl hkernel]
        simp_rw [sub_mul, Finset.sum_sub_distrib]
        have hdelta : (∑ t ∈ lowerFinset cs y,
            (if x = t then (1 : ℤ[X]) else 0) * polynomial cs t y) = polynomial cs x y := by
          rw [Finset.sum_eq_single x]
          · simp
          · intro t ht htx
            simp [Ne.symm htx]
          · intro hmiss
            exact (hmiss ((mem_lowerFinset cs y x).mpr hxy)).elim
        rw [hdelta]
        change polynomial cs x y - (∑ z ∈ lowerFinset cs y,
          OrdinaryR.polynomial cs x z * polynomial cs z y) = -defect cs x y
        rw [defect_full_sum cs x y hxy]
        ring
      rw [polynomial_recursion cs x y hxy hne, lowPart_solution _ _ hanti]
      rw [← polynomial_recursion cs x y hxy hne, defect_full_sum cs x y hxy]
      ring

end CanonicalP

attribute [local instance] OAI.KLInvariance.instDecidableEq_solutions_2
/-- Finitely supported interval sums agree with the lower-ideal sums used in
our construction; all incomparable summands are literally zero. -/
theorem normalized_interval_sum (cs : CoxeterSystem M W) (x y : W) :
    (∑ᶠ z : Interval cs x y,
      OrdinaryR.polynomial cs x z.val * CanonicalP.polynomial cs z.val y) =
    ∑ z ∈ lowerFinset cs y,
      OrdinaryR.polynomial cs x z * CanonicalP.polynomial cs z y := by
  classical
  let := interval_finite cs x y
  let : Fintype (Interval cs x y) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hsum := Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs x y)))
    ((lowerFinset cs y).filter (fun z => BruhatLE cs x z))
    (fun z => by simp only [Finset.mem_filter, mem_lowerFinset]; exact and_comm)
    (fun z => OrdinaryR.polynomial cs x z * CanonicalP.polynomial cs z y)
  refine hsum.symm.trans ?_
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hnxz : ¬BruhatLE cs x z := fun hxz => hnot (Finset.mem_filter.mpr ⟨hz, hxz⟩)
  rw [OrdinaryR.polynomial_zero cs x z hnxz, zero_mul]

/-- The selected polynomials really exist with the classical equal-parameter
normalization. This is a construction, not an extra hypothesis. -/
theorem constructed_normalizedKL (cs : CoxeterSystem M W) :
    NormalizedKL cs (OrdinaryR.polynomial cs, CanonicalP.polynomial cs) where
  R_diagonal := OrdinaryR.polynomial_diagonal cs
  R_zero := OrdinaryR.polynomial_zero cs
  R_recursion := OrdinaryR.polynomial_recursion cs
  P_diagonal := CanonicalP.polynomial_diagonal cs
  P_zero := CanonicalP.polynomial_zero cs
  P_degree := CanonicalP.polynomial_strict_degree cs
  reciprocity := by
    intro x y hxy
    rw [normalized_interval_sum]
    exact CanonicalP.polynomial_reciprocity cs x y hxy

theorem normalizedKL_existsUnique (cs : CoxeterSystem M W) :
    ∃! RP : PolynomialFamilies W, NormalizedKL cs RP := by
  refine ⟨(OrdinaryR.polynomial cs, CanonicalP.polynomial cs), constructed_normalizedKL cs, ?_⟩
  intro RP hRP
  exact normalizedKL_unique cs hRP (constructed_normalizedKL cs)

theorem klFamilies_spec (cs : CoxeterSystem M W) : NormalizedKL cs (klFamilies cs) := by
  exact Classical.epsilon_spec (normalizedKL_existsUnique cs).exists

theorem klFamilies_eq_constructed (cs : CoxeterSystem M W) :
    klFamilies cs = (OrdinaryR.polynomial cs, CanonicalP.polynomial cs) :=
  normalizedKL_unique cs (klFamilies_spec cs) (constructed_normalizedKL cs)

theorem klPolynomial_eq_constructed (cs : CoxeterSystem M W) (x y : W) :
    klPolynomial cs x y = CanonicalP.polynomial cs x y := by
  simp only [klPolynomial, klFamilies_eq_constructed]

theorem rPolynomial_eq_constructed (cs : CoxeterSystem M W) (x y : W) :
    rPolynomial cs x y = OrdinaryR.polynomial cs x y := by
  simp only [rPolynomial, klFamilies_eq_constructed]


/-- Every nontrivial Bruhat interval contains a first step of length one.
This is the grading fact needed to transport rank differences without labels. -/
theorem exists_bruhat_successor (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatLE cs x y) (hne : x ≠ y) :
    ∃ z, BruhatLE cs x z ∧ BruhatLE cs z y ∧ cs.length z = cs.length x + 1 := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x : W,
      BruhatLE cs x y → x ≠ y →
      ∃ z, BruhatLE cs x z ∧ BruhatLE cs z y ∧ cs.length z = cs.length x + 1 by
    exact this _ y rfl x hxy hne
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hyn x hxy hne
    have hy1 : y ≠ 1 := by
      intro hy
      subst y
      have hlen := length_le_of_bruhat cs hxy
      have hx : cs.length x = 0 := by simpa using hlen
      exact hne (cs.length_eq_zero_iff.mp hx)
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hy1
    change cs.length (cs.simple i * y) < cs.length y at hi
    have hylen : cs.length y = cs.length (cs.simple i * y) + 1 := by
      have := cs.length_simple_mul y i
      omega
    have hsyn : cs.length (cs.simple i * y) < n := by omega
    have hsyy : BruhatLE cs (cs.simple i * y) y := by
      simpa only [lowerSimple, ite_eq_left hi] using lowerSimple_le cs i y
    by_cases hxsy : BruhatLE cs x (cs.simple i * y)
    · by_cases hxeq : x = cs.simple i * y
      · exact ⟨y, hxy, bruhat_refl cs y, by simpa [hxeq] using hylen⟩
      · obtain ⟨z, hxz, hzsy, hzlen⟩ := ih _ hsyn _ rfl x hxsy hxeq
        exact ⟨z, hxz, bruhat_trans cs hzsy hsyy, hzlen⟩
    · have hxi : cs.length (cs.simple i * x) < cs.length x := by
        by_contra hnxi
        have hxim : cs.length x < cs.length (cs.simple i * x) := by
          have := cs.length_simple_mul x i
          omega
        exact hxsy (bruhat_lifting cs hxy i hxim hi).1
      have hxlen : cs.length x = cs.length (cs.simple i * x) + 1 := by
        have := cs.length_simple_mul x i
        omega
      have hsxsy : BruhatLE cs (cs.simple i * x) (cs.simple i * y) := by
        simpa only [lowerSimple, ite_eq_left hxi, ite_eq_left hi] using lowerSimple_mono cs i hxy
      have hne' : cs.simple i * x ≠ cs.simple i * y := fun he => hne (mul_left_cancel he)
      obtain ⟨w, hsxw, hwsy, hwlen⟩ := ih _ hsyn _ rfl _ hsxsy hne'
      have hux : upperSimple cs i (cs.simple i * x) = x := by
        rw [upperSimple_mul]
        simp only [upperSimple, ite_eq_left hxi]
      have huy : upperSimple cs i (cs.simple i * y) = y := by
        rw [upperSimple_mul]
        simp only [upperSimple, ite_eq_left hi]
      have hxz := upperSimple_mono cs i hsxw
      have hzy := upperSimple_mono cs i hwsy
      rw [hux] at hxz
      rw [huy] at hzy
      have hwlen' : cs.length w = cs.length x := by omega
      have hwi : ¬cs.length (cs.simple i * w) < cs.length w := by
        intro hwi
        simp only [upperSimple, ite_eq_left hwi] at hxz
        have hxw : x = w := by
          by_contra hnxw
          have := length_lt_of_bruhat_ne cs hxz hnxw
          omega
        exact hxsy (hxw ▸ hwsy)
      refine ⟨upperSimple cs i w, hxz, hzy, ?_⟩
      simp only [upperSimple, ite_eq_right hwi]
      have := cs.length_simple_mul w i
      omega


/-- An order embedding between Bruhat intervals cannot shorten rank. -/
theorem rankDifference_le_of_strictMono
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'}
    (f : Interval cs u b → Interval cs' u' b') (hf : StrictMono f)
    {x y : Interval cs u b} (hxy : x ≤ y) :
    rankDifference cs x.val y.val ≤ rankDifference cs' (f x).val (f y).val := by
  suffices ∀ n : ℕ, ∀ x y : Interval cs u b,
      rankDifference cs x.val y.val = n → x ≤ y →
      rankDifference cs x.val y.val ≤ rankDifference cs' (f x).val (f y).val by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hxy
    by_cases heq : x = y
    · subst y
      simp [rankDifference]
    · have hne : x.val ≠ y.val := fun hv => heq (Subtype.ext hv)
      obtain ⟨z, hxz, hzy, hzlen⟩ := exists_bruhat_successor cs hxy hne
      let zI : Interval cs u b := ⟨z, bruhat_trans cs x.property.1 hxz,
        bruhat_trans cs hzy y.property.2⟩
      have hxylen := length_le_of_bruhat cs hxy
      have hzylen := length_le_of_bruhat cs hzy
      have hsmall : rankDifference cs zI.val y.val < n := by
        dsimp [zI, rankDifference] at hn ⊢
        omega
      have hsub := ih _ hsmall zI y rfl hzy
      have hxz' : x < zI := by
        refine (lt_iff_le_and_ne).mpr ⟨hxz, ?_⟩
        intro hx
        have hv : x.val = z := congrArg Subtype.val hx
        have := congrArg cs.length hv
        omega
      have hfxz := hf hxz'
      have hfxzlen : cs'.length (f x).val < cs'.length (f zI).val := by
        apply length_lt_of_bruhat_ne cs' hfxz.le
        intro hv
        exact hfxz.ne (Subtype.ext hv)
      have hfzyle := length_le_of_bruhat cs' (hf.monotone (show zI ≤ y from hzy))
      change cs.length y.val - cs.length z ≤
        cs'.length (f y).val - cs'.length (f zI).val at hsub
      change cs.length y.val - cs.length x.val ≤
        cs'.length (f y).val - cs'.length (f x).val
      omega

/-- Rank is intrinsic to the abstract interval poset, with neither root
labels nor simple generators preserved by the isomorphism. -/
theorem intervalIso_rankDifference
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'}
    (ι : Interval cs u b ≃o Interval cs' u' b')
    {x y : Interval cs u b} (hxy : x ≤ y) :
    rankDifference cs x.val y.val = rankDifference cs' (ι x).val (ι y).val := by
  apply Nat.le_antisymm
  · exact rankDifference_le_of_strictMono cs cs' ι ι.strictMono hxy
  · have h := rankDifference_le_of_strictMono cs' cs ι.symm ι.symm.strictMono (ι.monotone hxy)
    simpa only [OrderIso.symm_apply_apply] using h

theorem intervalIso_bottom
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    ι (intervalBottom cs hub) = intervalBottom cs' hub' := by
  apply le_antisymm
  · have h : intervalBottom cs hub ≤ ι.symm (intervalBottom cs' hub') :=
      (ι.symm (intervalBottom cs' hub')).property.1
    simpa only [OrderIso.apply_symm_apply] using ι.monotone h
  · exact (ι (intervalBottom cs hub)).property.1

theorem intervalIso_top
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    ι (intervalTop cs hub) = intervalTop cs' hub' := by
  apply le_antisymm
  · exact (ι (intervalTop cs hub)).property.2
  · have h : ι.symm (intervalTop cs' hub') ≤ intervalTop cs hub :=
      (ι.symm (intervalTop cs' hub')).property.2
    simpa only [OrderIso.apply_symm_apply] using ι.monotone h

theorem intervalIso_full_rankDifference
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    rankDifference cs u b = rankDifference cs' u' b' := by
  have h := intervalIso_rankDifference cs cs' ι
    (show intervalBottom cs hub ≤ intervalTop cs hub from hub)
  rw [intervalIso_bottom cs cs' hub hub' ι, intervalIso_top cs cs' hub hub' ι] at h
  exact h

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

namespace KLInvariance.Dihedral

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

attribute [local instance] OAI.KLInvariance.Dihedral.instDecidable_solutions
theorem eq_alt_of_descent (cs : CoxeterSystem M W) (i : Bool) {w : W}
    (h : cs.length (cs.simple i * w) < cs.length w) :
    w = cs.wordProd (alt i (cs.length w)) := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced (cs.simple i * w)
  have hlen : cs.length w = ω.length + 1 := by
    have := cs.length_simple_mul w i
    rw [hw, hω.eq] at this h
    omega
  have hp : cs.wordProd (i :: ω) = w := by
    simp only [cs.wordProd_cons, ← hw, cs.simple_mul_simple_cancel_left]
  have hr : cs.IsReduced (i :: ω) := by
    simpa only [CoxeterSystem.IsReduced, hp, List.length_cons] using hlen
  rw [hlen, ← reduced_cons_eq_alt cs i ω hr, hp]

end KLInvariance.Dihedral

namespace KLInvariance.HeckeQ

universe uR vR
variable {B : Type uR} {W : Type vR} [Group W] {M : CoxeterMatrix B}
variable {C : Type*} [CommRing C]

@[simp] theorem dualR_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (x : W) :
    dualR cs q x x = 1 := by
  rw [dualR, rValue_diagonal, mul_one, ← mul_pow]
  simp

end KLInvariance.HeckeQ

end

section

namespace KLInvariance
open Polynomial
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

/-- The exact square-parameter normalization, proved from the two genuine
Hecke recurrences. Integer exponents let the formula include incomparable
pairs without silently changing the R-polynomial definition. -/
theorem rPolynomial_normalization {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0) (x y : W) :
    eval₂ (Int.castRingHom C) (v^2) (rPolynomial cs x y) =
      v ^ ((cs.length y : ℤ) - cs.length x) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x y) := by
  rw [rPolynomial_eq_constructed]
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x,
    eval₂ (Int.castRingHom C) (v^2) (OrdinaryR.polynomial cs x y) =
      v ^ ((cs.length y : ℤ) - cs.length x) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x y) from
    this _ y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y=1
    · subst y
      by_cases hx : x=1
      · subst x; simp
      · have hn : ¬BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x=0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [OrdinaryR.polynomial_zero cs _ _ hn,Hecke.rTilde_zero cs _ _ hn]
        simp
    · obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i*y)<n := hy ▸ hi
      have hylen : cs.length (cs.simple i*y)+1=cs.length y := by
        have := cs.length_simple_mul y i; omega
      rw [OrdinaryR.polynomial_recursion cs x y i hi,Hecke.rTilde_recursion cs x y i hi]
      by_cases hx : cs.length (cs.simple i*x) < cs.length x
      · rw [ite_eq_left hx,ite_eq_left hx,ih _ hlt _ rfl (cs.simple i*x)]
        congr 2
        have := cs.length_simple_mul x i
        omega
      · rw [ite_eq_right hx,ite_eq_right hx]
        simp only [eval₂_add,eval₂_mul,eval₂_sub,eval₂_X,eval₂_one]
        rw [ih _ hlt _ rfl x,ih _ hlt _ rfl (cs.simple i*x)]
        have hxlen : cs.length (cs.simple i*x)=cs.length x+1 := by
          have := cs.length_simple_mul x i; omega
        have h1 : (cs.length (cs.simple i*y) : ℤ)-cs.length x =
            ((cs.length y : ℤ)-cs.length x)-1 := by omega
        have h2 : (cs.length (cs.simple i*y) : ℤ)-cs.length (cs.simple i*x) =
            ((cs.length y : ℤ)-cs.length x)-2 := by omega
        rw [h1,h2,zpow_sub₀ hv ((cs.length y : ℤ)-cs.length x) 1,
          zpow_sub₀ hv ((cs.length y : ℤ)-cs.length x) 2]
        simp only [zpow_ofNat]
        field_simp [hv]
        ; ring

/-- Exact normalized reciprocity in the direction useful for reversing the
parameter. No path formula and no moment-graph assumption occurs here. -/
theorem scaledKL_reciprocity_inverse {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0)
    (x b : W) (hxb : BruhatLE cs x b) :
    scaledKL cs v⁻¹ x b = ∑ᶠ z : Interval cs x b,
      eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x z.val) *
        scaledKL cs v z.val b := by
  classical
  let : Finite (Interval cs x b) := interval_finite cs x b
  let : Fintype (Interval cs x b) := Fintype.ofFinite _
  have hrec := (klFamilies_spec cs).reciprocity x b hxb
  change reflect (rankDifference cs x b) (klPolynomial cs x b) =
      ∑ᶠ z : Interval cs x b, rPolynomial cs x z.val * klPolynomial cs z.val b at hrec
  have hdeg : (klPolynomial cs x b).natDegree ≤ rankDifference cs x b := by
    rw [klPolynomial_eq_constructed]
    exact CanonicalP.polynomial_degree cs x b
  let q : Cˣ := Units.mk0 (v^2) (pow_ne_zero 2 hv)
  have heval := congrArg (eval₂ (Int.castRingHom C) (q : C)) hrec
  rw [eval₂_reflect_unit q _ _ hdeg] at heval
  simp only [finsum_eq_sum_of_fintype,eval₂_finsetSum,eval₂_mul] at heval ⊢
  have hq : (q : C) = v^2 := rfl
  have hqi : (↑q⁻¹ : C) = (v⁻¹)^2 := by simp [q,inv_pow]
  rw [hq,hqi] at heval
  have heq := congrArg (fun a : C => v ^ ((cs.length x : ℤ)-cs.length b)*a) heval
  have hd : (rankDifference cs x b : ℤ) = (cs.length b : ℤ)-cs.length x := by
    have hlen := length_le_of_bruhat cs hxb
    simp [rankDifference,Int.ofNat_sub hlen]
  have hscale : v ^ ((cs.length x : ℤ)-cs.length b) *
      (v^2)^(rankDifference cs x b) =
        (v⁻¹) ^ ((cs.length x : ℤ)-cs.length b) := by
    rw [←pow_mul,←zpow_natCast,←zpow_add₀ hv,inv_zpow,←zpow_neg]
    congr 1
    push_cast
    omega
  rw [←mul_assoc,hscale,Finset.mul_sum] at heq
  change (v⁻¹)^((cs.length x : ℤ)-cs.length b)*
      eval₂ (Int.castRingHom C) ((v⁻¹)^2) (klPolynomial cs x b) = _
  rw [heq]
  apply Finset.sum_congr rfl
  intro z _
  rw [rPolynomial_normalization cs v hv]
  unfold scaledKL
  calc
    _ = (v ^ ((cs.length x : ℤ)-cs.length b) *
        v ^ ((cs.length z.val : ℤ)-cs.length x)) *
        eval₂ (Int.castRingHom C) (v-v⁻¹) (Hecke.rTilde cs x z.val) *
        eval₂ (Int.castRingHom C) (v^2) (klPolynomial cs z.val b) := by ring
    _ = _ := by
      rw [←zpow_add₀ hv,show (cs.length x : ℤ)-cs.length b+
        ((cs.length z.val : ℤ)-cs.length x) =
        (cs.length z.val : ℤ)-cs.length b by ring]
      ring


theorem scaledKL_reciprocity {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (v : C) (hv : v ≠ 0)
    (x b : W) (hxb : BruhatLE cs x b) :
    scaledKL cs v x b = ∑ᶠ z : Interval cs x b,
      eval₂ (Int.castRingHom C) (v⁻¹-v) (Hecke.rTilde cs x z.val) *
        scaledKL cs v⁻¹ z.val b := by
  simpa only [inv_inv] using scaledKL_reciprocity_inverse cs v⁻¹ (inv_ne_zero hv) x b hxb

end KLInvariance


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Tits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual Bruhat graph labels, Tits realizations and extended root spaces, cotangent coordinates and standard parabolic support.
-/

section

/-! The finite Coxeter relations for the actual real geometric reflection
operators required in `bg:realization`. Faithfulness is not assumed or claimed. -/

/-! Coordinate-dual geometric action. This exists in arbitrary rank and is
used only to prove the finite standard-parabolic reduction of the main goal. -/

namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I) [Fintype J]
noncomputable section

lemma rankDifference_inclusion (x y : (matrix (M := M) J).Group) :
    rankDifference cs (inclusion cs J x) (inclusion cs J y) =
      rankDifference (system (M := M) J) x y := by
  simp only [rankDifference, length_inclusion]

/-- Restriction of the actual normalized families satisfies their exact
recurrence, degree bound and interval reciprocity in the standard parabolic. -/
theorem normalized_restriction {RP : PolynomialFamilies W} (hRP : NormalizedKL cs RP) :
    NormalizedKL (system (M := M) J)
      (fun x y => RP.1 (inclusion cs J x) (inclusion cs J y),
       fun x y => RP.2 (inclusion cs J x) (inclusion cs J y)) where
  R_diagonal x := hRP.R_diagonal _
  R_zero x y hxy := hRP.R_zero _ _ (fun h => hxy ((bruhat_inclusion_iff cs J x y).1 h))
  R_recursion := by
    intro x y i hy
    have hs (z : (matrix (M := M) J).Group) :
        inclusion cs J ((system (M := M) J).simple i * z) =
          cs.simple i.val * inclusion cs J z := by rw [map_mul, inclusion_simple]
    have hl (z : (matrix (M := M) J).Group) :
        cs.length (cs.simple i.val * inclusion cs J z) =
          (system (M := M) J).length ((system (M := M) J).simple i * z) := by
      rw [← hs, length_inclusion]
    have h := hRP.R_recursion (inclusion cs J x) (inclusion cs J y) i.val
      (by rwa [hl, length_inclusion])
    simpa only [hs, hl, length_inclusion] using h
  P_diagonal x := hRP.P_diagonal _
  P_zero x y hxy := hRP.P_zero _ _ (fun h => hxy ((bruhat_inclusion_iff cs J x y).1 h))
  P_degree := by
    intro x y hxy hne
    have h := hRP.P_degree (inclusion cs J x) (inclusion cs J y)
      ((bruhat_inclusion_iff cs J x y).2 hxy) (fun h => hne (inclusion_injective cs J h))
    rwa [rankDifference_inclusion] at h
  reciprocity := by
    intro x y hxy
    have h := hRP.reciprocity (inclusion cs J x) (inclusion cs J y)
      ((bruhat_inclusion_iff cs J x y).2 hxy)
    rw [rankDifference_inclusion] at h
    rw [h]
    let := interval_finite cs (inclusion cs J x) (inclusion cs J y)
    let := interval_finite (system (M := M) J) x y
    let := Fintype.ofFinite (Interval cs (inclusion cs J x) (inclusion cs J y))
    let := Fintype.ofFinite (Interval (system (M := M) J) x y)
    simp only [finsum_eq_sum_of_fintype]
    exact ((intervalIso cs J x y).toEquiv.sum_comp
      (fun z => RP.1 (inclusion cs J x) z.val * RP.2 z.val (inclusion cs J y))).symm

theorem klFamilies_inclusion :
    (fun x y => rPolynomial cs (inclusion cs J x) (inclusion cs J y),
     fun x y => klPolynomial cs (inclusion cs J x) (inclusion cs J y)) =
      klFamilies (system (M := M) J) :=
  normalizedKL_unique _ (normalized_restriction cs J (klFamilies_spec cs))
    (klFamilies_spec _)

theorem klPolynomial_inclusion (x y : (matrix (M := M) J).Group) :
    klPolynomial cs (inclusion cs J x) (inclusion cs J y) =
      klPolynomial (system (M := M) J) x y :=
  congrFun (congrFun (congrArg Prod.snd (klFamilies_inclusion cs J)) x) y

end
end KLInvariance.StandardParabolic

/-! Construction of the source's geometric reflection schedule. The moment
curve avoids every forbidden hyperplane of a countable root set, using only
finite polynomial root sets and uncountability of the real field. -/

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionSchedules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Reflection schedules, decreasing paths, root-space and edge algebra, and dihedral path recursions.
-/

section


namespace KLInvariance.SchedulePaths
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
variable (source target : E → V)

variable [Semiring R]

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions
/-- The full matrix expansion, each sublist contributing exactly one path
term. Noncomposable sublists contribute zero by the definition of pathTerm. -/
theorem dispatch_eq_path_sum (T : R) (v : V → R) (p : List E) (x : V) :
    dispatch source target T v p x =
      ((p.sublists').map (fun q => pathTerm source target T v q x)).sum := by
  classical
  induction p generalizing x with
  | nil => simp [dispatch, List.sublists', pathTerm]
  | cons e p ih =>
    rw [dispatch,step,List.sublists'_cons,List.map_append,List.sum_append,List.map_map]
    rw [ih x]
    congr 1
    by_cases he : source e = x
    · simp only [Function.comp_def,pathTerm,he,ite_true, if_true]
      rw [List.sum_map_mul_left,ih (target e)]
    · simp [Function.comp_def,he,pathTerm]

/-- With a delta initial value, a path contributes its length weight, not an
invariant defined by the desired conclusion. -/
theorem pathTerm_delta (T : R) (x y : V) (p : List E) :
    pathTerm source target T (fun z => if z = y then 1 else 0) p x =
      if IsPath source target x y p then T ^ p.length else 0 := by
  classical
  induction p generalizing x with
  | nil => simp [pathTerm,IsPath]
  | cons e p ih =>
    simp only [pathTerm,IsPath,List.length_cons]
    by_cases he : source e = x
    · rw [ite_eq_left he,ih]
      by_cases hp : IsPath source target (target e) y p
      · simp only [hp,he,and_self,ite_true, if_true,pow_succ']
      · simp [hp,he]
    · simp [he]

/-- The entry of the elementary-matrix product is exactly the sum of weights
of directed schedule-subpaths. -/
theorem entry_eq_weighted_paths (T : R) (p : List E) (x y : V) :
    dispatch source target T (fun z => if z = y then 1 else 0) p x =
      ((p.sublists').map (fun q =>
        if IsPath source target x y q then T ^ q.length else 0)).sum := by
  classical
  rw [dispatch_eq_path_sum]
  congr 1
  exact List.map_congr_left (fun q _ => pathTerm_delta source target T x y q)


section LabelOrder
variable {Λ : Type*} [LinearOrder Λ] (label : E → Λ)

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions
/-- Ties in a legitimate reflection schedule cannot occur on a composable
pair. Hence every nonzero term in the schedule expansion has strictly
rather than merely weakly decreasing labels. -/
theorem decreasing_of_schedule_path
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    {p : List E} {x y : V}
    (hp : IsPath source target x y p)
    (hs : p.Pairwise (fun e f => label f ≤ label e)) :
    p.Pairwise (fun e f => label f < label e) := by
  induction p generalizing x with
  | nil => exact List.Pairwise.nil
  | cons e p ih =>
    cases p with
    | nil => simp
    | cons f p =>
      have ht : IsPath source target (target e) y (f :: p) := hp.2
      have hef : label f < label e := by
        apply lt_of_le_of_ne ((List.pairwise_cons.mp hs).1 f (List.mem_cons_self))
        intro heq
        exact hties e f heq.symm ht.1.symm
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih ht hs.tail⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hef
      · exact lt_of_le_of_lt ((List.pairwise_cons.mp hs.tail).1 g hg) hef

/-- Every strictly decreasing edge list contained in a weakly decreasing
schedule occurs as a sublist. This also handles arbitrary ordering of ties:
a strict list can use at most one edge of each label. -/
theorem sublist_of_decreasing_subset {p schedule : List E}
    (hp : p.Pairwise (fun e f => label f < label e))
    (hs : schedule.Pairwise (fun e f => label f ≤ label e))
    (hmem : p ⊆ schedule) : List.Sublist p schedule := by
  induction schedule generalizing p with
  | nil =>
    have : p = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => List.not_mem_nil (hmem ha))
    subst p
    exact List.Sublist.refl []
  | cons e schedule ih =>
    cases p with
    | nil => exact List.nil_sublist _
    | cons f p =>
      by_cases hef : e = f
      · subst f
        apply List.Sublist.cons_cons
        apply ih hp.tail hs.tail
        intro g hg
        rcases List.mem_cons.mp (hmem (List.mem_cons_of_mem e hg)) with heq | hin
        · have hlt := (List.pairwise_cons.mp hp).1 g hg
          rw [heq] at hlt
          exact (lt_irrefl _ hlt).elim
        · exact hin
      · apply List.Sublist.cons
        apply ih hp hs.tail
        intro g hg
        have hfg : f ∈ schedule := (List.mem_cons.mp (hmem (List.mem_cons_self))).resolve_left
          (Ne.symm hef)
        have hfe : label f ≤ label e := (List.pairwise_cons.mp hs).1 f hfg
        rcases List.mem_cons.mp (hmem hg) with heq | hin
        · subst g
          rcases List.mem_cons.mp hg with h | h
          · exact (hef h).elim
          · exact (not_lt_of_ge hfe ((List.pairwise_cons.mp hp).1 e h)).elim
        · exact hin

end LabelOrder

end
end KLInvariance.SchedulePaths

/-! NEW GRAPH CLOSURE -/


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_HilbertSeries
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.Graded.piPiece_finite _root_.OAI.KLInvariance.Graded.subPiece_finite _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree
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
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree
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


section

/-! Graded linear equivalence preserves the genuine free-module character.
This does not assert its identification with any KL polynomial. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ)}

 theorem character_eq_of_gradedEquiv [Module.Free (MvPolynomial σ k) M]
    [Module.Free (MvPolynomial σ k) N] (e : M ≃ₗ[MvPolynomial σ k] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n) :
    character (σ := σ) M.piece M.nonneg = character (σ := σ) N.piece N.nonneg := by
  let b := (exists_nonnegativeBasis (σ := σ) M.piece M.nonneg).some
  rw [character_eq M.piece M.nonneg b,
    character_eq N.piece N.nonneg (mapNonnegativeBasis e he b)]
  rfl

end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Decomposition
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem simpleRoot_mem (i : Bool) : (B.simpleRoot i).val ∈ P := by
  cases i
  · exact B.left_mem
  · exact B.right_mem

end PlaneBasis


end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
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

namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
noncomputable section

 theorem char_unit :
    (unit.{uk,max uk us,um} (polynomialGrading_negative k σ)).char=1 := by
  rw [char,character_eq _ _ (unitPolynomialBasis (k := k) (σ := σ))]
  change (∑ i : PUnit.{max uk us um + 1}, (X : Polynomial ℤ)^0)=1
  simp

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_3
theorem stalkCharacter_top :
    stalkCharacter cs 1 b basis (one_bruhat cs b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩=1 := by
  let B := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let := B.free ⟨b,one_bruhat cs b,bruhat_refl cs b⟩
  change (B.sheaf.vertex ⟨b,one_bruhat cs b,bruhat_refl cs b⟩).char=1
  exact (ModuleData.character_eq_of_gradedEquiv (ModuleData.equivOfEq B.top)
    (ModuleData.equivOfEq_graded B.top)).trans ModuleData.char_unit

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem mem_coset_of_graphRoot {P : Submodule ℝ (I → ℝ)} {a₀ x y : W}
    (h : BruhatStep cs x y) (hx : x*a₀⁻¹ ∈ planeSubgroup M cs P)
    (hy : (graphRoot h).val ∈ P) : y*a₀⁻¹ ∈ planeSubgroup M cs P := by
  have hm := (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents h)).mpr hy
  convert (planeSubgroup M cs P).mul_mem hm hx using 1
  all_goals try with_reducible_and_instances rfl
  group

end
end KLInvariance.TitsSpace

end


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem inverted_of_positive_combination (w : W) (a b c : PositiveRoot M cs)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : c.val = r • a.val + s • b.val)
    (ha : rootInverted w a) (hb : rootInverted w b) :
    rootInverted w c := by
  intro i
  rw [hc, map_add, map_smul, map_smul]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr (ha i))
    (mul_nonpos_of_nonneg_of_nonpos hs (hb i))

/-- Incoming graph labels are actual inversions at their upper vertex. -/
theorem graphRoot_inverted_target {x y : W} (h : BruhatStep cs x y) :
    rootInverted y (graphRoot h) := by
  apply ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 y).mpr
  refine ⟨h.label_reflection, ?_⟩
  have he : (y*x⁻¹)*y=x := by
    calc
      (y*x⁻¹)*y = (y*x⁻¹)*((y*x⁻¹)*x) := by group
      _ = x := by rw [← mul_assoc,h.label_reflection.mul_self,one_mul]
  simpa only [he] using h.1

/-- Outgoing graph labels are actual noninversions at their lower vertex. -/
theorem graphRoot_not_inverted_source {x y : W} (h : BruhatStep cs x y) :
    ¬ rootInverted x (graphRoot h) := by
  intro hi
  have hh := ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 x).mp hi
  have he : (y*x⁻¹)*x=y := by group
  have hh' := hh.2
  rw [he] at hh'
  exact lt_asymm h.1 hh'

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- In a plane with its first simple root inverted, every noninverted root
is later than every inverted root. This uses convexity, not a signed-index
formula for a particular realization. -/
theorem slope_lt_of_inverted_left (w : W) (hl : rootInverted w B.left)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b := by
  by_contra h
  have hba : geometricSlope b < geometricSlope a :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hlb : geometricSlope B.left < geometricSlope b :=
    lt_of_le_of_ne (B.left_min b hbP) (fun he => hb (geometricSlope_injective he ▸ hl))
  have heq : rootPlane B.left a = P :=
    rootPlane_eq_of_mem B.left B.right B.left a B.distinct
      (Submodule.subset_span (Set.mem_insert _ _))
      (B.plane_eq.ge haP) (fun he => by rw [he] at hlb; exact (lt_asymm hlb hba)) |>.trans B.plane_eq
  obtain ⟨r,s,hr,hs,hc⟩ := positive_combination_of_slope_between B.left a b
    (heq.symm ▸ hbP) hlb hba
  exact hb (inverted_of_positive_combination w B.left a b hr.le hs.le hc hl ha)

/-- The other angular cut, when the last simple root is inverted. -/
theorem slope_lt_of_inverted_right (w : W) (hr : rootInverted w B.right)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope b < geometricSlope a := by
  by_contra h
  have hab : geometricSlope a < geometricSlope b :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hbr : geometricSlope b < geometricSlope B.right :=
    lt_of_le_of_ne (B.right_max b hbP) (fun he => hb (geometricSlope_injective he ▸ hr))
  have har : a ≠ B.right := by
    intro he
    rw [he] at hab
    exact lt_asymm hbr hab
  have heq : rootPlane a B.right = P :=
    (rootPlane_eq_of_mem B.left B.right a B.right B.distinct
      (B.plane_eq.ge haP) (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      har).trans B.plane_eq
  obtain ⟨r,s,hrr,hss,hc⟩ := positive_combination_of_slope_between a B.right b
    (heq.symm ▸ hbP) hab hbr
  exact hb (inverted_of_positive_combination w a B.right b hrr.le hss.le hc ha hr)

/-- In the mixed-sign case the angular cut is determined by the first
canonical simple root. In particular the comparison of consecutive path
labels depends only on their middle vertex. -/
theorem slope_lt_iff_inverted_left (w : W)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b ↔ rootInverted w B.left := by
  constructor
  · intro hab
    by_contra hl
    have hr : rootInverted w B.right := by
      by_contra hr
      obtain ⟨r,s,hrr,hss,he⟩ := B.positive_cone a haP
      exact noninverted_of_positive_combination w B.left B.right a hrr hss he hl hr ha
    exact lt_asymm hab (B.slope_lt_of_inverted_right w hr a b haP hbP ha hb)
  · intro hl
    exact B.slope_lt_of_inverted_left w hl a b haP hbP ha hb

/-- The exact middle-vertex test for two ascending graph arrows with both
labels in this root plane. -/
theorem consecutive_slopes_iff {x y z : W}
    (hxy : BruhatStep cs x y) (hyz : BruhatStep cs y z)
    (ha : (graphRoot hxy).val ∈ P) (hb : (graphRoot hyz).val ∈ P) :
    geometricSlope (graphRoot hxy) < geometricSlope (graphRoot hyz) ↔
      rootInverted y B.left :=
  B.slope_lt_iff_inverted_left y _ _ ha hb
    (graphRoot_inverted_target hxy) (graphRoot_not_inverted_source hyz)

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

/-- A nonzero length below an existing greater length has exactly one left
simple descent. This is not asserted for a finite dihedral longest element. -/
theorem unique_leftDescent (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    ∃! i : Bool, cs.IsLeftDescent w i := by
  obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one (w := w) (by
    intro he
    rw [he,cs.length_one] at hw
    omega)
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  have hj' : j = !i := by cases i <;> cases j <;> simp_all
  have he : cs.wordProd (alt i (cs.length w)) =
      cs.wordProd (alt (!i) (cs.length w)) := by
    rw [← eq_alt_of_descent cs i hi, ← hj', ← eq_alt_of_descent cs j hj]
  obtain ⟨a,b,hab,hab'⟩ := two_elements_length cs hw hz
  have all_eq (v : W) (hv : cs.length v = cs.length w) : v=w := by
    obtain ⟨k,hk⟩ := exists_alt cs v
    rw [hv] at hk
    have hki : k=i ∨ k=(!i) := by cases k <;> cases i <;> simp
    rcases hki with hki | hki
    · rw [hki] at hk
      exact hk.trans (eq_alt_of_descent cs i hi).symm
    · rw [hki] at hk
      exact hk.trans (he.symm.trans (eq_alt_of_descent cs i hi).symm)
  exact hab ((all_eq a ((hab' a).mpr (.inl rfl))).trans
    (all_eq b ((hab' b).mpr (.inr rfl))).symm)

/-- Internally, the diagram involution interchanges the two unique-descent
vertices of each rank. -/
theorem descent_swap_false_iff_not (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    cs.IsLeftDescent (swap cs w) false ↔ ¬ cs.IsLeftDescent w false := by
  rw [descent_swap]
  obtain ⟨i,hi,hu⟩ := unique_leftDescent cs hw hz
  cases i
  · constructor
    · intro h
      have hh := hu true h
      contradiction
    · exact fun h => (h hi).elim
  · constructor
    · intro _ h
      have hh := hu false h
      contradiction
    · exact fun _ => hi

end
end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- The ambient sign of a canonical plane root in a minimal coset is the
intrinsic simple-descent sign, with the original left labels. -/
theorem simpleRoot_inverted_coset_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (w : planeSubgroup M cs P) (i : Bool) :
    rootInverted ((w : W)*a₀) (B.simpleRoot i) ↔ B.system.IsLeftDescent w i := by
  change (∀ k, action M cs ((w : W)*a₀)⁻¹ (B.simpleRoot i).val k ≤ 0) ↔ _
  rw [root_inversion_coset_iff hmin w.property (B.simpleRoot i).property.1
    (B.simpleRoot_mem i)]
  have hr : Represents M cs (B.system.simple i : W) (B.simpleRoot i).val := by
    rw [B.system_simple]
    exact rootReflection_represents M cs _
  rw [B.inversion_iff hr (B.simpleRoot_mem i) (B.simpleRoot i).property.2 w]
  exact B.system.isLeftInversion_simple_iff_isLeftDescent w i

theorem edgeRoot_plane {x y : planeSubgroup M cs P} (h : BruhatStep B.system x y) :
    (B.edgeRoot h).val ∈ P := by
  apply (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents
    ((B.bruhatStep_iff x y).mpr h))).mp
  exact (planeSubgroup M cs P).mul_mem y.property
    ((planeSubgroup M cs P).inv_mem x.property)

/-- In the intrinsic system, the middle-vertex test uses its actual left
simple generator; it therefore applies to any induced dihedral realization. -/
theorem edgeRoot_slopes_iff {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      B.system.IsLeftDescent y false := by
  unfold edgeRoot
  rw [B.consecutive_slopes_iff ((B.bruhatStep_iff x y).mpr hxy)
    ((B.bruhatStep_iff y z).mpr hyz) (B.edgeRoot_plane hxy) (B.edgeRoot_plane hyz)]
  have hmin : ∀ z ∈ planeSubgroup M cs P, cs.length (1:W) ≤ cs.length (z*1) :=
    fun z _ => by simp
  simpa only [mul_one, simpleRoot, Bool.false_eq_true, ↓reduceIte] using
    B.simpleRoot_inverted_coset_iff hmin y false

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Geometric orders adapted to a fixed upper vertex. These are honest
ratios of linear functionals, with a strictly positive denominator. They
will be used only as a permissible choice of the source's schedule. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem simplePositive_injective : Function.Injective (simplePositive (M := M) (cs := cs)) := by
  intro i j hij
  have he := congrArg (fun a : PositiveRoot M cs => a.val i) hij
  by_contra hne
  simp [simplePositive, root, hne] at he

theorem height_positive : PositiveFunctional (height (I := I)) := by
  intro i
  simp [height,root]

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem simple_lower_bound (i : I)
    (hi : ∀ j, O.slope (simplePositive i) ≤ O.slope (simplePositive j))
    (a : PositiveRoot M cs) : O.slope (simplePositive i) ≤ O.slope a := by
  change O.slope (simplePositive i) ≤ O.numerator a.val / O.denominator a.val
  rw [le_div_iff₀ (O.denominator_pos a)]
  rw [dual_coordinate_sum O.numerator a.val, dual_coordinate_sum O.denominator a.val,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj := (le_div_iff₀ (O.positive j)).mp (hi j)
  change O.slope (simplePositive i) * O.denominator (root j) ≤ O.numerator (root j) at hj
  nlinarith [mul_nonneg (a.property.2 j) (sub_nonneg.mpr hj)]

theorem exists_least_simple [Nonempty I] : ∃ i : I,
    ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image (Finset.univ : Finset I)
    (fun i => O.slope (simplePositive i)) Finset.univ_nonempty
  exact ⟨i, O.simple_lower_bound i (fun j => hi j (Finset.mem_univ j))⟩

theorem least_simple_descent {y : W} (hy : y ≠ 1) (ha : O.Adapted y) :
    ∃ i : I, cs.IsLeftDescent y i ∧
      O.slope (simplePositive i) < 0 ∧
      ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a := by
  obtain ⟨j,hj⟩ := cs.exists_leftDescent_of_ne_one hy
  let : Nonempty I := ⟨j⟩
  obtain ⟨i,hi⟩ := O.exists_least_simple
  have hjr : rootInverted y (simplePositive (M := M) (cs := cs) j) := by
    apply ((rootReflection_represents M cs _).inversion_iff (simplePositive j).property.2 y).mpr
    simpa only [rootRef_simplePositive] using (show cs.IsLeftInversion y (cs.simple j) from
      ⟨cs.isReflection_simple j,hj⟩)
  have hi0 := lt_of_le_of_lt (hi (simplePositive j)) ((ha _).1.mpr hjr)
  refine ⟨i,?_,hi0,hi⟩
  have hir := ((rootReflection_represents M cs _).inversion_iff
    (simplePositive i).property.2 y).mp ((ha _).1.mp hi0)
  simpa only [rootRef_simplePositive, CoxeterSystem.IsLeftDescent] using hir.2


theorem adapted_of_chamber {y : W} (hc : O.Chamber y) : O.Adapted y := by
  let f : Module.Dual ℝ (I → ℝ) := O.numerator.comp (action M cs y).toLinearMap
  have hf : PositiveFunctional f := hc
  intro a
  have he (v : I → ℝ) : f (action M cs y⁻¹ v) = O.numerator v := by
    change O.numerator (action M cs y (action M cs y⁻¹ v)) = _
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  by_cases ha : rootInverted y a
  · have hv := hf.root_pos (positiveAction y⁻¹ a)
    rw [positiveAction_eq_of_nonpos _ _ ha, map_neg, he] at hv
    have hn : O.slope a < 0 := div_neg_of_neg_of_pos (by linarith) (O.denominator_pos a)
    exact ⟨iff_of_true hn ha, hn.ne⟩
  · have hp := (not_rootInverted_iff y a).mp ha
    have hv := hf.root_pos (positiveAction y⁻¹ a)
    rw [positiveAction_eq_of_nonneg _ _ hp, he] at hv
    have hn : 0 < O.slope a := div_pos hv (O.denominator_pos a)
    exact ⟨iff_of_false (not_lt.mpr hn.le) ha, hn.ne'⟩

end RatioOrder

/-- The generic functional can be chosen in any prescribed Coxeter chamber,
not just outside the countably many equality hyperplanes. The explicit
polynomial perturbation makes both requirements simultaneous. -/
theorem exists_ratioOrder_chamber_height (y : W) :
    ∃ O : RatioOrder (M := M) (cs := cs), O.Chamber y ∧ O.denominator=height := by
  classical
  let := countable_Positiveroot M cs
  let f₀ : Module.Dual ℝ (I → ℝ) := height.comp (action M cs y⁻¹).toLinearMap
  let f : ℝ → Module.Dual ℝ (I → ℝ) := fun t =>
    f₀ + t • ReflectionSchedules.momentFunctional t
  have hf (t : ℝ) (v : I → ℝ) : f t v = f₀ v +
      t * (ReflectionSchedules.coordinatePolynomial v).eval t := by
    simp [f,ReflectionSchedules.coordinatePolynomial_eval]
  let U : Set ℝ := {t | ∀ i, 0 < f t (action M cs y (root i))}
  have hu : IsOpen U := by
    change IsOpen {t | ∀ i, 0 < f t (action M cs y (root i))}
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt continuous_const
    simp only [hf]
    exact continuous_const.add (continuous_id.mul (Polynomial.continuous _))
  have h0 : 0 ∈ U := by
    intro i
    simp only [f,zero_smul,add_zero]
    change 0 < height (action M cs y⁻¹ (action M cs y (root i)))
    rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
    exact height_positive i
  let P := {p : PositiveRoot M cs × PositiveRoot M cs // p.1 ≠ p.2}
  let v : P → (I → ℝ) := fun p => normalizedRoot p.val.1 - normalizedRoot p.val.2
  let d : P → Polynomial ℝ := fun p => Polynomial.C (f₀ (v p)) +
    Polynomial.X * ReflectionSchedules.coordinatePolynomial (v p)
  have hd : ∀ p, d p ≠ 0 := by
    intro p hp
    have hz := congrArg (fun q : Polynomial ℝ => q.eval 0) hp
    have hz' : f₀ (v p) = 0 := by simpa [d] using hz
    have hq : ReflectionSchedules.coordinatePolynomial (v p) = 0 := by
      simpa only [d,hz',Polynomial.C_0,zero_add,mul_eq_zero,Polynomial.X_ne_zero,false_or] using hp
    have hv : v p = 0 := ReflectionSchedules.coordinatePolynomial_injective (by simpa [ReflectionSchedules.coordinatePolynomial] using hq)
    exact p.property (normalizedRoot_injective (sub_eq_zero.mp hv))
  let bad : Set ℝ := ⋃ p : P, {t | (d p).IsRoot t}
  have hbad : bad.Countable := Set.countable_iUnion
    (fun p => (Polynomial.finite_setOfPred_isRoot (hd p)).countable)
  obtain ⟨t,htU,ht⟩ := (hbad.dense_compl ℝ).inter_open_nonempty U hu ⟨0,h0⟩
  have hinj : Function.Injective (fun a : PositiveRoot M cs => f t a.val / height a.val) := by
    intro a b heq
    by_contra hab
    apply ht
    apply Set.mem_iUnion.mpr
    refine ⟨⟨(a,b),hab⟩,?_⟩
    change (d ⟨(a,b),hab⟩).eval t = 0
    dsimp only [d]
    rw [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,← hf]
    change f t (normalizedRoot a - normalizedRoot b) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    simpa only [normalizedRoot,map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm] using heq
  exact ⟨⟨height,f t,height_positive,hinj⟩,htU,rfl⟩

theorem simple_action_nonneg (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) : ∀ k, 0 ≤ action M cs (cs.simple i) a.val k := by
  apply a.property.1.act (cs.simple i) |>.sign.resolve_right
  intro hn
  exact ha (Subtype.ext (a.property.1.eq_simple_of_nonpos a.property.2 i hn))

theorem simple_positiveAction_val (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) :
    (positiveAction (cs.simple i) a).val = action M cs (cs.simple i) a.val :=
  positiveAction_eq_of_nonneg _ _ (simple_action_nonneg i a ha)

theorem simple_positiveAction_ne (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) : positiveAction (cs.simple i) a ≠ simplePositive i := by
  intro he
  apply ha
  exact (positiveActionEquiv (cs.simple i)).injective (he.trans (positiveAction_simplePositive i).symm)

theorem exists_uniform_pos_lt (v : I → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε < v i := by
  have aux (s : Finset I) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε < v i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ε,hε,hlt⟩ := ih
      refine ⟨min ε (v a / 2),lt_min hε (half_pos (hv a)),?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (hv i))
      · exact lt_of_le_of_lt (min_le_left _ _) (hlt i hi)
  obtain ⟨ε,hε,hlt⟩ := aux Finset.univ
  exact ⟨ε,hε,fun i => hlt i (Finset.mem_univ i)⟩

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_8
theorem exists_turn_parameter (i : I) (hi0 : O.slope (simplePositive i) < 0)
    (hi : ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a) :
    ∃ k : ℝ, k < 0 ∧ O.slope (simplePositive i) < k ∧
      PositiveFunctional (O.turnDenominator i k) := by
  let c := O.slope (simplePositive i)
  let v : I → ℝ := fun j => if j=i then -c else
    O.slope (positiveAction (cs.simple i) (simplePositive j)) - c
  have hv : ∀ j, 0 < v j := by
    intro j
    by_cases hj : j=i
    · simp only [v,ite_eq_left hj]
      exact neg_pos.mpr hi0
    · simp only [v,ite_eq_right hj]
      apply sub_pos.mpr
      apply lt_of_le_of_ne (hi _)
      intro he
      exact simple_positiveAction_ne i (simplePositive j)
        (fun hh => hj (simplePositive_injective hh)) (O.slope_injective he.symm)
  obtain ⟨ε,hε,hεv⟩ := exists_uniform_pos_lt v hv
  have hεc : ε < -c := by simpa only [v,ite_eq_left rfl] using hεv i
  refine ⟨c+ε,by linarith,by dsimp [c]; linarith,?_⟩
  intro j
  change 0 < O.numerator (action M cs (cs.simple i) (root j)) -
    (c+ε)*O.denominator (action M cs (cs.simple i) (root j))
  by_cases hj : j=i
  · subst j
    rw [action_simple_root,map_neg,map_neg]
    have hc : c * O.denominator (root i) = O.numerator (root i) := by
      exact div_mul_cancel₀ _ (O.positive i).ne'
    nlinarith [mul_pos hε (O.positive i)]
  · let a := positiveAction (cs.simple i) (simplePositive (M := M) (cs := cs) j)
    have ha : a.val = action M cs (cs.simple i) (root j) :=
      simple_positiveAction_val i (simplePositive j) (fun hh => hj (simplePositive_injective hh))
    rw [← ha]
    have hvj : ε < O.slope a - c := by simpa only [v,ite_eq_right hj] using hεv j
    have hlt : c+ε < O.slope a := by linarith
    exact sub_pos.mpr ((lt_div_iff₀ (O.denominator_pos a)).mp hlt)


theorem turn_chamber (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) {y : W} (hy : O.Chamber y) :
    (O.turn i k hk hp).Chamber (cs.simple i * y) := by
  intro j
  change 0 < O.numerator (action M cs (cs.simple i)
    (action M cs (cs.simple i * y) (root j)))
  rw [← LinearEquiv.mul_apply,← map_mul,cs.simple_mul_simple_cancel_left]
  exact hy j

theorem turn_simple_greatest (i : I) (k : ℝ) (hk : k < 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) :
    (O.turn i k hk.ne hp).slope a < (O.turn i k hk.ne hp).slope (simplePositive i) := by
  have hlt : (O.turn i k hk.ne hp).slope a < 1 := by
    apply (div_lt_iff₀ (hp.root_pos a)).mpr
    change O.numerator (action M cs (cs.simple i) a.val) <
      1 * (O.numerator (action M cs (cs.simple i) a.val) -
        k * O.denominator (action M cs (cs.simple i) a.val))
    have hap := O.denominator_pos (positiveAction (cs.simple i) a)
    rw [simple_positiveAction_val i a ha] at hap
    nlinarith [mul_neg_of_neg_of_pos hk hap]
  have hgt : 1 < (O.turn i k hk.ne hp).slope (simplePositive i) := by
    apply (lt_div_iff₀ (hp.root_pos (simplePositive i))).mpr
    change 1 * (O.numerator (action M cs (cs.simple i) (root i)) -
       k * O.denominator (action M cs (cs.simple i) (root i))) <
      O.numerator (action M cs (cs.simple i) (root i))
    rw [action_simple_root,map_neg,map_neg]
    nlinarith [mul_neg_of_neg_of_pos hk (O.positive i)]
  exact hlt.trans hgt

theorem turn_slope_lt_iff (i : I) (k : ℝ) (hk : k < 0)
    (hp : PositiveFunctional (O.turnDenominator i k))
    (a b : PositiveRoot M cs) (ha : a ≠ simplePositive i) (hb : b ≠ simplePositive i) :
    (O.turn i k hk.ne hp).slope (positiveAction (cs.simple i) a) <
      (O.turn i k hk.ne hp).slope (positiveAction (cs.simple i) b) ↔ O.slope a < O.slope b := by
  have hact (a : PositiveRoot M cs) (ha : a ≠ simplePositive i) :
      action M cs (cs.simple i) (positiveAction (cs.simple i) a).val = a.val := by
    rw [simple_positiveAction_val i a ha,← LinearEquiv.mul_apply,← map_mul,
      (cs.isReflection_simple i).mul_self,map_one]
    rfl
  have haD := hp.root_pos (positiveAction (cs.simple i) a)
  have hbD := hp.root_pos (positiveAction (cs.simple i) b)
  change 0 < O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) -
    k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) at haD
  change 0 < O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) -
    k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) at hbD
  rw [hact a ha] at haD
  rw [hact b hb] at hbD
  change O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) /
    (O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) -
      k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val)) <
    O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) /
    (O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) -
      k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val)) ↔
    O.numerator a.val / O.denominator a.val < O.numerator b.val / O.denominator b.val
  rw [hact a ha,hact b hb,div_lt_div_iff₀ haD hbD,
    div_lt_div_iff₀ (O.denominator_pos a) (O.denominator_pos b)]
  constructor
  · intro h
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg hk.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
  · intro h
    have := mul_neg_of_neg_of_pos hk (sub_pos.mpr h)
    nlinarith

/-- The actual geometric rotation needed for the Hecke recursion. It moves
the least simple root to last and preserves all other root comparisons. -/
theorem exists_rotation {y : W} (hy : y ≠ 1) (hc : O.Chamber y) :
    ∃ (i : I) (O' : RatioOrder (M := M) (cs := cs)),
      cs.IsLeftDescent y i ∧ O'.Chamber (cs.simple i * y) ∧
      (∀ a : PositiveRoot M cs, a ≠ simplePositive i →
        O.slope (simplePositive i) < O.slope a ∧ O'.slope a < O'.slope (simplePositive i)) ∧
      (∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
        (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
          O.slope a < O.slope b)) := by
  obtain ⟨i,hi,hi0,hmin⟩ := O.least_simple_descent hy (O.adapted_of_chamber hc)
  obtain ⟨k,hk,_,hpos⟩ := O.exists_turn_parameter i hi0 hmin
  refine ⟨i,O.turn i k hk.ne hpos,hi,O.turn_chamber i k hk.ne hpos hc,?_,?_⟩
  · intro a ha
    exact ⟨lt_of_le_of_ne (hmin a) (fun he => ha (O.slope_injective he).symm),
      O.turn_simple_greatest i k hk hpos a ha⟩
  · exact O.turn_slope_lt_iff i k hk hpos

end RatioOrder

end
end KLInvariance.TitsSpace

end


section

/-! Rank-two path reversal in the actual induced root plane, for every finite
full interval. This is a required Dyer wall-crossing relation, not the Dyer
identification itself. -/

namespace KLInvariance.SchedulePaths
variable {V E V' E' : Type*} (source target : E → V) (source' target' : E' → V')

/-- Relabelling graph vertices and edges preserves the actual path predicate. -/
theorem IsPath.map {x y : V} {p : List E}
    (hp : IsPath source target x y p) (f : V → V') (g : E → E')
    (hs : ∀ e, source' (g e) = f (source e))
    (ht : ∀ e, target' (g e) = f (target e)) :
    IsPath source' target' (f x) (f y) (p.map g) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
    exact ⟨(hs e).trans (congrArg f hp.1), ht e ▸ ih hp.2⟩

/-- A path's adjacent comparisons suffice for a transitive label order. The
statement allows the comparison to change under an edge map, provided the
local relation is checked only on composable edges. -/
theorem IsPath.pairwise_map_of_local {Λ Λ' : Type*} [LinearOrder Λ] [LinearOrder Λ']
    {x y : V} {p : List E} (hp : IsPath source target x y p)
    (label : E → Λ) (label' : E' → Λ') (g : E → E')
    (hlocal : ∀ e f, target e = source f →
      label e < label f → label' (g e) < label' (g f))
    (horder : p.Pairwise (fun e f => label e < label f)) :
    (p.map g).Pairwise (fun e f => label' e < label' f) := by
  rw [← List.isChain_iff_pairwise] at horder ⊢
  rw [List.isChain_map]
  induction p generalizing x with
  | nil => exact .nil
  | cons e p ih =>
    cases p with
    | nil => exact .singleton e
    | cons f p =>
      rw [List.isChain_cons_cons] at horder ⊢
      exact ⟨hlocal e f hp.2.1.symm horder.1, ih hp.2 horder.2⟩

end KLInvariance.SchedulePaths

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph

attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable
theorem edgeRoot_ne_of_path {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    B.edgeRoot hxy ≠ B.edgeRoot hyz :=
  graphRoot_ne_of_path ((B.bruhatStep_iff x y).mpr hxy) ((B.bruhatStep_iff y z).mpr hyz)

/-- At every internal vertex, the cut switches side under the path involution.
This is the local relation behind rank-two path-product reversal. -/
theorem edgeRoot_slopes_rankFlip {x y z top : planeSubgroup M cs P} {L : ℕ}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z)
    (hL : L < B.system.length y) (hH : B.system.length y < B.system.length top) :
    let hx := (rankFlip_step_iff B.system L (B.system.length top) x y).mpr hxy
    let hz := (rankFlip_step_iff B.system L (B.system.length top) y z).mpr hyz
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      geometricSlope (B.edgeRoot hz) < geometricSlope (B.edgeRoot hx) := by
  dsimp only
  let hx := (rankFlip_step_iff B.system L (B.system.length top) x y).mpr hxy
  let hz := (rankFlip_step_iff B.system L (B.system.length top) y z).mpr hyz
  have hsign : B.system.IsLeftDescent
      (rankFlip B.system L (B.system.length top) y) false ↔
      ¬ B.system.IsLeftDescent y false := by
    rw [rankFlip,ite_eq_left ⟨hL,hH⟩]
    exact descent_swap_false_iff_not B.system (by omega) hH
  have hne : geometricSlope (B.edgeRoot hx) ≠ geometricSlope (B.edgeRoot hz) :=
    fun he => B.edgeRoot_ne_of_path hx hz (geometricSlope_injective he)
  rw [B.edgeRoot_slopes_iff]
  constructor
  · intro hi
    have hn : ¬ geometricSlope (B.edgeRoot hx) < geometricSlope (B.edgeRoot hz) := by
      rw [B.edgeRoot_slopes_iff,hsign]
      exact not_not.mpr hi
    exact lt_of_le_of_ne (le_of_not_gt hn) hne.symm
  · intro hi
    by_contra hn
    have hlt := (B.edgeRoot_slopes_iff hx hz).mpr (hsign.mpr hn)
    exact lt_asymm hlt hi

/-- The global edge map reverses the comparison for every composable pair.
No statement is asserted for disjoint edge labels, which can share ties. -/
theorem intervalEdgeSlope_flip {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi)
    (hjoin : target B.system lo hi e = source B.system lo hi f) :
    B.intervalEdgeSlope lo hi e < B.intervalEdgeSlope lo hi f ↔
      B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi f) <
        B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi e) := by
  rcases e with ⟨⟨ex,ey⟩,he⟩
  rcases f with ⟨⟨fx,fy⟩,hf⟩
  change ey = fx at hjoin
  subst fx
  have hl : B.system.length lo < B.system.length ey.val :=
    lt_of_le_of_lt (length_le_of_bruhat B.system ex.property.1) he.1
  have hh : B.system.length ey.val < B.system.length hi :=
    lt_of_lt_of_le hf.1 (length_le_of_bruhat B.system fy.property.2)
  exact B.edgeRoot_slopes_rankFlip he hf hl hh

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.SchedulePaths
open scoped BigOperators
variable {V E R : Type*} (source target : E → V)
noncomputable section

variable [Semiring R]

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_1
theorem dispatch_eq_subpaths_sum (T : R) (schedule : List E) (hnd : schedule.Nodup)
    (x y : V) :
    dispatch source target T (fun z => if z=y then 1 else 0) schedule x =
      ∑ p ∈ subpaths source target schedule x y, T ^ p.length := by
  rw [entry_eq_weighted_paths, subpaths, Finset.sum_filter,
    List.sum_toFinset _ (List.nodup_sublists'.mpr hnd)]

/-- A length-preserving involution on the actual schedule-path sets proves
an operator-entry relation, with no Hecke polynomial used in the assumptions. -/
theorem dispatch_eq_of_path_involution (T : R) (schedule schedule' : List E)
    (hnd : schedule.Nodup) (hnd' : schedule'.Nodup) (x y : V) (g : E → E)
    (hg : Function.Involutive g)
    (hforward : ∀ p ∈ subpaths source target schedule x y,
      p.map g ∈ subpaths source target schedule' x y)
    (hbackward : ∀ p ∈ subpaths source target schedule' x y,
      p.map g ∈ subpaths source target schedule x y) :
    dispatch source target T (fun z => if z=y then 1 else 0) schedule x =
      dispatch source target T (fun z => if z=y then 1 else 0) schedule' x := by
  rw [dispatch_eq_subpaths_sum source target T schedule hnd,
    dispatch_eq_subpaths_sum source target T schedule' hnd']
  exact Finset.sum_nbij' (List.map g) (List.map g) hforward hbackward
    (fun p _ => List.map_involutive_iff.mpr hg p)
    (fun p _ => List.map_involutive_iff.mpr hg p) (fun p _ => by simp)

end
end KLInvariance.SchedulePaths

namespace KLInvariance.SchedulePaths
variable {V E : Type*} (source target : E → V)
noncomputable section

local instance instDecidable_solutions_2_ra2d10a_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Sorted full schedules select precisely their strictly monotone paths;
an actual graph map satisfying the adjacent comparison test transports them. -/
theorem subpaths_map_of_sorted (label label' : E → ℝ)
    (schedule schedule' : List E) (x y : V)
    (hs : schedule.Pairwise (fun e f => label f ≤ label e))
    (hs' : schedule'.Pairwise (fun e f => label' f ≤ label' e))
    (hfull' : ∀ e, e ∈ schedule')
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (f : V → V) (g : E → E)
    (hsource : ∀ e, source (g e) = f (source e))
    (htarget : ∀ e, target (g e) = f (target e))
    (hx : f x=x) (hy : f y=y)
    (hlocal : ∀ e f, target e=source f → label f<label e → label' (g f)<label' (g e))
    (p : List E) (hp : p ∈ subpaths source target schedule x y) :
    p.map g ∈ subpaths source target schedule' x y := by
  obtain ⟨hsub,hp⟩ := (mem_subpaths source target schedule x y p).mp hp
  have hstrict := decreasing_of_schedule_path source target label hties hp (hs.sublist hsub)
  have horder := hp.pairwise_map_of_local source target
    (Λ := OrderDual ℝ) (Λ' := OrderDual ℝ)
    (fun e => (label e : OrderDual ℝ)) (fun e => (label' e : OrderDual ℝ)) g hlocal hstrict
  have hp' := hp.map source target source target f g hsource htarget
  rw [hx,hy] at hp'
  exact (mem_subpaths source target schedule' x y (p.map g)).mpr
    ⟨sublist_of_decreasing_subset label' horder hs' (fun _ _ => hfull' _), hp'⟩

end
end KLInvariance.SchedulePaths

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph SchedulePaths

attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_1
theorem intervalEdgeSlope_ties {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi) (heq : B.intervalEdgeSlope lo hi e = B.intervalEdgeSlope lo hi f) :
    target B.system lo hi e ≠ source B.system lo hi f := by
  intro hjoin
  rcases e with ⟨⟨ex,ey⟩,he⟩
  rcases f with ⟨⟨fx,fy⟩,hf⟩
  change ey = fx at hjoin
  subst fx
  exact B.edgeRoot_ne_of_path he hf (geometricSlope_injective heq)

theorem intervalEdgeSlope_flip_reverse {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi)
    (hjoin : target B.system lo hi e = source B.system lo hi f) :
    B.intervalEdgeSlope lo hi f < B.intervalEdgeSlope lo hi e ↔
      B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi e) <
        B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi f) := by
  have hj : target B.system lo hi (edgeFlip B.system lo hi e) =
      source B.system lo hi (edgeFlip B.system lo hi f) := by
    simpa only [edgeFlip_source,edgeFlip_target] using congrArg (intervalFlip B.system lo hi) hjoin
  simpa only [edgeFlip_involutive B.system lo hi e, edgeFlip_involutive B.system lo hi f] using
    (B.intervalEdgeSlope_flip (edgeFlip B.system lo hi e) (edgeFlip B.system lo hi f) hj).symm

/-- Rank-two reversal of the genuine path-product entry between the two
ends of any full interval. The order is the actual induced angular order. -/
theorem dispatch_reverse_endpoints {R : Type*} [Semiring R]
    {lo hi : planeSubgroup M cs P} (hlohi : BruhatLE B.system lo hi)
    (schedule : List (Edge B.system lo hi)) (hnd : schedule.Nodup)
    (hfull : ∀ e, e ∈ schedule)
    (hs : schedule.Pairwise (fun e f => B.intervalEdgeSlope lo hi f ≤ B.intervalEdgeSlope lo hi e))
    (T : R) :
    let x : Interval B.system lo hi := ⟨lo,bruhat_refl B.system lo,hlohi⟩
    let y : Interval B.system lo hi := ⟨hi,hlohi,bruhat_refl B.system hi⟩
    dispatch (source B.system lo hi) (target B.system lo hi) T
      (fun z => if z=y then 1 else 0) schedule x =
    dispatch (source B.system lo hi) (target B.system lo hi) T
      (fun z => if z=y then 1 else 0) schedule.reverse x := by
  dsimp only
  let x : Interval B.system lo hi := ⟨lo,bruhat_refl B.system lo,hlohi⟩
  let y : Interval B.system lo hi := ⟨hi,hlohi,bruhat_refl B.system hi⟩
  have hx : intervalFlip B.system lo hi x=x := Subtype.ext (rankFlip_lower B.system lo hi)
  have hy : intervalFlip B.system lo hi y=y := Subtype.ext (rankFlip_upper B.system lo hi)
  have hrs : schedule.reverse.Pairwise
      (fun e f => -B.intervalEdgeSlope lo hi f ≤ -B.intervalEdgeSlope lo hi e) := by
    rw [List.pairwise_reverse]
    exact hs.imp (fun h => neg_le_neg h)
  have hrfull : ∀ e, e ∈ schedule.reverse := fun e => List.mem_reverse.mpr (hfull e)
  apply dispatch_eq_of_path_involution _ _ T schedule schedule.reverse hnd (List.nodup_reverse.mpr hnd) x y
    (edgeFlip B.system lo hi) (edgeFlip_involutive B.system lo hi)
  · apply subpaths_map_of_sorted _ _ (B.intervalEdgeSlope lo hi)
      (fun e => -B.intervalEdgeSlope lo hi e) schedule schedule.reverse x y hs hrs hrfull
      (B.intervalEdgeSlope_ties) (intervalFlip B.system lo hi) (edgeFlip B.system lo hi)
      (edgeFlip_source B.system lo hi) (edgeFlip_target B.system lo hi) hx hy
    intro e f hj hlt
    exact neg_lt_neg ((B.intervalEdgeSlope_flip_reverse e f hj).mp hlt)
  · apply subpaths_map_of_sorted _ _ (fun e => -B.intervalEdgeSlope lo hi e)
      (B.intervalEdgeSlope lo hi) schedule.reverse schedule x y hrs hs hfull
      (fun e f he => B.intervalEdgeSlope_ties e f (neg_injective he))
      (intervalFlip B.system lo hi) (edgeFlip B.system lo hi)
      (edgeFlip_source B.system lo hi) (edgeFlip_target B.system lo hi) hx hy
    intro e f hj hlt
    exact (B.intervalEdgeSlope_flip e f hj).mp (neg_lt_neg_iff.mp hlt)

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Genuine Dyer identification for geometric orders adapted to a fixed top.
The path values below are defined from actual reflection edges; equality with
`Hecke.rTilde` will be proved by its genuine simple-descent recurrence. -/
namespace KLInvariance.AdaptedDyer
open TitsSpace SchedulePaths
open scoped BigOperators
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

attribute [local instance] OAI.KLInvariance.AdaptedDyer.instDecidable_solutions
theorem target_eq_root (e : Edge cs) :
    target cs e = rootRef (rootLabel cs e) * source cs e := by
  rw [rootRef_rootLabel]
  group

theorem rootLabel_ne_of_join (e f : Edge cs) (h : target cs e = source cs f) :
    rootLabel cs e ≠ rootLabel cs f := by
  rcases e with ⟨⟨x,y⟩,he⟩
  rcases f with ⟨⟨z,w⟩,hf⟩
  change y=z at h
  subst z
  exact graphRoot_ne_of_path he hf

variable {cs}

theorem score_ties (O : RatioOrder (M := M) (cs := cs)) (e f : Edge cs)
    (h : score O e = score O f) : target cs e ≠ source cs f :=
  fun hj => rootLabel_ne_of_join cs e f hj (O.slope_injective h)

variable (cs)

variable {cs}

theorem schedule_increasing (O : RatioOrder (M := M) (cs := cs)) (b : W) :
    (schedule O b).Pairwise (fun e f => score O e ≤ score O f) := by
  unfold schedule
  apply List.pairwise_mergeSort'

variable (cs)
omit [Fintype I] in
theorem path_le {x y : W} {p : List (Edge cs)}
    (hp : IsPath (source cs) (target cs) x y p) : BruhatLE cs x y := by
  induction p generalizing x with
  | nil => exact hp ▸ .refl
  | cons e p ih =>
    exact hp.1 ▸ (show BruhatLE cs (source cs e) (target cs e) from .single e.property).trans (ih hp.2)

omit [Fintype I] in
theorem path_targets_le {x y : W} {p : List (Edge cs)}
    (hp : IsPath (source cs) (target cs) x y p) :
    ∀ e ∈ p, BruhatLE cs (target cs e) y := by
  induction p generalizing x with
  | nil => simp
  | cons e p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact path_le cs hp.2
    · exact ih hp.2 f hf

variable {cs}

@[simp] theorem mem_paths (O : RatioOrder (M := M) (cs := cs)) (x y : W) (p : List (Edge cs)) :
    p ∈ paths O x y ↔ IsPath (source cs) (target cs) x y p ∧
      p.Pairwise (fun e f => score O e < score O f) := by
  rw [paths,mem_subpaths]
  constructor
  · rintro ⟨hsub,hp⟩
    refine ⟨hp,?_⟩
    exact decreasing_of_schedule_path (source cs) (target cs)
      (Λ := OrderDual ℝ) (fun e => (score O e : OrderDual ℝ))
      (fun e f h => score_ties O e f h) hp ((schedule_increasing O y).sublist hsub)
  · rintro ⟨hp,hord⟩
    refine ⟨?_,hp⟩
    apply sublist_of_decreasing_subset (Λ := OrderDual ℝ)
      (fun e => (score O e : OrderDual ℝ)) hord (schedule_increasing O y)
    intro e he
    exact (mem_schedule O y e).mpr (path_targets_le cs hp e he)


variable (cs)
theorem rootRef_injective : Function.Injective (rootRef (M := M) (cs := cs)) := by
  intro a b h
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext h

theorem rootLabel_simple_iff (i : I) (e : Edge cs) :
    rootLabel cs e = simplePositive i ↔ target cs e = cs.simple i * source cs e := by
  constructor
  · intro h
    rw [target_eq_root cs e,h,rootRef_simplePositive]
  · intro h
    apply rootRef_injective cs
    rw [rootRef_rootLabel,rootRef_simplePositive,h]
    group

theorem rotateEdge_val (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    (rotateEdge cs i e).val = (cs.simple i * source cs e,cs.simple i * target cs e) := by
  rw [rotateEdge,dite_eq_right (fun hh => h ((rootLabel_simple_iff cs i e).mpr hh))]

theorem rotateEdge_root (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    rootLabel cs (rotateEdge cs i e) = positiveAction (cs.simple i) (rootLabel cs e) := by
  apply rootRef_injective cs
  rw [rootRef_rootLabel]
  change (rotateEdge cs i e).val.2 * (rotateEdge cs i e).val.1⁻¹ =
    rootRef (positiveAction (cs.simple i) (rootLabel cs e))
  have hc : rootRef (positiveAction (cs.simple i) (rootLabel cs e)) =
      cs.simple i * rootRef (rootLabel cs e) * (cs.simple i)⁻¹ :=
    rootReflection_positiveAction _ _
  rw [rotateEdge_val cs i e h,hc,rootRef_rootLabel]
  group

theorem rotateEdge_nonsimple (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    rootLabel cs (rotateEdge cs i e) ≠ simplePositive i := by
  rw [rotateEdge_root cs i e h]
  exact simple_positiveAction_ne i _ h

@[simp] theorem rotateEdge_involutive (i : I) : Function.Involutive (rotateEdge cs i) := by
  intro e
  by_cases h : rootLabel cs e = simplePositive i
  · have he : rotateEdge cs i e = e := by
      rw [rotateEdge,dite_eq_left ((rootLabel_simple_iff cs i e).mp h)]
    rw [he,he]
  · apply Subtype.ext
    rw [rotateEdge_val cs i _ (rotateEdge_nonsimple cs i e h)]
    change (cs.simple i * (rotateEdge cs i e).val.1,
      cs.simple i * (rotateEdge cs i e).val.2) = e.val
    rw [rotateEdge_val cs i e h]
    simp only [cs.simple_mul_simple_cancel_left]
    rfl

omit [Fintype I] in
theorem path_map_of_mem {E E' V V' : Type*} (src tgt : E → V) (src' tgt' : E' → V')
    {p : List E} {x y : V} (hp : IsPath src tgt x y p) (f : V → V') (g : E → E')
    (hs : ∀ e ∈ p, src' (g e) = f (src e)) (ht : ∀ e ∈ p, tgt' (g e) = f (tgt e)) :
    IsPath src' tgt' (f x) (f y) (p.map g) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
    refine ⟨(hs e List.mem_cons_self).trans (congrArg f hp.1),?_⟩
    rw [ht e List.mem_cons_self]
    exact ih hp.2 (fun a ha => hs a (List.mem_cons_of_mem e ha))
      (fun a ha => ht a (List.mem_cons_of_mem e ha))

theorem path_rotate {x y : W} {p : List (Edge cs)} (i : I)
    (hp : IsPath (source cs) (target cs) x y p)
    (hn : ∀ e ∈ p, rootLabel cs e ≠ simplePositive i) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y) (p.map (rotateEdge cs i)) := by
  apply path_map_of_mem (source cs) (target cs) (source cs) (target cs)
    hp (fun z => cs.simple i*z) (rotateEdge cs i)
  · intro e he
    exact congrArg Prod.fst (rotateEdge_val cs i e (hn e he))
  · intro e he
    exact congrArg Prod.snd (rotateEdge_val cs i e (hn e he))


@[simp] theorem rotateEdge_twice (i : I) (e : Edge cs) :
    rotateEdge cs i (rotateEdge cs i e) = e := rotateEdge_involutive cs i e

variable {cs}

@[simp] theorem nonsimple_map (i : I) {p : List (Edge cs)} (hn : Nonsimple i p) :
    Nonsimple i (p.map (rotateEdge cs i)) := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact rotateEdge_nonsimple cs i f (hn f hf)

@[simp] theorem path_map_twice (i : I) (p : List (Edge cs)) :
    (p.map (rotateEdge cs i)).map (rotateEdge cs i) = p := by
  simp only [List.map_map,Function.comp_def,rotateEdge_twice]
  exact List.map_id p

theorem path_rotate_iff (i : I) {x y : W} {p : List (Edge cs)} (hn : Nonsimple i p) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y)
      (p.map (rotateEdge cs i)) ↔ IsPath (source cs) (target cs) x y p := by
  constructor
  · intro hp
    simpa only [cs.simple_mul_simple_cancel_left,path_map_twice] using
      path_rotate cs i hp (nonsimple_map i hn)
  · intro hp
    exact path_rotate cs i hp hn

theorem paths_rotate_iff (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    {x y : W} {p : List (Edge cs)} (hn : Nonsimple i p) :
    p.map (rotateEdge cs i) ∈ paths O' (cs.simple i*x) (cs.simple i*y) ↔ p ∈ paths O x y := by
  rw [mem_paths,mem_paths,path_rotate_iff i hn,List.pairwise_map]
  apply and_congr_right
  intro _
  apply List.Pairwise.iff_of_mem
  intro e f he hf
  simpa only [score,rotateEdge_root cs i e (hn e he),rotateEdge_root cs i f (hn f hf)] using
    hcmp (rootLabel cs e) (rootLabel cs f) (hn e he) (hn f hf)

theorem nonsimple_of_greatest (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope a < O.slope (simplePositive i))
    {x y : W} (hy : ¬cs.length (cs.simple i*y) < cs.length y)
    {p : List (Edge cs)} (hp : p ∈ paths O x y) : Nonsimple i p := by
  rw [mem_paths] at hp
  rcases hp with ⟨hp,ho⟩
  induction p generalizing x with
  | nil => simp [Nonsimple]
  | cons e p ih =>
    have he : rootLabel cs e ≠ simplePositive i := by
      intro he
      cases p with
      | nil =>
        have hy' : target cs e = y := hp.2
        have hr := (rootLabel_simple_iff cs i e).mp he
        have hx' : source cs e = cs.simple i*y := by
          rw [← hy',hr,cs.simple_mul_simple_cancel_left]
        have hl := e.property.1
        change cs.length (source cs e) < cs.length (target cs e) at hl
        rw [hy',hx'] at hl
        exact hy hl
      | cons f p =>
        have hlt := (List.pairwise_cons.mp ho).1 f List.mem_cons_self
        have hle : score O f ≤ O.slope (simplePositive i) := by
          by_cases hf : rootLabel cs f = simplePositive i
          · exact le_of_eq (congrArg O.slope hf)
          · exact (hmax _ hf).le
        have hes : score O e = O.slope (simplePositive i) := congrArg O.slope he
        exact (not_lt_of_ge hle) (hes ▸ hlt)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact ih hp.2 ho.tail f hf

theorem nonsimple_tail_of_least (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {e : Edge cs} {p : List (Edge cs)}
    (ho : (e::p).Pairwise (fun e f => score O e < score O f)) : Nonsimple i p := by
  intro f hf heq
  have hef := (List.pairwise_cons.mp ho).1 f hf
  have he : O.slope (simplePositive i) ≤ score O e := by
    by_cases he : rootLabel cs e = simplePositive i
    · exact le_of_eq (congrArg O.slope he).symm
    · exact (hmin _ he).le
  have hf' : score O f = O.slope (simplePositive i) := congrArg O.slope heq
  exact (not_lt_of_ge he) (hf' ▸ hef)

theorem nonsimple_of_least_descent (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length (cs.simple i*x) < cs.length x)
    {p : List (Edge cs)} (hp : p ∈ paths O x y) : Nonsimple i p := by
  obtain ⟨hp,ho⟩ := (mem_paths O x y p).mp hp
  cases p with
  | nil => simp [Nonsimple]
  | cons e p =>
    have he : rootLabel cs e ≠ simplePositive i := by
      intro he
      have hr := (rootLabel_simple_iff cs i e).mp he
      have hl := e.property.1
      change cs.length (source cs e) < cs.length (target cs e) at hl
      rw [hr,hp.1] at hl
      exact (lt_asymm hx hl)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact nonsimple_tail_of_least O i hmin ho f hf

@[simp] theorem mem_nonsimplePaths (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (x y : W) (p : List (Edge cs)) :
    p ∈ nonsimplePaths O i x y ↔ p ∈ paths O x y ∧ Nonsimple i p := by
  simp [nonsimplePaths]

theorem sum_nonsimple_rotate (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O'.slope a < O'.slope (simplePositive i))
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    (x y : W) (hy : cs.length (cs.simple i*y) < cs.length y) :
    ∑ p ∈ nonsimplePaths O i x y, (Polynomial.X : Polynomial ℤ)^p.length =
      polynomial O' (cs.simple i*x) (cs.simple i*y) := by
  unfold polynomial
  have hasc : ¬cs.length (cs.simple i*(cs.simple i*y)) < cs.length (cs.simple i*y) := by
    rw [cs.simple_mul_simple_cancel_left]
    omega
  apply Finset.sum_bij (fun p _ => p.map (rotateEdge cs i))
  · intro p hp
    obtain ⟨hp,hn⟩ := (mem_nonsimplePaths O i x y p).mp hp
    exact (paths_rotate_iff O O' i hcmp hn).mpr hp
  · intro p hp q hq he
    have := congrArg (List.map (rotateEdge cs i)) he
    simpa only [path_map_twice] using this
  · intro q hq
    have hn := nonsimple_of_greatest O' i hmax hasc hq
    refine ⟨q.map (rotateEdge cs i),?_,path_map_twice i q⟩
    have hn' := nonsimple_map i hn
    apply (mem_nonsimplePaths O i x y _).mpr
    refine ⟨?_,hn'⟩
    apply (paths_rotate_iff O O' i hcmp hn').mp
    simpa only [path_map_twice] using hq
  · intro p hp
    simp only [List.length_map]


variable (cs)

@[simp] theorem simpleEdge_root (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    rootLabel cs (simpleEdge cs i x hx) = simplePositive i :=
  (rootLabel_simple_iff cs i _).mpr rfl

variable {cs}
theorem cons_simple_mem (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x))
    {p : List (Edge cs)} (hp : p ∈ nonsimplePaths O i (cs.simple i*x) y) :
    simpleEdge cs i x hx :: p ∈ paths O x y := by
  obtain ⟨hp,hn⟩ := (mem_nonsimplePaths O i _ _ _).mp hp
  obtain ⟨hp,ho⟩ := (mem_paths O _ _ _).mp hp
  apply (mem_paths O _ _ _).mpr
  refine ⟨⟨rfl,hp⟩,List.pairwise_cons.mpr ⟨?_,ho⟩⟩
  intro e he
  change O.slope (rootLabel cs (simpleEdge cs i x hx)) < O.slope (rootLabel cs e)
  rw [simpleEdge_root]
  exact hmin _ (hn e he)

theorem not_nonsimple_iff_cons (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x)) (p : List (Edge cs)) :
    p ∈ (paths O x y).filter (fun p => ¬Nonsimple i p) ↔
      ∃ q ∈ nonsimplePaths O i (cs.simple i*x) y, p = simpleEdge cs i x hx :: q := by
  constructor
  · intro hp
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,ho⟩ := (mem_paths O _ _ _).mp hp
    cases p with
    | nil => exact (hn (by simp [Nonsimple])).elim
    | cons e p =>
      have hnp : Nonsimple i p := nonsimple_tail_of_least O i hmin ho
      have he : rootLabel cs e = simplePositive i := by
        by_contra he
        apply hn
        intro f hf
        rcases List.mem_cons.mp hf with rfl|hf
        · exact he
        · exact hnp f hf
      have heq : e = simpleEdge cs i x hx := by
        apply Subtype.ext
        apply Prod.ext
        · exact hp.1
        · change target cs e = cs.simple i*x
          rw [(rootLabel_simple_iff cs i e).mp he,hp.1]
      subst e
      refine ⟨p,(mem_nonsimplePaths O i _ _ _).mpr ⟨?_,hnp⟩,rfl⟩
      exact (mem_paths O _ _ _).mpr ⟨hp.2,ho.tail⟩
  · rintro ⟨q,hq,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨cons_simple_mem O i hmin hx hq,?_⟩
    intro hn
    exact hn _ List.mem_cons_self (simpleEdge_root cs i x hx)

theorem polynomial_split (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x)) :
    polynomial O x y =
      (∑ p ∈ nonsimplePaths O i x y, (Polynomial.X : Polynomial ℤ)^p.length) +
      Polynomial.X * (∑ p ∈ nonsimplePaths O i (cs.simple i*x) y,
        (Polynomial.X : Polynomial ℤ)^p.length) := by
  unfold polynomial
  rw [← Finset.sum_filter_add_sum_filter_not (paths O x y) (Nonsimple i)]
  congr 1
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun p _ => simpleEdge cs i x hx :: p)
  · intro p hp
    exact (not_nonsimple_iff_cons O i hmin hx _).mpr ⟨p,hp,rfl⟩
  · intro p hp q hq he
    exact List.cons.inj he |>.2
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := (not_nonsimple_iff_cons O i hmin hx q).mp hq
    exact ⟨p,hp,rfl⟩
  · intro p hp
    simp only [List.length_cons,pow_succ']

/-- The path expansion satisfies exactly the genuine normalized Hecke
recursion, because the chosen geometric order can be rotated at a descent. -/
theorem polynomial_recursion (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O'.slope a < O'.slope (simplePositive i))
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    (x y : W) (hy : cs.length (cs.simple i*y) < cs.length y) :
    polynomial O x y = if cs.length (cs.simple i*x) < cs.length x then
      polynomial O' (cs.simple i*x) (cs.simple i*y) else
      polynomial O' (cs.simple i*x) (cs.simple i*y) +
        Polynomial.X * polynomial O' x (cs.simple i*y) := by
  split_ifs with hx
  · have heq : nonsimplePaths O i x y = paths O x y := by
      ext p
      rw [mem_nonsimplePaths]
      exact and_iff_left_of_imp (nonsimple_of_least_descent O i hmin hx)
    rw [← sum_nonsimple_rotate O O' i hmax hcmp x y hy,heq]
    rfl
  · have ha : cs.length x < cs.length (cs.simple i*x) := by
      have := cs.length_simple_mul x i
      omega
    rw [polynomial_split O i hmin ha,
      sum_nonsimple_rotate O O' i hmax hcmp x y hy,
      sum_nonsimple_rotate O O' i hmax hcmp (cs.simple i*x) y hy,
      cs.simple_mul_simple_cancel_left]


@[simp] theorem paths_diagonal (O : RatioOrder (M := M) (cs := cs)) (x : W) :
    paths O x x = {[]} := by
  ext p
  rw [mem_paths,Finset.mem_singleton]
  cases p with
  | nil => simp [IsPath]
  | cons e p =>
    constructor
    · rintro ⟨hp,_⟩
      have hl := length_le_of_bruhat cs (path_le cs hp.2)
      have he := e.property.1
      change cs.length (source cs e) < cs.length (target cs e) at he
      rw [hp.1] at he
      omega
    · simp

@[simp] theorem polynomial_diagonal (O : RatioOrder (M := M) (cs := cs)) (x : W) :
    polynomial O x x = 1 := by
  simp [polynomial]

theorem polynomial_zero (O : RatioOrder (M := M) (cs := cs)) (x y : W)
    (h : ¬BruhatLE cs x y) : polynomial O x y = 0 := by
  have hp : paths O x y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact h (path_le cs ((mem_paths O x y p).mp hp).1)
  simp [polynomial,hp]

/-- Dyer's increasing-path formula for a genuine generic geometric order
whose numerator is in the top chamber. The target is the Hecke-defined
normalized R-polynomial, not a renamed path polynomial. -/
theorem polynomial_eq_rTilde (O : RatioOrder (M := M) (cs := cs)) (x y : W)
    (hc : O.Chamber y) : polynomial O x y = Hecke.rTilde cs x y := by
  generalize hn : cs.length y = n
  induction n using Nat.strong_induction_on generalizing O x y with
  | h n ih =>
    by_cases hy : y=1
    · subst y
      by_cases hx : x=1
      · subst x
        rw [polynomial_diagonal,Hecke.rTilde_diagonal]
      · have hxy : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          rw [cs.length_one] at hl
          exact hx (cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl))
        rw [polynomial_zero O x 1 hxy,Hecke.rTilde_zero cs x 1 hxy]
    · obtain ⟨i,O',hi,hc',hends,hcmp⟩ := O.exists_rotation hy hc
      have hi' : cs.length (cs.simple i*y) < n := hn ▸ hi
      have hsx := ih _ hi' O' (cs.simple i*x) (cs.simple i*y) hc' rfl
      have hx := ih _ hi' O' x (cs.simple i*y) hc' rfl
      rw [polynomial_recursion O O' i (fun a ha => (hends a ha).1)
        (fun a ha => (hends a ha).2) hcmp x y hi,
        Hecke.rTilde_recursion cs x y i hi,hsx,hx]

end
end KLInvariance.AdaptedDyer

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionOrders
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite sweep algebra, wall orders and the full reflection-order path formula.
-/

section

namespace KLInvariance.SchedulePaths
open scoped BigOperators
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
variable (source target : E → V) [Semiring R]

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_3
theorem dispatch_append (T : R) (v : V → R) (p q : List E) :
    dispatch source target T v (p ++ q) =
      dispatch source target T (dispatch source target T v q) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append,dispatch,ih]

theorem dispatch_add (T : R) (v w : V → R) (p : List E) :
    dispatch source target T (v+w) p =
      dispatch source target T v p + dispatch source target T w p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp only [step,Pi.add_apply]
    split_ifs <;> simp [mul_add,add_assoc,add_left_comm,add_comm]

theorem dispatch_mul_right (T c : R) (v : V → R) (p : List E) :
    dispatch source target T (fun x => v x*c) p =
      fun x => dispatch source target T v p x*c := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp only [step]
    split_ifs <;> simp [add_mul,mul_assoc]

theorem dispatch_zero (T : R) (p : List E) : dispatch source target T (0 : V → R) p = 0 := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp [step]

theorem dispatch_sum {A : Type*} (T : R) (F : Finset A) (v : A → V → R) (p : List E) :
    dispatch source target T (∑ a ∈ F, v a) p =
      ∑ a ∈ F, dispatch source target T (v a) p := by
  induction F using Finset.induction_on with
  | empty => simp [dispatch_zero]
  | @insert a F ha ih => simp only [Finset.sum_insert ha,dispatch_add,ih]

theorem dispatch_eq_sum_entries [Fintype V] (T : R) (v : V → R) (p : List E) (x : V) :
    dispatch source target T v p x =
      ∑ y, dispatch source target T (fun z => if z=y then 1 else 0) p x * v y := by
  have hv : v = ∑ y, (fun z => (if z=y then 1 else 0)*v y) := by
    funext z
    simp [Finset.sum_apply]
  conv_lhs => rw [hv]
  rw [dispatch_sum]
  simp only [Finset.sum_apply,dispatch_mul_right]

/-- A finite lower region is closed under every target occurring in its
edge schedule, so values outside that region never enter its product. -/
theorem dispatch_congr_on (T : R) (S : Set V) (p : List E)
    (htarget : ∀ e ∈ p, target e ∈ S) (v w : V → R)
    (hvw : ∀ x ∈ S, v x=w x) :
    ∀ x ∈ S, dispatch source target T v p x = dispatch source target T w p x := by
  induction p with
  | nil => exact hvw
  | cons e p ih =>
    have htail := ih (fun f hf => htarget f (List.mem_cons_of_mem _ hf))
    intro x hx
    simp only [dispatch,step,htail x hx,htail (target e) (htarget e List.mem_cons_self)]

theorem dispatch_eq_finite_entries (T : R) (F : Finset V) (p : List E)
    (htarget : ∀ e ∈ p, target e ∈ F) (v : V → R) (x : V) (hx : x ∈ F) :
    dispatch source target T v p x =
      ∑ y ∈ F, dispatch source target T (fun z => if z=y then 1 else 0) p x * v y := by
  let w : V → R := ∑ y ∈ F, (fun z => (if z=y then 1 else 0)*v y)
  have hvw : ∀ z ∈ (F : Set V), v z=w z := by
    intro z hz
    simp [w,Finset.sum_apply,show z ∈ F from hz]
  rw [dispatch_congr_on source target T (F : Set V) p htarget v w hvw x hx]
  dsimp only [w]
  rw [dispatch_sum]
  simp only [Finset.sum_apply,dispatch_mul_right]

theorem dispatch_eq_of_entries_on (T : R) (F : Finset V) (p q : List E)
    (hp : ∀ e ∈ p, target e ∈ F) (hq : ∀ e ∈ q, target e ∈ F)
    (h : ∀ x ∈ F, ∀ y ∈ F,
      dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x)
    (v : V → R) (x : V) (hx : x ∈ F) :
    dispatch source target T v p x = dispatch source target T v q x := by
  rw [dispatch_eq_finite_entries source target T F p hp v x hx,
    dispatch_eq_finite_entries source target T F q hq v x hx]
  exact Finset.sum_congr rfl (fun y hy => congrArg (fun a => a*v y) (h x hx y hy))

variable {Λ : Type*} [LinearOrder Λ]

/-- A genuine path in a sorted schedule is determined by its edge set and
strict label order. Arbitrary permutations of repeated reflection labels
therefore have no effect. -/
theorem subpaths_eq_of_sorted (label : E → Λ)
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (p q : List E)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (x y : V) :
    subpaths source target p x y = subpaths source target q x y := by
  ext s
  simp only [mem_subpaths]
  constructor
  · rintro ⟨hs,hpath⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset label
      (decreasing_of_schedule_path source target label hties hpath (hp.sublist hs)) hq
    exact fun e he => (hmem e).mp (hs.subset he)
  · rintro ⟨hs,hpath⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset label
      (decreasing_of_schedule_path source target label hties hpath (hq.sublist hs)) hp
    exact fun e he => (hmem e).mpr (hs.subset he)


variable {V' E' : Type*} (source' target' : E' → V')

theorem IsPath.map_iff (j : V' → V) (hj : Function.Injective j) (J : E' → E)
    (hs : ∀ e, source (J e)=j (source' e))
    (ht : ∀ e, target (J e)=j (target' e)) {x y : V'} {p : List E'} :
    IsPath source target (j x) (j y) (p.map J) ↔ IsPath source' target' x y p := by
  induction p generalizing x with
  | nil => exact hj.eq_iff
  | cons e p ih =>
    change (source (J e)=j x ∧ IsPath source target (target (J e)) (j y) (p.map J)) ↔ _
    rw [hs,ht,ih,hj.eq_iff]
    rfl

theorem exists_list_lift (J : E' → E) (p : List E)
    (h : ∀ e ∈ p, ∃ e', J e'=e) : ∃ p' : List E', p'.map J=p := by
  induction p with
  | nil => exact ⟨[],rfl⟩
  | cons e p ih =>
    obtain ⟨e',he⟩ := h e List.mem_cons_self
    obtain ⟨p',hp⟩ := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    exact ⟨e'::p',by simp [he,hp]⟩

/-- If all actual paths between the specified endpoints lie in a full embedded
subgraph, its full sorted product computes the same entry. -/
theorem dispatch_entry_graph_embedding (T : R) (label : E → Λ)
    (hties : ∀ e f, label e=label f → target e ≠ source f)
    (j : V' → V) (hj : Function.Injective j) (J : E' → E) (hJ : Function.Injective J)
    (hs : ∀ e, source (J e)=j (source' e))
    (ht : ∀ e, target (J e)=j (target' e))
    (p : List E) (q : List E') (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label (J f) ≤ label (J e)))
    (hqfull : ∀ e, e ∈ q) (hJmem : ∀ e, J e ∈ p)
    (x y : V')
    (hpath : ∀ r ∈ subpaths source target p (j x) (j y), ∀ e ∈ r, ∃ e', J e'=e) :
    dispatch source target T (fun z => if z=j y then 1 else 0) p (j x) =
      dispatch source' target' T (fun z => if z=y then 1 else 0) q x := by
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source' target' T q hqnd]
  symm
  have hties' : ∀ e f, label (J e)=label (J f) → target' e ≠ source' f := by
    intro e f he hf
    apply hties (J e) (J f) he
    rw [ht,hs,hf]
  apply Finset.sum_bij (fun r _ => r.map J)
  · intro r hr
    obtain ⟨hr,hpr⟩ := (mem_subpaths source' target' q x y r).mp hr
    apply (mem_subpaths source target p (j x) (j y) (r.map J)).mpr
    constructor
    · apply sublist_of_decreasing_subset label
      · rw [List.pairwise_map]
        exact decreasing_of_schedule_path source' target' (label ∘ J) hties' hpr (hq.sublist hr)
      · exact hp
      · intro e he
        obtain ⟨f,_,rfl⟩ := List.mem_map.mp he
        exact hJmem f
    · exact hpr.map source' target' source target j J hs ht
  · intro r _ s _ he
    exact List.map_injective_iff.mpr hJ he
  · intro r hr
    obtain ⟨s,he⟩ := exists_list_lift J r (hpath r hr)
    refine ⟨s,?_,he⟩
    obtain ⟨hrsub,hrpath⟩ := (mem_subpaths source target p (j x) (j y) r).mp hr
    have hspath : IsPath source' target' x y s :=
      (IsPath.map_iff source target source' target' j hj J hs ht).mp (he ▸ hrpath)
    apply (mem_subpaths source' target' q x y s).mpr
    refine ⟨?_,hspath⟩
    apply sublist_of_decreasing_subset (label ∘ J)
    · have hstrict := decreasing_of_schedule_path source target label hties hrpath (hp.sublist hrsub)
      rw [← he,List.pairwise_map] at hstrict
      exact hstrict
    · exact hq
    · exact fun e _ => hqfull e
  · intro r _
    simp

end
end KLInvariance.SchedulePaths

end


section

/-! Linear coordinates on the actual normalized root line. These give the
rank-two geometry of finite wall crossings for genuine root schedules. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_9_ra2d10a_1 (p : Prop) : Decidable p := Classical.propDecidable p
theorem normalizedRoot_mem_iff (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    normalizedRoot a ∈ P ↔ a.val ∈ P := by
  constructor
  · intro h
    have hh := P.smul_mem (height a.val) h
    simpa [normalizedRoot,smul_smul,a.height_pos.ne'] using hh
  · exact fun h => P.smul_mem _ h

theorem rootPlane_eq_normalized_span (a b : PositiveRoot M cs) :
    rootPlane a b = Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mp (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mp (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mpr (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mpr (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The intersection of a root-plane with the height-one hyperplane is the
actual affine line through the two normalized roots. -/
theorem normalizedRoot_affine {a b c : PositiveRoot M cs}
    (hc : c.val ∈ rootPlane a b) :
    ∃ t : ℝ, normalizedRoot c = t • normalizedRoot a + (1-t) • normalizedRoot b := by
  have hcn : normalizedRoot c ∈ Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
    rw [← rootPlane_eq_normalized_span]
    exact (normalizedRoot_mem_iff _ _).mpr hc
  obtain ⟨t,s,he⟩ := Submodule.mem_span_pair.mp hcn
  have hh := congrArg (height (I := I)) he
  simp only [map_add,map_smul,normalizedRoot_height,smul_eq_mul,mul_one] at hh
  refine ⟨t,?_⟩
  have hs : s=1-t := by linarith
  exact hs ▸ he.symm

/-- On each genuine root plane, every height-normalized linear functional
is an affine function of the fixed angular slope. -/
theorem exists_affine_rootPlane (f : Module.Dual ℝ (I → ℝ))
    (a b : PositiveRoot M cs) (hab : a ≠ b) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  let A := geometricSlope a
  let B := geometricSlope b
  let fa := f (normalizedRoot a)
  let fb := f (normalizedRoot b)
  have hAB : A-B ≠ 0 := sub_ne_zero.mpr (fun h => hab (geometricSlope_injective h))
  let c := (fa-fb)/(A-B)
  let d := fb-c*B
  have ha : fa=c*A+d := by
    dsimp [d,c]
    field_simp
    ring
  have hb : fb=c*B+d := by dsimp [d]; ring
  refine ⟨c,d,fun r hr => ?_⟩
  obtain ⟨t,ht⟩ := normalizedRoot_affine hr
  have hf : f (normalizedRoot r) = t*fa+(1-t)*fb := by
    rw [ht]
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hg : geometricSlope r = t*A+(1-t)*B := by
    rw [← geometricFunctional_normalizedRoot,ht]
    simp only [map_add,map_smul,geometricFunctional_normalizedRoot,smul_eq_mul]
    rfl
  rw [hf,hg,ha,hb]
  ring

namespace PlaneBasis
local instance instDecidable_solutions_9_ra2d10a_2 (p : Prop) : Decidable p := Classical.propDecidable p
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
theorem exists_affine (f : Module.Dual ℝ (I → ℝ)) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ P →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  simpa only [B.plane_eq] using exists_affine_rootPlane f B.left B.right B.distinct

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Localization of genuine directed paths in a maximal root-plane coset.
The full relative interval is proved to contain every such path. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module SchedulePaths
open AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_2
/-- All edges of a plane-labelled path lie in the full induced relative
interval between its endpoints, with the original ambient labels. -/
theorem path_coordinates {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (g : planeSubgroup M cs P) {y : W} {p : List (AdaptedDyer.Edge cs)}
    (hp : IsPath (source cs) (target cs) ((g:W)*a₀) y p)
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P) :
    ∃ k : planeSubgroup M cs P, y=(k:W)*a₀ ∧ BruhatLE B.system g k ∧
      ∀ e ∈ p, ∃ l r : planeSubgroup M cs P,
        source cs e=(l:W)*a₀ ∧ target cs e=(r:W)*a₀ ∧
        BruhatLE B.system g l ∧ BruhatStep B.system l r ∧ BruhatLE B.system r k := by
  induction p generalizing g with
  | nil => exact ⟨g,hp.symm,.refl,by simp⟩
  | cons e p ih =>
    have hg : source cs e*a₀⁻¹ ∈ planeSubgroup M cs P := by
      rw [hp.1]
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using g.property
    have hh := mem_coset_of_graphRoot e.property hg (hP e List.mem_cons_self)
    let h : planeSubgroup M cs P := ⟨target cs e*a₀⁻¹,hh⟩
    have heqh : target cs e=(h:W)*a₀ := by dsimp [h]; group
    have he : BruhatStep B.system g h := by
      apply (B.coset_step_iff hmin g h).mp
      rw [← hp.1,← heqh]
      exact e.property
    obtain ⟨k,hky,hk,hbody⟩ := ih h (heqh ▸ hp.2)
      (fun f hf => hP f (List.mem_cons_of_mem _ hf))
    refine ⟨k,hky,(show BruhatLE B.system g h from .single he).trans hk,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨g,h,hp.1,heqh,.refl,he,hk⟩
    · obtain ⟨l,r,hl,hr,hhl,hlr,hrk⟩ := hbody f hf
      exact ⟨l,r,hl,hr,(show BruhatLE B.system g h from .single he).trans hhl,hlr,hrk⟩

theorem intervalToAmbient_injective {a₀ : W} {g k : planeSubgroup M cs P} :
    Function.Injective (B.intervalToAmbient (a₀ := a₀) (g := g) (k := k)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (mul_right_cancel h))

theorem edgeToAmbient_injective {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} :
    Function.Injective (B.edgeToAmbient hmin (g := g) (k := k)) := by
  intro e f h
  have hh := congrArg Subtype.val h
  apply Subtype.ext
  exact Prod.ext (B.intervalToAmbient_injective (congrArg Prod.fst hh))
    (B.intervalToAmbient_injective (congrArg Prod.snd hh))

/-- Edge-by-edge lifting of every plane path into the full relative interval.
It is obtained from actual path connectivity, not from ambient comparability
alone (which would not suffice). -/
theorem path_edges_lift {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} {p : List (AdaptedDyer.Edge cs)}
    (hp : IsPath (source cs) (target cs) ((g:W)*a₀) ((k:W)*a₀) p)
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P) :
    ∀ e ∈ p, ∃ e' : BruhatGraph.Edge B.system g k, B.edgeToAmbient hmin e'=e := by
  obtain ⟨k',he,_,hbody⟩ := B.path_coordinates hmin g hp hP
  have hk : k'=k := Subtype.ext (mul_right_cancel he.symm)
  subst k'
  intro e he
  obtain ⟨l,r,hl,hr,hgl,hlr,hrk⟩ := hbody e he
  let vl : Interval B.system g k := ⟨l,hgl,(show BruhatLE B.system l r from .single hlr).trans hrk⟩
  let vr : Interval B.system g k := ⟨r,hgl.trans (.single hlr),hrk⟩
  refine ⟨⟨(vl,vr),hlr⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext hl.symm hr.symm


include B in
/-- Reversal of a complete angular block of genuine ambient edges preserves
all its endpoint entries. Fullness is with respect to the actual root plane,
not to a rank-two subgroup chosen merely to contain two arbitrary reflections. -/
theorem dispatch_plane_reverse {R : Type*} [Semiring R] (T : R) (b : W)
    (p : List (AdaptedDyer.Edge cs)) (hnd : p.Nodup)
    (hfull : ∀ e, e ∈ p ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hs : p.Pairwise (fun e f => geometricSlope (rootLabel cs f) ≤ geometricSlope (rootLabel cs e)))
    (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p x =
      dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p.reverse x := by
  obtain ⟨a₀,g,hg,hx,hmin⟩ := planeCoset_exists_minimal M cs P x
  let g' : planeSubgroup M cs P := ⟨g,hg⟩
  have hx' : x=(g':W)*a₀ := hx
  let L : AdaptedDyer.Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
  have hties : ∀ e f, L e=L f → target cs e ≠ source cs f := by
    intro e f he
    exact fun hj => rootLabel_ne_of_join cs e f hj (geometricSlope_injective he)
  by_cases hex : ∃ r : List (AdaptedDyer.Edge cs),
      IsPath (source cs) (target cs) x y r ∧ ∀ e ∈ r, (rootLabel cs e).val ∈ P
  · obtain ⟨r,hr,hrP⟩ := hex
    obtain ⟨k,hyk,hgk,_⟩ := B.path_coordinates hmin g' (hx' ▸ hr) hrP
    let lo : Interval B.system g' k := ⟨g',.refl,hgk⟩
    let hi : Interval B.system g' k := ⟨k,hgk,.refl⟩
    let j := B.intervalToAmbient (a₀ := a₀) (g := g') (k := k)
    let J := B.edgeToAmbient hmin (g := g') (k := k)
    have hjlo : j lo=x := hx'.symm
    have hjhi : j hi=y := hyk.symm
    let : Fintype (BruhatGraph.Edge B.system g' k) := Fintype.ofFinite _
    let q : List (BruhatGraph.Edge B.system g' k) :=
      Finset.univ.toList.mergeSort (fun e f => B.intervalEdgeSlope g' k f ≤ B.intervalEdgeSlope g' k e)
    have hqnd : q.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
    have hqfull : ∀ e, e ∈ q := by intro e; simp [q]
    have hqs : q.Pairwise (fun e f => B.intervalEdgeSlope g' k f ≤ B.intervalEdgeSlope g' k e) :=
      List.pairwise_mergeSort' _ _
    have hJroot (e : BruhatGraph.Edge B.system g' k) : L (J e)=B.intervalEdgeSlope g' k e := by
      dsimp [L,J,intervalEdgeSlope]
      rw [B.edgeToAmbient_root]
    have hJmem (e : BruhatGraph.Edge B.system g' k) : J e ∈ p := by
      apply (hfull _).mpr
      constructor
      · dsimp [J]
        rw [B.edgeToAmbient_root]
        exact B.edgeRoot_plane e.property
      · have ht : BruhatLE cs ((e.val.2.val:W)*a₀) ((k:W)*a₀) :=
          B.coset_bruhat hmin e.val.2.property.2
        exact ht.trans (hyk ▸ hy)
    have hlift (s : List (AdaptedDyer.Edge cs))
        (hst : ∀ e ∈ s, e ∈ p)
        (hp : IsPath (source cs) (target cs) (j lo) (j hi) s) :
        ∀ e ∈ s, ∃ e' : BruhatGraph.Edge B.system g' k, J e'=e :=
      B.path_edges_lift hmin hp (fun e he => ((hfull e).mp (hst e he)).1)
    have hleft := dispatch_entry_graph_embedding (source cs) (target cs)
      (BruhatGraph.source B.system g' k) (BruhatGraph.target B.system g' k)
      T L hties j (B.intervalToAmbient_injective) J (B.edgeToAmbient_injective hmin)
      (B.edgeToAmbient_source hmin) (B.edgeToAmbient_target hmin)
      p q hnd hqnd hs (by simpa only [hJroot] using hqs) hqfull hJmem lo hi (by
        intro s hsp
        obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hsp
        exact hlift s (fun e he => hsub.subset he) hpath)
    have hright := dispatch_entry_graph_embedding (source cs) (target cs)
      (BruhatGraph.source B.system g' k) (BruhatGraph.target B.system g' k)
      T (fun e => -L e) (fun e f he => hties e f (neg_injective he))
      j (B.intervalToAmbient_injective) J (B.edgeToAmbient_injective hmin)
      (B.edgeToAmbient_source hmin) (B.edgeToAmbient_target hmin)
      p.reverse q.reverse (List.nodup_reverse.mpr hnd) (List.nodup_reverse.mpr hqnd)
      (by rw [List.pairwise_reverse]; exact hs.imp (fun he => neg_le_neg he))
      (by rw [List.pairwise_reverse]; exact hqs.imp (fun he => by simpa only [hJroot] using neg_le_neg he))
      (fun e => List.mem_reverse.mpr (hqfull e))
      (fun e => List.mem_reverse.mpr (hJmem e)) lo hi (by
        intro s hsp
        obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hsp
        exact hlift s (fun e he => List.mem_reverse.mp (hsub.subset he)) hpath)
    rw [hjlo,hjhi] at hleft hright
    rw [hleft,hright]
    exact B.dispatch_reverse_endpoints hgk q hqnd hqfull hqs T
  · have hzero (q : List (AdaptedDyer.Edge cs))
        (hqp : ∀ e ∈ q, e ∈ p) : subpaths (source cs) (target cs) q x y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hr
      exact hex ⟨r,hpath,fun e he => ((hfull e).mp (hqp e (hsub.subset he))).1⟩
    rw [dispatch_eq_subpaths_sum _ _ _ _ hnd,
      dispatch_eq_subpaths_sum _ _ _ _ (List.nodup_reverse.mpr hnd),
      hzero p (fun _ he => he),hzero p.reverse (fun _ he => List.mem_reverse.mp he)]

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Algebra and finite ordered-list bookkeeping for wall crossings. -/
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_4
attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidableEq_solutions
theorem sortedSchedule_nodup (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem sortedSchedule_pairwise (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Pairwise (fun e f => score f ≤ score e) :=
  List.pairwise_mergeSort' _ _

theorem blockValues_strict (F : Finset E) (primary : E → A) :
    (blockValues F primary).Pairwise (fun a b => b < a) := by
  have hs := Finset.pairwise_sort (F.image primary) (fun a b => b ≤ a)
  have hn := Finset.sort_nodup (F.image primary) (fun a b => b ≤ a)
  exact (List.pairwise_and_iff.mpr ⟨hs,hn⟩).imp (fun h => lt_of_le_of_ne h.1 h.2.symm)

theorem groupedSchedule_nodup (F : Finset E) (primary : E → A) (score : E → Λ) :
    (groupedSchedule F primary score).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    exact sortedSchedule_nodup _ _
  · apply (blockValues_strict F primary).imp
    intro a b hab
    apply List.disjoint_left.mpr
    intro e hea heb
    have ha := ((mem_scheduleBlock F primary score a e).mp hea).2
    have hb := ((mem_scheduleBlock F primary score b e).mp heb).2
    exact hab.ne (hb.symm.trans ha)

theorem groupedSchedule_pairwise (F : Finset E) (primary : E → A) (score : E → Λ)
    (h : ∀ e ∈ F, ∀ f ∈ F, primary f < primary e → score f ≤ score e) :
    (groupedSchedule F primary score).Pairwise (fun e f => score f ≤ score e) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    exact sortedSchedule_pairwise _ _
  · apply (blockValues_strict F primary).imp
    intro a b hab e he f hf
    obtain ⟨he,heq⟩ := (mem_scheduleBlock F primary score a e).mp he
    obtain ⟨hf,hfq⟩ := (mem_scheduleBlock F primary score b f).mp hf
    exact h e he f hf (by simpa only [heq,hfq] using hab)

variable {V : Type*} {R : Type*} [Semiring R] (source target : E → V)

theorem dispatch_entries_eq_of_sorted (T : R) (label : E → Λ)
    (hties : ∀ e f, label e=label f → target e ≠ source f)
    (p q : List E) (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (x y : V) :
    dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x := by
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source target T q hqnd,
    subpaths_eq_of_sorted source target label hties p q hp hq hmem x y]

omit [LinearOrder A] in
/-- Replacement on a finite lower region requires no artificial finiteness
assumption on the ambient Coxeter group. -/
theorem dispatch_flatMap_eq_on (T : R) (S : Set V) (blocks : List A) (p q : A → List E)
    (htarget : ∀ a ∈ blocks, ∀ e ∈ p a, target e ∈ S)
    (h : ∀ a ∈ blocks, ∀ v, ∀ x ∈ S,
      dispatch source target T v (p a) x = dispatch source target T v (q a) x)
    (v : V → R) : ∀ x ∈ S,
    dispatch source target T v (blocks.flatMap p) x =
      dispatch source target T v (blocks.flatMap q) x := by
  induction blocks with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro x hx
    simp only [List.flatMap_cons,dispatch_append]
    rw [dispatch_congr_on source target T S (p a) (htarget a List.mem_cons_self)
      _ _ (ih (fun b hb => htarget b (List.mem_cons_of_mem _ hb))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))) x hx]
    exact h a List.mem_cons_self _ x hx

end
end KLInvariance.SchedulePaths

end


section

/-! The actual rank-two edge product is independent of every linear
functional restricted to that root plane, including a wall tie refinement. -/
namespace KLInvariance.TitsSpace
open Module SchedulePaths AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_10
theorem lexRootScore_injective (f : Module.Dual ℝ (I → ℝ)) :
    Function.Injective (lexRootScore (M := M) (cs := cs) f) := by
  intro a b hab
  apply geometricSlope_injective
  exact congrArg (fun p : ℝ ×ₗ ℝ => (ofLex p).2) hab

theorem lexEdgeScore_ties (f : Module.Dual ℝ (I → ℝ)) (e e' : AdaptedDyer.Edge cs)
    (he : lexEdgeScore f e=lexEdgeScore f e') : target cs e ≠ source cs e' := by
  intro hj
  exact rootLabel_ne_of_join cs e e' hj (lexRootScore_injective f he)

omit [Fintype I] in
theorem lex_affine_nonneg {c d x y : ℝ} (hc : 0 ≤ c)
    (h : (toLex (c*x+d,x) : ℝ ×ₗ ℝ) ≤ toLex (c*y+d,y)) : x ≤ y := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · by_contra hn
    have hxy : y < x := lt_of_not_ge hn
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hxy.le)]
  · exact h.2

omit [Fintype I] in
theorem lex_affine_neg {c d x y : ℝ} (hc : c < 0)
    (h : (toLex (c*x+d,x) : ℝ ×ₗ ℝ) ≤ toLex (c*y+d,y)) : y ≤ x := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · by_contra hn
    have hxy : x < y := lt_of_not_ge hn
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.mpr hxy.le)]
  · have he : x=y := by nlinarith [h.1]
    exact he.symm.le

namespace PlaneBasis
attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_10
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
/-- Any linearly sorted full plane block is either angularly sorted or
reverse-angularly sorted. This includes tied primary labels refined by the
fixed genuine geometric functional. -/
theorem lex_block_orientation (f : Module.Dual ℝ (I → ℝ))
    (p : List (AdaptedDyer.Edge cs))
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P)
    (hs : p.Pairwise (fun e e' => lexEdgeScore f e' ≤ lexEdgeScore f e)) :
    p.Pairwise (fun e e' => geometricSlope (rootLabel cs e') ≤ geometricSlope (rootLabel cs e)) ∨
    p.Pairwise (fun e e' => geometricSlope (rootLabel cs e) ≤ geometricSlope (rootLabel cs e')) := by
  obtain ⟨c,d,hf⟩ := B.exists_affine f
  have hv (e : AdaptedDyer.Edge cs) (he : e ∈ p) :
      lexEdgeScore f e=toLex (c*geometricSlope (rootLabel cs e)+d,geometricSlope (rootLabel cs e)) := by
    unfold lexEdgeScore lexRootScore
    rw [hf _ (hP e he)]
  by_cases hc : 0 ≤ c
  · left
    apply hs.imp_of_mem
    intro e e' he he' hee'
    rw [hv e he,hv e' he'] at hee'
    exact lex_affine_nonneg hc hee'
  · right
    apply hs.imp_of_mem
    intro e e' he he' hee'
    rw [hv e he,hv e' he'] at hee'
    exact lex_affine_neg (lt_of_not_ge hc) hee'

include B in
/-- A complete plane block, sorted by any functional, has precisely the
same actual path product as its angularly sorted version. -/
theorem dispatch_plane_functional {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (p q : List (AdaptedDyer.Edge cs))
    (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hpfull : ∀ e, e ∈ p ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hqfull : ∀ e, e ∈ q ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hp : p.Pairwise (fun e e' => lexEdgeScore f e' ≤ lexEdgeScore f e))
    (hq : q.Pairwise (fun e e' => geometricSlope (rootLabel cs e') ≤ geometricSlope (rootLabel cs e)))
    (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p x =
      dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) q x := by
  let L : AdaptedDyer.Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
  have hties : ∀ e e', L e=L e' → target cs e ≠ source cs e' := by
    intro e e' he hj
    exact rootLabel_ne_of_join cs e e' hj (geometricSlope_injective he)
  rcases B.lex_block_orientation f p (fun e he => ((hpfull e).mp he).1) hp with hs|hs
  · exact dispatch_entries_eq_of_sorted (source cs) (target cs) T L hties
      p q hpnd hqnd hs hq (fun e => (hpfull e).trans (hqfull e).symm) x y
  · have hentry := dispatch_entries_eq_of_sorted (source cs) (target cs) T
      (fun e => -L e) (fun e e' he => hties e e' (neg_injective he))
      p q.reverse hpnd (List.nodup_reverse.mpr hqnd)
      (hs.imp (fun he => neg_le_neg he))
      (by rw [List.pairwise_reverse]; exact hq.imp (fun he => neg_le_neg he))
      (fun e => (hpfull e).trans ((hqfull e).symm.trans List.mem_reverse.symm)) x y
    exact hentry.trans (B.dispatch_plane_reverse T b q hqnd hqfull hq x y hy).symm

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Generic pencils of genuine linear root-label functionals. At a wall all
roots of a tied block belong to one full actual root plane. -/
namespace KLInvariance.ReflectionSchedules
open Polynomial
universe u v
variable {I : Type u} [Fintype I]
noncomputable section

/-- A countable family of nonzero vectors can be simultaneously avoided. -/
theorem exists_avoiding_functional {A : Type v} [Countable A] (v : A → (I → ℝ)) :
    ∃ f : Module.Dual ℝ (I → ℝ), ∀ a, v a ≠ 0 → f (v a) ≠ 0 := by
  classical
  let P := {a : A // v a ≠ 0}
  have hn (a : P) : coordinatePolynomial (v a.val) ≠ 0 := by
    intro h
    apply a.property
    apply coordinatePolynomial_injective
    simpa [coordinatePolynomial] using h
  let bad : Set ℝ := ⋃ a : P, {t | (coordinatePolynomial (v a.val)).IsRoot t}
  have hb : bad.Countable := Set.countable_iUnion
    (fun a => (Polynomial.finite_setOfPred_isRoot (hn a)).countable)
  obtain ⟨t,ht⟩ : ∃ t, t ∉ bad := by
    by_contra h
    push Not at h
    have he : bad=Set.univ := Set.eq_univ_of_forall h
    rw [he] at hb
    exact Set.not_countable_univ hb
  refine ⟨momentFunctional t,fun a ha he => ht ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨a,ha⟩,?_⟩
  simpa only [Set.mem_ofPred_eq,Polynomial.IsRoot,coordinatePolynomial_eval] using he

end
end KLInvariance.ReflectionSchedules

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_11
omit [Fintype I] in
theorem pencil_apply (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) (v : I → ℝ) :
    pencil f g t v=(1-t)*f v+t*g v := rfl

theorem pencil_tie_plane (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (t : ℝ)
    (a b : PositiveRoot M cs) (hab : a ≠ b)
    (he : pencil f g t (normalizedRoot a)=pencil f g t (normalizedRoot b)) :
    ∀ c : PositiveRoot M cs,
      pencil f g t (normalizedRoot c)=pencil f g t (normalizedRoot a) ↔
        c.val ∈ rootPlane a b := by
  let v := rootDifference a b
  have hv : f v ≠ 0 := by
    change f (normalizedRoot b-normalizedRoot a) ≠ 0
    rw [map_sub,sub_ne_zero]
    exact fun h => hab (hf h).symm
  have hvt : (1-t)*f v+t*g v=0 := by
    rw [← pencil_apply]
    change pencil f g t (normalizedRoot b-normalizedRoot a)=0
    rw [map_sub,he,sub_self]
  have ht : t ≠ 0 := by
    intro h
    subst t
    simp only [sub_zero,one_mul,zero_mul,add_zero] at hvt
    exact hv hvt
  intro c
  constructor
  · intro hc
    let w := rootDifference a c
    have hwt : (1-t)*f w+t*g w=0 := by
      rw [← pencil_apply]
      change pencil f g t (normalizedRoot c-normalizedRoot a)=0
      rw [map_sub,hc,sub_self]
    have hz : g (wallVector f a b c)=0 := by
      change g (f v • w-f w • v)=0
      rw [map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      apply (mul_eq_zero.mp (show t * (f v*g w-f w*g v)=0 by
        calc
          _ = f v*((1-t)*f w+t*g w)-f w*((1-t)*f v+t*g v) := by ring
          _ = 0 := by rw [hwt,hvt]; ring)).resolve_left ht
    have heq : f v • w=f w • v := sub_eq_zero.mp (hg a b c hz)
    let P := rootPlane a b
    have haP : normalizedRoot a ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert _ _))
    have hbP : normalizedRoot b ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hvP : v ∈ P := P.sub_mem hbP haP
    have hwP : w ∈ P := by
      have hh := P.smul_mem (f v)⁻¹ (heq ▸ P.smul_mem (f w) hvP)
      simpa only [smul_smul,inv_mul_cancel₀ hv,one_smul] using hh
    apply (normalizedRoot_mem_iff P c).mp
    have hh := P.add_mem hwP haP
    simpa only [w,rootDifference,sub_add_cancel] using hh
  · intro hc
    obtain ⟨s,hs⟩ := normalizedRoot_affine hc
    rw [hs,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,← he]
    ring

/-- One intermediate functional is simultaneously transverse to any two
specified generic endpoints, even with infinitely many positive roots. -/
theorem exists_common_transverse (f h : Module.Dual ℝ (I → ℝ)) :
    ∃ g : Module.Dual ℝ (I → ℝ),
      Function.Injective (fun a : PositiveRoot M cs => g (normalizedRoot a)) ∧
      Transverse (M := M) (cs := cs) f g ∧ Transverse (M := M) (cs := cs) h g := by
  let := countable_Positiveroot M cs
  let E := PositiveRoot M cs
  let A := (E × E) ⊕ (Bool × E × E × E)
  let v : A → (I → ℝ) := fun x => match x with
    | .inl (a,b) => rootDifference a b
    | .inr (i,a,b,c) => wallVector (if i then f else h) a b c
  obtain ⟨g,hg⟩ := ReflectionSchedules.exists_avoiding_functional v
  refine ⟨g,?_,?_,?_⟩
  · intro a b he
    by_contra hab
    have hn : rootDifference a b ≠ 0 := by
      exact fun hz => hab (normalizedRoot_injective (sub_eq_zero.mp hz)).symm
    apply hg (.inl (a,b)) hn
    simp only [v,rootDifference,map_sub,he,sub_self]
  · intro a b c he
    by_contra hz
    exact hg (.inr (true,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)
  · intro a b c he
    by_contra hz
    exact hg (.inr (false,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)

end
end KLInvariance.TitsSpace

end


section

/-! Finite wall crossing for actual reflection-edge path matrices. -/
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
open scoped Topology
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.WallDyer.instDecidable_solutions
/-- The complete tied block at any genuine simple wall has an actual
operator independent of the linear tie-breaking functional. -/
theorem block_entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (hf : rootPlaneTies (M := M) (cs := cs) f)
    (g h : Module.Dual ℝ (I → ℝ)) (a : ℝ) (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore g) a) x =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore h) a) x := by
  let F := (edgeFinset cs b).filter (fun e => rootValue f e=a)
  let p := sortedSchedule F (lexEdgeScore g)
  let q := sortedSchedule F (lexEdgeScore h)
  let r := sortedSchedule F (fun e => geometricSlope (rootLabel cs e))
  change dispatch (source cs) (target cs) T _ p x = dispatch (source cs) (target cs) T _ q x
  have hmem (k : Edge cs) : k ∈ F ↔ BruhatLE cs (target cs k) b ∧ rootValue f k=a := by
    simp only [F,Finset.mem_filter,mem_edgeFinset]
  by_cases hex : ∃ e ∈ F, ∃ e' ∈ F, rootLabel cs e ≠ rootLabel cs e'
  · obtain ⟨e,he,e',he',hne⟩ := hex
    obtain ⟨B⟩ := nonempty_planeBasis (rootLabel cs e) (rootLabel cs e') hne
    have hv := hf (rootLabel cs e) (rootLabel cs e') hne
      (((hmem e).mp he).2.trans ((hmem e').mp he').2.symm)
    have hfull (k : Edge cs) : k ∈ F ↔
        (rootLabel cs k).val ∈ rootPlane (rootLabel cs e) (rootLabel cs e') ∧
        BruhatLE cs (target cs k) b := by
      rw [hmem,← hv,show f (normalizedRoot (rootLabel cs e))=a from ((hmem e).mp he).2]
      exact and_comm
    have hp := B.dispatch_plane_functional T b g p r
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _)
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (sortedSchedule_pairwise _ _) (sortedSchedule_pairwise _ _) x y hy
    have hq := B.dispatch_plane_functional T b h q r
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _)
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (sortedSchedule_pairwise _ _) (sortedSchedule_pairwise _ _) x y hy
    exact hp.trans hq.symm
  · have heq (e : Edge cs) (he : e ∈ F) (e' : Edge cs) (he' : e' ∈ F) :
        rootLabel cs e=rootLabel cs e' := by
      by_contra hn
      exact hex ⟨e,he,e',he',hn⟩
    let L : Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
    have hties : ∀ e e', L e=L e' → target cs e ≠ source cs e' := by
      intro e e' he hj
      exact rootLabel_ne_of_join cs e e' hj (geometricSlope_injective he)
    have hs (s : Module.Dual ℝ (I → ℝ)) :
        (sortedSchedule F (lexEdgeScore s)).Pairwise (fun e e' => L e' ≤ L e) := by
      apply (sortedSchedule_pairwise F (lexEdgeScore s)).imp_of_mem
      intro e e' he he' _
      have hr := heq e ((mem_sortedSchedule _ _ _).mp he) e' ((mem_sortedSchedule _ _ _).mp he')
      exact (congrArg geometricSlope hr).symm.le
    exact dispatch_entries_eq_of_sorted (source cs) (target cs) T L hties p q
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _) (hs g) (hs h)
      (fun e => (mem_sortedSchedule _ _ e).trans (mem_sortedSchedule _ _ e).symm) x y

/-- All blocks may be replaced simultaneously on the finite lower region. -/
theorem grouped_entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (hf : rootPlaneTies (M := M) (cs := cs) f)
    (g h : Module.Dual ℝ (I → ℝ)) (x y : W) (hx : BruhatLE cs x b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore g)) x =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore h)) x := by
  let K := lowerFinset cs b
  have ht (s : Module.Dual ℝ (I → ℝ)) (a : ℝ) (e : Edge cs)
      (he : e ∈ scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore s) a) :
      target cs e ∈ K := by
    exact (mem_lowerFinset cs b _).mpr ((mem_edgeFinset cs b e).mp
      ((mem_scheduleBlock _ _ _ _ _).mp he).1)
  apply dispatch_flatMap_eq_on (source cs) (target cs) T (K : Set W)
    (blockValues (edgeFinset cs b) (rootValue f))
    (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore g))
    (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore h))
    (fun a _ e he => ht g a e he) _ _ x ((mem_lowerFinset cs b x).mpr hx)
  intro a _ v z hz
  apply dispatch_eq_of_entries_on (source cs) (target cs) T K _ _ (ht g a) (ht h a) _ v z hz
  intro l _ k hk
  exact block_entry_independent T b f hf g h a l k ((mem_lowerFinset cs b k).mp hk)

/-- Stable strict primary comparisons identify the genuine sorted schedule
with the corresponding product of tied blocks. -/
theorem entry_eq_grouped {R : Type*} [Semiring R] (T : R) (b : W)
    (f g : Module.Dual ℝ (I → ℝ))
    (h : ∀ e ∈ edgeFinset cs b, ∀ e' ∈ edgeFinset cs b,
      rootValue f e' < rootValue f e → rootValue g e' < rootValue g e)
    (x y : W) :
    entry (cs := cs) T g b x y =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore g)) x := by
  apply dispatch_entries_eq_of_sorted (source cs) (target cs) T (lexEdgeScore g)
    (lexEdgeScore_ties g) _ _ (sortedSchedule_nodup _ _) (groupedSchedule_nodup _ _ _)
    (sortedSchedule_pairwise _ _)
  · apply groupedSchedule_pairwise
    intro e he e' he' hlt
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (h e he e' he' hlt))
  · intro e
    simp only [mem_sortedSchedule,mem_groupedSchedule]

theorem pencil_strict_stable (b : W) (f g : Module.Dual ℝ (I → ℝ)) (t₀ : ℝ) :
    ∀ᶠ t in 𝓝 t₀, ∀ e ∈ edgeFinset cs b, ∀ e' ∈ edgeFinset cs b,
      rootValue (pencil f g t₀) e' < rootValue (pencil f g t₀) e →
        rootValue (pencil f g t) e' < rootValue (pencil f g t) e := by
  apply (Filter.eventually_all_finset _).mpr
  intro e _
  apply (Filter.eventually_all_finset _).mpr
  intro e' _
  have hc (k : Edge cs) : Continuous (fun t : ℝ => rootValue (pencil f g t) k) := by
    change Continuous (fun t : ℝ => (1-t)*f (normalizedRoot (rootLabel cs k))+
      t*g (normalizedRoot (rootLabel cs k)))
    fun_prop
  by_cases hlt : rootValue (pencil f g t₀) e' < rootValue (pencil f g t₀) e
  · filter_upwards [(isOpen_lt (hc e') (hc e)).mem_nhds hlt] with t ht
    exact fun _ => ht
  · exact Filter.Eventually.of_forall (fun _ h => (hlt h).elim)

/-- Crossing all actual root-plane walls leaves the full path matrix fixed,
not merely a single adapted endpoint column. -/
theorem locally_constant_pencil {R : Type*} [Semiring R] (T : R) (b : W)
    (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (x y : W) (hx : BruhatLE cs x b) :
    IsLocallyConstant (fun t : ℝ => entry (cs := cs) T (pencil f g t) b x y) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t₀
  filter_upwards [pencil_strict_stable b f g t₀] with t ht
  have hp : rootPlaneTies (M := M) (cs := cs) (pencil f g t₀) := by
    intro a d had he
    exact pencil_tie_plane f g hf hg t₀ a d had he
  rw [entry_eq_grouped T b (pencil f g t₀) (pencil f g t) ht,
    entry_eq_grouped T b (pencil f g t₀) (pencil f g t₀) (fun _ _ _ _ h => h)]
  exact grouped_entry_independent T b (pencil f g t₀) hp (pencil f g t) (pencil f g t₀) x y hx

/-- Full matrix order independence for genuine finite geometric orders. -/
theorem entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f h : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hh : Function.Injective (fun a : PositiveRoot M cs => h (normalizedRoot a)))
    (x y : W) (hx : BruhatLE cs x b) : entry (cs := cs) T f b x y=entry (cs := cs) T h b x y := by
  obtain ⟨g,_,hfg,hhg⟩ := exists_common_transverse (M := M) (cs := cs) f h
  have he := (locally_constant_pencil T b f g hf hfg x y hx).apply_eq_of_preconnectedSpace 0 1
  have he' := (locally_constant_pencil T b h g hh hhg x y hx).apply_eq_of_preconnectedSpace 0 1
  simp only [pencil_zero,pencil_one] at he he'
  exact he.trans he'.symm

end
end KLInvariance.WallDyer

end


section

/-! Dyer's full path-matrix identity, for the same geometric schedule in
every endpoint column, with the genuine Hecke-defined normalized R. -/
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_1_ra2d10a_1 (p : Prop) : Decidable p := Classical.propDecidable p
theorem neg_numerator_normalized (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (a : PositiveRoot M cs) :
    (-O.numerator) (normalizedRoot a) = -O.slope a := by
  simp only [LinearMap.neg_apply,dual_normalizedRoot,RatioOrder.slope,hh]

/-- An upper bound larger than the path endpoint creates no extra paths:
every actual directed path stays inside its endpoint interval. -/
theorem subpaths_neg_numerator (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (b x y : W) (hy : BruhatLE cs y b) :
    subpaths (source cs) (target cs) (WallDyer.schedule (-O.numerator) b) x y =
      paths O x y := by
  have hscore (e : Edge cs) : rootValue (-O.numerator) e = -score O e :=
    neg_numerator_normalized O hh (rootLabel cs e)
  ext p
  rw [mem_subpaths,mem_paths]
  constructor
  · rintro ⟨hsub,hpath⟩
    refine ⟨hpath,?_⟩
    have hs := (sortedSchedule_pairwise (edgeFinset cs b) (lexEdgeScore (-O.numerator))).sublist hsub
    have hs' : p.Pairwise (fun e e' => score O e ≤ score O e') := by
      apply hs.imp
      intro e e' he
      have hm := Prod.Lex.monotone_fst _ _ he
      change rootValue (-O.numerator) e' ≤ rootValue (-O.numerator) e at hm
      rw [hscore e',hscore e] at hm
      exact neg_le_neg_iff.mp hm
    exact decreasing_of_schedule_path (source cs) (target cs)
      (Λ := OrderDual ℝ) (fun e => (score O e : OrderDual ℝ))
      (fun e e' he => score_ties O e e' he) hpath hs'
  · rintro ⟨hpath,hord⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset (lexEdgeScore (-O.numerator))
    · apply hord.imp
      intro e e' he
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      change rootValue (-O.numerator) e' < rootValue (-O.numerator) e
      rw [hscore e',hscore e]
      exact neg_lt_neg he
    · exact sortedSchedule_pairwise _ _
    · intro e he
      apply (mem_sortedSchedule _ _ _).mpr
      exact (mem_edgeFinset cs b e).mpr ((path_targets_le cs hpath e he).trans hy)

theorem entry_neg_numerator (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (b x y : W) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) (-O.numerator) b x y =
      polynomial O x y := by
  unfold entry
  rw [dispatch_eq_subpaths_sum _ _ _ _ (show (WallDyer.schedule (-O.numerator) b).Nodup from sortedSchedule_nodup _ _),
    subpaths_neg_numerator O hh b x y hy]
  rfl


theorem entry_eq_rTilde (f : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (b x y : W) (hx : BruhatLE cs x b) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) f b x y = Hecke.rTilde cs x y := by
  obtain ⟨O,hO,hh⟩ := exists_ratioOrder_chamber_height (M := M) (cs := cs) y
  have hn : Function.Injective (fun a : PositiveRoot M cs => (-O.numerator) (normalizedRoot a)) := by
    intro a b he
    change (-O.numerator) (normalizedRoot a) = (-O.numerator) (normalizedRoot b) at he
    rw [neg_numerator_normalized O hh a,neg_numerator_normalized O hh b] at he
    exact O.slope_injective (neg_injective he)
  rw [entry_independent (Polynomial.X : Polynomial ℤ) b f (-O.numerator) hf hn x y hx,
    entry_neg_numerator O hh b x y hy,polynomial_eq_rTilde O x y hO]

/-- The manuscript's fixed geometric functional provides such a genuine
full Dyer schedule for every finite lower Bruhat region. -/
theorem geometric_entry_eq_rTilde (b x y : W) (hx : BruhatLE cs x b) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) (geometricFunctional (M := M) (cs := cs)) b x y =
      Hecke.rTilde cs x y := by
  apply entry_eq_rTilde _ _ b x y hx hy
  simpa only [geometricFunctional_normalizedRoot] using
    (geometricSlope_injective (M := M) (cs := cs))

end
end KLInvariance.WallDyer

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/

section

namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_6
omit [Fintype I] [Fintype I'] in
 theorem transportedEdge_injective : Function.Injective (transportedEdge φ) := by
  intro e f h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  exact Prod.ext (φ.injective (Subtype.ext (congrArg Prod.fst hh)))
    (φ.injective (Subtype.ext (congrArg Prod.snd hh)))

omit [Fintype I] in
 theorem transportedSchedule_nodup : (transportedSchedule φ).Nodup := by
  unfold transportedSchedule
  exact sortedSchedule_nodup _ _

omit [Fintype I] in
 theorem transportedSchedule_full (e : Edge cs u b) : e ∈ transportedSchedule φ := by
  let := Fintype.ofFinite (Edge cs u b)
  unfold transportedSchedule
  exact (mem_sortedSchedule _ _ _).mpr (Finset.mem_univ _)

omit [Fintype I] in
 theorem transportedSchedule_pairwise : (transportedSchedule φ).Pairwise
     (fun e f => transportedScore φ f ≤ transportedScore φ e) := by
  unfold transportedSchedule
  exact sortedSchedule_pairwise _ _

omit [Fintype I] [Fintype I'] in
 theorem transportedEdge_lift (e : AdaptedDyer.Edge cs')
    (hu : BruhatLE cs' u' (AdaptedDyer.source cs' e))
    (hb : BruhatLE cs' (AdaptedDyer.target cs' e) b') : ∃ f, transportedEdge φ f=e := by
  let x : Interval cs' u' b' := ⟨AdaptedDyer.source cs' e,hu,
    (show BruhatLE cs' (AdaptedDyer.source cs' e) (AdaptedDyer.target cs' e) from
      .single e.property).trans hb⟩
  let y : Interval cs' u' b' := ⟨AdaptedDyer.target cs' e,
    hu.trans (.single e.property),hb⟩
  let f : Edge cs u b := ⟨(φ.symm x,φ.symm y),
    (intervalIso_bruhatStep_iff_general cs' cs φ.symm x y).mpr e.property⟩
  refine ⟨f,?_⟩
  apply Subtype.ext
  change ((φ (φ.symm x)).val,(φ (φ.symm y)).val)=e.val
  rw [φ.apply_symm_apply,φ.apply_symm_apply]
  rfl

omit [Fintype I] in
 theorem transported_dispatch_entry {R : Type*} [Semiring R] (T : R)
    (x y : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) T (fun z => if z=y then 1 else 0)
      (transportedSchedule φ) x =
    WallDyer.entry (cs := cs') T (geometricFunctional (M := M') (cs := cs'))
      b' (φ x).val (φ y).val := by
  have hsource {z w : W'} {p : List (AdaptedDyer.Edge cs')}
      (hp : IsPath (AdaptedDyer.source cs') (AdaptedDyer.target cs') z w p) :
      ∀ e ∈ p, BruhatLE cs' z (AdaptedDyer.source cs' e) := by
    induction p generalizing z with
    | nil => simp
    | cons e p ih =>
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hp.1 ▸ bruhat_refl cs' z
      · rw [← hp.1]
        exact (show BruhatLE cs' (AdaptedDyer.source cs' e)
          (AdaptedDyer.target cs' e) from .single e.property).trans (ih hp.2 f hf)
  symm
  apply dispatch_entry_graph_embedding (AdaptedDyer.source cs') (AdaptedDyer.target cs')
    (source cs u b) (target cs u b) T
    (lexEdgeScore (geometricFunctional (M := M') (cs := cs')))
    (lexEdgeScore_ties _) (fun z : Interval cs u b => (φ z).val)
    (fun _ _ h => φ.injective (Subtype.ext h)) (transportedEdge φ)
    (transportedEdge_injective φ) (fun _ => rfl) (fun _ => rfl)
    (WallDyer.schedule (geometricFunctional (M := M') (cs := cs')) b')
    (transportedSchedule φ) (sortedSchedule_nodup _ _)
    (transportedSchedule_nodup φ) (sortedSchedule_pairwise _ _)
    (transportedSchedule_pairwise φ) (transportedSchedule_full φ)
  · intro e
    exact (mem_sortedSchedule _ _ _).mpr ((AdaptedDyer.mem_edgeFinset cs' b' _).mpr
      (φ (target cs u b e)).property.2)
  · intro r hr e he
    have hp := ((mem_subpaths _ _ _ _ _ r).mp hr).2
    exact transportedEdge_lift φ e ((φ x).property.1.trans (hsource hp e he))
      ((AdaptedDyer.path_targets_le cs' hp e he).trans (φ y).property.2)

omit [Fintype I] in

 theorem transported_entry_eq_rTilde (x y : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) (Polynomial.X : Polynomial ℤ)
      (fun z => if z=y then 1 else 0) (transportedSchedule φ) x =
      Hecke.rTilde cs' (φ x).val (φ y).val := by
  rw [transported_dispatch_entry]
  exact WallDyer.geometric_entry_eq_rTilde b' (φ x).val (φ y).val
    (φ x).property.2 (φ y).property.2

end
end KLInvariance.BruhatGraph

end


section

/-! Actual transported numerical R-tilde matrix and its genuine KL reciprocal
vector. No sheaf or desired invariance conclusion is assumed. -/
namespace KLInvariance.SchedulePaths
universe u v w w'
variable {V : Type u} {E : Type v} {R : Type w} {S : Type w'}
  [Semiring R] [Semiring S] (source target : E → V)
noncomputable section

 attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_5
theorem dispatch_map (f : R →+* S) (T : R) (v : V → R) (p : List E) (x : V) :
    f (dispatch source target T v p x) =
      dispatch source target (f T) (fun z => f (v z)) p x := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,step,map_add]
    split_ifs <;> simp only [map_mul,map_zero,ih]

end
end KLInvariance.SchedulePaths

namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem scaledKL_reciprocity_upper {C : Type*} [Field C]
    (t : C) (ht : t ≠ 0) (u b : W) (x : Interval cs u b) :
    scaledKL cs t x.val b = ∑ᶠ z : Interval cs u b,
      Polynomial.eval₂ (Int.castRingHom C) (t⁻¹-t) (Hecke.rTilde cs x.val z.val) *
        scaledKL cs t⁻¹ z.val b := by
  classical
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  let := interval_finite cs x.val b
  let := Fintype.ofFinite (Interval cs x.val b)
  rw [scaledKL_reciprocity cs t ht x.val b x.property.2,
    finsum_eq_sum_of_fintype,finsum_eq_sum_of_fintype]
  let f : W → C := fun z => Polynomial.eval₂ (Int.castRingHom C) (t⁻¹-t)
    (Hecke.rTilde cs x.val z) * scaledKL cs t⁻¹ z b
  have hs (a : W) [Fintype (Interval cs a b)] :
      (∑ z : Interval cs a b, f z.val) =
        ∑ z ∈ (lowerFinset cs b).filter (fun z => BruhatLE cs a z), f z := by
    exact (Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs a b)))
      ((lowerFinset cs b).filter (fun z => BruhatLE cs a z))
      (fun z => by simp only [Finset.mem_filter,mem_lowerFinset]; exact and_comm) f).symm
  change (∑ z : Interval cs x.val b, f z.val) = ∑ z : Interval cs u b, f z.val
  rw [hs,hs]
  apply Finset.sum_subset
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hz,hxz⟩
    exact Finset.mem_filter.mpr ⟨hz,x.property.1.trans hxz⟩
  · intro z hz hn
    have hxz : ¬ BruhatLE cs x.val z := by
      intro h
      exact hn (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,h⟩)
    dsimp [f]
    rw [Hecke.rTilde_zero cs _ _ hxz,Polynomial.eval₂_zero,zero_mul]

end
end KLInvariance

namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_7
theorem transported_entry_eval {C : Type*} [CommSemiring C] (T : C)
    (x y : Interval cs u b) (f : ℤ →+* C) :
    dispatch (source cs u b) (target cs u b) T
      (fun z => if z=y then 1 else 0) (transportedSchedule φ) x =
      Polynomial.eval₂ f T (Hecke.rTilde cs' (φ x).val (φ y).val) := by
  rw [← transported_entry_eq_rTilde φ x y]
  have h := dispatch_map (source cs u b) (target cs u b) (Polynomial.eval₂RingHom f T)
    Polynomial.X (fun z : Interval cs u b => if z=y then 1 else 0) (transportedSchedule φ) x
  simpa using h.symm

 theorem transported_dispatch_matrix {C : Type*} [CommSemiring C] (T : C)
    (f : ℤ →+* C) (v : Interval cs u b → C) (x : Interval cs u b) :
    dispatch (source cs u b) (target cs u b) T v (transportedSchedule φ) x =
      ∑ᶠ y : Interval cs u b,
        Polynomial.eval₂ f T (Hecke.rTilde cs' (φ x).val (φ y).val) * v y := by
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  rw [dispatch_eq_sum_entries,finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl (fun y _ => congrArg (fun a => a*v y)
    (transported_entry_eval φ T x y f))

 theorem transported_reciprocal_vector {C : Type*} [Field C]
    (t : C) (ht : t ≠ 0) (x : Interval cs u b) :
    scaledKL cs' t (φ x).val b' =
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (fun y => scaledKL cs' t⁻¹ (φ y).val b') (transportedSchedule φ) x := by
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  let := interval_finite cs' u' b'
  let := Fintype.ofFinite (Interval cs' u' b')
  rw [transported_dispatch_matrix φ _ (Int.castRingHom C),
    scaledKL_reciprocity_upper cs' t ht u' b' (φ x),
    finsum_eq_sum_of_fintype,finsum_eq_sum_of_fintype]
  exact (φ.toEquiv.sum_comp _).symm

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PositiveTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive transfer inequalities, strict Hilbert-series detection including higher-codimension support, and reverse-filtration projective-to-free arguments.
-/


section

/-! Strict later-label membership in a finite nondecreasing schedule,
with arbitrary positions for equal labels. -/
namespace KLInvariance.SchedulePaths
universe u v
variable {E : Type u} {Λ : Type v} [LinearOrder Λ]

 theorem mem_suffix_iff_score_lt (score : E → Λ) {p q : List E} {e f : E}
    (hs : p.Pairwise (fun a b => score a ≤ score b))
    (hq : e::q <:+ p) (hf : f ∈ p) (hne : score e ≠ score f) :
    f ∈ q ↔ score e < score f := by
  obtain ⟨a,rfl⟩ := hq
  have h := List.pairwise_append.mp hs
  constructor
  · intro hfq
    exact lt_of_le_of_ne ((List.pairwise_cons.mp h.2.1).1 f hfq) hne
  · intro hlt
    rcases List.mem_append.mp hf with hfa | hfr
    · exact False.elim (not_le_of_gt hlt (h.2.2 f hfa e List.mem_cons_self))
    · rcases List.mem_cons.mp hfr with rfl | hfr
      · exact False.elim (hne rfl)
      · exact hfr

end KLInvariance.SchedulePaths

end


section

/-! Exact identification of chronological suffix conditions with the
strictly-later root conditions used in the height-one edge-image proof.
Equal-label edges may be ordered arbitrarily and cause no extra incident
condition. -/
namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths MomentGraph
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

local instance instDecidable_solutions_8_ra2d10a_1 (p : Prop) : Decidable p := Classical.propDecidable p
omit [Fintype I] in
 theorem transportedScore_eq (e : Edge cs u b) : transportedScore φ e =
    toLex (transportedSlope φ e,transportedSlope φ e) := by
  unfold transportedScore lexEdgeScore lexRootScore transportedSlope
  rw [geometricFunctional_normalizedRoot]

omit [Fintype I] in
 theorem chronologicalSchedule_pairwise : (chronologicalSchedule φ).Pairwise
    (fun e f => transportedSlope φ e ≤ transportedSlope φ f) := by
  rw [chronologicalSchedule,List.pairwise_reverse]
  apply (transportedSchedule_pairwise φ).imp
  intro e f h
  have hh := Prod.Lex.monotone_fst _ _ h
  rw [transportedScore_eq,transportedScore_eq] at hh
  exact hh

omit [Fintype I] in
 theorem chronologicalSchedule_full (e : Edge cs u b) : e ∈ chronologicalSchedule φ :=
  List.mem_reverse.mpr (transportedSchedule_full φ e)

omit [Fintype I] in
 theorem transportedSlope_path_ne (e f : Edge cs u b)
    (hs : target cs u b e=source cs u b f) :
    transportedSlope φ e ≠ transportedSlope φ f := by
  intro h
  exact AdaptedDyer.rootLabel_ne_of_join cs' (transportedEdge φ e) (transportedEdge φ f)
    (congrArg (fun x => (φ x).val) hs) (geometricSlope_injective h)

omit [Fintype I] in
 theorem suffix_target_iff {e f : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ) (hf : source cs u b f=target cs u b e) :
    f ∈ q ↔ transportedSlope φ e < transportedSlope φ f :=
  mem_suffix_iff_score_lt (transportedSlope φ) (chronologicalSchedule_pairwise φ)
    hq (chronologicalSchedule_full φ f) (transportedSlope_path_ne φ e f hf.symm)

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_TerminalKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All-section transport, terminal kernels, scalar quotients, height-one membership in free targets and scaled edge-image inclusion.
-/


section

namespace KLInvariance.SchedulePaths
universe u v
variable {E : Type u} {Λ : Type v} [LinearOrder Λ]

 theorem exists_suffix_score_gt (score : E → Λ) (r : Λ) (p : List E)
    (hp : p.Pairwise (fun a b => score a ≤ score b)) :
    ∃ q, q <:+ p ∧ ∀ e, e ∈ q ↔ e ∈ p ∧ r < score e := by
  induction p with
  | nil => exact ⟨[],List.suffix_refl _,fun e => by simp⟩
  | cons a p ih =>
    have hs := List.pairwise_cons.mp hp
    by_cases ha : r < score a
    · refine ⟨a::p,List.suffix_refl _,?_⟩
      intro e
      constructor
      · intro he
        refine ⟨he,?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact ha
        · exact lt_of_lt_of_le ha (hs.1 e he)
      · exact And.left
    · obtain ⟨q,hq,hmem⟩ := ih hs.2
      refine ⟨q,hq.trans (List.suffix_cons a p),?_⟩
      intro e
      rw [hmem,List.mem_cons]
      constructor
      · exact fun h => ⟨Or.inr h.1,h.2⟩
      · rintro ⟨he,hr⟩
        rcases he with rfl | he
        · exact (ha hr).elim
        · exact ⟨he,hr⟩

end KLInvariance.SchedulePaths

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SimultaneousInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
R-first simultaneous invariance and transported-schedule terminal-kernel freeness: upper-interval freeness, lower-interval cancellation, reversal and endpoint bottom freeness; all-entry transport and KL degree rigidity.
-/

section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  {cs : CoxeterSystem M W} {I' : Type u'} {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem upperGraphInclusion_outgoing (x : Interval cs u b) (e : Edge cs u b)
    (z : Interval cs x.val b)
    (hz : (upperGraphInclusion x).vertex z=source cs u b e) :
    ∃ a, (upperGraphInclusion x).edge a=e ∧ source cs x.val b a=z := by
  have hzval := congrArg Subtype.val hz
  let y : Interval cs x.val b := ⟨(target cs u b e).val,
    z.property.1.trans (hzval.symm ▸ Relation.ReflTransGen.single e.property),
    (target cs u b e).property.2⟩
  let a : Edge cs x.val b := ⟨(z,y),hzval.symm ▸ e.property⟩
  refine ⟨a,?_,rfl⟩
  exact Subtype.ext (Prod.ext hz rfl)

variable [Fintype I']

 theorem cutoff_is_suffix (s : ℝ) :
    ∃ q, q <:+ chronologicalSchedule φ ∧
      ∀ e : Edge cs u b, e ∈ q ↔ s < transportedSlope φ e := by
  obtain ⟨q,hq,he⟩ := exists_suffix_score_gt (transportedSlope φ) s
    (chronologicalSchedule φ) (chronologicalSchedule_pairwise φ)
  exact ⟨q,hq,fun e => by simpa only [chronologicalSchedule_full φ e,true_and] using he e⟩

variable [Fintype I] {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)

 theorem intervalBoundary_upper_kernel (x : Interval cs u b)
    (z : Interval cs x.val b) (T : Set (Edge cs u b)) :
    (intervalBoundary basis x.property.2).sheaf.upwardSubmodule z
      {e | (upperGraphInclusion x).edge e.val ∈ T} =
    (intervalBoundary basis hub).sheaf.upwardSubmodule ((upperGraphInclusion x).vertex z)
      {e | e.val ∈ T} := by
  exact (intervalBoundary basis hub).sheaf.forget.pullback_kernel
    (upperGraphInclusion x) z T Set.univ
    (fun e he => False.elim (he (Set.mem_univ e)))
    (fun e _ he => upperGraphInclusion_outgoing x e z he)

end
end KLInvariance.BruhatGraph

end


section

/-! Transport of the actual partial-kernel freeness from a smaller-bottom
interval. No change of ambient sheaf, grading, or reflection order. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem target_free_of_upper_suffixes {e : Edge cs u b} {q : List (Edge cs u b)}
    (hq : e::q <:+ chronologicalSchedule φ)
    (hsmall : FreeSuffixes basis (target cs u b e).property.2
      (upperIntervalIso φ (target cs u b e))) :
    Module.Free (Coefficient (σ := σ))
      ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
        (remainingConditions cs u b q (target cs u b e))) := by
  let x := target cs u b e
  let z := intervalBottom cs x.property.2
  obtain ⟨p,hp,he⟩ := cutoff_is_suffix (upperIntervalIso φ x) (transportedSlope φ e)
  have hh := hsmall p hp z
  let T : Set (Edge cs u b) := {f | transportedSlope φ e < transportedSlope φ f}
  have hs : remainingConditions cs x.val b p z =
      {f | (upperGraphInclusion x).edge f.val ∈ T} := by
    ext f
    exact he f.val
  rw [hs,intervalBoundary_upper_kernel basis hub x z T] at hh
  have hb : remainingConditions cs u b q x = {f | f.val ∈ T} := by
    ext f
    exact suffix_target_iff φ hq f.property
  rw [hb]
  exact hh

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.Comparison
open Polynomial
noncomputable section

 theorem eq_of_scaled_difference_reciprocal (p p' : ℤ[X]) (d : ℕ)
    (hp : 2*p.natDegree < d) (hp' : 2*p'.natDegree < d)
    (h : ∀ t : ℝ, 0 < t → t < 1 →
      scaledPolynomial t d p-scaledPolynomial t d p' =
        scaledPolynomial t⁻¹ d p-scaledPolynomial t⁻¹ d p') : p=p' := by
  apply eq_of_eval_difference_reciprocal p p' d hp hp'
  intro q hq hq1
  let t := Real.sqrt q
  have ht : 0 < t := Real.sqrt_pos.2 hq
  have hsq : t^2=q := Real.sq_sqrt hq.le
  have ht1 : t < 1 := by nlinarith
  have hisq : (t⁻¹)^2=q⁻¹ := by rw [inv_pow,hsq]
  have he := h t ht ht1
  simp only [scaledPolynomial,zpow_neg,zpow_natCast,inv_pow,inv_inv,hsq,hisq,
    ← mul_sub] at he
  have hh := congrArg (fun z : ℝ => t^d*z) he
  have htd : t^d ≠ 0 := pow_ne_zero d ht.ne'
  rw [← mul_assoc,mul_inv_cancel₀ htd,one_mul] at hh
  rw [← mul_assoc,← pow_add] at hh
  rw [show d+d=2*d by omega,pow_mul,hsq] at hh
  exact hh

 theorem matrix_difference_single {V : Type*} [Fintype V] (a : V → ℝ)
    (v w : V → ℝ) (x : V) (hdiag : a x=1)
    (hvw : ∀ y, y ≠ x → v y=w y) :
    (∑ y, a y*v y)-(∑ y, a y*w y)=v x-w x := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ y, (a y*v y-a y*w y)) = ∑ y, if y=x then v x-w x else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y=x
      · subst y
        simp [hdiag]
      · simp [hy,hvw y hy]
    _ = v x-w x := by simp

 theorem matrix_difference_le {V : Type*} [Fintype V]
    (a : V → ℝ) (v w : V → ℝ) (x : V) (p p' : ℝ)
    (hdiag : a x=1) (hvw : ∀ y, y ≠ x → v y=w y)
    (hp : p ≤ ∑ y, a y*v y) (hp' : p'=∑ y, a y*w y) :
    p-p' ≤ v x-w x := by
  rw [← matrix_difference_single a v w x hdiag hvw]
  exact sub_le_sub hp hp'.ge

end
end KLInvariance.Comparison

end


section

/-! A different closing invariant: genuine R kernels. Comparing actual BMP
characters, native R-reciprocity cancels all proper-lower-interval entries.
The top stalk is 1, so the remaining bottom/top R entry is bounded directly.
No degree or character-identification assertion is required. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'} (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
  (φ : Interval cs a b ≃o Interval cs' a' b')
noncomputable section

 local instance instDecidableEq_solutions_2_ra2d10a_1 (X : Type*) : DecidableEq X := Classical.decEq X
theorem scaledStalk_upper_top {C : Type*} [Field C] (t : C) :
    scaledStalk cs b basis t ((upperInclusion cs a b).vertex (intervalTop cs hab))=1 := by
  change t^((cs.length b : ℤ)-cs.length b)*
    eval₂ (Int.castRingHom C) (t^2)
      (stalkCharacter cs 1 b basis (one_bruhat cs b)
        ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)=1
  rw [stalkCharacter_top]
  simp

include hab hab'

 theorem rTilde_eval_le_of_comparison
    (hrow : ∀ z : Interval cs a b, z.val≠b →
      Hecke.rTilde cs a z.val=Hecke.rTilde cs' a' (φ z).val)
    {t : ℝ} (ht : 0<t) (_ht1 : t<1)
    (hcomp : (fun x : Interval cs a b => scaledStalk cs b basis t ((upperInclusion cs a b).vertex x)) ≤
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (fun x => scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex x))
        (transportedSchedule φ)) :
    eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs a b) ≤
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs' a' b') := by
  let := interval_finite cs a b
  let := Fintype.ofFinite (Interval cs a b)
  have hc := hcomp (intervalBottom cs hab)
  change scaledStalk cs b basis t ((upperInclusion cs a b).vertex (intervalBottom cs hab)) ≤ _ at hc
  rw [transported_dispatch_matrix φ _ (Int.castRingHom ℝ),
    scaledStalk_reciprocity_upper cs b basis t ht.ne' a,
    intervalIso_bottom cs cs' hab hab' φ,finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype] at hc
  have hd := Comparison.matrix_difference_single
    (fun z : Interval cs a b => scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z))
    (fun z => eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs a z.val))
    (fun z => eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs' a' (φ z).val))
    (intervalTop cs hab) (scaledStalk_upper_top basis hab t⁻¹)
    (fun z hz => congrArg _ (hrow z (fun h => hz (Subtype.ext h))))
  rw [intervalIso_top cs cs' hab hab' φ] at hd
  have hh : (∑ z : Interval cs a b, scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z)*
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs a z.val))-
      (∑ z : Interval cs a b, scaledStalk cs b basis t⁻¹ ((upperInclusion cs a b).vertex z)*
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs' a' (φ z).val)) ≤ 0 := by
    apply sub_nonpos.mpr
    simpa only [mul_comm,intervalBottom] using hc
  rw [hd] at hh
  exact sub_nonpos.mp hh

 theorem rTilde_eval_le_of_upper_freeness
    (hrow : ∀ z : Interval cs a b, z.val≠b →
      Hecke.rTilde cs a z.val=Hecke.rTilde cs' a' (φ z).val)
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e))))
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs a b) ≤
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) (Hecke.rTilde cs' a' b') :=
  rTilde_eval_le_of_comparison basis hab hab' φ hrow ht ht1
    (actual_comparison_of_upper_freeness basis hab φ hfree ht ht1)

end
end KLInvariance.BruhatGraph

namespace KLInvariance.Comparison
open Polynomial
 theorem polynomial_eq_of_transfer_eval_eq (p q : ℤ[X])
    (h : ∀ t : ℝ, 0<t → t<1 →
      eval₂ (Int.castRingHom ℝ) (t⁻¹-t) p=eval₂ (Int.castRingHom ℝ) (t⁻¹-t) q) : p=q := by
  apply Polynomial.map_injective (f := Int.castRingHom ℝ) Int.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Set.InjOn (fun t : ℝ => t⁻¹-t) (Set.Ioo 0 1) := by
    apply StrictAntiOn.injOn
    intro x hx y _ hxy
    exact sub_lt_sub (inv_lt_inv₀ (lt_trans hx.1 hxy) hx.1 |>.mpr hxy) hxy
  apply (Set.Ioo_infinite (show (0:ℝ)<1 by norm_num)).image hinj |>.mono
  rintro _ ⟨t,ht,rfl⟩
  simpa only [eval_map,Set.mem_ofPred_eq] using h t ht.1 ht.2
end KLInvariance.Comparison

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Invariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Genuine KL invariance, finite-parabolic transport and unrestricted finite interval models; the main theorem for two arbitrary Coxeter systems in four independent universes.
-/

section

namespace KLInvariance
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'}
noncomputable section

 theorem rankDifference_subinterval_lt (x z : Interval cs a b) (hxz : x≤z)
    (hne : x.val≠a ∨ z.val≠b) :
    rankDifference cs x.val z.val < rankDifference cs a b := by
  have ha := length_le_of_bruhat cs x.property.1
  have hb := length_le_of_bruhat cs z.property.2
  have hm := length_le_of_bruhat cs hxz
  dsimp only [rankDifference]
  rcases hne with h|h
  · have := length_lt_of_bruhat_ne cs x.property.1 h.symm
    omega
  · have := length_lt_of_bruhat_ne cs z.property.2 h
    omega

 theorem rTilde_transport_all (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b')
    (hr : Hecke.rTilde cs a b=Hecke.rTilde cs' a' b')
    (hsmall : ∀ (x z : Interval cs a b), x≤z →
      rankDifference cs x.val z.val < rankDifference cs a b →
      Hecke.rTilde cs x.val z.val=Hecke.rTilde cs' (φ x).val (φ z).val) :
    ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val := by
  intro x z
  by_cases hxz : x≤z
  · by_cases hxa : x.val=a
    · by_cases hzb : z.val=b
      · have hx : x=intervalBottom cs hab := Subtype.ext hxa
        have hz : z=intervalTop cs hab := Subtype.ext hzb
        rw [hx,hz,intervalIso_bottom cs cs' hab hab' φ,intervalIso_top cs cs' hab hab' φ]
        exact hr
      · exact hsmall x z hxz (rankDifference_subinterval_lt x z hxz (Or.inr hzb))
    · exact hsmall x z hxz (rankDifference_subinterval_lt x z hxz (Or.inl hxa))
  · have hnot : ¬BruhatLE cs' (φ x).val (φ z).val := fun h => hxz (φ.le_iff_le.mp h)
    rw [Hecke.rTilde_zero cs x.val z.val hxz,Hecke.rTilde_zero cs' _ _ hnot]

end
end KLInvariance

end


section

/-! One rank-induction step for genuine R invariance. All inputs concern strictly
smaller intervals in the eventual induction; no KL character theorem is assumed. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {σ' : Type u'} [Fintype σ'] (basis' : Basis σ' ℝ (Extended M'))
  {a b : W} {a' b' : W'} (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
  (φ : Interval cs a b ≃o Interval cs' a' b')
noncomputable section

 theorem actual_target_freeness
    (hupper : ∀ y : Interval cs a b, y.val≠a →
      FreeSuffixes basis y.property.2 (upperIntervalIso φ y)) :
    ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e))) := by
  intro e q hq
  apply target_free_of_upper_suffixes basis hab φ hq
  apply hupper
  have hle := length_le_of_bruhat cs (source cs a b e).property.1
  have hlt := e.property.1
  change cs.length (source cs a b e).val < cs.length (target cs a b e).val at hlt
  intro heq
  rw [heq] at hlt
  omega

include hab hab' in
 theorem rTilde_eq_of_smaller_data
    (hrow : ∀ z : Interval cs a b, z.val≠b →
      Hecke.rTilde cs a z.val=Hecke.rTilde cs' a' (φ z).val)
    (hrow' : ∀ z : Interval cs' a' b', z.val≠b' →
      Hecke.rTilde cs' a' z.val=Hecke.rTilde cs a (φ.symm z).val)
    (hupper : ∀ y : Interval cs a b, y.val≠a →
      FreeSuffixes basis y.property.2 (upperIntervalIso φ y))
    (hupper' : ∀ y : Interval cs' a' b', y.val≠a' →
      FreeSuffixes basis' y.property.2 (upperIntervalIso φ.symm y)) :
    Hecke.rTilde cs a b=Hecke.rTilde cs' a' b' := by
  apply Comparison.polynomial_eq_of_transfer_eval_eq
  intro t ht ht1
  apply le_antisymm
  · exact rTilde_eval_le_of_upper_freeness basis hab hab' φ hrow
      (actual_target_freeness basis hab φ hupper) ht ht1
  · exact rTilde_eval_le_of_upper_freeness basis' hab' hab φ.symm hrow'
      (actual_target_freeness basis' hab' φ.symm hupper') ht ht1

end
end KLInvariance.BruhatGraph

end


section

/-! Unconditional genuine R-tilde invariance and transported terminal freeness.
Induction is over arbitrary interval rank, with both endpoints varying. Actual
BMP characters are only test vectors for the edge inequalities. Their genuine
R-reciprocity and top1 are enough; strict halfdegree is NOT assumed. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {σ' : Type u'} [Fintype σ'] (basis' : Basis σ' ℝ (Extended M'))
noncomputable section

 theorem rTilde_freeness_of_below
    (a b : W) (a' b' : W') (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b') (n : ℕ) (hn : rankDifference cs a b=n)
    (hbelow : ∀ (c d : W) (c' d' : W') (hcd : BruhatLE cs c d) (hcd' : BruhatLE cs' c' d')
      (ψ : Interval cs c d ≃o Interval cs' c' d'), rankDifference cs c d<n →
      Hecke.rTilde cs c d=Hecke.rTilde cs' c' d' ∧
        FreeSuffixes basis hcd ψ ∧ FreeSuffixes basis' hcd' ψ.symm) :
    Hecke.rTilde cs a b=Hecke.rTilde cs' a' b' ∧
      FreeSuffixes basis hab φ ∧ FreeSuffixes basis' hab' φ.symm := by
  have hn' : rankDifference cs' a' b'=n :=
    (intervalIso_full_rankDifference cs cs' hab hab' φ).symm.trans hn
  have hsmall (x z : Interval cs a b) (hxz : x≤z)
      (hlt : rankDifference cs x.val z.val < rankDifference cs a b) :
      Hecke.rTilde cs x.val z.val=Hecke.rTilde cs' (φ x).val (φ z).val :=
    (hbelow x.val z.val (φ x).val (φ z).val hxz (φ.monotone hxz)
      (intervalIso_restrict cs cs' φ x z) (hn ▸ hlt)).1
  have hrow (z : Interval cs a b) (hz : z.val≠b) :
      Hecke.rTilde cs a z.val=Hecke.rTilde cs' a' (φ z).val := by
    have h := hsmall (intervalBottom cs hab) z z.property.1
      (rankDifference_subinterval_lt (intervalBottom cs hab) z z.property.1 (Or.inr hz))
    rw [intervalIso_bottom cs cs' hab hab' φ] at h
    exact h
  have hrow' (z : Interval cs' a' b') (hz : z.val≠b') :
      Hecke.rTilde cs' a' z.val=Hecke.rTilde cs a (φ.symm z).val := by
    let x := intervalBottom cs' hab'
    have hxz : x≤z := z.property.1
    have hlt : rankDifference cs (φ.symm x).val (φ.symm z).val<n := by
      rw [←intervalIso_rankDifference cs' cs φ.symm hxz]
      exact hn' ▸ rankDifference_subinterval_lt x z hxz (Or.inr hz)
    have h := (hbelow (φ.symm x).val (φ.symm z).val x.val z.val
      (φ.symm.monotone hxz) hxz (intervalIso_restrict cs' cs φ.symm x z).symm hlt).1.symm
    dsimp only [x] at h
    rw [intervalIso_bottom cs' cs hab' hab φ.symm] at h
    exact h
  have hupper (y : Interval cs a b) (hy : y.val≠a) :
      FreeSuffixes basis y.property.2 (upperIntervalIso φ y) := by
    exact (hbelow y.val b (φ y).val b' y.property.2 (φ y).property.2
      (upperIntervalIso φ y)
      (hn ▸ rankDifference_subinterval_lt y (intervalTop cs hab) y.property.2 (Or.inl hy))).2.1
  have hupper' (y : Interval cs' a' b') (hy : y.val≠a') :
      FreeSuffixes basis' y.property.2 (upperIntervalIso φ.symm y) := by
    let ψ := (upperIntervalIso φ.symm y).symm
    have hlt : rankDifference cs (φ.symm y).val b<n := by
      rw [intervalIso_full_rankDifference cs cs' (φ.symm y).property.2 y.property.2 ψ]
      exact hn' ▸ rankDifference_subinterval_lt y (intervalTop cs' hab') y.property.2 (Or.inl hy)
    exact (hbelow (φ.symm y).val b y.val b' (φ.symm y).property.2 y.property.2 ψ hlt).2.2
  have hr := rTilde_eq_of_smaller_data basis basis' hab hab' φ hrow hrow' hupper hupper'
  have hrall := rTilde_transport_all hab hab' φ hr hsmall
  refine ⟨hr,actual_freeSuffixes_of_rTilde_eq basis hab φ hrall
    (actual_target_freeness basis hab φ hupper),?_⟩
  apply actual_freeSuffixes_of_rTilde_eq basis' hab' φ.symm
    (fun x z => by simpa only [φ.apply_symm_apply] using (hrall (φ.symm x) (φ.symm z)).symm)
    (actual_target_freeness basis' hab' φ.symm hupper')

 theorem rTilde_invariance_and_freeness
    (a b : W) (a' b' : W') (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b') :
    Hecke.rTilde cs a b=Hecke.rTilde cs' a' b' ∧
      FreeSuffixes basis hab φ ∧ FreeSuffixes basis' hab' φ.symm := by
  have hp : ∀ n, ∀ (c d : W) (c' d' : W') (hcd : BruhatLE cs c d) (hcd' : BruhatLE cs' c' d')
      (ψ : Interval cs c d ≃o Interval cs' c' d'), rankDifference cs c d=n →
      Hecke.rTilde cs c d=Hecke.rTilde cs' c' d' ∧
        FreeSuffixes basis hcd ψ ∧ FreeSuffixes basis' hcd' ψ.symm := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c d c' d' hcd hcd' ψ hn
      apply rTilde_freeness_of_below basis basis' c d c' d' hcd hcd' ψ n hn
      intro e f e' f' hef hef' θ hlt
      exact ih _ hlt e f e' f' hef hef' θ rfl
  exact hp _ a b a' b' hab hab' φ rfl

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance
open Polynomial
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem scaledKL_eq_scaledPolynomial (t : ℝ) {x b : W} (hxb : BruhatLE cs x b) :
    scaledKL cs t x b = Comparison.scaledPolynomial t (rankDifference cs x b)
      (klPolynomial cs x b) := by
  have hh := length_le_of_bruhat cs hxb
  have he : (cs.length x : ℤ)-cs.length b = -(rankDifference cs x b : ℤ) := by
    unfold rankDifference
    omega
  simp only [scaledKL,Comparison.scaledPolynomial,he]

variable {I' : Type u'} {M' : CoxeterMatrix I'} {W' : Type v'} [Group W']
  (cs' : CoxeterSystem M' W') {u b : W} {u' b' : W'}
  (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
  (φ : Interval cs u b ≃o Interval cs' u' b')

include hub hub'

 theorem intervalIso_upper_rankDifference (x : Interval cs u b) :
    rankDifference cs x.val b = rankDifference cs' (φ x).val b' := by
  have h := intervalIso_rankDifference cs cs' φ
    (show x ≤ intervalTop cs hub from x.property.2)
  rw [intervalIso_top cs cs' hub hub' φ] at h
  exact h

 theorem scaledKL_transport (t : ℝ) (x : Interval cs u b)
    (hx : klPolynomial cs x.val b=klPolynomial cs' (φ x).val b') :
    scaledKL cs t x.val b=scaledKL cs' t (φ x).val b' := by
  rw [scaledKL_eq_scaledPolynomial cs t x.property.2,
    scaledKL_eq_scaledPolynomial cs' t (φ x).property.2,
    intervalIso_upper_rankDifference cs cs' hub hub' φ x,hx]

end
end KLInvariance

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

omit [Fintype I] in
include hub in
 theorem comparison_difference_le (hub' : BruhatLE cs' u' b')
    (x : Interval cs u b)
    (hother : ∀ y : Interval cs u b, y ≠ x →
      klPolynomial cs y.val b=klPolynomial cs' (φ y).val b')
    {t : ℝ} (ht : t ≠ 0)
    (hcomp : scaledKL cs t x.val b ≤
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (fun y => scaledKL cs t⁻¹ y.val b) (transportedSchedule φ) x) :
    scaledKL cs t x.val b-scaledKL cs' t (φ x).val b' ≤
      scaledKL cs t⁻¹ x.val b-scaledKL cs' t⁻¹ (φ x).val b' := by
  classical
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  have hp' := transported_reciprocal_vector φ t ht x
  rw [transported_dispatch_matrix φ _ (Int.castRingHom ℝ),finsum_eq_sum_of_fintype] at hcomp hp'
  exact Comparison.matrix_difference_le _ _ _ x _ _ (by simp)
    (fun y hy => scaledKL_transport cs cs' hub hub' φ t⁻¹ y (hother y hy)) hcomp hp'

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem bottom_eq_of_comparisons (hne : u ≠ b)
    (hupper : ∀ y : Interval cs u b, y.val ≠ u →
      klPolynomial cs y.val b=klPolynomial cs' (φ y).val b')
    (hforward : ∀ t : ℝ, 0<t → t<1 →
      scaledKL cs t u b ≤ dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (fun y => scaledKL cs t⁻¹ y.val b) (transportedSchedule φ) (intervalBottom cs hub))
    (hbackward : ∀ t : ℝ, 0<t → t<1 →
      scaledKL cs' t u' b' ≤ dispatch (source cs' u' b') (target cs' u' b') (t⁻¹-t)
        (fun y => scaledKL cs' t⁻¹ y.val b') (transportedSchedule φ.symm)
          (intervalBottom cs' hub')) : klPolynomial cs u b=klPolynomial cs' u' b' := by
  have hr := intervalIso_full_rankDifference cs cs' hub hub' φ
  have hne' : u' ≠ b' := by
    intro h
    have hp := length_lt_of_bruhat_ne cs hub hne
    unfold rankDifference at hr
    simp only [h,Nat.sub_self] at hr
    omega
  apply Comparison.eq_of_scaled_difference_reciprocal
    (klPolynomial cs u b) (klPolynomial cs' u' b') (rankDifference cs u b)
    ((klFamilies_spec cs).P_degree u b hub hne)
  · rw [hr]
    exact (klFamilies_spec cs').P_degree u' b' hub' hne'
  intro t ht ht1
  have hf := comparison_difference_le hub φ hub' (intervalBottom cs hub)
    (fun y hy => hupper y (fun he => hy (Subtype.ext he))) ht.ne' (hforward t ht ht1)
  have hb := comparison_difference_le hub' φ.symm hub (intervalBottom cs' hub')
    (fun y hy => by
      have hyy : (φ.symm y).val ≠ u := by
        intro he
        have he' : φ.symm y=intervalBottom cs hub := Subtype.ext he
        apply hy
        have hh := congrArg φ he'
        rw [φ.apply_symm_apply,intervalIso_bottom cs cs' hub hub' φ] at hh
        exact hh
      simpa only [φ.apply_symm_apply] using (hupper (φ.symm y) hyy).symm)
    ht.ne' (hbackward t ht ht1)
  rw [intervalIso_bottom cs cs' hub hub' φ] at hf
  rw [intervalIso_bottom cs' cs hub' hub φ.symm] at hb
  change scaledKL cs t u b-scaledKL cs' t u' b' ≤
    scaledKL cs t⁻¹ u b-scaledKL cs' t⁻¹ u' b' at hf
  change scaledKL cs' t u' b'-scaledKL cs t u b ≤
    scaledKL cs' t⁻¹ u' b'-scaledKL cs t⁻¹ u b at hb
  have he : scaledKL cs t u b-scaledKL cs' t u' b' =
      scaledKL cs t⁻¹ u b-scaledKL cs' t⁻¹ u' b' := by linarith
  simpa only [scaledKL_eq_scaledPolynomial cs _ hub,
    scaledKL_eq_scaledPolynomial cs' _ hub',hr] using he

end
end KLInvariance.BruhatGraph

end


section

/-! Closing the main theorem in finite generator rank. The actual BMP sheaves
are used only to prove the genuine R-kernel invariance. Canonical KL degree
bounds and reciprocity now identify the genuine KL polynomials; no BMP stalk
character identification or strict halfdegree assumption is used. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {σ' : Type u'} [Fintype σ'] (basis' : Basis σ' ℝ (Extended M'))
noncomputable section
include basis basis'

 theorem rTilde_invariance_all_entries {a b : W} {a' b' : W'}
    (φ : Interval cs a b ≃o Interval cs' a' b') (x z : Interval cs a b) :
    Hecke.rTilde cs x.val z.val=Hecke.rTilde cs' (φ x).val (φ z).val := by
  by_cases h : x≤z
  · exact (rTilde_invariance_and_freeness basis basis' x.val z.val (φ x).val (φ z).val
      h (φ.monotone h) (intervalIso_restrict cs cs' φ x z)).1
  · rw [Hecke.rTilde_zero cs _ _ h, Hecke.rTilde_zero cs' _ _ (fun h' => h (φ.le_iff_le.mp h'))]

 theorem scaledKL_eq_transported {a b : W} {a' b' : W'}
    (φ : Interval cs a b ≃o Interval cs' a' b')
    {C : Type*} [Field C] (t : C) (ht : t≠0) (x : Interval cs a b) :
    scaledKL cs t x.val b =
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (fun y => scaledKL cs t⁻¹ y.val b) (transportedSchedule φ) x := by
  rw [transported_dispatch_matrix φ _ (Int.castRingHom C),
    scaledKL_reciprocity_upper cs t ht a b x]
  apply finsum_congr
  intro z
  rw [rTilde_invariance_all_entries basis basis' φ x z]

 theorem klPolynomial_invariance_finite (a b : W) (a' b' : W')
    (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b') :
    klPolynomial cs a b=klPolynomial cs' a' b' := by
  have hp : ∀ n, ∀ (c : W) (c' : W')
      (hcb : BruhatLE cs c b) (hcb' : BruhatLE cs' c' b')
      (ψ : Interval cs c b ≃o Interval cs' c' b'), rankDifference cs c b=n →
      klPolynomial cs c b=klPolynomial cs' c' b' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c c' hcb hcb' ψ hn
      by_cases hne : c=b
      · have hne' : c'=b' := by
          by_contra h
          have hp := length_lt_of_bruhat_ne cs' hcb' h
          have hr := intervalIso_full_rankDifference cs cs' hcb hcb' ψ
          unfold rankDifference at hr
          rw [hne,Nat.sub_self] at hr
          omega
        simp only [hne,hne',klPolynomial,(klFamilies_spec cs).P_diagonal,(klFamilies_spec cs').P_diagonal]
      · apply bottom_eq_of_comparisons hcb hcb' ψ hne
        · intro y hy
          apply ih (rankDifference cs y.val b)
            (hn ▸ rankDifference_subinterval_lt y (intervalTop cs hcb) y.property.2 (Or.inl hy))
            y.val (ψ y).val y.property.2 (ψ y).property.2 (upperIntervalIso ψ y) rfl
        · intro t ht _ht1
          exact (scaledKL_eq_transported basis basis' ψ t ht.ne' (intervalBottom cs hcb)).le
        · intro t ht _ht1
          exact (scaledKL_eq_transported basis' basis ψ.symm t ht.ne' (intervalBottom cs' hcb')).le
  exact hp _ a a' hab hab' φ rfl

end
end KLInvariance.BruhatGraph

end


section

/-! The finite-rank reduction of the exact main target.  The model's interval
and genuine KL polynomial are identified with those of the unrestricted
ambient Coxeter system, not with an order-theoretically defined invariant. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (u b : W)
noncomputable section

 theorem exists_finiteIntervalModel (hub : BruhatLE cs u b) :
    Nonempty (FiniteIntervalModel cs u b) := by
  obtain ⟨J,hJ,hJgen⟩ := lower_ideal_finite_generator_support cs b
  obtain ⟨v,hv,hvu⟩ := hJgen u hub
  obtain ⟨w,hw,hwb⟩ := hJgen b (bruhat_refl cs b)
  obtain ⟨v',hv'⟩ := StandardParabolic.lift_word J hv
  obtain ⟨w',hw'⟩ := StandardParabolic.lift_word J hw
  refine ⟨⟨J,hJ,(StandardParabolic.system (M := M) J).wordProd v',
    (StandardParabolic.system (M := M) J).wordProd w',?_,?_⟩⟩
  · rw [StandardParabolic.inclusion_word,hv',hvu]
  · rw [StandardParabolic.inclusion_word,hw',hwb]

namespace FiniteIntervalModel
variable {cs u b} (F : FiniteIntervalModel cs u b)

 theorem bruhat (hub : BruhatLE cs u b) :
    BruhatLE (StandardParabolic.system (M := M) F.indices) F.lower F.upper := by
  let _ : Fintype F.indices := F.finite.fintype
  apply (StandardParabolic.bruhat_inclusion_iff cs F.indices F.lower F.upper).mp
  simpa only [F.lower_eq,F.upper_eq] using hub

 theorem kl_eq : klPolynomial (StandardParabolic.system (M := M) F.indices) F.lower F.upper =
    klPolynomial cs u b := by
  let _ : Fintype F.indices := F.finite.fintype
  simpa only [F.lower_eq,F.upper_eq] using
    (StandardParabolic.klPolynomial_inclusion cs F.indices F.lower F.upper).symm

end FiniteIntervalModel
end
end KLInvariance

end


section

/-! Exact unrestricted main theorem. Finite parabolic restriction preserves
actual intervals and genuine equal-parameter KL polynomials. Bases used in
the temporary finite realization are selected here, not added as hypotheses. -/
namespace KLInvariance
open Module TitsSpace BruhatGraph
universe u v u' v'
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
noncomputable section

 theorem combinatorial_invariance_oai
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'}
    (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    klPolynomial cs u b = klPolynomial cs' u' b' := by
  obtain ⟨F⟩ := exists_finiteIntervalModel cs u b hub
  obtain ⟨F'⟩ := exists_finiteIntervalModel cs' u' b' hub'
  let : Fintype F.indices := F.finite.fintype
  let : Fintype F'.indices := F'.finite.fintype
  let basis := Module.Free.chooseBasis ℝ (Extended (StandardParabolic.matrix (M := M) F.indices))
  let basis' := Module.Free.chooseBasis ℝ (Extended (StandardParabolic.matrix (M := M') F'.indices))
  rw [←F.kl_eq,←F'.kl_eq]
  exact klPolynomial_invariance_finite basis basis' F.lower F.upper F'.lower F'.upper
    (F.bruhat hub) (F'.bruhat hub') ((F.orderIso.trans ι).trans F'.orderIso.symm)

end
end KLInvariance

end


-- Recursive standard-axiom closure of the exact unrestricted exported main.

end OAI
end

theorem solution.{u, v, u', v'} : type_of% @OAI.KLInvariance.combinatorial_invariance_oai.{u, v, u', v'} := @OAI.KLInvariance.combinatorial_invariance_oai.{u, v, u', v'}
