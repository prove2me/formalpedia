-- Prove2me | solution 1 for OAI.JointDickman.largeMajorArc_box_bound_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:45:04.608215+00:00
-- url     : https://prove2.me/submissions/639c663b-e66e-469b-a13d-b36e37001a4d

import Mathlib
import Definitions.Def_OAIQ083J003

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OscillatoryTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth oscillatory tests used in the coefficient estimate -/

namespace JointDickman

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_additivePhase (x : ℝ) :
    HasDerivAt additivePhase (additivePhase x * ((2 * Real.pi : ℝ) * Complex.I)) x := by
  have h := (((hasDerivAt_id x).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simpa only [mul_one, id_eq] using! h

theorem continuous_additivePhase : Continuous additivePhase :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_additivePhase x).continuousAt)

theorem hasDerivAt_oscillatoryTest {w : ℝ → ℝ} {w' ξ t : ℝ}
    (hw : HasDerivAt w w' t) :
    HasDerivAt (oscillatoryTest w ξ) (oscillatoryTestDeriv w (fun _ => w') ξ t) t := by
  have hp := (hasDerivAt_additivePhase (ξ * t)).scomp t (hasDerivAt_const_mul ξ)
  simpa only [oscillatoryTest, oscillatoryTestDeriv, Function.comp_def, Complex.real_smul,
    mul_comm (ξ : ℂ)] using! hw.ofReal_comp.mul hp

theorem oscillatoryTest_norm (w : ℝ → ℝ) (ξ t : ℝ) :
    ‖oscillatoryTest w ξ t‖ = |w t| := by
  simp only [oscillatoryTest, norm_mul, norm_additivePhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem oscillatoryTestDeriv_norm_le (w w' : ℝ → ℝ) (ξ t : ℝ) :
    ‖oscillatoryTestDeriv w w' ξ t‖ ≤ |w' t| + 2 * Real.pi * |ξ| * |w t| := by
  unfold oscillatoryTestDeriv
  calc
    _ ≤ ‖(w' t : ℂ) * additivePhase (ξ * t)‖ +
        ‖(w t : ℂ) * (additivePhase (ξ * t) * ((2 * Real.pi : ℝ) * Complex.I) * ξ)‖ :=
      norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, norm_additivePhase, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one, one_mul, abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem oscillatoryTestDeriv_continuousOn {w w' : ℝ → ℝ} {s : Set ℝ}
    (hw : ContinuousOn w s) (hw' : ContinuousOn w' s) (ξ : ℝ) :
    ContinuousOn (oscillatoryTestDeriv w w' ξ) s := by
  unfold oscillatoryTestDeriv
  have hp : ContinuousOn (fun t => additivePhase (ξ * t)) s :=
    (continuous_additivePhase.comp (continuous_const.mul continuous_id)).continuousOn
  exact ((Complex.continuous_ofReal.comp_continuousOn hw').mul hp).add
    ((Complex.continuous_ofReal.comp_continuousOn hw).mul ((hp.mul_const _).mul_const _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamanujanRoots
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive-root sums and the Ramanujan factor -/

namespace JointDickman

open Finset Polynomial
open scoped ArithmeticFunction.Moebius

theorem stdAddChar_natCast {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I * n / q) := by
  simpa only [Int.cast_natCast] using
    ZMod.stdAddChar_coe (N := q) (n : ℤ)

theorem stdAddChar_eq_primitive_power {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I / q) ^ n := by
  rw [stdAddChar_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

open Classical in
theorem nthRoots_image_stdAddChar (q : ℕ) [NeZero q] :
    nthRootsFinset q (1 : ℂ) = univ.image (ZMod.stdAddChar (N := q)) := by
  ext z
  rw [mem_nthRootsFinset (NeZero.pos q), mem_image]
  constructor
  · intro hz
    obtain ⟨i, _, hi⟩ := (Complex.isPrimitiveRoot_exp q (NeZero.ne q)).eq_pow_of_pow_eq_one hz
    exact ⟨(i : ZMod q), mem_univ _, (stdAddChar_eq_primitive_power i).trans hi⟩
  · rintro ⟨r, _, rfl⟩
    rw [← ZMod.natCast_zmod_val r, stdAddChar_eq_primitive_power, ← pow_mul,
      mul_comm r.val q, pow_mul, (Complex.isPrimitiveRoot_exp q (NeZero.ne q)).pow_eq_one,
      one_pow]

open Classical in
theorem sum_nthRoots_one (q : ℕ) (hq : 0 < q) :
    ∑ z ∈ nthRootsFinset q (1 : ℂ), z = if q = 1 then 1 else 0 := by
  let : NeZero q := ⟨hq.ne'⟩
  rw [nthRoots_image_stdAddChar, sum_image]
  · by_cases hq1 : q = 1
    · subst q
      simp only [Fintype.sum_unique, ite_true, if_true]
      convert! (ZMod.stdAddChar (N := 1)).map_zero_eq_one using 1
    · rw [ite_eq_right hq1]
      apply AddChar.sum_eq_zero_of_ne_one
      intro h
      have hh : ZMod.stdAddChar (1 : ZMod q) = ZMod.stdAddChar (0 : ZMod q) := by rw [h]; rfl
      have h10 := ZMod.injective_stdAddChar hh
      have hq2 : 1 < q := by omega
      let : Fact (1 < q) := ⟨hq2⟩
      exact one_ne_zero h10
  · exact fun _ _ _ _ h => ZMod.injective_stdAddChar h

open Classical in
theorem sum_primitiveRoots_eq_moebius (q : ℕ) (hq : 0 < q) :
    ∑ z ∈ primitiveRoots q ℂ, z = (μ q : ℂ) := by
  have hdiv : ∀ n > 0,
      ∑ d ∈ n.divisors, (∑ z ∈ primitiveRoots d ℂ, z) =
        (if n = 1 then (1 : ℂ) else 0) := by
    intro n hn
    rw [← sum_nthRoots_one n hn, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
      sum_biUnion]
    intro i _ j _ hij
    exact IsPrimitiveRoot.disjoint hij
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hdiv) q hq
  rw [sum_eq_single (q, 1)] at h
  · simpa using h.symm
  · rintro ⟨a, b⟩ hab hne
    by_cases hb : b = 1
    · have habq := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have ha : a = q := by simpa only [hb, mul_one] using habq
      exact False.elim (hne (Prod.ext ha hb))
    · simp [hb]
  · simp [Nat.mem_divisorsAntidiagonal, hq.ne']

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamanujanSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact unit-frequency Ramanujan sum -/

namespace JointDickman

open Finset
open scoped ArithmeticFunction.Moebius

open Classical in
theorem primitiveRoots_image_units (q : ℕ) [NeZero q] :
    primitiveRoots q ℂ = univ.image (fun r : (ZMod q)ˣ => ZMod.stdAddChar (r : ZMod q)) := by
  ext z
  rw [mem_primitiveRoots (NeZero.pos q), mem_image]
  constructor
  · intro hz
    obtain ⟨i, _, hic, hi⟩ := (Complex.isPrimitiveRoot_iff z q (NeZero.ne q)).mp hz
    refine ⟨ZMod.unitOfCoprime i hic, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, stdAddChar_natCast]
    calc
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((i : ℂ) / q)) := by congr 1; ring
      _ = z := hi
  · rintro ⟨r, _, rfl⟩
    have hc : (r : ZMod q).val.Coprime q := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [ZMod.natCast_zmod_val] using r.isUnit
    rw [← ZMod.natCast_zmod_val (r : ZMod q), stdAddChar_natCast]
    have he : 2 * (Real.pi : ℂ) * Complex.I * ((r : ZMod q).val : ℂ) / q =
        2 * (Real.pi : ℂ) * Complex.I * (((r : ZMod q).val : ℂ) / q) := by ring
    rw [he]
    exact Complex.isPrimitiveRoot_exp_of_coprime _ _ (NeZero.ne q) hc

open Classical in
theorem sum_stdAddChar_units (q : ℕ) [NeZero q] :
    ∑ r : (ZMod q)ˣ, ZMod.stdAddChar (r : ZMod q) = (μ q : ℂ) := by
  rw [← sum_primitiveRoots_eq_moebius q (NeZero.pos q), primitiveRoots_image_units,
    sum_image]
  exact fun _ _ _ _ h => Units.val_injective (ZMod.injective_stdAddChar h)

open Classical in
theorem ramanujan_sum_unit_frequency {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    ∑ r : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * (r : ZMod q)) = (μ q : ℂ) := by
  rw [← sum_stdAddChar_units q]
  simpa only [Units.val_mul] using
    Fintype.sum_bijective (fun r : (ZMod q)ˣ => u * r) (Equiv.mulLeft u).bijective
      (fun r : (ZMod q)ˣ => ZMod.stdAddChar ((u : ZMod q) * (r : ZMod q)))
      (fun r : (ZMod q)ˣ => ZMod.stdAddChar (r : ZMod q)) (fun _ => rfl)

theorem norm_stdAddChar {q : ℕ} [NeZero q] (r : ZMod q) :
    ‖ZMod.stdAddChar r‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle r).norm_coe

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditivePhaseBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relating real exponential notation to residue characters -/

namespace JointDickman

theorem additivePhase_add (s t : ℝ) :
    additivePhase (s + t) = additivePhase s * additivePhase t := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdAddChar_as_additivePhase {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = additivePhase ((n : ℝ) / q) := by
  rw [stdAddChar_natCast]
  unfold additivePhase
  congr 1
  push_cast
  ring

theorem unit_nat_phase {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) (n : ℕ) :
    ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) =
      additivePhase (((u : ZMod q).val : ℝ) * n / q) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val (u : ZMod q), ← Nat.cast_mul, stdAddChar_as_additivePhase]
  push_cast
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSetWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prime-selection and fair-split weights

The independent prime-set model and its fair splits satisfy exact finite
identities without prime asymptotics or analytic equidistribution premises.
-/

namespace JointDickman

open scoped BigOperators

theorem bernoulliSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    0 ≤ bernoulliSubsetMass P q S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p hp => (hq p (hS hp)).1)
  · exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hq p
      (Finset.mem_sdiff.mp hp).1).2)

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

theorem primeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    primeProductMass P z (∏ p ∈ S, p) =
      bernoulliSubsetMass P (fun p => z / p) S := by
  classical
  unfold primeProductMass
  rw [Finset.sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (Finset.mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (Finset.mem_powerset.mpr hS))

theorem primeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    primeProductMass P z n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq =>
    hn (Finset.mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing finite product laws

Replacing one independent coordinate at a time bounds the `L¹` distance
of two finite product probability laws by the sum of their coordinate
distances. Applied to the mutually exclusive prime-site law, this gives
the accumulated quadratic error for arbitrary bounded complex tests.
All identities and inequalities here are proved by finite sums.
-/

namespace JointDickman

open scoped BigOperators

theorem bernoulliSubsetMass_eq_product {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : P.powerset) :
    finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val)) (subsetHitEquiv P S) =
      bernoulliSubsetMass P q S.val := by
  classical
  have hp : finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val))
      (subsetHitEquiv P S) = ∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val := by
    unfold finiteProductMass
    apply Finset.prod_congr rfl
    intro i _
    simp [bernoulliBitMass, subsetHitEquiv]
  rw [hp, show (∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val) =
    ∏ i ∈ P, if i ∈ S.val then q i else 1 - q i from
      Finset.prod_coe_sort P (fun i => if i ∈ S.val then q i else 1 - q i), Finset.prod_ite]
  have hs : P.filter (fun i => i ∈ S.val) = S.val := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => Finset.mem_powerset.mp S.property hi)
  have hc : P.filter (fun i => i ∉ S.val) = P \ S.val := by
    ext i
    simp
  rw [hs, hc]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReciprocalTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative reciprocal-square tails

The error in the independent-product replacement is controlled by the tail
of all integers; no prime number theorem is needed here.
-/

namespace JointDickman

open Finset

theorem sum_reciprocal_square_tail (Q : Finset ℕ) {N : ℕ} (hN : N ≠ 0)
    (hQ : ∀ q ∈ Q, N < q) : (∑ q ∈ Q, 1 / (q : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let M := max N (Q.sup id)
  have hsub : Q ⊆ Ioc N M := by
    intro q hq
    exact mem_Ioc.mpr ⟨hQ q hq, (le_sup (f := id) hq).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑ q ∈ Ioc N M, 1 / (q : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
      simpa only [one_div] using (sum_Ioc_inv_sq_le_sub (α := ℝ) hN (le_max_left _ _))
    _ ≤ _ := sub_le_self _ (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogProductBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite logarithmic errors for prime-product normalizations

The quadratic logarithmic error is summable above the lower prime cutoff.
The inverse factors in the exact Bernoulli product mass are controlled
separately by a reciprocal sum over the selected primes.
-/

namespace JointDickman

open Finset

theorem log_one_sub_add_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hbase : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx, add_comm] using h
  have hden : 0 < 1 - x := by linarith
  apply hbase.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem finite_log_product_error {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    |Real.log (∏ i ∈ P, (1 - x i)) + ∑ i ∈ P, x i| ≤ 2 * ∑ i ∈ P, (x i) ^ 2 := by
  rw [Real.log_prod (fun i hi => by linarith [(hx i hi).2]), ← sum_add_distrib]
  calc
    _ ≤ ∑ i ∈ P, |Real.log (1 - x i) + x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, 2 * (x i) ^ 2 := sum_le_sum fun i hi =>
      log_one_sub_add_error (hx i hi).1 (hx i hi).2
    _ = _ := (mul_sum _ _ _).symm

/-- A selected-prime normalizer differs logarithmically from the linear
reciprocal-prime sum by at most the reciprocal-square tail. -/
theorem prime_log_product_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ P, N < p) :
    |Real.log (∏ p ∈ P, (1 - z / (p : ℝ))) + z * ∑ p ∈ P, 1 / (p : ℝ)| ≤
      2 * z ^ 2 / (N : ℝ) := by
  have hx (p : ℕ) (hp : p ∈ P) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have h := finite_log_product_error P (fun p => z / (p : ℝ)) hx
  have heq : (∑ p ∈ P, (z / (p : ℝ)) ^ 2) = z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    simp only [div_pow, mul_one_div]
  rw [heq] at h
  have hlin : (∑ p ∈ P, z / (p : ℝ)) = z * ∑ p ∈ P, 1 / (p : ℝ) := by
    simp only [mul_sum, mul_one_div]
  rw [hlin] at h
  calc
    _ ≤ 2 * (z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2) := h
    _ ≤ 2 * (z ^ 2 * (1 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (sq_nonneg z))
        (by norm_num)
    _ = _ := by ring

/-- The exact odds correction is bounded by an exponential of the
selected reciprocal mass, uniformly in the number of allowed primes. -/
theorem inverse_product_le_exp {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    (∏ i ∈ P, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ P, x i) := by
  have hpoint (i : ι) (hi : i ∈ P) : (1 - x i)⁻¹ ≤ Real.exp (2 * x i) := by
    have hpos : 0 < 1 - x i := by linarith [(hx i hi).2]
    have herr := log_one_sub_add_error (hx i hi).1 (hx i hi).2
    have hlog : Real.log ((1 - x i)⁻¹) ≤ 2 * x i := by
      rw [Real.log_inv]
      have hmul := mul_nonneg (hx i hi).1 (show 0 ≤ 1 - 2 * x i by linarith [(hx i hi).2])
      nlinarith [(abs_le.mp herr).1]
    calc
      _ = Real.exp (Real.log ((1 - x i)⁻¹)) := (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ ∏ i ∈ P, Real.exp (2 * x i) := Finset.prod_le_prod
      (fun i hi => inv_nonneg.mpr (by linarith [(hx i hi).2])) hpoint
    _ = Real.exp (∑ i ∈ P, 2 * x i) := (Real.exp_sum P (fun i => 2 * x i)).symm
    _ = _ := by rw [← mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact removal of the small prime factors

Removing a finite set of prime factors is an exact convolution identity.
The moving roughness cutoff is then controlled by Selberg–Delange estimates.
-/

namespace JointDickman

open ArithmeticFunction Finset

theorem squarefreeWeight_isMultiplicative (z : ℝ) :
    (squarefreeWeight z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨squarefreeWeight_one z, fun {m n} hm hn hmn => ?_⟩
  simp only [squarefreeWeight, coe_mk, Nat.squarefree_mul hmn,
    ite_zero_mul_ite_zero, cardFactors_mul hm hn, pow_add]

theorem smoothCorrection_isMultiplicative (E : Finset ℕ) (z : ℝ) :
    (smoothCorrection E z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨smoothCorrection_one E z, fun {m n} hm hn _ => ?_⟩
  simp only [smoothCorrection, coe_mk, hm, hn, mul_ne_zero hm hn,
    ↓reduceIte, Nat.primeFactors_mul hm hn, union_subset_iff,
    cardFactors_mul hm hn, pow_add, ite_zero_mul_ite_zero]

theorem roughSquarefreeWeight_isMultiplicative (E : Finset ℕ) (z : ℝ) :
    (roughSquarefreeWeight E z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨roughSquarefreeWeight_one E z, fun {m n} hm hn hmn => ?_⟩
  simp only [roughSquarefreeWeight, coe_mk, Nat.primeFactors_mul hm hn,
    disjoint_union_left, (squarefreeWeight_isMultiplicative z).2 hmn,
    ite_zero_mul_ite_zero]

theorem squarefreeWeight_prime_pow (z : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    squarefreeWeight z (p ^ k) = if k = 1 then z else 0 := by
  by_cases hk1 : k = 1
  · simp [hk1, squarefreeWeight, hp.squarefree, cardFactors_apply_prime hp]
  · have hsq : ¬Squarefree (p ^ k) := by
      rw [Nat.squarefree_pow_iff hp.ne_one hk]
      simp [hk1]
    simp [squarefreeWeight, hsq, hk1]

theorem smoothCorrection_prime_pow (E : Finset ℕ) (z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    smoothCorrection E z (p ^ k) = if p ∈ E then (-z) ^ k else 0 := by
  rw [smoothCorrection, coe_mk, ite_eq_right (pow_ne_zero k hp.ne_zero),
    Nat.primeFactors_pow p hk, hp.primeFactors]
  simp [cardFactors_apply_prime_pow hp]

theorem roughSquarefreeWeight_prime_pow (E : Finset ℕ) (z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    roughSquarefreeWeight E z (p ^ k) =
      if p ∈ E then 0 else if k = 1 then z else 0 := by
  simp [roughSquarefreeWeight, Nat.primeFactors_pow p hk, hp.primeFactors,
    squarefreeWeight_prime_pow z hp hk]

/-- Only the divisors `1` and `p` contribute from the squarefree weight. -/
theorem squarefreeWeight_convolution_prime_pow (z : ℝ) (h : ArithmeticFunction ℝ)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (squarefreeWeight z * h) (p ^ k) = h (p ^ k) + z * h (p ^ (k - 1)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => squarefreeWeight z a * h b),
    Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ']
  simp only [pow_zero, squarefreeWeight_one, one_mul, Nat.div_one]
  have hpdiv : p ^ k / p = p ^ (k - 1) := by
    have hh := Nat.pow_div (m := k) (n := 1) (by omega : 1 ≤ k) hp.pos
    simpa only [pow_one] using hh
  simp_rw [squarefreeWeight_prime_pow z hp (Nat.succ_ne_zero _)]
  simp [hk, hpdiv, add_comm]

/-- Removing finitely many Euler factors is exact at every integer. -/
theorem squarefreeWeight_mul_smoothCorrection (E : Finset ℕ) (z : ℝ) :
    squarefreeWeight z * smoothCorrection E z = roughSquarefreeWeight E z := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((squarefreeWeight_isMultiplicative z).mul (smoothCorrection_isMultiplicative E z))
    _ (roughSquarefreeWeight_isMultiplicative E z)).mpr
  intro p k hp
  by_cases hk : k = 0
  · simp [hk]
  rw [squarefreeWeight_convolution_prime_pow z _ hp hk,
    smoothCorrection_prime_pow E z hp hk, roughSquarefreeWeight_prime_pow E z hp hk]
  by_cases hpE : p ∈ E
  · simp only [hpE, ite_eq_left]
    by_cases hk1 : k = 1
    · simp [hk1]
    · rw [smoothCorrection_prime_pow E z hp (by omega)]
      simp only [hpE, ite_eq_left]
      have hpow : k = (k - 1) + 1 := by omega
      nth_rw 1 [hpow]
      rw [pow_succ]
      ring
  · simp only [hpE, ↓reduceIte, zero_add]
    by_cases hk1 : k = 1
    · simp [hk1]
    · rw [smoothCorrection_prime_pow E z hp (by omega)]
      simp [hpE, hk1]

/-- Exact finite summatory identity used before the analytic truncation. -/
theorem roughSquarefreeWeight_summatory (E : Finset ℕ) (z : ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, roughSquarefreeWeight E z n) =
      ∑ v ∈ Ioc 0 N, smoothCorrection E z v *
        ∑ m ∈ Ioc 0 (N / v), squarefreeWeight z m := by
  rw [← squarefreeWeight_mul_smoothCorrection, mul_comm]
  exact sum_Ioc_mul_eq_sum_sum _ _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

/-- Every smaller real power is negligible compared with a larger one. -/
theorem power_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => B ^ a / B ^ b) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [← Real.rpow_sub hB]
  congr 1
  ring

/-- In particular, each fixed polynomial degree below the cutoff exponent
is negligible compared with `P₀ = B^1000`. -/
theorem polynomial_div_primeCutoff_tendsto_zero {k : ℕ} (hk : k < 1000) :
    Tendsto (fun B : ℝ => B ^ k / B ^ (1000 : ℕ)) atTop (𝓝 0) := by
  have h : (k : ℝ) < (1000 : ℝ) := by exact_mod_cast hk
  have hlim := power_div_power_tendsto_zero h
  change Tendsto (fun B : ℝ => B ^ (k : ℝ) / B ^ ((1000 : ℕ) : ℝ))
    atTop (𝓝 0) at hlim
  simpa only [Real.rpow_natCast] using hlim

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal primes on fixed logarithmic intervals

Mertens' second theorem supplies the fixed-power interval limit. Together
with Chebyshev's estimate, it bounds the error in the marginal tuple count.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primesLE_eq_filter (N : ℕ) :
    Nat.primesLE N = (Icc 2 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.two_le, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

theorem largePrimeSet_eq_sdiff {N y : ℝ} (hy : 0 ≤ y) :
    largePrimeSet N y = Nat.primesLE ⌊N⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  apply Finset.ext
  intro p
  rw [Finset.mem_sdiff]
  simp only [largePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpy⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    rintro ⟨hpy', _⟩
    exact (not_le_of_gt hpy) ((Nat.le_floor_iff hy).mp hpy')
  · rintro ⟨⟨hpN, hp⟩, hnot⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    by_contra h
    exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩

theorem largePrimeSet_reciprocal_eq {N y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) :
    (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) = primeReciprocalSum N - primeReciprocalSum y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊N⌋₊ := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyN), hp⟩
  rw [largePrimeSet_eq_sdiff hy]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the independent prime-product law

The logarithm of the all-absent probability is its linear prime sum up to
a reciprocal-square error. Mertens' second theorem therefore determines
the normalization for a moving lower and upper cutoff.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Both endpoint Mertens remainders control the prime-interval remainder. -/
theorem prime_interval_mertens_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 2 ≤ X → X ≤ Y →
      |(∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) -
        (Real.log (Real.log Y) - Real.log (Real.log X))| ≤
        C / Real.log Y + C / Real.log X := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨C, hC, fun X Y hX hXY => ?_⟩
  have hY : 2 ≤ Y := hX.trans hXY
  have h₁ : |primeReciprocalSum X - Real.log (Real.log X) - M| ≤ C / Real.log X := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound X hX
  have h₂ : |primeReciprocalSum Y - Real.log (Real.log Y) - M| ≤ C / Real.log Y := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound Y hY
  rw [largePrimeSet_reciprocal_eq (by linarith) hXY]
  calc
    _ = |(primeReciprocalSum Y - Real.log (Real.log Y) - M) -
        (primeReciprocalSum X - Real.log (Real.log X) - M)| := by congr 1; ring
    _ ≤ |primeReciprocalSum Y - Real.log (Real.log Y) - M| +
        |primeReciprocalSum X - Real.log (Real.log X) - M| := abs_sub _ _
    _ ≤ _ := add_le_add h₂ h₁

/-- Uniform logarithmic normalizer error, retaining both endpoint errors. -/
theorem primeNormalizer_log_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (Y z : ℝ), 2 ≤ N → (N : ℝ) ≤ Y →
      0 ≤ z → z ≤ 1 →
      |Real.log (primeNormalizer (largePrimeSet Y N) z) +
        z * Real.log (Real.log Y / Real.log N)| ≤
        2 * z ^ 2 / (N : ℝ) + z * (C / Real.log Y + C / Real.log N) := by
  obtain ⟨C, hC, hinterval⟩ := prime_interval_mertens_error hM
  refine ⟨C, hC, fun N Y z hN hNY hz hz1 => ?_⟩
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hP : ∀ p ∈ largePrimeSet Y (N : ℝ), p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet Y (N : ℝ), N < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have h₁ := prime_log_product_error (largePrimeSet Y N) hP hz hz1
    (show N ≠ 0 by omega) hcut
  have h₂ := hinterval (N : ℝ) Y hNreal hNY
  have hlog : Real.log (Real.log Y / Real.log N) =
      Real.log (Real.log Y) - Real.log (Real.log N) :=
    Real.log_div hlogY.ne' hlogN.ne'
  let S := ∑ p ∈ largePrimeSet Y (N : ℝ), 1 / (p : ℝ)
  change |Real.log (primeNormalizer (largePrimeSet Y N) z) + z * Real.log (Real.log Y / Real.log N)| ≤ _
  calc
    _ = |(Real.log (primeNormalizer (largePrimeSet Y N) z) + z * S) +
        z * (Real.log (Real.log Y / Real.log N) - S)| := by congr 1; ring
    _ ≤ |Real.log (primeNormalizer (largePrimeSet Y N) z) + z * S| +
        |z * (Real.log (Real.log Y / Real.log N) - S)| := abs_add_le _ _
    _ ≤ 2 * z ^ 2 / (N : ℝ) + z * (C / Real.log Y + C / Real.log N) := by
      apply add_le_add h₁
      rw [abs_mul, abs_of_nonneg hz, abs_sub_comm, hlog]
      exact mul_le_mul_of_nonneg_left h₂ hz

/-- The all-absent product has the expected logarithmic normalization.
Only Mertens' reciprocal-prime input is used. -/
theorem primeNormalizer_normalized_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (N : ℕ → ℕ) (Y : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (hY : Tendsto Y atTop atTop) (hNY : ∀ᶠ B in atTop, (N B : ℝ) ≤ Y B)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => primeNormalizer (largePrimeSet (Y B) (N B)) z *
      (Real.log (Y B) / Real.log (N B)) ^ z) atTop (𝓝 1) := by
  obtain ⟨C, _, hbound⟩ := primeNormalizer_log_error hM
  have hNreal : Tendsto (fun B => (N B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hlim : Tendsto (fun B => 2 * z ^ 2 / (N B : ℝ) +
      z * (C / Real.log (Y B) + C / Real.log (N B))) atTop (𝓝 0) := by
    have h₁ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * z ^ 2) atTop (𝓝 (2 * z ^ 2))).div_atTop hNreal
    have h₂ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop
      (Real.tendsto_log_atTop.comp hY)
    have h₃ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop
      (Real.tendsto_log_atTop.comp hNreal)
    simpa using h₁.add ((h₂.add h₃).const_mul z)
  let E := fun B => Real.log (primeNormalizer (largePrimeSet (Y B) (N B)) z) +
    z * Real.log (Real.log (Y B) / Real.log (N B))
  have hE : Tendsto E atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [hN.eventually (eventually_ge_atTop 2), hNY] with B hNB hNYB
    simpa [E, Real.norm_eq_abs] using hbound (N B) (Y B) z hNB hNYB hz hz1
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hE
  have heq : (fun B => Real.exp (E B)) =ᶠ[atTop]
      (fun B => primeNormalizer (largePrimeSet (Y B) (N B)) z *
        (Real.log (Y B) / Real.log (N B)) ^ z) := by
    filter_upwards [hN.eventually (eventually_ge_atTop 2), hNY] with B hNB hNYB
    have hN2 : (2 : ℝ) ≤ N B := by exact_mod_cast hNB
    have hlogN : 0 < Real.log (N B) := Real.log_pos (by linarith)
    have hlogY : 0 < Real.log (Y B) := Real.log_pos (by linarith)
    have hprod : 0 < primeNormalizer (largePrimeSet (Y B) (N B)) z := by
      apply prod_pos
      intro p hp
      have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hfrac : z / (p : ℝ) < 1 := (div_lt_one hp0).mpr (by linarith)
      linarith
    dsimp [E]
    rw [Real.exp_add, Real.exp_log hprod,
      Real.rpow_def_of_pos (div_pos hlogY hlogN)]
    congr 1
    congr 1
    ring
  simpa using hexp.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeMassApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the local odds correction from prime-product masses

For every event, the independent-subset mass differs from the uncorrected
Euler weight by at most the sum of squared selection probabilities.
The resulting prime-tail error is uniform over events.
-/

namespace JointDickman

open Finset

theorem uncorrectedSubsetMass_identity {P S : Finset ℕ} (q : ℕ → ℝ) (hS : S ⊆ P) :
    uncorrectedSubsetMass P q S = bernoulliSubsetMass P q S * ∏ p ∈ S, (1 - q p) := by
  unfold uncorrectedSubsetMass bernoulliSubsetMass
  rw [← prod_sdiff hS (f := fun p => 1 - q p)]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeHarmonicWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact harmonic weights of squarefree prime products

The uncorrected independent-prime mass is the harmonic rough coefficient,
including the empty product. This identifies the weight used in partial summation.
-/

namespace JointDickman

open Finset ArithmeticFunction

theorem primeProduct_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
  · exact fun p hp => (hS p hp).squarefree

theorem primeProduct_cardFactors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    cardFactors (∏ p ∈ S, p) = S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hpprime := hS p (mem_insert_self p S)
      have hrest : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
      rw [prod_insert hp, cardFactors_mul hpprime.ne_zero
        (prod_ne_zero_iff.mpr (fun q hq => (hrest q hq).ne_zero)),
        cardFactors_apply_prime hpprime, ih hrest, card_insert_of_notMem hp]
      omega

theorem uncorrectedSubsetMass_harmonic {P S E : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (hE : Disjoint S E) :
    uncorrectedSubsetMass P (fun p => z / p) S =
      primeNormalizer P z * roughSquarefreeWeight E z (∏ p ∈ S, p) / (∏ p ∈ S, p : ℕ) := by
  have hSP : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hrough : roughSquarefreeWeight E z (∏ p ∈ S, p) = z ^ S.card := by
    simp only [roughSquarefreeWeight, ArithmeticFunction.coe_mk, Nat.primeFactors_prod hSP,
      hE, ite_eq_left, squarefreeWeight, primeProduct_squarefree S hSP,
      primeProduct_cardFactors S hSP]
  rw [hrough]
  simp only [uncorrectedSubsetMass, primeNormalizer, prod_div_distrib, prod_const, Nat.cast_prod]
  ring

theorem uncorrectedPrimeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    uncorrectedPrimeProductMass P z (∏ p ∈ S, p) = uncorrectedSubsetMass P (fun p => z / p) S := by
  classical
  unfold uncorrectedPrimeProductMass
  rw [sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (mem_powerset.mpr hS))

theorem uncorrectedPrimeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    uncorrectedPrimeProductMass P z n = 0 := by
  classical
  apply sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq => hn (mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

theorem uncorrectedPrimeProductMass_harmonic {U : ℝ} {N n : ℕ}
    (hnU : (n : ℝ) ≤ U) (z : ℝ) :
    uncorrectedPrimeProductMass (largePrimeSet U N) z n =
      primeNormalizer (largePrimeSet U N) z * roughSquarefreeWeight (Nat.primesLE N) z n / n := by
  classical
  let P := largePrimeSet U N
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  by_cases hn : n ∈ P.powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hn
    have hS : S ⊆ P := mem_powerset.mp hSP
    have hd : Disjoint S (Nat.primesLE N) := by
      apply disjoint_left.mpr
      intro p hp hsmall
      have hgt : (N : ℝ) < p := (mem_filter.mp (hS hp)).2
      have hle : p ≤ N := (Nat.mem_primesLE.mp hsmall).1
      exact (not_lt_of_ge (by exact_mod_cast hle)) hgt
    rw [← hSn, uncorrectedPrimeProductMass_at_product z hP hS]
    exact uncorrectedSubsetMass_harmonic z hP hS hd
  · rw [uncorrectedPrimeProductMass_eq_zero z n hn]
    by_cases hd : Disjoint n.primeFactors (Nat.primesLE N)
    · by_cases hsq : Squarefree n
      · have hsub : n.primeFactors ⊆ P := by
          intro p hp
          have hpprime := Nat.prime_of_mem_primeFactors hp
          have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
          have hpU : (p : ℝ) ≤ U := (by exact_mod_cast hpn : (p : ℝ) ≤ n).trans hnU
          have hpN : N < p := by
            by_contra hnot
            exact disjoint_left.mp hd hp (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
          exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpU, hpprime⟩, by exact_mod_cast hpN⟩
        exact False.elim (hn (mem_image.mpr ⟨n.primeFactors, mem_powerset.mpr hsub,
          Nat.prod_primeFactors_of_squarefree hsq⟩))
      · simp [roughSquarefreeWeight, hd, squarefreeWeight, hsq]
    · simp [roughSquarefreeWeight, hd]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SelectedPrimeOdds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform odds corrections on bounded prime products -/

namespace JointDickman

open Finset

theorem selectedPrime_card_log_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (S.card : ℝ) * Real.log 2 ≤ Real.log (∏ p ∈ S, p : ℕ) := by
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).ne_zero)]
  calc
    _ = ∑ _p ∈ S, Real.log 2 := by simp
    _ ≤ _ := sum_le_sum (fun p hp => Real.log_le_log (by norm_num)
      (by exact_mod_cast (hS p hp).two_le))

theorem inverseSelectedPrimeOdds_le {P z : ℝ} (hP : 0 < P)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hcut : ∀ p ∈ S, P ≤ p) :
    (∏ p ∈ S, (1 - z / (p : ℝ))⁻¹) ≤ Real.exp (2 * (S.card : ℝ) / P) := by
  have hx (p : ℕ) (hp : p ∈ S) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have hsum : (∑ p ∈ S, z / (p : ℝ)) ≤ (S.card : ℝ) / P := by
    calc
      _ ≤ ∑ _p ∈ S, 1 / P := sum_le_sum (fun p hp => by
        have hp0 : (0 : ℝ) < p := hP.trans_le (hcut p hp)
        exact (div_le_div_of_nonneg_right hz1 hp0.le).trans
          (one_div_le_one_div_of_le hP (hcut p hp)))
      _ = _ := by simp [div_eq_mul_inv]
  exact (inverse_product_le_exp S (fun p => z / (p : ℝ)) hx).trans
    (Real.exp_le_exp.mpr (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)))

theorem bernoulliSubsetMass_eq_uncorrected_odds {P S : Finset ℕ} (q : ℕ → ℝ)
    (hS : S ⊆ P) (hq : ∀ p ∈ S, 1 - q p ≠ 0) :
    bernoulliSubsetMass P q S =
      uncorrectedSubsetMass P q S * ∏ p ∈ S, (1 - q p)⁻¹ := by
  rw [uncorrectedSubsetMass_identity q hS, prod_inv_distrib, mul_assoc,
    mul_inv_cancel₀ (prod_ne_zero_iff.mpr hq), mul_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RpowTaylor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform power expansion for removing roughness

Taylor expansion is made on the fixed compact interval `[0, 1/2]`.
Its coefficients are independent of the expansion order and of the
moving logarithmic scale.
-/

namespace JointDickman

open Finset Set

theorem rpowShift_contDiff (a : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun t : ℝ => (1 - t) ^ a) (Icc 0 (1 / 2)) := by
  apply ContDiffOn.rpow_const_of_ne
  · exact contDiffOn_const.sub contDiffOn_id
  · intro t ht
    linarith [ht.2]

theorem rpowShift_taylor_eval (a t : ℝ) (H : ℕ) :
    taylorWithinEval (fun u : ℝ => (1 - u) ^ a) H (Icc 0 (1 / 2)) 0 t =
      ∑ k ∈ range (H + 1), rpowShiftCoeff a k * t ^ k := by
  rw [taylor_within_apply]
  apply sum_congr rfl
  intro k _
  simp only [sub_zero, smul_eq_mul, rpowShiftCoeff]
  ring

theorem rpowShift_remainder (a : ℝ) (H : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
      |(1 - t) ^ a - ∑ k ∈ range (H + 1), rpowShiftCoeff a k * t ^ k| ≤
        C * t ^ (H + 1) := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (rpowShift_contDiff a (H + 1))
  refine ⟨max C 0, le_max_right _ _, fun t ht ht1 => ?_⟩
  have h := hC t ⟨ht, ht1⟩
  rw [Real.norm_eq_abs, rpowShift_taylor_eval, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ht _))

theorem rpowShift_scaled_term (a L v : ℝ) (k : ℕ) (hL : 0 < L) :
    L ^ a * (rpowShiftCoeff a k * (v / L) ^ k) =
      rpowShiftCoeff a k * v ^ k * L ^ (a - k) := by
  rw [Real.rpow_sub hL, Real.rpow_natCast, div_pow]
  ring

/-- The power expansion with an error uniform throughout `0 ≤ v ≤ L/2`.
The exponent `a` is arbitrary; the application uses `a = z - 1 - j`. -/
theorem rpow_scaled_remainder (a : ℝ) (H : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L v : ℝ, 0 < L → 0 ≤ v → v ≤ L / 2 →
      |(L - v) ^ a - ∑ k ∈ range (H + 1),
        rpowShiftCoeff a k * v ^ k * L ^ (a - k)| ≤
          C * L ^ (a - (H + 1)) * v ^ (H + 1) := by
  obtain ⟨C, hC, hbound⟩ := rpowShift_remainder a H
  refine ⟨C, hC, fun L v hL hv hvL => ?_⟩
  have ht : 0 ≤ v / L := div_nonneg hv hL.le
  have ht1 : v / L ≤ 1 / 2 := (div_le_iff₀ hL).mpr (by linarith)
  have hfactor : (L - v) ^ a = L ^ a * (1 - v / L) ^ a := by
    rw [← Real.mul_rpow hL.le (by linarith : 0 ≤ 1 - v / L)]
    congr 1
    field_simp
  have hsum : (∑ k ∈ range (H + 1), rpowShiftCoeff a k * v ^ k * L ^ (a - k)) =
      L ^ a * ∑ k ∈ range (H + 1), rpowShiftCoeff a k * (v / L) ^ k := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    exact (rpowShift_scaled_term a L v k hL).symm
  rw [hfactor, hsum, ← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg hL.le a)]
  calc
    _ ≤ L ^ a * (C * (v / L) ^ (H + 1)) :=
      mul_le_mul_of_nonneg_left (hbound _ ht ht1) (Real.rpow_nonneg hL.le a)
    _ = _ := by
      rw [Real.rpow_sub hL,
        show (H : ℝ) + 1 = ((H + 1 : ℕ) : ℝ) by norm_cast,
        Real.rpow_natCast, div_pow]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript's auxiliary prime scale

The lower cutoff is `B^1000`, the upper cutoff is `exp (4 B)`, and
`R = B / log (B^1000)`. The normalizing constant below is derived from
the published reciprocal-prime Mertens estimate.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

theorem auxiliaryCutoff_tendsto : Tendsto auxiliaryCutoff atTop atTop :=
  tendsto_pow_atTop (by norm_num : (1000 : ℕ) ≠ 0)

theorem auxiliaryUpper_tendsto : Tendsto auxiliaryUpper atTop atTop :=
  Real.tendsto_exp_atTop.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4))

theorem auxiliaryCutoff_le_upper :
    ∀ᶠ B in atTop, (auxiliaryCutoff B : ℝ) ≤ auxiliaryUpper B := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 1000 (by norm_num : (0 : ℝ) < 4)).def
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with B hB
  have hpow : (0 : ℝ) ≤ (B : ℝ) ^ 1000 := pow_nonneg (Nat.cast_nonneg B) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpow,
    abs_of_pos (Real.exp_pos _), one_mul, auxiliaryCutoff, auxiliaryUpper,
    Nat.cast_pow] using hB

theorem auxiliaryRatio_pos {B : ℕ} (hB : 1 < B) : 0 < auxiliaryRatio B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  exact div_pos (by linarith) (mul_pos (by norm_num) (Real.log_pos hBreal))

theorem auxiliaryRatio_tendsto : Tendsto auxiliaryRatio atTop atTop := by
  have hlim : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ)))
      atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul 1000
  have hpos : ∀ᶠ B : ℕ in atTop, 0 < 1000 * (Real.log B / (B : ℝ)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
    exact mul_pos (by norm_num) (div_pos (Real.log_pos hBreal) (by linarith))
  have hgt : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ)))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hlim, hpos⟩
  convert hgt.inv_tendsto_nhdsGT_zero using 1
  all_goals try with_reducible_and_instances rfl
  ext B
  simp only [auxiliaryRatio, Pi.inv_apply, mul_inv_rev, inv_div]
  ring

theorem auxiliary_log_ratio (B : ℕ) :
    Real.log (auxiliaryUpper B) / Real.log (auxiliaryCutoff B) =
      4 * auxiliaryRatio B := by
  simp only [auxiliaryUpper, Real.log_exp, auxiliaryCutoff, Nat.cast_pow,
    Real.log_pow, auxiliaryRatio]
  ring

/-- The paper's `Q_{z,B} ~ (4 R)^{-z}` in normalized-limit form. -/
theorem auxiliary_primeNormalizer_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => primeNormalizer (auxiliaryPrimes B) z *
      auxiliaryRatio B ^ z) atTop (𝓝 ((4 : ℝ) ^ (-z))) := by
  have h := primeNormalizer_normalized_tendsto hM auxiliaryCutoff auxiliaryUpper
    auxiliaryCutoff_tendsto auxiliaryUpper_tendsto auxiliaryCutoff_le_upper hz hz1
  simp_rw [auxiliary_log_ratio] at h
  have hdiv := h.div_const ((4 : ℝ) ^ z)
  have heq : (fun B => primeNormalizer (largePrimeSet (auxiliaryUpper B)
      (auxiliaryCutoff B)) z * (4 * auxiliaryRatio B) ^ z / (4 : ℝ) ^ z)
      =ᶠ[atTop] (fun B => primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (auxiliaryRatio_pos hB).le]
    change _ = primeNormalizer (largePrimeSet (auxiliaryUpper B) (auxiliaryCutoff B)) z * _
    have hfour : (4 : ℝ) ^ z ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) z).ne'
    field_simp
  simpa [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] using hdiv.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ConvolutionTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite truncation estimates for roughness removal

The large-divisor part of the convolution is bounded before invoking any
Selberg–Delange input. The bound needs only the elementary `|g_z| ≤ 1`.
-/

namespace JointDickman

open Finset

theorem squarefreeWeight_abs_le_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    |squarefreeWeight z n| ≤ 1 := by
  unfold squarefreeWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs
  · rw [abs_of_nonneg (pow_nonneg hz _)]
    exact pow_le_one₀ hz hz1
  · norm_num

theorem squarefreeWeight_sum_abs_le {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (N : ℕ) :
    |∑ n ∈ Ioc 0 N, squarefreeWeight z n| ≤ N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, |squarefreeWeight z n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) := sum_le_sum fun n _ => squarefreeWeight_abs_le_one hz hz1 n
    _ = _ := by simp

theorem roughConvolutionTail_abs_le (E : Finset ℕ) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (N V : ℕ) :
    |roughConvolutionTail E z N V| ≤
      (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) := by
  unfold roughConvolutionTail
  calc
    _ ≤ ∑ v ∈ Ioc V N, |smoothCorrection E z v *
        ∑ m ∈ Ioc 0 (N / v), squarefreeWeight z m| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ Ioc V N, (N : ℝ) * (|smoothCorrection E z v| / v) := by
      apply sum_le_sum
      intro v hv
      have hvpos : 0 < v := (mem_Ioc.mp hv).1.trans_le' (Nat.zero_le V)
      have hvpos' : (0 : ℝ) < v := by exact_mod_cast hvpos
      have hfloor : ((N / v : ℕ) : ℝ) ≤ (N : ℝ) / v := by
        apply (le_div_iff₀ hvpos').mpr
        exact_mod_cast Nat.div_mul_le_self N v
      rw [abs_mul]
      calc
        _ ≤ |smoothCorrection E z v| * ((N / v : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (squarefreeWeight_sum_abs_le hz hz1 _) (abs_nonneg _)
        _ ≤ |smoothCorrection E z v| * ((N : ℝ) / v) :=
          mul_le_mul_of_nonneg_left hfloor (abs_nonneg _)
        _ = _ := by ring
    _ = _ := (mul_sum _ _ _).symm

/-- The elementary Rankin inequality for the harmonic tail. -/
theorem harmonic_tail_rankin {ι : Type*} (s : Finset ι) (v a : ι → ℝ)
    {V ε : ℝ} (hV : 0 < V) (hε : 0 ≤ ε)
    (hv : ∀ i ∈ s, V ≤ v i) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i / v i) ≤
      (∑ i ∈ s, a i / (v i) ^ (1 - ε)) / V ^ ε := by
  have hVpow : 0 < V ^ ε := Real.rpow_pos_of_pos hV _
  apply (le_div_iff₀ hVpow).mpr
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hvi : 0 < v i := hV.trans_le (hv i hi)
  have hpow : V ^ ε ≤ (v i) ^ ε := Real.rpow_le_rpow hV.le (hv i hi) hε
  calc
    a i / v i * V ^ ε ≤ a i / v i * (v i) ^ ε :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg (ha i hi) hvi.le)
    _ = a i / (v i) ^ (1 - ε) := by
      rw [Real.rpow_sub hvi, Real.rpow_one]
      field_simp

/-- Quantitative large-divisor truncation in terms of one weighted moment
of the correction coefficients. -/
theorem roughConvolutionTail_rankin (E : Finset ℕ) {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 ≤ ε) (N V : ℕ) (hV : 0 < V) :
    |roughConvolutionTail E z N V| ≤
      ((N : ℝ) / (V : ℝ) ^ ε) *
        ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) ^ (1 - ε) := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have h := harmonic_tail_rankin (Ioc V N) (fun v : ℕ => (v : ℝ))
    (fun v => |smoothCorrection E z v|) hV' hε
    (fun v hv => by exact_mod_cast (mem_Ioc.mp hv).1.le)
    (fun _ _ => abs_nonneg _)
  calc
    _ ≤ (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) :=
      roughConvolutionTail_abs_le E hz hz1 N V
    _ ≤ (N : ℝ) * ((∑ v ∈ Ioc V N, |smoothCorrection E z v| /
        (v : ℝ) ^ (1 - ε)) / (V : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothCorrectionSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The convergent correction series

The finite Euler factors used in removing the small primes are proved
as identities of absolutely convergent series, including at the shifted
exponent required by Rankin's bound.
-/

namespace JointDickman

open Finset

theorem smoothDirichletTerm_mul (E : Finset ℕ) (z s : ℝ) {m n : ℕ}
    (hmn : m.Coprime n) :
    smoothDirichletTerm E z s (m * n) =
      smoothDirichletTerm E z s m * smoothDirichletTerm E z s n := by
  simp only [smoothDirichletTerm, (smoothCorrection_isMultiplicative E z).map_mul_of_coprime hmn,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem smoothDirichletTerm_prime_pow (E : Finset ℕ) (z s : ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    smoothDirichletTerm E z s (p ^ k) =
      (if p ∈ E then -z / (p : ℝ) ^ s else 0) ^ k := by
  by_cases hk : k = 0
  · simp [hk]
  simp only [smoothDirichletTerm, smoothCorrection_prime_pow E z hp hk, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) s,
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  split_ifs <;> simp [div_pow, hk]

theorem smoothDirichletTerm_ratio_lt_one (E : Finset ℕ) {z s : ℝ}
    (hz : |z| < 1) (hs : 0 ≤ s) {p : ℕ} (hp : p.Prime) :
    ‖(if p ∈ E then -z / (p : ℝ) ^ s else 0)‖ < 1 := by
  by_cases hpE : p ∈ E
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ s := Real.one_le_rpow hp1 hs
    simp only [hpE, ite_eq_left, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (Real.rpow_pos_of_pos hp0 s)]
    exact (div_lt_one (Real.rpow_pos_of_pos hp0 s)).mpr (hz.trans_le hpow)
  · simp [hpE]

theorem smoothDirichletTerm_support (E : Finset ℕ) (z s : ℝ) :
    Function.support (smoothDirichletTerm E z s) ⊆ Nat.factoredNumbers E := by
  intro n hn
  rw [Function.mem_support] at hn
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp [smoothDirichletTerm] at hn
  refine ⟨hn0, ?_⟩
  by_contra h
  simp [smoothDirichletTerm, smoothCorrection, hn0, h] at hn

/-- Absolute convergence and the signed Euler-factor identity. -/
theorem smoothCorrection_hasSum (E : Finset ℕ) {z s : ℝ}
    (hz : |z| < 1) (hs : 0 ≤ s) :
    Summable (fun n => ‖smoothDirichletTerm E z s n‖) ∧
      HasSum (smoothDirichletTerm E z s)
        (∏ p ∈ E with p.Prime, (1 + z / (p : ℝ) ^ s)⁻¹) := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k => ‖smoothDirichletTerm E z s (p ^ k)‖) := by
    intro p hp
    simp_rw [smoothDirichletTerm_prime_pow E z s hp]
    exact summable_norm_geometric_of_norm_lt_one
      (smoothDirichletTerm_ratio_lt_one E hz hs hp)
  obtain ⟨hnorm, hsum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      (smoothDirichletTerm_one E z s) (smoothDirichletTerm_mul E z s) hlocal E
  have hsupport := smoothDirichletTerm_support E z s
  have habs_support : Function.support (fun n => ‖smoothDirichletTerm E z s n‖) ⊆
      Nat.factoredNumbers E := by
    intro n hn
    apply hsupport
    simpa only [Function.mem_support, norm_ne_zero_iff] using hn
  refine ⟨((hasSum_subtype_iff_of_support_subset habs_support).mp hnorm.hasSum).summable, ?_⟩
  apply (hasSum_subtype_iff_of_support_subset hsupport).mp
  convert hsum using 1
  all_goals try rfl
  apply prod_congr rfl
  intro p hp
  obtain ⟨_, hprime⟩ := mem_filter.mp hp
  simp_rw [smoothDirichletTerm_prime_pow E z s hprime]
  rw [(hasSum_geometric_of_norm_lt_one
    (smoothDirichletTerm_ratio_lt_one E hz hs hprime)).tsum_eq]
  simp [mem_of_mem_filter p hp, sub_eq_add_neg, neg_div]

/-- The zeroth correction moment is the inverse of the removed local factors. -/
theorem smoothCorrection_zeroth_moment (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun n => smoothCorrection E z n / (n : ℝ))
      (∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹) := by
  have h := (smoothCorrection_hasSum E hz (by norm_num : (0 : ℝ) ≤ 1)).2
  have hf : smoothDirichletTerm E z 1 = fun n => smoothCorrection E z n / (n : ℝ) := by
    funext n
    simp [smoothDirichletTerm]
  rw [hf] at h
  simpa using h

theorem smoothDirichletTerm_abs (E : Finset ℕ) {z : ℝ} (hz : 0 ≤ z)
    (s : ℝ) (n : ℕ) :
    |smoothDirichletTerm E z s n| = smoothDirichletTerm E (-z) s n := by
  simp only [smoothDirichletTerm, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s),
    smoothCorrection, ArithmeticFunction.coe_mk]
  split_ifs <;> simp [abs_pow, abs_neg, abs_of_nonneg hz]

/-- The absolute correction moment is a finite product of positive geometric factors. -/
theorem smoothCorrection_abs_hasSum (E : Finset ℕ) {z s : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hs : 0 ≤ s) :
    HasSum (fun n => |smoothCorrection E z n| / (n : ℝ) ^ s)
      (∏ p ∈ E with p.Prime, (1 - z / (p : ℝ) ^ s)⁻¹) := by
  have hz' : |-z| < 1 := by simpa [abs_of_nonneg hz] using hz1
  have h := (smoothCorrection_hasSum E hz' hs).2
  have hf : smoothDirichletTerm E (-z) s =
      fun n => |smoothCorrection E z n| / (n : ℝ) ^ s := by
    funext n
    rw [← smoothDirichletTerm_abs E hz]
    simp [smoothDirichletTerm, abs_div,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
  rw [hf] at h
  simpa [neg_div, sub_eq_add_neg] using h

/-- An exponential bound for every finite truncation of the absolute series. -/
theorem smoothCorrection_abs_sum_le_exp (E S : Finset ℕ) {z s : ℝ}
    (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (hs : 0 ≤ s) :
    (∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) ^ s) ≤
      Real.exp (2 * z * ∑ p ∈ E with p.Prime, 1 / (p : ℝ) ^ s) := by
  have hsum := smoothCorrection_abs_hasSum E hz (by linarith) hs
  calc
    _ ≤ ∏ p ∈ E with p.Prime, (1 - z / (p : ℝ) ^ s)⁻¹ := by
      rw [← hsum.tsum_eq]
      exact hsum.summable.sum_le_tsum S (fun n _ =>
        div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) s))
    _ ≤ Real.exp (2 * ∑ p ∈ E with p.Prime, z / (p : ℝ) ^ s) := by
      apply inverse_product_le_exp
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_lt.le
      have hpow := Real.one_le_rpow hp1 hs
      refine ⟨div_nonneg hz (by positivity), ?_⟩
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by
      congr 1
      simp only [div_eq_mul_inv, one_mul, ← mul_sum]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMomentBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the moving roughness correction

The exponent shift `1 / log P` costs only a fixed power of `log P`.
This supplies the moment in Rankin's argument from Mertens' estimate,
rather than assuming a cutoff-dependent bound.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem shifted_reciprocal_le {p P : ℝ} (hp : 0 < p) (hpP : p ≤ P)
    (hlog : 0 < Real.log P) :
    1 / p ^ (1 - 1 / Real.log P) ≤ Real.exp 1 / p := by
  have hpow : p ^ (1 / Real.log P) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hp]
    apply Real.exp_le_exp.mpr
    have hle : Real.log p ≤ Real.log P := Real.log_le_log hp hpP
    simpa only [mul_one_div] using (div_le_one hlog).mpr hle
  rw [Real.rpow_sub hp, Real.rpow_one]
  simpa only [one_div_div] using div_le_div_of_nonneg_right hpow hp.le

theorem shifted_prime_sum_le (P : ℕ) (hlog : 0 < Real.log P) :
    (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P)) ≤
      Real.exp 1 * primeReciprocalSum P := by
  simp only [primeReciprocalSum, Nat.floor_natCast, mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpP, hprime⟩ := Nat.mem_primesLE.mp hp
  simpa only [mul_one_div] using shifted_reciprocal_le
    (by exact_mod_cast hprime.pos) (by exact_mod_cast hpP) hlog

/-- Mertens controls the shifted absolute correction moment by a fixed
power of the logarithm, uniformly over all finite truncations. -/
theorem smoothCorrection_shifted_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (S : Finset ℕ) (z : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      (∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| /
        (n : ℝ) ^ (1 - 1 / Real.log P)) ≤
        A * (Real.log P) ^ (Real.exp 1) := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨Real.exp (Real.exp 1 * (|M| + C)), Real.exp_pos _, ?_⟩
  intro P S z hP hlog hz hzhalf
  have hlogpos : 0 < Real.log P := by linarith
  have hshift : 0 ≤ 1 - 1 / Real.log P := by
    have h := (div_le_one hlogpos).mpr hlog
    linarith
  have hMertens : primeReciprocalSum P ≤ Real.log (Real.log P) + |M| + C := by
    have h := (abs_le.mp (hbound P (by exact_mod_cast hP))).2
    have hCdiv : C / Real.log P ≤ C := (div_le_iff₀ hlogpos).mpr (by nlinarith)
    have hMabs := le_abs_self M
    simp only [← primesLE_eq_filter] at h
    change primeReciprocalSum P - Real.log (Real.log P) - M ≤ C / Real.log P at h
    linarith
  have hprime : (Nat.primesLE P).filter Nat.Prime = Nat.primesLE P :=
    filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  calc
    _ ≤ Real.exp (2 * z * ∑ p ∈ Nat.primesLE P,
        1 / (p : ℝ) ^ (1 - 1 / Real.log P)) := by
      simpa only [hprime] using smoothCorrection_abs_sum_le_exp
        (Nat.primesLE P) S hz hzhalf hshift
    _ ≤ Real.exp (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P)) := by
      apply Real.exp_le_exp.mpr
      have hsum : 0 ≤ ∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P) :=
        sum_nonneg (fun p _ => by positivity)
      nlinarith
    _ ≤ Real.exp (Real.exp 1 * primeReciprocalSum P) :=
      Real.exp_le_exp.mpr (shifted_prime_sum_le P hlogpos)
    _ ≤ Real.exp (Real.exp 1 * (Real.log (Real.log P) + |M| + C)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hMertens (Real.exp_pos _).le)
    _ = _ := by
      rw [show Real.exp 1 * (Real.log (Real.log P) + |M| + C) =
        Real.exp 1 * (|M| + C) + Real.log (Real.log P) * Real.exp 1 by ring,
        Real.exp_add, ← Real.rpow_def_of_pos hlogpos]

/-- The same constant controls the actual large-divisor convolution error. -/
theorem roughConvolutionTail_shifted_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P N V : ℕ) (z : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 ≤ z → z ≤ 1 / 2 →
      |roughConvolutionTail (Nat.primesLE P) z N V| ≤
        (N : ℝ) / (V : ℝ) ^ (1 / Real.log P) *
          (A * (Real.log P) ^ (Real.exp 1)) := by
  obtain ⟨A, hA, hmoment⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P N V z hP hlog hV hz hzhalf => ?_⟩
  have hlogpos : 0 < Real.log P := by linarith
  exact (roughConvolutionTail_rankin (Nat.primesLE P) hz (by linarith)
    (by positivity) N V hV).trans
      (mul_le_mul_of_nonneg_left (hmoment P (Ioc V N) z hP hlog hz hzhalf)
        (by positivity))

theorem log_pow_le_rpow (k : ℕ) {v ε : ℝ} (hv : 1 ≤ v) (hε : 0 < ε) :
    (Real.log v) ^ k ≤ ((k.factorial : ℝ) / ε ^ k) * v ^ ε := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h := (div_le_iff₀ hfact).mp
    (Real.pow_div_factorial_le_exp (ε * Real.log v) (mul_nonneg hε.le (Real.log_nonneg hv)) k)
  have hexp : Real.exp (ε * Real.log v) = v ^ ε := by
    rw [Real.rpow_def_of_pos hv0, mul_comm]
  rw [mul_pow, hexp] at h
  calc
    (Real.log v) ^ k ≤ (v ^ ε * (k.factorial : ℝ)) / ε ^ k :=
      (le_div_iff₀ (pow_pos hε k)).mpr (by nlinarith [h])
    _ = _ := by ring

/-- Exponential tilting controls every logarithmic correction moment. -/
theorem smoothCorrection_log_moment_le (E S : Finset ℕ) (k : ℕ)
    (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) * (Real.log n) ^ k) ≤
      ((k.factorial : ℝ) / ε ^ k) *
        ∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) ^ (1 - ε) := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  calc
    _ ≤ (|smoothCorrection E z n| / (n : ℝ)) *
        (((k.factorial : ℝ) / ε ^ k) * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (log_pow_le_rpow k hn1 hε) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]
      field_simp

/-- The absolute constant in the roughness bound works for every fixed
moment order; only the factorial and extra logarithmic power change. -/
theorem smoothCorrection_log_moments_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (S : Finset ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      (∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| / (n : ℝ) *
        (Real.log n) ^ k) ≤
        A * (k.factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + k) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P S z k hP hlog hz hzhalf => ?_⟩
  have hlogpos : 0 < Real.log P := by linarith
  calc
    _ ≤ ((k.factorial : ℝ) / (1 / Real.log P) ^ k) *
        ∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| /
          (n : ℝ) ^ (1 - 1 / Real.log P) :=
      smoothCorrection_log_moment_le _ _ k z (by positivity)
    _ ≤ ((k.factorial : ℝ) / (1 / Real.log P) ^ k) *
        (A * (Real.log P) ^ (Real.exp 1)) :=
      mul_le_mul_of_nonneg_left (hbound P S z hP hlog hz hzhalf) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlogpos, Real.rpow_natCast]
      simp only [one_div, inv_pow, div_inv_eq_mul]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CorrectionMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coefficients' actual logarithmic moments

These are absolutely convergent series of the smooth correction.
The bounds are uniform in the moving cutoff and every fixed moment order.
-/

namespace JointDickman

open Finset

theorem correctionLogTerm_norm (E : Finset ℕ) (z : ℝ) (k n : ℕ) :
    ‖correctionLogTerm E z k n‖ =
      |smoothCorrection E z n| / (n : ℝ) * (Real.log n) ^ k := by
  rw [correctionLogTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)]

theorem correctionLogTerm_summable (E : Finset ℕ) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (k : ℕ) :
    Summable (fun n => ‖correctionLogTerm E z k n‖) := by
  have hbase := (smoothCorrection_abs_hasSum E hz hz1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).summable
  have hdom : Summable (fun n => ((k.factorial : ℝ) / (1 / 2 : ℝ) ^ k) *
      (|smoothCorrection E z n| / (n : ℝ) ^ (1 - (1 / 2 : ℝ)))) := by
    simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      hbase.mul_left ((k.factorial : ℝ) / (1 / 2 : ℝ) ^ k)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hdom
  intro n
  rw [correctionLogTerm_norm]
  simpa using smoothCorrection_log_moment_le E {n} k z (by norm_num : (0 : ℝ) < 1 / 2)

theorem correctionLogMoment_zero (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    correctionLogMoment E z 0 =
      ∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹ := by
  simpa [correctionLogMoment, correctionLogTerm] using
    (smoothCorrection_zeroth_moment E hz).tsum_eq

/-- The fixed-order coefficient moments are bounded with one absolute
logarithmic exponent. -/
theorem correctionLogMoment_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      |correctionLogMoment (Nat.primesLE P) z k| ≤
        A * (k.factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + k) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_log_moments_bound hM
  refine ⟨A, hA, fun P z k hP hlog hz hzhalf => ?_⟩
  have hsum := correctionLogTerm_summable (Nat.primesLE P) hz (by linarith) k
  have hnorm := hsum.tsum_le_of_sum_le (fun S => by
    simpa only [correctionLogTerm_norm] using hbound P S z k hP hlog hz hzhalf)
  calc
    _ = ‖∑' n, correctionLogTerm (Nat.primesLE P) z k n‖ := by
      rw [Real.norm_eq_abs, correctionLogMoment]
    _ ≤ ∑' n, ‖correctionLogTerm (Nat.primesLE P) z k n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ _ := hnorm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients after removal of the small prime factors

Each coefficient is a finite combination of the published fixed-order
Selberg–Delange coefficients and the actual correction moments. The
definition has no dependence on a subsequently chosen truncation order.
-/

namespace JointDickman

open Finset

theorem roughCoefficient_zero (c : ℕ → ℝ) (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    roughCoefficient c E z 0 = c 0 *
      ∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹ := by
  simp [roughCoefficient, correctionLogMoment_zero E hz]

/-- Grouping the Taylor terms by their total degree gives the actual
rough coefficients, with no discarded cross terms. -/
theorem roughCoefficient_expansion (c : ℕ → ℝ) (E : Finset ℕ)
    (z L : ℝ) (H : ℕ) :
    (∑ ν ∈ range (H + 1), roughCoefficient c E z ν * L ^ (z - 1 - ν)) =
      ∑ j ∈ range (H + 1), c j *
        ∑ k ∈ range (H - j + 1), rpowShiftCoeff (z - 1 - j) k *
          correctionLogMoment E z k * L ^ (z - 1 - j - k) := by
  let f := fun j k : ℕ => c j * rpowShiftCoeff (z - 1 - j) k *
    correctionLogMoment E z k * L ^ (z - 1 - j - k)
  calc
    _ = ∑ ν ∈ range (H + 1), ∑ j ∈ range (ν + 1), f j (ν - j) := by
      apply sum_congr rfl
      intro ν _
      rw [roughCoefficient, sum_mul]
      apply sum_congr rfl
      intro j hj
      have hjν : j ≤ ν := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      dsimp [f]
      rw [Nat.cast_sub hjν]
      congr 1
      congr 1
      ring
    _ = ∑ j ∈ range (H + 1), ∑ k ∈ range (H + 1 - j), f j k :=
      sum_range_diag_flip (H + 1) f
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjH : j ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      rw [show H + 1 - j = H - j + 1 by omega, mul_sum]
      apply sum_congr rfl
      intro k _
      dsimp [f]
      ring

/-- Uniform coefficient bound with the absolute exponent supplied by
the correction moment estimate. -/
theorem roughCoefficient_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (c : ℕ → ℝ)
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (ν : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, 2 ≤ P → 1 ≤ Real.log P →
      |roughCoefficient c (Nat.primesLE P) z ν| ≤
        C * (Real.log P) ^ (Real.exp 1 + ν) := by
  obtain ⟨A, hA, hmom⟩ := correctionLogMoment_bound hM
  let C := ∑ j ∈ range (ν + 1),
    |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| * A * ((ν - j).factorial : ℝ)
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => by positivity)
  refine ⟨C, hC, fun P hP hlog => ?_⟩
  unfold roughCoefficient
  calc
    _ ≤ ∑ j ∈ range (ν + 1),
        |c j * rpowShiftCoeff (z - 1 - j) (ν - j) *
          correctionLogMoment (Nat.primesLE P) z (ν - j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (ν + 1),
        (|c j * rpowShiftCoeff (z - 1 - j) (ν - j)| * A * ((ν - j).factorial : ℝ)) *
          (Real.log P) ^ (Real.exp 1 + ν) := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      have hpow : (Real.log P) ^ (Real.exp 1 + (ν - j : ℕ)) ≤
          (Real.log P) ^ (Real.exp 1 + ν) := by
        apply Real.rpow_le_rpow_of_exponent_le hlog
        have hsub : ((ν - j : ℕ) : ℝ) ≤ ν := by exact_mod_cast Nat.sub_le ν j
        linarith
      calc
        _ ≤ |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| *
            (A * ((ν - j).factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + (ν - j : ℕ))) :=
          mul_le_mul_of_nonneg_left (hmom P z (ν - j) hP hlog hz hzhalf) (abs_nonneg _)
        _ ≤ |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| *
            (A * ((ν - j).factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + ν)) := by
          gcongr
        _ = _ := by ring
    _ = _ := by rw [← sum_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of the squarefree Selberg–Delange Euler factor

Cancellation of the linear local logarithms proves absolute convergence.
This identifies the same Euler product used in the published leading
coefficient, without assuming its convergence as another input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem log_one_add_sub_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-x| < 1 by rw [abs_neg, abs_of_nonneg hx]; linarith) 1
  have hbase : |Real.log (1 + x) - x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_neg, abs_of_nonneg hx, sub_neg_eq_add, sub_eq_add_neg, add_comm] using h
  apply hbase.trans
  apply (div_le_iff₀ (show 0 < 1 - x by linarith)).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem squarefreeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) {p : ℕ} (hp : p.Prime) :
    0 < squarefreeEulerFactor z p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply mul_pos
  · have h := div_nonneg hz hp0.le
    linarith
  · apply Real.rpow_pos_of_pos
    have h := (div_lt_one hp0).mpr hp1
    linarith

theorem squarefreeEulerFactor_log_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {p : ℕ} (hp : p.Prime) :
    |Real.log (squarefreeEulerFactor z p)| ≤ 4 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsub : 0 < 1 - 1 / (p : ℝ) := by
    have h := (div_lt_one hp0).mpr hp1
    linarith
  have hadd : 0 < 1 + z / (p : ℝ) := by positivity
  have hfrac : z / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hrec : 1 / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have h₁ := log_one_add_sub_error (div_nonneg hz hp0.le) hfrac
  have h₂ := log_one_sub_add_error (by positivity : (0 : ℝ) ≤ 1 / p) hrec
  have heq : Real.log (squarefreeEulerFactor z p) =
      (Real.log (1 + z / (p : ℝ)) - z / p) + z *
        (Real.log (1 - 1 / (p : ℝ)) + 1 / p) := by
    rw [squarefreeEulerFactor, Real.log_mul hadd.ne' (Real.rpow_pos_of_pos hsub z).ne',
      Real.log_rpow hsub]
    ring
  rw [heq]
  calc
    _ ≤ |Real.log (1 + z / (p : ℝ)) - z / p| +
        |z * (Real.log (1 - 1 / (p : ℝ)) + 1 / p)| := abs_add_le _ _
    _ ≤ 2 * (z / (p : ℝ)) ^ 2 + z * (2 * (1 / (p : ℝ)) ^ 2) := by
      rw [abs_mul, abs_of_nonneg hz]
      exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hz)
    _ ≤ 4 / (p : ℝ) ^ 2 := by
      have hzsq : z ^ 2 ≤ 1 := by nlinarith
      field_simp
      nlinarith

theorem primeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 < primeEulerFactor z n := by
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn] using squarefreeEulerFactor_pos hz hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_log_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun n => Real.log (primeEulerFactor z n)) := by
  have hsum := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 4
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsum
  intro n
  rw [Real.norm_eq_abs]
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn, mul_one_div] using squarefreeEulerFactor_log_bound hz hz1 hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_multipliable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Multipliable (primeEulerFactor z) :=
  Real.multipliable_of_summable_log (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)

theorem squarefreeEulerProduct_pos {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < ∏' n : ℕ, primeEulerFactor z n := by
  rw [← Real.rexp_tsum_eq_tprod (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)]
  exact Real.exp_pos _

theorem squarefreeEulerProduct_eq (z : ℝ) :
    (∏' n : ℕ, primeEulerFactor z n) =
      ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p := by
  calc
    _ = ∏' n : ℕ, ({p : ℕ | p.Prime}.mulIndicator (squarefreeEulerFactor z)) n := by
      apply tprod_congr
      intro n
      by_cases hn : n.Prime <;> simp [primeEulerFactor, Set.mulIndicator, hn]
    _ = _ := (tprod_subtype {p : ℕ | p.Prime} (squarefreeEulerFactor z)).symm

theorem squarefreeEulerProduct_partial (z : ℝ) (N : ℕ) :
    (∏ n ∈ range (N + 1), primeEulerFactor z n) =
      ∏ p ∈ Nat.primesLE N, squarefreeEulerFactor z p := by
  have hset : (range (N + 1)).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter, mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
  simp only [primeEulerFactor]
  rw [← prod_filter, hset]

theorem squarefreeEulerProduct_partial_tendsto {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun N => ∏ p ∈ Nat.primesLE N, squarefreeEulerFactor z p)
      atTop (𝓝 (∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p)) := by
  have h := (primeEulerFactor_multipliable hz hz1).tendsto_prod_tprod_nat.comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, squarefreeEulerProduct_partial, squarefreeEulerProduct_eq] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughLeadingCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The leading coefficient after the roughness cutoff

Mertens' product theorem and the convergent squarefree Euler factor give
the precise constant `exp(-γ z) / Gamma(z)`.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughLeadingCoefficient_identity {z : ℝ} (hz : 0 ≤ z) (P : ℕ) :
    roughLeadingCoefficient z P * (Real.log P) ^ z =
      (squarefreeLeadingConstant z / ∏ p ∈ Nat.primesLE P, squarefreeEulerFactor z p) *
        (Real.log P * ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) ^ z := by
  let S := Nat.primesLE P
  have hlocal (p : ℕ) (hp : p ∈ S) : 0 < 1 - 1 / (p : ℝ) := by
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    have hh := (div_lt_one hp0).mpr hp1
    linarith
  have hU : 0 < ∏ p ∈ S, (1 - 1 / (p : ℝ)) := prod_pos hlocal
  have hA : 0 < ∏ p ∈ S, (1 + z / (p : ℝ)) := by
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    have hh := div_nonneg hz hp0.le
    linarith
  have hF : (∏ p ∈ S, squarefreeEulerFactor z p) =
      (∏ p ∈ S, (1 + z / (p : ℝ))) * (∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ z := by
    simp only [squarefreeEulerFactor, prod_mul_distrib]
    rw [Real.finsetProd_rpow S _ (fun p hp => (hlocal p hp).le)]
  change (squarefreeLeadingConstant z * ∏ p ∈ S, (1 + z / (p : ℝ))⁻¹) *
    (Real.log P) ^ z = (squarefreeLeadingConstant z / ∏ p ∈ S, squarefreeEulerFactor z p) *
      (Real.log P * ∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ z
  rw [hF, Real.mul_rpow (Real.log_natCast_nonneg P) hU.le, prod_inv_distrib]
  have hUz := (Real.rpow_pos_of_pos hU z).ne'
  field_simp [hA.ne', hUz]

/-- Only the cited Mertens product input is used in this normalization. -/
theorem roughLeadingCoefficient_tendsto
    (hM : PublishedInputs.PrimeProductMertensInput) {z : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) :
    Tendsto (fun P => roughLeadingCoefficient z P * (Real.log P) ^ z) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) := by
  let G := ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p
  have hG : 0 < G := by
    dsimp only [G]
    rw [← squarefreeEulerProduct_eq]
    exact squarefreeEulerProduct_pos hz.le hz1
  have hprod : Tendsto (fun P : ℕ => Real.log P *
      ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa only [← primesLE_eq_filter, Function.comp_def, Nat.floor_natCast] using
      hM.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => squarefreeLeadingConstant z) atTop
      (𝓝 (squarefreeLeadingConstant z))).div
        (squarefreeEulerProduct_partial_tendsto hz.le hz1) hG.ne').mul
          (hprod.rpow_const (Or.inr hz.le))
  have hconstant : squarefreeLeadingConstant z / G *
      Real.exp (-Real.eulerMascheroniConstant) ^ z =
        Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z := by
    change (G / Real.Gamma z) / G * _ = _
    rw [← Real.exp_mul]
    field_simp [hG.ne', (Real.Gamma_pos_of_pos hz).ne']
  rw [hconstant] at h
  exact h.congr' (Eventually.of_forall (fun P => (roughLeadingCoefficient_identity hz.le P).symm))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ScaledRoughCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients in the limiting prime-product density

The zeroth normalized coefficient has the stated limit, and every fixed
higher coefficient vanishes. No residue-distribution assertion is assumed.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primeNormalizer_bounds (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ primeNormalizer E z ∧ primeNormalizer E z ≤ 1 := by
  have hlocal (p : ℕ) (hp : p ∈ E) : 0 ≤ 1 - z / (p : ℝ) ∧ 1 - z / (p : ℝ) ≤ 1 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hE p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hE p hp).one_le
    have hdiv : z / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr (hz1.trans hp1)
    constructor
    · linarith
    · linarith [div_nonneg hz hp0.le]
  exact ⟨prod_nonneg (fun p hp => (hlocal p hp).1),
    Finset.prod_le_one (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2)⟩

theorem roughCoefficient_zero_eq_leading (c : ℕ → ℝ) {z : ℝ}
    (hc : c 0 = squarefreeLeadingConstant z) (hz : |z| < 1) (P : ℕ) :
    roughCoefficient c (Nat.primesLE P) z 0 = roughLeadingCoefficient z P := by
  rw [roughCoefficient_zero c _ hz, hc]
  have hp : (Nat.primesLE P).filter Nat.Prime = Nat.primesLE P :=
    filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  simp only [roughLeadingCoefficient, hp]

theorem auxiliaryRatio_mul_log {B : ℕ} (hB : 1 < B) :
    auxiliaryRatio B * Real.log (auxiliaryCutoff B) = B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hlog : Real.log B ≠ 0 := (Real.log_pos hBreal).ne'
  simp only [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  norm_num
  field_simp

theorem scaledRoughCoefficient_zero_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hz1 : z < 1) :
    Tendsto (fun B => scaledRoughCoefficient c z 0 B) atTop
      (𝓝 ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z))) := by
  have hlead := (roughLeadingCoefficient_tendsto hMP hz hz1.le).comp auxiliaryCutoff_tendsto
  have h := (auxiliary_primeNormalizer_tendsto hM hz.le hz1.le).mul hlead
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hR : 0 ≤ auxiliaryRatio B := (auxiliaryRatio_pos hB).le
  have hlog : 0 ≤ Real.log (auxiliaryCutoff B) := Real.log_natCast_nonneg _
  have hpow : (auxiliaryRatio B) ^ z * (Real.log (auxiliaryCutoff B)) ^ z = (B : ℝ) ^ z := by
    rw [← Real.mul_rpow hR hlog, auxiliaryRatio_mul_log hB]
  unfold scaledRoughCoefficient
  rw [Nat.cast_zero, sub_zero,
    roughCoefficient_zero_eq_leading c hc (by rwa [abs_of_pos hz])]
  dsimp only [Function.comp_def]
  rw [mul_mul_mul_comm, hpow]

theorem scaledRoughCoefficient_succ_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (j : ℕ) :
    Tendsto (fun B => scaledRoughCoefficient c z (j + 1) B) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := roughCoefficient_bound hM c hz hzhalf (j + 1)
  let a : ℝ := (j + 1 : ℕ) - z
  let r : ℝ := Real.exp 1 + (j + 1 : ℕ)
  have ha : 0 < a := by dsimp [a]; push_cast <;> linarith [Nat.cast_nonneg j (α := ℝ)]
  have hlimit := ((log_power_div_power_tendsto_zero r ha).const_mul
    (C * (1000 : ℝ) ^ r)).comp tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlimit
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlimit
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlogP : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hP, hlogP, eventually_gt_atTop 1] with B hp hlog hB
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hQ := primeNormalizer_bounds _ (auxiliaryPrimes_prime B) hz (by linarith : z ≤ 1)
  have hb := hbound (auxiliaryCutoff B) hp hlog
  rw [Real.norm_eq_abs, scaledRoughCoefficient, abs_mul, abs_mul,
    abs_of_nonneg hQ.1, abs_of_pos (Real.rpow_pos_of_pos hB0 _)]
  calc
    _ ≤ 1 * (C * (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (j + 1 : ℕ))) *
        (B : ℝ) ^ (z - (j + 1 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hQ.2 hb (abs_nonneg _) (by norm_num)) (Real.rpow_nonneg hB0.le _)
    _ = C * (1000 : ℝ) ^ r * ((Real.log B) ^ r / (B : ℝ) ^ a) := by
      have hcut : Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
        simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow] <;> norm_num
      rw [one_mul, hcut, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_pos hBreal).le]
      have hexp : z - (j + 1 : ℕ) = -a := by dsimp [a] <;> ring
      rw [hexp, Real.rpow_neg hB0.le]
      dsimp [r]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform convergence of the prime-product density

Finite combinations of the actual rough coefficients converge uniformly
away from zero. This is the smooth density used for the coarse channel.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem scaledRoughDensity_eq (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    scaledRoughDensity c z H B s =
      B * primeNormalizer (auxiliaryPrimes B) z *
        roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (B * s) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  unfold scaledRoughDensity roughDensityPolynomial
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j _
  unfold scaledRoughCoefficient
  have hfirst : (B : ℝ) ^ (z - j) = B * (B : ℝ) ^ (z - 1 - j) := by
    rw [show z - (j : ℝ) = 1 + (z - 1 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  have hsecond : (B : ℝ) ^ (z - 1 - j) = B * (B : ℝ) ^ (z - 2 - j) := by
    rw [show z - 1 - (j : ℝ) = 1 + (z - 2 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  rw [Real.mul_rpow hB0.le hs.le, Real.mul_rpow hB0.le hs.le, hfirst]
  have hBn : (B : ℝ) ≠ 0 := hB0.ne'
  field_simp
  rw [hsecond]
  ring

/-- A coefficient limit gives a uniform limit for a fixed negative power. -/
theorem scalar_power_uniform {a δ c : ℝ} {u : ℕ → ℝ}
    (ha : a ≤ 0) (hδ : 0 < δ) (hu : Tendsto u atTop (𝓝 c)) :
    TendstoUniformlyOn (fun (B : ℕ) (s : ℝ) => u B * s ^ a)
      (fun s => c * s ^ a) atTop (Set.Ici δ) := by
  have hnorm : Tendsto (fun n : ℕ => |u n - c| * δ ^ a) atTop (𝓝 0) := by
    simpa using ((hu.sub_const c).abs.mul_const (δ ^ a))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall := hnorm.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with B hB
  intro s hs
  have hs0 : 0 < s := hδ.trans_le hs
  have hp := Real.rpow_le_rpow_of_nonpos hδ hs ha
  calc
    dist (c * s ^ a) (u B * s ^ a) = |u B - c| * s ^ a := by
      rw [Real.dist_eq, ← sub_mul, abs_mul, abs_sub_comm,
        abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    _ ≤ |u B - c| * δ ^ a := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ < ε := hB

/-- Finite fixed powers preserve uniform convergence of their coefficients. -/
theorem finite_power_uniform (S : Finset ℕ) (a c : ℕ → ℝ) (u : ℕ → ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (ha : ∀ j ∈ S, a j ≤ 0)
    (hu : ∀ j ∈ S, Tendsto (fun B => u B j) atTop (𝓝 (c j))) :
    TendstoUniformlyOn (fun B s => ∑ j ∈ S, u B j * s ^ a j)
      (fun s => ∑ j ∈ S, c j * s ^ a j) atTop (Set.Ici δ) := by
  induction S using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const (Set.Ici δ)
  | @insert i S hi ih =>
      have hfirst := scalar_power_uniform (ha i (mem_insert_self i S)) hδ (hu i (mem_insert_self i S))
      have hrest := ih (fun j hj => ha j (mem_insert_of_mem hj))
        (fun j hj => hu j (mem_insert_of_mem hj))
      convert hfirst.add hrest using 1 <;> first | (with_reducible_and_instances rfl) | (ext <;> simp [sum_insert hi])

/-- The density converges uniformly on every interval bounded away from zero.
The stronger half-line statement is available because all exponents are negative. -/
theorem scaledRoughDensity_tendstoUniformlyOn
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    TendstoUniformlyOn (fun B s => scaledRoughDensity c z H B s)
      (fun s => ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) * s ^ (z - 1))
      atTop (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hfirst := finite_power_uniform (range (H + 1)) (fun j => z - 1 - j) b
    (fun B j => scaledRoughCoefficient c z j B) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => hcoef j)
  have hsecond := finite_power_uniform (range (H + 1)) (fun j => z - 2 - j) (fun _ => 0)
    (fun B j => scaledRoughCoefficient c z j B / B * (z - 1 - j)) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => by
      simpa using ((hcoef j).div_atTop tendsto_natCast_atTop_atTop).mul_const (z - 1 - j))
  convert hfirst.add hsecond using 1
  · rfl
  · funext s
    simp [b, k]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Derivatives of the density used in partial summation

The finite model is differentiated directly, and its first derivative
converges uniformly away from zero along with the density itself.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem hasDerivAt_scaledRoughDensity (c : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (scaledRoughDensity c z H B) (scaledRoughDensityDeriv c z H B s) s := by
  have hfirst : ∀ j ∈ range (H + 1),
      HasDerivAt (fun t => scaledRoughCoefficient c z j B * t ^ (z - 1 - j))
        ((scaledRoughCoefficient c z j B * (z - 1 - j)) * s ^ (z - 2 - j)) s := by
    intro j _
    convert (Real.hasDerivAt_rpow_const (p := z - 1 - j) (Or.inl hs.ne')).const_mul
      (scaledRoughCoefficient c z j B) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show z - 1 - (j : ℝ) - 1 = z - 2 - j by ring]
    ring
  have hsecond : ∀ j ∈ range (H + 1),
      HasDerivAt (fun t => (scaledRoughCoefficient c z j B / B * (z - 1 - j)) * t ^ (z - 2 - j))
        ((scaledRoughCoefficient c z j B / B * (z - 1 - j) * (z - 2 - j)) * s ^ (z - 3 - j)) s := by
    intro j _
    convert (Real.hasDerivAt_rpow_const (p := z - 2 - j) (Or.inl hs.ne')).const_mul
      (scaledRoughCoefficient c z j B / B * (z - 1 - j)) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show z - 2 - (j : ℝ) - 1 = z - 3 - j by ring]
    ring
  exact (HasDerivAt.fun_sum hfirst).add (HasDerivAt.fun_sum hsecond)

theorem hasDerivAt_logarithmic_model (c : ℕ → ℝ) (E : Finset ℕ) (z : ℝ) (H : ℕ)
    {Y : ℝ} (hY : 1 < Y) :
    HasDerivAt (fun X => X * ∑ j ∈ range (H + 1),
      roughCoefficient c E z j * (Real.log X) ^ (z - 1 - j))
      (roughDensityPolynomial c E z H (Real.log Y)) Y := by
  have hY0 : 0 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hterm : ∀ j ∈ range (H + 1),
      HasDerivAt (fun X => X * (roughCoefficient c E z j * (Real.log X) ^ (z - 1 - j)))
        (roughCoefficient c E z j * ((Real.log Y) ^ (z - 1 - j) +
          (z - 1 - j) * (Real.log Y) ^ (z - 2 - j))) Y := by
    intro j _
    have hp := (Real.hasDerivAt_rpow_const (p := z - 1 - j) (Or.inl hlog.ne')).comp Y
      (Real.hasDerivAt_log hY0.ne')
    refine ((hasDerivAt_id Y).mul (hp.const_mul (roughCoefficient c E z j))).congr_deriv (Eq.symm ?_)
    · dsimp only [Function.comp_def, id_eq]
      rw [show z - 1 - (j : ℝ) - 1 = z - 2 - j by ring]
      field_simp
  refine ((HasDerivAt.fun_sum hterm).congr_of_eventuallyEq (Filter.Eventually.of_forall fun X => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    rw [mul_sum]
  · rfl

theorem scaledRoughDensityDeriv_tendstoUniformlyOn
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    TendstoUniformlyOn (fun B s => scaledRoughDensityDeriv c z H B s)
      (fun s => ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) *
          (z - 1) * s ^ (z - 2)) atTop (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hfirst := finite_power_uniform (range (H + 1)) (fun j => z - 2 - j)
    (fun j => b j * (z - 1 - j)) (fun B j => scaledRoughCoefficient c z j B * (z - 1 - j))
    hδ (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)])
    (fun j _ => (hcoef j).mul_const _)
  have hsecond := finite_power_uniform (range (H + 1)) (fun j => z - 3 - j) (fun _ => 0)
    (fun B j => scaledRoughCoefficient c z j B / B * (z - 1 - j) * (z - 2 - j)) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => by
      simpa using (((hcoef j).div_atTop tendsto_natCast_atTop_atTop).mul_const
        (z - 1 - j)).mul_const (z - 2 - j))
  convert hfirst.add hsecond using 1
  · rfl
  · funext s
    simp [b, k]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughSelbergDelange
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published expansion inside the roughness convolution

The expansion is inserted only below the truncation, where its endpoint
and logarithmic hypotheses hold. The complementary terms remain the
actual convolution tail, already controlled by Rankin's bound.
-/

namespace JointDickman

open Finset

/-- The usual square-root truncation meets both local expansion conditions. -/
theorem square_root_truncation_conditions {Y : ℝ} {V : ℕ}
    (hY : 9 ≤ Y) (hV : (V : ℝ) ^ 2 ≤ Y) :
    V ≤ ⌊Y⌋₊ ∧ ∀ v ∈ Ioc 0 V,
      3 ≤ Y / (v : ℝ) ∧ Real.log Y / 2 ≤ Real.log (Y / (v : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  refine ⟨Nat.le_floor (by nlinarith), fun v hv => ?_⟩
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  have hvV : (v : ℝ) ≤ V := by exact_mod_cast (mem_Ioc.mp hv).2
  have hv2 : (v : ℝ) ^ 2 ≤ Y := by nlinarith
  constructor
  · apply (le_div_iff₀ hv0).mpr
    nlinarith
  · have hlog := Real.log_le_log (sq_pos_of_pos hv0) hv2
    rw [Real.log_pow] at hlog
    rw [Real.log_div hY0.ne' hv0.ne']
    norm_num at hlog
    linarith

theorem roughSquarefreeSummatory_split (E : Finset ℕ) (z Y : ℝ)
    (V : ℕ) (hV : V ≤ ⌊Y⌋₊) :
    roughSquarefreeSummatory E z Y =
      (∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) +
        roughConvolutionTail E z ⌊Y⌋₊ V := by
  unfold roughSquarefreeSummatory
  rw [roughSquarefreeWeight_summatory,
    ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le V) hV, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1
  apply sum_congr rfl
  intro v _
  simp only [squarefreeSummatory, Nat.floor_div_natCast]

theorem smallConvolution_SD_error (E : Finset ℕ) (c : ℕ → ℝ)
    (z Y : ℝ) (H V : ℕ) {C : ℝ} (hC : 0 ≤ C) (hY : 1 < Y)
    (hz : z ≤ 1)
    (hSD : ∀ X : ℝ, 3 ≤ X →
      |squarefreeSummatory z X - X * sdPolynomial c z H (Real.log X)| ≤
        C * X * (Real.log X) ^ (z - 2 - H))
    (hsize : ∀ v ∈ Ioc 0 V, 3 ≤ Y / (v : ℝ))
    (hlog : ∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / (v : ℝ))) :
    |(∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
      Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        sdPolynomial c z H (Real.log (Y / v))| ≤
      C * Y * (Real.log Y / 2) ^ (z - 2 - H) *
        ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) := by
  have hlogpos : 0 < Real.log Y / 2 := div_pos (Real.log_pos hY) (by norm_num)
  have hexp : z - 2 - (H : ℝ) ≤ 0 := by linarith [Nat.cast_nonneg H (α := ℝ)]
  have heq : (∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
      Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        sdPolynomial c z H (Real.log (Y / v)) =
      ∑ v ∈ Ioc 0 V, smoothCorrection E z v *
        (squarefreeSummatory z (Y / v) -
          (Y / v) * sdPolynomial c z H (Real.log (Y / v))) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro v _
    ring
  rw [heq, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro v hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  have hpow := Real.rpow_le_rpow_of_nonpos hlogpos (hlog v hv) hexp
  rw [abs_mul]
  calc
    _ ≤ |smoothCorrection E z v| *
        (C * (Y / v) * (Real.log (Y / v)) ^ (z - 2 - H)) :=
      mul_le_mul_of_nonneg_left (hSD _ (hsize v hv)) (abs_nonneg _)
    _ ≤ |smoothCorrection E z v| *
        (C * (Y / v) * (Real.log Y / 2) ^ (z - 2 - H)) := by
      gcongr
    _ = _ := by ring

/-- Direct consequence of the published fixed-order expansion, with an
explicit remaining tail and no assumed moving-cutoff estimate. -/
theorem roughSelbergDelange_truncated
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Finset ℕ) (Y : ℝ) (V : ℕ),
        1 < Y → V ≤ ⌊Y⌋₊ →
        (∀ v ∈ Ioc 0 V, 3 ≤ Y / (v : ℝ)) →
        (∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / (v : ℝ))) →
        |roughSquarefreeSummatory E z Y -
          Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
            sdPolynomial c z H (Real.log (Y / v))| ≤
          C * Y * (Real.log Y / 2) ^ (z - 2 - H) *
            (∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ)) +
              |roughConvolutionTail E z ⌊Y⌋₊ V| := by
  obtain ⟨c, hc0, hcpos, horders⟩ := hSD z hz
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨C, hC, hbound⟩ := horders H
  refine ⟨C, hC, fun E Y V hY hV hsize hlog => ?_⟩
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have hsmall := smallConvolution_SD_error E c z Y H V hC hY hz1 hbound hsize hlog
  rw [roughSquarefreeSummatory_split E z Y V hV]
  calc
    _ = |((∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
        Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
          sdPolynomial c z H (Real.log (Y / v))) +
            roughConvolutionTail E z ⌊Y⌋₊ V| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hsmall (le_refl _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact character-twisted roughness convolution -/

namespace JointDickman

open Finset ArithmeticFunction

theorem characterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) :
    characterTwist χ (f * g) = characterTwist χ f * characterTwist χ g := by
  ext n
  simp only [characterTwist_apply, mul_apply, Complex.ofReal_sum]
  rw [sum_mul]
  apply sum_congr rfl
  intro ab hab
  have hmul : ab.1 * ab.2 = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [← hmul, Nat.cast_mul, map_mul, Complex.ofReal_mul]
  ring

theorem roughCharacterSum_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    (E : Finset ℕ) (z Y : ℝ) (V : ℕ) (hV : V ≤ ⌊Y⌋₊) :
    roughCharacterSum χ E z Y =
      (∑ v ∈ Ioc 0 V, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
        squarefreeCharacterSum χ z (Y / v)) +
      characterConvolutionTail χ E z ⌊Y⌋₊ V := by
  have hconv := congrArg (characterTwist χ) (squarefreeWeight_mul_smoothCorrection E z)
  rw [characterTwist_mul, mul_comm] at hconv
  change (∑ n ∈ Ioc 0 ⌊Y⌋₊, characterTwist χ (roughSquarefreeWeight E z) n) = _
  rw [← hconv, sum_Ioc_mul_eq_sum_sum,
    ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le V) hV, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1
  · apply sum_congr rfl
    intro v _
    simp only [characterTwist_apply, squarefreeCharacterSum, Nat.floor_div_natCast]
  · simp only [characterConvolutionTail, squarefreeCharacterSum, Nat.floor_natCast,
      characterTwist_apply]

theorem squarefreeCharacterSum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (N : ℕ) :
    ‖squarefreeCharacterSum χ z N‖ ≤ N := by
  unfold squarefreeCharacterSum
  rw [Nat.floor_natCast]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(squarefreeWeight z n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul (squarefreeWeight_abs_le_one hz hz1 n)
          (χ.norm_le_one _) (norm_nonneg _) zero_le_one
        _ = _ := by ring
    _ = _ := by simp

/-- Twisting cannot enlarge the Rankin remainder. -/
theorem characterConvolutionTail_rankin {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 ≤ ε) (N V : ℕ) (hV : 0 < V) :
    ‖characterConvolutionTail χ E z N V‖ ≤
      ((N : ℝ) / (V : ℝ) ^ ε) *
        ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) ^ (1 - ε) := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have htail := harmonic_tail_rankin (Ioc V N) (fun v : ℕ => (v : ℝ))
    (fun v => |smoothCorrection E z v|) hV' hε
    (fun v hv => by exact_mod_cast (mem_Ioc.mp hv).1.le)
    (fun _ _ => abs_nonneg _)
  calc
    _ ≤ (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) := by
      unfold characterConvolutionTail
      rw [mul_sum]
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro v hv
      have hvpos : (0 : ℝ) < v := by exact_mod_cast
        ((mem_Ioc.mp hv).1.trans_le' (Nat.zero_le V))
      have hfloor : ((N / v : ℕ) : ℝ) ≤ (N : ℝ) / v := by
        apply (le_div_iff₀ hvpos).mpr
        exact_mod_cast Nat.div_mul_le_self N v
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |smoothCorrection E z v| * ((N / v : ℕ) : ℝ) :=
          mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _))
            (squarefreeCharacterSum_norm_le χ hz hz1 _) (norm_nonneg _) (abs_nonneg _)
        _ ≤ |smoothCorrection E z v| * ((N : ℝ) / v) :=
          mul_le_mul_of_nonneg_left hfloor (abs_nonneg _)
        _ = _ := by ring
    _ ≤ (N : ℝ) * ((∑ v ∈ Ioc V N, |smoothCorrection E z v| /
        (v : ℝ) ^ (1 - ε)) / (V : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inserting the published character bound below the square-root cutoff -/

namespace JointDickman

open Finset

theorem smallCharacterConvolution_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (z Y D : ℝ) (V : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (hY : 1 < Y) (hD : 0 ≤ D)
    (hbound : ∀ v ∈ Ioc 0 V,
      ‖squarefreeCharacterSum χ z (Y / v)‖ ≤
        K * (Y / v) * (Real.log (Y / v)) ^ (-D))
    (hlog : ∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / v)) :
    ‖∑ v ∈ Ioc 0 V, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
      squarefreeCharacterSum χ z (Y / v)‖ ≤
        K * Y * (Real.log Y / 2) ^ (-D) *
          ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) := by
  have hlogpos : 0 < Real.log Y / 2 := div_pos (Real.log_pos hY) (by norm_num)
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  have hpow := Real.rpow_le_rpow_of_nonpos hlogpos (hlog v hv) (neg_nonpos.mpr hD)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |smoothCorrection E z v| * (K * (Y / v) * (Real.log (Y / v)) ^ (-D)) :=
      mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _))
        (hbound v hv) (norm_nonneg _) (abs_nonneg _)
    _ ≤ |smoothCorrection E z v| * (K * (Y / v) * (Real.log Y / 2) ^ (-D)) := by
      gcongr
    _ = _ := by ring

/-- Uniformity in the modulus is inherited from the published input.
The large-divisor remainder is the actual, already bounded convolution tail. -/
theorem roughCharacterSum_truncated
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (E : Finset ℕ) (Y : ℝ) (V : ℕ),
      9 ≤ Y → (V : ℝ) ^ 2 ≤ Y → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log Y / 2) ^ C → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ E z Y‖ ≤
        K * Y * (Real.log Y / 2) ^ (-D) *
          (∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ)) +
        ‖characterConvolutionTail χ E z ⌊Y⌋₊ V‖ := by
  obtain ⟨K, hK, hbound⟩ := hSW z hz C D hC hD
  refine ⟨K, hK, fun E Y V hY hV q _ hq χ hχ => ?_⟩
  obtain ⟨hVN, hsize⟩ := square_root_truncation_conditions hY hV
  have hY1 : 1 < Y := by linarith
  have hsmall := smallCharacterConvolution_bound χ E z Y D V hK hY1 hD
    (fun v hv => hbound (Y / v) (hsize v hv).1 q
      (hq.trans (Real.rpow_le_rpow (by positivity [Real.log_pos hY1])
        (hsize v hv).2 hC.le)) χ hχ)
    (fun v hv => (hsize v hv).2)
  rw [roughCharacterSum_split χ E z Y V hVN]
  exact (norm_add_le _ _).trans (add_le_add hsmall (le_refl _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughErrorLimits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Decay of the roughness-cutoff errors

The exponential Rankin error absorbs every fixed power of the scale
and of its logarithm. This is the limit needed after the explicit
moving-cutoff expansion.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

theorem rough_exponential_error_tendsto {a K C : ℝ}
    (ha : 0 < a) (hK : 0 < K) (hC : 0 ≤ C) (D : ℝ) :
    Tendsto (fun B : ℝ => B ^ D * (Real.log B) ^ C *
      Real.exp (-(B ^ a / (K * Real.log B)))) atTop (𝓝 0) := by
  have ha2 : 0 < a / 2 := by positivity
  have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((D + C) / (a / 2)) (1 / K) (by positivity)).comp (tendsto_rpow_atTop ha2)
  have hlim : Tendsto (fun B : ℝ => B ^ (D + C) *
      Real.exp (-(1 / K) * B ^ (a / 2))) atTop (𝓝 0) := by
    apply hbase.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    dsimp
    rw [← Real.rpow_mul hB.le]
    congr 2
    field_simp
  have hsmall := (isLittleO_log_rpow_atTop ha2).def (by norm_num : (0 : ℝ) < 1)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_pos hB).le _))
      (Real.exp_pos _).le
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hsmall] with B hB hs
    have hB0 : 0 < B := by linarith
    have hlog : 0 < Real.log B := Real.log_pos hB
    have hlogpow : Real.log B ≤ B ^ (a / 2) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hlog,
        abs_of_pos (Real.rpow_pos_of_pos hB0 _), one_mul] using hs
    have hlogB : Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hB0]
    have hlogC : (Real.log B) ^ C ≤ B ^ C :=
      Real.rpow_le_rpow hlog.le hlogB hC
    have hden : K * Real.log B ≤ K * B ^ (a / 2) :=
      mul_le_mul_of_nonneg_left hlogpow hK.le
    have hquot : (1 / K) * B ^ (a / 2) ≤ B ^ a / (K * Real.log B) := by
      calc
        _ = B ^ a / (K * B ^ (a / 2)) := by
          have hsquare : B ^ a = B ^ (a / 2) * B ^ (a / 2) := by
            rw [← Real.rpow_add hB0]
            congr 1
            ring
          rw [hsquare]
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hB0.le _)
          (mul_pos hK hlog) hden
    have hexp : Real.exp (-(B ^ a / (K * Real.log B))) ≤
        Real.exp (-(1 / K) * B ^ (a / 2)) := by
      apply Real.exp_le_exp.mpr
      linarith
    calc
      _ ≤ (B ^ D * B ^ C) * Real.exp (-(1 / K) * B ^ (a / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlogC (Real.rpow_nonneg hB0.le _))
          hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [← Real.rpow_add hB0]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CorrectionTails
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the logarithmic correction moments

Half of the exponential tilt absorbs the logarithmic moment; the other
half yields decay in the truncation point.
-/

namespace JointDickman

open Finset

theorem log_pow_tail_bound (k : ℕ) {v V ε : ℝ}
    (hv : 1 ≤ v) (hV : 0 < V) (hVv : V ≤ v) (hε : 0 < ε) :
    (Real.log v) ^ k ≤
      ((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) * v ^ ε := by
  have hhalf : 0 < ε / 2 := by positivity
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hcut := Real.rpow_le_rpow hV.le hVv hhalf.le
  have hlog := log_pow_le_rpow k hv hhalf
  have hfact : 0 ≤ (k.factorial : ℝ) / (ε / 2) ^ k := by positivity
  have hmul := mul_le_mul hlog hcut (Real.rpow_nonneg hV.le _) (mul_nonneg hfact
    (Real.rpow_nonneg hv0.le _))
  have hsquare : v ^ (ε / 2) * v ^ (ε / 2) = v ^ ε := by
    rw [← Real.rpow_add hv0]
    congr 1
    ring
  have hquot := (le_div_iff₀ (Real.rpow_pos_of_pos hV _)).mpr hmul
  calc
    _ ≤ (((k.factorial : ℝ) / (ε / 2) ^ k * v ^ (ε / 2)) * v ^ (ε / 2)) /
        V ^ (ε / 2) := hquot
    _ = _ := by rw [mul_assoc, hsquare]; ring

theorem correctionLogTerm_tail_bound (E : Finset ℕ) (z : ℝ) (k : ℕ)
    {n : ℕ} {V ε : ℝ} (hV : 0 < V) (hn : V ≤ n) (hε : 0 < ε) :
    ‖correctionLogTerm E z k n‖ ≤
      ((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) *
        (|smoothCorrection E z n| / (n : ℝ) ^ (1 - ε)) := by
  have hn0 : (0 : ℝ) < n := hV.trans_le hn
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  rw [correctionLogTerm_norm]
  calc
    _ ≤ (|smoothCorrection E z n| / (n : ℝ)) *
        (((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (log_pow_tail_bound k hn1 hV hn hε) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hn0, Real.rpow_one]
      field_simp

/-- A uniform quantitative error when replacing a truncated correction
moment by its convergent full value. -/
theorem correctionLogMoment_tail_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P V : ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 ≤ z → z ≤ 1 / 2 →
      |correctionLogMoment (Nat.primesLE P) z k -
        ∑ n ∈ range (V + 1), correctionLogTerm (Nat.primesLE P) z k n| ≤
          ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
            (V : ℝ) ^ ((1 / Real.log P) / 2)) *
              (A * (Real.log P) ^ (Real.exp 1)) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P V z k hP hlog hV hz hzhalf => ?_⟩
  let E := Nat.primesLE P
  let ε := 1 / Real.log (P : ℝ)
  let D := (k.factorial : ℝ) / (ε / 2) ^ k / (V : ℝ) ^ (ε / 2)
  let f := correctionLogTerm E z k
  let g := fun n : ℕ => |smoothCorrection E z n| / (n : ℝ) ^ (1 - ε)
  have hε : 0 < ε := by dsimp [ε] <;> positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by linarith)).mpr hlog
  have hVreal : (0 : ℝ) < V := by exact_mod_cast hV
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  have hg : Summable g :=
    (smoothCorrection_abs_hasSum E hz (by linarith) (by linarith : 0 ≤ 1 - ε)).summable
  have hf := correctionLogTerm_summable E hz (by linarith) k
  have hnorm : Summable (fun n : {n // n ∉ range (V + 1)} => ‖f n‖) := hf.subtype _
  have hgD : Summable (fun n => D * g n) := hg.mul_left D
  have hcomparison : (∑' n : {n // n ∉ range (V + 1)}, ‖f n‖) ≤
      ∑' n : ℕ, D * g n := by
    apply Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun n _ => mul_nonneg hD (by dsimp [g] <;> positivity)) _ hnorm hgD
    intro n
    have hnV : V < n.val := by
      have hnrange := n.property
      simp only [mem_range] at hnrange
      omega
    exact correctionLogTerm_tail_bound E z k hVreal (by exact_mod_cast hnV.le) hε
  have htotal : (∑' n, g n) ≤ A * (Real.log P) ^ (Real.exp 1) := by
    apply hg.tsum_le_of_sum_le
    intro S
    exact hbound P S z hP hlog hz hzhalf
  have hsplit := hf.of_norm.sum_add_tsum_subtype_compl (range (V + 1))
  have heq : correctionLogMoment E z k - ∑ n ∈ range (V + 1), f n =
      ∑' n : {n // n ∉ range (V + 1)}, f n := by
    change (∑' n, f n) - _ = _
    linarith [hsplit]
  change |correctionLogMoment E z k - ∑ n ∈ range (V + 1), f n| ≤ D * _
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' n : {n // n ∉ range (V + 1)}, ‖f n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, D * g n := hcomparison
    _ = D * ∑' n, g n := hg.tsum_mul_left D
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal hD

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPowerExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Taylor expansion inside the correction convolution

This is the finite-sum expansion before the truncated moments are
replaced by their convergent infinite-series values.
-/

namespace JointDickman

open Finset

theorem truncatedLogMoment_eq_range (E : Finset ℕ) (z : ℝ) (V k : ℕ) :
    truncatedLogMoment E z V k = ∑ v ∈ range (V + 1), correctionLogTerm E z k v := by
  have hset : insert 0 (Ioc 0 V) = range (V + 1) := by
    ext n
    simp only [mem_insert, mem_Ioc, mem_range]
    omega
  rw [← hset, sum_insert (by simp)]
  simp [truncatedLogMoment, correctionLogTerm]

theorem correction_expansion_reindex (E : Finset ℕ) (z a L : ℝ) (V H : ℕ) :
    (∑ k ∈ range (H + 1), rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k)) =
      ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        ∑ k ∈ range (H + 1), rpowShiftCoeff a k * (Real.log v) ^ k * L ^ (a - k) := by
  unfold truncatedLogMoment correctionLogTerm
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro k _
  ring

/-- Expansion using the full correction moments. Both errors are explicit:
the Taylor remainder and the exponentially tilted tails of the moments. -/
theorem correction_power_expansion_full
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (z a : ℝ) (H : ℕ), 0 ≤ z → z ≤ 1 / 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (P V : ℕ) (L : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 < L →
        (∀ v ∈ Ioc 0 V, Real.log v ≤ L / 2) →
        |(∑ v ∈ Ioc 0 V, smoothCorrection (Nat.primesLE P) z v / (v : ℝ) *
            (L - Real.log v) ^ a) -
          ∑ k ∈ range (H + 1), rpowShiftCoeff a k *
            correctionLogMoment (Nat.primesLE P) z k * L ^ (a - k)| ≤
          C * L ^ (a - (H + 1)) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            A * (Real.log P) ^ (Real.exp 1) *
              ∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
                ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
                  (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
  obtain ⟨A, hA, htail⟩ := correctionLogMoment_tail_bound hM
  obtain ⟨B, hB, hmom⟩ := smoothCorrection_log_moments_bound hM
  refine ⟨A, hA, fun z a H hz hzhalf => ?_⟩
  -- The Taylor constant depends only on the exponent and order.
  obtain ⟨C₀, hC₀, hunit⟩ := rpow_scaled_remainder a H
  refine ⟨C₀ * B * ((H + 1).factorial : ℝ), by positivity,
    fun P V L hP hlog hV hL hsmall => ?_⟩
  let E := Nat.primesLE P
  let T := ∑ k ∈ range (H + 1), rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k)
  let F := ∑ k ∈ range (H + 1), rpowShiftCoeff a k * correctionLogMoment E z k * L ^ (a - k)
  have hfirst : |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - T| ≤
      C₀ * L ^ (a - (H + 1)) *
        ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) * (Real.log v) ^ (H + 1) := by
    dsimp only [T]
    rw [correction_expansion_reindex, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
    rw [← mul_sub, abs_mul, abs_div, abs_of_pos hv0]
    exact (mul_le_mul_of_nonneg_left
      (hunit L (Real.log v) hL (Real.log_natCast_nonneg v) (hsmall v hv))
        (by positivity)).trans_eq (by ring)
  have hfirst' : |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - T| ≤
      (C₀ * B * ((H + 1).factorial : ℝ)) * L ^ (a - (H + 1)) *
        (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply hfirst.trans
    have h := mul_le_mul_of_nonneg_left
      (hmom P (Ioc 0 V) z (H + 1) hP hlog hz hzhalf)
      (mul_nonneg hC₀ (Real.rpow_nonneg hL.le (a - ((H : ℝ) + 1))))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsecond : |T - F| ≤ A * (Real.log P) ^ (Real.exp 1) *
      ∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
        ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
          (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
    dsimp [T, F]
    rw [← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro k _
    have hk := htail P V z k hP hlog hV hz hzhalf
    rw [← truncatedLogMoment_eq_range, abs_sub_comm] at hk
    have heq : rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k) -
        rpowShiftCoeff a k * correctionLogMoment E z k * L ^ (a - k) =
        (rpowShiftCoeff a k * L ^ (a - k)) *
          (truncatedLogMoment E z V k - correctionLogMoment E z k) := by ring
    rw [heq, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hL _)]
    exact (mul_le_mul_of_nonneg_left hk (by positivity)).trans_eq (by ring)
  have heq : (∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - F =
      ((∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) * (L - Real.log v) ^ a) - T) +
        (T - F) := by ring
  change |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) * (L - Real.log v) ^ a) - F| ≤ _
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hfirst' hsecond)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MovingRoughExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The moving-cutoff expansion with explicit errors

The classical expansion, Taylor approximation, and correction-moment
tails are now combined for the actual rough squarefree summatory function.
No moving-cutoff asymptotic is used as an input.
-/

namespace JointDickman

open Finset

/-- For the nonpositive powers occurring here, the moment-tail sum is
bounded by a single fixed logarithmic power. -/
theorem powerExpansionError_le {A C a L : ℝ} {H P V : ℕ}
    (hA : 0 ≤ A) (ha : a ≤ 0) (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log P) (hV : 0 < V) :
    powerExpansionError A C a H P V L ≤
      C * L ^ (a - (H + 1)) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        A * (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 < Real.log P := by linarith
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hVpow : 0 < (V : ℝ) ^ ((1 / Real.log P) / 2) := Real.rpow_pos_of_pos hV0 _
  have hsum : (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
      ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
        (V : ℝ) ^ ((1 / Real.log P) / 2))) ≤
      (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
        (Real.log P) ^ H / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
    rw [sum_mul, sum_div]
    apply sum_le_sum
    intro k hk
    have hkH : k ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hk
    have hpow : (Real.log P) ^ k ≤ (Real.log P) ^ H := pow_le_pow_right₀ hlog hkH
    have hunit : L ^ (a - k) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith [Nat.cast_nonneg k (α := ℝ)])
    have hc : 0 ≤ |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k := by positivity
    calc
      _ = (|rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          ((Real.log P) ^ k * L ^ (a - k)) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
        simp only [div_pow, one_pow]
        field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hVpow.le
        apply mul_le_mul_of_nonneg_left _ hc
        simpa using mul_le_mul hpow hunit (Real.rpow_nonneg hL0.le _) (by positivity : (0 : ℝ) ≤ (Real.log P) ^ H)
  unfold powerExpansionError
  refine add_le_add (le_refl _) ?_
  calc
    _ ≤ A * (Real.log P) ^ (Real.exp 1) *
        ((∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          (Real.log P) ^ H / (V : ℝ) ^ ((1 / Real.log P) / 2)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hA (Real.rpow_nonneg hlog0.le _))
    _ = _ := by
      rw [Real.rpow_add hlog0, Real.rpow_natCast]
      ring

theorem correction_sdPolynomial_reindex (c : ℕ → ℝ) (E : Finset ℕ)
    (z Y : ℝ) (H V : ℕ) (hY : 0 < Y) :
    (∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      sdPolynomial c z H (Real.log (Y / v))) =
      ∑ j ∈ range (H + 1), c j * ∑ v ∈ Ioc 0 V,
        smoothCorrection E z v / (v : ℝ) * (Real.log Y - Real.log v) ^ (z - 1 - j) := by
  unfold sdPolynomial
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro v hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  rw [Real.log_div hY.ne' hv0.ne']
  ring

/-- The actual expansion with separately identified classical, Rankin,
Taylor, and moment-tail errors. Its coefficients are the defined moments. -/
theorem moving_rough_expansion_explicit
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ A : ℝ, 0 < A ∧ ∀ H : ℕ, ∃ Csd : ℝ, ∃ C : ℕ → ℝ,
        0 ≤ Csd ∧ (∀ j, 0 ≤ C j) ∧ ∀ (P V : ℕ) (Y : ℝ),
          2 ≤ P → 1 ≤ Real.log P → 0 < V → 9 ≤ Y → (V : ℝ) ^ 2 ≤ Y →
          |roughSquarefreeSummatory (Nat.primesLE P) z Y -
            Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
              (Real.log Y) ^ (z - 1 - ν)| ≤
            Csd * Y * (Real.log Y / 2) ^ (z - 2 - H) *
              (∑ v ∈ Ioc 0 V, |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) +
              |roughConvolutionTail (Nat.primesLE P) z ⌊Y⌋₊ V| +
              Y * ∑ j ∈ range (H + 1), |c j| *
                powerExpansionError A (C j) (z - 1 - j) (H - j) P V (Real.log Y) := by
  obtain ⟨c, hc0, hcpos, hclassical⟩ := roughSelbergDelange_truncated hSD hz
  obtain ⟨A, hA, hexp⟩ := correction_power_expansion_full hM
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, A, hA, fun H => ?_⟩
  obtain ⟨Csd, hCsd, hraw⟩ := hclassical H
  have hexists := fun j : ℕ => hexp z (z - 1 - j) (H - j) hz0 hzhalf
  choose C hC hpower using hexists
  refine ⟨Csd, C, hCsd, hC, fun P V Y hP hlogP hV hY hV2 => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 < Y := by linarith
  have hL : 0 < Real.log Y := Real.log_pos hY1
  obtain ⟨hVfloor, hcut⟩ := square_root_truncation_conditions hY hV2
  have hsmall : ∀ v ∈ Ioc 0 V, Real.log v ≤ Real.log Y / 2 := by
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
    have hh := (hcut v hv).2
    rw [Real.log_div hY0.ne' hv0.ne'] at hh
    linarith
  let W := ∑ v ∈ Ioc 0 V, smoothCorrection (Nat.primesLE P) z v / (v : ℝ) *
    sdPolynomial c z H (Real.log (Y / v))
  let Q := ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
    (Real.log Y) ^ (z - 1 - ν)
  have hfirst := hraw (Nat.primesLE P) Y V hY1 hVfloor
    (fun v hv => (hcut v hv).1) (fun v hv => (hcut v hv).2)
  have hsecond : |W - Q| ≤ ∑ j ∈ range (H + 1), |c j| *
      powerExpansionError A (C j) (z - 1 - j) (H - j) P V (Real.log Y) := by
    dsimp [W, Q]
    rw [correction_sdPolynomial_reindex c _ z Y H V hY0,
      roughCoefficient_expansion, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j hj
    rw [← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact hpower j P V (Real.log Y) hP hlogP hV hL hsmall
  have heq : roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * Q =
      (roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W) + Y * (W - Q) := by ring
  change |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * Q| ≤ _
  rw [heq]
  calc
    _ ≤ |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W| + |Y * (W - Q)| :=
      abs_add_le _ _
    _ = |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W| + Y * |W - Q| := by
      rw [abs_mul, abs_of_pos hY0]
    _ ≤ _ := add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond hY0.le)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughUniformExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform remainder for removal of small primes

The four explicit errors are bounded by one algebraic remainder and one
Rankin remainder. All constants are independent of the cutoff and endpoint.
-/

namespace JointDickman

open Finset

theorem powerTailConstant_nonneg (a : ℝ) (H : ℕ) :
    0 ≤ powerTailConstant a H := sum_nonneg (fun _ _ => by positivity)

theorem powerExpansionError_le_uniform {A C z L : ℝ} {H j P V : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hz : z ≤ 1) (hj : j ≤ H)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log P) (hV : 0 < V) :
    powerExpansionError A C (z - 1 - j) (H - j) P V L ≤
      C * L ^ (z - 2 - H) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        A * powerTailConstant (z - 1 - j) (H - j) *
          (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hsub : ((H - j : ℕ) : ℝ) = H - j := Nat.cast_sub hj
  have hexp : z - 1 - j - ((H - j : ℕ) + 1) = z - 2 - H := by
    rw [hsub]
    ring
  have hpow1 : (Real.log P) ^ (Real.exp 1 + (H - j + 1 : ℕ)) ≤
      (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hcast : ((H - j + 1 : ℕ) : ℝ) ≤ (H + 1 : ℕ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le H j) 1
    linarith
  have hpow2 : (Real.log P) ^ (Real.exp 1 + (H - j : ℕ)) ≤
      (Real.log P) ^ (Real.exp 1 + H) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hcast : ((H - j : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H j
    linarith
  have h := powerExpansionError_le (C := C) (H := H - j) hA (by linarith : z - 1 - j ≤ 0) hL hlog hV
  rw [hexp] at h
  refine h.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left hpow1 (by positivity)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hpow2
      (mul_nonneg hA (powerTailConstant_nonneg _ _))

/-- A single cutoff-independent bound for the complete moving expansion. -/
theorem moving_rough_expansion_uniform
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (P V : ℕ) (Y : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 0 < V → 9 ≤ Y → 1 ≤ Real.log Y →
        (V : ℝ) ^ 2 ≤ Y →
        |roughSquarefreeSummatory (Nat.primesLE P) z Y -
          Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
            (Real.log Y) ^ (z - 1 - ν)| ≤
          Y * K * ((Real.log Y) ^ (z - 2 - H) *
            (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
  obtain ⟨c, hc0, hcpos, A, hA, hraw⟩ := moving_rough_expansion_explicit hSD hM hz
  obtain ⟨M, hMpos, hmom⟩ := smoothCorrection_log_moments_bound hM
  obtain ⟨T, hTpos, htail⟩ := roughConvolutionTail_shifted_bound hM
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨Csd, C, hCsd, hC, hbound⟩ := hraw H
  let E := Csd * M * (2 : ℝ) ^ (-(z - 2 - H))
  let F := ∑ j ∈ range (H + 1), |c j| * C j
  let G := ∑ j ∈ range (H + 1), |c j| * A * powerTailConstant (z - 1 - j) (H - j)
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hF : 0 ≤ F := sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hC j))
  have hG : 0 ≤ G := sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) hA.le) (powerTailConstant_nonneg _ _))
  refine ⟨E + F + T + G, by positivity, fun P V Y hP hlog hV hY hLY hV2 => ?_⟩
  let L := Real.log Y
  let U := L ^ (z - 2 - H) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ))
  let W := (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2)
  have hL : 0 < L := by dsimp [L] <;> linarith
  have hlog0 : 0 < Real.log P := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hU : 0 ≤ U := by dsimp [U] <;> positivity
  have hW : 0 ≤ W := by dsimp [W] <;> positivity
  have hm := hmom P (Ioc 0 V) z 0 hP hlog hz0 hzhalf
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, add_zero] at hm
  have hlogpow : (Real.log P) ^ (Real.exp 1) ≤
      (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hn : (0 : ℝ) ≤ (H + 1 : ℕ) := Nat.cast_nonneg _
    linarith
  have hclassical : Csd * Y * (L / 2) ^ (z - 2 - H) *
      (∑ v ∈ Ioc 0 V, |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) ≤
      Y * E * U := by
    calc
      _ ≤ Csd * Y * (L / 2) ^ (z - 2 - H) *
          (M * (Real.log P) ^ (Real.exp 1)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ Csd * Y * (L / 2) ^ (z - 2 - H) *
          (M * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ))) := by gcongr
      _ = _ := by
        dsimp [E, U]
        rw [Real.div_rpow hL.le (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
  have htail' : |roughConvolutionTail (Nat.primesLE P) z ⌊Y⌋₊ V| ≤ Y * T * W := by
    have h := htail P ⌊Y⌋₊ V z hP hlog hV hz0 hzhalf
    have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
    have hp : (V : ℝ) ^ ((1 / Real.log P) / 2) ≤ (V : ℝ) ^ (1 / Real.log P) := by
      apply Real.rpow_le_rpow_of_exponent_le hV1
      have hpos : 0 < 1 / Real.log P := by positivity
      linarith
    have hlogpow' : (Real.log P) ^ (Real.exp 1) ≤
        (Real.log P) ^ (Real.exp 1 + H) := by
      apply Real.rpow_le_rpow_of_exponent_le hlog
      linarith [Nat.cast_nonneg H (α := ℝ)]
    calc
      _ ≤ (⌊Y⌋₊ : ℝ) / (V : ℝ) ^ (1 / Real.log P) *
          (T * (Real.log P) ^ (Real.exp 1)) := h
      _ ≤ Y / (V : ℝ) ^ ((1 / Real.log P) / 2) *
          (T * (Real.log P) ^ (Real.exp 1 + H)) := by
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · exact div_le_div₀ (by positivity) (Nat.floor_le hY0) (by positivity) hp
        · exact mul_le_mul_of_nonneg_left hlogpow' hTpos.le
      _ = _ := by dsimp [W] <;> ring
  have hpowers : (∑ j ∈ range (H + 1), |c j| *
      powerExpansionError A (C j) (z - 1 - j) (H - j) P V L) ≤ F * U + G * W := by
    calc
      _ ≤ ∑ j ∈ range (H + 1), |c j| * (C j * U +
          A * powerTailConstant (z - 1 - j) (H - j) * W) := by
        apply sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hjH : j ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hj
        simpa only [U, W, mul_div_assoc, mul_assoc] using
          powerExpansionError_le_uniform hA.le (hC j) (by linarith : z ≤ 1) hjH hLY hlog hV
      _ = _ := by
        dsimp [F, G]
        simp only [mul_add, sum_add_distrib, sum_mul]
        apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intro j _ <;> ring
  have h := hbound P V Y hP hlog hV hY hV2
  change _ ≤ Y * (E + F + T + G) * (U + W)
  refine h.trans ?_
  change _ + _ + Y * _ ≤ _
  have hsum := add_le_add (add_le_add hclassical htail')
    (mul_le_mul_of_nonneg_left hpowers hY0)
  refine hsum.trans ?_
  nlinarith [mul_nonneg hY0 (mul_nonneg (add_nonneg hE hF) hW),
    mul_nonneg hY0 (mul_nonneg (add_nonneg hTpos.le hG) hU)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCutoffTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing the roughness truncation

An integer square-root truncation turns the remaining Rankin error into
an explicit exponential in the endpoint logarithm.
-/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem roughTruncation_bounds {Y : ℝ} (hY : 0 < Y) (hL : 16 ≤ Real.log Y) :
    0 < roughTruncation Y ∧ (roughTruncation Y : ℝ) ^ 2 ≤ Y ∧
      Real.log Y / 4 ≤ Real.log (roughTruncation Y) := by
  let t := Real.exp (Real.log Y / 2)
  have ht0 : 0 < t := Real.exp_pos _
  have ht2 : 2 ≤ t := by
    have h := Real.add_one_le_exp (Real.log Y / 2)
    dsimp [t]
    linarith
  have ht1 : 1 ≤ t := by linarith
  have hV : 0 < roughTruncation Y := Nat.floor_pos.mpr ht1
  have hVle : (roughTruncation Y : ℝ) ≤ t := Nat.floor_le ht0.le
  have hVhalf : t / 2 ≤ (roughTruncation Y : ℝ) := by
    have h := Nat.lt_floor_add_one t
    change t < (roughTruncation Y : ℝ) + 1 at h
    linarith
  refine ⟨hV, ?_, ?_⟩
  · have heq : t ^ 2 = Y := by
      dsimp [t]
      rw [sq, ← Real.exp_add, add_halves, Real.exp_log hY]
    have hV0 : (0 : ℝ) ≤ roughTruncation Y := Nat.cast_nonneg _
    nlinarith
  · have h := Real.log_le_log (div_pos ht0 (by norm_num)) hVhalf
    rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at h
    have hlog2 := Real.log_two_lt_d9
    linarith

theorem roughTruncation_rankin {Y : ℝ} {P : ℕ}
    (hY : 0 < Y) (hL : 16 ≤ Real.log Y) (hP : 0 < Real.log P) :
    1 / (roughTruncation Y : ℝ) ^ ((1 / Real.log P) / 2) ≤
      Real.exp (-(Real.log Y / (8 * Real.log P))) := by
  obtain ⟨hV, _, hlogV⟩ := roughTruncation_bounds hY hL
  have hV0 : (0 : ℝ) < roughTruncation Y := by exact_mod_cast hV
  rw [Real.rpow_def_of_pos hV0, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlogV
    (show 0 ≤ (1 / Real.log P) / 2 by positivity)
  have heq : (Real.log Y / 4) * ((1 / Real.log P) / 2) =
      Real.log Y / (8 * Real.log P) := by ring
  rw [heq] at h
  linarith

/-- The complete roughness expansion before substituting `P = B^1000`. -/
theorem moving_rough_expansion_exponential
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) (Y : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 9 ≤ Y → 16 ≤ Real.log Y →
        |roughSquarefreeSummatory (Nat.primesLE P) z Y -
          Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
            (Real.log Y) ^ (z - 1 - ν)| ≤
          Y * K * ((Real.log Y) ^ (z - 2 - H) *
            (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            (Real.log P) ^ (Real.exp 1 + H) *
              Real.exp (-(Real.log Y / (8 * Real.log P)))) := by
  obtain ⟨c, hc0, hcpos, horders⟩ := moving_rough_expansion_uniform hSD hM hz
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨K, hK, hbound⟩ := horders H
  refine ⟨K, hK, fun P Y hP hlog hY hL => ?_⟩
  have hY0 : 0 < Y := by linarith
  obtain ⟨hV, hV2, _⟩ := roughTruncation_bounds hY0 hL
  refine (hbound P (roughTruncation Y) Y hP hlog hV hY (by linarith) hV2).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hY0.le hK)
  apply add_le_add (le_refl _)
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (roughTruncation_rankin hY0 hL (by linarith))
    (Real.rpow_nonneg (by linarith) _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughAuxiliaryExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The moving-cutoff expansion on the manuscript's auxiliary scale

The remainder is uniform once `log Y ≥ B^0.89`. Its decay is derived
from the explicit expansion, rather than assumed as an analytic input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughErrorEnvelope_tendsto {z D : ℝ} {H : ℕ}
    (hH : D + (89 / 100 : ℝ) * (z - 2 - H) < 0) :
    Tendsto (fun B : ℝ => B ^ D * roughErrorEnvelope z H B) atTop (𝓝 0) := by
  let a : ℝ := D + (89 / 100 : ℝ) * (z - 2 - H)
  let C : ℝ := Real.exp 1 + (H + 1 : ℕ)
  have ha : 0 < -a := by dsimp [a] <;> linarith
  have hfirst := (log_power_div_power_tendsto_zero C ha).const_mul ((1000 : ℝ) ^ C)
  have hsecond := (rough_exponential_error_tendsto (by norm_num : (0 : ℝ) < 89 / 100)
    (by norm_num : (0 : ℝ) < 8000)
    (by positivity : 0 ≤ Real.exp 1 + H) D).const_mul
      ((1000 : ℝ) ^ (Real.exp 1 + H))
  have hsum := hfirst.add hsecond
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
  have hB0 : 0 < B := by linarith
  have hlog : 0 ≤ Real.log B := (Real.log_pos hB).le
  dsimp [roughErrorEnvelope, a, C]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) hlog,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) hlog,
    Real.rpow_neg hB0.le, div_inv_eq_mul, ← Real.rpow_mul hB0.le]
  rw [mul_add, ← mul_assoc (B ^ D), ← Real.rpow_add hB0]
  congr 1 <;> ring

theorem rough_error_at_auxiliaryCutoff {z Y : ℝ} {B H : ℕ}
    (hB : 1 < B) (hz : z ≤ 1) (hY : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y) :
    (Real.log Y) ^ (z - 2 - H) *
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (H + 1 : ℕ)) +
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + H) *
        Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B)))) ≤
      roughErrorEnvelope z H B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hlog : 0 < Real.log B := Real.log_pos hBreal
  have hcut : Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
    simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
    norm_num
  have hexp : z - 2 - (H : ℝ) ≤ 0 := by linarith [Nat.cast_nonneg H (α := ℝ)]
  have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hB0 _) hY hexp
  rw [hcut]
  unfold roughErrorEnvelope
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    apply Real.exp_le_exp.mpr
    have hdiv := div_le_div_of_nonneg_right hY (by positivity : 0 ≤ 8000 * Real.log B)
    convert neg_le_neg hdiv using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

/-- The full untwisted moving-cutoff estimate, conditional only on the
classical fixed-order expansion and the cited reciprocal-prime estimate. -/
theorem moving_rough_auxiliary_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y -
          Y * ∑ ν ∈ range (H + 1),
            roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν *
              (Real.log Y) ^ (z - 1 - ν)| ≤ K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc0, hcpos, horders⟩ := moving_rough_expansion_exponential hSD hM hz
  obtain ⟨H, hH⟩ := exists_nat_gt (D / (89 / 100 : ℝ))
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have hgap : D + (89 / 100 : ℝ) * (z - 2 - H) < 0 := by
    have hHD : D < (H : ℝ) * (89 / 100 : ℝ) :=
      (div_lt_iff₀ (by norm_num : (0 : ℝ) < 89 / 100)).mp hH
    linarith
  obtain ⟨K, hK, hbound⟩ := horders H
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  have hlim := (roughErrorEnvelope_tendsto hgap).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ D * roughErrorEnvelope z H B ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ B : ℕ in atTop, (16 : ℝ) ≤ (B : ℝ) ^ (89 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 16)
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge, hP, hlog, eventually_gt_atTop 1] with B hs hl hp hlogP hB
  intro Y hY hY9
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have henv : roughErrorEnvelope z H B ≤ (B : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hB0.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr (by simpa [mul_comm] using hs)
  calc
    _ ≤ Y * K * ((Real.log Y) ^ (z - 2 - H) *
          (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + H) *
          Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B))))) :=
      hbound (auxiliaryCutoff B) Y hp hlogP hY9 (hl.trans hY)
    _ ≤ Y * K * roughErrorEnvelope z H B :=
      mul_le_mul_of_nonneg_left (rough_error_at_auxiliaryCutoff hB hz1 hY)
        (mul_nonneg (by linarith) hK)
    _ ≤ Y * K * (B : ℝ) ^ (-D) := mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MovingCharacterBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonprincipal character estimate after removing the small primes -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem roughTruncation_rankin_full {Y : ℝ} {P : ℕ}
    (hY : 0 < Y) (hL : 16 ≤ Real.log Y) (hP : 0 < Real.log P) :
    1 / (roughTruncation Y : ℝ) ^ (1 / Real.log P) ≤
      Real.exp (-(Real.log Y / (8 * Real.log P))) := by
  obtain ⟨hV, _, hlogV⟩ := roughTruncation_bounds hY hL
  have hV0 : (0 : ℝ) < roughTruncation Y := by exact_mod_cast hV
  rw [Real.rpow_def_of_pos hV0, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlogV
    (show 0 ≤ 1 / Real.log P by positivity)
  have hpos : 0 ≤ Real.log Y / (8 * Real.log P) := by positivity
  have heq : (Real.log Y / 4) * (1 / Real.log P) =
      2 * (Real.log Y / (8 * Real.log P)) := by ring
  rw [heq] at h
  linarith

/-- Every fixed logarithmic saving survives the convolution, at the
cost of a fixed power of the cutoff logarithm and an explicit Rankin error. -/
theorem roughCharacterSum_exponential
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) (Y : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 9 ≤ Y → 16 ≤ Real.log Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log Y / 2) ^ (200 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ (Nat.primesLE P) z Y‖ ≤
        Y * K * ((Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1 + 1) +
          (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P)))) := by
  obtain ⟨C, hC, hbound⟩ := roughCharacterSum_truncated hSW hz (by norm_num : (0 : ℝ) < 200) hD
  obtain ⟨A, hA, hmom⟩ := smoothCorrection_log_moments_bound hM
  obtain ⟨A', hA', hshift⟩ := smoothCorrection_shifted_bound hM
  let K := C * A * (2 : ℝ) ^ D + A'
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzh : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  refine ⟨K, hK, fun P Y hP hlogP hY hL q _ hq χ hχ => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hLP : 0 < Real.log P := by linarith
  have hLY : 0 < Real.log Y := by linarith
  obtain ⟨hV, hV2, _⟩ := roughTruncation_bounds hY0 hL
  have hmain := hbound (Nat.primesLE P) Y (roughTruncation Y) hY hV2 q hq χ hχ
  have habs : (∑ v ∈ Ioc 0 (roughTruncation Y),
      |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) ≤ A * (Real.log P) ^ (Real.exp 1) := by
    simpa using hmom P (Ioc 0 (roughTruncation Y)) z 0 hP hlogP hz0 hzh
  have htail : ‖characterConvolutionTail χ (Nat.primesLE P) z ⌊Y⌋₊ (roughTruncation Y)‖ ≤
      Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
    have ht := characterConvolutionTail_rankin χ (Nat.primesLE P) hz0 (by linarith)
      (by positivity : 0 ≤ 1 / Real.log P) ⌊Y⌋₊ (roughTruncation Y) hV
    calc
      _ ≤ ((⌊Y⌋₊ : ℝ) / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) *
          (A' * (Real.log P) ^ (Real.exp 1)) :=
        ht.trans (mul_le_mul_of_nonneg_left
          (hshift P (Ioc (roughTruncation Y) ⌊Y⌋₊) z hP hlogP hz0 hzh) (by positivity))
      _ ≤ (Y / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) *
          (A' * (Real.log P) ^ (Real.exp 1)) := by
        gcongr
        exact Nat.floor_le hY0.le
      _ = Y * (A' * (Real.log P) ^ (Real.exp 1)) *
          (1 / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) := by ring
      _ ≤ Y * (A' * (Real.log P) ^ (Real.exp 1)) *
          Real.exp (-(Real.log Y / (8 * Real.log P))) :=
        mul_le_mul_of_nonneg_left (roughTruncation_rankin_full hY0 hL hLP) (by positivity)
      _ = _ := by ring
  have hfactor : (Real.log Y / 2) ^ (-D) = (2 : ℝ) ^ D * (Real.log Y) ^ (-D) := by
    rw [Real.div_rpow hLY.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  have hlogpow : (Real.log P) ^ (Real.exp 1) ≤ (Real.log P) ^ (Real.exp 1 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hlogP (by linarith)
  have hK1 : C * A * (2 : ℝ) ^ D ≤ K := by dsimp [K] <;> linarith
  have hK2 : A' ≤ K := by
    dsimp [K]
    have hpos : 0 ≤ C * A * (2 : ℝ) ^ D := by positivity
    linarith
  calc
    _ ≤ C * Y * (Real.log Y / 2) ^ (-D) * (A * (Real.log P) ^ (Real.exp 1)) +
        Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) :=
      hmain.trans (add_le_add (mul_le_mul_of_nonneg_left habs (by positivity)) htail)
    _ = Y * (C * A * (2 : ℝ) ^ D) * (Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1) +
        Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
      rw [hfactor]
      ring
    _ ≤ Y * K * (Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1 + 1) +
        Y * K * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hK1 hY0.le) (by positivity)) hlogpow (by positivity) (by positivity)
      · gcongr
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterAuxiliaryBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform character cancellation on the manuscript's scale -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem auxiliary_modulus_bound : ∀ᶠ B : ℕ in atTop,
    ∀ L : ℝ, (B : ℝ) ^ (89 / 100 : ℝ) ≤ L →
      (B : ℝ) ^ (100 : ℝ) ≤ (L / 2) ^ (200 : ℝ) := by
  have hlarge : ∀ᶠ B : ℕ in atTop, (2 : ℝ) ≤ (B : ℝ) ^ (39 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge, eventually_gt_atTop 0] with B hlargeB hB
  intro L hL
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ (1 / 2 : ℝ) ≤ L / 2 := by
    have heq : (B : ℝ) ^ (89 / 100 : ℝ) =
        (B : ℝ) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (39 / 100 : ℝ) := by
      rw [← Real.rpow_add hB0]
      norm_num
    rw [heq] at hL
    nlinarith [Real.rpow_pos_of_pos hB0 (1 / 2 : ℝ)]
  calc
    _ = ((B : ℝ) ^ (1 / 2 : ℝ)) ^ (200 : ℝ) := by
      rw [← Real.rpow_mul hB0.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB0.le _) hpow (by norm_num)

/-- Cancellation after moving small-prime removal holds for all
nonprincipal characters of modulus at most `B^100`. -/
theorem moving_rough_character_bound
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ (Nat.primesLE (auxiliaryCutoff B)) z Y‖ ≤
        K * Y * (B : ℝ) ^ (-D) := by
  let E : ℝ := 2 * (D + 1)
  have hE : 0 ≤ E := by dsimp [E] <;> linarith
  obtain ⟨K, hK, hbound⟩ := roughCharacterSum_exponential hSW hM hz hE
  refine ⟨K, hK, ?_⟩
  have hgap : D + (89 / 100 : ℝ) * ((2 - E) - 2 - (0 : ℕ)) < 0 := by
    dsimp [E]
    norm_num
    linarith
  have hlim := (roughErrorEnvelope_tendsto hgap).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ D * roughErrorEnvelope (2 - E) 0 B ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ B : ℕ in atTop, (16 : ℝ) ≤ (B : ℝ) ^ (89 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 16)
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge, hP, hlog, auxiliary_modulus_bound,
    eventually_gt_atTop 1] with B hs hl hp hlogP hmod hB
  intro Y hY hY9 q _ hq χ hχ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have henv : roughErrorEnvelope (2 - E) 0 B ≤ (B : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hB0.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr (by simpa [mul_comm] using hs)
  have hpoint : (Real.log Y) ^ (-E) *
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + 1) +
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1) *
        Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B)))) ≤
      roughErrorEnvelope (2 - E) 0 B := by
    have h := rough_error_at_auxiliaryCutoff (H := 0) (z := 2 - E) hB
      (by dsimp [E] <;> linarith) hY
    simp only [Nat.cast_zero, sub_zero, Nat.reduceAdd, Nat.cast_one, add_zero] at h
    rw [show 2 - E - 2 = -E by ring] at h
    exact h
  calc
    _ ≤ Y * K * ((Real.log Y) ^ (-E) *
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + 1) +
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1) *
          Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B))))) :=
      hbound (auxiliaryCutoff B) Y hp hlogP hY9 (hl.trans hY) q
        (hq.trans (hmod (Real.log Y) hY)) χ hχ
    _ ≤ Y * K * roughErrorEnvelope (2 - E) 0 B :=
      mul_le_mul_of_nonneg_left hpoint (by positivity)
    _ ≤ Y * K * (B : ℝ) ^ (-D) := mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterResidues
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Character orthogonality for the actual rough coefficients -/

namespace JointDickman

open Finset

open Classical in
theorem progressionSum_characters {q : ℕ} [NeZero q]
    (S : Finset ℕ) (w : ℕ → ℝ) (r : (ZMod q)ˣ) :
    (q.totient : ℂ) * (progressionSum S w (r : ZMod q) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ) *
        ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q) := by
  rw [progressionSum, Complex.ofReal_sum, mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  calc
    _ = (w n : ℂ) * (if (r : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0) := by
      split_ifs <;> simp_all
      ring
    _ = (w n : ℂ) * ∑ χ : DirichletCharacter ℂ q,
        χ (r⁻¹ : (ZMod q)ˣ) * χ (n : ZMod q) := by
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit, ZMod.inv_coe_unit]
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro χ _; ring

open Classical in
/-- The normalized character average loses no factor depending on the modulus. -/
theorem progressionSum_error_le {q : ℕ} [NeZero q]
    (S : Finset ℕ) (w : ℕ → ℝ) (r : (ZMod q)ˣ) {E : ℝ} (hE : 0 ≤ E)
    (hunit : ∀ n ∈ S, w n ≠ 0 → IsUnit (n : ZMod q))
    (hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ ≤ E) :
    |progressionSum S w (r : ZMod q) - (∑ n ∈ S, w n) / (q.totient : ℝ)| ≤ E := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hprincipal : (∑ n ∈ S, (w n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q)) =
      (∑ n ∈ S, w n : ℝ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro n hn
    by_cases hw : w n = 0
    · simp [hw]
    · rw [MulChar.one_apply (hunit n hn hw), mul_one]
  have hid : (q.totient : ℂ) *
      ((progressionSum S w (r : ZMod q) : ℂ) - (∑ n ∈ S, w n : ℝ) / (q.totient : ℂ)) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q) := by
    have hφ0 : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    rw [mul_sub, mul_div_cancel₀ _ hφ0, progressionSum_characters]
    rw [← sum_erase_add _ _ (mem_univ (1 : DirichletCharacter ℂ q)), hprincipal,
      MulChar.one_apply_coe, one_mul, add_sub_cancel_right]
  have hsum : ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ ≤
      (q.totient : ℝ) * E := by
    calc
      _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, E := by
        apply sum_le_sum
        intro χ hχ
        rw [norm_mul, χ.unit_norm_eq_one, one_mul]
        exact hbound χ (ne_of_mem_erase hχ)
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, E :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => hE)
      _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  rw [← hid, norm_mul, Complex.norm_natCast] at hsum
  have heq : ‖(progressionSum S w (r : ZMod q) : ℂ) - (∑ n ∈ S, w n : ℝ) / (q.totient : ℂ)‖ =
      |progressionSum S w (r : ZMod q) - (∑ n ∈ S, w n) / (q.totient : ℝ)| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [heq] at hsum
  exact (mul_le_mul_iff_right₀ hφ).mp hsum

theorem roughSquarefreeWeight_coprime {P q n : ℕ} (hq : q ≠ 0) (hqP : q ≤ P)
    (z : ℝ) (hn : roughSquarefreeWeight (Nat.primesLE P) z n ≠ 0) : n.Coprime q := by
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  have hd : Disjoint n.primeFactors (Nat.primesLE P) := by
    by_contra h
    simp [roughSquarefreeWeight, h] at hn
  by_contra h
  obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
    (Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpq).trans hqP, hp⟩)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueSummatory
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform progression estimate for rough squarefree integers -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem auxiliary_modulus_le_cutoff {B q : ℕ} (hB : 1 ≤ B)
    (hq : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ)) : q ≤ auxiliaryCutoff B := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hcut : (auxiliaryCutoff B : ℝ) = (B : ℝ) ^ (1000 : ℝ) := by
    norm_num [auxiliaryCutoff]
  have hle := hq.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (100 : ℝ) ≤ 1000))
  rw [← hcut] at hle
  exact_mod_cast hle

/-- Equidistribution in the unit classes, before partial summation. -/
theorem roughResidueSummatory_error
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ r : (ZMod q)ˣ,
      |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient| ≤
        K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨K, hK, hbound⟩ := moving_rough_character_bound hSW hM hz hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro Y hY hY9 q _ hq r
  have hqP := auxiliary_modulus_le_cutoff hB hq
  exact progressionSum_error_le (Ioc 0 ⌊Y⌋₊)
    (roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z) r (by positivity)
    (fun n _ hn => (ZMod.isUnit_iff_coprime n q).mpr
      (roughSquarefreeWeight_coprime (NeZero.ne q) hqP z hn))
    (fun χ hχ => hboundB Y hY hY9 q hq χ hχ)

/-- The same actual coefficients as the untwisted expansion serve in
all unit progressions; the error is uniform in every modulus up to `B^100`. -/
theorem roughResidueSummatory_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
          (Y * ∑ ν ∈ range (H + 1),
            roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν *
              (Real.log Y) ^ (z - 1 - ν)) / q.totient| ≤
          K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := moving_rough_auxiliary_expansion hSD hM hz D
  obtain ⟨K', hK', hres⟩ := roughResidueSummatory_error hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K + K', add_nonneg hK hK', ?_⟩
  filter_upwards [hbound, hres] with B hboundB hresB
  intro Y hY hY9 q _ hq r
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hφ0 : (0 : ℝ) < q.totient := by linarith
  have hu := hboundB Y hY hY9
  have hr := hresB Y hY hY9 q hq r
  let T := Y * ∑ ν ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν * (Real.log Y) ^ (z - 1 - ν)
  have hdiv : |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient -
      T / q.totient| ≤ K * Y * (B : ℝ) ^ (-D) := by
    rw [← sub_div, abs_div, abs_of_pos hφ0]
    exact (div_le_self (abs_nonneg _) hφ).trans hu
  calc
    _ ≤ |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient| +
        |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient -
          T / q.totient| := abs_sub_le _ _ _
    _ ≤ K' * Y * (B : ℝ) ^ (-D) + K * Y * (B : ℝ) ^ (-D) := add_le_add hr hdiv
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual arithmetic coefficient weight A₀ -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_nonneg (B : ℕ) : 0 ≤ coefficientScale B := by
  unfold coefficientScale
  exact mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B))) _)

theorem coefficientWeight_nonneg (B n : ℕ) : 0 ≤ coefficientWeight B n := by
  have hs := coefficientScale_nonneg B
  unfold coefficientWeight roughSquarefreeWeight squarefreeWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs <;> positivity

theorem coefficientScale_eventually_le : ∀ᶠ B : ℕ in atTop, coefficientScale B ≤ B := by
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 1] with B hR hB
  have hp : auxiliaryRatio B ^ (1 / 2 : ℝ) ≤ auxiliaryRatio B := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1 / 2 : ℝ) ≤ 1))
  calc
    coefficientScale B ≤ Real.log (auxiliaryCutoff B) * auxiliaryRatio B :=
      mul_le_mul_of_nonneg_left hp (Real.log_natCast_nonneg _)
    _ = B := by rw [mul_comm, auxiliaryRatio_mul_log hB]

open Classical in
theorem coefficientProgression_eq {q : ℕ} (r : ZMod q) (B : ℕ) (Y : ℝ) :
    progressionSum (Ioc 0 ⌊Y⌋₊) (coefficientWeight B) r =
      coefficientScale B * roughResidueSummatory r (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) Y := by
  unfold roughResidueSummatory progressionSum coefficientWeight
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem hasDerivAt_coefficientModel (c : ℕ → ℝ) (H B : ℕ) {Y : ℝ}
    (hB : 0 < B) (hY : 1 < Y) :
    HasDerivAt (coefficientModel c H B) (coefficientDensity c H B (Real.log Y / B)) Y := by
  have h := (hasDerivAt_logarithmic_model c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) H hY).const_mul
    (coefficientScale B)
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  change HasDerivAt (fun y => coefficientScale B * (y * ∑ j ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) j *
      (Real.log y) ^ ((1 / 2 : ℝ) - 1 - j))) _ Y
  simpa only [coefficientDensity, mul_div_cancel₀ _ hB0] using h

open Classical in
/-- The progression expansion for the actual A₀ weight, retaining an
arbitrary prescribed polynomial saving after normalization. -/
theorem coefficientProgression_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) → ∀ r : (ZMod q)ˣ,
        |progressionSum (Ioc 0 ⌊Y⌋₊) (coefficientWeight B) (r : ZMod q) -
          coefficientModel c H B Y / q.totient| ≤ K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := roughResidueSummatory_expansion hSD hSW hM
    (Or.inr rfl : (1 / 2 : ℝ) = 1 / 4 ∨ (1 / 2 : ℝ) = 1 / 2) (by linarith : 0 ≤ D + 1)
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, coefficientScale_eventually_le, eventually_gt_atTop 0] with B hboundB hscale hB
  intro Y hY hY9 q _ hq r
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := hboundB Y hY hY9 q hq r
  rw [coefficientProgression_eq]
  change |coefficientScale B * _ - coefficientScale B * _ / _| ≤ _
  rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_nonneg (coefficientScale_nonneg B)]
  calc
    _ ≤ coefficientScale B * (K * Y * (B : ℝ) ^ (-(D + 1))) :=
      mul_le_mul_of_nonneg_left hh (coefficientScale_nonneg B)
    _ ≤ (B : ℝ) * (K * Y * (B : ℝ) ^ (-(D + 1))) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = _ := by
      have he : (B : ℝ) * (B : ℝ) ^ (-(D + 1)) = (B : ℝ) ^ (-D) := by
        calc
          _ = (B : ℝ) ^ (1 + -(D + 1)) := by rw [Real.rpow_add hB0, Real.rpow_one]
          _ = _ := by congr 1; ring
      calc
        _ = K * Y * ((B : ℝ) * (B : ℝ) ^ (-(D + 1))) := by ring
        _ = _ := by rw [he]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryOdds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded odds corrections at the manuscript's auxiliary scale -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_mul_sqrt_ratio {B : ℕ} (hB : 1 < B) :
    coefficientScale B * auxiliaryRatio B ^ (1 / 2 : ℝ) = B := by
  unfold coefficientScale
  rw [mul_assoc, ← Real.rpow_add (auxiliaryRatio_pos hB)]
  norm_num only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [mul_comm, auxiliaryRatio_mul_log hB]

theorem primeNormalizer_coefficientScale_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      primeNormalizer (auxiliaryPrimes B) (1 / 2) ≤ C * coefficientScale B / B := by
  let C : ℝ := (4 : ℝ) ^ (-(1 / 2 : ℝ)) + 1
  have hC : 0 < C := by unfold C; positivity
  refine ⟨C, hC, ?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1 / 2) (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (Iio_mem_nhds (show (4 : ℝ) ^ (-(1 / 2 : ℝ)) < C by
      dsimp [C] <;> linarith)), eventually_gt_atTop 1] with B hQ hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  apply (le_div_iff₀ hB0).mpr
  calc
    _ = (primeNormalizer (auxiliaryPrimes B) (1 / 2) * auxiliaryRatio B ^ (1 / 2 : ℝ)) *
        coefficientScale B := by rw [mul_right_comm, mul_assoc, coefficientScale_mul_sqrt_ratio hB]
    _ ≤ C * coefficientScale B :=
      mul_le_mul_of_nonneg_right hQ.le (coefficientScale_nonneg B)

theorem auxiliary_selected_odds_bound :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
      (∏ p ∈ S, (1 - (1 / 2 : ℝ) / p)⁻¹) ≤ Real.exp 1 := by
  have ht : Tendsto (fun B : ℕ => (32 / (5 * Real.log 2)) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have hp := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (32 / (5 * Real.log 2))
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using hp
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp (hS hp)).1).2
  have hcut : ∀ p ∈ S, (auxiliaryCutoff B : ℝ) ≤ p := by
    intro p hp
    exact (mem_filter.mp (hS hp)).2.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ (16 / 5 : ℝ) * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  apply (inverseSelectedPrimeOdds_le hP (by norm_num) (by norm_num) S hprime hcut).trans
  apply Real.exp_le_exp.mpr
  calc
    2 * (S.card : ℝ) / auxiliaryCutoff B ≤
        2 * ((16 / 5 : ℝ) * B / Real.log 2) / auxiliaryCutoff B := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hP.le
    _ = (32 / (5 * Real.log 2)) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
    _ ≤ 1 := hsmall.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ScaledOscillatoryTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling the smooth oscillatory test -/

namespace JointDickman

open MeasureTheory

theorem hasDerivAt_scaledOscillatoryTest {w w' : ℝ → ℝ} {ξ X t : ℝ}
    (hw : HasDerivAt w (w' (t / X)) (t / X)) :
    HasDerivAt (scaledOscillatoryTest w ξ X)
      (scaledOscillatoryTestDeriv w w' ξ X t) t := by
  have h := (hasDerivAt_oscillatoryTest (ξ := ξ) hw).scomp t ((hasDerivAt_id t).div_const X)
  change HasDerivAt (fun s => oscillatoryTest w ξ (s / X)) _ t
  simpa only [scaledOscillatoryTestDeriv,
    oscillatoryTestDeriv, Function.comp_def, id_eq, one_div, one_mul, Complex.real_smul,
    Complex.ofReal_inv, div_eq_mul_inv, mul_comm (X : ℂ)⁻¹] using! h

theorem scaledOscillatoryTest_norm_le {w : ℝ → ℝ} {M ξ X t : ℝ}
    (hw : |w (t / X)| ≤ M) : ‖scaledOscillatoryTest w ξ X t‖ ≤ M := by
  simpa only [scaledOscillatoryTest, oscillatoryTest_norm] using hw

theorem scaledOscillatoryTestDeriv_norm_le {w w' : ℝ → ℝ} {M N ξ X t : ℝ}
    (hX : 0 < X) (hw : |w (t / X)| ≤ M) (hw' : |w' (t / X)| ≤ N) :
    ‖scaledOscillatoryTestDeriv w w' ξ X t‖ ≤ (N + 2 * Real.pi * |ξ| * M) / X := by
  simp only [scaledOscillatoryTestDeriv, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]
  apply div_le_div_of_nonneg_right _ hX.le
  exact (oscillatoryTestDeriv_norm_le w w' ξ (t / X)).trans
    (add_le_add hw' (mul_le_mul_of_nonneg_left hw (by positivity)))

theorem scaledOscillatoryTestDeriv_continuous {w w' : ℝ → ℝ}
    (hw : Continuous w) (hw' : Continuous w') (ξ X : ℝ) :
    Continuous (scaledOscillatoryTestDeriv w w' ξ X) := by
  have hc := oscillatoryTestDeriv_continuousOn hw.continuousOn hw'.continuousOn ξ
    (s := Set.univ)
  have hglobal := continuousOn_univ.mp hc
  exact (hglobal.comp (continuous_id.div_const X)).div_const _

theorem scaledOscillatoryTest_integral (w : ℝ → ℝ) (ρ : ℝ → ℂ)
    (ξ a b X : ℝ) (hX : X ≠ 0) :
    (∫ t in a * X..b * X, scaledOscillatoryTest w ξ X t * ρ t) =
      (X : ℂ) * ∫ s in a..b, oscillatoryTest w ξ s * ρ (s * X) := by
  have h := intervalIntegral.smul_integral_comp_mul_right
    (fun t => scaledOscillatoryTest w ξ X t * ρ t) (a := a) (b := b) X
  simpa only [scaledOscillatoryTest, mul_div_cancel_right₀ _ hX, Complex.real_smul] using h.symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CompactOscillatorySupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing finite cutoffs for compactly supported tests -/

namespace JointDickman

open Finset MeasureTheory

open Classical in
theorem tsum_eq_Ioc_of_scaled_support {w : ℝ → ℝ} {a b X : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hX : 0 < X)
    (hws : ∀ t, t ≤ a ∨ b < t → w t = 0)
    (f : ℕ → ℂ) (hf : ∀ n : ℕ, w (n / X) = 0 → f n = 0) :
    ∑' n, f n = ∑ n ∈ Ioc ⌊a * X⌋₊ ⌊b * X⌋₊, f n := by
  apply tsum_eq_sum
  intro n hn
  apply hf n
  apply hws
  by_cases hna : n ≤ ⌊a * X⌋₊
  · left
    exact (div_le_iff₀ hX).mpr ((Nat.le_floor_iff (mul_nonneg ha hX.le)).mp hna)
  · right
    have hnb : ⌊b * X⌋₊ < n := by
      have hn' : ¬(⌊a * X⌋₊ < n ∧ n ≤ ⌊b * X⌋₊) := by simpa only [mem_Ioc] using hn
      omega
    exact (lt_div_iff₀ hX).mpr ((Nat.floor_lt (mul_nonneg (ha.trans hab) hX.le)).mp hnb)

theorem oscillatory_integral_eq_integral {w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hws : ∀ t, t ≤ a ∨ b < t → w t = 0)
    (ξ : ℝ) (ρ : ℝ → ℂ) :
    (∫ t in a..b, oscillatoryTest w ξ t * ρ t) =
      ∫ t, oscillatoryTest w ξ t * ρ t := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have h : t ≤ a ∨ b < t := by
    by_cases hta : t ≤ a
    · exact Or.inl hta
    · exact Or.inr (lt_of_not_ge (fun htb => ht ⟨lt_of_not_ge hta, htb⟩))
  simp only [oscillatoryTest, hws t h, Complex.ofReal_zero, zero_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteAdditiveOrthogonality
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite additive orthogonality for the arithmetic kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped ComplexConjugate

theorem additivePhase_conj (t : ℝ) : conj (additivePhase t) = additivePhase (-t) := by
  unfold additivePhase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem integral_additivePhase_int (k : ℤ) :
    (∫ θ in (0 : ℝ)..1, additivePhase ((k : ℝ)*θ)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk,additivePhase]
  · have hc : (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hk)
        (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    have he : (fun θ : ℝ => additivePhase ((k : ℝ)*θ)) =
        (fun θ : ℝ => Complex.exp ((k : ℂ)*(2*(Real.pi : ℂ)*Complex.I)*θ)) := by
      funext θ
      unfold additivePhase
      congr 1
      push_cast
      ring
    rw [he,integral_exp_mul_complex hc]
    simp [hk,Complex.exp_int_mul_two_pi_mul_I]

theorem finiteAdditiveSum_continuous (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (finiteAdditiveSum s c) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))

theorem integral_additive_pair (n m : ℕ) (c d : ℂ) :
    (∫ θ in (0 : ℝ)..1,
      (c*additivePhase ((n : ℝ)*θ))*conj (d*additivePhase ((m : ℝ)*θ))) =
      if n = m then c*conj d else 0 := by
  have he : (fun θ : ℝ => (c*additivePhase ((n : ℝ)*θ))*
      conj (d*additivePhase ((m : ℝ)*θ))) =
      (fun θ : ℝ => (c*conj d)*additivePhase (((n : ℤ)-m : ℤ)*θ)) := by
    funext θ
    rw [map_mul,additivePhase_conj]
    have hp : additivePhase (((n : ℤ)-m : ℤ)*θ) =
        additivePhase ((n : ℝ)*θ)*additivePhase (-((m : ℝ)*θ)) := by
      rw [← additivePhase_add]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [he,intervalIntegral.integral_const_mul,integral_additivePhase_int]
  by_cases h : n = m
  · simp [h]
  · have h' : (n : ℤ)-(m : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    simp [h,h']

/-- The exact finite Parseval pairing; different supports are allowed. -/
theorem finiteAdditiveSum_pair_integral (s t : Finset ℕ) (c d : ℕ → ℂ) :
    (∫ θ in (0 : ℝ)..1, finiteAdditiveSum s c θ*conj (finiteAdditiveSum t d θ)) =
      ∑ n ∈ s, ∑ m ∈ t, if n = m then c n*conj (d m) else 0 := by
  have hcont (n m : ℕ) : Continuous (fun θ : ℝ =>
      (c n*additivePhase ((n : ℝ)*θ))*conj (d m*additivePhase ((m : ℝ)*θ))) :=
    (continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))).mul
      (continuous_star.comp (continuous_const.mul
        (continuous_additivePhase.comp (continuous_const.mul continuous_id))))
  have hint (n m : ℕ) := (hcont n m).intervalIntegrable (μ := volume) 0 1
  simp only [finiteAdditiveSum,map_sum,mul_sum,sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [sum_comm]
    apply sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro m hm
      exact integral_additive_pair m n (c m) (d n)
    · intro m _
      exact hint m n
  · intro n _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro m _
    exact hcont m n

/-- Parseval for the finite trigonometric polynomials used in each box. -/
theorem finiteAdditiveSum_parseval (s : Finset ℕ) (c : ℕ → ℂ) :
    (∫ θ in (0 : ℝ)..1, ‖finiteAdditiveSum s c θ‖^2) = ∑ n ∈ s, ‖c n‖^2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (fun θ : ℝ => ((‖finiteAdditiveSum s c θ‖^2 : ℝ) : ℂ)) =
      (fun θ : ℝ => finiteAdditiveSum s c θ*conj (finiteAdditiveSum s c θ)) := by
    funext θ
    simp only [Complex.ofReal_pow,Complex.mul_conj']
  rw [he,finiteAdditiveSum_pair_integral]
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  rw [sum_eq_single n]
  · simp [Complex.mul_conj']
  · intro m _ hmn
    simp [Ne.symm hmn]
  · exact fun h => (h hn).elim

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform boundedness and Lipschitz control of the actual density

These estimates provide the profile hypotheses in the coarse channel.
Their constants are independent of the auxiliary integer B.
-/

namespace JointDickman

open Filter
open scoped Topology NNReal

theorem uniform_power_eventually_bounded {u : ℕ → ℝ → ℝ} {k a δ : ℝ}
    (hδ : 0 < δ) (ha : a ≤ 0)
    (hu : TendstoUniformlyOn u (fun s => k * s ^ a) atTop (Set.Ici δ)) :
    ∀ᶠ B : ℕ in atTop, ∀ s ∈ Set.Ici δ, |u B s| ≤ |k| * δ ^ a + 1 := by
  have h := (Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)
  filter_upwards [h] with B hB
  intro s hs
  have hs0 : 0 < s := hδ.trans_le hs
  have hdist := hB s hs
  rw [Real.dist_eq] at hdist
  have hpow := Real.rpow_le_rpow_of_nonpos hδ hs ha
  calc
    |u B s| = |(u B s - k * s ^ a) + k * s ^ a| := by congr 1; ring
    _ ≤ |u B s - k * s ^ a| + |k * s ^ a| := abs_add_le _ _
    _ = |k * s ^ a - u B s| + |k| * s ^ a := by
      rw [abs_sub_comm, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    _ ≤ |k| * δ ^ a + 1 := by nlinarith [mul_le_mul_of_nonneg_left hpow (abs_nonneg k)]

theorem scaledRoughDensity_bounded_lipschitz
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
      (∀ s ∈ Set.Ici δ, |scaledRoughDensity c z H B s| ≤ M) ∧
      LipschitzOnWith L (scaledRoughDensity c z H B) (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let M := |k| * δ ^ (z - 1) + 1
  let L : ℝ≥0 := ⟨|k * (z - 1)| * δ ^ (z - 2) + 1, by positivity⟩
  have hfun := uniform_power_eventually_bounded hδ (by linarith : z - 1 ≤ 0)
    (scaledRoughDensity_tendstoUniformlyOn hM hMP c hc hz hzhalf hδ H)
  have hder := uniform_power_eventually_bounded hδ (by linarith : z - 2 ≤ 0)
    (scaledRoughDensityDeriv_tendstoUniformlyOn hM hMP c hc hz hzhalf hδ H)
  refine ⟨M, by dsimp [M] <;> positivity, L, ?_⟩
  filter_upwards [hfun, hder] with B hf hd
  refine ⟨hf, ?_⟩
  apply (convex_Ici δ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_scaledRoughDensity c z H B (hδ.trans_le hs)).hasDerivWithinAt)
  intro s hs
  change ‖scaledRoughDensityDeriv c z H B s‖₊ ≤ L
  exact_mod_cast hd s hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMeanNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalization of rough summatory means -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughMeanNormalization_nonneg (B : ℕ) (z : ℝ) :
    0 ≤ roughMeanNormalization B z := by
  exact mul_nonneg (Real.log_natCast_nonneg _)
    (Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg B)
      (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B))) _)

theorem roughMeanNormalization_ratio {B : ℕ} (hB : 1 < B) (z : ℝ) :
    roughMeanNormalization B z / (B : ℝ) = 1 / auxiliaryRatio B ^ z := by
  have hR := auxiliaryRatio_pos hB
  have hmul := auxiliaryRatio_mul_log hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hB)
  have hrpow : auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    simp
  unfold roughMeanNormalization
  apply (div_eq_div_iff hB0 (Real.rpow_pos_of_pos hR z).ne').mpr
  calc
    _ = Real.log (auxiliaryCutoff B) *
        (auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z) := by ring
    _ = B := by rw [hrpow, mul_comm, hmul]
    _ = _ := by ring

theorem roughMeanNormalization_eventually_le {z : ℝ} (hz : 0 ≤ z) :
    ∀ᶠ B : ℕ in atTop, roughMeanNormalization B z ≤ B := by
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 1]
    with B hR hB
  have hp : auxiliaryRatio B ^ (1 - z) ≤ auxiliaryRatio B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hR (show 1 - z ≤ 1 by linarith)
  calc
    _ ≤ Real.log (auxiliaryCutoff B) * auxiliaryRatio B :=
      mul_le_mul_of_nonneg_left hp (Real.log_natCast_nonneg _)
    _ = B := by rw [mul_comm, auxiliaryRatio_mul_log hB]

theorem roughMeanNormalization_quotient_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => roughMeanNormalization B z /
      (primeNormalizer (auxiliaryPrimes B) z * B)) atTop (𝓝 ((4 : ℝ) ^ z)) := by
  have hlim := (auxiliary_primeNormalizer_tendsto hM hz hz1).inv₀
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (-z)).ne'
  have heq : (fun B => (primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z)⁻¹) =ᶠ[atTop]
      (fun B => roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    conv_rhs => rw [mul_comm (primeNormalizer (auxiliaryPrimes B) z)]
    rw [div_mul_eq_div_div, roughMeanNormalization_ratio hB]
    ring
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] at hlim
  simpa only [inv_inv] using hlim.congr' heq

theorem roughMeanProfile_eq (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    roughMeanProfile c z H B s = (B : ℝ) * primeNormalizer (auxiliaryPrimes B) z *
      ∑ j ∈ range (H + 1), roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z j *
        ((B : ℝ) * s) ^ (z - 1 - j) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  unfold roughMeanProfile scaledRoughCoefficient
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [Real.mul_rpow hB0.le hs.le]
  have he : (B : ℝ) ^ (z - j) = B * (B : ℝ) ^ (z - 1 - j) := by
    rw [show z - (j : ℝ) = 1 + (z - 1 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  rw [he]
  ring

theorem roughMeanProfile_eventually_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ B : ℕ in atTop, ∀ s : ℝ, δ ≤ s →
      |roughMeanProfile c z H B s| ≤ M := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b := fun j : ℕ => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hunif := finite_power_uniform (range (H + 1)) (fun j => z - 1 - j) b
    (fun B j => scaledRoughCoefficient c z j B) hδ
    (fun j _ => by linarith [Nat.cast_nonneg (α := ℝ) j]) (fun j _ => hcoef j)
  have hlimit : TendstoUniformlyOn (roughMeanProfile c z H) (fun s => k * s ^ (z - 1))
      atTop (Set.Ici δ) := by
    change TendstoUniformlyOn (fun B s => ∑ j ∈ range (H + 1),
      scaledRoughCoefficient c z j B * s ^ (z - 1 - j)) _ _ _
    simpa [b] using hunif
  refine ⟨|k| * δ ^ (z - 1) + 1, by positivity, ?_⟩
  exact uniform_power_eventually_bounded hδ (by linarith) hlimit

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMeanBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rough coefficient means on the fixed logarithmic scales -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- The normalized summatory mean is bounded uniformly away from the
zero logarithmic scale. Only the cited classical expansion and prime
estimates are used. -/
theorem rough_normalized_mean_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {z δ : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      roughMeanNormalization B z *
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y ≤ C * Y := by
  have hzpos : 0 < z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  obtain ⟨c, hc, _, H, K, hK, hexp⟩ := moving_rough_auxiliary_expansion hSD hM hz 1
  obtain ⟨M, hM0, hprof⟩ := roughMeanProfile_eventually_bounded hM hMP c hc hzpos hzhalf hδ H
  let J : ℝ := (4 : ℝ) ^ z + 1
  have hJ : 0 ≤ J := by dsimp [J] <;> positivity
  have hquot : ∀ᶠ B : ℕ in atTop,
      |roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)| ≤ J := by
    have h := (roughMeanNormalization_quotient_tendsto hM hzpos.le (by linarith : z ≤ 1)).abs
    simpa only [abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) z)] using
      h.eventually (eventually_le_nhds (lt_add_one |(4 : ℝ) ^ z|))
  have hlow : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(11 / 100 : ℝ)) ≤ δ :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_le_nhds hδ)
  refine ⟨K + J * M, by positivity, ?_⟩
  filter_upwards [hexp, hprof, hquot, hlow, roughMeanNormalization_eventually_le hzpos.le,
    eventually_gt_atTop 1] with B hexpB hprofB hquotB hlowB hnorm hB
  intro Y hY hlog
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hBnat : 0 < B := lt_trans Nat.zero_lt_one hB
  have hY0 : 0 ≤ Y := by linarith
  have hs : δ ≤ Real.log Y / B := (le_div_iff₀ hB0).mpr hlog
  have hs0 : 0 < Real.log Y / B := hδ.trans_le hs
  have hpower : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y := by
    have hmul := mul_le_mul_of_nonneg_left hlowB hB0.le
    have heq : (B : ℝ) * (B : ℝ) ^ (-(11 / 100 : ℝ)) = (B : ℝ) ^ (89 / 100 : ℝ) := by
      calc
        _ = (B : ℝ) ^ (1 : ℝ) * (B : ℝ) ^ (-(11 / 100 : ℝ)) := by rw [Real.rpow_one]
        _ = (B : ℝ) ^ ((1 : ℝ) + -(11 / 100 : ℝ)) := (Real.rpow_add hB0 _ _).symm
        _ = _ := by norm_num
    rw [heq] at hmul
    exact hmul.trans (by simpa [mul_comm] using hlog)
  have herror := hexpB Y hpower hY
  have hQ : primeNormalizer (auxiliaryPrimes B) z ≠ 0 := by
    apply ne_of_gt
    unfold primeNormalizer
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact sub_pos.mpr ((div_lt_one hp0).mpr (by linarith))
  let T := Y * ∑ j ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z j * (Real.log Y) ^ (z - 1 - j)
  have hmodel : roughMeanNormalization B z * T = Y *
      (roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)) *
        roughMeanProfile c z H B (Real.log Y / B) := by
    rw [roughMeanProfile_eq c z H B hBnat hs0, mul_div_cancel₀ _ hB0.ne']
    dsimp [T]
    field_simp
  have hmodelBound : |roughMeanNormalization B z * T| ≤ Y * (J * M) := by
    rw [hmodel, abs_mul, abs_mul, abs_of_nonneg hY0]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hquotB (hprofB _ hs) (abs_nonneg _) hJ) hY0
  have herrorBound : |roughMeanNormalization B z *
      (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T)| ≤ K * Y := by
    rw [abs_mul, abs_of_nonneg (roughMeanNormalization_nonneg B z)]
    calc
      _ ≤ roughMeanNormalization B z * (K * Y * (B : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left herror (roughMeanNormalization_nonneg B z)
      _ ≤ (B : ℝ) * (K * Y * (B : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = _ := by rw [Real.rpow_neg_one]; field_simp
  calc
    _ = roughMeanNormalization B z *
        (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T) +
        roughMeanNormalization B z * T := by ring
    _ ≤ |roughMeanNormalization B z *
        (roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y - T)| +
        |roughMeanNormalization B z * T| := add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ K * Y + Y * (J * M) := add_le_add herrorBound hmodelBound
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First and second moments of the actual coefficient A₀

These are the estimates in equation (5) of the manuscript.  The two
specializations of the published Selberg–Delange input suffice here.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughSquarefreeWeight_sq (E : Finset ℕ) (z : ℝ) (n : ℕ) :
    roughSquarefreeWeight E z n ^ 2 = roughSquarefreeWeight E (z ^ 2) n := by
  simp only [roughSquarefreeWeight, squarefreeWeight, ArithmeticFunction.coe_mk]
  split_ifs <;> simp [← pow_mul, Nat.mul_comm]

theorem coefficientScale_eq_roughMeanNormalization (B : ℕ) :
    coefficientScale B = roughMeanNormalization B (1 / 2) := by
  norm_num [coefficientScale, roughMeanNormalization]

theorem coefficientScale_sq (B : ℕ) (hB : 1 < B) :
    coefficientScale B ^ 2 =
      (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) *
        roughMeanNormalization B (1 / 4) := by
  have hR := auxiliaryRatio_pos hB
  have hhalf : (auxiliaryRatio B ^ (1 / 2 : ℝ)) ^ 2 = auxiliaryRatio B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  have hquarter : auxiliaryRatio B ^ (1 / 4 : ℝ) *
      auxiliaryRatio B ^ (1 - 1 / 4 : ℝ) = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    norm_num
  simp only [coefficientScale, roughMeanNormalization, mul_pow, hhalf]
  rw [mul_mul_mul_comm, hquarter]
  ring

theorem coefficient_second_moment_factor {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop,
      Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ) ≤
        (B : ℝ) ^ (1 / 4 + ε) := by
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (1000 : ℝ) ^ (3 / 4 : ℝ) * (Real.log B) ^ (3 / 4 : ℝ) /
        (B : ℝ) ^ ε ≤ 1 := by
    have h := ((log_power_div_power_tendsto_zero (3 / 4) hε).const_mul
      ((1000 : ℝ) ^ (3 / 4 : ℝ))).comp tendsto_natCast_atTop_atTop
    simp only [mul_zero] at h
    filter_upwards [h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hB
    simpa [mul_div_assoc] using hB
  filter_upwards [hsmall, eventually_gt_atTop 1] with B hsmallB hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hl : 0 < Real.log (auxiliaryCutoff B) := by
    simpa [auxiliaryCutoff, Nat.cast_pow, Real.log_pow] using
      mul_pos (by norm_num : (0 : ℝ) < 1000)
        (Real.log_pos (show (1 : ℝ) < B by exact_mod_cast hB))
  have hr : auxiliaryRatio B = (B : ℝ) / Real.log (auxiliaryCutoff B) := by
    simp [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  have hpow : Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) ≤ (B : ℝ) ^ ε := by
    simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_natCast_nonneg B)]
    exact (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp hsmallB
  calc
    _ = (B : ℝ) ^ (1 / 4 : ℝ) * Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) := by
      rw [hr, Real.div_rpow hB0.le hl.le]
      have he : Real.log (auxiliaryCutoff B) /
          Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ) =
          Real.log (auxiliaryCutoff B) ^ (3 / 4 : ℝ) := by
        calc
          _ = Real.log (auxiliaryCutoff B) ^ (1 : ℝ) /
              Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hl]; norm_num
      calc
        _ = (B : ℝ) ^ (1 / 4 : ℝ) *
            (Real.log (auxiliaryCutoff B) / Real.log (auxiliaryCutoff B) ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [he]
    _ ≤ (B : ℝ) ^ (1 / 4 : ℝ) * (B : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := (Real.rpow_add hB0 _ _).symm

theorem coefficient_first_moment
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      ∑ n ∈ Ioc 0 ⌊Y⌋₊, coefficientWeight B n ≤ C * Y := by
  obtain ⟨C, hC, hbound⟩ := rough_normalized_mean_bound hSD hM hMP (Or.inr rfl) hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with B hboundB
  intro Y hY hlog
  simpa only [coefficientWeight, ← mul_sum, coefficientScale_eq_roughMeanNormalization,
    roughSquarefreeSummatory] using hboundB Y hY hlog

theorem coefficient_second_moment
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      9 ≤ Y → δ * B ≤ Real.log Y →
      ∑ n ∈ Ioc 0 ⌊Y⌋₊, coefficientWeight B n ^ 2 ≤
        C * Y * (B : ℝ) ^ (1 / 4 + ε) := by
  obtain ⟨C, hC, hbound⟩ := rough_normalized_mean_bound hSD hM hMP (Or.inl rfl) hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, coefficient_second_moment_factor hε, eventually_gt_atTop 1]
    with B hboundB hfactor hB
  intro Y hY hlog
  have hY0 : 0 ≤ Y := by linarith
  calc
    _ = coefficientScale B ^ 2 *
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) (1 / 4) Y := by
      simp only [coefficientWeight, mul_pow, roughSquarefreeWeight_sq]
      norm_num [roughSquarefreeSummatory, mul_sum]
    _ = (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) *
        (roughMeanNormalization B (1 / 4) *
          roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) (1 / 4) Y) := by
      rw [coefficientScale_sq B hB, mul_assoc]
    _ ≤ (Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ (1 / 4 : ℝ)) * (C * Y) :=
      mul_le_mul_of_nonneg_left (hboundB Y hY hlog)
        (mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg
          (auxiliaryRatio_pos hB).le _))
    _ ≤ (B : ℝ) ^ (1 / 4 + ε) * (C * Y) :=
      mul_le_mul_of_nonneg_right hfactor (mul_nonneg hC hY0)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FairSplitChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite fair-split channel

A site is a vector of independent Bernoulli bits. Conditional on that site,
each present prime is retained independently with probability one half and
each absent prime stays absent. Integrating two conditionally independent
retentions gives exactly the same-site two-split law, including for arbitrary
output cells. This connects that law to the actual finite channel kernel.
-/

namespace JointDickman

open scoped BigOperators

theorem fairRetentionBitMass_marginal (q : ℝ) (b : Bool) :
    (∑ hit, bernoulliBitMass q hit * fairRetentionBitMass hit b) = bernoulliBitMass (q / 2) b := by
  cases b <;> simp [fairRetentionBitMass, bernoulliBitMass] <;> ring

theorem fairRetentionMass_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → Bool) :
    (∑ x, bernoulliSiteMass q x * fairRetentionMass x y) =
      bernoulliSiteMass (fun i => q i / 2) y := by
  classical
  simp only [bernoulliSiteMass, fairRetentionMass, finiteProductMass, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i hit => bernoulliBitMass (q i) hit *
    fairRetentionBitMass hit (y i))]
  simp_rw [fairRetentionBitMass_marginal]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetThinning
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair thinning of an independently selected prime set -/

namespace JointDickman

open Finset

theorem fairRetentionMass_subsets {α : Type*} [DecidableEq α]
    (P : Finset α) (S T : P.powerset) :
    fairRetentionMass (subsetHitEquiv P S) (subsetHitEquiv P T) =
      subsetRetentionMass S.val T.val := by
  classical
  have heq : fairRetentionMass (subsetHitEquiv P S) (subsetHitEquiv P T) =
      ∏ p ∈ P, if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1 := by
    unfold fairRetentionMass finiteProductMass
    calc
      _ = ∏ p : P, if p.val ∈ S.val then (1 / 2 : ℝ) else if p.val ∈ T.val then 0 else 1 := by
        apply prod_congr rfl
        intro p _
        by_cases hs : p.val ∈ S.val <;> by_cases ht : p.val ∈ T.val <;>
          norm_num [subsetHitEquiv, fairRetentionBitMass, bernoulliBitMass, hs, ht]
      _ = _ := prod_coe_sort P (fun p => if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1)

  rw [heq]
  by_cases ht : T.val ⊆ S.val
  · rw [subsetRetentionMass, ite_eq_left ht]
    have hp (p : α) : (if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1) =
        if p ∈ S.val then (1 / 2 : ℝ) else 1 := by
      by_cases hs : p ∈ S.val
      · simp [hs]
      · have hn : p ∉ T.val := fun h => hs (ht h)
        simp [hs, hn]
    simp_rw [hp]
    rw [← prod_filter]
    have hf : P.filter (fun p => p ∈ S.val) = S.val := by
      ext p
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hp => (mem_powerset.mp S.property) hp)
    rw [hf, prod_const]
  · rw [subsetRetentionMass, ite_eq_right ht]
    obtain ⟨p, hpT, hpS⟩ := not_subset.mp ht
    apply prod_eq_zero (mem_powerset.mp T.property hpT)
    simp only [hpT, hpS, ite_false, if_false, ite_true, if_true]

theorem subsetRetentionMass_marginal {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) {T : Finset α} (hT : T ⊆ P) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * subsetRetentionMass S T) =
      bernoulliSubsetMass P (fun p => q p / 2) T := by
  classical
  let t : P.powerset := ⟨T, mem_powerset.mpr hT⟩
  have h := fairRetentionMass_marginal (fun p : P => q p.val) (subsetHitEquiv P t)
  rw [← (subsetHitEquiv P).sum_comp] at h
  change (∑ s : P.powerset,
    finiteProductMass (fun p : P => bernoulliBitMass (q p.val)) (subsetHitEquiv P s) *
      fairRetentionMass (subsetHitEquiv P s) (subsetHitEquiv P t)) =
    finiteProductMass (fun p : P => bernoulliBitMass (q p.val / 2)) (subsetHitEquiv P t) at h
  simp_rw [bernoulliSubsetMass_eq_product, fairRetentionMass_subsets] at h
  rw [bernoulliSubsetMass_eq_product P (fun p => q p / 2) t] at h
  exact (sum_coe_sort P.powerset (fun S => bernoulliSubsetMass P q S * subsetRetentionMass S T)).symm.trans h

/-- Integrating both the first remaining set and its fair second coins
leaves precisely the independent addition law with halved parameters. -/
theorem subsetRetentionMass_expectation {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (F : Finset α → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S *
      ∑ T ∈ P.powerset, subsetRetentionMass S T * F T) =
      ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => q p / 2) T * F T := by
  classical
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  rw [← sum_mul, subsetRetentionMass_marginal P q (mem_powerset.mp hT)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDomination
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Manuscript equation (4): domination by the coefficient weight -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The actual prime-product probability is bounded by A₀(n)/(Bn),
uniformly over the full product range needed by the application. -/
theorem primeProductMass_coefficient_domination
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ n : ℕ, 0 < n →
      (n : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
      primeProductMass (auxiliaryPrimes B) (1 / 2) n ≤
        C * coefficientWeight B n / ((B : ℝ) * n) := by
  obtain ⟨C, hC, hQ⟩ := primeNormalizer_coefficientScale_bound hM
  refine ⟨Real.exp 1 * C, mul_pos (Real.exp_pos _) hC, ?_⟩
  filter_upwards [hQ, auxiliary_selected_odds_bound, eventually_gt_atTop 1] with B hQB hodds hB
  intro n hn hsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 ≤ roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n := by
    unfold roughSquarefreeWeight squarefreeWeight
    simp only [ArithmeticFunction.coe_mk]
    split_ifs <;> positivity
  by_cases hs : n ∈ (auxiliaryPrimes B).powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hs
    have hS : S ⊆ auxiliaryPrimes B := mem_powerset.mp hSP
    have hprime : ∀ p ∈ auxiliaryPrimes B, p.Prime := by
      intro p hp
      exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
    have hnonzero : ∀ p ∈ S, 1 - (1 / 2 : ℝ) / p ≠ 0 := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p (hS hp)).two_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hf : (1 / 2 : ℝ) / p < 1 := (div_lt_one hp0).mpr (by linarith)
      linarith
    have hmass : primeProductMass (auxiliaryPrimes B) (1 / 2) n =
        uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S *
          ∏ p ∈ S, (1 - (1 / 2 : ℝ) / p)⁻¹ := by
      rw [← hSn, primeProductMass_at_product (1 / 2) hprime hS,
        bernoulliSubsetMass_eq_uncorrected_odds _ hS hnonzero]
    have hnU : (n : ℝ) ≤ auxiliaryUpper B := by
      refine hsize.trans (Real.exp_le_exp.mpr ?_)
      nlinarith
    have hunc : uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S =
        primeNormalizer (auxiliaryPrimes B) (1 / 2) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n := by
      rw [← uncorrectedPrimeProductMass_at_product (1 / 2) hprime hS, hSn]
      exact uncorrectedPrimeProductMass_harmonic hnU (1 / 2)
    have hunc0 : 0 ≤ uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S := by
      unfold uncorrectedSubsetMass
      apply mul_nonneg
      · apply prod_nonneg
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
        have hf : (1 / 2 : ℝ) / p ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)
        linarith
      · exact prod_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))
    rw [hmass]
    calc
      _ ≤ uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (hodds S hS (by simpa only [hSn] using hsize)) hunc0
      _ = Real.exp 1 * primeNormalizer (auxiliaryPrimes B) (1 / 2) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n := by rw [hunc]; ring
      _ ≤ Real.exp 1 * (C * coefficientScale B / B) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQB (Real.exp_pos _).le) hr) hn0.le
      _ = _ := by unfold coefficientWeight; ring
  · rw [primeProductMass_eq_zero (1 / 2) n hs]
    exact div_nonneg (mul_nonneg (mul_pos (Real.exp_pos _) hC).le (coefficientWeight_nonneg B n))
      (mul_nonneg hB0.le hn0.le)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedSplitProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed fair-split product law used by the kernel -/

namespace JointDickman
open Finset

theorem splitProductMass_nonneg (P S : Finset ℕ) (n : ℕ) :
    0 ≤ splitProductMass P S n := by
  classical
  apply sum_nonneg
  intro A _
  unfold subsetRetentionMass
  split_ifs <;> positivity

theorem signedSplitProductMass_one (P : Finset ℕ) (n : ℕ) :
    signedSplitProductMass P (fun _ => 1) n = primeProductMass P (1/2) n := by
  classical
  unfold signedSplitProductMass splitProductMass
  simp only [mul_one]
  rw [subsetRetentionMass_expectation]
  unfold primeProductMass
  apply sum_congr rfl
  intro A _
  have hq : (fun p : ℕ => (1/(p : ℝ))/2) = (fun p : ℕ => (1/2 : ℝ)/(p : ℝ)) := by
    funext p
    ring
  rw [hq]
  split_ifs <;> simp

theorem signedSplitProductMass_abs_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : Finset ℕ → ℝ} (hg : ∀ S ⊆ P, |g S| ≤ 1) (n : ℕ) :
    |signedSplitProductMass P g n| ≤ primeProductMass P (1/2) n := by
  classical
  rw [← signedSplitProductMass_one]
  unfold signedSplitProductMass
  calc
    _ ≤ ∑ S ∈ P.powerset,
        |bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S * splitProductMass P S n| :=
      abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro S hS
      have hmass : 0 ≤ bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S := by
        apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
        exact ⟨by positivity,(div_le_one (by linarith)).mpr hp1⟩
      rw [abs_mul,abs_mul,abs_of_nonneg hmass,abs_of_nonneg (splitProductMass_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hg S (mem_powerset.mp hS)) hmass)
        (splitProductMass_nonneg _ _ _)

theorem signedSplitProductMass_coefficient_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in Filter.atTop,
      ∀ (g : Finset ℕ → ℝ), (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) →
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        C*coefficientWeight B n/((B : ℝ)*n) := by
  obtain ⟨C,hC,hbound⟩ := primeProductMass_coefficient_domination hM
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with B hboundB
  intro g hg n hn hsize
  exact (signedSplitProductMass_abs_le (auxiliaryPrimes_prime B) hg n).trans
    (hboundB n hn hsize)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointFourierBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First and second Fourier bounds for signed endpoint masses -/

namespace JointDickman
open Finset MeasureTheory

/-- Pointwise domination of each weighted endpoint coefficient. -/
theorem endpoint_weight_domination {B n : ℕ} {a X D M : ℝ}
    {γ : ℕ → ℝ} {w : ℝ → ℝ} (hB : 0 < B) (ha : 0 < a) (hX : 0 < X)
    (hD : 0 ≤ D) (_hM : 0 ≤ M) (hn : a*X < n)
    (hγ : |γ n| ≤ D*coefficientWeight B n/((B : ℝ)*n))
    (hw : |w (n/X)| ≤ M) :
    |γ n*w (n/X)| ≤ (D*M/((B : ℝ)*(a*X)))*coefficientWeight B n := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hn0 : (0 : ℝ) < n := (mul_pos ha hX).trans hn
  have hγ' : |γ n| ≤ D*coefficientWeight B n/((B : ℝ)*(a*X)) :=
    hγ.trans (div_le_div_of_nonneg_left (mul_nonneg hD (coefficientWeight_nonneg B n))
      (mul_pos hB0 (mul_pos ha hX))
      (mul_le_mul_of_nonneg_left hn.le hB0.le))
  rw [abs_mul]
  exact (mul_le_mul hγ' hw (abs_nonneg _)
    (div_nonneg (mul_nonneg hD (coefficientWeight_nonneg B n))
      (mul_pos hB0 (mul_pos ha hX)).le)).trans_eq (by ring)

/-- Finite-window form of both endpoint Fourier estimates. -/
theorem endpoint_fourier_bounds {B : ℕ} {a b X D M : ℝ}
    (hB : 0 < B) (ha : 0 < a) (hX : 0 < X) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ)
    (hγ : ∀ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        D*coefficientWeight B n/((B : ℝ)*n))
    (hw : ∀ t, |w t| ≤ M) :
    (∀ θ, ‖endpointFourierSum B a b X g w θ‖ ≤
      (D*M/((B : ℝ)*(a*X)))*∑ n ∈ Ioc 0 ⌊b*X⌋₊, coefficientWeight B n) ∧
    (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b X g w θ‖^2) ≤
      (D*M/((B : ℝ)*(a*X)))^2*∑ n ∈ Ioc 0 ⌊b*X⌋₊, coefficientWeight B n^2 := by
  classical
  let F := D*M/((B : ℝ)*(a*X))
  have hF : 0 ≤ F := by dsimp [F] <;> positivity
  have hdom (n : ℕ) (hn : n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊) :
      |signedSplitProductMass (auxiliaryPrimes B) g n*w (n/X)| ≤ F*coefficientWeight B n := by
    exact endpoint_weight_domination hB ha hX hD hM
      ((Nat.floor_lt (mul_pos ha hX).le).mp (mem_Ioc.mp hn).1) (hγ n hn) (hw _)
  have hsub : Ioc ⌊a*X⌋₊ ⌊b*X⌋₊ ⊆ Ioc 0 ⌊b*X⌋₊ := by
    intro n hn
    simp only [mem_Ioc] at *
    omega
  constructor
  · intro θ
    calc
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
          ‖(signedSplitProductMass (auxiliaryPrimes B) g n*w (n/X) : ℝ) *
            additivePhase ((n : ℝ)*θ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, F*coefficientWeight B n := by
        apply sum_le_sum
        intro n hn
        simpa only [norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul] using hdom n hn
      _ ≤ ∑ n ∈ Ioc 0 ⌊b*X⌋₊, F*coefficientWeight B n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg hF (coefficientWeight_nonneg B n))
      _ = _ := (mul_sum _ _ _).symm
  · unfold endpointFourierSum
    rw [finiteAdditiveSum_parseval]
    calc
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, F^2*coefficientWeight B n^2 := by
        apply sum_le_sum
        intro n hn
        rw [Complex.norm_real,Real.norm_eq_abs]
        have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hF (coefficientWeight_nonneg B n))).mpr (hdom n hn)
        simpa only [mul_pow] using hh
      _ ≤ ∑ n ∈ Ioc 0 ⌊b*X⌋₊, F^2*coefficientWeight B n^2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := (mul_sum _ _ _).symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient expansion on a fixed scaled support -/

namespace JointDickman

open Filter
open scoped Topology

theorem coefficient_support_window {a : ℝ} (ha : 0 < a) :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9 / 10 : ℝ) * B ≤ Real.log X →
      9 ≤ a * X ∧ (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log (a * X) := by
  have hloglim : Tendsto (fun B : ℕ => Real.log a / B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hpowlim : Tendsto (fun B : ℕ => (B : ℝ) ^ (-(11 / 100 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 100)).comp tendsto_natCast_atTop_atTop
  have hpowlarge : Tendsto (fun B : ℕ => (B : ℝ) ^ (89 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hloglim.eventually (Ioi_mem_nhds (by norm_num : -(9 / 20 : ℝ) < 0)),
    hpowlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 9 / 20)),
    hpowlarge.eventually_ge_atTop (Real.log 9), eventually_gt_atTop 0] with B hloga hsmall hlarge hB
  intro X hX hlogX
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlower : -(9 / 20 : ℝ) * B ≤ Real.log a := (lt_div_iff₀ hB0).mp hloga |>.le
  have hpower : (B : ℝ) ^ (89 / 100 : ℝ) = (B : ℝ) ^ (-(11 / 100 : ℝ)) * B := by
    calc
      _ = (B : ℝ) ^ (-(11 / 100 : ℝ) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hB0, Real.rpow_one]
  have hs : (B : ℝ) ^ (89 / 100 : ℝ) ≤ (9 / 20 : ℝ) * B := by
    rw [hpower]
    exact mul_le_mul_of_nonneg_right hsmall.le hB0.le
  have hbound : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log (a * X) := by
    rw [Real.log_mul ha.ne' hX.ne']
    linarith
  exact ⟨(Real.log_le_log_iff (by norm_num) (mul_pos ha hX)).mp (hlarge.trans hbound), hbound⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EndpointScaleWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient range for a fixed scaled endpoint support -/

namespace JointDickman
open Filter
open scoped Topology

theorem endpoint_scale_window {b : ℝ} (hb : 0 < b) :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X → Real.log X ≤ (5/2 : ℝ)*B →
      9 ≤ b*X ∧ (1/2 : ℝ)*B ≤ Real.log (b*X) ∧
        b*X ≤ Real.exp ((16/5 : ℝ)*B) := by
  have hlo : ∀ᶠ B : ℕ in atTop, -Real.log b ≤ (2/5 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2/5)).eventually_ge_atTop _
  have hhi : ∀ᶠ B : ℕ in atTop, Real.log b ≤ (7/10 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 7/10)).eventually_ge_atTop _
  filter_upwards [hlo,hhi,coefficient_support_window hb] with B hloB hhiB hw
  intro X hX hloglo hloghi
  have he : Real.log (b*X) = Real.log b+Real.log X := Real.log_mul hb.ne' hX.ne'
  refine ⟨(hw X hX hloglo).1,?_,?_⟩
  · rw [he]
    linarith
  · apply (Real.log_le_iff_le_exp (mul_pos hb hX)).mp
    rw [he]
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_EndpointFourierMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Manuscript (35) and the trivial endpoint sum bound -/

namespace JointDickman
open Filter Finset MeasureTheory
open scoped Topology

theorem endpoint_fourier_moments
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ᶠ B : ℕ in atTop,
      ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      Real.log X ≤ (5/2 : ℝ)*B →
      ∀ (g : Finset ℕ → ℝ), (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      ∀ (w : ℝ → ℝ) (M : ℝ), 0 ≤ M → (∀ t, |w t| ≤ M) →
      (∀ θ, ‖endpointFourierSum B a b X g w θ‖ ≤ C₁*M/B) ∧
      (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b X g w θ‖^2) ≤
        C₂*M^2*(B : ℝ)^(-7/4+ε)/X := by
  obtain ⟨D,hD,hdom⟩ := signedSplitProductMass_coefficient_bound hM
  obtain ⟨K₁,hK₁,hfirst⟩ := coefficient_first_moment hSD hM hMP (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨K₂,hK₂,hsecond⟩ := coefficient_second_moment hSD hM hMP
    (by norm_num : (0 : ℝ) < 1/2) hε
  have hb : 0 < b := ha.trans_le hab
  refine ⟨D*K₁*b/a,D^2*K₂*b/a^2,by positivity,by positivity,?_⟩
  filter_upwards [hdom,hfirst,hsecond,endpoint_scale_window hb,eventually_gt_atTop 0]
    with B hdomB hfirstB hsecondB hwindow hB
  intro X hX hloglo hloghi g hg w M hM0 hw
  obtain ⟨hY,hlogY,hsize⟩ := hwindow X hX hloglo hloghi
  have hdom' : ∀ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        D*coefficientWeight B n/((B : ℝ)*n) := by
    intro n hn
    have hlow : a*X < (n : ℝ) := (Nat.floor_lt (mul_pos ha hX).le).mp (mem_Ioc.mp hn).1
    have hn0 : 0 < n := by exact_mod_cast ((mul_pos ha hX).trans hlow)
    have hnY : (n : ℝ) ≤ b*X := (Nat.le_floor_iff (mul_pos hb hX).le).mp (mem_Ioc.mp hn).2
    exact hdomB g hg n hn0 (hnY.trans hsize)
  obtain ⟨hmax,hL2⟩ := endpoint_fourier_bounds hB ha hX hD.le hM0 g w hdom' hw
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hBne := hB0.ne'
  have hXne := hX.ne'
  have hane := ha.ne'
  constructor
  · intro θ
    refine (hmax θ).trans ?_
    calc
      _ ≤ (D*M/((B : ℝ)*(a*X)))*(K₁*(b*X)) :=
        mul_le_mul_of_nonneg_left (hfirstB _ hY hlogY) (by positivity)
      _ = _ := by field_simp
  · refine hL2.trans ?_
    calc
      _ ≤ (D*M/((B : ℝ)*(a*X)))^2*(K₂*(b*X)*(B : ℝ)^(1/4+ε)) :=
        mul_le_mul_of_nonneg_left (hsecondB _ hY hlogY) (sq_nonneg _)
      _ = _ := by
        have hp : (B : ℝ)^(1/4+ε) = (B : ℝ)^(-7/4+ε)*(B : ℝ)^2 := by
          rw [← Real.rpow_natCast,← Real.rpow_add hB0]
          congr 1
          norm_num
          ring
        rw [hp]
        field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DiscardedRegionBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paying for a discarded frequency region by endpoint square moments -/

namespace JointDickman
open MeasureTheory

/-- Young's inequality gives the needed two-endpoint estimate without
introducing a separate square root of each Parseval bound. -/
theorem discarded_region_integral_bound {F G H : ℝ → ℂ} {E : Set ℝ} {D : ℝ}
    (hE : MeasurableSet E) (hsub : E ⊆ Set.Ioc 0 1) (hD : 0 ≤ D)
    (hF : Continuous F) (hG : Continuous G)
    (hH : ∀ θ ∈ E, ‖H θ‖ ≤ D) :
    ‖∫ θ in E, F θ*G θ*H θ‖ ≤
      D/2*((∫ θ in (0 : ℝ)..1, ‖F θ‖^2)+(∫ θ in (0 : ℝ)..1, ‖G θ‖^2)) := by
  let U : ℝ → ℝ := fun θ => D/2*(‖F θ‖^2+‖G θ‖^2)
  have hU : Continuous U := continuous_const.mul ((hF.norm.pow 2).add (hG.norm.pow 2))
  have hU0 (θ : ℝ) : 0 ≤ U θ := by dsimp [U] <;> positivity
  have hUi : IntegrableOn U (Set.Ioc 0 1) := (hU.intervalIntegrable 0 1).1
  have hUE : IntegrableOn U E := hUi.mono_set hsub
  have hbound (θ : ℝ) (hθ : θ ∈ E) : ‖F θ*G θ*H θ‖ ≤ U θ := by
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (‖F θ‖*‖G θ‖)*D := mul_le_mul_of_nonneg_left (hH θ hθ) (by positivity)
      _ ≤ U θ := by
        have h := sq_nonneg (‖F θ‖-‖G θ‖)
        have hh : ‖F θ‖*‖G θ‖ ≤ (‖F θ‖^2+‖G θ‖^2)/2 := by nlinarith
        have hh' := mul_le_mul_of_nonneg_right hh hD
        dsimp [U]
        nlinarith
  calc
    _ ≤ ∫ θ in E, ‖F θ*G θ*H θ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in E, U θ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) hUE
      (by filter_upwards [ae_restrict_mem hE] with θ hθ; exact hbound θ hθ)
    _ ≤ ∫ θ in Set.Ioc 0 1, U θ := setIntegral_mono_set hUi
      (Filter.Eventually.of_forall hU0) (Filter.Eventually.of_forall hsub)
    _ = _ := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      dsimp [U]
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add]
      · exact (hF.norm.pow 2).intervalIntegrable 0 1
      · exact (hG.norm.pow 2).intervalIntegrable 0 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointFourierReflection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reflecting the second endpoint in the Fourier integral -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem finiteAdditiveSum_neg_real (s : Finset ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    finiteAdditiveSum s (fun n => (c n : ℂ)) (-θ) =
      conj (finiteAdditiveSum s (fun n => (c n : ℂ)) θ) := by
  unfold finiteAdditiveSum
  rw [map_sum]
  apply sum_congr rfl
  intro n _
  rw [map_mul,Complex.conj_ofReal,additivePhase_conj]
  congr 2
  ring

theorem endpointFourierSum_neg_norm (B : ℕ) (a b X : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) (θ : ℝ) :
    ‖endpointFourierSum B a b X g w (-θ)‖ = ‖endpointFourierSum B a b X g w θ‖ := by
  unfold endpointFourierSum
  rw [finiteAdditiveSum_neg_real]
  exact Complex.norm_conj _

theorem endpointFourierSum_continuous (B : ℕ) (a b X : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) :
    Continuous (endpointFourierSum B a b X g w) :=
  finiteAdditiveSum_continuous _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OscillatoryError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit modulus and frequency losses in the coefficient estimate -/

namespace JointDickman

/-- A saving of 79 powers absorbs the modulus and frequency ranges in
manuscript equation (1), leaving 50 powers. -/
theorem oscillatory_error_bookkeeping {B q K X a b M N ξ : ℝ}
    (hB : 1 ≤ B) (hq : q ≤ B ^ (15 : ℝ))
    (hK : 0 ≤ K) (hX : 0 < X) (hb : 0 ≤ b) (hab : a ≤ b)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hξ : |ξ| ≤ B ^ (14 : ℝ)) :
    q * (K * B ^ (-79 : ℝ) * (b * X) *
        (2 * M + (N + 2 * Real.pi * |ξ| * M) / X * (b * X - a * X))) ≤
      (K * b * (2 * M + (N + 2 * Real.pi * M) * (b - a))) * X * B ^ (-50 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have h14 : 1 ≤ B ^ (14 : ℝ) := Real.one_le_rpow hB (by norm_num)
  have hC : 0 ≤ 2 * M + (N + 2 * Real.pi * M) * (b - a) := by positivity
  have hfreq : N + 2 * Real.pi * |ξ| * M ≤ B ^ (14 : ℝ) * (N + 2 * Real.pi * M) := by
    have h1 := mul_le_mul_of_nonneg_left hξ (show 0 ≤ 2 * Real.pi * M by positivity)
    have h2 := mul_le_mul_of_nonneg_right h14 hN
    nlinarith
  have hbracket : 2 * M + (N + 2 * Real.pi * |ξ| * M) * (b - a) ≤
      B ^ (14 : ℝ) * (2 * M + (N + 2 * Real.pi * M) * (b - a)) := by
    have h1 := mul_le_mul_of_nonneg_right hfreq (sub_nonneg.mpr hab)
    have h2 := mul_le_mul_of_nonneg_right h14 (show 0 ≤ 2 * M by positivity)
    nlinarith
  have hcancel : (N + 2 * Real.pi * |ξ| * M) / X * (b * X - a * X) =
      (N + 2 * Real.pi * |ξ| * M) * (b - a) := by
    field_simp
  rw [hcancel]
  calc
    _ ≤ B ^ (15 : ℝ) * (K * B ^ (-79 : ℝ) * (b * X) *
        (B ^ (14 : ℝ) * (2 * M + (N + 2 * Real.pi * M) * (b - a)))) := by
      apply mul_le_mul hq
      · exact mul_le_mul_of_nonneg_left hbracket (by positivity)
      · positivity
      · positivity
    _ = _ := by
      have hp : B ^ (15 : ℝ) * B ^ (-79 : ℝ) * B ^ (14 : ℝ) = B ^ (-50 : ℝ) := by
        rw [← Real.rpow_add hB0, ← Real.rpow_add hB0]
        norm_num
      calc
        _ = (K * b * (2 * M + (N + 2 * Real.pi * M) * (b - a))) * X *
            (B ^ (15 : ℝ) * B ^ (-79 : ℝ) * B ^ (14 : ℝ)) := by ring
        _ = _ := by rw [hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative partial summation for coefficient tests -/

namespace JointDickman

open MeasureTheory Finset

/-- A C¹ test loses only its value and first-derivative bounds when a
summatory estimate is transferred to a weighted sum. -/
theorem weighted_counting_error_le (w : ℕ → ℝ) (F φ φ' : ℝ → ℝ)
    {a b ε M N : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hε : 0 ≤ ε) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.Icc a b)) (hF : ContinuousOn F (Set.Icc a b))
    (hvalue : ∀ t ∈ Set.Icc a b, |φ t| ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, |φ' t| ≤ N)
    (herr : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤ ε * t) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * w n) -
      (φ b * F b - φ a * F a - ∫ t in a..b, φ' t * F t)| ≤
      ε * b * (2 * M + N * (b - a)) := by
  have hd : ContinuousOn (deriv φ) (Set.Icc a b) := hφ'.congr (fun t ht => (hφ t ht).deriv)
  have hAbel := sum_mul_eq_sub_sub_integral_mul (c := w) ha hab
    (fun t ht => (hφ t ht).differentiableAt) hd.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  have hiw : IntervalIntegrable (fun t => φ' t * finiteCountingFunction w t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact integrableOn_mul_sum_Icc w ha hφ'.integrableOn_Icc
  have hiF : IntervalIntegrable (fun t => φ' t * F t) volume a b :=
    (hφ'.mul hF).intervalIntegrable_of_Icc hab
  have hid : (∫ t in a..b, deriv φ t * ∑ n ∈ Icc 0 ⌊t⌋₊, w n) =
      ∫ t in a..b, φ' t * finiteCountingFunction w t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    dsimp only
    rw [(hφ t ht).deriv]
    rfl
  rw [hid] at hAbel
  have hdiff : (∫ t in a..b, φ' t * finiteCountingFunction w t) -
      (∫ t in a..b, φ' t * F t) =
      ∫ t in a..b, φ' t * (finiteCountingFunction w t - F t) := by
    rw [← intervalIntegral.integral_sub hiw hiF]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hE (t : ℝ) (ht : t ∈ Set.Icc a b) : |finiteCountingFunction w t - F t| ≤ ε * b :=
    (herr t ht).trans (mul_le_mul_of_nonneg_left ht.2 hε)
  have hboundary (t : ℝ) (ht : t ∈ Set.Icc a b) :
      |φ t * (finiteCountingFunction w t - F t)| ≤ M * (ε * b) := by
    rw [abs_mul]
    exact mul_le_mul (hvalue t ht) (hE t ht) (abs_nonneg _) hM
  have hint : |∫ t in a..b, φ' t * (finiteCountingFunction w t - F t)| ≤ N * (ε * b) * (b - a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun t => φ' t * (finiteCountingFunction w t - F t))
      (C := N * (ε * b)) (fun t ht => by
        have ht' : t ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc ht
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hderiv t ht') (hE t ht') (abs_nonneg _) hN)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have heq : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * w n) -
      (φ b * F b - φ a * F a - ∫ t in a..b, φ' t * F t) =
      φ b * (finiteCountingFunction w b - F b) - φ a * (finiteCountingFunction w a - F a) -
        ∫ t in a..b, φ' t * (finiteCountingFunction w t - F t) := by
    rw [← hdiff, hAbel]
    unfold finiteCountingFunction
    ring
  rw [heq]
  calc
    _ ≤ |φ b * (finiteCountingFunction w b - F b)| +
        |φ a * (finiteCountingFunction w a - F a)| +
        |∫ t in a..b, φ' t * (finiteCountingFunction w t - F t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ M * (ε * b) + M * (ε * b) + N * (ε * b) * (b - a) :=
      add_le_add (add_le_add (hboundary b ⟨hab, le_rfl⟩) (hboundary a ⟨le_rfl, hab⟩)) hint
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughHarmonicLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The harmonic rough coefficient law

Partial summation of the proved moving-cutoff expansion gives the
weighted interval law needed for the independent prime-product model.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughDensityPolynomial_continuousAt (c : ℕ → ℝ) (E : Finset ℕ)
    (z : ℝ) (H : ℕ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (roughDensityPolynomial c E z H) L := by
  apply tendsto_finsetSum
  intro j _
  apply continuousAt_const.mul
  apply ContinuousAt.add
  · exact continuousAt_id.rpow_const (Or.inl hL.ne')
  · exact continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hL.ne'))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_WeightedCoefficientLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth real tests of the coefficient progression law -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

open Classical in
theorem finiteCountingFunction_coefficient_residue {q : ℕ}
    (B : ℕ) (r : ZMod q) (Y : ℝ) :
    finiteCountingFunction (fun n => if (n : ZMod q) = r then coefficientWeight B n else 0) Y =
      progressionSum (Ioc 0 ⌊Y⌋₊) (coefficientWeight B) r := by
  unfold finiteCountingFunction progressionSum
  rw [← Ioc_insert_left (Nat.zero_le ⌊Y⌋₊), sum_insert left_notMem_Ioc]
  simp [coefficientWeight]

open Classical in
/-- Weighted equidistribution in one unit class. The constants and
expansion order are independent of the smooth test. -/
theorem coefficientProgression_smooth_test
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b : ℝ, 9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) → ∀ r : (ZMod q)ˣ,
      ∀ φ φ' : ℝ → ℝ, ∀ M N : ℝ, 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, |φ t| ≤ M) → (∀ t ∈ Set.Icc a b, |φ' t| ≤ N) →
      |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then φ n * coefficientWeight B n else 0) -
        (∫ t in a..b, φ t * coefficientDensity c H B (Real.log t / B)) / q.totient| ≤
        K * (B : ℝ) ^ (-D) * b * (2 * M + N * (b - a)) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := coefficientProgression_expansion hSD hSW hM hD
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro a b ha hab hloga q _ hq r φ φ' M N hM0 hN hφ hφ' hvalue hderiv
  let w : ℕ → ℝ := fun n => if (n : ZMod q) = r then coefficientWeight B n else 0
  let F : ℝ → ℝ := fun t => coefficientModel c H B t / q.totient
  let F' : ℝ → ℝ := fun t => coefficientDensity c H B (Real.log t / B) / q.totient
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt F (F' t) t :=
    (hasDerivAt_coefficientModel c H B hB (by linarith [ht.1])).div_const _
  have hFc : ContinuousOn F (Set.Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hF'c : ContinuousOn F' (Set.Icc a b) := by
    have heq : F' = fun t => coefficientScale B *
        roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) H (Real.log t) / q.totient := by
      funext t
      simp only [F', coefficientDensity, mul_div_cancel₀ _ hB0]
    rw [heq]
    intro t ht
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact ((continuousAt_const.mul ((roughDensityPolynomial_continuousAt c _ _ H hlogt).comp
      (Real.continuousAt_log (by linarith [ht.1] : t ≠ 0)))).div_const _).continuousWithinAt
  have he : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤
      (K * (B : ℝ) ^ (-D)) * t := by
    intro t ht
    have hlogt := hloga.trans (Real.log_le_log (by linarith : 0 < a) ht.1)
    simpa only [w, F, finiteCountingFunction_coefficient_residue, mul_right_comm] using
      hboundB t hlogt (ha.trans ht.1) q hq r
  have htest := weighted_counting_error_le w F φ φ' (by linarith) hab
    (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg B) _)) hM0 hN hφ hφ' hFc hvalue hderiv he
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hφ t (Set.uIcc_of_le hab ▸ ht))
    (fun t ht => hd t (Set.uIcc_of_le hab ▸ ht))
    (hφ'.intervalIntegrable_of_Icc hab) (hF'c.intervalIntegrable_of_Icc hab)
  rw [← hparts] at htest
  have hsum : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, φ n * w n) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then φ n * coefficientWeight B n else 0 := by
    apply sum_congr rfl
    intro n _
    simp only [w, mul_ite, mul_zero]
  rw [hsum] at htest
  have hint : (∫ t in a..b, φ t * F' t) =
      (∫ t in a..b, φ t * coefficientDensity c H B (Real.log t / B)) / q.totient := by
    simp only [F', ← mul_div_assoc, intervalIntegral.integral_div]
  rw [hint] at htest
  exact htest

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ComplexCoefficientLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex smooth tests of the actual coefficient progression law -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

private theorem density_log_continuousOn (c : ℕ → ℝ) (H B : ℕ)
    (hB : 0 < B) {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t => coefficientDensity c H B (Real.log t / B)) (Set.Icc a b) := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have heq : (fun t => coefficientDensity c H B (Real.log t / B)) =
      fun t => coefficientScale B * roughDensityPolynomial c
        (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) H (Real.log t) := by
    funext t
    simp only [coefficientDensity, mul_div_cancel₀ _ hB0]
  rw [heq]
  intro t ht
  exact (continuousAt_const.mul ((roughDensityPolynomial_continuousAt c _ _ H
    (Real.log_pos (ha.trans_le ht.1))).comp
      (Real.continuousAt_log (by linarith [ht.1] : t ≠ 0)))).continuousWithinAt

open Classical in
/-- The same fixed expansion works for all complex C¹ tests; only two real
component estimates are used. -/
theorem coefficientProgression_complex_test
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b : ℝ, 9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) → ∀ r : (ZMod q)ˣ,
      ∀ φ φ' : ℝ → ℂ, ∀ M N : ℝ, 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M) → (∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N) →
      ‖(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)‖ ≤
        K * (B : ℝ) ^ (-D) * b * (2 * M + N * (b - a)) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := coefficientProgression_smooth_test hSD hSW hM hD
  refine ⟨c, hc, hcpos, H, 2 * K, by positivity, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro a b ha hab hloga q _ hq r φ φ' M N hM0 hN hφ hφ' hvalue hderiv
  have hre := hboundB a b ha hab hloga q hq r (fun t => (φ t).re)
    (fun t => (φ' t).re) M N hM0 hN
    (fun t ht => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hφ t ht))
    (Complex.continuous_re.comp_continuousOn hφ')
    (fun t ht => (Complex.abs_re_le_norm _).trans (hvalue t ht))
    (fun t ht => (Complex.abs_re_le_norm _).trans (hderiv t ht))
  have him := hboundB a b ha hab hloga q hq r (fun t => (φ t).im)
    (fun t => (φ' t).im) M N hM0 hN
    (fun t ht => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hφ t ht))
    (Complex.continuous_im.comp_continuousOn hφ')
    (fun t ht => (Complex.abs_im_le_norm _).trans (hvalue t ht))
    (fun t ht => (Complex.abs_im_le_norm _).trans (hderiv t ht))
  have hcont : ContinuousOn φ (Set.Icc a b) :=
    fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun t => φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) volume a b :=
    (hcont.mul (Complex.continuous_ofReal.comp_continuousOn
      (density_log_continuousOn c H B hB (by linarith)))).intervalIntegrable_of_Icc hab
  have hrint := intervalIntegral.intervalIntegral_re hint
  have hiint := intervalIntegral.intervalIntegral_im hint
  change (∫ t in a..b, (φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)).re) =
    (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)).re at hrint
  change (∫ t in a..b, (φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)).im) =
    (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)).im at hiint
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add] at hrint hiint
  have hreq : ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)).re =
      (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          (φ n).re * coefficientWeight B n else 0) -
        (∫ t in a..b, (φ t).re * coefficientDensity c H B (Real.log t / B)) / q.totient := by
    simp only [Complex.sub_re, ← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.re_sum, apply_ite Complex.re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
      mul_zero, sub_zero, ← hrint]
  have hieq : ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)).im =
      (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          (φ n).im * coefficientWeight B n else 0) -
        (∫ t in a..b, (φ t).im * coefficientDensity c H B (Real.log t / B)) / q.totient := by
    simp only [Complex.sub_im, ← Complex.ofReal_natCast, Complex.div_ofReal_im, Complex.im_sum, apply_ite Complex.im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im,
      mul_zero, zero_add, ← hiint]
  calc
    _ ≤ |((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)).re| +
        |((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, if (n : ZMod q) = r then
          φ n * (coefficientWeight B n : ℂ) else 0) -
        (∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
          (q.totient : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by rw [hreq, hieq]; nlinarith [hre, him]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UnitResidueSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing a unit-supported weight against residue phases -/

namespace JointDickman

open Finset

open Classical in
theorem sum_unit_residues {q : ℕ} [NeZero q] (S : Finset ℕ)
    (f : ℕ → ℂ) (ψ : ZMod q → ℂ)
    (hunit : ∀ n ∈ S, f n ≠ 0 → IsUnit (n : ZMod q)) :
    ∑ n ∈ S, ψ (n : ZMod q) * f n =
      ∑ r : (ZMod q)ˣ, ψ r * ∑ n ∈ S, if (n : ZMod q) = r then f n else 0 := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  by_cases hf : f n = 0
  · simp [hf]
  obtain ⟨r, hr⟩ := hunit n hn hf
  rw [← hr]
  symm
  rw [sum_eq_single r]
  · simp
  · intro s _ hsr
    have hne : (r : ZMod q) ≠ s := fun h => hsr (Units.val_injective h.symm)
    simp [hne]
  · simp

open Classical in
theorem sum_unit_residue_error {q : ℕ} [NeZero q] (S : Finset ℕ)
    (f : ℕ → ℂ) (ψ : ZMod q → ℂ) (I : ℂ) {E : ℝ}
    (hunit : ∀ n ∈ S, f n ≠ 0 → IsUnit (n : ZMod q))
    (hψ : ∀ r : (ZMod q)ˣ, ‖ψ r‖ ≤ 1)
    (hE : ∀ r : (ZMod q)ˣ,
      ‖(∑ n ∈ S, if (n : ZMod q) = r then f n else 0) - I‖ ≤ E) :
    ‖(∑ n ∈ S, ψ (n : ZMod q) * f n) - (∑ r : (ZMod q)ˣ, ψ r) * I‖ ≤
      q.totient * E := by
  rw [sum_unit_residues S f ψ hunit, sum_mul, ← sum_sub_distrib]
  calc
    _ ≤ ∑ r : (ZMod q)ˣ,
        ‖ψ r * (∑ n ∈ S, if (n : ZMod q) = r then f n else 0) - ψ r * I‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : (ZMod q)ˣ, E := by
      apply sum_le_sum
      intro r _
      rw [← mul_sub, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hψ r) (norm_nonneg _)).trans
        (by simpa using hE r)
    _ = _ := by simp [ZMod.card_units_eq_totient]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicCoefficientLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient estimates against bounded periodic phases -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

theorem coefficientWeight_isUnit {B q n : ℕ} [NeZero q]
    (hq : q ≤ auxiliaryCutoff B) (hn : coefficientWeight B n ≠ 0) :
    IsUnit (n : ZMod q) := by
  apply (ZMod.isUnit_iff_coprime n q).mpr
  apply roughSquarefreeWeight_coprime (NeZero.ne q) hq (1 / 2)
  exact (mul_ne_zero_iff.mp hn).2

open Classical in
/-- Summing unit progressions costs at most the modulus. The bounded
periodic phase is arbitrary, so additive phases are included. -/
theorem coefficient_periodic_smooth_test
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b : ℝ, 9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ ψ : ZMod q → ℂ, (∀ r : (ZMod q)ˣ, ‖ψ r‖ ≤ 1) →
      ∀ φ φ' : ℝ → ℂ, ∀ M N : ℝ, 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc a b, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, ‖φ t‖ ≤ M) → (∀ t ∈ Set.Icc a b, ‖φ' t‖ ≤ N) →
      ‖(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ψ (n : ZMod q) *
          (φ n * (coefficientWeight B n : ℂ))) -
        (∑ r : (ZMod q)ˣ, ψ r) *
          ((∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
            (q.totient : ℂ))‖ ≤
        (q : ℝ) * (K * (B : ℝ) ^ (-D) * b * (2 * M + N * (b - a))) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := coefficientProgression_complex_test hSD hSW hM hD
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro a b ha hab hloga q _ hq ψ hψ φ φ' M N hM0 hN hφ hφ' hvalue hderiv
  have hBP : (B : ℝ) ^ (100 : ℝ) ≤ auxiliaryCutoff B := by
    calc
      (B : ℝ) ^ (100 : ℝ) = (B : ℝ) ^ (100 : ℕ) := by norm_num
      _ ≤ (B : ℝ) ^ (1000 : ℕ) :=
        pow_le_pow_right₀ (by exact_mod_cast hB) (by omega)
      _ = auxiliaryCutoff B := by simp only [auxiliaryCutoff, Nat.cast_pow]
  have hqP : q ≤ auxiliaryCutoff B := by exact_mod_cast hq.trans hBP
  have hunit : ∀ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
      φ n * (coefficientWeight B n : ℂ) ≠ 0 → IsUnit (n : ZMod q) := by
    intro n _ hn
    apply coefficientWeight_isUnit hqP
    intro hz
    simp only [hz, Complex.ofReal_zero, mul_zero, ne_eq, not_true_eq_false] at hn
  have hest := sum_unit_residue_error (Ioc ⌊a⌋₊ ⌊b⌋₊)
    (fun n => φ n * (coefficientWeight B n : ℂ)) ψ
    ((∫ t in a..b, φ t * (coefficientDensity c H B (Real.log t / B) : ℂ)) /
      (q.totient : ℂ)) hunit hψ
    (fun r => hboundB a b ha hab hloga q hq r φ φ' M N hM0 hN hφ hφ' hvalue hderiv)
  refine hest.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q) ?_)
  exact mul_nonneg (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg B) _))
    (by linarith)) (add_nonneg (by positivity) (mul_nonneg hN (sub_nonneg.mpr hab)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ScaledCoefficientLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scaled coefficient law with explicit oscillatory savings -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

open Classical in
/-- The analytic estimate in equation (1), before evaluating the finite
unit-phase sum. The expansion order is independent of the smooth test. -/
theorem coefficient_scaled_oscillatory_test
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ a b X : ℝ, 0 < a → a ≤ b → 0 < X → 9 ≤ a * X →
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log (a * X) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (15 : ℝ) →
      ∀ ψ : ZMod q → ℂ, (∀ r : (ZMod q)ˣ, ‖ψ r‖ ≤ 1) →
      ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) → |ξ| ≤ (B : ℝ) ^ (14 : ℝ) →
      ‖(∑ n ∈ Ioc ⌊a * X⌋₊ ⌊b * X⌋₊, ψ (n : ZMod q) *
          (scaledOscillatoryTest w ξ X n * (coefficientWeight B n : ℂ))) -
        (X : ℂ) * ((∑ r : (ZMod q)ˣ, ψ r) / (q.totient : ℂ)) *
          ∫ s in a..b, oscillatoryTest w ξ s *
            (coefficientDensity c H B (Real.log (s * X) / B) : ℂ)‖ ≤
        (K * b * (2 * M + (N + 2 * Real.pi * M) * (b - a))) * X * (B : ℝ) ^ (-50 : ℝ) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ :=
    coefficient_periodic_smooth_test hSD hSW hM (D := 79) (by norm_num)
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro a b X ha hab hX haX hloga q _ hq ψ hψ w w' M N ξ hM0 hN hw hw' hwbound hw'bound hξ
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hq100 : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) :=
    hq.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num))
  have hcw : Continuous w := continuous_iff_continuousAt.mpr (fun t => (hw t).continuousAt)
  have htest := hboundB (a * X) (b * X) haX
    (mul_le_mul_of_nonneg_right hab hX.le) hloga q hq100 ψ hψ
    (scaledOscillatoryTest w ξ X) (scaledOscillatoryTestDeriv w w' ξ X)
    M ((N + 2 * Real.pi * |ξ| * M) / X) hM0 (by positivity)
    (fun t _ => hasDerivAt_scaledOscillatoryTest (hw (t / X)))
    (scaledOscillatoryTestDeriv_continuous hcw hw' ξ X).continuousOn
    (fun t _ => scaledOscillatoryTest_norm_le (hwbound (t / X)))
    (fun t _ => scaledOscillatoryTestDeriv_norm_le hX (hwbound (t / X)) (hw'bound (t / X)))
  have hint := scaledOscillatoryTest_integral w
    (fun t => (coefficientDensity c H B (Real.log t / B) : ℂ)) ξ a b X hX.ne'
  rw [hint] at htest
  have hmain : (∑ r : (ZMod q)ˣ, ψ r) *
        ((X : ℂ) * (∫ s in a..b, oscillatoryTest w ξ s *
            (coefficientDensity c H B (Real.log (s * X) / B) : ℂ)) / (q.totient : ℂ)) =
      (X : ℂ) * ((∑ r : (ZMod q)ˣ, ψ r) / (q.totient : ℂ)) *
        ∫ s in a..b, oscillatoryTest w ξ s *
          (coefficientDensity c H B (Real.log (s * X) / B) : ℂ) := by ring
  rw [hmain] at htest
  exact htest.trans (oscillatory_error_bookkeeping hB1 hq hK hX
    (ha.le.trans hab) hab hM0 hN hξ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_OscillatoryCoefficientLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Manuscript equation (1): the oscillatory coefficient law -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

open Classical in
/-- Equation (1) follows from the three cited arithmetic inputs. The
expansion is fixed before the test and its support are chosen. -/
theorem coefficient_oscillatory_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9 / 10 : ℝ) * B) ((11 / 5 : ℝ) * B) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (15 : ℝ) → ∀ u : (ZMod q)ˣ,
      ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) → |ξ| ≤ (B : ℝ) ^ (14 : ℝ) →
      ‖coefficientExponentialSum B q u ξ X w -
        (X : ℂ) * ((μ q : ℂ) / (q.totient : ℂ)) *
          ∫ s : ℝ, (w s : ℂ) * (coefficientDensity c H B (Real.log (s * X) / B) : ℂ) *
            additivePhase (ξ * s)‖ ≤
        (K * b * (2 * M + (N + 2 * Real.pi * M) * (b - a))) * X * (B : ℝ) ^ (-50 : ℝ) := by
  obtain ⟨c, hc, hcpos, H, K, hK, hbound⟩ := coefficient_scaled_oscillatory_test hSD hSW hM
  refine ⟨c, hc, hcpos, H, K, hK, ?_⟩
  intro a b ha hab
  filter_upwards [hbound, coefficient_support_window ha] with B hboundB hwindow
  intro X hX hlogX q _ hq u w w' M N ξ hM0 hN hw hw' hwbound hw'bound hsupport hξ
  obtain ⟨haX, hloga⟩ := hwindow X hX hlogX.1
  have htest := hboundB a b X ha hab hX haX hloga q hq
    (fun r => ZMod.stdAddChar ((u : ZMod q) * r))
    (fun r => (norm_stdAddChar _).le) w w' M N ξ hM0 hN hw hw' hwbound hw'bound hξ
  rw [ramanujan_sum_unit_frequency u] at htest
  have hsum := tsum_eq_Ioc_of_scaled_support ha.le hab hX hsupport
    (fun n => ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) *
      (scaledOscillatoryTest w ξ X n * (coefficientWeight B n : ℂ)))
    (fun n hn => by simp only [scaledOscillatoryTest, oscillatoryTest, hn,
      Complex.ofReal_zero, zero_mul, mul_zero])
  rw [← hsum, oscillatory_integral_eq_integral hab hsupport] at htest
  have heq : (∑' n : ℕ, ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) *
      (scaledOscillatoryTest w ξ X n * (coefficientWeight B n : ℂ))) =
      coefficientExponentialSum B q u ξ X w := by
    unfold coefficientExponentialSum
    apply tsum_congr
    intro n
    rw [scaledOscillatoryTest, oscillatoryTest, unit_nat_phase, additivePhase_add]
    have ht : ξ * ((n : ℝ) / X) = ξ * n / X := by ring
    rw [ht]
    ring
  rw [heq] at htest
  have hint : (∫ s : ℝ, oscillatoryTest w ξ s *
      (coefficientDensity c H B (Real.log (s * X) / B) : ℂ)) =
      ∫ s : ℝ, (w s : ℂ) * (coefficientDensity c H B (Real.log (s * X) / B) : ℂ) *
        additivePhase (ξ * s) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by unfold oscillatoryTest; ring)
  rw [hint] at htest
  exact htest

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MajorArcPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measurable major-arc partition of the exact Fourier integral -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

theorem majorArcRegion_eq_iUnion (B j : ℕ) (X : ℝ) :
    majorArcRegion B j X = ⋃ r : ℚ, rationalArcPiece B j X r := by
  ext θ
  simp only [majorArcRegion,rationalArcPiece,mem_ofPred_eq,mem_iUnion,InRationalArc]
  aesop

theorem rationalArcPiece_measurable (B j : ℕ) (X : ℝ) (r : ℚ) :
    MeasurableSet (rationalArcPiece B j X r) := by
  by_cases hr : (r.den : ℝ) ≤ (B : ℝ)^12
  · have hs : MeasurableSet {θ : ℝ | |-(j : ℝ)*θ-(r : ℝ)| ≤ (B : ℝ)^13/X} :=
      (isClosed_le ((continuous_const.mul continuous_id).sub continuous_const).abs
        continuous_const).measurableSet
    convert (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)).inter hs using 1
    all_goals try with_reducible_and_instances rfl
    ext θ
    simp [rationalArcPiece,hr]
  · simp [rationalArcPiece,hr]

theorem majorArcRegion_measurable (B j : ℕ) (X : ℝ) :
    MeasurableSet (majorArcRegion B j X) := by
  rw [majorArcRegion_eq_iUnion]
  exact MeasurableSet.iUnion (rationalArcPiece_measurable B j X)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TruncatedMajorRegion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting the major arcs at a finite denominator -/

namespace JointDickman
open Filter MeasureTheory Set Function
open scoped Topology

theorem smallMajorArcRegion_measurable (B j : ℕ) (X : ℝ) (Q : ℕ) :
    MeasurableSet (smallMajorArcRegion B j X Q) := by
  apply MeasurableSet.iUnion
  intro r
  split_ifs
  · exact rationalArcPiece_measurable B j X r
  · exact MeasurableSet.empty

theorem largeMajorArcRegion_measurable (B j : ℕ) (X : ℝ) (Q : ℕ) :
    MeasurableSet (largeMajorArcRegion B j X Q) :=
  (majorArcRegion_measurable B j X).diff (smallMajorArcRegion_measurable B j X Q)

theorem largeMajorArcRegion_witness {B j Q : ℕ} {X x : ℝ}
    (hx : x ∈ largeMajorArcRegion B j X Q) :
    ∃ r : ℚ, Q < r.den ∧ (r.den : ℝ) ≤ (B : ℝ)^12 ∧
      |-(j : ℝ)*x-(r : ℝ)| ≤ (B : ℝ)^13/X := by
  obtain ⟨r,hr,hnear⟩ := hx.1.2
  refine ⟨r,?_,hr,hnear⟩
  by_contra h
  have hq : r.den ≤ Q := le_of_not_gt h
  apply hx.2
  apply mem_iUnion.mpr
  exact ⟨r,by rw [ite_eq_left hq]; exact ⟨hx.1.1,hr,hnear⟩⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArcCoefficientIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact coefficient phase on a lifted major arc -/

namespace JointDickman
open Finset

theorem additivePhase_int (k : ℤ) : additivePhase (k : ℝ) = 1 := by
  unfold additivePhase
  have he : ((2*Real.pi*(k : ℝ) : ℝ) : ℂ)*Complex.I =
      (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by push_cast <;> ring
  rw [he,Complex.exp_int_mul_two_pi_mul_I]

theorem additivePhase_add_int (x : ℝ) (k : ℤ) : additivePhase (x+k) = additivePhase x := by
  rw [additivePhase_add,additivePhase_int,mul_one]

theorem coefficientExponentialSum_eq_smooth (B q : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (ξ X : ℝ) (w : ℝ → ℝ) :
    coefficientExponentialSum B q u ξ X w =
      smoothCoefficientAdditiveSum B X (((u : ZMod q).val : ℝ)/q+ξ/X) w := by
  unfold coefficientExponentialSum smoothCoefficientAdditiveSum
  apply tsum_congr
  intro n
  congr 2
  ring

theorem smoothCoefficientAdditiveSum_add_int (B : ℕ) (X θ : ℝ) (w : ℝ → ℝ) (k : ℤ) :
    smoothCoefficientAdditiveSum B X (θ+k) w = smoothCoefficientAdditiveSum B X θ w := by
  unfold smoothCoefficientAdditiveSum
  apply tsum_congr
  intro n
  have he : (n : ℝ)*(θ+k) = n*θ+((n : ℤ)*k : ℤ) := by push_cast <;> ring
  rw [he,additivePhase_add_int]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDensityBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform boundedness of the actual A0 density away from zero -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem auxiliary_half_normalizer_pos (B : ℕ) :
    0 < primeNormalizer (auxiliaryPrimes B) (1/2) := by
  unfold primeNormalizer
  apply prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
  exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < p)).mpr (by norm_num <;> linarith))

theorem coefficientDensity_eq_scaled (c : ℕ → ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    coefficientDensity c H B s =
      (coefficientScale B / (primeNormalizer (auxiliaryPrimes B) (1/2)*B))*
        scaledRoughDensity c (1/2) H B s := by
  rw [scaledRoughDensity_eq c (1/2) H B hB hs]
  unfold coefficientDensity
  have hQ := (auxiliary_half_normalizer_pos B).ne'
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

theorem coefficientDensity_eventually_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    {δ : ℝ} (hδ : 0 < δ) (H : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ s : ℝ, δ ≤ s →
      |coefficientDensity c H B s| ≤ K := by
  obtain ⟨M,hM0,L,hbound⟩ := scaledRoughDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1/2) hδ H
  let J : ℝ := (4 : ℝ)^(1/2 : ℝ)+1
  have hJ : 0 ≤ J := by dsimp [J] <;> positivity
  have hquot : ∀ᶠ B : ℕ in atTop,
      |coefficientScale B/(primeNormalizer (auxiliaryPrimes B) (1/2)*B)| ≤ J := by
    have hh := (roughMeanNormalization_quotient_tendsto hM
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).abs
    have hpos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (1/2 : ℝ)
    have he := hh.eventually (eventually_le_nhds (lt_add_one |(4 : ℝ)^(1/2 : ℝ)|))
    simpa only [← coefficientScale_eq_roughMeanNormalization,abs_of_pos hpos] using he
  refine ⟨J*M,mul_nonneg hJ hM0,?_⟩
  filter_upwards [hbound,hquot,eventually_gt_atTop 0] with B hboundB hquotB hB
  intro s hs
  rw [coefficientDensity_eq_scaled c H B hB (hδ.trans_le hs),abs_mul]
  exact mul_le_mul hquotB (hboundB.1 s hs) (abs_nonneg _) hJ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientLogBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Totient denominators on the major arcs -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem totient_eq_prime_product_real (q : ℕ) :
    (q.totient : ℝ) = q*∏ p ∈ q.primeFactors, (1-1/(p : ℝ)) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,
    Rat.cast_one,Rat.cast_inv,one_div] using h

/-- Only moduli up to the fixed B^15 major-arc cutoff are needed. -/
theorem totient_log_bound (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ q : ℕ,
      0 < q → q ≤ B^15 → (q : ℝ) ≤ K*Real.log B*q.totient := by
  let κ := Real.exp (-Real.eulerMascheroniConstant)/2
  have hκ : 0 < κ := half_pos (Real.exp_pos _)
  have hlim := hMP.comp ((tendsto_pow_atTop (by decide : (15 : ℕ) ≠ 0)).comp
    tendsto_natCast_atTop_atTop)
  have hsmall := hlim.eventually (eventually_ge_nhds (show κ < Real.exp (-Real.eulerMascheroniConstant) by
    dsimp [κ] <;> linarith [Real.exp_pos (-Real.eulerMascheroniConstant)]))
  refine ⟨15/κ,by positivity,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop 2] with B hproduct hB
  intro q hq hqB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hlog : 0 ≤ Real.log ((B : ℝ)^15) := Real.log_nonneg (one_le_pow₀ hB1)
  have hset : q.primeFactors ⊆ Nat.primesLE (B^15) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hqB,Nat.prime_of_mem_primeFactors hp⟩
  have hprod : (∏ p ∈ Nat.primesLE (B^15), (1-1/(p : ℝ))) ≤
      ∏ p ∈ q.primeFactors, (1-1/(p : ℝ)) := by
    apply prod_le_prod_of_subset_of_le_one hset
    · intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp1)
    · intro p _ _
      exact sub_le_self _ (by positivity)
  have hprod' : κ ≤ Real.log ((B : ℝ)^15)*
      ∏ p ∈ Nat.primesLE (B^15), (1-1/(p : ℝ)) := by
    simpa only [Function.comp_def,← Nat.cast_pow,Nat.floor_natCast,← primesLE_eq_filter] using hproduct
  have hh := hprod'.trans (mul_le_mul_of_nonneg_left hprod hlog)
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hh'' : (q : ℝ)*κ ≤ (15*Real.log B)*q.totient := by
    refine hh'.trans_eq ?_
    rw [totient_eq_prime_product_real,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  calc
    _ ≤ ((15*Real.log B)*q.totient)/κ := (le_div_iff₀ hκ).mpr hh''
    _ = _ := by ring

/-- The reciprocal totient has the required B^(-0.4+epsilon) saving. -/
theorem majorArc_totient_power (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ q : ℕ, 0 < q → q ≤ B^15 →
      (B : ℝ)^(2/5 : ℝ) ≤ q →
      1/(q.totient : ℝ) ≤ (B : ℝ)^(-2/5+ε) := by
  obtain ⟨K,hK,hbound⟩ := totient_log_bound hMP
  have hlim := ((log_power_div_power_tendsto_zero 1 hε).const_mul K).comp
    tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlim
  filter_upwards [hbound,hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hboundB hsmall hB
  intro q hq hqB hqlo
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr hq)
  have hlogpower : K*Real.log B ≤ (B : ℝ)^ε := by
    apply (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp
    simpa only [Function.comp_def,Real.rpow_one,mul_div_assoc] using hsmall
  have hφ : 1/(q.totient : ℝ) ≤ K*Real.log B/q := by
    apply (div_le_div_iff₀ hφ0 hq0).mpr
    simpa only [one_mul] using hboundB q hq hqB
  calc
    _ ≤ K*Real.log B/q := hφ
    _ ≤ (B : ℝ)^ε/(B : ℝ)^(2/5 : ℝ) :=
      div_le_div₀ (by positivity) hlogpower (Real.rpow_pos_of_pos hB0 _) hqlo
    _ = _ := by rw [← Real.rpow_sub hB0]; congr 1; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_MajorCoefficientBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform norm bound on the coefficient major arcs -/

namespace JointDickman
open Filter Finset MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

theorem compact_density_integral_bound {a b M D ξ : ℝ} {w ρ : ℝ → ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M) (_hD : 0 ≤ D)
    (hw : ∀ t, |w t| ≤ M) (hρ : ∀ t ∈ Set.Icc a b, |ρ t| ≤ D)
    (hsupp : ∀ t, t ≤ a ∨ b < t → w t = 0) :
    ‖∫ s : ℝ, (w s : ℂ)*(ρ s : ℂ)*additivePhase (ξ*s)‖ ≤ M*D*(b-a) := by
  have he : (fun s : ℝ => (w s : ℂ)*(ρ s : ℂ)*additivePhase (ξ*s)) =
      (fun s => oscillatoryTest w ξ s*(ρ s : ℂ)) := by
    funext s
    unfold oscillatoryTest
    ring
  rw [he,← oscillatory_integral_eq_integral hab hsupp ξ (fun s => (ρ s : ℂ))]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := M*D)
    (f := fun s => oscillatoryTest w ξ s*(ρ s : ℂ)) (fun s hs => by
      have hs' : s ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc hs
      rw [norm_mul,oscillatoryTest_norm,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (hw s) (hρ s hs') (abs_nonneg _) hM)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh

theorem coefficient_majorArc_norm_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ)^(15 : ℝ) → ∀ u : (ZMod q)ˣ,
      ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) → |ξ| ≤ (B : ℝ)^(14 : ℝ) →
      ‖coefficientExponentialSum B q u ξ X w‖ ≤
        X*(D*M*(b-a)/q.totient +
          K*b*(2*M+(N+2*Real.pi*M)*(b-a))*(B : ℝ)^(-50 : ℝ)) := by
  obtain ⟨c,hc,_,H,K,hK,hexp⟩ := coefficient_oscillatory_law hSD hSW hM
  obtain ⟨D,hD,hdensity⟩ := coefficientDensity_eventually_bounded hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  refine ⟨D,K,hD,hK,?_⟩
  intro a b ha hab
  filter_upwards [hexp a b ha hab,hdensity,endpoint_scale_window ha,eventually_gt_atTop 0]
    with B hexpB hdensityB hwindow hB
  intro X hX hlog q _ hq u w w' M N ξ hM0 hN hw hw' hbw hbw' hsupp hξ
  have hloga := (hwindow X hX hlog.1 (hlog.2.trans (by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith))).2.1
  have hρ : ∀ s ∈ Set.Icc a b, |coefficientDensity c H B (Real.log (s*X)/B)| ≤ D := by
    intro s hs
    apply hdensityB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    apply (le_div_iff₀ hB0).mpr
    exact hloga.trans (Real.log_le_log (mul_pos ha hX) (mul_le_mul_of_nonneg_right hs.1 hX.le))
  have hI := compact_density_integral_bound hab hM0 hD hbw hρ hsupp (ξ := ξ)
  have hμ : ‖(μ q : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast,Int.cast_one] using
      (show |((μ q : ℤ) : ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q))
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hmain : ‖(X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*
      ∫ s : ℝ, (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)*
        additivePhase (ξ*s)‖ ≤ X*(D*M*(b-a)/q.totient) := by
    rw [norm_mul,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX,
      Complex.norm_natCast]
    have hfrac : ‖(μ q : ℂ)‖/(q.totient : ℝ) ≤ 1/(q.totient : ℝ) :=
      div_le_div_of_nonneg_right hμ hφ.le
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hfrac hX.le) hI
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have herr := hexpB X hX hlog q hq u w w' M N ξ hM0 hN hw hw' hbw hbw' hsupp hξ
  calc
    _ ≤ ‖coefficientExponentialSum B q u ξ X w -
        (X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*
          ∫ s : ℝ, (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)*additivePhase (ξ*s)‖ +
        ‖(X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*
          ∫ s : ℝ, (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)*additivePhase (ξ*s)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ _ := by nlinarith [add_le_add herr hmain]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LargeMajorCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Suppression of coefficient sums on the larger-denominator major arcs -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficient_large_majorArc_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ a b ε : ℝ, 0 < a → a ≤ b → 0 < ε →
      ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ (q : ℕ) [NeZero q], q ≤ B^15 → (B : ℝ)^(2/5 : ℝ) ≤ q →
      ∀ u : (ZMod q)ˣ, ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) → |ξ| ≤ (B : ℝ)^(14 : ℝ) →
      ‖coefficientExponentialSum B q u ξ X w‖ ≤
        (D*M*(b-a)+K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*X*(B : ℝ)^(-2/5+ε) := by
  obtain ⟨D,K,hD,hK,hbound⟩ := coefficient_majorArc_norm_bound hSD hSW hM hMP
  refine ⟨D,K,hD,hK,?_⟩
  intro a b ε ha hab hε
  filter_upwards [hbound a b ha hab,majorArc_totient_power hMP hε,eventually_ge_atTop 1]
    with B hboundB hφB hB
  intro X hX hlog q _ hq hqlo u w w' M N ξ hM0 hN hw hw' hbw hbw' hsupp hξ
  have hqreal : (q : ℝ) ≤ (B : ℝ)^(15 : ℝ) := by
    norm_cast
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hφ := hφB q (NeZero.pos q) hq hqlo
  have hpow : (B : ℝ)^(-50 : ℝ) ≤ (B : ℝ)^(-2/5+ε) :=
    Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hDM : 0 ≤ D*M*(b-a) := mul_nonneg (mul_nonneg hD hM0) (sub_nonneg.mpr hab)
  have hnorm : 0 ≤ K*b*(2*M+(N+2*Real.pi*M)*(b-a)) := by
    have hb : 0 < b := ha.trans_le hab
    positivity
  refine (hboundB X hX hlog q hqreal u w w' M N ξ hM0 hN hw hw' hbw hbw' hsupp hξ).trans ?_
  calc
    _ ≤ X*(D*M*(b-a)*(B : ℝ)^(-2/5+ε)+
        K*b*(2*M+(N+2*Real.pi*M)*(b-a))*(B : ℝ)^(-2/5+ε)) := by
      apply mul_le_mul_of_nonneg_left _ hX.le
      apply add_le_add
      · simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hφ hDM
      · exact mul_le_mul_of_nonneg_left hpow hnorm
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientRationalArc
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large-denominator coefficient estimate on an arbitrary rational arc -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficient_on_large_rational_arc
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ a b ε : ℝ, 0 < a → a ≤ b → 0 < ε →
      ∀ᶠ B : ℕ in atTop, ∀ X θ : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ r : ℚ, r.den ≤ B^15 → (B : ℝ)^(2/5 : ℝ) ≤ r.den →
      |θ-(r : ℝ)| ≤ (B : ℝ)^13/X →
      ∀ (w w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) →
      ‖smoothCoefficientAdditiveSum B X θ w‖ ≤
        (D*M*(b-a)+K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*X*(B : ℝ)^(-2/5+ε) := by
  obtain ⟨D,K,hD,hK,hbound⟩ := coefficient_large_majorArc_bound hSD hSW hM hMP
  refine ⟨D,K,hD,hK,?_⟩
  intro a b ε ha hab hε
  filter_upwards [hbound a b ε ha hab hε,eventually_ge_atTop 1] with B hboundB hB
  intro X θ hX hlog r hq hqlo hnear w w' M N hM0 hN hw hw' hwb hw'b hsupp
  let : NeZero r.den := ⟨r.pos.ne'⟩
  obtain ⟨u,k,hr⟩ := rational_eq_unit_fraction_add_int r
  let ξ : ℝ := X*(θ-r)
  have hθ : θ = (((u : ZMod r.den).val : ℝ)/r.den+ξ/X)+(k : ℝ) := by
    dsimp [ξ]
    rw [hr]
    field_simp
    ring
  have hξ : |ξ| ≤ (B : ℝ)^(14 : ℝ) := by
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    dsimp [ξ]
    rw [abs_mul,abs_of_pos hX,Real.rpow_ofNat]
    calc
      _ ≤ X*((B : ℝ)^13/X) := mul_le_mul_of_nonneg_left hnear hX.le
      _ = (B : ℝ)^13 := by field_simp
      _ ≤ (B : ℝ)^14 := pow_le_pow_right₀ hB1 (by norm_num)
  rw [hθ,smoothCoefficientAdditiveSum_add_int,← coefficientExponentialSum_eq_smooth]
  exact hboundB X hX hlog r.den hq hqlo u w w' M N ξ hM0 hN hw hw' hwb hw'b hsupp hξ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeMajorBoxBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large-denominator part of the actual separated kernel is negligible -/

namespace JointDickman
open Filter MeasureTheory Finset
open scoped Topology

theorem largeMajorArc_box_bound_jd_oai
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b c d ε : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) (hε : 0 < ε) :
    ∃ C D K : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ K ∧
      ∀ᶠ B : ℕ in atTop, ∀ T X : ℝ, 0 < T → 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      Real.log (T*X) ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ Q : ℕ, (B : ℝ)^(2/5 : ℝ) ≤ Q → ∀ j : ℕ,
      ∀ g h : Finset ℕ → ℝ,
      (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      (∀ S ⊆ auxiliaryPrimes B, |h S| ≤ 1) →
      ∀ (w₁ w₂ w₃ w₃' : ℝ → ℝ) (M M₃ N₃ : ℝ),
      0 ≤ M → 0 ≤ M₃ → 0 ≤ N₃ →
      (∀ t, |w₁ t| ≤ M) → (∀ t, |w₂ t| ≤ M) →
      (∀ t, HasDerivAt w₃ (w₃' t) t) → Continuous w₃' →
      (∀ t, |w₃ t| ≤ M₃) → (∀ t, |w₃' t| ≤ N₃) →
      (∀ t, t ≤ c ∨ d < t → w₃ t = 0) →
      ‖(B : ℂ)*(∫ θ in largeMajorArcRegion B j X Q,
        endpointFourierSum B a b (T*X) g w₁ θ *
        endpointFourierSum B a b (T*X) h w₂ (-θ) *
        smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)‖ ≤
      C*M^2*(D*M₃*(d-c)+K*d*(2*M₃+(N₃+2*Real.pi*M₃)*(d-c)))*
        (B : ℝ)^(-23/20+ε)/T := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hmom⟩ := endpoint_fourier_moments hSD hM hMP ha hab (half_pos hε)
  obtain ⟨D,K,hD,hK,hcoeff⟩ := coefficient_on_large_rational_arc hSD hSW hM hMP
  refine ⟨C₂,D,K,hC₂,hD,hK,?_⟩
  filter_upwards [hmom,hcoeff c d (ε/2) hc hcd (half_pos hε),eventually_ge_atTop 1]
    with B hmomB hcoeffB hB
  intro T X hT hX hlogX hlogTX Q hQ j g h hg hh w₁ w₂ w₃ w₃' M M₃ N₃
    hM0 hM₃ hN₃ hw₁ hw₂ hw₃ hw₃' hbw₃ hbw₃' hsupp
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  let P := C₂*M^2*(B : ℝ)^(-7/4+ε/2)/(T*X)
  let R := (D*M₃*(d-c)+K*d*(2*M₃+(N₃+2*Real.pi*M₃)*(d-c)))*X*
    (B : ℝ)^(-2/5+ε/2)
  have hR : 0 ≤ R := by dsimp [R]; have hd := hc.trans_le hcd; positivity
  have hF := (hmomB (T*X) (mul_pos hT hX) hlogTX.1 hlogTX.2 g hg w₁ M hM0 hw₁).2
  have hG : (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b (T*X) h w₂ (-θ)‖^2) ≤ P := by
    simpa only [endpointFourierSum_neg_norm] using
      (hmomB (T*X) (mul_pos hT hX) hlogTX.1 hlogTX.2 h hh w₂ M hM0 hw₂).2
  have hint := discarded_region_integral_bound
    (H := fun θ => smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w₃)
    (largeMajorArcRegion_measurable B j X Q) (fun _ hx => hx.1.1) hR
    (endpointFourierSum_continuous B a b (T*X) g w₁)
    ((endpointFourierSum_continuous B a b (T*X) h w₂).comp continuous_neg)
    (fun θ hθ => by
      obtain ⟨r,hrQ,hrB,hnear⟩ := largeMajorArcRegion_witness hθ
      have hr15 : r.den ≤ B^15 := by
        have hr12 : r.den ≤ B^12 := by exact_mod_cast hrB
        exact hr12.trans (pow_le_pow_right₀ hB (by norm_num : 12 ≤ 15))
      have hrlo : (B : ℝ)^(2/5 : ℝ) ≤ r.den :=
        hQ.trans (by exact_mod_cast hrQ.le)
      exact hcoeffB X (-(j : ℝ)*θ) hX hlogX r hr15 hrlo hnear
        w₃ w₃' M₃ N₃ hM₃ hN₃ hw₃ hw₃' hbw₃ hbw₃' hsupp)
  rw [norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (B : ℝ)*(R/2*(P+P)) := mul_le_mul_of_nonneg_left
      (hint.trans (mul_le_mul_of_nonneg_left (add_le_add hF hG) (div_nonneg hR (by norm_num)))) hB0.le
    _ = _ := by
      have hp : (B : ℝ)^(-23/20+ε) =
          (B : ℝ)*(B : ℝ)^(-2/5+ε/2)*(B : ℝ)^(-7/4+ε/2) := by
        calc
          _ = (B : ℝ)^((1+(-2/5+ε/2))+(-7/4+ε/2)) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hB0,Real.rpow_add hB0,Real.rpow_one]
      rw [hp]
      dsimp [R,P]
      field_simp
      ring

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.largeMajorArc_box_bound_jd_oai := @OAI.JointDickman.largeMajorArc_box_bound_jd_oai
