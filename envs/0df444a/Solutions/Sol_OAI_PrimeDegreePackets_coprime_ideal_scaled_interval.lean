-- Prove2me | solution 1 for OAI.PrimeDegreePackets.coprime_ideal_scaled_interval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:32:40.857371+00:00
-- url     : https://prove2.me/submissions/a7dbe049-b50b-4256-bba8-f50534814e6b

import Mathlib
import Definitions.Def_OAIQ244Duke024

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_DivisorBounds
attribute [-instance] _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
namespace PrimeDegreePackets

 

lemma sum_divisors_initial {A : Type*} [AddCommMonoid A] (F : ℕ → ℕ → A) (N : ℕ) :
    (∑ m ∈ Icc 1 N, ∑ d ∈ m.divisors, F d (m / d)) =
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), F d e := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => ⟨p.2, p.1 / p.2⟩)
  · intro p hp
    obtain ⟨hm, hd⟩ := mem_sigma.mp hp
    obtain ⟨hdm, hm0⟩ := Nat.mem_divisors.mp hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hdmle := Nat.le_of_dvd (by omega : 0 < p.1) hdm
    apply mem_sigma.mpr
    refine ⟨mem_Icc.mpr ⟨hd0, hdmle.trans (mem_Icc.mp hm).2⟩, mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact Nat.le_div_iff_mul_le hd0 |>.mpr (by simpa using hdmle)
    · exact Nat.div_le_div_right (mem_Icc.mp hm).2
  · intro p hp q hq hpq
    obtain ⟨hpm, hpd⟩ := mem_sigma.mp hp
    obtain ⟨hqm, hqd⟩ := mem_sigma.mp hq
    have h1 : p.2 = q.2 := congrArg Sigma.fst hpq
    have h2 : p.1 / p.2 = q.1 / q.2 := by simpa using congrArg Sigma.snd hpq
    have hm : p.1 = q.1 := by
      calc
        p.1 = p.2 * (p.1 / p.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hpd).1).symm
        _ = q.2 * (q.1 / q.2) := by rw [h2, h1]
        _ = q.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hqd).1
    cases p
    cases q
    simp_all
  · intro q hq
    obtain ⟨hd, he⟩ := mem_sigma.mp hq
    have hd0 : 0 < q.1 := (mem_Icc.mp hd).1
    have he0 : 0 < q.2 := (mem_Icc.mp he).1
    have hmul : q.1 * q.2 ≤ N := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp (mem_Icc.mp he).2
    refine ⟨⟨q.1 * q.2, q.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd0 he0, hmul⟩,
      Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, by positivity⟩⟩, ?_⟩
    simp [Nat.mul_div_cancel_left _ hd0]
  · intro p hp
    rfl



lemma nFoldDivisor_succ (k m : ℕ) :
    nFoldDivisor (k + 1) m = ∑ d ∈ m.divisors, nFoldDivisor k d := by
  simp only [nFoldDivisor, pow_succ, ArithmeticFunction.mul_zeta_apply]

lemma nFoldDivisor_one (m : ℕ) : nFoldDivisor 1 m = if m = 0 then 0 else 1 := by
  simp only [nFoldDivisor, pow_one]
  rfl

 
lemma nFoldDivisor_sum_succ (k N : ℕ) :
    (∑ m ∈ Icc 1 N, nFoldDivisor (k + 1) m) =
      ∑ d ∈ Icc 1 N, nFoldDivisor k d * (N / d) := by
  simp_rw [nFoldDivisor_succ]
  rw [sum_divisors_initial (fun d _ => nFoldDivisor k d)]
  simp [Nat.card_Icc, mul_comm]

lemma harmonic_real_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ d ∈ Icc 1 N, (d : ℝ)⁻¹ := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma harmonic_real_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  rw [harmonic_real_eq_sum]
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma harmonic_real_mono {M N : ℕ} (h : M ≤ N) :
    (harmonic M : ℝ) ≤ harmonic N := by
  simp only [harmonic_real_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun _ _ _ => by positivity)

 

lemma nFoldDivisor_reciprocal_sum (k N : ℕ) :
    (∑ m ∈ Icc 1 N, (nFoldDivisor k m : ℝ) / m) ≤ (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [nFoldDivisor, pow_zero, ArithmeticFunction.one_apply]
    by_cases hN : 1 ≤ N
    · simp [ite_div, hN]
    · have : N = 0 := by omega
      simp [this]
  | succ k ih =>
    have hc : (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ) / m) =
        ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), (nFoldDivisor k d : ℝ) / (d * e) := by
      simp_rw [nFoldDivisor_succ, Nat.cast_sum, Finset.sum_div]
      have hid := sum_divisors_initial (fun d e => (nFoldDivisor k d : ℝ) / (d * e)) N
      convert hid using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [hc]
    calc
      _ = ∑ d ∈ Icc 1 N, ((nFoldDivisor k d : ℝ) / d) * harmonic (N / d) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [harmonic_real_eq_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ ∑ d ∈ Icc 1 N, ((nFoldDivisor k d : ℝ) / d) * harmonic N := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (harmonic_real_mono (Nat.div_le_self _ _)) (by positivity)
      _ = (∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) / d) * harmonic N := by rw [Finset.sum_mul]
      _ ≤ (harmonic N : ℝ) ^ k * harmonic N :=
        mul_le_mul_of_nonneg_right ih (harmonic_real_nonneg N)
      _ = (harmonic N : ℝ) ^ (k + 1) := (pow_succ _ _).symm

 

theorem nFoldDivisor_summatory_le (k N : ℕ) :
    (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ)) ≤
      N * (1 + Real.log N) ^ k := by
  have hsum : (∑ m ∈ Icc 1 N, (nFoldDivisor (k + 1) m : ℝ)) =
      ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) * (N / d : ℕ) := by
    exact_mod_cast nFoldDivisor_sum_succ k N
  rw [hsum]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) * ((N : ℝ) / d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left ((Nat.cast_div_le)) (by positivity)
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, (nFoldDivisor k d : ℝ) / d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (N : ℝ) * (harmonic N : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left (nFoldDivisor_reciprocal_sum k N) (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (harmonic_real_nonneg N) (harmonic_le_one_add_log N) k



theorem nFoldDivisor_prime_pow (k j p : ℕ) (hp : p.Prime) :
    nFoldDivisor (k + 1) (p ^ j) = (j + k).choose k := by
  induction k generalizing j with
  | zero => simp [nFoldDivisor_one, hp.ne_zero]
  | succ k ih =>
    rw [nFoldDivisor_succ, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    simpa [Nat.add_assoc] using Nat.sum_range_add_choose j k

 
theorem nFoldDivisor_prime_pow_le (k j p : ℕ) (hp : p.Prime) :
    nFoldDivisor (k + 1) (p ^ j) ≤ (k + 1) ^ j := by
  rw [nFoldDivisor_prime_pow k j p hp]
  calc
    (j + k).choose k = (k + j).choose j := by
      rw [Nat.add_comm j k, Nat.choose_symm_add]
    _ ≤ (k + 1) ^ j := Nat.choose_add_le_add_one_pow k j

 
lemma choose_mul_geometric_le (k j : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ((j + k).choose k : ℝ) * r ^ j ≤ 1 / (1 - r) ^ (k + 1) := by
  have H := hasSum_choose_mul_geometric_of_norm_lt_one k
    (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  rw [← H.tsum_eq]
  exact H.summable.le_tsum j (fun m _ => by positivity)

 

lemma nFoldDivisor_prime_pow_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p j : ℕ, p.Prime →
      (nFoldDivisor (k + 1) (p ^ j) : ℝ) ≤ C * ((p : ℝ) ^ j) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ (-ε)
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let C : ℝ := 1 / (1 - r) ^ (k + 1)
  have hC : 1 ≤ C := by
    simpa [C] using choose_mul_geometric_le k 0 r hrpos.le hrlt
  refine ⟨C, hC, ?_⟩
  intro p j hp
  have H := choose_mul_geometric_le k j r hrpos.le hrlt
  rw [nFoldDivisor_prime_pow k j p hp]
  have hr : r ^ j = (((2 : ℝ) ^ j) ^ ε)⁻¹ := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), mul_comm ε (j : ℝ), Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hr] at H
  have H' : ((j + k).choose k : ℝ) ≤ C * (((2 : ℝ) ^ j) ^ ε) := by
    exact (mul_inv_le_iff₀ (Real.rpow_pos_of_pos (by positivity) ε)).mp H
  apply H'.trans
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ C)
  apply Real.rpow_le_rpow (by positivity) _ hε.le
  exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp.two_le) j

 

theorem nFoldDivisor_subpolynomial (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, (nFoldDivisor (k + 1) m : ℝ) ≤ C * (m : ℝ) ^ ε := by
  classical
  obtain ⟨C₀, hC₀, hsmall⟩ := nFoldDivisor_prime_pow_rpow k ε hε
  have hlarge : ∀ᶠ p : ℕ in Filter.atTop, (k + 1 : ℝ) ≤ (p : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (k + 1 : ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨C₀ ^ N, by positivity, ?_⟩
  intro m
  by_cases hm : m = 0
  · subst m
    simp [nFoldDivisor, Real.zero_rpow hε.ne']
  have hfactor := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (ArithmeticFunction.zeta ^ (k + 1)) (ArithmeticFunction.isMultiplicative_zeta.pow) hm
  have hfactorR : (nFoldDivisor (k + 1) m : ℝ) =
      ∏ p ∈ m.factorization.support, (nFoldDivisor (k + 1) (p ^ m.factorization p) : ℝ) := by
    exact_mod_cast hfactor
  rw [hfactorR]
  calc
    _ ≤ ∏ p ∈ m.factorization.support,
        (if p < N then C₀ else 1) * ((p : ℝ) ^ m.factorization p) ^ ε := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      by_cases hpN : p < N
      · simpa [hpN] using hsmall p (m.factorization p) hprime
      · simp only [ite_eq_right hpN, one_mul]
        calc
          _ ≤ ((k + 1 : ℝ) ^ m.factorization p) := by
            exact_mod_cast nFoldDivisor_prime_pow_le k (m.factorization p) p hprime
          _ ≤ ((p : ℝ) ^ ε) ^ m.factorization p :=
            pow_le_pow_left₀ (by positivity) (hN p (by omega)) _
          _ = ((p : ℝ) ^ m.factorization p) ^ ε := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm,
              Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    _ = (∏ p ∈ m.factorization.support with p < N, C₀) *
        (∏ p ∈ m.factorization.support, ((p : ℝ) ^ m.factorization p) ^ ε) := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
    _ ≤ C₀ ^ N * (∏ p ∈ m.factorization.support,
        ((p : ℝ) ^ m.factorization p) ^ ε) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ∏ p ∈ Finset.range N, C₀ := by
          apply Finset.prod_le_prod_of_subset_of_one_le
          · intro p hp
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          · intro p _
            linarith
          · intro p _ _
            exact hC₀
        _ = C₀ ^ N := by simp
    _ = C₀ ^ N * (m : ℝ) ^ ε := by
      congr 1
      rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
      congr 1
      exact_mod_cast Nat.prod_factorization_pow_eq_self hm

end PrimeDegreePackets


namespace PrimeDegreePackets
open Finset Nat


lemma powerfulCorrection_nonneg (k m : ℕ) : 0 ≤ powerfulCorrection k m := by
  unfold powerfulCorrection
  split_ifs <;> positivity

lemma powerfulRepresentation_spec (m : {m : ℕ // IsPowerful m}) :
    0 < (powerfulRepresentation m).1 ∧ 0 < (powerfulRepresentation m).2 ∧
      (powerfulRepresentation m).1 ^ 2 * (powerfulRepresentation m).2 ^ 3 = m := by
  exact ((powerful_square_cube m.property).choose_spec).choose_spec

lemma powerfulRepresentation_injective : Function.Injective powerfulRepresentation := by
  intro m n h
  apply Subtype.ext
  calc
    (m : ℕ) = (powerfulRepresentation m).1^2 * (powerfulRepresentation m).2^3 := (powerfulRepresentation_spec m).2.2.symm
    _ = (n : ℕ) := by rw [h]; exact (powerfulRepresentation_spec n).2.2

end PrimeDegreePackets


namespace PrimeDegreePackets
open Finset Nat

lemma powerful_rpow_summable :
    Summable (fun m : {m : ℕ // IsPowerful m} => ((m : ℕ) : ℝ) ^ (-(5:ℝ)/8)) := by
  have ha : Summable (fun a : ℕ => (a : ℝ)^(-(5:ℝ)/4)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hb : Summable (fun b : ℕ => (b : ℝ)^(-(15:ℝ)/8)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hab := ha.mul_of_nonneg hb (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _)
    (fun b => Real.rpow_nonneg (Nat.cast_nonneg b) _)
  apply (hab.comp_injective powerfulRepresentation_injective).congr
  intro m
  have hm := (powerfulRepresentation_spec m).2.2
  have ha0 : 0 ≤ (((powerfulRepresentation m).1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb0 : 0 ≤ (((powerfulRepresentation m).2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [← hm, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul ha0, ← Real.rpow_natCast_mul hb0]
  norm_num

 

theorem powerfulCorrection_summable (k : ℕ) :
    Summable (fun m : ℕ => powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) := by
  obtain ⟨C, hC, hbound⟩ := nFoldDivisor_subpolynomial k ((1:ℝ)/8) (by norm_num)
  have H : Summable (fun m : {m : ℕ // IsPowerful m} =>
      (nFoldDivisor (k+1) m : ℝ) / ((m : ℕ) : ℝ)^((3:ℝ)/4)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (powerful_rpow_summable.mul_left C)
    intro m
    have hm : 0 < ((m : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero m.property.1
    calc
      _ ≤ (C * ((m : ℕ) : ℝ)^((1:ℝ)/8)) / ((m : ℕ) : ℝ)^((3:ℝ)/4) :=
        div_le_div_of_nonneg_right (hbound m) (Real.rpow_nonneg hm.le _)
      _ = C * ((m : ℕ) : ℝ)^(-(5:ℝ)/8) := by
        rw [mul_div_assoc, ← Real.rpow_sub hm]
        norm_num
  have Hind := (summable_subtype_iff_indicator
    (f := fun m : ℕ => (nFoldDivisor (k+1) m : ℝ) / (m : ℝ)^((3:ℝ)/4))
    (s := {m : ℕ | IsPowerful m})).mp H
  apply Hind.congr
  intro m
  by_cases hm : IsPowerful m <;> simp [powerfulCorrection, Set.indicator, hm]

lemma powerfulMoment_nonneg (k : ℕ) : 0 ≤ powerfulMoment k := by
  exact tsum_nonneg (fun m => div_nonneg (powerfulCorrection_nonneg k m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))

lemma powerfulCorrection_moment_sum_le (k : ℕ) (s : Finset ℕ) :
    (∑ m ∈ s, powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) ≤ powerfulMoment k :=
  (powerfulCorrection_summable k).sum_le_tsum s
    (fun m _ => div_nonneg (powerfulCorrection_nonneg k m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))

end PrimeDegreePackets


namespace PrimeDegreePackets
open Finset Nat

lemma powerfulCorrection_reciprocal_sum_le (k : ℕ) (s : Finset ℕ) :
    (∑ m ∈ s, powerfulCorrection k m / (m : ℝ)) ≤ powerfulMoment k := by
  apply (Finset.sum_le_sum (g := fun m => powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) ?_).trans
    (powerfulCorrection_moment_sum_le k s)
  intro m _
  by_cases hm : m = 0
  · simp [hm]
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
  apply div_le_div_of_nonneg_left (powerfulCorrection_nonneg k m) (by positivity)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (3:ℝ)/4 ≤ 1)

lemma powerfulCorrection_reciprocal_identity (k : ℕ) (m : ℕ) (hm : m ≠ 0) :
    powerfulCorrection k m / (m : ℝ) =
      (powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) * (m : ℝ)^(-(1:ℝ)/4) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hm0.le, mul_assoc,
    ← Real.rpow_add hm0]
  norm_num [Real.rpow_neg_one]

 
theorem powerfulCorrection_reciprocal_tail (k : ℕ) (s : Finset ℕ) (T : ℝ)
    (hT : 0 < T) (hs : ∀ m ∈ s, T ≤ (m : ℝ)) :
    (∑ m ∈ s, powerfulCorrection k m / (m : ℝ)) ≤ T^(-(1:ℝ)/4) * powerfulMoment k := by
  calc
    _ ≤ ∑ m ∈ s, T^(-(1:ℝ)/4) * (powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 : m ≠ 0 := by
        have := hT.trans_le (hs m hm)
        exact_mod_cast this.ne'
      rw [powerfulCorrection_reciprocal_identity k m hm0, mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hT (hs m hm) (by norm_num))
        (div_nonneg (powerfulCorrection_nonneg k m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
    _ = T^(-(1:ℝ)/4) * ∑ m ∈ s, powerfulCorrection k m / (m : ℝ)^((3:ℝ)/4) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (powerfulCorrection_moment_sum_le k s) (Real.rpow_nonneg hT.le _)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PowerfulIdeals
attribute [-instance] _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
namespace PrimeDegreePackets
open Finset Nat

lemma isPowerful_mul_iff {a b : ℕ} (hab : a.Coprime b) :
    IsPowerful (a*b) ↔ IsPowerful a ∧ IsPowerful b := by
  by_cases ha : a=0
  · simp [ha, IsPowerful]
  by_cases hb : b=0
  · simp [hb, IsPowerful]
  have heqa : ∀ p ∈ a.primeFactors, (a*b).factorization p = a.factorization p := by
    intro p hp
    apply Nat.factorization_eq_of_coprime_left hab
    exact (Nat.mem_primeFactorsList_iff_dvd ha (Nat.prime_of_mem_primeFactors hp)).mpr (Nat.dvd_of_mem_primeFactors hp)
  have heqb : ∀ p ∈ b.primeFactors, (a*b).factorization p = b.factorization p := by
    intro p hp
    apply Nat.factorization_eq_of_coprime_right hab
    exact (Nat.mem_primeFactorsList_iff_dvd hb (Nat.prime_of_mem_primeFactors hp)).mpr (Nat.dvd_of_mem_primeFactors hp)
  constructor
  · intro hm
    constructor
    · refine ⟨ha, ?_⟩
      intro p hp
      rw [← heqa p hp]
      exact hm.2 p (by rw [Nat.primeFactors_mul ha hb]; exact Finset.mem_union_left _ hp)
    · refine ⟨hb, ?_⟩
      intro p hp
      rw [← heqb p hp]
      exact hm.2 p (by rw [Nat.primeFactors_mul ha hb]; exact Finset.mem_union_right _ hp)
  · rintro ⟨hpa,hpb⟩
    refine ⟨mul_ne_zero ha hb, ?_⟩
    intro p hp
    rw [Nat.primeFactors_mul ha hb, Finset.mem_union] at hp
    rcases hp with hp | hp
    · rw [heqa p hp]
      exact hpa.2 p hp
    · rw [heqb p hp]
      exact hpb.2 p hp

lemma isPowerful_prime_pow {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) : IsPowerful (p^j) := by
  refine ⟨pow_ne_zero _ hp.ne_zero, ?_⟩
  intro q hq
  rw [Nat.primeFactors_pow _ (by omega : j ≠ 0), hp.primeFactors, Finset.mem_singleton] at hq
  subst q
  simpa [Nat.factorization_pow, hp.factorization] using hj

lemma powerfulCorrection_one (k : ℕ) : powerfulCorrection k 1 = 1 := by
  have hn : nFoldDivisor (k+1) 1 = 1 := ArithmeticFunction.IsMultiplicative.map_one (ArithmeticFunction.isMultiplicative_zeta.pow)
  simp [powerfulCorrection, IsPowerful, hn]


lemma powerfulFunction_apply (k m : ℕ) : powerfulFunction k m = powerfulCorrection k m := rfl

lemma powerfulFunction_multiplicative (k : ℕ) : (powerfulFunction k).IsMultiplicative := by
  classical
  refine ⟨powerfulCorrection_one k, ?_⟩
  intro a b hab
  simp only [powerfulFunction_apply, powerfulCorrection, isPowerful_mul_iff hab]
  have hn : nFoldDivisor (k+1) (a*b) = nFoldDivisor (k+1) a * nFoldDivisor (k+1) b :=
    ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (ArithmeticFunction.isMultiplicative_zeta.pow) hab
  split_ifs <;> simp_all

end PrimeDegreePackets

open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
namespace PrimeDegreePackets.Sieve

 
lemma sum_moebius_div_indicator (l k : ℕ) (hk : 0 < k) :
    (∑ d ∈ k.divisors, if l ∣ d then (μ (k / d) : ℝ) else 0) =
      if k = l then 1 else 0 := by
  have H : ∀ n > 0, (∑ i ∈ n.divisors, if i = l then (1 : ℝ) else 0) =
      if l ∣ n then 1 else 0 := by
    intro n hn
    simp [Nat.mem_divisors, hn.ne']
  have H' := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp H) k hk
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (μ x : ℝ) * (if l ∣ y then 1 else 0))] at H'
  simpa only [mul_ite, mul_one, mul_zero] using H'

lemma sum_moebius_interval {P l k : ℕ} (hP : P ≠ 0) (hk : k ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ k then (μ (k / d) : ℝ) else 0) =
      if k = l then 1 else 0 := by
  have H := sum_moebius_div_indicator l k (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hk))
  rw [← Nat.divisors_filter_dvd_of_dvd hP hk, Finset.sum_filter] at H
  simpa only [← ite_and, and_comm] using H


lemma sum_multipleMobius {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P) (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then multipleMobius P y d else 0) = y l := by
  simp only [multipleMobius, Finset.ite_sum_zero, ← ite_and]
  rw [Finset.sum_comm]
  calc
    (∑ k ∈ P.divisors, ∑ d ∈ P.divisors,
      if l ∣ d ∧ d ∣ k then (μ (k / d) : ℝ) * y k else 0) =
        ∑ k ∈ P.divisors,
          (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ k then (μ (k / d) : ℝ) else 0) * y k := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
    _ = ∑ k ∈ P.divisors, (if k = l then (1 : ℝ) else 0) * y k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [sum_moebius_interval hP (Nat.dvd_of_mem_divisors hk)]
    _ = y l := by
      simp [ite_mul, Nat.mem_divisors.mpr ⟨hl, hP⟩]


lemma sieveDenominator_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    0 < sieveDenominator s z := by
  unfold sieveDenominator
  apply Finset.sum_pos'
  · intro k hk
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hk)).le
    · rfl
  · refine ⟨1, Nat.one_mem_divisors.mpr s.prodPrimes_ne_zero, ?_⟩
    rw [ite_eq_left hz]
    exact s.selbergTerms_pos (one_dvd _)

lemma nu_mul_optimalWeight (s : BoundingSieve) (z : ℕ) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.nu d * optimalWeight s z d = multipleMobius s.prodPrimes (optimalY s z) d := by
  rw [optimalWeight, ← mul_assoc, mul_inv_cancel₀ (s.nu_ne_zero hd), one_mul]

lemma optimalWeight_transform (s : BoundingSieve) (z : ℕ) {l : ℕ} (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * optimalWeight s z d else 0) =
      optimalY s z l := by
  convert sum_multipleMobius s.prodPrimes_ne_zero hl (optimalY s z) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro d hd
  rw [nu_mul_optimalWeight s z (Nat.dvd_of_mem_divisors hd)]

lemma optimalWeight_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    optimalWeight s z 1 = 1 := by
  have hD : sieveDenominator s z ≠ 0 := (sieveDenominator_pos s hz).ne'
  unfold optimalWeight multipleMobius
  rw [s.nu_mult.map_one, inv_one, one_mul]
  simp only [one_dvd, ite_true, if_true, Nat.div_one, optimalY, mul_ite, mul_zero]
  have H : ∀ k ∈ s.prodPrimes.divisors,
      (μ k : ℝ) * ((μ k : ℝ) * s.selbergTerms k / sieveDenominator s z) =
      s.selbergTerms k / sieveDenominator s z := by
    intro k hk
    have hm : (μ k : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
        (s.squarefree_of_mem_divisors_prodPrimes hk)
    calc
      _ = (μ k : ℝ)^2 * s.selbergTerms k / sieveDenominator s z := by ring
      _ = _ := by rw [hm, one_mul]
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun a => if k ≤ z then a else 0) (H k hk))]
  rw [show (∑ k ∈ s.prodPrimes.divisors, if k ≤ z then s.selbergTerms k / sieveDenominator s z else 0) =
      sieveDenominator s z / sieveDenominator s z by
    simp only [sieveDenominator, Finset.sum_div, ite_div, zero_div]]
  exact div_self hD

lemma optimalWeight_mainSum (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (BoundingSieve.lambdaSquared (optimalWeight s z)) =
      (sieveDenominator s z)⁻¹ := by
  have hD : sieveDenominator s z ≠ 0 := (sieveDenominator_pos s hz).ne'
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * optimalWeight s z d else 0) ^ 2) =
      ∑ l ∈ s.prodPrimes.divisors,
        (if l ≤ z then s.selbergTerms l else 0) / (sieveDenominator s z)^2 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [optimalWeight_transform s z (Nat.dvd_of_mem_divisors hl)]
      unfold optimalY
      split_ifs with h
      · have hg : s.selbergTerms l ≠ 0 := (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).ne'
        have hm : (μ l : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
            (s.squarefree_of_mem_divisors_prodPrimes hl)
        rw [div_pow, mul_pow, hm, one_mul]
        field_simp
      · simp
    _ = sieveDenominator s z / (sieveDenominator s z)^2 := by rw [← Finset.sum_div]; rfl
    _ = (sieveDenominator s z)⁻¹ := by field_simp

lemma optimalWeight_eq_zero_of_lt (s : BoundingSieve) {z d : ℕ} (h : z < d) :
    optimalWeight s z d = 0 := by
  unfold optimalWeight multipleMobius
  suffices (∑ k ∈ s.prodPrimes.divisors,
      if d ∣ k then (μ (k / d) : ℝ) * optimalY s z k else 0) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hd : d ∣ k
  · have hdk := Nat.le_of_dvd (Nat.pos_of_mem_divisors hk) hd
    simp [hd, optimalY, show ¬ k ≤ z by omega]
  · simp [hd]

lemma abs_optimalWeight_le (s : BoundingSieve) {z d : ℕ} (hz : 1 ≤ z)
    (hd : d ∣ s.prodPrimes) : |optimalWeight s z d| ≤ (s.nu d)⁻¹ := by
  have hD := sieveDenominator_pos s hz
  have hnu := s.nu_pos_of_dvd_prodPrimes hd
  have hm (k : ℕ) : |(μ k : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
  have hy (k : ℕ) (hk : k ∈ s.prodPrimes.divisors) :
      |optimalY s z k| ≤ (if k ≤ z then s.selbergTerms k else 0) / sieveDenominator s z := by
    unfold optimalY
    split_ifs with h
    · rw [abs_div, abs_mul, abs_of_pos (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hk)),
        abs_of_pos hD]
      exact div_le_div_of_nonneg_right (by nlinarith [s.selbergTerms_pos (Nat.dvd_of_mem_divisors hk), hm k]) hD.le
    · simp
  unfold optimalWeight multipleMobius
  rw [abs_mul, abs_inv, abs_of_pos hnu]
  apply mul_le_of_le_one_right (inv_nonneg.mpr hnu.le)
  calc
    |∑ k ∈ s.prodPrimes.divisors,
      if d ∣ k then (μ (k / d) : ℝ) * optimalY s z k else 0| ≤
        ∑ k ∈ s.prodPrimes.divisors,
          (if k ≤ z then s.selbergTerms k else 0) / sieveDenominator s z := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk' : d ∣ k
      · rw [ite_eq_left hk', abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hm _)).trans (hy k hk)
      · rw [ite_eq_right hk', abs_zero]
        exact (abs_nonneg _).trans (hy k hk)
    _ = 1 := by
      rw [← Finset.sum_div]
      exact div_self hD.ne'

lemma sum_divisors_lambdaSquared (P : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d) =
      (∑ d ∈ P.divisors, w d)^2 := by
  have he (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ d ∈ P.divisors, ∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
        if d = Nat.lcm d₁ d₂ then f d₁ d₂ d else 0) =
      (∑ d ∈ P.divisors, ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
        if d = Nat.lcm d₁ d₂ then f d₁ d₂ d else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hdP, hP⟩ := Nat.mem_divisors.mp hd
    have H : ∀ d₁ d₂, (d₁ ∣ d ∧ d₂ ∣ d ∧ d = d₁.lcm d₂) = (d = d₁.lcm d₂) := by
      intro d₁ d₂
      simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hP hdP, Finset.sum_filter,
      Finset.ite_sum_zero, ← ite_and, H]
  unfold BoundingSieve.lambdaSquared
  rw [he, Finset.sum_comm, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d₁ h₁
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d₂ h₂
  apply Finset.sum_ite_eq_of_mem'
  exact Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors h₁)
    (Nat.dvd_of_mem_divisors h₂), (Nat.mem_divisors.mp h₁).2⟩

lemma abs_lambdaSquared_le (w : ℕ → ℝ) (d : ℕ) :
    |BoundingSieve.lambdaSquared w d| ≤ BoundingSieve.lambdaSquared (fun k => |w k|) d := by
  unfold BoundingSieve.lambdaSquared
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d₁ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d₂ _
  split_ifs <;> simp [abs_mul]

lemma errSum_lambdaSquared_le (s : BoundingSieve) (w : ℕ → ℝ) {R : ℝ}
    (_hR : 0 ≤ R) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ R) :
    s.errSum (BoundingSieve.lambdaSquared w) ≤
      R * (∑ d ∈ s.prodPrimes.divisors, |w d|)^2 := by
  unfold BoundingSieve.errSum
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        BoundingSieve.lambdaSquared (fun k => |w k|) d * R := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul (abs_lambdaSquared_le w d) (hrem d hd) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_lambdaSquared_le w d))
    _ = _ := by rw [← Finset.sum_mul, sum_divisors_lambdaSquared, mul_comm]

lemma optimalWeight_errSum_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) {R : ℝ}
    (hR : 0 ≤ R) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ R) :
    s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) ≤
      R * (∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (s.nu d)⁻¹ else 0)^2 := by
  apply (errSum_lambdaSquared_le s _ hR hrem).trans
  apply mul_le_mul_of_nonneg_left _ hR
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  apply Finset.sum_le_sum
  intro d hd
  split_ifs with h
  · exact abs_optimalWeight_le s hz (Nat.dvd_of_mem_divisors hd)
  · rw [optimalWeight_eq_zero_of_lt s (by omega), abs_zero]

 

theorem optimized_sieve_bound (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / sieveDenominator s z +
      s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) := by
  have H := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (BoundingSieve.lambdaSquared (optimalWeight s z))
    (BoundingSieve.upperMoebius_lambdaSquared _ (optimalWeight_one s hz))
  rw [optimalWeight_mainSum s hz] at H
  simpa only [div_eq_mul_inv] using H

end PrimeDegreePackets.Sieve

open scoped BigOperators Classical
open Finset Nat
namespace PrimeDegreePackets.Sieve

lemma radical_dvd (n : ℕ) : radical n ∣ n := Nat.prod_primeFactors_dvd n

lemma radical_pos (n : ℕ) : 0 < radical n :=
  Finset.prod_pos (fun _p hp => Nat.pos_of_mem_primeFactors hp)

lemma primeFactors_radical (n : ℕ) : (radical n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod_primeFactors n

lemma div_radical_factored {n : ℕ} (hn : n ≠ 0) :
    n / radical n ∈ Nat.factoredNumbers (radical n).primeFactors := by
  refine ⟨Nat.div_ne_zero_iff.mpr ⟨(radical_pos n).ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (radical_dvd n)⟩, ?_⟩
  intro p hp
  rw [primeFactors_radical]
  apply Nat.primeFactors_mono (Nat.div_dvd_of_dvd (radical_dvd n)) hn
  exact Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp

lemma reciprocal_factored_hasSum (d : ℕ) :
    HasSum (fun m : Nat.factoredNumbers d.primeFactors => (m.val : ℝ)⁻¹)
      (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) := by
  have hsum {p : ℕ} (hp : p.Prime) :
      Summable (fun j : ℕ => ‖((p ^ j : ℕ) : ℝ)⁻¹‖) := by
    have hp2 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    simpa only [Nat.cast_pow, Real.norm_eq_abs, abs_pow, abs_inv,
      abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p), inv_pow] using
      (summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p))
        (inv_lt_one_of_one_lt₀ hp2))
  have H := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (n : ℝ)⁻¹) (by simp)
    (fun {m n} _ => by simp [Nat.cast_mul, mul_inv_rev, mul_comm])
    (fun {p} hp => hsum hp) d.primeFactors
  have he : (∏ p ∈ d.primeFactors with p.Prime, ∑' j : ℕ, ((p ^ j : ℕ) : ℝ)⁻¹) =
      ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    simpa only [Nat.cast_pow, inv_pow] using tsum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p))
      (inv_lt_one_of_one_lt₀ hp2)
  exact he ▸ H.2

lemma reciprocal_radical_class_bound (A : Finset ℕ) {d : ℕ}
    (hA : ∀ n ∈ A, n ≠ 0 ∧ radical n = d) :
    (∑ n ∈ A, (n : ℝ)⁻¹) ≤ (d.totient : ℝ)⁻¹ := by
  let e : A → Nat.factoredNumbers d.primeFactors := fun n =>
    ⟨n.val / d, by rw [← (hA n.val n.property).2]; exact div_radical_factored (hA n.val n.property).1⟩
  have hmul (n : A) : d * (n.val / d) = n.val := by
    rw [← (hA n.val n.property).2]
    exact Nat.mul_div_cancel' (radical_dvd n.val)
  have he : Function.Injective e := by
    intro m n h
    apply Subtype.ext
    have H := congrArg (fun x : Nat.factoredNumbers d.primeFactors => d * x.val) h
    exact (hmul m).symm.trans (H.trans (hmul n))
  have hsum := (reciprocal_factored_hasSum d).mul_left ((d : ℝ)⁻¹)
  have H := Summable.tsum_le_tsum_of_inj e he
    (fun _ _ => by positivity)
    (f := fun n : A => (n.val : ℝ)⁻¹)
    (g := fun m : Nat.factoredNumbers d.primeFactors => (d : ℝ)⁻¹ * (m.val : ℝ)⁻¹)
    (fun n => le_of_eq (by
      change (n.val : ℝ)⁻¹ = (d : ℝ)⁻¹ * ((n.val / d : ℕ) : ℝ)⁻¹
      rw [← mul_inv_rev, ← Nat.cast_mul, Nat.mul_comm, hmul n]))
    Summable.of_finite hsum.summable
  rw [tsum_fintype, Finset.sum_coe_sort A (fun n => (n : ℝ)⁻¹), hsum.tsum_eq] at H
  have ht : (d.totient : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have H := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors d)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using H
  simpa only [ht, mul_inv_rev, Finset.prod_inv_distrib, mul_comm] using H

 

theorem harmonic_le_inverse_totient_sum {P z : ℕ} (hP : P ≠ 0)
    (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ P) :
    (harmonic z : ℝ) ≤ ∑ d ∈ P.divisors, if d ≤ z then (d.totient : ℝ)⁻¹ else 0 := by
  let A := Finset.Icc 1 z
  let D := P.divisors.filter (fun d => d ≤ z)
  have hmap : ∀ n ∈ A, radical n ∈ D := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    apply Finset.mem_filter.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      refine ⟨Nat.prod_primeFactors_dvd_iff hP |>.mpr ?_, hP⟩
      intro p hp
      exact (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
        hprimes p (Nat.prime_of_mem_primeFactors hp)
          ((Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)).trans (Finset.mem_Icc.mp hn).2), hP⟩)
    · exact (Nat.le_of_dvd hn0 (radical_dvd n)).trans (Finset.mem_Icc.mp hn).2
  have he : (∑ n ∈ A, (n : ℝ)⁻¹) =
      ∑ d ∈ D, ∑ n ∈ A with radical n = d, (n : ℝ)⁻¹ := by
    exact (Finset.sum_fiberwise_of_maps_to hmap (fun n => (n : ℝ)⁻¹)).symm
  calc
    (harmonic z : ℝ) = ∑ n ∈ A, (n : ℝ)⁻¹ := by
      simp only [A, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ = _ := he
    _ ≤ ∑ d ∈ D, (d.totient : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d _
      exact reciprocal_radical_class_bound _ (fun n hn =>
        ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1; omega,
          (Finset.mem_filter.mp hn).2⟩)
    _ = _ := Finset.sum_filter _ _

end PrimeDegreePackets.Sieve
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntervalSieve
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
namespace PrimeDegreePackets.Sieve
open Finset Nat ArithmeticFunction BoundingSieve


lemma interval_divisibility_card (a b d : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter (fun n => d ∣ n)).card = b / d - a / d := by
  have hdis : Disjoint ((Finset.Ioc 0 a).filter (fun n => d ∣ n))
      ((Finset.Ioc a b).filter (fun n => d ∣ n)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [mem_filter, Finset.mem_Ioc] at hn hm
    omega
  have hu : ((Finset.Ioc 0 a).filter (fun n => d ∣ n)) ∪
      ((Finset.Ioc a b).filter (fun n => d ∣ n)) =
      ((Finset.Ioc 0 b).filter (fun n => d ∣ n)) := by
    ext n
    simp only [Finset.mem_union, mem_filter, Finset.mem_Ioc]
    omega
  have H := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hdis, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at H
  omega

lemma interval_multSum (a b P : ℕ) (hP : Squarefree P) (hab : a ≤ b) (d : ℕ) :
    (intervalSieve a b P hP).multSum d = (b / d : ℕ) - (a / d : ℕ) := by
  rw [BoundingSieve.multSum]
  change (∑ n ∈ Finset.Ioc a b, if d ∣ n then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, interval_divisibility_card a b d hab]
  exact Nat.cast_sub (Nat.div_le_div_right hab)

lemma real_div_lt_nat_div_add_one (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (a : ℝ) / d < (a / d : ℕ) + 1 := by
  have H : a < (a / d + 1) * d := by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ a hd
  exact (div_lt_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr (by exact_mod_cast H)

lemma interval_rem_abs_le_one (a b P : ℕ) (hP : Squarefree P) (hab : a ≤ b)
    {d : ℕ} (hd : 0 < d) : |(intervalSieve a b P hP).rem d| ≤ 1 := by
  rw [BoundingSieve.rem, interval_multSum a b P hP hab]
  change |(b / d : ℕ) - (a / d : ℕ) - (d : ℝ)⁻¹ * ((b : ℝ) - a)| ≤ 1
  rw [abs_le]
  have ha := real_div_lt_nat_div_add_one a hd
  have hb := real_div_lt_nat_div_add_one b hd
  have ha' : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := Nat.cast_div_le
  have hb' : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d := Nat.cast_div_le
  simp only [div_eq_mul_inv] at *
  constructor <;> nlinarith

lemma interval_selbergTerms (a b P : ℕ) (hP : Squarefree P) (d : ℕ) :
    (intervalSieve a b P hP).selbergTerms d = (d.totient : ℝ)⁻¹ := by
  rw [BoundingSieve.selbergTerms_apply]
  have ht : (d.totient : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have H := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors d)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using H
  simp only [intervalSieve, reciprocalDensity, ArithmeticFunction.coe_mk, ht,
    mul_inv, Finset.prod_inv_distrib]



end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat


lemma sum_divisors_coprime {P R : ℕ} (h : P.Coprime R) (f : ℕ → ℝ) :
    (∑ d ∈ (P * R).divisors, f d) =
      ∑ d ∈ P.divisors, ∑ e ∈ R.divisors, f (d * e) := by
  rw [h.divisors_mul, Finset.sum_map]
  change (∑ x ∈ (P.divisors ×ˢ R.divisors).attach, f (x.val.1 * x.val.2)) = _
  rw [Finset.sum_attach _ (fun x : ℕ × ℕ => f (x.1 * x.2)), Finset.sum_product]

lemma truncatedTotientSum_mul_le {P R z : ℕ} (h : P.Coprime R) :
    truncatedTotientSum (P * R) z ≤
      truncatedTotientSum P z * ∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹ := by
  rw [truncatedTotientSum, sum_divisors_coprime h]
  unfold truncatedTotientSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hde : d.Coprime e :=
    (h.of_dvd_left (Nat.dvd_of_mem_divisors hd)).of_dvd_right (Nat.dvd_of_mem_divisors he)
  have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
  by_cases hdz : d * e ≤ z
  · have hd_le : d ≤ z := (Nat.le_mul_of_pos_right d he1).trans hdz
    simp only [ite_eq_left hdz, ite_eq_left hd_le, Nat.totient_mul hde, Nat.cast_mul, mul_inv, le_refl]
  · rw [ite_eq_right hdz]
    split_ifs <;> positivity

lemma harmonic_le_truncatedTotientSum_mul {P R z : ℕ} (h : P.Coprime R)
    (hPR : P * R ≠ 0) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ P * R) :
    (harmonic z : ℝ) ≤
      truncatedTotientSum P z * ∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹ := by
  exact (harmonic_le_inverse_totient_sum hPR hprimes).trans
    (truncatedTotientSum_mul_le h)

 

theorem sifted_interval_complement_bound (a b P R z : ℕ)
    (hP : Squarefree P) (hR : R ≠ 0) (hPR : P.Coprime R) (hab : a ≤ b)
    (hz : 1 ≤ z) (hprimes : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ P * R) :
    (((Finset.Ioc a b).filter (fun n => P.Coprime n)).card : ℝ) ≤
      (((b : ℝ) - a) / Real.log (z + 1)) *
        (∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹) +
        ((z : ℝ) * (z + 1)) ^ 2 := by
  let s := intervalSieve a b P hP
  have hs := optimized_sieve_bound s hz
  have he := optimalWeight_errSum_le s hz (by norm_num : (0 : ℝ) ≤ 1)
    (fun d hd => interval_rem_abs_le_one a b P hP hab
      (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.dvd_of_mem_divisors hd))))
  have hlog : 0 < Real.log (z + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < z + 1))
  have hden : Real.log (z + 1) ≤ sieveDenominator s z *
      (∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹) := by
    apply (show Real.log (z + 1) ≤ (harmonic z : ℝ) by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic z).trans
    have H := harmonic_le_truncatedTotientSum_mul hPR (mul_ne_zero hP.ne_zero hR) hprimes
    unfold sieveDenominator
    change (harmonic z : ℝ) ≤ (∑ d ∈ P.divisors,
      if d ≤ z then (intervalSieve a b P hP).selbergTerms d else 0) * _
    simpa only [interval_selbergTerms, truncatedTotientSum] using H
  have herr : (∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (s.nu d)⁻¹ else 0) ≤
      (z : ℝ) * (z + 1) := by
    change (∑ d ∈ P.divisors, if d ≤ z then ((d : ℝ)⁻¹)⁻¹ else 0) ≤ _
    simp only [inv_inv]
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ d ∈ P.divisors.filter (fun d => d ≤ z), (z : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact_mod_cast (Finset.mem_filter.mp hd).2
      _ ≤ ∑ _d ∈ Finset.range (z + 1), (z : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; positivity)
        intro d hd
        exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hd).2; omega)
      _ = _ := by simp <;> ring
  have herr0 : 0 ≤ ∑ d ∈ s.prodPrimes.divisors, if d ≤ z then (s.nu d)⁻¹ else 0 := by
    apply Finset.sum_nonneg
    intro d hd
    split_ifs
    · exact inv_nonneg.mpr (s.nu_pos_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hd)).le
    · rfl
  have hm : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hf : s.siftedSum = (((Finset.Ioc a b).filter (fun n => P.Coprime n)).card : ℝ) := by
    simp [BoundingSieve.siftedSum, s, intervalSieve]
  rw [hf] at hs
  apply hs.trans
  apply _root_.add_le_add
  · change ((b : ℝ) - a) / sieveDenominator s z ≤ _
    have hD := sieveDenominator_pos s hz
    apply (div_le_iff₀ hD).mpr
    have H := mul_le_mul_of_nonneg_left hden hm
    have H' := (le_div_iff₀ hlog).mpr H
    convert H' using 1 <;> first | rfl | ring
  · apply he.trans
    rw [one_mul]
    exact pow_le_pow_left₀ herr0 herr 2

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma squarefree_prime_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (hS p hp).squarefree)
  simpa only [← Nat.coprime_iff_isRelPrime] using
    (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq

lemma fullTotientSum_mul {P R : ℕ} (h : P.Coprime R) :
    (∑ d ∈ (P * R).divisors, (d.totient : ℝ)⁻¹) =
      (∑ d ∈ P.divisors, (d.totient : ℝ)⁻¹) *
      (∑ e ∈ R.divisors, (e.totient : ℝ)⁻¹) := by
  rw [sum_divisors_coprime h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hde : d.Coprime e :=
    (h.of_dvd_left (Nat.dvd_of_mem_divisors hd)).of_dvd_right (Nat.dvd_of_mem_divisors he)
  rw [Nat.totient_mul hde, Nat.cast_mul, mul_inv]

lemma fullTotientSum_prime_product (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ d ∈ (∏ p ∈ S, p).divisors, (d.totient : ℝ)⁻¹) =
      ∏ p ∈ S, (1 + ((p : ℝ) - 1)⁻¹) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hpP := hS p (Finset.mem_insert_self _ _)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      exact (Nat.coprime_primes hpP (hS' q hq)).mpr (by intro h; exact hp (h ▸ hq))
    rw [Finset.prod_insert hp, fullTotientSum_mul hc, ih hS', Finset.prod_insert hp]
    congr 1
    simp [hpP.divisors, hpP.ne_one.symm, Nat.totient_prime hpP, Nat.cast_sub hpP.one_le]



lemma mixtureMass_nonneg (S T : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) : 0 ≤ mixtureMass S T g := by
  exact mul_nonneg (Finset.prod_nonneg (fun p _ => sub_nonneg.mpr (hg p).2))
    (Finset.prod_nonneg (fun p _ => (hg p).1))

lemma sum_mixtureMass (S : Finset ℕ) (g : ℕ → ℝ) :
    ∑ T ∈ S.powerset, mixtureMass S T g = 1 := by
  unfold mixtureMass
  rw [← Finset.prod_add]
  simp

lemma coprime_prime_product_indicator (T : Finset ℕ) (m : ℕ) :
    (if (∏ p ∈ T, p).Coprime m then (1 : ℝ) else 0) =
      ∏ p ∈ T, (if p.Coprime m then (1 : ℝ) else 0) := by
  simp only [Finset.prod_boole, Nat.coprime_prod_left_iff]

lemma softWeight_eq_mixture (S : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) :
    softWeight S g m = ∑ T ∈ S.powerset,
      mixtureMass S T g * (if (∏ p ∈ T, p).Coprime m then 1 else 0) := by
  rw [softWeight, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib, coprime_prime_product_indicator, mixtureMass]
  ring

lemma sum_softWeight_eq_mixture (S : Finset ℕ) (g : ℕ → ℝ) (a b : ℕ) :
    (∑ m ∈ Finset.Ioc a b, softWeight S g m) =
      ∑ T ∈ S.powerset, mixtureMass S T g *
        (((Finset.Ioc a b).filter (fun m => (∏ p ∈ T, p).Coprime m)).card : ℝ) := by
  simp_rw [softWeight_eq_mixture]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.mul_sum]
  congr 1
  simp

lemma sum_mixture_complementEuler (S : Finset ℕ) (g : ℕ → ℝ) :
    (∑ T ∈ S.powerset, mixtureMass S T g *
      ∏ p ∈ S \ T, (1 + ((p : ℝ) - 1)⁻¹)) =
      ∏ p ∈ S, (1 + g p / ((p : ℝ) - 1)) := by
  calc
    _ = ∑ T ∈ S.powerset, (∏ p ∈ T, (1 - g p)) *
        ∏ p ∈ S \ T, (g p * (1 + ((p : ℝ) - 1)⁻¹)) := by
      apply Finset.sum_congr rfl
      intro T _
      rw [mixtureMass, Finset.prod_mul_distrib]
      ring
    _ = ∏ p ∈ S, ((1 - g p) + g p * (1 + ((p : ℝ) - 1)⁻¹)) :=
      (Finset.prod_add _ _ _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      ring

 

theorem soft_interval_bound (a b z : ℕ) (S : Finset ℕ) (g : ℕ → ℝ)
    (hab : a ≤ b) (hz : 1 ≤ z) (hS : ∀ p ∈ S, p.Prime)
    (hcontains : ∀ p : ℕ, p.Prime → p ≤ z → p ∈ S)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) :
    (∑ m ∈ Finset.Ioc a b, softWeight S g m) ≤
      (((b : ℝ) - a) / Real.log (z + 1)) *
        (∏ p ∈ S, (1 + g p / ((p : ℝ) - 1))) +
        ((z : ℝ) * (z + 1)) ^ 2 := by
  rw [sum_softWeight_eq_mixture]
  calc
    _ ≤ ∑ T ∈ S.powerset, mixtureMass S T g *
        ((((b : ℝ) - a) / Real.log (z + 1)) *
          (∏ p ∈ S \ T, (1 + ((p : ℝ) - 1)⁻¹)) +
          ((z : ℝ) * (z + 1)) ^ 2) := by
      apply Finset.sum_le_sum
      intro T hT
      have hTS := Finset.mem_powerset.mp hT
      have heq : (∏ p ∈ T, p) * (∏ p ∈ S \ T, p) = ∏ p ∈ S, p :=
        by rw [mul_comm, Finset.prod_sdiff hTS]
      have hsf : Squarefree ((∏ p ∈ T, p) * (∏ p ∈ S \ T, p)) :=
        heq ▸ squarefree_prime_product S hS
      obtain ⟨hcop, hsT, hsR⟩ := Nat.squarefree_mul_iff.mp hsf
      apply mul_le_mul_of_nonneg_left _ (mixtureMass_nonneg S T g hg)
      have H := sifted_interval_complement_bound a b _ _ z hsT hsR.ne_zero hcop hab hz (by
        intro p hp hpz
        rw [heq]
        exact Finset.dvd_prod_of_mem (fun q : ℕ => q) (hcontains p hp hpz))
      simpa only [fullTotientSum_prime_product _ (fun p hp => hS p (Finset.mem_sdiff.mp hp).1)] using H
    _ = _ := by
      rw [show (∑ T ∈ S.powerset, mixtureMass S T g *
          ((((b : ℝ) - a) / Real.log (z + 1)) *
            (∏ p ∈ S \ T, (1 + ((p : ℝ) - 1)⁻¹)) +
            ((z : ℝ) * (z + 1)) ^ 2)) =
          (((b : ℝ) - a) / Real.log (z + 1)) *
            (∑ T ∈ S.powerset, mixtureMass S T g *
              (∏ p ∈ S \ T, (1 + ((p : ℝ) - 1)⁻¹))) +
          (∑ T ∈ S.powerset, mixtureMass S T g) *
            ((z : ℝ) * (z + 1)) ^ 2 by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro T _
        ring]
      rw [sum_mixtureMass, one_mul, sum_mixture_complementEuler]

end PrimeDegreePackets.Sieve

open scoped BigOperators
namespace PrimeDegreePackets.Sieve


lemma primePenalty_apply (g : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) :
    primePenalty g m = ∏ p ∈ m.primeFactors, g p := by
  simp [primePenalty, hm]

lemma primePenalty_multiplicative (g : ℕ → ℝ) :
    (primePenalty g).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [primePenalty], ?_⟩
  intro m n hm hn hmn
  simp only [primePenalty_apply g hm, primePenalty_apply g hn,
    primePenalty_apply g (mul_ne_zero hm hn), Nat.primeFactors_mul hm hn]
  exact Finset.prod_union hmn.disjoint_primeFactors

lemma primePenalty_one (g : ℕ → ℝ) : primePenalty g 1 = 1 :=
  (primePenalty_multiplicative g).map_one

lemma primePenalty_prime_pow (g : ℕ → ℝ) {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) :
    primePenalty g (p ^ j) = g p := by
  rw [primePenalty_apply _ (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_pow _ hj,
    hp.primeFactors, Finset.prod_singleton]

lemma primePenalty_nonneg (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (m : ℕ) :
    0 ≤ primePenalty g m := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [primePenalty_apply _ hm]
    exact Finset.prod_nonneg (fun p _ => hg p)

lemma primePenalty_le_one (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (m : ℕ) :
    primePenalty g m ≤ 1 := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [primePenalty_apply _ hm]
    exact Finset.prod_le_one (fun prime _ => (hg prime).1) (fun prime _ => (hg prime).2)



lemma logWeight_pow (f : ArithmeticFunction ℝ) (k : ℕ) :
    logWeight (f ^ (k + 1)) = ((k + 1 : ℕ) : ℝ) • (f ^ k * logWeight f) := by
  have H := coefficientLogDerivation.leibniz_pow f (k + 1)
  change logWeight (f ^ (k + 1)) = (k + 1) • (f ^ (k + 1 - 1) * logWeight f) at H
  simpa only [Nat.add_sub_cancel, Nat.cast_smul_eq_nsmul] using H

 
lemma convolution_nonneg {f g : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (hg : ∀ m, 0 ≤ g m) (m : ℕ) :
    0 ≤ (f * g) m := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun de _ => mul_nonneg (hf de.1) (hg de.2))

lemma convolution_pow_nonneg {f : ArithmeticFunction ℝ} (hf : ∀ m, 0 ≤ f m)
    (k m : ℕ) : 0 ≤ (f ^ k) m := by
  induction k generalizing m with
  | zero => simp [ArithmeticFunction.one_apply]; split_ifs <;> positivity
  | succ k ih =>
    rw [pow_succ]
    exact convolution_nonneg ih hf m


lemma reciprocalCoefficients_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) : (reciprocalCoefficients f).IsMultiplicative := by
  refine ⟨by simp [hf], ?_⟩
  intro m n hmn
  simp only [reciprocalCoefficients_apply, hf.map_mul_of_coprime hmn, Nat.cast_mul]
  ring

open scoped ArithmeticFunction.zeta


lemma divisorReciprocal_apply (f : ArithmeticFunction ℝ) (m : ℕ) :
    divisorReciprocal f m = ∑ d ∈ m.divisors, f d / d := by
  rw [divisorReciprocal, ArithmeticFunction.coe_mul_zeta_apply]
  rfl

lemma divisorReciprocal_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) : (divisorReciprocal f).IsMultiplicative :=
  (reciprocalCoefficients_multiplicative hf).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast

lemma divisorReciprocal_nonneg {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (m : ℕ) : 0 ≤ divisorReciprocal f m := by
  rw [divisorReciprocal_apply]
  exact Finset.sum_nonneg (fun d _ => div_nonneg (hf d) (Nat.cast_nonneg d))

lemma geometric_partial_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ∑ j ∈ Finset.range k, r ^ j ≤ (1 - r)⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (by linarith : 0 < 1 - r), geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hr0 k)

lemma primePenalty_divisorReciprocal_pow (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divisorReciprocal (primePenalty g) (p ^ k) =
      1 + g p * (p : ℝ)⁻¹ * ∑ j ∈ Finset.range k, ((p : ℝ)⁻¹) ^ j := by
  rw [divisorReciprocal_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
  simp only [pow_zero, primePenalty_one, Nat.cast_one, div_one]
  rw [add_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [primePenalty_prime_pow g hp (by omega), Nat.cast_pow, pow_succ]
  ring

lemma primePenalty_divisorReciprocal_pow_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divisorReciprocal (primePenalty g) (p ^ k) ≤ 1 + g p / ((p : ℝ) - 1) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hr := geometric_partial_sum_le (p : ℝ)⁻¹ (by positivity)
    (inv_lt_one_of_one_lt₀ hp1) k
  rw [primePenalty_divisorReciprocal_pow g hp k]
  apply _root_.add_le_add (le_refl 1)
  calc
    _ ≤ g p * (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg (hg p) (by positivity))
    _ = g p / ((p : ℝ) - 1) := by
      field_simp

 
lemma primePenalty_divisorReciprocal_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    {m : ℕ} (hm : m ≠ 0) :
    divisorReciprocal (primePenalty g) m ≤
      ∏ p ∈ m.primeFactors, (1 + g p / ((p : ℝ) - 1)) := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    (divisorReciprocal_multiplicative (primePenalty_multiplicative g)) hm]
  change (∏ p ∈ m.factorization.support,
    divisorReciprocal (primePenalty g) (p ^ m.factorization p)) ≤ _
  rw [Nat.support_factorization]
  apply Finset.prod_le_prod
  · intro p _
    exact divisorReciprocal_nonneg (primePenalty_nonneg g hg) _
  · intro p hp
    exact primePenalty_divisorReciprocal_pow_le g hg (Nat.prime_of_mem_primeFactors hp) _

 
lemma reciprocalCoefficients_mul (f g : ArithmeticFunction ℝ) :
    reciprocalCoefficients (f * g) = reciprocalCoefficients f * reciprocalCoefficients g := by
  ext m
  rw [reciprocalCoefficients_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  rintro ⟨d, e⟩ hde
  have hde := (Nat.mem_divisorsAntidiagonal.mp hde).1
  simp only [reciprocalCoefficients_apply]
  rw [← hde, Nat.cast_mul]
  ring

lemma divisorReciprocal_mono_divisor {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) {d m : ℕ} (hm : m ≠ 0) (hdm : d ∣ m) :
    divisorReciprocal f d ≤ divisorReciprocal f m := by
  simp only [divisorReciprocal_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hm hdm)
    (fun i _ _ => div_nonneg (hf i) (Nat.cast_nonneg i))

lemma divisorReciprocal_mul_le {f g : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (hg : ∀ m, 0 ≤ g m) {m : ℕ} (hm : m ≠ 0) :
    divisorReciprocal (f * g) m ≤ divisorReciprocal f m * divisorReciprocal g m := by
  rw [divisorReciprocal, reciprocalCoefficients_mul, mul_assoc]
  change (reciprocalCoefficients f * divisorReciprocal g) m ≤ _
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d e => reciprocalCoefficients f d * divisorReciprocal g e)]
  calc
    _ ≤ ∑ d ∈ m.divisors, (f d / d) * divisorReciprocal g m := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (divisorReciprocal_mono_divisor hg hm (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
        (div_nonneg (hf d) (Nat.cast_nonneg d))
    _ = _ := by rw [← Finset.sum_mul, ← divisorReciprocal_apply]

lemma divisorReciprocal_one {m : ℕ} (hm : m ≠ 0) :
    divisorReciprocal (1 : ArithmeticFunction ℝ) m = 1 := by
  have hrec : reciprocalCoefficients (1 : ArithmeticFunction ℝ) = 1 := by
    ext d
    by_cases hd : d = 1 <;> simp [hd]
  rw [divisorReciprocal, hrec, one_mul]
  simp [hm]

lemma divisorReciprocal_pow_le {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    divisorReciprocal (f ^ k) m ≤ (divisorReciprocal f m) ^ k := by
  induction k with
  | zero => simp [divisorReciprocal_one hm]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (divisorReciprocal_mul_le (convolution_pow_nonneg hf k) hf hm).trans
      (mul_le_mul_of_nonneg_right ih (divisorReciprocal_nonneg hf m))

lemma sum_reciprocal_le_divisorReciprocal_factorial {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, f m / m) ≤ divisorReciprocal f (N.factorial) := by
  rw [divisorReciprocal_apply]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hm1 hmN, Nat.factorial_ne_zero N⟩
  · intro m _ _
    exact div_nonneg (hf m) (Nat.cast_nonneg m)

 
theorem sum_primePenalty_pow_reciprocal_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    (k N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ((primePenalty g) ^ k) m / m) ≤
      (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (1 + g p / ((p : ℝ) - 1))) ^ k := by
  have hfactor : (N.factorial).primeFactors = (Finset.Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, hpd, _⟩
      exact ⟨⟨hp.one_le, hp.dvd_factorial.mp hpd⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨hp, hp.dvd_factorial.mpr hpN, Nat.factorial_ne_zero N⟩
  calc
    _ ≤ divisorReciprocal ((primePenalty g) ^ k) (N.factorial) :=
      sum_reciprocal_le_divisorReciprocal_factorial
        (convolution_pow_nonneg (primePenalty_nonneg g hg) k) N
    _ ≤ (divisorReciprocal (primePenalty g) (N.factorial)) ^ k :=
      divisorReciprocal_pow_le (primePenalty_nonneg g hg) k (Nat.factorial_ne_zero N)
    _ ≤ _ := by
      apply pow_le_pow_left₀ (divisorReciprocal_nonneg (primePenalty_nonneg g hg) _)
      rw [← hfactor]
      exact primePenalty_divisorReciprocal_le g hg (Nat.factorial_ne_zero N)


lemma largeFactorConvolution_nonneg {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (k H m : ℕ) : 0 ≤ largeFactorConvolution f k H m := by
  exact Finset.sum_nonneg (fun d _ =>
    mul_nonneg (hf d) (convolution_pow_nonneg hf k (m / d)))

 

lemma convolution_pow_le_largeFactor {f : ArithmeticFunction ℝ}
    (hf : ∀ m, 0 ≤ f m) (k H m : ℕ) (hH : 1 ≤ H) (hm : 2 ≤ m)
    (hlog : 2 * ((k + 1 : ℕ) : ℝ) * Real.log H ≤ Real.log m) :
    (f ^ (k + 1)) m ≤ 2 * ((k + 1 : ℕ) : ℝ) * largeFactorConvolution f k H m := by
  have hH0 : 0 < (H : ℝ) := by exact_mod_cast hH
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm1 : 1 < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hLH : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hLm : 0 < Real.log m := Real.log_pos hm1
  have hk0 : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hcoef : 0 ≤ (f ^ (k + 1)) m := convolution_pow_nonneg hf _ _
  have hlarge : 0 ≤ largeFactorConvolution f k H m := largeFactorConvolution_nonneg hf _ _ _
  have hsum : (f ^ (k + 1)) m = ∑ d ∈ m.divisors, f d * (f ^ k) (m / d) := by
    rw [pow_succ, mul_comm, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d e => f d * (f ^ k) e)]
  have hlogsum : Real.log m * (f ^ (k + 1)) m =
      ((k + 1 : ℕ) : ℝ) * ∑ d ∈ m.divisors,
        Real.log d * (f d * (f ^ k) (m / d)) := by
    have ht := congrArg (fun F : ArithmeticFunction ℝ => F m) (logWeight_pow f k)
    rw [mul_comm (f ^ k) (logWeight f)] at ht
    change Real.log m * (f ^ (k + 1)) m =
      ((k + 1 : ℕ) : ℝ) * (logWeight f * f ^ k) m at ht
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d e => logWeight f d * (f ^ k) e)] at ht
    simpa only [logWeight_apply, mul_assoc] using ht
  have hbound : (∑ d ∈ m.divisors, Real.log d * (f d * (f ^ k) (m / d))) ≤
      Real.log H * (f ^ (k + 1)) m + Real.log m * largeFactorConvolution f k H m := by
    rw [hsum, largeFactorConvolution, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast (Nat.pos_of_mem_divisors hd)
    have hterm : 0 ≤ f d * (f ^ k) (m / d) :=
      mul_nonneg (hf d) (convolution_pow_nonneg hf _ _)
    by_cases hHd : H < d
    · simp only [hHd, ite_true, if_true]
      have hdm : (d : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_dvd (by omega : 0 < m) (Nat.dvd_of_mem_divisors hd))
      exact (mul_le_mul_of_nonneg_right (Real.log_le_log hd0 hdm) hterm).trans
        (le_add_of_nonneg_left (mul_nonneg hLH hterm))
    · simp only [hHd, ite_false, if_false, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right
        (Real.log_le_log hd0 (by exact_mod_cast (Nat.le_of_not_gt hHd))) hterm
  have hprod := mul_le_mul_of_nonneg_left hbound hk0.le
  rw [← hlogsum] at hprod
  have haux := mul_le_mul_of_nonneg_right hlog hcoef
  nlinarith

 

lemma sum_divisor_large_interval {A : Type*} [AddCommMonoid A]
    (F : ℕ → ℕ → A) (a b H : ℕ) :
    (∑ m ∈ Finset.Ioc a b, ∑ d ∈ m.divisors.filter (H < ·), F d (m / d)) =
      ∑ e ∈ Finset.Icc 1 (b / (H + 1)),
        ∑ d ∈ (Finset.Ioc (a / e) (b / e)).filter (H < ·), F d e := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => ⟨p.1 / p.2, p.2⟩)
  · intro p hp
    obtain ⟨hpm, hpd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hdm, hHd⟩ := Finset.mem_filter.mp hpd
    obtain ⟨ham, hmb⟩ := Finset.mem_Ioc.mp hpm
    have hm0 : 0 < p.1 := by omega
    have hd0 := Nat.pos_of_mem_divisors hdm
    have hdvd := Nat.dvd_of_mem_divisors hdm
    have he0 : 0 < p.1 / p.2 := Nat.div_pos (Nat.le_of_dvd hm0 hdvd) hd0
    have hmul : p.2 * (p.1 / p.2) = p.1 := Nat.mul_div_cancel' hdvd
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      refine ⟨he0, (Nat.le_div_iff_mul_le (by omega : 0 < H + 1)).mpr ?_⟩
      calc
        (p.1 / p.2) * (H + 1) ≤ (p.1 / p.2) * p.2 := Nat.mul_le_mul_left _ (by omega)
        _ = p.1 := by simpa [mul_comm] using hmul
        _ ≤ b := hmb
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hHd⟩
      · exact (Nat.div_lt_iff_lt_mul he0).mpr (by simpa [hmul] using ham)
      · exact (Nat.le_div_iff_mul_le he0).mpr (by simpa [hmul] using hmb)
  · intro p hp q hq hpq
    obtain ⟨_, hpd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨_, hqd⟩ := Finset.mem_sigma.mp hq
    have hd : p.2 = q.2 := by simpa using congrArg Sigma.snd hpq
    have he : p.1 / p.2 = q.1 / q.2 := congrArg Sigma.fst hpq
    have hm : p.1 = q.1 := by
      calc
        _ = p.2 * (p.1 / p.2) :=
          (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hpd).1)).symm
        _ = q.2 * (q.1 / q.2) := by rw [he, hd]
        _ = _ := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hqd).1)
    cases p
    cases q
    simp_all
  · intro q hq
    obtain ⟨hqe, hqd⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hqd, hHd⟩ := Finset.mem_filter.mp hqd
    have he0 : 0 < q.1 := (Finset.mem_Icc.mp hqe).1
    have hd0 : 0 < q.2 := by omega
    obtain ⟨had, hdb⟩ := Finset.mem_Ioc.mp hqd
    refine ⟨⟨q.2 * q.1, q.2⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul he0).mp had,
        (Nat.le_div_iff_mul_le he0).mp hdb⟩
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨dvd_mul_right _ _, by positivity⟩, hHd⟩
    · simp [Nat.mul_div_cancel_left _ hd0]
  · intro p _
    rfl

lemma sum_largeFactorConvolution_le (f : ArithmeticFunction ℝ)
    (hf : ∀ m, 0 ≤ f m) (k a b H : ℕ) :
    (∑ m ∈ Finset.Ioc a b, largeFactorConvolution f k H m) ≤
      ∑ e ∈ Finset.Icc 1 (b / (H + 1)), (f ^ k) e *
        ∑ d ∈ Finset.Ioc (a / e) (b / e), f d := by
  simp only [largeFactorConvolution]
  rw [sum_divisor_large_interval (fun d e => f d * (f ^ k) e)]
  apply Finset.sum_le_sum
  intro e _
  rw [← Finset.sum_mul, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (convolution_pow_nonneg hf k e)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun d _ _ => hf d)

end PrimeDegreePackets.Sieve
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PenaltyEuler
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma penaltyEuler_one_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) (N : ℕ) :
    1 ≤ penaltyEuler g N := by
  apply Finset.one_le_prod
  intro p hp
  have hp1 : 1 < (p : ℝ) := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  exact le_add_of_nonneg_right (div_nonneg (hg p) (by linarith))

lemma penaltyEuler_mono (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    {N M : ℕ} (hNM : N ≤ M) : penaltyEuler g N ≤ penaltyEuler g M := by
  apply Finset.prod_le_prod_of_subset_of_one_le
  · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hNM)
  · intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact add_nonneg (by norm_num) (div_nonneg (hg p) (by linarith))
  · intro p hp _
    have hp1 : 1 < (p : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact le_add_of_nonneg_right (div_nonneg (hg p) (by linarith))

lemma primePenalty_le_softWeight (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) {m : ℕ} (hm : m ≠ 0) :
    primePenalty g m ≤ softWeight S g m := by
  have hsoft : softWeight S g m = ∏ p ∈ S.filter (· ∣ m), g p := by
    rw [softWeight, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hpd : p ∣ m
    · simp [hpd, (hS p hp).coprime_iff_not_dvd]
    · simp [hpd, (hS p hp).coprime_iff_not_dvd]
  have hsub : S.filter (· ∣ m) ⊆ m.primeFactors := by
    intro p hp
    obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hS p hpS, hpd, hm⟩
  rw [primePenalty_apply g hm, hsoft, ← Finset.prod_sdiff hsub]
  have hrem : (∏ p ∈ m.primeFactors \ S.filter (· ∣ m), g p) ≤ 1 :=
    Finset.prod_le_one (fun prime _ => (hg prime).1) (fun prime _ => (hg prime).2)
  simpa using mul_le_mul_of_nonneg_right hrem
    (Finset.prod_nonneg (fun p _ => (hg p).1))

lemma primePenalty_interval_bound (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (a b z B : ℕ)
    (hab : a ≤ b) (hz : 1 ≤ z) (hzB : z ≤ B) :
    (∑ m ∈ Finset.Ioc a b, primePenalty g m) ≤
      (((b : ℝ) - a) / Real.log (z + 1)) * penaltyEuler g B +
        ((z : ℝ) * (z + 1)) ^ 2 := by
  apply (Finset.sum_le_sum (s := Finset.Ioc a b) (g := softWeight (smallPrimes B) g) ?_).trans
    (soft_interval_bound a b z (smallPrimes B) g hab hz ?_ ?_ hg)
  · intro m hm
    exact primePenalty_le_softWeight _ (fun p hp => (Finset.mem_filter.mp hp).2) g hg
      (by have := (Finset.mem_Ioc.mp hm).1; omega)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp hpz
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpz.trans hzB⟩, hp⟩

lemma interval_div_length_le (a b e : ℕ) (he : 0 < e) :
    ((b / e : ℕ) : ℝ) - (a / e : ℕ) ≤ ((b : ℝ) - a) / e + 1 := by
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hb : ((b / e : ℕ) : ℝ) * e ≤ b := by exact_mod_cast Nat.div_mul_le_self b e
  have ha : (a : ℝ) < (((a / e : ℕ) : ℝ) + 1) * e := by
    exact_mod_cast (Nat.div_lt_iff_lt_mul he).mp (Nat.lt_succ_self (a / e))
  calc
    _ ≤ ((b : ℝ) - a + e) / e := (le_div_iff₀ heR).mpr (by nlinarith)
    _ = _ := by rw [add_div, div_self heR.ne']

lemma sum_le_mul_sum_reciprocal (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, F m) ≤
      N * ∑ m ∈ Finset.Icc 1 N, F m / m := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  obtain ⟨hm0, hmN⟩ := Finset.mem_Icc.mp hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  calc
    F m = m * (F m / m) := by field_simp
    _ ≤ N * (F m / m) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hmN) (div_nonneg (hF m) hmR.le)

lemma primePenalty_pow_reciprocal_le (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p)
    (k N B : ℕ) (hNB : N ≤ B) :
    (∑ m ∈ Finset.Icc 1 N, ((primePenalty g) ^ k) m / m) ≤
      (penaltyEuler g B) ^ k := by
  exact (sum_primePenalty_pow_reciprocal_le g hg k N).trans
    (pow_le_pow_left₀ ((zero_le_one : (0 : ℝ) ≤ 1).trans (penaltyEuler_one_le g hg N))
      (penaltyEuler_mono g hg hNB) k)

 

theorem sum_primePenalty_largeFactor_bound (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (k a b H z : ℕ)
    (hab : a ≤ b) (hz : 1 ≤ z) (hzb : z ≤ b) :
    (∑ m ∈ Finset.Ioc a b, largeFactorConvolution (primePenalty g) k H m) ≤
      (penaltyEuler g b) ^ k *
       ((((b : ℝ) - a) / Real.log (z + 1)) * penaltyEuler g b +
        (b / (H + 1) : ℕ) *
          (penaltyEuler g b / Real.log (z + 1) + ((z : ℝ) * (z + 1)) ^ 2)) := by
  let E := penaltyEuler g b
  let L := Real.log (z + 1)
  let R := ((z : ℝ) * (z + 1)) ^ 2
  let N := b / (H + 1)
  let F := ((primePenalty g) ^ k)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < z + 1 by omega))
  have hE : 0 ≤ E := (zero_le_one : (0 : ℝ) ≤ 1).trans (penaltyEuler_one_le g (fun p => (hg p).1) b)
  have hR : 0 ≤ R := sq_nonneg _
  have hy : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hF : ∀ m, 0 ≤ F m := convolution_pow_nonneg (primePenalty_nonneg g (fun p => (hg p).1)) k
  have hNM : N ≤ b := Nat.div_le_self _ _
  have hrec : (∑ e ∈ Finset.Icc 1 N, F e / e) ≤ E ^ k :=
    primePenalty_pow_reciprocal_le g (fun p => (hg p).1) k N b hNM
  have hsum : (∑ e ∈ Finset.Icc 1 N, F e) ≤ N * E ^ k :=
    (sum_le_mul_sum_reciprocal F hF N).trans
      (mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg N))
  calc
    _ ≤ ∑ e ∈ Finset.Icc 1 N, F e *
        ∑ d ∈ Finset.Ioc (a / e) (b / e), primePenalty g d :=
      sum_largeFactorConvolution_le _ (primePenalty_nonneg g (fun p => (hg p).1)) k a b H
    _ ≤ ∑ e ∈ Finset.Icc 1 N, F e *
        (((((b : ℝ) - a) / e + 1) / L) * E + R) := by
      apply Finset.sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_left _ (hF e)
      apply (primePenalty_interval_bound g hg (a / e) (b / e) z b
        (Nat.div_le_div_right hab) hz hzb).trans
      exact _root_.add_le_add
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (interval_div_length_le a b e (Finset.mem_Icc.mp he).1) hL.le) hE) (le_refl R)
    _ = (((b : ℝ) - a) / L * E) * (∑ e ∈ Finset.Icc 1 N, F e / e) +
          (E / L + R) * (∑ e ∈ Finset.Icc 1 N, F e) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ ≤ (((b : ℝ) - a) / L * E) * E ^ k + (E / L + R) * (N * E ^ k) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hrec (mul_nonneg (div_nonneg hy hL.le) hE))
        (mul_le_mul_of_nonneg_left hsum (add_nonneg (div_nonneg hE hL.le) hR))
    _ = _ := by ring

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma sum_primePenalty_largeFactor_bound' (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (k a b H z : ℕ)
    (hab : a ≤ b) (hz : 1 ≤ z) (hzb : z ≤ b) :
    (∑ m ∈ Finset.Ioc a b, largeFactorConvolution (primePenalty g) k H m) ≤
      (penaltyEuler g b) ^ (k + 1) *
       (((b : ℝ) - a) / Real.log (z + 1) +
        (b / (H + 1) : ℕ) *
          ((Real.log (z + 1))⁻¹ + ((z : ℝ) * (z + 1)) ^ 2)) := by
  have hE := penaltyEuler_one_le g (fun p => (hg p).1) b
  have hE0 : 0 ≤ penaltyEuler g b := by linarith
  have hR : 0 ≤ ((z : ℝ) * (z + 1)) ^ 2 := sq_nonneg _
  apply (sum_primePenalty_largeFactor_bound g hg k a b H z hab hz hzb).trans
  rw [pow_succ (penaltyEuler g b) k, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hE0 k)
  have hNR : 0 ≤ (b / (H + 1) : ℕ) * ((z : ℝ) * (z + 1)) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) hR
  have hx := mul_le_mul_of_nonneg_right hE hNR
  simp only [one_mul] at hx
  simp only [div_eq_mul_inv]
  nlinarith only [hx]

 

theorem primePenalty_pow_interval_finite (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (k a b H z : ℕ)
    (hab : a ≤ b) (hH : 1 ≤ H) (hz : 1 ≤ z) (hzb : z ≤ b)
    (hTb : H ^ (2 * (k + 1)) ≤ b) :
    (∑ m ∈ Finset.Ioc a b, ((primePenalty g) ^ (k + 1)) m) ≤
      (penaltyEuler g b) ^ (k + 1) *
        ((H ^ (2 * (k + 1)) : ℕ) + 2 * ((k + 1 : ℕ) : ℝ) *
          (((b : ℝ) - a) / Real.log (z + 1) +
            (b / (H + 1) : ℕ) *
              ((Real.log (z + 1))⁻¹ + ((z : ℝ) * (z + 1)) ^ 2))) := by
  let f := primePenalty g
  let T := H ^ (2 * (k + 1))
  let E := penaltyEuler g b
  have hf : ∀ m, 0 ≤ f m := primePenalty_nonneg g (fun p => (hg p).1)
  have hFn : ∀ m, 0 ≤ (f ^ (k + 1)) m := convolution_pow_nonneg hf _
  have hTpos : 0 < T := pow_pos (by omega) _
  have hpoint : ∀ m ∈ Finset.Ioc a b, (f ^ (k + 1)) m ≤
      (if m ≤ T then (f ^ (k + 1)) m else 0) +
        2 * ((k + 1 : ℕ) : ℝ) * largeFactorConvolution f k H m := by
    intro m _
    split_ifs with hmT
    · exact le_add_of_nonneg_right (mul_nonneg (by positivity)
        (largeFactorConvolution_nonneg hf _ _ _))
    · rw [zero_add]
      apply convolution_pow_le_largeFactor hf k H m hH (by omega)
      have hTm : (T : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hmT))
      have hl := Real.log_le_log (by exact_mod_cast hTpos) hTm
      simpa [T, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        mul_assoc] using hl
  have hsmall : (∑ m ∈ Finset.Ioc a b, if m ≤ T then (f ^ (k + 1)) m else 0) ≤
      T * E ^ (k + 1) := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 T, (f ^ (k + 1)) m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨hm, hmT⟩ := Finset.mem_filter.mp hm
          exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hm).1; omega, hmT⟩
        · intro m _ _
          exact hFn m
      _ ≤ T * ∑ m ∈ Finset.Icc 1 T, (f ^ (k + 1)) m / m :=
        sum_le_mul_sum_reciprocal _ hFn T
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (primePenalty_pow_reciprocal_le g (fun p => (hg p).1) (k + 1) T b hTb)
        (Nat.cast_nonneg T)
  have hlarge := sum_primePenalty_largeFactor_bound' g hg k a b H z hab hz hzb
  calc
    _ ≤ ∑ m ∈ Finset.Ioc a b,
        ((if m ≤ T then (f ^ (k + 1)) m else 0) +
          2 * ((k + 1 : ℕ) : ℝ) * largeFactorConvolution f k H m) :=
      Finset.sum_le_sum hpoint
    _ = (∑ m ∈ Finset.Ioc a b, if m ≤ T then (f ^ (k + 1)) m else 0) +
        2 * ((k + 1 : ℕ) : ℝ) * (∑ m ∈ Finset.Ioc a b, largeFactorConvolution f k H m) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ T * E ^ (k + 1) + 2 * ((k + 1 : ℕ) : ℝ) *
        ((penaltyEuler g b) ^ (k + 1) *
          (((b : ℝ) - a) / Real.log (z + 1) +
            (b / (H + 1) : ℕ) *
              ((Real.log (z + 1))⁻¹ + ((z : ℝ) * (z + 1)) ^ 2))) := by
      exact _root_.add_le_add hsmall (mul_le_mul_of_nonneg_left hlarge (by positivity))
    _ = _ := by dsimp [T, E] <;> ring

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

 

lemma sieve_error_scaled (z b N T n : ℝ) (hz : 1 ≤ z)
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hn : 0 ≤ n)
    (hTz : T * z ^ 2 ≤ b) (hNz : N * z ^ 6 ≤ b) :
    T * Real.log (z + 1) + 2 * n * N *
      (1 + Real.log (z + 1) * (z * (z + 1)) ^ 2) ≤ (1 + 10 * n) * b / z := by
  have hz0 : 0 < z := by linarith
  have hL0 : 0 ≤ Real.log (z + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log (z + 1) ≤ z := by
    have ht := Real.log_le_sub_one_of_pos (show 0 < z + 1 by linarith)
    linarith
  have hR : (z * (z + 1)) ^ 2 ≤ 4 * z ^ 4 := by
    have ht : z + 1 ≤ 2 * z := by linarith
    have hu := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ z + 1) ht 2
    nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hu)]
  have hz6 : z ≤ z ^ 6 := by
    simpa using (pow_le_pow_right₀ hz (show 1 ≤ 6 by omega))
  have hLR : Real.log (z + 1) * (z * (z + 1)) ^ 2 ≤ 4 * z ^ 5 := by
    calc
      _ ≤ z * (4 * z ^ 4) := mul_le_mul hL hR (sq_nonneg _) (le_trans (by norm_num) hz)
      _ = _ := by ring
  have hpoly : z * (1 + Real.log (z + 1) * (z * (z + 1)) ^ 2) ≤ 5 * z ^ 6 := by
    have ht := mul_le_mul_of_nonneg_left hLR hz0.le
    nlinarith only [ht, hz6]
  have hsmall : T * Real.log (z + 1) * z ≤ b := by
    calc
      _ ≤ T * z * z := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hL hT) hz0.le
      _ = T * z ^ 2 := by ring
      _ ≤ b := hTz
  have hlarge : N * (1 + Real.log (z + 1) * (z * (z + 1)) ^ 2) * z ≤ 5 * b := by
    calc
      _ = N * (z * (1 + Real.log (z + 1) * (z * (z + 1)) ^ 2)) := by ring
      _ ≤ N * (5 * z ^ 6) := mul_le_mul_of_nonneg_left hpoly hN
      _ = 5 * (N * z ^ 6) := by ring
      _ ≤ 5 * b := by linarith
  apply (le_div_iff₀ hz0).mpr
  have ht := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 2 * n by positivity)
  nlinarith only [ht, hsmall]

lemma primePenalty_pow_interval_at_level (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (k a b z : ℕ) (η : ℝ)
    (hab : a ≤ b) (hz : 2 ≤ z) (_hη : 0 < η)
    (hrel : η * b ≤ (b : ℝ) - a)
    (hsize : 1 + 10 * ((k + 1 : ℕ) : ℝ) ≤ η * z)
    (hroot : z ^ (12 * (k + 1) + 2) ≤ b)
    (hroot' : b < (z + 1) ^ (12 * (k + 1) + 2)) :
    (∑ m ∈ Finset.Ioc a b, ((primePenalty g) ^ (k + 1)) m) ≤
      ((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + 1) *
        (((b : ℝ) - a) / Real.log b) * (penaltyEuler g b) ^ (k + 1) := by
  let n : ℝ := (k + 1 : ℕ)
  let H := z ^ 6
  let T := H ^ (2 * (k + 1))
  let N := b / (H + 1)
  let L := Real.log ((z : ℝ) + 1)
  let R := ((z : ℝ) * (z + 1)) ^ 2
  let E := (penaltyEuler g b) ^ (k + 1)
  have hz1 : 1 ≤ z := by omega
  have hzR : 1 ≤ (z : ℝ) := by exact_mod_cast hz1
  have hz0 : 0 < (z : ℝ) := by linarith
  have hzb : z ≤ b := (Nat.le_self_pow (by omega : 12 * (k + 1) + 2 ≠ 0) z).trans hroot
  have hb1 : 1 < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hL : 0 < L := Real.log_pos (by linarith)
  have hE : 0 ≤ E := pow_nonneg
    ((zero_le_one : (0 : ℝ) ≤ 1).trans (penaltyEuler_one_le g (fun p => (hg p).1) b)) _
  have hH : 1 ≤ H := one_le_pow₀ hz1
  have hTb : T ≤ b := by
    dsimp [T, H]
    rw [← pow_mul]
    apply (Nat.pow_le_pow_right hz1 (show 6 * (2 * (k + 1)) ≤ 12 * (k + 1) + 2 by omega)).trans hroot
  have hTz : (T : ℝ) * (z : ℝ) ^ 2 ≤ b := by
    have hnat : T * z ^ 2 = z ^ (12 * (k + 1) + 2) := by
      dsimp [T, H]
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    exact_mod_cast (hnat ▸ hroot)
  have hNz : (N : ℝ) * (z : ℝ) ^ 6 ≤ b := by
    have hNat : N * H ≤ b := (Nat.mul_le_mul_left N (Nat.le_succ H)).trans (Nat.div_mul_le_self b (H + 1))
    exact_mod_cast hNat
  have herr := sieve_error_scaled (z : ℝ) b N T n hzR (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) hTz hNz
  have hsize' : (1 + 10 * n) * (b : ℝ) / z ≤ η * b := by
    apply (div_le_iff₀ hz0).mpr
    have ht := mul_le_mul_of_nonneg_right hsize hb0
    dsimp [n]
    nlinarith only [ht]
  have herr' : (T : ℝ) * L + 2 * n * N * (1 + L * R) ≤ (b : ℝ) - a :=
    herr.trans (hsize'.trans hrel)
  have hbracket : (T : ℝ) + 2 * n * (((b : ℝ) - a) / L + N * (L⁻¹ + R)) ≤
      (2 * n + 1) * ((b : ℝ) - a) / L := by
    apply (le_div_iff₀ hL).mpr
    have hident : ((T : ℝ) + 2 * n * (((b : ℝ) - a) / L + N * (L⁻¹ + R))) * L =
        2 * n * ((b : ℝ) - a) + ((T : ℝ) * L + 2 * n * N * (1 + L * R)) := by
      field_simp
      ring
    rw [hident]
    nlinarith only [herr']
  have hlog : Real.log b ≤ ((12 * (k + 1) + 2 : ℕ) : ℝ) * L := by
    have ht := Real.log_le_log (show 0 < (b : ℝ) by linarith)
      (show (b : ℝ) ≤ ((z : ℝ) + 1) ^ (12 * (k + 1) + 2) by exact_mod_cast hroot'.le)
    rwa [Real.log_pow] at ht
  have hy : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hratio : (2 * n + 1) * ((b : ℝ) - a) / L ≤
      ((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * n + 1) * (((b : ℝ) - a) / Real.log b) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hL hlogb).mpr
    have ht := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (2 * n + 1) * ((b : ℝ) - a) by positivity)
    nlinarith only [ht]
  calc
    _ ≤ E * ((T : ℝ) + 2 * n * (((b : ℝ) - a) / L + N * (L⁻¹ + R))) :=
      primePenalty_pow_interval_finite g hg k a b H z hab hH hz1 hzb hTb
    _ ≤ E * ((2 * n + 1) * ((b : ℝ) - a) / L) := mul_le_mul_of_nonneg_left hbracket hE
    _ ≤ E * (((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * n + 1) * (((b : ℝ) - a) / Real.log b)) :=
      mul_le_mul_of_nonneg_left hratio hE
    _ = _ := by dsimp [n, E] <;> ring

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

 

theorem primePenalty_pow_interval_uniform (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ (g : ℕ → ℝ), (∀ p, 0 ≤ g p ∧ g p ≤ 1) →
      ∀ a b : ℕ, B ≤ b → a ≤ b → η * b ≤ (b : ℝ) - a →
      (∑ m ∈ Finset.Ioc a b, ((primePenalty g) ^ (k + 1)) m) ≤
        ((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + 1) *
          (((b : ℝ) - a) / Real.log b) * (penaltyEuler g b) ^ (k + 1) := by
  obtain ⟨Z, hZ⟩ := exists_nat_ge ((1 + 10 * ((k + 1 : ℕ) : ℝ)) / η)
  let W := max 2 Z
  let r := 12 * (k + 1) + 2
  have hr : r ≠ 0 := by omega
  refine ⟨W ^ r, ?_⟩
  intro g hg a b hb hab hrel
  let z := Nat.nthRoot r b
  have hW : W ≤ z := (Nat.le_nthRoot_iff hr).mpr hb
  have hz : 2 ≤ z := (le_max_left 2 Z).trans hW
  have hZz : (Z : ℝ) ≤ z := by exact_mod_cast (le_max_right 2 Z).trans hW
  have hsize : 1 + 10 * ((k + 1 : ℕ) : ℝ) ≤ η * z := by
    have ht := (div_le_iff₀ hη).mp (hZ.trans hZz)
    linarith
  exact primePenalty_pow_interval_at_level g hg k a b z η hab hz hη hrel hsize
    (Nat.pow_nthRoot_le (.inl hr)) (Nat.lt_pow_nthRoot_add_one hr b)

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma reciprocal_gap_sum (b : ℕ) (hb : 1 ≤ b) :
    (∑ p ∈ Finset.Icc 2 b, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) =
      1 - 1 / (b : ℝ) := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    ring

lemma prime_reciprocal_gap_le_one (b : ℕ) :
    (∑ p ∈ smallPrimes b, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) ≤ 1 := by
  by_cases hb : b = 0
  · simp [hb, smallPrimes]
  have hsub : smallPrimes b ⊆ Finset.Icc 2 b := by
    intro p hp
    obtain ⟨hp, hpr⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hpr.two_le, (Finset.mem_Icc.mp hp).2⟩
  calc
    _ ≤ ∑ p ∈ Finset.Icc 2 b, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hp1 : 1 < (p : ℝ) := by exact_mod_cast (show 1 < p from (Finset.mem_Icc.mp hp).1)
      apply sub_nonneg.mpr
      exact div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)
    _ = 1 - 1 / (b : ℝ) := reciprocal_gap_sum b (by omega)
    _ ≤ 1 := by
      have hb0 : 0 ≤ (1 : ℝ) / (b : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg b)
      linarith only [hb0]

lemma penaltyEuler_le_exp (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (b : ℕ) :
    penaltyEuler g b ≤ Real.exp (1 + ∑ p ∈ smallPrimes b, g p / p) := by
  have hsum : (∑ p ∈ smallPrimes b, g p / ((p : ℝ) - 1)) ≤
      1 + ∑ p ∈ smallPrimes b, g p / p := by
    calc
      _ ≤ ∑ p ∈ smallPrimes b, (g p / p + (1 / ((p : ℝ)-1) - 1 / p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
        have hi : 0 ≤ 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) :=
          sub_nonneg.mpr (div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith))
        have ht := mul_le_mul_of_nonneg_right (hg p).2 hi
        simp only [div_eq_mul_inv] at ht ⊢
        nlinarith only [ht]
      _ = (∑ p ∈ smallPrimes b, g p / p) +
          (∑ p ∈ smallPrimes b, (1 / ((p : ℝ)-1) - 1 / p)) := Finset.sum_add_distrib
      _ ≤ _ := by linarith only [prime_reciprocal_gap_le_one b]
  calc
    _ ≤ ∏ p ∈ smallPrimes b, Real.exp (g p / ((p : ℝ) - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
        exact add_nonneg zero_le_one (div_nonneg (hg p).1 (by linarith))
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (g p / ((p : ℝ) - 1))
    _ = Real.exp (∑ p ∈ smallPrimes b, g p / ((p : ℝ) - 1)) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

lemma penaltyEuler_pow_le_exp (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (b n : ℕ) :
    (penaltyEuler g b)^n ≤ Real.exp n * Real.exp (∑ p ∈ smallPrimes b, (n : ℝ) * g p / p) := by
  have hE : 0 ≤ penaltyEuler g b := zero_le_one.trans (penaltyEuler_one_le g (fun p => (hg p).1) b)
  calc
    _ ≤ (Real.exp (1 + ∑ p ∈ smallPrimes b, g p / p))^n :=
      pow_le_pow_left₀ hE (penaltyEuler_le_exp g hg b) n
    _ = Real.exp ((n : ℝ) * (1 + ∑ p ∈ smallPrimes b, g p / p)) := (Real.exp_nat_mul _ n).symm
    _ = _ := by
      rw [mul_add, mul_one, Real.exp_add, Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro p _
      ring

 

theorem primePenalty_pow_relative_interval (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ (g : ℕ → ℝ), (∀ p, 0 ≤ g p ∧ g p ≤ 1) →
      ∀ a b : ℕ, B ≤ b → a ≤ b → η * b ≤ (b : ℝ) - a →
      (∑ m ∈ Finset.Ioc a b, ((primePenalty g) ^ (k + 1)) m) ≤
        (((12 * (k + 1) + 2 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + 1) * Real.exp (k+1)) *
          (((b : ℝ) - a) / Real.log b) *
            Real.exp (∑ p ∈ smallPrimes b, ((k + 1 : ℕ) : ℝ) * g p / p) := by
  obtain ⟨B, hB⟩ := primePenalty_pow_interval_uniform k η hη
  refine ⟨B, ?_⟩
  intro g hg a b hb hab hrel
  apply (hB g hg a b hb hab hrel).trans
  have hlog : 0 ≤ Real.log (b : ℝ) := by
    by_cases hb0 : b = 0
    · simp [hb0]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega))
  have hy : 0 ≤ (b : ℝ)-a := sub_nonneg.mpr (by exact_mod_cast hab)
  have ht := mul_le_mul_of_nonneg_left (penaltyEuler_pow_le_exp g hg b (k+1))
    (show 0 ≤ ((12 * (k+1)+2 : ℕ) : ℝ) * (2*((k+1 : ℕ):ℝ)+1) * (((b : ℝ)-a)/Real.log b) by positivity)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end PrimeDegreePackets.Sieve
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_SieveConvolution
attribute [-instance] _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma convolution_prime {R : Type*} [Semiring R] (f g : ArithmeticFunction R)
    {p : ℕ} (hp : p.Prime) : (f*g) p = f 1 * g p + f p * g 1 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)]
  rw [hp.sum_divisors]
  simp [Nat.div_self hp.pos, add_comm]

lemma convolution_pow_prime {R : Type*} [CommSemiring R] (f : ArithmeticFunction R)
    (h1 : f 1 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) : (f^k) p = k * f p := by
  induction k with
  | zero => simp [hp.ne_one]
  | succ k ih =>
    rw [pow_succ, convolution_prime _ _ hp, ih]
    have hk1 : (f^k) 1 = 1 := by
      clear ih
      induction k with
      | zero => simp
      | succ k ih => simp only [pow_succ, ArithmeticFunction.mul_apply_one, ih, h1, one_mul]
    rw [hk1, h1]
    push_cast
    ring

lemma nFoldDivisor_prime (k : ℕ) {p : ℕ} (hp : p.Prime) :
    nFoldDivisor k p = k := by
  unfold nFoldDivisor
  rw [convolution_pow_prime _ (by simp) hp]
  simp [ArithmeticFunction.zeta_apply, hp.ne_zero]

lemma mul_le_of_prime_power_le (f g : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (hf0 : ∀m, 0 ≤ f m) (h : ∀ p j, p.Prime → f (p^j) ≤ g (p^j)) (m : ℕ) :
    f m ≤ g m := by
  by_cases hm : m = 0
  · simp [hm]
  rw [hf.multiplicative_factorization f hm, hg.multiplicative_factorization g hm]
  apply Finset.prod_le_prod
  · intro p _
    exact hf0 _
  · intro p hp
    exact h p _ (Nat.prime_of_mem_primeFactors hp)



lemma coefficientPenalty_bounds (k : ℕ) (b : ArithmeticFunction ℝ)
    (hb : ∀m, 0 ≤ b m ∧ b m ≤ nFoldDivisor (k+1) m) (p : ℕ) :
    0 ≤ coefficientPenalty k b p ∧ coefficientPenalty k b p ≤ 1 := by
  unfold coefficientPenalty
  split_ifs with hp
  · constructor
    · exact div_nonneg (hb p).1 (by positivity)
    · apply (div_le_one (by positivity : (0:ℝ) < k+1)).mpr
      simpa [nFoldDivisor_prime _ hp] using (hb p).2
  · exact ⟨le_rfl, zero_le_one⟩

lemma coefficientPenalty_prime (k : ℕ) (b : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    (k+1 : ℝ) * coefficientPenalty k b p = b p := by
  simp only [coefficientPenalty, ite_eq_left hp]
  have hk : (k+1:ℝ) ≠ 0 := by positivity
  field_simp

lemma convolution_ge_left (f g : ArithmeticFunction ℝ) (hf : ∀m, 0 ≤ f m)
    (hg : ∀m, 0 ≤ g m) (hg1 : g 1 = 1) {m : ℕ} (hm : m ≠ 0) :
    f m ≤ (f*g) m := by
  rw [ArithmeticFunction.mul_apply]
  have hd : (m,1) ∈ m.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hm⟩
  simpa [hg1] using Finset.single_le_sum (fun de _ => mul_nonneg (hf de.1) (hg de.2)) hd

 

theorem divisor_bounded_majorant (k : ℕ) (b : ArithmeticFunction ℝ)
    (hmult : b.IsMultiplicative) (hb : ∀m, 0 ≤ b m ∧ b m ≤ nFoldDivisor (k+1) m)
    (m : ℕ) :
    b m ≤ (powerfulFunction k * (primePenalty (coefficientPenalty k b))^(k+1)) m := by
  let f := primePenalty (coefficientPenalty k b)
  have hf : f.IsMultiplicative := primePenalty_multiplicative _
  have hf0 : ∀m, 0 ≤ f m := primePenalty_nonneg _ (fun p => (coefficientPenalty_bounds k b hb p).1)
  have hF0 : ∀m, 0 ≤ (f^(k+1)) m := convolution_pow_nonneg hf0 _
  have hP0 : ∀m, 0 ≤ powerfulFunction k m := powerfulCorrection_nonneg k
  apply mul_le_of_prime_power_le b _ hmult ((powerfulFunction_multiplicative k).mul hf.pow)
    (fun m => (hb m).1) _ m
  intro p j hp
  by_cases hj0 : j=0
  · simp [hj0, hmult.map_one, ((powerfulFunction_multiplicative k).mul hf.pow).map_one]
  by_cases hj1 : j=1
  · have hfprime : (f^(k+1)) p = b p := by
      rw [convolution_pow_prime _ hf.map_one hp]
      have hp1 : f p = coefficientPenalty k b p := by
        simpa only [pow_one] using primePenalty_prime_pow (coefficientPenalty k b) hp (by omega : 1 ≠ 0)
      rw [hp1]
      simpa using coefficientPenalty_prime k b hp
    rw [hj1, pow_one]
    rw [mul_comm]
    rw [← hfprime]
    exact convolution_ge_left _ _ hF0 hP0 (powerfulCorrection_one k) hp.ne_zero
  · have hj2 : 2 ≤ j := by omega
    calc
      b (p^j) ≤ (nFoldDivisor (k+1) (p^j) : ℝ) := (hb _).2
      _ = powerfulFunction k (p^j) := by
        simp [powerfulFunction_apply, powerfulCorrection, isPowerful_prime_pow hp hj2]
      _ ≤ (powerfulFunction k * f^(k+1)) (p^j) :=
        convolution_ge_left _ _ hP0 hF0 hf.pow.map_one (pow_ne_zero _ hp.ne_zero)

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma nFoldDivisor_real (k m : ℕ) :
    (nFoldDivisor k m : ℝ) = ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)^k) m := by
  induction k generalizing m with
  | zero => simp [nFoldDivisor, ArithmeticFunction.one_apply]
  | succ k ih =>
    rw [nFoldDivisor_succ, pow_succ, ArithmeticFunction.coe_mul_zeta_apply]
    push_cast
    exact Finset.sum_congr rfl (fun d _ => ih d)

lemma primePenalty_pow_le_divisor (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p ∧ g p ≤ 1) (k m : ℕ) :
    ((primePenalty g)^k) m ≤ nFoldDivisor k m := by
  rw [nFoldDivisor_real]
  induction k generalizing m with
  | zero => exact le_rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    apply Finset.sum_le_sum
    intro de hde
    have he0 : de.2 ≠ 0 := by
      obtain ⟨hm, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hde
      intro h; simp_all
    apply mul_le_mul (ih de.1) _ (primePenalty_nonneg g (fun p => (hg p).1) de.2)
      (by rw [← nFoldDivisor_real]; positivity)
    simpa [ArithmeticFunction.zeta_apply, he0] using primePenalty_le_one g hg de.2

lemma convolution_sum_interval (f g : ArithmeticFunction ℝ) (a b : ℕ) :
    (∑ m ∈ Finset.Ioc a b, (f*g) m) =
      ∑ d ∈ Finset.Icc 1 b, g d * ∑ e ∈ Finset.Ioc (a/d) (b/d), f e := by
  have hdiv : ∀ m : ℕ, m.divisors.filter (0 < ·) = m.divisors := by
    intro m
    exact Finset.filter_eq_self.mpr (fun d hd => Nat.pos_of_mem_divisors hd)
  have hint : ∀ d : ℕ, (Finset.Ioc (a/d) (b/d)).filter (0 < ·) = Finset.Ioc (a/d) (b/d) := by
    intro d
    apply Finset.filter_eq_self.mpr
    intro e he
    exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp he).1
  simp only [ArithmeticFunction.mul_apply]
  simp_rw [Nat.sum_divisorsAntidiagonal (fun u v => f u * g v)]
  have hid := sum_divisor_large_interval (fun u v => f u * g v) a b 0
  simp only [hdiv, hint, zero_add, Nat.div_one] at hid
  rw [hid]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_mul, mul_comm]

lemma primePenalty_pow_initial_le (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p ∧ g p ≤ 1) (k N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ((primePenalty g)^(k+1)) m) ≤
      (N:ℝ) * (1 + Real.log N)^k := by
  apply (Finset.sum_le_sum (fun m _ => primePenalty_pow_le_divisor g hg (k+1) m)).trans
  exact nFoldDivisor_summatory_le k N

lemma primePenalty_pow_interval_trivial (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p ∧ g p ≤ 1)
    (k a b d : ℕ) (hd : 0 < d) :
    (∑ m ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) m) ≤
      ((b:ℝ)/d) * (1 + Real.log b)^k := by
  have hf0 := convolution_pow_nonneg (primePenalty_nonneg g (fun p => (hg p).1)) (k+1)
  have hsub : Finset.Ioc (a/d) (b/d) ⊆ Finset.Icc 1 (b/d) := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le (a/d)).trans_lt (Finset.mem_Ioc.mp hm).1), (Finset.mem_Ioc.mp hm).2⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hf0 m)).trans
  apply (primePenalty_pow_initial_le g hg k (b/d)).trans
  by_cases hq : b/d = 0
  · simp only [hq, Nat.cast_zero, zero_mul]
    have hlog : 0 ≤ 1 + Real.log (b:ℝ) := by
      by_cases hb : b=0
      · simp [hb]
      have hl : 0 ≤ Real.log (b:ℝ) := Real.log_nonneg (show (1:ℝ) ≤ b by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb)
      linarith
    positivity
  have hq1 : (1:ℝ) ≤ (b/d:ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have hq0 : (0:ℝ) < (b/d:ℕ) := lt_of_lt_of_le zero_lt_one hq1
  apply mul_le_mul Nat.cast_div_le _ (pow_nonneg (by linarith [Real.log_nonneg hq1]) _) (by positivity)
  apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hq1])
  linarith only [Real.log_le_log hq0 (show ((b/d:ℕ):ℝ) ≤ (b:ℝ) by exact_mod_cast Nat.div_le_self b d)]

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma divided_interval_estimates (a b d T : ℕ) (η : ℝ)
    (hab : a ≤ b) (hd : 0 < d) (hdT : d ≤ T) (hT : 2 ≤ T)
    (hTb : T^2 ≤ b) (hbT : b ≤ T^4) (hη : 0 < η)
    (hηT : 2 ≤ η*T) (hrel : η*b ≤ (b:ℝ)-a) :
    T ≤ b/d ∧ a/d ≤ b/d ∧
      (η/2) * (b/d:ℕ) ≤ ((b/d:ℕ):ℝ)-(a/d:ℕ) ∧
      (0 < Real.log b) ∧ (0 < Real.log (b/d:ℕ)) ∧
      (((b/d:ℕ):ℝ)-(a/d:ℕ))/Real.log (b/d:ℕ) ≤
        8 * (((b:ℝ)-a)/Real.log b) / d := by
  have hTu : T ≤ b/d := (Nat.le_div_iff_mul_le hd).mpr <|
    (Nat.mul_le_mul_left T hdT).trans (by simpa [pow_two] using hTb)
  have hdu : (0:ℝ) < d := by exact_mod_cast hd
  have hTc : (2:ℝ) ≤ T := by exact_mod_cast hT
  have hTuc : (T:ℝ) ≤ (b/d:ℕ) := by exact_mod_cast hTu
  have hU : ((b/d:ℕ):ℝ) ≤ (b:ℝ)/d := Nat.cast_div_le
  have hA : ((a/d:ℕ):ℝ) ≤ (a:ℝ)/d := Nat.cast_div_le
  have hU' := real_div_lt_nat_div_add_one b hd
  have hlen := interval_div_length_le a b d hd
  have hy : η * ((b:ℝ)/d) ≤ ((b:ℝ)-a)/d := by
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right hrel hdu.le
  have het : (2:ℝ) ≤ η * ((b/d:ℕ):ℝ) :=
    hηT.trans (mul_le_mul_of_nonneg_left hTuc hη.le)
  have het' : (2:ℝ) ≤ ((b:ℝ)-a)/d :=
    (het.trans (mul_le_mul_of_nonneg_left hU hη.le)).trans hy
  have hlow : η * ((b/d:ℕ):ℝ)-1 ≤ ((b/d:ℕ):ℝ)-(a/d:ℕ) := by
    have hηU := mul_le_mul_of_nonneg_left hU hη.le
    have hdiv : ((b:ℝ)-a)/d = (b:ℝ)/d-(a:ℝ)/d := sub_div _ _ _
    linarith
  have hrelative : (η/2)*((b/d:ℕ):ℝ) ≤ ((b/d:ℕ):ℝ)-(a/d:ℕ) := by linarith
  have hupper : ((b/d:ℕ):ℝ)-(a/d:ℕ) ≤ 2*(((b:ℝ)-a)/d) := by linarith
  have hb2 : 1 < b := by nlinarith
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb2)
  have hlogu : 0 < Real.log (b/d:ℕ) := Real.log_pos (by linarith)
  have hlogT : Real.log b ≤ 4 * Real.log T := by
    have hb0 : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have ht0 : (0:ℝ) < T := by linarith
    have h := Real.log_le_log hb0 (show (b:ℝ) ≤ (T:ℝ)^4 by exact_mod_cast hbT)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogTu : Real.log T ≤ Real.log (b/d:ℕ) := Real.log_le_log (by linarith) hTuc
  have hlog : Real.log b / 4 ≤ Real.log (b/d:ℕ) := by linarith
  refine ⟨hTu, Nat.div_le_div_right hab, hrelative, hlogb, hlogu, ?_⟩
  calc
    _ ≤ (2*(((b:ℝ)-a)/d))/(Real.log b/4) :=
      div_le_div₀ (by linarith only [hupper, het']) hupper (by positivity) hlog
    _ = _ := by ring

end PrimeDegreePackets.Sieve


namespace PrimeDegreePackets.Sieve
open Finset Nat

lemma intervalConstant_nonneg (k : ℕ) : 0 ≤ intervalConstant k := by unfold intervalConstant; positivity

lemma primeExponential_one_le (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p) (k b : ℕ) :
    1 ≤ primeExponential g k b := by
  apply Real.one_le_exp_iff.mpr
  exact Finset.sum_nonneg (fun p _ => div_nonneg (mul_nonneg (by positivity) (hg p)) (Nat.cast_nonneg p))

lemma primeExponential_mono (g : ℕ → ℝ) (hg : ∀p, 0 ≤ g p) (k : ℕ)
    {a b : ℕ} (hab : a ≤ b) : primeExponential g k a ≤ primeExponential g k b := by
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hab)
  · intro p _ _
    exact div_nonneg (mul_nonneg (by positivity) (hg p)) (Nat.cast_nonneg p)

 

theorem corrected_interval_finite (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ (g : ℕ → ℝ), (∀p, 0 ≤ g p ∧ g p ≤ 1) →
      ∀ a b T : ℕ, a ≤ b → 2 ≤ T → B ≤ T → T^2 ≤ b → b ≤ T^4 →
      2 ≤ η*T → η*b ≤ (b:ℝ)-a →
      (∑ m ∈ Finset.Ioc a b, (powerfulFunction k * (primePenalty g)^(k+1)) m) ≤
        8 * intervalConstant k * powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b +
        ((b:ℝ)*(1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) * powerfulMoment k := by
  obtain ⟨B, hB⟩ := primePenalty_pow_relative_interval k (η/2) (by positivity)
  refine ⟨B, ?_⟩
  intro g hg a b T hab hT hBT hTb hbT hηT hrel
  have hg0 : ∀p, 0 ≤ g p := fun p => (hg p).1
  have hf0 : ∀m, 0 ≤ ((primePenalty g)^(k+1)) m := convolution_pow_nonneg (primePenalty_nonneg g hg0) _
  have hT0 : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hb0 : (0:ℝ) < b := by exact_mod_cast (show 0 < b by nlinarith)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by nlinarith))
  have hy : 0 ≤ (b:ℝ)-a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hE : 0 ≤ primeExponential g k b := (zero_le_one.trans (primeExponential_one_le g hg0 k b))
  have hC : 0 ≤ intervalConstant k := intervalConstant_nonneg k
  have hM : 0 ≤ powerfulMoment k := powerfulMoment_nonneg k
  rw [mul_comm (powerfulFunction k), convolution_sum_interval]
  let S := Finset.Icc 1 b
  let A := S.filter (· ≤ T)
  let D := S.filter (fun d => ¬d ≤ T)
  let W := fun d : ℕ => powerfulFunction k d *
    ∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e
  have hsplit : (∑ d ∈ S, W d) = (∑ d ∈ A, W d) + ∑ d ∈ D, W d :=
    (Finset.sum_filter_add_sum_filter_not S (fun d => d ≤ T) W).symm
  change (∑ d ∈ S, W d) ≤ _
  rw [hsplit]
  apply _root_.add_le_add
  · calc
      (∑ d ∈ A, W d) ≤ ∑ d ∈ A, (8*intervalConstant k*(((b:ℝ)-a)/Real.log b)*primeExponential g k b) *
          (powerfulCorrection k d / (d:ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hds, hdT⟩ := Finset.mem_filter.mp hd
        have hd0 : 0 < d := (Finset.mem_Icc.mp hds).1
        obtain ⟨hTu, had, hrelative, _, hlogu, hlength⟩ :=
          divided_interval_estimates a b d T η hab hd0 hdT hT hTb hbT hη hηT hrel
        have hbase := hB g hg (a/d) (b/d) (hBT.trans hTu) had hrelative
        change (∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e) ≤
          intervalConstant k * ((((b/d:ℕ):ℝ)-(a/d:ℕ))/Real.log (b/d:ℕ)) * primeExponential g k (b/d) at hbase
        have hbound : (∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e) ≤
            intervalConstant k * (8*(((b:ℝ)-a)/Real.log b)/d) * primeExponential g k b := by
          apply hbase.trans
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hlength hC
          · exact primeExponential_mono g hg0 k (Nat.div_le_self b d)
          · exact Real.exp_nonneg _
          · positivity
        have hmul := mul_le_mul_of_nonneg_left hbound (powerfulCorrection_nonneg k d)
        calc
          W d = powerfulCorrection k d * (∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e) := rfl
          _ ≤ powerfulCorrection k d * (intervalConstant k * (8*(((b:ℝ)-a)/Real.log b)/d) * primeExponential g k b) := hmul
          _ = _ := by ring
      _ = (8*intervalConstant k*(((b:ℝ)-a)/Real.log b)*primeExponential g k b) *
          ∑ d ∈ A, powerfulCorrection k d / (d:ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        have H := mul_le_mul_of_nonneg_left (powerfulCorrection_reciprocal_sum_le k A)
          (show 0 ≤ 8*intervalConstant k*(((b:ℝ)-a)/Real.log b)*primeExponential g k b by positivity)
        convert H using 1
        all_goals try with_reducible_and_instances rfl
        ring
  · calc
      (∑ d ∈ D, W d) ≤ ∑ d ∈ D, ((b:ℝ)*(1+Real.log b)^k) * (powerfulCorrection k d/(d:ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
        have H := mul_le_mul_of_nonneg_left (primePenalty_pow_interval_trivial g hg k a b d hd0)
          (powerfulCorrection_nonneg k d)
        calc
          W d = powerfulCorrection k d * (∑ e ∈ Finset.Ioc (a/d) (b/d), ((primePenalty g)^(k+1)) e) := rfl
          _ ≤ powerfulCorrection k d * (((b:ℝ)/d) * (1+Real.log b)^k) := H
          _ = _ := by ring
      _ = ((b:ℝ)*(1+Real.log b)^k) * ∑ d ∈ D, powerfulCorrection k d/(d:ℝ) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
        have H := powerfulCorrection_reciprocal_tail k D (T:ℝ) hT0 (by
          intro d hd
          have hdT := (Finset.mem_filter.mp hd).2
          exact_mod_cast (show T ≤ d by omega))
        have H' := mul_le_mul_of_nonneg_left H (show 0 ≤ (b:ℝ)*(1+Real.log b)^k by positivity)
        convert H' using 1
        all_goals try with_reducible_and_instances rfl
        ring

end PrimeDegreePackets.Sieve

open Filter Topology
namespace PrimeDegreePackets.Sieve

lemma log_power_error_vanishes (k : ℕ) :
    Tendsto (fun b : ℕ => (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16))
      atTop (𝓝 0) := by
  have H := (isLittleO_log_rpow_rpow_atTop ((k+1:ℕ):ℝ)
    (by norm_num : (0:ℝ) < 1/16)).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast] at H
  have H' : Tendsto (fun b : ℕ => (2:ℝ)^k * ((Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16)))
      atTop (𝓝 ((2:ℝ)^k * 0)) := tendsto_const_nhds.mul (H.comp tendsto_natCast_atTop_atTop)
  simpa only [mul_div_assoc, mul_zero] using H'

lemma eventual_tail_threshold (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, ∀ b : ℕ, B ≤ b → 1 ≤ Real.log b ∧
      (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16) ≤ η := by
  have H : ∀ᶠ b : ℕ in atTop, 1 ≤ Real.log b ∧
      (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16) ≤ η := by
    filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1:ℝ)), (log_power_error_vanishes k).eventually_le_const hη] with b hlog herr
    exact ⟨hlog, herr⟩
  exact eventually_atTop.mp H

lemma reciprocal_cutoff_bound (b T : ℕ) (hb : 0 < b) (hT : 0 < T) (hbT : b ≤ T^4) :
    (T:ℝ)^(-(1:ℝ)/4) ≤ (b:ℝ)^(-(1:ℝ)/16) := by
  have hb0 : (0:ℝ) < b := by exact_mod_cast hb
  have hT0 : (0:ℝ) < T := by exact_mod_cast hT
  have H := Real.rpow_le_rpow_of_nonpos hb0 (show (b:ℝ) ≤ (T:ℝ)^4 by exact_mod_cast hbT)
    (by norm_num : -(1:ℝ)/16 ≤ 0)
  rw [← Real.rpow_natCast_mul hT0.le] at H
  norm_num at H ⊢
  exact H

lemma tail_absorbed (k a b T : ℕ) (η : ℝ) (hb : 0 < b) (hT : 0 < T)
    (hbT : b ≤ T^4) (hlog : 1 ≤ Real.log b)
    (herr : (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16) ≤ η)
    (hrel : η*b ≤ (b:ℝ)-a) :
    ((b:ℝ)*(1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) ≤ ((b:ℝ)-a)/Real.log b := by
  have hlog0 : 0 < Real.log b := by linarith
  have hb0 : (0:ℝ) < b := by exact_mod_cast hb
  have hcut : (Real.log b * (1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) ≤ η := by
    calc
      _ ≤ (Real.log b * (2*Real.log b)^k) * (b:ℝ)^(-(1:ℝ)/16) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ hlog0.le
          exact pow_le_pow_left₀ (by linarith) (by linarith) k
        · exact reciprocal_cutoff_bound b T hb hT hbT
        · apply Real.rpow_nonneg; positivity
        · positivity
      _ = (2:ℝ)^k * (Real.log b)^(k+1) / (b:ℝ)^((1:ℝ)/16) := by
        rw [mul_pow, pow_succ, show -(1:ℝ)/16 = -((1:ℝ)/16) by ring, Real.rpow_neg hb0.le]
        ring
      _ ≤ η := herr
  apply (le_div_iff₀ hlog0).mpr
  have H := mul_le_mul_of_nonneg_left hcut hb0.le
  nlinarith only [H, hrel]

lemma sqrt_fourth_bound {b : ℕ} (hb : 4 ≤ b) : b ≤ (Nat.sqrt b)^4 := by
  have hs : 2 ≤ Nat.sqrt b := Nat.le_sqrt'.mpr hb
  have htop := Nat.lt_succ_sqrt' b
  have h1 : Nat.sqrt b + 1 ≤ (Nat.sqrt b)^2 := by nlinarith
  calc
    b ≤ (Nat.sqrt b + 1)^2 := by linarith
    _ ≤ ((Nat.sqrt b)^2)^2 := Nat.pow_le_pow_left h1 2
    _ = (Nat.sqrt b)^4 := by ring

end PrimeDegreePackets.Sieve
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealCoefficients
attribute [-instance] _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.primaryIdealMultisetEquiv_val _root_.OAI.PrimeDegreePackets.primaryIdealNormEquiv_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
namespace PrimeDegreePackets.Sieve
open Finset Nat Filter Topology

lemma powerfulMoment_one_le (k : ℕ) : 1 ≤ powerfulMoment k := by
  simpa [powerfulCorrection_one] using powerfulCorrection_moment_sum_le k {1}

 

theorem corrected_relative_interval (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ R : ℕ, ∀ (g : ℕ → ℝ), (∀p, 0 ≤ g p ∧ g p ≤ 1) →
      ∀ a b : ℕ, R ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
      (∑ m ∈ Finset.Ioc a b, (powerfulFunction k * (primePenalty g)^(k+1)) m) ≤
        ((8 * intervalConstant k + 1) * powerfulMoment k) *
          (((b:ℝ)-a)/Real.log b) * primeExponential g k b := by
  obtain ⟨B,hB⟩ := corrected_interval_finite k η hη
  obtain ⟨R,hR⟩ := eventual_tail_threshold k η hη
  let N := max 2 (max B ⌈2/η⌉₊)
  refine ⟨max R (N^2), ?_⟩
  intro g hg a b hb hab hrel
  have hRb : R ≤ b := (le_max_left _ _).trans hb
  have hNb : N^2 ≤ b := (le_max_right _ _).trans hb
  let T := Nat.sqrt b
  have hNT : N ≤ T := Nat.le_sqrt'.mpr hNb
  have hT : 2 ≤ T := (le_max_left _ _).trans hNT
  have hBT : B ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hNT)
  have hηT : 2 ≤ η * (T:ℝ) := by
    have hceil : ⌈2/η⌉₊ ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hNT)
    have hdiv : (2:ℝ)/η ≤ T := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have H := (div_le_iff₀ hη).mp hdiv
    simpa [mul_comm] using H
  have hTb : T^2 ≤ b := Nat.sqrt_le' b
  have hb4 : 4 ≤ b := by nlinarith
  have hbT : b ≤ T^4 := sqrt_fourth_bound hb4
  have hbp : 0 < b := by omega
  have htp : 0 < T := by omega
  have hlog := (hR b hRb).1
  have hM : 0 ≤ powerfulMoment k := powerfulMoment_nonneg k
  have hy : 0 ≤ ((b:ℝ)-a)/Real.log b := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hab)) (by linarith)
  have hE := primeExponential_one_le g (fun p => (hg p).1) k b
  have htail := mul_le_mul_of_nonneg_right
    (tail_absorbed k a b T η hbp htp hbT hlog (hR b hRb).2 hrel) hM
  have herr : ((b:ℝ)*(1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) * powerfulMoment k ≤
      powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b := by
    calc
      _ ≤ (((b:ℝ)-a)/Real.log b) * powerfulMoment k := htail
      _ ≤ powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b := by
        have H := mul_le_mul_of_nonneg_left hE (mul_nonneg hM hy)
        simpa [mul_comm] using H
  calc
    _ ≤ 8 * intervalConstant k * powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b +
        ((b:ℝ)*(1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) * powerfulMoment k :=
      hB g hg a b T hab hT hBT hTb hbT hηT hrel
    _ ≤ 8 * intervalConstant k * powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b +
        powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b := by gcongr
    _ = _ := by ring

 

theorem divisor_bounded_relative_interval (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative →
        (∀m, 0 ≤ f m ∧ f m ≤ nFoldDivisor (k+1) m) →
        ∀ a b : ℕ, R ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
          (∑ m ∈ Finset.Ioc a b, f m) ≤
            C * (((b:ℝ)-a)/Real.log b) *
              Real.exp (∑ p ∈ smallPrimes b, f p / p) := by
  refine ⟨(8 * intervalConstant k + 1) * powerfulMoment k, ?_, ?_⟩
  · exact mul_pos (by have := intervalConstant_nonneg k; linarith)
      (lt_of_lt_of_le zero_lt_one (powerfulMoment_one_le k))
  intro η hη
  obtain ⟨R,hR⟩ := corrected_relative_interval k η hη
  refine ⟨R, ?_⟩
  intro f hmult hf a b hb hab hrel
  have H := hR (coefficientPenalty k f) (coefficientPenalty_bounds k f hf) a b hb hab hrel
  have hE : primeExponential (coefficientPenalty k f) k b =
      Real.exp (∑ p ∈ smallPrimes b, f p / p) := by
    unfold primeExponential
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2
    rw [show ((k+1:ℕ):ℝ) = (k+1:ℝ) by push_cast; rfl, coefficientPenalty_prime k f hprime]
  rw [hE] at H
  exact (Finset.sum_le_sum (fun m _ => divisor_bounded_majorant k f hmult hf m)).trans H

end PrimeDegreePackets.Sieve

open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

variable (K : Type*) [Field K] [NumberField K]



lemma idealCoefficient_pos (m : ℕ) (hm : m ≠ 0) :
    idealCoefficient K m = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := by
  simp [idealCoefficient,hm]

lemma idealCoefficient_one : idealCoefficient K 1 = 1 := by
  simp [idealCoefficient, Ideal.absNorm_eq_one_iff]

lemma idealCoefficient_multiplicative : (idealCoefficient K).IsMultiplicative := by
  refine ⟨idealCoefficient_one K, ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [idealCoefficient_pos K _ (mul_ne_zero hm hn), idealCoefficient_pos K _ hm,
    idealCoefficient_pos K _ hn, ← Nat.card_prod]
  exact Nat.card_congr (idealNormProductEquiv K m n hm hn hmn).symm


lemma ideal_factor_count_le {I : Ideal (𝓞 K)} {p r : ℕ}
    (hp : p.Prime) (hI : Ideal.absNorm I = p^r) : (normalizedFactors I).card ≤ r := by
  have hI0 : I ≠ ⊥ := by
    intro h; have H : (0:ℕ) = p^r := by simpa [h] using hI
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  have H : p ^ (normalizedFactors I).card ≤ Ideal.absNorm I := by
    have H := Multiset.pow_card_le_prod (s := (normalizedFactors I).map Ideal.absNorm)
      (a := p) (by
        intro x hx
        obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hx
        exact (ideal_factor_prime_power K hp hI hP).2)
    simpa only [Multiset.card_map, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI0] using H
  rw [hI] at H
  exact (pow_le_pow_iff_right₀ hp.one_lt).mp H


lemma idealsOverPrime_card_le {p : ℕ} (hp : p.Prime) :
    (idealsOverPrime K p).card ≤ Module.finrank ℤ (𝓞 K) := by
  exact (Multiset.toFinset_card_le _).trans
    (ideal_factor_count_le K hp (Ideal.absNorm_span_natCast p))

 
lemma idealCoefficient_prime_le {p : ℕ} (hp : p.Prime) :
    idealCoefficient K p ≤ Module.finrank ℤ (𝓞 K) := by
  rw [idealCoefficient_pos K p hp.ne_zero]
  have hmem : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p}, I.1 ∈ idealsOverPrime K p := by
    intro I
    have hI0 : I.1 ≠ ⊥ := by
      intro h
      have H : p = 0 := by simpa [h] using I.2.symm
      exact hp.ne_zero H
    have hIprime : I.1.IsPrime := Ideal.isPrime_of_irreducible_absNorm
      (by rw [I.2]; exact Nat.irreducible_iff_prime.mpr hp.prime)
    have hfac : I.1 ∈ normalizedFactors I.1 :=
      (Ideal.mem_normalizedFactors_iff hI0).mpr ⟨hIprime, le_rfl⟩
    exact ideal_factor_mem_over K hp (r := 1) (by simpa using I.2) hfac
  let f : {I : Ideal (𝓞 K) // Ideal.absNorm I = p} → idealsOverPrime K p :=
    fun I => ⟨I.1,hmem I⟩
  have hf : Function.Injective f := by
    intro I J h
    exact Subtype.ext (show I.1 = J.1 from congrArg (fun x : idealsOverPrime K p => x.1) h)
  have H := Nat.card_le_card_of_injective f hf
  exact H.trans (by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using idealsOverPrime_card_le K hp)



lemma decode_padMultiset {α : Type*} (s : Finset α) (r : ℕ) (m : Multiset α)
    (hm : ∀x ∈ m, x ∈ s) (hr : m.card ≤ r) :
    (padMultiset s r m hm hr).val.filterMap (Option.map Subtype.val) = m := by
  simp only [padMultiset, Multiset.filterMap_add, Multiset.filterMap_map]
  have hnone : ∀k, (Multiset.replicate k (none : Option s)).filterMap
      (Option.map Subtype.val) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Multiset.replicate_succ, Multiset.filterMap_cons_none _ _ rfl, ih]
  rw [hnone, add_zero]
  change m.attach.filterMap (some ∘ Subtype.val) = m
  rw [Multiset.filterMap_eq_map, Multiset.attach_map_val]

lemma card_le_of_multiset_encoding {α β : Type*} (s : Finset β) (r : ℕ)
    (f : α → Multiset β) (hf : Function.Injective f)
    (hs : ∀a x, x ∈ f a → x ∈ s) (hr : ∀a, (f a).card ≤ r) :
    Nat.card α ≤ (s.card + 1).multichoose r := by
  let g : α → Sym (Option s) r := fun a => padMultiset s r (f a) (hs a) (hr a)
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    have H := congrArg (fun v : Sym (Option s) r =>
      v.val.filterMap (Option.map Subtype.val)) hab
    simpa only [g, decode_padMultiset] using H
  have H := Nat.card_le_card_of_injective g hg
  rw [Sym.natCard_sym_eq_multichoose] at H
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe] using H

 

lemma idealCoefficient_prime_pow_le {p : ℕ} (hp : p.Prime) (r : ℕ) :
    idealCoefficient K (p^r) ≤ (r + Module.finrank ℤ (𝓞 K)).choose (Module.finrank ℤ (𝓞 K)) := by
  rw [idealCoefficient_pos K _ (pow_ne_zero _ hp.ne_zero)]
  let f : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^r} → Multiset (Ideal (𝓞 K)) :=
    fun I => normalizedFactors I.1
  have hzero : ∀I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^r}, I.1 ≠ ⊥ := by
    intro I h
    have H : (0:ℕ) = p^r := by simpa [h] using I.2
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  have hf : Function.Injective f := by
    intro I J h
    apply Subtype.ext
    have H := congrArg Multiset.prod h
    simpa only [f, Ideal.prod_normalizedFactors_eq_self (hzero I),
      Ideal.prod_normalizedFactors_eq_self (hzero J)] using H
  have H := card_le_of_multiset_encoding (idealsOverPrime K p) r f hf
    (fun I _ hP => ideal_factor_mem_over K hp I.2 hP)
    (fun I => ideal_factor_count_le K hp I.2)
  apply H.trans
  rw [Nat.multichoose_eq]
  calc
    _ ≤ (Module.finrank ℤ (𝓞 K) + r).choose r :=
      Nat.choose_le_choose r (by have := idealsOverPrime_card_le K hp; omega)
    _ = (r + Module.finrank ℤ (𝓞 K)).choose (Module.finrank ℤ (𝓞 K)) := by
      rw [Nat.add_comm (Module.finrank ℤ (𝓞 K)) r, Nat.choose_symm_add]

 
theorem idealCoefficient_le_divisor (m : ℕ) :
    idealCoefficient K m ≤ nFoldDivisor (Module.finrank ℤ (𝓞 K) + 1) m := by
  by_cases hm : m = 0
  · simp [hm,nFoldDivisor]
  unfold nFoldDivisor
  rw [(idealCoefficient_multiplicative K).multiplicative_factorization _ hm,
    ArithmeticFunction.isMultiplicative_zeta.pow.multiplicative_factorization _ hm]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  exact (idealCoefficient_prime_pow_le K hprime _).trans_eq
    (nFoldDivisor_prime_pow _ _ _ hprime).symm

open Filter Topology Asymptotics

lemma idealCoefficientReal_multiplicative : (idealCoefficientReal K).IsMultiplicative := by
  refine ⟨by simp [idealCoefficientReal,idealCoefficient_one], ?_⟩
  intro m n hmn
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk]
  rw [(idealCoefficient_multiplicative K).map_mul_of_coprime hmn, Nat.cast_mul]

lemma idealCoefficientReal_nonneg (m : ℕ) : 0 ≤ idealCoefficientReal K m := Nat.cast_nonneg _

 
lemma idealCoefficient_summatory_limit :
    Tendsto (fun n : ℕ => (∑k ∈ Icc 1 n, idealCoefficientReal K k) / (n:ℝ))
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le]
  congr 1
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk]
  rw [←Nat.cast_sum]
  congr 1
  rw [←add_left_inj 1, ←Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Icc_succ_left_eq_Ioc _ _]
  have H : (∑k ∈ Ioc 0 n, idealCoefficient K k) =
      ∑k ∈ Ioc 0 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} := by
    apply sum_congr rfl
    intro k hk
    exact idealCoefficient_pos K k (Nat.ne_of_gt (Finset.mem_Ioc.mp hk).1)
  rw [H, show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff], sum_Ioc_add_eq_sum_Icc n.zero_le,
    ←card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

lemma idealCoefficient_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun m => (idealCoefficientReal K m : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (idealCoefficientReal_nonneg K) zero_le_one hs
  apply isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
  simpa using idealCoefficient_summatory_limit K


lemma realDirichletTerm_ofReal (f : ArithmeticFunction ℝ) (s : ℝ) (m : ℕ) :
    (realDirichletTerm f s m : ℂ) = LSeries.term (fun m => (f m : ℂ)) s m := by
  by_cases hm : m = 0
  · subst m
    simp [realDirichletTerm]
  · simp only [realDirichletTerm, ArithmeticFunction.coe_mk,LSeries.term_of_ne_zero hm,
      Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg m),Complex.ofReal_natCast]

lemma idealCoefficient_real_summable {s : ℝ} (hs : 1 < s) :
    Summable (realDirichletTerm (idealCoefficientReal K) s) := by
  apply Complex.summable_ofReal.mp
  simp_rw [realDirichletTerm_ofReal]
  exact idealCoefficient_LSeriesSummable K (by simpa using hs)

lemma idealCoefficient_LSeries_eq (s : ℂ) :
    LSeries (fun m => (idealCoefficientReal K m : ℂ)) s = NumberField.dedekindZeta K s := by
  apply LSeries_congr _ s
  intro m hm
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk,idealCoefficient_pos K m hm,
    Complex.ofReal_natCast]

 
lemma idealDirichlet_eq_dedekindZeta (s : ℝ) :
    ((∑'m, realDirichletTerm (idealCoefficientReal K) s m : ℝ) : ℂ) =
      NumberField.dedekindZeta K s := by
  rw [Complex.ofReal_tsum, ←idealCoefficient_LSeries_eq]
  apply tsum_congr
  intro m
  exact realDirichletTerm_ofReal _ _ _

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MangoldtBounds
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

open scoped ArithmeticFunction.vonMangoldt

 
lemma vonMangoldt_floor_identity (N : ℕ) :
    (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * (N / d : ℕ)) =
      ∑ m ∈ Icc 1 N, Real.log m := by
  have H := sum_divisors_initial (fun d _ => ArithmeticFunction.vonMangoldt d) N
  simpa only [ArithmeticFunction.vonMangoldt_sum, sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, mul_comm] using H.symm

lemma nat_floor_quotient_half {N d : ℕ} (hd : 0 < d) (hN : d ≤ N) :
    (N:ℝ) / (2*d) ≤ (N / d : ℕ) := by
  have hq : 1 ≤ N/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa)
  have hlt : N < (N/d+1)*d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
  have hn : N ≤ 2*(N/d)*d := by nlinarith
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*d)).mpr
  have H : (N:ℝ) ≤ 2*(N/d:ℕ)*d := by exact_mod_cast hn
  nlinarith

 

theorem vonMangoldt_reciprocal_sum (N : ℕ) :
    (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d / d) ≤ 2 * Real.log N := by
  by_cases hN : N = 0
  · simp [hN]
  have hN0 : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have H : (N:ℝ)/2 * (∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d / d) ≤
      (N:ℝ) * Real.log N := by
    calc
      _ = ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N:ℝ)/(2*d)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d * (N/d:ℕ) := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left
          (nat_floor_quotient_half (mem_Icc.mp hd).1 (mem_Icc.mp hd).2)
          ArithmeticFunction.vonMangoldt_nonneg
      _ = ∑ m ∈ Icc 1 N, Real.log m := vonMangoldt_floor_identity N
      _ ≤ (N:ℝ) * Real.log N := by
        calc
          _ ≤ ∑ _m ∈ Icc 1 N, Real.log N := by
            apply sum_le_sum
            intro m hm
            exact Real.log_le_log (by exact_mod_cast (mem_Icc.mp hm).1)
              (by exact_mod_cast (mem_Icc.mp hm).2)
          _ = _ := by simp
  nlinarith

 
lemma finite_euler_lower (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hf0 : ∀m, 0 ≤ f m) (hs : Summable f) (S : Finset ℕ)
    (hS : ∀p ∈ S, p.Prime) :
    (∏ p ∈ S, (1 + f p)) ≤ ∑' m, f m := by
  have hnorm : Summable (fun m => ‖f m‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hs
  calc
    _ ≤ ∏ p ∈ S, ∑'j : ℕ, f (p^j) := by
      apply Finset.prod_le_prod (fun prime _ => by linarith [hf0 prime])
      intro p hp
      have hsp := hs.comp_injective (Nat.pow_right_injective (hS p hp).one_lt)
      have H := hsp.sum_le_tsum (range 2) (fun j _ => hf0 (p^j))
      simpa [sum_range_succ, hf.1] using H
    _ = ∑' m : Nat.factoredNumbers S, f m := by
      have H := EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers hf.1
        (fun {_ _} h => hf.map_mul_of_coprime h) hnorm S
      simpa only [Finset.filter_true_of_mem hS] using H
    _ ≤ ∑' m, f m := by
      exact Summable.tsum_subtype_le f (Nat.factoredNumbers S) hf0 hs

lemma log_one_add_lower_quadratic (x : ℝ) (hx : 0 ≤ x) : x - x^2 ≤ Real.log (1+x) := by
  apply le_trans ?_ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by linarith : (0:ℝ) < x+2)).mpr
  nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]

 

lemma prime_exp_le_euler (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative)
    (hf0 : ∀m, 0 ≤ f m) (hs : Summable f) (S : Finset ℕ)
    (hS : ∀p ∈ S, p.Prime) :
    Real.exp (∑p ∈ S, f p) ≤ Real.exp (∑p ∈ S, (f p)^2) * ∑'m, f m := by
  have H : (∑p ∈ S, f p) ≤ (∑p ∈ S, (f p)^2) + ∑p ∈ S, Real.log (1+f p) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro p _
    linarith [log_one_add_lower_quadratic (f p) (hf0 p)]
  calc
    _ ≤ Real.exp ((∑p ∈ S, (f p)^2) + ∑p ∈ S, Real.log (1+f p)) := Real.exp_le_exp.mpr H
    _ = Real.exp (∑p ∈ S, (f p)^2) * ∏p ∈ S, (1+f p) := by
      rw [Real.exp_add]
      congr 1
      rw [Real.exp_sum]
      apply prod_congr rfl
      intro p _
      exact Real.exp_log (by linarith [hf0 p])
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_euler_lower f hf hf0 hs S hS)
      (Real.exp_pos _).le

lemma realDirichletTerm_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (s : ℝ) : (realDirichletTerm f s).IsMultiplicative := by
  refine ⟨by simp [realDirichletTerm,hf.1], ?_⟩
  intro m n hmn
  simp only [realDirichletTerm, ArithmeticFunction.coe_mk,
    hf.map_mul_of_coprime hmn, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), mul_div_mul_comm]

lemma realDirichletTerm_nonneg {f : ArithmeticFunction ℝ}
    (hf0 : ∀m, 0 ≤ f m) (s : ℝ) (m : ℕ) : 0 ≤ realDirichletTerm f s m := by
  exact div_nonneg (hf0 m) (Real.rpow_nonneg (Nat.cast_nonneg m) s)

lemma realDirichletTerm_le_div {f : ArithmeticFunction ℝ} (hf0 : ∀m, 0 ≤ f m)
    {s B : ℝ} (hs : 1 ≤ s) {m : ℕ} (hm : 1 ≤ m) (hB : f m ≤ B) :
    realDirichletTerm f s m ≤ B / m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ ≤ f m / m := by
      apply div_le_div_of_nonneg_left (hf0 m) hm0
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 hs
    _ ≤ _ := div_le_div_of_nonneg_right hB hm0.le

 
lemma prime_quadratic_sum_le {f : ArithmeticFunction ℝ} (hf0 : ∀m, 0 ≤ f m)
    {s B : ℝ} (hs : 1 ≤ s) (hB : ∀p, p.Prime → f p ≤ B)
    (S : Finset ℕ) (hS : ∀p ∈ S, p.Prime) :
    (∑p ∈ S, (realDirichletTerm f s p)^2) ≤ B^2 * ∑'m:ℕ, ((m:ℝ)^2)⁻¹ := by
  have hsum : Summable (fun m:ℕ => ((m:ℝ)^2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  calc
    _ ≤ ∑p ∈ S, (B/(p:ℝ))^2 := by
      apply sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (realDirichletTerm_nonneg hf0 s p)
        (realDirichletTerm_le_div hf0 hs (hS p hp).one_le (hB p (hS p hp))) 2
    _ = B^2 * ∑p ∈ S, ((p:ℝ)^2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      simp only [div_eq_mul_inv, mul_pow, inv_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum S (fun m _ => by positivity)) (sq_nonneg B)

 
lemma reciprocal_dirichlet_difference {x h : ℝ} (hx : 0 < x) :
    1/x - 1/x^(1+h) ≤ h * Real.log x / x := by
  have H := Real.add_one_le_exp (-h * Real.log x)
  have heq : 1/x^(1+h) = Real.exp (-h * Real.log x)/x := by
    rw [Real.rpow_add hx, Real.rpow_one, Real.rpow_def_of_pos hx h]
    rw [show -h * Real.log x = -(Real.log x * h) by ring, Real.exp_neg]
    field_simp
  rw [heq, ← sub_div]
  apply (div_le_div_iff_of_pos_right hx).mpr
  linarith

lemma prime_reciprocal_log_sum (N : ℕ) :
    (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / p) ≤ 2 * Real.log N := by
  calc
    _ = ∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt p / p := by
      apply sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2]
    _ ≤ ∑d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d / d := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro d _ _
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)
    _ ≤ _ := vonMangoldt_reciprocal_sum N

lemma shifted_prime_sum_le {f : ArithmeticFunction ℝ} (hf0 : ∀m, 0 ≤ f m)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀p, p.Prime → f p ≤ B)
    {N : ℕ} (hN : 2 ≤ N) :
    (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, f p / p) ≤
      (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, realDirichletTerm f (1+1/Real.log N) p) + 2*B := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have HH : (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      (f p / p - realDirichletTerm f (1+1/Real.log N) p)) ≤ 2*B := by
    calc
      _ ≤ ∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, (B/Real.log N) * (Real.log p / p) := by
        apply sum_le_sum
        intro p hp
        have hpP := (mem_filter.mp hp).2
        have hp0 : (0:ℝ) < p := by exact_mod_cast hpP.pos
        have hpl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpP.one_le)
        calc
          _ = f p * (1/(p:ℝ) - 1/(p:ℝ)^(1+1/Real.log N)) := by
            simp only [realDirichletTerm,ArithmeticFunction.coe_mk]
            ring
          _ ≤ f p * ((1/Real.log N) * Real.log p / p) :=
            mul_le_mul_of_nonneg_left (reciprocal_dirichlet_difference hp0) (hf0 p)
          _ ≤ B * ((1/Real.log N) * Real.log p / p) := by
            exact mul_le_mul_of_nonneg_right (hB p hpP) (by positivity)
          _ = _ := by ring
      _ = (B/Real.log N) * ∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p / p :=
        (mul_sum _ _ _).symm
      _ ≤ (B/Real.log N) * (2*Real.log N) :=
        mul_le_mul_of_nonneg_left (prime_reciprocal_log_sum N) (div_nonneg hB0 hlog.le)
      _ = 2*B := by field_simp
  rw [sum_sub_distrib] at HH
  linarith

 

theorem prime_exponential_le_dirichlet {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hf0 : ∀m, 0 ≤ f m)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀p, p.Prime → f p ≤ B)
    {N : ℕ} (hN : 2 ≤ N)
    (hs : Summable (realDirichletTerm f (1+1/Real.log N))) :
    Real.exp (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, f p / p) ≤
      Real.exp (2*B + B^2 * ∑'m:ℕ, ((m:ℝ)^2)⁻¹) *
        ∑'m, realDirichletTerm f (1+1/Real.log N) m := by
  let S := (Finset.Icc 1 N).filter Nat.Prime
  have hS : ∀p ∈ S, p.Prime := fun _ hp => (mem_filter.mp hp).2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have H := prime_exp_le_euler (realDirichletTerm f (1+1/Real.log N))
    (realDirichletTerm_multiplicative hf _) (realDirichletTerm_nonneg hf0 _) hs S hS
  have HQ := prime_quadratic_sum_le hf0 (show 1 ≤ 1+1/Real.log N by linarith [one_div_pos.mpr hlog]) hB S hS
  calc
    _ ≤ Real.exp ((∑p ∈ S, realDirichletTerm f (1+1/Real.log N) p) + 2*B) :=
      Real.exp_le_exp.mpr (shifted_prime_sum_le hf0 hB0 hB hN)
    _ = Real.exp (2*B) * Real.exp (∑p ∈ S, realDirichletTerm f (1+1/Real.log N) p) := by
      rw [Real.exp_add,mul_comm]
    _ ≤ Real.exp (2*B) * (Real.exp (∑p ∈ S, (realDirichletTerm f (1+1/Real.log N) p)^2) *
        ∑'m, realDirichletTerm f (1+1/Real.log N) m) :=
      mul_le_mul_of_nonneg_left H (Real.exp_pos _).le
    _ ≤ Real.exp (2*B) * (Real.exp (B^2*∑'m:ℕ, ((m:ℝ)^2)⁻¹) *
        ∑'m, realDirichletTerm f (1+1/Real.log N) m) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr HQ)
        (tsum_nonneg (realDirichletTerm_nonneg hf0 _))
    _ = _ := by rw [←mul_assoc,←Real.exp_add]

end PrimeDegreePackets


namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]

lemma idealCoefficientReal_prime_le {p : ℕ} (hp : p.Prime) :
    idealCoefficientReal K p ≤ (Module.finrank ℤ (𝓞 K) : ℝ) := by
  change (idealCoefficient K p : ℝ) ≤ (Module.finrank ℤ (𝓞 K) : ℝ)
  exact_mod_cast idealCoefficient_prime_le K hp

 

theorem ideal_prime_exponential_le_zeta {N : ℕ} (hN : 2 ≤ N) :
    Real.exp (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p) ≤
      Real.exp (2*(Module.finrank ℤ (𝓞 K):ℝ) +
        (Module.finrank ℤ (𝓞 K):ℝ)^2 * ∑'m:ℕ, ((m:ℝ)^2)⁻¹) *
      (NumberField.dedekindZeta K (1+1/Real.log N)).re := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have H := prime_exponential_le_dirichlet (idealCoefficientReal_multiplicative K)
    (idealCoefficientReal_nonneg K) (by positivity)
    (fun p hp => idealCoefficientReal_prime_le K hp) hN
    (idealCoefficient_real_summable K (by linarith [one_div_pos.mpr hlog]))
  have heq := congrArg Complex.re (idealDirichlet_eq_dedekindZeta K (1+1/Real.log N))
  simp only [Complex.ofReal_re] at heq
  rw [heq] at H
  simpa using H

end PrimeDegreePackets


namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]


lemma coprimeIdealCoefficient_multiplicative (q : ℕ) :
    (coprimeIdealCoefficient K q).IsMultiplicative := by
  refine ⟨by simp [coprimeIdealCoefficient,idealCoefficientReal,idealCoefficient_one], ?_⟩
  intro m n hmn
  simp only [coprimeIdealCoefficient,ArithmeticFunction.coe_mk,Nat.coprime_mul_iff_left]
  rw [(idealCoefficientReal_multiplicative K).map_mul_of_coprime hmn]
  split_ifs <;> simp_all

lemma coprimeIdealCoefficient_bounds (q m : ℕ) :
    0 ≤ coprimeIdealCoefficient K q m ∧
      coprimeIdealCoefficient K q m ≤
        (nFoldDivisor (Module.finrank ℤ (𝓞 K)+1) m : ℝ) := by
  simp only [coprimeIdealCoefficient,ArithmeticFunction.coe_mk]
  split_ifs
  · exact ⟨idealCoefficientReal_nonneg K m, by
      change (idealCoefficient K m : ℝ) ≤ _
      exact_mod_cast idealCoefficient_le_divisor K m⟩
  · exact ⟨le_rfl, Nat.cast_nonneg _⟩

end PrimeDegreePackets


namespace PrimeDegreePackets


lemma multichoose_succ_eq (n k : ℕ) : (n+1).multichoose k = (k+n).choose n := by
  rw [Nat.multichoose_eq, show n+1+k-1 = k+n by omega]
  rw [← Nat.choose_symm (show k ≤ k+n by omega)]
  congr 1
  omega

lemma summable_multichoose_geometric (n : ℕ) :
    Summable (fun k : ℕ => ((n+1).multichoose k : ℝ) * (1/2:ℝ)^k) := by
  simp_rw [multichoose_succ_eq]
  exact summable_choose_mul_geometric_of_norm_lt_one n
    (by norm_num : ‖(1/2:ℝ)‖ < 1)

lemma summable_localEulerTailConstant (n : ℕ) :
    Summable (fun k : ℕ => ((n+1).multichoose (k+2) : ℝ) * (1/2:ℝ)^k) := by
  have hh : Function.Injective (fun k : ℕ => k+2) := fun a b h => Nat.add_right_cancel h
  have H := ((summable_multichoose_geometric n).comp_injective hh).mul_left (4:ℝ)
  apply H.congr
  intro k
  change 4 * (((n+1).multichoose (k+2) : ℝ)*(1/2:ℝ)^(k+2)) = _
  rw [pow_add]
  ring

lemma localEulerTailConstant_nonneg (n : ℕ) : 0 ≤ localEulerTailConstant n :=
  tsum_nonneg (fun _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))

variable (K : Type*) [Field K] [NumberField K]



lemma idealPrimeEuler_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => idealCoefficientReal K (p^k) / (p:ℝ)^k) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply Summable.of_nonneg_of_le
    (fun _ => div_nonneg (idealCoefficientReal_nonneg K _) (by positivity))
    (fun k => ?_) (summable_multichoose_geometric (Module.finrank ℤ (𝓞 K)))
  calc
    _ ≤ (((Module.finrank ℤ (𝓞 K)+1).multichoose k : ℕ) : ℝ) / (p:ℝ)^k := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      change (idealCoefficient K (p^k) : ℝ) ≤ _
      rw [multichoose_succ_eq]
      exact_mod_cast idealCoefficient_prime_pow_le K hp k
    _ ≤ (((Module.finrank ℤ (𝓞 K)+1).multichoose k : ℕ) : ℝ) / (2:ℝ)^k := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by norm_num) hp2 k)
    _ = _ := by simp [div_eq_mul_inv, ←inv_pow]

lemma idealPrimeEuler_one_le {p : ℕ} (hp : p.Prime) :
    1 ≤ idealPrimeEuler K p := by
  have H := (idealPrimeEuler_summable K hp).sum_le_tsum {0}
    (fun _ _ => div_nonneg (idealCoefficientReal_nonneg K _) (by positivity))
  simpa [idealPrimeEuler,idealCoefficientReal,idealCoefficient_one] using H

 

lemma idealPrimeEuler_le {p : ℕ} (hp : p.Prime) :
    idealPrimeEuler K p ≤ 1 + idealCoefficientReal K p / p +
      localEulerTailConstant (Module.finrank ℤ (𝓞 K)) / (p:ℝ)^2 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsum := idealPrimeEuler_summable K hp
  rw [idealPrimeEuler, ← hsum.sum_add_tsum_nat_add 2]
  have hfirst : (∑ k ∈ range 2, idealCoefficientReal K (p^k)/(p:ℝ)^k) =
      1 + idealCoefficientReal K p / p := by
    simp [sum_range_succ,idealCoefficientReal,idealCoefficient_one]
  rw [hfirst]
  apply add_le_add_right
  calc
    _ ≤ ∑' k : ℕ, (((Module.finrank ℤ (𝓞 K)+1).multichoose (k+2) : ℝ) *
        (1/2:ℝ)^k) / (p:ℝ)^2 := by
      apply Summable.tsum_le_tsum _ (hsum.comp_injective (show Function.Injective (fun k : ℕ => k+2) from
          fun a b h => Nat.add_right_cancel h))
        ((summable_localEulerTailConstant _).div_const _)
      intro k
      calc
        _ ≤ (((Module.finrank ℤ (𝓞 K)+1).multichoose (k+2) : ℕ) : ℝ) / (p:ℝ)^(k+2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          change (idealCoefficient K (p^(k+2)) : ℝ) ≤ _
          rw [multichoose_succ_eq]
          exact_mod_cast idealCoefficient_prime_pow_le K hp (k+2)
        _ = ((((Module.finrank ℤ (𝓞 K)+1).multichoose (k+2) : ℕ) : ℝ) / (p:ℝ)^k) /
            (p:ℝ)^2 := by rw [pow_add,div_mul_eq_div_div]
        _ ≤ ((((Module.finrank ℤ (𝓞 K)+1).multichoose (k+2) : ℕ) : ℝ) / (2:ℝ)^k) /
            (p:ℝ)^2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
            (pow_le_pow_left₀ (by norm_num) hp2 k)
        _ = _ := by simp [div_eq_mul_inv, ←inv_pow]
    _ = _ := by rw [tsum_div_const]; rfl

lemma log_idealPrimeEuler_le {p : ℕ} (hp : p.Prime) :
    Real.log (idealPrimeEuler K p) ≤ idealCoefficientReal K p / p +
      localEulerTailConstant (Module.finrank ℤ (𝓞 K)) / (p:ℝ)^2 := by
  have hpos : 0 < idealPrimeEuler K p := lt_of_lt_of_le zero_lt_one (idealPrimeEuler_one_le K hp)
  calc
    _ ≤ idealPrimeEuler K p - 1 := Real.log_le_sub_one_of_pos hpos
    _ ≤ _ := by linarith [idealPrimeEuler_le K hp]


lemma badPrimeEuler_pos (q : ℕ) : 0 < badPrimeEuler K q := by
  apply Finset.prod_pos
  intro p hp
  exact lt_of_lt_of_le zero_lt_one
    (idealPrimeEuler_one_le K (Nat.prime_of_mem_primeFactors hp))

lemma log_badPrimeEuler_le (q : ℕ) :
    Real.log (badPrimeEuler K q) ≤
      (∑p ∈ q.primeFactors, idealCoefficientReal K p / p) +
      localEulerTailConstant (Module.finrank ℤ (𝓞 K)) * ∑'m:ℕ, ((m:ℝ)^2)⁻¹ := by
  rw [badPrimeEuler, Real.log_prod (fun p hp => ne_of_gt
    (lt_of_lt_of_le zero_lt_one (idealPrimeEuler_one_le K (Nat.prime_of_mem_primeFactors hp))))]
  calc
    _ ≤ ∑p ∈ q.primeFactors, (idealCoefficientReal K p / p +
        localEulerTailConstant (Module.finrank ℤ (𝓞 K)) / (p:ℝ)^2) := by
      exact sum_le_sum (fun p hp => log_idealPrimeEuler_le K (Nat.prime_of_mem_primeFactors hp))
    _ = (∑p ∈ q.primeFactors, idealCoefficientReal K p / p) + localEulerTailConstant (Module.finrank ℤ (𝓞 K)) *
        ∑p ∈ q.primeFactors, ((p:ℝ)^2)⁻¹ := by
      rw [sum_add_distrib, mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ _ := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (localEulerTailConstant_nonneg _)
      exact (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).sum_le_tsum _
        (fun m _ => by positivity)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeSums
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

lemma card_primeFactors_le_log {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have hpos : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply prod_pos
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  calc
    _ = ∑ _p ∈ q.primeFactors, Real.log 2 := by simp
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p:ℝ) := by
      apply sum_le_sum
      intro p hp
      exact Real.log_le_log (by norm_num)
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
    _ = Real.log (∏ p ∈ q.primeFactors, (p:ℝ)) :=
      (Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)).symm
    _ ≤ _ := by
      apply Real.log_le_log hpos
      have H := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
      simpa only [Nat.cast_prod] using (show (((∏ p ∈ q.primeFactors, p):ℕ):ℝ) ≤ (q:ℝ) by exact_mod_cast H)

variable (K : Type*) [Field K] [NumberField K]

lemma coprime_prime_sum_split (q N : ℕ) (hq : q ≠ 0) :
    (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, coprimeIdealCoefficient K q p / p) +
      (∑p ∈ q.primeFactors.filter (fun p => p ≤ N), idealCoefficientReal K p / p) =
    ∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p := by
  have heq : q.primeFactors.filter (fun p => p ≤ N) =
      ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => p ∈ q.primeFactors) := by
    ext p
    simp only [mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp,hpN⟩
      exact ⟨⟨⟨(Nat.prime_of_mem_primeFactors hp).one_le,hpN⟩,
        Nat.prime_of_mem_primeFactors hp⟩,hp⟩
    · rintro ⟨⟨⟨_,hpN⟩,_⟩,hp⟩
      exact ⟨hp,hpN⟩
  rw [heq]
  rw [Finset.sum_filter (s := (Finset.Icc 1 N).filter Nat.Prime)
    (p := fun p => p ∈ q.primeFactors), ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hpP := (mem_filter.mp hp).2
  simp only [coprimeIdealCoefficient,ArithmeticFunction.coe_mk]
  by_cases hdiv : p ∣ q
  · have hps := Nat.mem_primeFactors.mpr ⟨hpP,hdiv,hq⟩
    have hnc : ¬p.Coprime q := by simpa only [hpP.coprime_iff_not_dvd,not_not] using hdiv
    simp [hps,hnc]
  · have hps : p ∉ q.primeFactors := by intro h; exact hdiv (Nat.dvd_of_mem_primeFactors h)
    have hcop : p.Coprime q := hpP.coprime_iff_not_dvd.mpr hdiv
    rw [ite_eq_left hcop]
    simp [hps]

lemma omitted_prime_tail (q : ℕ) {N : ℕ} (hN : 0 < N) :
    (∑p ∈ q.primeFactors.filter (fun p => N < p), idealCoefficientReal K p / p) ≤
      (Module.finrank ℤ (𝓞 K):ℝ) * q.primeFactors.card / N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑_p ∈ q.primeFactors.filter (fun p => N < p),
        (Module.finrank ℤ (𝓞 K):ℝ) / N := by
      apply sum_le_sum
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      have hpN : (N:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.le
      calc
        _ ≤ (Module.finrank ℤ (𝓞 K):ℝ) / p := by
          exact div_le_div_of_nonneg_right (idealCoefficientReal_prime_le K hpp) (Nat.cast_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hN0 hpN
    _ ≤ (q.primeFactors.card:ℝ) * ((Module.finrank ℤ (𝓞 K):ℝ)/N) := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) (by positivity)
    _ = _ := by ring

lemma prime_sum_add_log_bad_le {q N : ℕ} (hq : 0 < q) (hN : 2 ≤ N) :
    (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, coprimeIdealCoefficient K q p / p) +
      Real.log (badPrimeEuler K q) ≤
      (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p) +
      (Module.finrank ℤ (𝓞 K):ℝ) * q.primeFactors.card / N +
      localEulerTailConstant (Module.finrank ℤ (𝓞 K)) * ∑'m:ℕ, ((m:ℝ)^2)⁻¹ := by
  have hpartition : (∑p ∈ q.primeFactors, idealCoefficientReal K p / p) =
      (∑p ∈ q.primeFactors.filter (fun p => p ≤ N), idealCoefficientReal K p / p) +
      (∑p ∈ q.primeFactors.filter (fun p => N < p), idealCoefficientReal K p / p) := by
    simpa only [not_le] using
      (sum_filter_add_sum_filter_not q.primeFactors (fun p => p ≤ N)
        (fun p => idealCoefficientReal K p / p)).symm
  have H := log_badPrimeEuler_le K q
  rw [hpartition] at H
  have HS := coprime_prime_sum_split K q N hq.ne'
  have HT := omitted_prime_tail K q (show 0 < N by omega)
  linarith

 

theorem coprime_prime_exponential_le_zeta {q N : ℕ} (hq : 0 < q) (hN : 2 ≤ N)
    (hqN : Real.log q ≤ N) :
    Real.exp (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, coprimeIdealCoefficient K q p / p) ≤
      Real.exp (2*(Module.finrank ℤ (𝓞 K):ℝ) +
        (Module.finrank ℤ (𝓞 K):ℝ)/Real.log 2 +
        ((Module.finrank ℤ (𝓞 K):ℝ)^2 +
          localEulerTailConstant (Module.finrank ℤ (𝓞 K))) * ∑'m:ℕ, ((m:ℝ)^2)⁻¹) *
      (NumberField.dedekindZeta K (1+1/Real.log N)).re / badPrimeEuler K q := by
  let n : ℝ := Module.finrank ℤ (𝓞 K)
  let S : ℝ := ∑'m:ℕ, ((m:ℝ)^2)⁻¹
  let T := localEulerTailConstant (Module.finrank ℤ (𝓞 K))
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : (q.primeFactors.card:ℝ) ≤ N / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    exact (card_primeFactors_le_log hq).trans hqN
  have htail : n * q.primeFactors.card / N ≤ n / Real.log 2 := by
    calc
      _ ≤ n * ((N:ℝ)/Real.log 2) / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hn) hN0.le
      _ = _ := by field_simp
  have H := prime_sum_add_log_bad_le K hq hN
  have He : Real.exp
      ((∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, coprimeIdealCoefficient K q p / p) +
        Real.log (badPrimeEuler K q)) ≤
      Real.exp ((∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p) +
        n / Real.log 2 + T*S) := by
    apply Real.exp_le_exp.mpr
    dsimp only [n,S,T] at htail ⊢
    linarith
  rw [Real.exp_add,Real.exp_log (badPrimeEuler_pos K q)] at He
  apply (le_div_iff₀ (badPrimeEuler_pos K q)).mpr
  calc
    _ ≤ _ := He
    _ = Real.exp (n / Real.log 2 + T*S) *
        Real.exp (∑p ∈ (Finset.Icc 1 N).filter Nat.Prime, idealCoefficientReal K p / p) := by
      simp only [Real.exp_add]
      
      ring
    _ ≤ Real.exp (n / Real.log 2 + T*S) * (Real.exp (2*n+n^2*S) *
        (NumberField.dedekindZeta K (1+1/Real.log N)).re) :=
      mul_le_mul_of_nonneg_left (ideal_prime_exponential_le_zeta K hN) (Real.exp_pos _).le
    _ = _ := by
      rw [←mul_assoc, ←Real.exp_add]
      congr 2
      dsimp [n,S,T]
      ring

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem coprime_ideal_relative_interval_normalized (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℤ (𝓞 K) = n →
        ∀ q a b : ℕ, 0 < q → Real.log q ≤ b →
          R ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
          (∑m ∈ Finset.Ioc a b, coprimeIdealCoefficient K q m) ≤
            C * (((b:ℝ)-a)/Real.log b) *
              (NumberField.dedekindZeta K (1+1/Real.log b)).re / badPrimeEuler K q := by
  obtain ⟨C,hC,hInt⟩ := Sieve.divisor_bounded_relative_interval n
  let E : ℝ := Real.exp (2*(n:ℝ)+(n:ℝ)/Real.log 2+
    ((n:ℝ)^2+localEulerTailConstant n)*∑'m:ℕ, ((m:ℝ)^2)⁻¹)
  refine ⟨C*E,mul_pos hC (Real.exp_pos _),?_⟩
  intro η hη
  obtain ⟨R,hR⟩ := hInt η hη
  refine ⟨max R 2,?_⟩
  intro K _ _ hn q a b hq hqb hb hab hrel
  have hb2 : 2 ≤ b := (le_max_right R 2).trans hb
  have hcoeff : ∀m, 0 ≤ coprimeIdealCoefficient K q m ∧
      coprimeIdealCoefficient K q m ≤ (nFoldDivisor (n+1) m : ℝ) := by
    intro m
    simpa only [hn] using coprimeIdealCoefficient_bounds K q m
  have H := hR (coprimeIdealCoefficient K q)
    (coprimeIdealCoefficient_multiplicative K q) hcoeff a b
    ((le_max_left R 2).trans hb) hab hrel
  have hpe : Real.exp (∑p ∈ Sieve.smallPrimes b, coprimeIdealCoefficient K q p / p) ≤
      E * (NumberField.dedekindZeta K (1+1/Real.log b)).re / badPrimeEuler K q := by
    simpa only [E,hn,Sieve.smallPrimes] using coprime_prime_exponential_le_zeta K hq hb2 hqb
  have hfactor : 0 ≤ C * (((b:ℝ)-a)/Real.log b) := by
    apply mul_nonneg hC.le
    apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hab)
    · exact (Real.log_pos (by exact_mod_cast hb2 : (1:ℝ) < b)).le
  calc
    _ ≤ C * (((b:ℝ)-a)/Real.log b) *
        Real.exp (∑p ∈ Sieve.smallPrimes b, coprimeIdealCoefficient K q p / p) := H
    _ ≤ C * (((b:ℝ)-a)/Real.log b) *
        (E * (NumberField.dedekindZeta K (1+1/Real.log b)).re / badPrimeEuler K q) :=
      mul_le_mul_of_nonneg_left hpe hfactor
    _ = _ := by ring

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

lemma dedekindZeta_real_eq_terms (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    (NumberField.dedekindZeta K s).re =
      ∑' m : ℕ, realDirichletTerm (idealCoefficientReal K) s m := by
  simpa only [Complex.ofReal_re] using
    (congrArg Complex.re (idealDirichlet_eq_dedekindZeta K s)).symm

lemma dedekindZeta_real_nonneg (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    0 ≤ (NumberField.dedekindZeta K s).re := by
  rw [dedekindZeta_real_eq_terms]
  exact tsum_nonneg (realDirichletTerm_nonneg (idealCoefficientReal_nonneg K) s)

lemma dedekindZeta_real_antitone (K : Type*) [Field K] [NumberField K]
    {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    (NumberField.dedekindZeta K t).re ≤ (NumberField.dedekindZeta K s).re := by
  simp only [dedekindZeta_real_eq_terms]
  apply Summable.tsum_le_tsum _ (idealCoefficient_real_summable K (hs.trans_le hst))
    (idealCoefficient_real_summable K hs)
  intro m
  by_cases hm : m = 0
  · simp [hm]
  · change (idealCoefficientReal K m) / (m:ℝ)^t ≤ (idealCoefficientReal K m) / (m:ℝ)^s
    exact div_le_div_of_nonneg_left (idealCoefficientReal_nonneg K m)
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) s)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hm) hst)

 

lemma dedekindZeta_log_scale_le (K : Type*) [Field K] [NumberField K]
    {u b : ℕ} (hu : 2 ≤ u) (hub : u ≤ b) (hbu : b ≤ u^2) :
    (NumberField.dedekindZeta K (1+1/Real.log u)).re / Real.log u ≤
      2 * (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b := by
  have huR : 0 < Real.log (u:ℝ) := Real.log_pos (by exact_mod_cast hu : (1:ℝ) < u)
  have hbR : 0 < Real.log (b:ℝ) := Real.log_pos (by exact_mod_cast hu.trans hub : (1:ℝ) < b)
  have hlog : Real.log (u:ℝ) ≤ Real.log (b:ℝ) :=
    Real.log_le_log (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hu)
      (by exact_mod_cast hub)
  have hlog2 : Real.log (b:ℝ) ≤ 2*Real.log (u:ℝ) := by
    have H := Real.log_le_log (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (hu.trans hub))
      (show (b:ℝ) ≤ (u:ℝ)^2 by exact_mod_cast hbu)
    simpa only [Real.log_pow, Nat.cast_ofNat] using H
  have hz := dedekindZeta_real_nonneg K (1+1/Real.log b)
  have H := dedekindZeta_real_antitone K
    (show 1 < 1+1/Real.log (b:ℝ) by linarith [one_div_pos.mpr hbR])
    (show 1+1/Real.log (b:ℝ) ≤ 1+1/Real.log (u:ℝ) by
      linarith [one_div_le_one_div_of_le huR hlog])
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one] at H hz
  have hrec : 1/Real.log (u:ℝ) ≤ 2/Real.log (b:ℝ) := by
    apply (div_le_div_iff₀ huR hbR).mpr
    simpa using hlog2
  calc
    _ ≤ (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log u :=
      div_le_div_of_nonneg_right H huR.le
    _ ≤ (NumberField.dedekindZeta K (1+1/Real.log b)).re * (2/Real.log b) := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hrec hz
    _ = _ := by ring

 

theorem coprime_ideal_scaled_interval_oai (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K], Module.finrank ℤ (𝓞 K) = n →
        ∀ q a b d : ℕ, 0 < q → 0 < d → Real.log q ≤ (b/d : ℕ) →
          R ≤ b/d → a ≤ b → η*(b/d : ℕ) ≤ (b/d : ℕ)-(a/d : ℕ) →
          b ≤ (b/d)^2 →
          ((b/d : ℕ):ℝ)-(a/d : ℕ) ≤ 2*((b:ℝ)-a)/d →
          (∑ m ∈ Ioc (a/d) (b/d), coprimeIdealCoefficient K q m) ≤
            C * (((b:ℝ)-a)/d) *
              ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b) /
                badPrimeEuler K q := by
  obtain ⟨C,hC,hInt⟩ := coprime_ideal_relative_interval_normalized n
  refine ⟨4*C,by positivity,?_⟩
  intro η hη
  obtain ⟨R,hR⟩ := hInt η hη
  refine ⟨max R 2,?_⟩
  intro K _ _ hn q a b d hq hd hlog hbound hab hrel hsquare hwidth
  have hu : 2 ≤ b/d := (le_max_right R 2).trans hbound
  have H := hR K hn q (a/d) (b/d) hq hlog ((le_max_left R 2).trans hbound)
    (Nat.div_le_div_right hab) hrel
  have hlogu : 0 < Real.log ((b/d : ℕ):ℝ) := Real.log_pos (by exact_mod_cast hu : (1:ℝ) < (b/d:ℕ))
  have hΔ : 0 ≤ ((b:ℝ)-a)/d := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hab)) (Nat.cast_nonneg _)
  have hz := dedekindZeta_real_nonneg K (1+1/Real.log (b/d : ℕ))
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one] at hz
  have hscale := dedekindZeta_log_scale_le K hu (Nat.div_le_self b d) hsquare
  calc
    _ ≤ C * ((((b/d : ℕ):ℝ)-(a/d : ℕ))/Real.log (b/d : ℕ)) *
        (NumberField.dedekindZeta K (1+1/Real.log (b/d : ℕ))).re / badPrimeEuler K q := H
    _ = (C * (((b/d : ℕ):ℝ)-(a/d : ℕ))) *
        ((NumberField.dedekindZeta K (1+1/Real.log (b/d : ℕ))).re / Real.log (b/d : ℕ)) /
        badPrimeEuler K q := by ring
    _ ≤ (C * (2*((b:ℝ)-a)/d)) *
        ((NumberField.dedekindZeta K (1+1/Real.log (b/d : ℕ))).re / Real.log (b/d : ℕ)) /
        badPrimeEuler K q := by
      apply div_le_div_of_nonneg_right _ (badPrimeEuler_pos K q).le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth hC.le)
        (div_nonneg hz hlogu.le)
    _ ≤ (C * (2*((b:ℝ)-a)/d)) *
        (2 * (NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b) /
        badPrimeEuler K q := by
      apply div_le_div_of_nonneg_right _ (badPrimeEuler_pos K q).le
      apply mul_le_mul_of_nonneg_left hscale
      exact mul_nonneg hC.le (by
        simpa only [mul_div_assoc] using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hΔ)
    _ = _ := by ring

end PrimeDegreePackets
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.coprime_ideal_scaled_interval_oai.{u_1} := @OAI.PrimeDegreePackets.coprime_ideal_scaled_interval_oai.{u_1}
