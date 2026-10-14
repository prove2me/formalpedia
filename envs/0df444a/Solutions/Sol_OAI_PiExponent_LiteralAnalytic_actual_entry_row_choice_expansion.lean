-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.actual_entry_row_choice_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T09:23:54.388224+00:00
-- url     : https://prove2.me/submissions/70f38604-cd32-488e-8323-14a5a76943ba

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

namespace EntryExpansion
open MvPolynomial OAI.PiExponent.RowTranslation

section Binomial
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

lemma shift_C' (c : σ → R) (r : R) : shift c (C r) = C r := by
  simp [shift]

lemma shift_X' (c : σ → R) (i : σ) : shift c (X i) = X i + C (c i) := by
  simp [shift]

lemma shifted_power (c : σ → R) (i : σ) (n : ℕ) :
    (X i + C (c i)) ^ n =
      ∑ b : Fin (n + 1), C ((n.choose b : R) * c i ^ (n - b)) * X i ^ (b : ℕ) := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [map_mul, map_pow, map_natCast]
  ring

lemma shifted_product (c : σ → R) (a : σ → ℕ) :
    (∏ i, (X i + C (c i)) ^ a i) =
      ∑ b : (∀ i, Fin (a i + 1)),
        C (∏ i, ((a i).choose (b i) : R) * c i ^ (a i - b i)) *
          monomial (multiIndex (fun i => (b i : ℕ))) 1 := by
  simp_rw [shifted_power]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.prod_mul_distrib, ← map_prod, prod_X_pow]
  have hidx : Finsupp.indicator Finset.univ (fun i _ => (b i : ℕ)) =
      multiIndex (fun i => (b i : ℕ)) := by
    ext i
    simp [Finsupp.indicator, multiIndex]
  rw [hidx]

lemma shift_monomial (c : σ → R) (a : σ →₀ ℕ) :
    shift c (monomial a 1) = ∏ i, (X i + C (c i)) ^ a i := by
  simp only [shift, eval₂Hom_monomial, map_one, one_mul]
  exact a.prod_fintype _ (fun i => pow_zero _)

lemma shift_coefficient (c : σ → R) (β a : σ →₀ ℕ) :
    shiftCoefficient c β a = ∏ i, ((a i).choose (β i) : R) * c i ^ (a i - β i) := by
  classical
  rw [shiftCoefficient, shift_monomial, shifted_product, coeff_sum]
  simp only [coeff_C_mul, coeff_monomial]
  by_cases h : ∀ i, β i ≤ a i
  · let b₀ : ∀ i, Fin (a i + 1) := fun i => ⟨β i, Nat.lt_succ_of_le (h i)⟩
    have hidx : multiIndex (fun i => (b₀ i : ℕ)) = β := by
      ext i
      simp [b₀, multiIndex]
    rw [Finset.sum_eq_single b₀]
    · simp [hidx, b₀]
    · intro b hb hne
      have hidx' : multiIndex (fun i => (b i : ℕ)) ≠ β := by
        intro he
        apply hne
        funext i
        apply Fin.ext
        have hi := congrArg (fun d : σ →₀ ℕ => d i) he
        simpa [b₀, multiIndex] using hi
      simp [hidx']
    · simp
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hright : (∏ j, ((a j).choose (β j) : R) * c j ^ (a j - β j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    rw [hright]
    apply Finset.sum_eq_zero
    intro b hb
    have hidx : multiIndex (fun j => (b j : ℕ)) ≠ β := by
      intro he
      have hi' := congrArg (fun d : σ →₀ ℕ => d i) he
      have hbi : (b i : ℕ) = β i := by simpa [multiIndex] using hi'
      have hlt := (b i).isLt
      omega
    simp [hidx]

lemma binomial_product (ε τ : σ → R) (n : σ → ℕ) :
    (∏ i, (ε i + τ i) ^ n i) =
      ∑ d : (∀ i, Fin (n i + 1)),
        ((∏ i, (n i).choose (d i) : ℕ) : R) *
          (∏ i, ε i ^ (n i - d i)) * ∏ i, τ i ^ (d i : ℕ) := by
  have h (i : σ) : (ε i + τ i) ^ n i =
      ∑ d : Fin (n i + 1), ((n i).choose d : R) * ε i ^ (n i - d) * τ i ^ (d : ℕ) := by
    rw [add_comm, add_pow, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp_rw [h]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.prod_mul_distrib, Nat.cast_prod]

lemma coefficient_shift_over (c : σ → R) (p : MvPolynomial σ R) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) :
    (shift c p).coeff β = ∑ a ∈ S, p.coeff a * shiftCoefficient c β a := by
  classical
  have h : (shift c p).coeff β =
      ∑ a ∈ p.support, p.coeff a * shiftCoefficient c β a := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, coeff_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [show monomial a (p.coeff a) = C (p.coeff a) * monomial a 1 by
      simp [C_mul_monomial]]
    simp [shiftCoefficient, coeff_C_mul, shift_C']
  rw [h]
  apply Finset.sum_subset hp
  intro a ha hnot
  simp [MvPolynomial.notMem_support_iff.mp hnot]
end Binomial

section Series
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

lemma coefficient_error_tail (ε : σ → R) (τ : σ → PowerSeries R)
    (n : σ → ℕ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, (PowerSeries.C (ε i) + τ i) ^ n i) =
      ∑ d : (∀ i, Fin (n i + 1)),
        ((∏ i, (n i).choose (d i) : ℕ) : R) *
          (∏ i, ε i ^ (n i - d i)) *
            PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ)) := by
  rw [binomial_product]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [← map_pow, ← map_prod]
  rw [show ((∏ i, (n i).choose (d i) : ℕ) : PowerSeries R) =
    PowerSeries.C (((∏ i, (n i).choose (d i) : ℕ) : R)) by simp]
  rw [← map_mul, PowerSeries.coeff_C_mul]

lemma coefficient_scalar (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (k : ℕ) :
    PowerSeries.coeff k (shiftCoefficient (fun i => PowerSeries.C (ε i) + τ i) β a) =
      ∑ d : (∀ i, Fin (a i - β i + 1)), rowScalar ε τ β a d k := by
  rw [shift_coefficient, Finset.prod_mul_distrib]
  have hcast : (∏ i, ((a i).choose (β i) : PowerSeries R)) =
      PowerSeries.C ((∏ i, (a i).choose (β i) : ℕ) : R) := by simp
  rw [hcast, PowerSeries.coeff_C_mul, coefficient_error_tail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [rowScalar, Finset.prod_mul_distrib, Nat.cast_mul]
  ring

lemma row_identity (ε : σ → R) (τ : σ → PowerSeries R)
    (p : MvPolynomial σ (PowerSeries R)) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) (s : ℕ) :
    PowerSeries.coeff s ((shift (fun i => PowerSeries.C (ε i) + τ i) p).coeff β) =
      ∑ t : RowChoices S β s, rowScalar ε τ β t.1.1 t.2.1 t.2.2 *
        PowerSeries.coeff (s - t.2.2) (p.coeff t.1.1) := by
  classical
  rw [coefficient_shift_over _ p β S hp]
  simp only [map_sum]
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm, PowerSeries.coeff_mul]
  simp only [coefficient_scalar, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
end Series

lemma period_coefficient {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (MatrixTranslation.periodMonomial j ω h a).coeff A =
      ((∏ i, (a i).choose (A i) : ℕ) : PowerSeries ℂ) *
        (1 + PowerSeries.X) ^ h *
          MatrixTranslation.periodCoordinate j ω ^ (∑ i : Fin m, (a i - A i)) := by
  have hs : MatrixTranslation.periodMonomial j ω h a =
      C ((1 + PowerSeries.X) ^ h) *
        shift (fun _ => MatrixTranslation.periodCoordinate j ω)
          (monomial (InterpolationMatrix.exponentVector a) 1) := by
    rw [shift_monomial]
    simp [MatrixTranslation.periodMonomial, InterpolationMatrix.exponentVector, add_comm]
  rw [hs, coeff_C_mul]
  change _ * shiftCoefficient _ _ _ = _
  rw [shift_coefficient, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [InterpolationMatrix.exponentVector, Finsupp.equivFunOnFinite_symm_apply_apply,
    Nat.cast_prod]
  ring

lemma period_support_le {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) {A : Fin m →₀ ℕ}
    (hA : A ∈ (MatrixTranslation.periodMonomial j ω h a).support) : ∀ i, A i ≤ a i := by
  intro i
  by_contra hn
  have hi : a i < A i := Nat.lt_of_not_ge hn
  have hz : (∏ k, (a k).choose (A k) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Nat.choose_eq_zero_of_lt hi
  exact (MvPolynomial.mem_support_iff.mp hA) (by rw [period_coefficient, hz]; simp)

lemma actual_support {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) (c : Column d H) :
    (MatrixTranslation.periodMonomial r.1.val logarithmicPeriod (c.1 0)
      (fun i => c.1 i.succ)).support ⊆ MatrixTranslation.transverseIndices (fixedWeights d) H := by
  classical
  intro A hA
  have hle := period_support_le r.1.val logarithmicPeriod (c.1 0) (fun i => c.1 i.succ) hA
  have hc := Finset.mem_filter.mp c.2
  have hbox := Fintype.mem_piFinset.mp hc.1
  have hw : ∀ i, 0 ≤ fixedWeights d i := fun i => by
    unfold fixedWeights MatrixArithmetic.logWeights
    positivity
  have hs : ∑ i : Fin d.m, fixedWeights d i * (c.1 i.succ : ℝ) ≤ H := by
    have hh := hc.2
    rw [Fin.sum_univ_succ] at hh
    change (d.w0 : ℝ) * (c.1 0 : ℝ) +
      (∑ i : Fin d.m, fixedWeights d i * (c.1 i.succ : ℝ)) ≤ H at hh
    exact (le_add_of_nonneg_left (mul_nonneg d.w0_pos.le (Nat.cast_nonneg _))).trans hh
  unfold MatrixTranslation.transverseIndices
  apply Finset.mem_map.mpr
  refine ⟨(fun i => A i), ?_, ?_⟩
  · unfold realWeightedSimplex
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      have hi := Finset.mem_range.mp (hbox i.succ)
      apply Finset.mem_range.mpr
      change A i < ⌊H / fixedWeights d i⌋₊ + 1
      change c.1 i.succ < ⌊H / fixedWeights d i⌋₊ + 1 at hi
      exact lt_of_le_of_lt (hle i) hi
    · apply le_trans _ hs
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle i) (hw i)
  · ext i
    simp

lemma period_shift {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j : ℕ) (ω : ℂ) (h : ℕ) (a : Fin m → ℕ) :
    shift (fun i => PowerSeries.C ((j : ℂ) * (r i - ω)) + tail (T i) (PowerSeries.log ℂ))
      (MatrixTranslation.periodMonomial j ω h a) =
      MvPolynomial.map Polynomial.coeToPowerSeries.ringHom
        (InterpolationMatrix.monomialImage r (fun i => InterpolationMatrix.truncatedLog (T i)) j h a) := by
  have hc (i : Fin m) : MatrixTranslation.periodCoordinate j ω +
      (PowerSeries.C ((j : ℂ) * (r i - ω)) + tail (T i) (PowerSeries.log ℂ)) =
      PowerSeries.C ((j : ℂ) * r i) + (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) := by
    unfold MatrixTranslation.periodCoordinate tail InterpolationMatrix.truncatedLog
    calc
      _ = PowerSeries.C ((j : ℂ) * ω) + PowerSeries.C ((j : ℂ) * (r i - ω)) +
          (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) := by ring
      _ = _ := by rw [← map_add]; congr 1; congr 1; ring
  simp only [MatrixTranslation.periodMonomial, InterpolationMatrix.monomialImage,
    map_mul, map_prod, map_pow, map_add, shift_C', shift_X', MvPolynomial.map_C,
    MvPolynomial.map_X, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_one, Polynomial.coe_X]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  calc
    _ = C (MatrixTranslation.periodCoordinate j ω +
        (PowerSeries.C ((j : ℂ) * (r i - ω)) + tail (T i) (PowerSeries.log ℂ))) + X i := by
      simp only [map_add, map_mul]
      ring
    _ = _ := by rw [hc]; simp [map_add]
end EntryExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (r : Row d H) (c : Column d H) :
    actualMatrix d H r c =
      ∑ t : RowChoice d H r, choiceScalar d r t *
        PowerSeries.coeff (r.2.1 0 - t.2.2)
          ((MatrixTranslation.periodMonomial r.1.val logarithmicPeriod
            (c.1 0) (fun i => c.1 i.succ)).coeff t.1.1) := by
  classical
  have he := EntryExpansion.row_identity
    (fun i => (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - logarithmicPeriod))
    (fun i => RowTranslation.tail
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) (PowerSeries.log ℂ))
    (MatrixTranslation.periodMonomial r.1.val logarithmicPeriod (c.1 0) (fun i => c.1 i.succ))
    (beta d r) (MatrixTranslation.transverseIndices (fixedWeights d) H)
    (EntryExpansion.actual_support d r c) (r.2.1 0)
  rw [EntryExpansion.period_shift] at he
  simp only [MvPolynomial.coeff_map, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeff_coe] at he
  convert! he using 1
