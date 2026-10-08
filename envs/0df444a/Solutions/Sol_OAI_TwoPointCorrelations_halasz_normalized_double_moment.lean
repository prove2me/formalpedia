-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_normalized_double_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:34:13.491862+00:00
-- url     : https://prove2.me/submissions/d6150b86-f413-4c46-97d2-807087ff9a08

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
namespace OAI

/-! The diagonal algebra for the complete Vinogradov system: its first
s power sums determine all elementary symmetric functions of s entries.
This is the finite algebraic starting point for the mean-value argument
underlying Ford's logarithmic exponential-sum estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MvPolynomial




@[simp] lemma mem_halaszVinogradovFiber {s N k : ℕ} {x y : Fin s → Fin N} :
    y ∈ halaszVinogradovFiber x k ↔ ∀ j ∈ Icc 1 k,
      (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j := by
  classical
  simp [halaszVinogradovFiber]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovOrthogonality
namespace OAI

/-! Fourier orthogonality for the complete Vinogradov system, with
normalised Haar measure on its coefficient torus. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate





lemma halasz_vinogradov_fourier_integral (n : ℤ) :
    (∫ x : AddCircle (1:ℝ), fourier n x ∂AddCircle.haarAddCircle) =
      if n=0 then (1:ℂ) else 0 := by
  by_cases hn : n=0
  · subst n
    simp
  · simp only [hn,ite_false]
    exact integral_eq_zero_of_add_right_eq_neg
      (fourier_add_half_inv_index hn (by norm_num))

theorem halasz_vinogradov_character_integral {k : ℕ} (m : Fin k → ℤ) :
    (∫ α, halaszVinogradovCharacter m α ∂halaszVinogradovHaar k) =
      if m=0 then (1:ℂ) else 0 := by
  unfold halaszVinogradovCharacter halaszVinogradovHaar
  rw [integral_fintype_prod_eq_prod]
  simp_rw [halasz_vinogradov_fourier_integral]
  by_cases hm : m=0
  · subst m
    simp
  · simp only [hm,ite_false]
    obtain ⟨j,hj⟩ : ∃ j, m j≠0 := by
      by_contra hn
      push Not at hn
      apply hm
      funext j
      exact hn j
    apply prod_eq_zero (mem_univ j)
    simp [hj]

lemma halasz_vinogradov_character_add {k : ℕ} (m n : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (m+n) α =
      halaszVinogradovCharacter m α*halaszVinogradovCharacter n α := by
  simp only [halaszVinogradovCharacter,Pi.add_apply,fourier_add,prod_mul_distrib]

lemma halasz_vinogradov_character_neg {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (-m) α = conj (halaszVinogradovCharacter m α) := by
  simp only [halaszVinogradovCharacter,Pi.neg_apply,fourier_neg,map_prod]


lemma halasz_vinogradov_character_integrable {k : ℕ} (m : Fin k → ℤ) :
    Integrable (halaszVinogradovCharacter m) (halaszVinogradovHaar k) := by
  exact (halasz_vinogradov_character_continuous m).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma halasz_vinogradov_character_inner {k : ℕ} (m n : Fin k → ℤ) :
    (∫ α, halaszVinogradovCharacter m α*conj (halaszVinogradovCharacter n α)
      ∂halaszVinogradovHaar k) = if m=n then (1:ℂ) else 0 := by
  simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
  rw [halasz_vinogradov_character_integral]
  simp only [← sub_eq_add_neg,sub_eq_zero]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovMoment
namespace OAI

/-! The complete Vinogradov solution count is exactly a torus moment of
the polynomial exponential sum. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate



lemma halasz_vinogradov_character_sum {s k : ℕ} (S : Finset (Fin s))
    (m : Fin s → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (∑ i ∈ S, m i) α =
      ∏ i ∈ S, halaszVinogradovCharacter (m i) α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [halaszVinogradovCharacter]
  | @insert i S hi ih =>
    rw [sum_insert hi,prod_insert hi,halasz_vinogradov_character_add,ih]

lemma halasz_vinogradov_power_expand (s k N : ℕ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovPolynomial k N α ^ s =
      ∑ x : Fin s → Fin N, halaszVinogradovCharacter (halaszVinogradovFrequency k x) α := by
  classical
  rw [halaszVinogradovPolynomial,Fintype.sum_pow]
  apply sum_congr rfl
  intro x _
  rw [← halasz_vinogradov_character_sum]
  congr 1
  ext j
  simp [halaszVinogradovFrequency]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFrequencyBox
namespace OAI

/-! Explicit coordinate bounds for complete-system frequencies. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_vinogradov_frequency_nonneg {s k M : ℕ} (x : Fin s → Fin M) (j : Fin k) :
    0≤ halaszVinogradovFrequency k x j := by
  unfold halaszVinogradovFrequency
  exact sum_nonneg (fun _ _ => Int.natCast_nonneg _)

lemma halasz_vinogradov_frequency_le {s k M : ℕ} (x : Fin s → Fin M) (j : Fin k) :
    halaszVinogradovFrequency k x j≤(s*M^(j.val+1):ℕ) := by
  unfold halaszVinogradovFrequency
  have hh : (∑ i, ((x i).val+1)^(j.val+1))≤ s*M^(j.val+1) := by
    calc
      _ ≤ ∑ _i : Fin s,M^(j.val+1) := sum_le_sum (fun i _ =>
        Nat.pow_le_pow_left (by omega : (x i).val+1≤ M) _)
      _ = _ := by simp
  exact_mod_cast hh

lemma halasz_vinogradov_difference_abs {s k M : ℕ}
    (x y : Fin s → Fin M) (j : Fin k) :
    |halaszVinogradovFrequency k x j-halaszVinogradovFrequency k y j|≤
      (s*M^(j.val+1):ℕ) := by
  apply abs_le.mpr
  constructor <;> linarith [halasz_vinogradov_frequency_nonneg x j,
    halasz_vinogradov_frequency_nonneg y j,halasz_vinogradov_frequency_le x j,
    halasz_vinogradov_frequency_le y j]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovRealMoment
namespace OAI

/-! Real nonnegative moments, in the form used by the mean-value
inequalities in the complete-system iteration. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate

lemma halasz_vinogradov_character_norm {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) : ‖halaszVinogradovCharacter m α‖=1 := by
  simp [halaszVinogradovCharacter,norm_prod,fourier_apply,Circle.norm_coe]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszZeroRepresentation
namespace OAI

/-! The zero-representation inequality used for the translated complete
systems: any prescribed difference has at most as many representations
as zero. This is Proposition ZRD in Ford's mean-value argument. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate




theorem halasz_representation_integral {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) :
    (∫ α, halaszRepresentationWeight f w α ∂halaszVinogradovHaar k) =
      (halaszRepresentationCount f w:ℂ) := by
  classical
  have hi (x y : ι) : Integrable (fun α =>
      (halaszVinogradovCharacter (f x) α * conj (halaszVinogradovCharacter (f y) α)) *
        halaszVinogradovCharacter (-w) α) (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  unfold halaszRepresentationWeight halaszRepresentationSum
  simp_rw [map_sum,sum_mul,mul_sum,sum_mul]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  simp_rw [integral_finsetSum _ (fun y _ => hi _ y),← halasz_vinogradov_character_neg,
    ← halasz_vinogradov_character_add,halasz_vinogradov_character_integral,
    ← sub_eq_add_neg,sub_eq_zero]
  rw [← Fintype.sum_prod_type']
  simp only [sum_boole,halaszRepresentationCount]

lemma halasz_representation_weight_norm {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) :
    ‖halaszRepresentationWeight f w α‖ = ‖halaszRepresentationSum f α‖^2 := by
  simp only [halaszRepresentationWeight,norm_mul,Complex.norm_conj,
    halasz_vinogradov_character_norm,mul_one,pow_two]

lemma halasz_representation_energy {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) :
    (∫ α, ‖halaszRepresentationSum f α‖^2 ∂halaszVinogradovHaar k) =
      (halaszRepresentationCount f 0:ℝ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hc := halasz_representation_integral f 0
  convert (preTransparency := .instances) hc using 1
  · apply integral_congr_ae
    filter_upwards [] with α
    simp [halaszRepresentationWeight,halaszVinogradovCharacter,Complex.mul_conj']

theorem halasz_zero_representation_dominates {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (w : Fin k → ℤ) :
    halaszRepresentationCount f w ≤ halaszRepresentationCount f 0 := by
  have h := norm_integral_le_integral_norm (halaszRepresentationWeight f w)
    (μ := halaszVinogradovHaar k)
  rw [halasz_representation_integral] at h
  simp_rw [halasz_representation_weight_norm] at h
  rw [halasz_representation_energy,Complex.norm_natCast] at h
  exact_mod_cast h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFiberEnergy
namespace OAI

/-! Finite energy under refinement of a partition. This is the counting
form of the Cauchy--Schwarz step that introduces the congruences on the
long variables in the complete-system mean-value argument. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_fiber_energy_rows {α β : Type*} (F : Finset α) (f : α → β) :
    halaszFiberEnergy F f = ∑ x ∈ F, (F.filter (fun y => f y=f x)).card := by
  unfold halaszFiberEnergy
  calc
    _ = ∑ t ∈ F.image f, ∑ x ∈ F.filter (fun x => f x=t),
        (F.filter (fun y => f y=f x)).card := by
      apply sum_congr rfl
      intro t _
      rw [show (∑ x ∈ F.filter (fun x => f x=t),
          (F.filter (fun y => f y=f x)).card) =
          ∑ _x ∈ F.filter (fun x => f x=t), (F.filter (fun y => f y=t)).card from
        sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2])]
      simp [pow_two]
    _ = _ := sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem f hx) _




lemma halasz_fiber_energy_congr {α β γ : Type*} (F : Finset α)
    (f : α → β) (g : α → γ)
    (h : ∀ x∈F, ∀ y∈F, f y=f x ↔ g y=g x) :
    halaszFiberEnergy F f = halaszFiberEnergy F g := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows]
  apply sum_congr rfl
  intro x hx
  congr 1
  ext y
  simpa only [mem_filter] using and_congr_right (fun hy => h x hx y hy)



lemma halasz_fiber_energy_representation {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) :
    halaszFiberEnergy univ f = halaszRepresentationCount f 0 := by
  rw [halasz_fiber_energy_rows]
  unfold halaszRepresentationCount
  rw [show (univ.filter (fun xy : ι × ι => f xy.1-f xy.2=0)) =
      univ.filter (fun xy : ι × ι => f xy.2=f xy.1) by
    ext xy
    simp only [mem_filter,mem_univ,true_and,sub_eq_zero]
    exact eq_comm]
  simp_rw [card_eq_sum_ones,sum_filter]
  rw [← Fintype.sum_prod_type']
  congr 1
  funext x
  by_cases h : f x.2=f x.1 <;> simp [h]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLongShortEnergy
namespace OAI

/-! Once the long variables agree modulo a prime power exceeding their
range, the remaining energy is the ordinary complete-system moment. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_nat_power_frequency_eq {s k N : ℕ} (x y : Fin s → Fin N) :
    halaszNatPowerFrequency k y = halaszNatPowerFrequency k x ↔
      y ∈ halaszVinogradovFiber x k := by
  rw [mem_halaszVinogradovFiber]
  constructor
  · intro h j hj
    have hj1 := (mem_Icc.mp hj).1
    have hjk := (mem_Icc.mp hj).2
    have he := congrFun h (⟨j-1,by omega⟩ : Fin k)
    simpa only [halaszNatPowerFrequency,Nat.sub_add_cancel hj1] using he.symm
  · intro h
    funext j
    exact (h (j.val+1) (mem_Icc.mpr ⟨by omega,by omega⟩)).symm

lemma halasz_nat_power_energy (s k N : ℕ) :
    halaszFiberEnergy (univ : Finset (Fin s → Fin N)) (halaszNatPowerFrequency k) =
      halaszVinogradovCount s k N := by
  rw [halasz_fiber_energy_rows,halaszVinogradovCount]
  apply sum_congr rfl
  intro x _
  congr 1
  ext y
  simp only [mem_filter,mem_univ,true_and,halasz_nat_power_frequency_eq]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCollisionPartition
namespace OAI

/-! The complete-system moment is controlled by the tuples whose
chosen long coordinates are pairwise distinct. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma halasz_frequency_energy (n k N : ℕ) :
    halaszFiberEnergy (univ : Finset (Fin n → Fin N)) (halaszVinogradovFrequency k) =
      halaszVinogradovCount n k N := by
  rw [← halasz_nat_power_energy n k N]
  apply halasz_fiber_energy_congr
  intro x _ y _
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    simp only [halaszVinogradovFrequency,← Nat.cast_sum] at hj
    exact_mod_cast hj
  · intro h
    funext j
    simp only [halaszVinogradovFrequency,← Nat.cast_sum]
    exact_mod_cast congrFun h j


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDifferenceCount
namespace OAI

/-! Counting allowed differences by the zero-representation inequality. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_difference_set_count {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (W : Finset (Fin k → ℤ)) :
    (univ.filter (fun xy : ι×ι => f xy.1-f xy.2∈W)).card≤
      W.card*halaszRepresentationCount f 0 := by
  have hsub : univ.filter (fun xy : ι×ι => f xy.1-f xy.2∈W) ⊆
      W.biUnion (fun w => univ.filter (fun xy : ι×ι => f xy.1-f xy.2=w)) := by
    intro xy hxy
    exact mem_biUnion.mpr ⟨f xy.1-f xy.2,(mem_filter.mp hxy).2,
      mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ ∑ w∈W,(univ.filter (fun xy : ι×ι => f xy.1-f xy.2=w)).card := card_biUnion_le
    _ = ∑ w∈W,halaszRepresentationCount f w := rfl
    _ ≤ ∑ _w∈W,halaszRepresentationCount f 0 :=
      sum_le_sum (fun w _ => halasz_zero_representation_dominates f w)
    _ = _ := by simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWeightedMeanSquare
namespace OAI

/-! Weighted Schur estimates for the prime-supported polynomials in Halász's
mean-value argument.  The weight occurs only once in the squared coefficient
sum, so a bound for the weighted frequency rows saves the extra logarithm
that an unrestricted integer mean-value theorem would lose. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators _root_.Classical

lemma halasz_weighted_symmetric_row_bound {ι : Type*} (S : Finset ι)
    (K : ι → ι → ℝ) (w v : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, w j * K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, (v i * w i) * (v j * w j) * K i j) ≤
      C * ∑ i ∈ S, (v i) ^ 2 * w i := by
  have he : (∑ i ∈ S, ∑ j ∈ S,
      ((v i) ^ 2 + (v j) ^ 2) / 2 * (w i * w j * K i j)) =
      ∑ i ∈ S, (v i) ^ 2 * w i * ∑ j ∈ S, w j * K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S)
      (f := fun i j => (v j) ^ 2 / 2 * (w i * w j * K i j))]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [hsymm j hj i hi]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        ((v i) ^ 2 + (v j) ^ 2) / 2 * (w i * w j * K i j) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hv : v i * v j ≤ ((v i) ^ 2 + (v j) ^ 2) / 2 := by
        nlinarith [sq_nonneg (v i - v j)]
      convert (preTransparency := .instances) mul_le_mul_of_nonneg_right hv
        (mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (hK i hi j hj)) using 1; ring
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * w i * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (mul_nonneg (sq_nonneg _) (hw i hi))
    _ = _ := by rw [← sum_mul, mul_comm]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseGram
namespace OAI

/-! Finite duality for sparse Dirichlet-polynomial samples.  The analytic
input is an explicit Gram-row sum, with no density-to-energy substitution. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_gram_synthesis {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (a : ι → ℂ)
    {B : ℝ} (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    ‖∑ i ∈ S, a i • v i‖^2 ≤ B * ∑ i ∈ S, ‖a i‖^2 := by
  calc
    _ = (inner ℂ (∑ i ∈ S, a i • v i) (∑ i ∈ S, a i • v i)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ ≤ ‖inner ℂ (∑ i ∈ S, a i • v i) (∑ i ∈ S, a i • v i)‖ := re_le_norm _
    _ = ‖∑ i ∈ S, ∑ j ∈ S, conj (a i) * a j * inner ℂ (v i) (v j)‖ := by
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖conj (a i) * a j * inner ℂ (v i) (v j)‖ := by
      exact (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (‖a i‖ * 1) * (‖a j‖ * 1) * ‖inner ℂ (v i) (v j)‖ := by
      simp only [norm_mul, norm_conj, mul_one]
    _ ≤ B * ∑ i ∈ S, ‖a i‖^2 := by
      simpa only [mul_one] using halasz_weighted_symmetric_row_bound S
        (fun i j => ‖inner ℂ (v i) (v j)‖) (fun _ => 1) (fun i => ‖a i‖) B
        (fun _ _ => by norm_num) (fun _ _ _ _ => norm_nonneg _)
        (fun i _ j _ => norm_inner_symm _ _) (by simpa only [one_mul] using hrow)

/-- Finite Bessel inequality with an absolute Gram-row bound. -/
theorem mrt_gram_analysis {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (u : E)
    {B : ℝ} (hB : 0 ≤ B) (hrow : ∀ i ∈ S, ∑ j ∈ S, ‖inner ℂ (v i) (v j)‖ ≤ B) :
    (∑ i ∈ S, ‖inner ℂ (v i) u‖^2) ≤ B * ‖u‖^2 := by
  let b := fun i => inner ℂ (v i) u
  let z := ∑ i ∈ S, b i • v i
  let A := ∑ i ∈ S, ‖b i‖^2
  have hA : 0 ≤ A := sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : inner ℂ z u = (A : ℂ) := by
    dsimp only [z, A]
    rw [sum_inner]
    push_cast
    apply sum_congr rfl
    intro i _
    rw [inner_smul_left]
    exact conj_mul' (b i)
  have hc : A ≤ ‖z‖ * ‖u‖ := by
    calc
      A = ‖inner ℂ z u‖ := by rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
      _ ≤ _ := norm_inner_le_norm _ _
  have hz2 : ‖z‖^2 ≤ B*A := mrt_gram_synthesis S v b hrow
  have hc2 : A^2 ≤ ‖z‖^2 * ‖u‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hA hc 2
  have hprod := mul_le_mul_of_nonneg_right hz2 (sq_nonneg ‖u‖)
  by_cases hAz : A = 0
  · change A ≤ B * ‖u‖^2
    rw [hAz]
    exact mul_nonneg hB (sq_nonneg _)
  · change A ≤ B * ‖u‖^2
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    apply (mul_le_mul_iff_right₀ hApos).mp
    calc
      A * A = A^2 := by ring
      _ ≤ B * A * ‖u‖^2 := hc2.trans hprod
      _ = A * (B * ‖u‖^2) := by ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTorusBessel
namespace OAI

/-! Finite Fourier Bessel inequality on the coefficient torus, for the
localized kernel in the double mean-value estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.Classical


lemma halasz_character_l2_coe {k : ℕ} (m : Fin k → ℤ) :
    (halaszCharacterL2 m : (Fin k → AddCircle (1:ℝ)) → ℂ) =ᵐ[halaszVinogradovHaar k]
      halaszVinogradovCharacter m :=
  ContinuousMap.coeFn_toAEEqFun (halaszVinogradovHaar k)
    ⟨halaszVinogradovCharacter m,halasz_vinogradov_character_continuous m⟩

lemma halasz_character_l2_inner {k : ℕ} (m n : Fin k → ℤ) :
    inner ℂ (halaszCharacterL2 m) (halaszCharacterL2 n) = if m=n then 1 else 0 := by
  rw [L2.inner_def]
  have hh : (∫ α, inner ℂ (halaszCharacterL2 m α) (halaszCharacterL2 n α)
      ∂halaszVinogradovHaar k) =
      ∫ α, halaszVinogradovCharacter n α*conj (halaszVinogradovCharacter m α)
        ∂halaszVinogradovHaar k := by
    apply integral_congr_ae
    filter_upwards [halasz_character_l2_coe m,halasz_character_l2_coe n] with α hm hn
    rw [hm,hn]
    simp only [RCLike.inner_apply',mul_comm]
  rw [hh,halasz_vinogradov_character_inner]
  simp only [eq_comm]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCircleWindow
namespace OAI

/-! A compact circle window with a lower bound for its small Fourier
coefficients. This supplies the localizer for the double moment estimate. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ComplexConjugate

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩



lemma halasz_circle_window_volume {δ : ℝ} (hδ : 0≤δ) (hδhalf : δ≤1/2) :
    AddCircle.haarAddCircle.real (closedBall (0:AddCircle (1:ℝ)) δ)=2*δ := by
  have hμ : (volume : Measure (AddCircle (1:ℝ)))=AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ)))
  rw [← hμ,measureReal_def,AddCircle.volume_closedBall,
    min_eq_right (by linarith : 2*δ≤1),ENNReal.toReal_ofReal (by positivity)]

lemma halasz_circle_character_re {δ : ℝ} {n : ℤ}
    (hphase : 2*Real.pi*|(n:ℝ)| * δ≤1) (x : AddCircle (1:ℝ)) (hx : x∈closedBall 0 δ) :
    (1/2:ℝ)≤(fourier n x).re := by
  let y := AddCircle.equivIoc (1:ℝ) (-(1/2:ℝ)) x
  have hy : -(1/2:ℝ)<(y:ℝ) ∧ (y:ℝ)≤1/2 := by
    have hh := y.property
    change -(1/2:ℝ)<(y:ℝ) ∧ (y:ℝ)≤-(1/2:ℝ)+1 at hh
    constructor <;> linarith [hh.1,hh.2]
  have hyx : ((y:ℝ):AddCircle (1:ℝ))=x := AddCircle.coe_equivIoc
  have hn : ‖x‖=|(y:ℝ)| := by
    rw [← hyx]
    exact (AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num)).mpr
      (by simpa using abs_le.mpr ⟨hy.1.le,hy.2⟩)
  have hyδ : |(y:ℝ)|≤δ := by
    simpa only [mem_closedBall,dist_zero_right,hn] using hx
  have ha : |2*Real.pi*(n:ℝ)*(y:ℝ)|≤1 := by
    rw [abs_mul,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]
    exact (mul_le_mul_of_nonneg_left hyδ (by positivity)).trans hphase
  have hs : (2*Real.pi*(n:ℝ)*(y:ℝ))^2≤1 := by
    nlinarith [(abs_le.mp ha).1,(abs_le.mp ha).2]
  have hc := Real.one_sub_sq_div_two_le_cos (x := 2*Real.pi*(n:ℝ)*(y:ℝ))
  rw [← hyx,fourier_coe_apply]
  have he : (Complex.exp (2*↑Real.pi*Complex.I*(n:ℂ)*(y:ℂ)/(1:ℂ))).re =
      Real.cos (2*Real.pi*(n:ℝ)*(y:ℝ)) := by
    rw [show 2*↑Real.pi*Complex.I*(n:ℂ)*(y:ℂ)/(1:ℂ)=
      ((2*Real.pi*(n:ℝ)*(y:ℝ):ℝ):ℂ)*Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  norm_num only [Complex.ofReal_one] at *
  rw [he]
  linarith

/-- The small Fourier coefficients of the indicator window cannot cancel. -/
theorem halasz_circle_window_coefficient {δ : ℝ} {n : ℤ}
    (hδ : 0≤δ) (hδhalf : δ≤1/2) (hphase : 2*Real.pi*|(n:ℝ)| * δ≤1) :
    δ≤‖∫ x : AddCircle (1:ℝ), conj (fourier n x)*halaszCircleWindow δ x
      ∂AddCircle.haarAddCircle‖ := by
  have hi : IntegrableOn (fun x : AddCircle (1:ℝ) => conj (fourier n x))
      (closedBall 0 δ) AddCircle.haarAddCircle := by
    exact ((Complex.continuous_conj.comp (fourier n).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  have heq : (∫ x : AddCircle (1:ℝ), conj (fourier n x)*halaszCircleWindow δ x
      ∂AddCircle.haarAddCircle) =
      ∫ x in closedBall (0:AddCircle (1:ℝ)) δ, conj (fourier n x)
        ∂AddCircle.haarAddCircle := by
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈closedBall (0:AddCircle (1:ℝ)) δ <;>
      simp [halaszCircleWindow,hx]
  rw [heq]
  apply le_trans _ (Complex.re_le_norm _)
  change δ≤ RCLike.re (∫ x in closedBall (0:AddCircle (1:ℝ)) δ,
    conj (fourier n x) ∂AddCircle.haarAddCircle)
  rw [← integral_re hi]
  have hh := setIntegral_mono_on (integrableOn_const (C := (1/2:ℝ))) hi.re
    measurableSet_closedBall (fun x hx => by
      change (1/2:ℝ)≤(conj (fourier n x)).re
      simpa only [Complex.conj_re] using halasz_circle_character_re hphase x hx)
  rw [setIntegral_const,smul_eq_mul,halasz_circle_window_volume hδ hδhalf] at hh
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFiniteHolder
namespace OAI

/-! The two finite Hölder steps used in the double mean-value argument. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_finite_weighted_power {ι : Type*} (S : Finset ι)
    (w f : ι → ℝ) (hw : ∀ i, 0≤ w i) (hf : ∀ i, 0≤ f i)
    {s : ℕ} (hs : 1≤ s) :
    (∑ i∈S, w i*f i)^s ≤ (∑ i∈S,w i)^(s-1)*(∑ i∈S,w i*(f i)^s) := by
  have hsR : (1:ℝ)≤ s := by exact_mod_cast hs
  have hs0 : (s:ℝ)≠0 := by exact_mod_cast (by omega : s≠0)
  have h := Real.inner_le_weight_mul_Lp_of_nonneg S hsR w f hw hf
  have hp := pow_le_pow_left₀ (sum_nonneg (fun i _ => mul_nonneg (hw i) (hf i))) h s
  have hW : 0≤∑ i∈S,w i := sum_nonneg (fun i _ => hw i)
  have hF : 0≤∑ i∈S,w i*(f i)^(s:ℝ) := sum_nonneg (fun i _ =>
    mul_nonneg (hw i) (Real.rpow_nonneg (hf i) _))
  have he : (1-(s:ℝ)⁻¹)*(s:ℝ)=((s-1:ℕ):ℝ) := by
    rw [Nat.cast_sub hs,Nat.cast_one]
    field_simp
  rw [mul_pow,← Real.rpow_mul_natCast hW,← Real.rpow_mul_natCast hF,
    he,inv_mul_cancel₀ hs0,Real.rpow_one,Real.rpow_natCast] at hp
  simpa only [Real.rpow_natCast] using hp

theorem halasz_finite_weighted_holder {ι : Type*} (S : Finset ι)
    (w f : ι → ℝ) (hw : ∀ i, 0≤ w i) (hf : ∀ i, 0≤ f i)
    {s : ℕ} (hs : 1≤ s) :
    (∑ i∈S,w i*f i)^(2*s) ≤
      (∑ i∈S,w i)^(2*s-2)*(∑ i∈S,(w i)^2)*(∑ i∈S,(f i)^(2*s)) := by
  have h := halasz_finite_weighted_power S w f hw hf hs
  have hp := pow_le_pow_left₀ (pow_nonneg
    (sum_nonneg (fun i _ => mul_nonneg (hw i) (hf i))) s) h 2
  have hc := sum_mul_sq_le_sq_mul_sq S w (fun i => (f i)^s)
  rw [mul_pow,← pow_mul,← pow_mul] at hp
  rw [show s*2=2*s by omega,show (s-1)*2=2*s-2 by omega] at hp
  simp only [← pow_mul,show s*2=2*s by omega] at hc
  exact hp.trans (by
    have hh := mul_le_mul_of_nonneg_left hc (pow_nonneg
      (sum_nonneg (s := S) (fun i _ => hw i)) (2*s-2))
    simpa only [mul_assoc] using hh)

lemma halasz_complex_sum_power {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    {r : ℕ} (hr : 1≤ r) :
    ‖∑ i∈S,z i‖^r≤(S.card:ℝ)^(r-1)*(∑ i∈S,‖z i‖^r) := by
  have hh := halasz_finite_weighted_power S (fun _ => (1:ℝ)) (fun i => ‖z i‖)
    (fun _ => zero_le_one) (fun _ => norm_nonneg _) hr
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S z) r
  exact hn.trans (by simpa using hh)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFiberHolder
namespace OAI

/-! Weighted Hölder after grouping tuples by their complete-system
frequency. The square multiplicity sum is exactly the Vinogradov energy. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_fiber_norm_sum {α β : Type*} (F : Finset α) (f : α → β) (z : β → ℂ) :
    ‖∑ a∈F,z (f a)‖≤∑ c∈F.image f,((F.filter (fun a => f a=c)).card:ℝ)*‖z c‖ := by
  apply (norm_sum_le _ _).trans_eq
  rw [← sum_fiberwise_of_maps_to (s := F) (t := F.image f) (g := f)
    (fun a ha => mem_image_of_mem f ha)]
  apply sum_congr rfl
  intro c _
  calc
    _ = ∑ _a∈F.filter (fun a => f a=c), ‖z c‖ := by
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ = _ := by simp

theorem halasz_fiber_holder {α β : Type*} (F : Finset α) (f : α → β)
    (z : β → ℂ) {s : ℕ} (hs : 1≤ s) :
    ‖∑ a∈F,z (f a)‖^(2*s) ≤ (F.card:ℝ)^(2*s-2)*
      (halaszFiberEnergy F f:ℝ)*(∑ c∈F.image f,‖z c‖^(2*s)) := by
  have h := halasz_finite_weighted_holder (F.image f)
    (fun c => ((F.filter (fun a => f a=c)).card:ℝ)) (fun c => ‖z c‖)
    (fun _ => Nat.cast_nonneg _) (fun _ => norm_nonneg _) hs
  have hcard : (∑ c∈F.image f,((F.filter (fun a => f a=c)).card:ℝ))=(F.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image f F).symm
  have henergy : (∑ c∈F.image f,((F.filter (fun a => f a=c)).card:ℝ)^2)=
      (halaszFiberEnergy F f:ℝ) := by
    simp only [halaszFiberEnergy,Nat.cast_sum,Nat.cast_pow]
  rw [hcard,henergy] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (halasz_fiber_norm_sum F f z) _).trans h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleHolder
namespace OAI

/-! The two Hölder steps in Ford's double mean-value argument (Lemma 5.1),
with the full complete-system frequency on both sides. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem halasz_double_holder {ι : Type*} (B : Finset ι) (k M r s : ℕ)
    (hr : 1≤ r) (hs : 1≤ s) (α : ι → Fin k → AddCircle (1:ℝ)) :
    ∃ ε : ι → ℂ, (∀ b, ‖ε b‖=1) ∧
    ‖∑ b∈B,halaszVinogradovPolynomial k M (α b)‖^(2*r*s) ≤
      (B.card:ℝ)^((r-1)*(2*s))*(M:ℝ)^(r*(2*s-2))*
        (halaszVinogradovCount r k M:ℝ)*
          ∑ c∈(univ : Finset (Fin r → Fin M)).image (halaszVinogradovFrequency k),
            ‖∑ b∈B,ε b*halaszVinogradovCharacter c (α b)‖^(2*s) := by
  let P := fun b => halaszVinogradovPolynomial k M (α b)
  choose ε hεnorm hεeq using (fun b : ι => Complex.exists_norm_eq_mul_self ((P b)^r))
  refine ⟨ε,hεnorm,?_⟩
  let V := fun c : Fin k → ℤ => ∑ b∈B,ε b*halaszVinogradovCharacter c (α b)
  have hnonneg : 0≤∑ b∈B,‖P b‖^r := sum_nonneg (fun _ _ => by positivity)
  have hexpand : ((∑ b∈B,‖P b‖^r:ℝ):ℂ)=∑ x : Fin r → Fin M,
      V (halaszVinogradovFrequency k x) := by
    push_cast
    simp_rw [show ∀ b, ((‖P b‖:ℝ):ℂ)^r=ε b*(P b)^r from fun b => by
      simpa only [norm_pow,Complex.ofReal_pow] using hεeq b]
    dsimp only [P]
    simp_rw [halasz_vinogradov_power_expand,mul_sum]
    exact sum_comm
  have hnorm : (∑ b∈B,‖P b‖^r:ℝ)=
      ‖∑ x : Fin r → Fin M,V (halaszVinogradovFrequency k x)‖ := by
    have hh := congrArg norm hexpand
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg] using hh
  have h1 := halasz_complex_sum_power B P hr
  have hp := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) r) h1 (2*s)
  rw [mul_pow,← pow_mul,← pow_mul,hnorm] at hp
  have h2 := halasz_fiber_holder (univ : Finset (Fin r → Fin M))
    (halaszVinogradovFrequency k) V hs
  rw [halasz_frequency_energy] at h2
  simp only [card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,← pow_mul] at h2
  have hh := mul_le_mul_of_nonneg_left h2
    (pow_nonneg (Nat.cast_nonneg B.card) ((r-1)*(2*s)))
  have he : r*(2*s)=2*r*s := by ring
  rw [he] at hp
  have himage (d : DecidableEq (Fin k → ℤ)) :
      @Finset.image (Fin r → Fin M) (Fin k → ℤ) d (halaszVinogradovFrequency k) univ =
      @Finset.image (Fin r → Fin M) (Fin k → ℤ)
        (fun a b => Fintype.decidablePiFintype a b) (halaszVinogradovFrequency k) univ := by
    ext c
    simp only [mem_image]
  rw [himage] at hh
  exact hp.trans (by simpa only [V,mul_assoc] using hh)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszOverlapSynthesis
namespace OAI

/-! Finite synthesis bounded by the number of overlapping localization
windows, retaining the actual pair count. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate

lemma halasz_synthesis_pair_sum {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (a : ι → ℂ)
    (ha : ∀ i∈S, ‖a i‖≤1) :
    ‖∑ i∈S,a i • v i‖^2≤∑ i∈S,∑ j∈S,‖inner ℂ (v i) (v j)‖ := by
  calc
    _ = (inner ℂ (∑ i∈S,a i • v i) (∑ i∈S,a i • v i)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ ≤ ‖inner ℂ (∑ i∈S,a i • v i) (∑ i∈S,a i • v i)‖ := re_le_norm _
    _ = ‖∑ i∈S,∑ j∈S,conj (a i)*a j*inner ℂ (v i) (v j)‖ := by
      simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i∈S,∑ j∈S,‖conj (a i)*a j*inner ℂ (v i) (v j)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [norm_mul,norm_mul,norm_conj]
      have hmul : ‖a i‖*‖a j‖≤1 := by
        calc
          _ ≤ 1*1 := mul_le_mul (ha i hi) (ha j hj) (norm_nonneg _) zero_le_one
          _ = 1 := mul_one _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmul (norm_nonneg _)

theorem halasz_synthesis_overlap {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (a : ι → ℂ)
    (R : ι → ι → Prop) {V : ℝ} (ha : ∀ i∈S,‖a i‖≤1)
    (hR : ∀ i∈S,∀ j∈S,‖inner ℂ (v i) (v j)‖ ≤ (if R i j then V else 0)) :
    ‖∑ i∈S,a i • v i‖^2≤ V*(((S×ˢS).filter (fun p => R p.1 p.2)).card:ℝ) := by
  apply (halasz_synthesis_pair_sum S v a ha).trans
  calc
    _ ≤ ∑ i∈S,∑ j∈S,if R i j then V else 0 :=
      sum_le_sum (fun i hi => sum_le_sum (fun j hj => hR i hi j hj))
    _ = _ := by
      rw [← sum_product S S (fun p : ι×ι => if R p.1 p.2 then V else 0)]
      simp only [card_eq_sum_ones,Nat.cast_sum,sum_filter]
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      by_cases h : R p.1 p.2 <;> simp [h]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTorusTranslation
namespace OAI

/-! Translation of the localized Fourier kernel on the coefficient torus. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset
open scoped _root_.ComplexConjugate

lemma halasz_character_argument_add {k : ℕ} (m : Fin k → ℤ)
    (α β : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter m (α+β)=
      halaszVinogradovCharacter m α*halaszVinogradovCharacter m β := by
  simp only [halaszVinogradovCharacter,Pi.add_apply,fourier_apply,zsmul_add,
    AddCircle.toCircle_add,Circle.coe_mul,prod_mul_distrib]

lemma halasz_character_argument_neg {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter m (-α)=conj (halaszVinogradovCharacter m α) := by
  simp only [halaszVinogradovCharacter,Pi.neg_apply,fourier_apply,zsmul_neg,
    AddCircle.toCircle_neg,Circle.coe_inv_eq_conj,map_prod]

lemma halasz_torus_fourier_translation {k : ℕ}
    (g : (Fin k → AddCircle (1:ℝ)) → ℂ) (m : Fin k → ℤ)
    (β : Fin k → AddCircle (1:ℝ)) :
    (∫ α, conj (halaszVinogradovCharacter m α)*g (α+β) ∂halaszVinogradovHaar k) =
      halaszVinogradovCharacter m β*
        ∫ α, conj (halaszVinogradovCharacter m α)*g α ∂halaszVinogradovHaar k := by
  have : (halaszVinogradovHaar k).IsAddRightInvariant := by
    unfold halaszVinogradovHaar
    infer_instance
  rw [← integral_add_right_eq_self
    (fun α => conj (halaszVinogradovCharacter m α)*g (α+β)) (-β)]
  simp only [neg_add_cancel_right,halasz_character_argument_add,
    halasz_character_argument_neg,map_mul,Complex.conj_conj]
  simp_rw [show ∀ α, conj (halaszVinogradovCharacter m α)*
      halaszVinogradovCharacter m β*g α =
      halaszVinogradovCharacter m β*(conj (halaszVinogradovCharacter m α)*g α)
    from fun α => by ring]
  exact integral_const_mul _ _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTorusWindow
namespace OAI

/-! The product localization window and its exact volume on the finite
coefficient torus. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set _root_.Metric
open scoped _root_.Classical _root_.ComplexConjugate



lemma halasz_torus_window_product {k : ℕ} (δ : Fin k → ℝ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszTorusWindow δ α=∏ j,halaszCircleWindow (δ j) (α j) := by
  simp [halaszTorusWindow,halaszCircleWindow,Set.indicator,Finset.prod_boole]


lemma halasz_torus_window_norm_square {k : ℕ} (δ : Fin k → ℝ)
    (α : Fin k → AddCircle (1:ℝ)) :
    ‖halaszTorusWindow δ α‖^2=
      ∏ j,(closedBall (0:AddCircle (1:ℝ)) (δ j)).indicator (fun _ => (1:ℝ)) (α j) := by
  rw [halasz_torus_window_product,norm_prod,← Finset.prod_pow]
  apply prod_congr rfl
  intro j _
  by_cases h : α j∈closedBall (0:AddCircle (1:ℝ)) (δ j) <;>
    simp [halaszCircleWindow,h]

lemma halasz_torus_window_square_integral {k : ℕ} (δ : Fin k → ℝ)
    (hδ : ∀ j, 0≤δ j) (hδhalf : ∀ j,δ j≤1/2) :
    (∫ α, ‖halaszTorusWindow δ α‖^2 ∂halaszVinogradovHaar k)=∏ j,2*δ j := by
  simp_rw [halasz_torus_window_norm_square]
  unfold halaszVinogradovHaar
  rw [integral_fintype_prod_eq_prod]
  apply prod_congr rfl
  intro j _
  rw [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul,mul_one,
    halasz_circle_window_volume (hδ j) (hδhalf j)]

lemma halasz_torus_window_coefficient {k : ℕ} (δ : Fin k → ℝ) (m : Fin k → ℤ)
    (hδ : ∀ j,0≤δ j) (hδhalf : ∀ j,δ j≤1/2)
    (hphase : ∀ j,2*Real.pi*|(m j:ℝ)| * δ j≤1) :
    (∏ j,δ j)≤‖∫ α,conj (halaszVinogradovCharacter m α)*halaszTorusWindow δ α
      ∂halaszVinogradovHaar k‖ := by
  simp_rw [halasz_torus_window_product,halaszVinogradovCharacter,map_prod,← prod_mul_distrib]
  unfold halaszVinogradovHaar
  change (∏ j,δ j)≤‖∫ α,∏ j,(fun x : AddCircle (1:ℝ) =>
    conj (fourier (m j) x)*halaszCircleWindow (δ j) x) (α j)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)‖
  have hi := integral_fintype_prod_eq_prod
    (E := fun _ : Fin k => AddCircle (1:ℝ))
    (μ := fun _ : Fin k => AddCircle.haarAddCircle)
    (fun j x => conj (fourier (m j) x)*halaszCircleWindow (δ j) x)
  rw [hi,norm_prod]
  apply Finset.prod_le_prod (fun j _ => hδ j)
  intro j _
  exact halasz_circle_window_coefficient (hδ j) (hδhalf j) (hphase j)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowOverlap
namespace OAI

/-! Translated product windows only interact at nearby centers. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset _root_.Set _root_.Metric
open scoped _root_.Classical _root_.ComplexConjugate


lemma halasz_window_common_near {k : ℕ} (δ : Fin k → ℝ)
    (α β γ : Fin k → AddCircle (1:ℝ))
    (hβ : α+β∈Set.univ.pi (fun j => closedBall 0 (δ j)))
    (hγ : α+γ∈Set.univ.pi (fun j => closedBall 0 (δ j))) :
    HalaszWindowNear δ β γ := by
  intro j
  have hb : ‖α j+β j‖≤δ j := by
    simpa only [mem_closedBall,dist_zero_right,Pi.add_apply] using hβ j (mem_univ j)
  have hc : ‖α j+γ j‖≤δ j := by
    simpa only [mem_closedBall,dist_zero_right,Pi.add_apply] using hγ j (mem_univ j)
  calc
    _ = ‖(α j+β j)-(α j+γ j)‖ := by congr 1; abel
    _ ≤ ‖α j+β j‖+‖α j+γ j‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma halasz_window_product_bound {k : ℕ} (δ : Fin k → ℝ)
    (α β γ : Fin k → AddCircle (1:ℝ)) :
    ‖conj (halaszTorusWindow δ (α+β))*halaszTorusWindow δ (α+γ)‖≤
      if HalaszWindowNear δ β γ then ‖halaszTorusWindow δ (α+β)‖^2 else 0 := by
  by_cases hb : α+β∈Set.univ.pi (fun j => closedBall 0 (δ j))
  · by_cases hc : α+γ∈Set.univ.pi (fun j => closedBall 0 (δ j))
    · have hn := halasz_window_common_near δ α β γ hb hc
      simp [halaszTorusWindow,hb,hc,hn]
    · simp only [halaszTorusWindow,indicator_of_mem hb,indicator_of_notMem hc,
        mul_zero,norm_zero,norm_one,one_pow]
      split_ifs <;> norm_num
  · simp [halaszTorusWindow,hb]


lemma halasz_window_overlap_integral {k : ℕ} (δ : Fin k → ℝ)
    (hδ : ∀ j,0≤δ j) (hδhalf : ∀ j,δ j≤1/2)
    (β γ : Fin k → AddCircle (1:ℝ)) :
    ‖∫ α,conj (halaszTorusWindow δ (α+β))*halaszTorusWindow δ (α+γ)
      ∂halaszVinogradovHaar k‖≤
      if HalaszWindowNear δ β γ then ∏ j,2*δ j else 0 := by
  apply (norm_integral_le_integral_norm _).trans
  by_cases hn : HalaszWindowNear δ β γ
  · rw [if_pos hn]
    have hi := (halasz_window_translate_memLp δ β).norm.integrable_sq
    have hh := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      hi (Filter.Eventually.of_forall (fun α => by
        simpa only [if_pos hn] using halasz_window_product_bound δ α β γ))
    apply hh.trans_eq
    have : (halaszVinogradovHaar k).IsAddRightInvariant := by
      unfold halaszVinogradovHaar
      infer_instance
    rw [integral_add_right_eq_self (fun α => ‖halaszTorusWindow δ α‖^2) β,
      halasz_torus_window_square_integral δ hδ hδhalf]
  · rw [if_neg hn]
    have hz : ∀ α, ‖conj (halaszTorusWindow δ (α+β))*
        halaszTorusWindow δ (α+γ)‖=0 := by
      intro α
      have hh := halasz_window_product_bound δ α β γ
      rw [if_neg hn] at hh
      exact le_antisymm hh (norm_nonneg _)
    simp only [hz,integral_zero,le_refl]


lemma halasz_window_l2_coe {k : ℕ} (δ : Fin k → ℝ)
    (β : Fin k → AddCircle (1:ℝ)) :
    (halaszWindowL2 δ β : (Fin k → AddCircle (1:ℝ)) → ℂ) =ᵐ[halaszVinogradovHaar k]
      (fun α => halaszTorusWindow δ (α+β)) :=
  (halasz_window_translate_memLp δ β).coeFn_toLp

lemma halasz_window_l2_overlap {k : ℕ} (δ : Fin k → ℝ)
    (hδ : ∀ j,0≤δ j) (hδhalf : ∀ j,δ j≤1/2)
    (β γ : Fin k → AddCircle (1:ℝ)) :
    ‖inner ℂ (halaszWindowL2 δ β) (halaszWindowL2 δ γ)‖≤
      if HalaszWindowNear δ β γ then ∏ j,2*δ j else 0 := by
  rw [L2.inner_def]
  have he : (∫ α,inner ℂ (halaszWindowL2 δ β α) (halaszWindowL2 δ γ α)
      ∂halaszVinogradovHaar k)=
      ∫ α,conj (halaszTorusWindow δ (α+β))*halaszTorusWindow δ (α+γ)
        ∂halaszVinogradovHaar k := by
    apply integral_congr_ae
    filter_upwards [halasz_window_l2_coe δ β,halasz_window_l2_coe δ γ] with α hb hc
    rw [hb,hc]
    simp only [RCLike.inner_apply']
  rw [he]
  exact halasz_window_overlap_integral δ hδ hδhalf β γ

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszScaledFrequency
namespace OAI

/-! The symmetric character pairing in the double mean-value argument. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate


lemma halasz_scaled_character_symm {k : ℕ} (γ : Fin k → ℝ) (m n : Fin k → ℤ) :
    halaszVinogradovCharacter m (halaszScaledFrequency γ n)=
      halaszVinogradovCharacter n (halaszScaledFrequency γ m) := by
  unfold halaszVinogradovCharacter halaszScaledFrequency
  apply prod_congr rfl
  intro j _
  rw [fourier_coe_apply,fourier_coe_apply]
  congr 1
  push_cast
  ring


lemma halasz_scaled_norm_abs (γ d : ℝ) :
    ‖((|γ| * d:ℝ):AddCircle (1:ℝ))‖=‖((γ*d:ℝ):AddCircle (1:ℝ))‖ := by
  rcases le_total 0 γ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,neg_mul,AddCircle.coe_neg,norm_neg]

lemma halasz_scaled_near_abs {k : ℕ} (γ δ : Fin k → ℝ) (m n : Fin k → ℤ) :
    HalaszWindowNear δ (halaszScaledFrequency γ m) (halaszScaledFrequency γ n) ↔
      HalaszWindowNear δ (halaszScaledFrequency (fun j => |γ j|) m)
        (halaszScaledFrequency (fun j => |γ j|) n) := by
  unfold HalaszWindowNear halaszScaledFrequency
  simp only [← AddCircle.coe_sub,← mul_sub,halasz_scaled_norm_abs]

lemma halasz_weighted_character_power {k M : ℕ} (s : ℕ) (a : Fin M → ℂ)
    (α : Fin k → AddCircle (1:ℝ)) :
    (∑ b : Fin M,a b*halaszVinogradovCharacter
      (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)) α)^s=
      ∑ x : Fin s → Fin M,(∏ i,a (x i))*
        halaszVinogradovCharacter (halaszVinogradovFrequency k x) α := by
  rw [Fintype.sum_pow]
  apply sum_congr rfl
  intro x _
  rw [prod_mul_distrib,← halasz_vinogradov_character_sum]
  congr 2
  ext j
  simp [halaszVinogradovFrequency]

lemma halasz_scaled_power {k M : ℕ} (s : ℕ) (γ : Fin k → ℝ)
    (a : Fin M → ℂ) (m : Fin k → ℤ) :
    (∑ b : Fin M,a b*halaszVinogradovCharacter m
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ))))^s=
      ∑ x : Fin s → Fin M,(∏ i,a (x i))*
        halaszVinogradovCharacter m
          (halaszScaledFrequency γ (halaszVinogradovFrequency k x)) := by
  simp_rw [halasz_scaled_character_symm γ m]
  rw [halasz_weighted_character_power]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowSampling
namespace OAI

/-! A finite sampling inequality from the compact coefficient-torus window.
The right side counts actual nearby pairs of sampling centers. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate

lemma halasz_character_window_inner {k : ℕ} (δ : Fin k → ℝ)
    (m : Fin k → ℤ) (β : Fin k → AddCircle (1:ℝ)) :
    inner ℂ (halaszCharacterL2 m) (halaszWindowL2 δ β)=
      halaszVinogradovCharacter m β*
        ∫ α,conj (halaszVinogradovCharacter m α)*halaszTorusWindow δ α
          ∂halaszVinogradovHaar k := by
  rw [L2.inner_def]
  have he : (∫ α,inner ℂ (halaszCharacterL2 m α) (halaszWindowL2 δ β α)
      ∂halaszVinogradovHaar k)=
      ∫ α,conj (halaszVinogradovCharacter m α)*halaszTorusWindow δ (α+β)
        ∂halaszVinogradovHaar k := by
    apply integral_congr_ae
    filter_upwards [halasz_character_l2_coe m,halasz_window_l2_coe δ β] with α hm hb
    rw [hm,hb]
    simp only [RCLike.inner_apply']
  rw [he,halasz_torus_fourier_translation]

/-- Finite Fourier sampling costs only the volume of the window times the
number of pairs of centers whose translated windows can meet. -/
theorem halasz_window_sampling {ι : Type*} {k : ℕ}
    (B : Finset ι) (S : Finset (Fin k → ℤ))
    (β : ι → Fin k → AddCircle (1:ℝ)) (a : ι → ℂ) (δ : Fin k → ℝ)
    (ha : ∀ b∈B,‖a b‖≤1) (hδ : ∀ j,0≤δ j) (hδhalf : ∀ j,δ j≤1/2)
    (hphase : ∀ m∈S,∀ j,2*Real.pi*|(m j:ℝ)| * δ j≤1) :
    (∏ j,δ j)^2*(∑ m∈S,‖∑ b∈B,a b*halaszVinogradovCharacter m (β b)‖^2)≤
      (∏ j,2*δ j)*
        (((B×ˢB).filter (fun p => HalaszWindowNear δ (β p.1) (β p.2))).card:ℝ) := by
  let u := ∑ b∈B,a b • halaszWindowL2 δ (β b)
  have he (m : Fin k → ℤ) : inner ℂ (halaszCharacterL2 m) u=
      (∫ α,conj (halaszVinogradovCharacter m α)*halaszTorusWindow δ α
        ∂halaszVinogradovHaar k)*
      (∑ b∈B,a b*halaszVinogradovCharacter m (β b)) := by
    simp only [u,inner_sum,inner_smul_right,halasz_character_window_inner,mul_sum]
    apply sum_congr rfl
    intro b _
    ring
  have hb := mrt_gram_analysis S halaszCharacterL2 u (B := 1) (by norm_num)
    (fun m hm => by
      simp only [halasz_character_l2_inner,apply_ite norm,norm_one,norm_zero]
      simp [hm])
  have hs := halasz_synthesis_overlap B (fun b => halaszWindowL2 δ (β b)) a
    (fun b c => HalaszWindowNear δ (β b) (β c)) ha
    (fun b _ c _ => halasz_window_l2_overlap δ hδ hδhalf (β b) (β c))
  apply le_trans _ (hb.trans (by simpa only [one_mul] using hs))
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  rw [he,norm_mul,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (prod_nonneg (fun j _ => hδ j))
    (halasz_torus_window_coefficient δ m hδ hδhalf (hphase m hm)) 2

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszIntegerWindow
namespace OAI

/-! Counting lattice points near integers, with all interval endpoints real. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_integer_interval_card (S : Finset ℤ) {a b : ℝ} (hab : a≤ b)
    (hS : ∀ d∈S,a≤(d:ℝ) ∧ (d:ℝ)≤ b) : (S.card:ℝ)≤ b-a+1 := by
  have hcf : ⌈a⌉≤⌊b⌋+1 := by
    apply Int.ceil_le.mpr
    push_cast
    exact hab.trans (Int.lt_floor_add_one b).le
  have hsub : S⊆Icc ⌈a⌉ ⌊b⌋ := by
    intro d hd
    exact mem_Icc.mpr ⟨Int.ceil_le.mpr (hS d hd).1,Int.le_floor.mpr (hS d hd).2⟩
  have hcard : ((Icc ⌈a⌉ ⌊b⌋).card:ℝ)=(⌊b⌋:ℝ)+1-(⌈a⌉:ℝ) := by
    exact_mod_cast Int.card_Icc_of_le ⌈a⌉ ⌊b⌋ hcf
  have hh : (S.card:ℝ)≤((Icc ⌈a⌉ ⌊b⌋).card:ℝ) := by
    exact_mod_cast card_le_card hsub
  rw [hcard] at hh
  linarith [Int.floor_le b,Int.le_ceil a]

/-- A finite set of integers lying in [-K,K] whose multiples by γ are close
to integers. This is the lattice count used by the double mean-value method. -/
theorem halasz_integer_window_card (S : Finset ℤ) {K γ δ : ℝ}
    (hK : 0≤ K) (hγ : 0<γ) (hδ : 0≤δ) (hδhalf : δ≤1/2)
    (hS : ∀ d∈S, |(d:ℝ)|≤ K ∧ ‖((γ*(d:ℝ):ℝ):AddCircle (1:ℝ))‖≤δ) :
    (S.card:ℝ)≤4*K*δ+2*K*γ+4*δ/γ+2 := by
  let f : ℤ → ℤ := fun d => round (γ*(d:ℝ))
  have hnear (d : ℤ) (hd : d∈S) : |γ*(d:ℝ)-(f d:ℝ)|≤δ := by
    simpa only [AddCircle.norm_eq,inv_one,one_mul,mul_one,f] using (hS d hd).2
  have himage : ∀ j∈S.image f, -K*γ-δ≤(j:ℝ) ∧ (j:ℝ)≤ K*γ+δ := by
    intro j hj
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
    have hdK := abs_le.mp (hS d hd).1
    have hnd := abs_le.mp (hnear d hd)
    constructor <;> nlinarith
  have hjcard := halasz_integer_interval_card (S.image f)
    (show -K*γ-δ≤ K*γ+δ by nlinarith [mul_nonneg hK hγ.le]) himage
  have hfcard (j : ℤ) : ((S.filter (fun d => f d=j)).card:ℝ)≤2*δ/γ+1 := by
    have hh := halasz_integer_interval_card (S.filter (fun d => f d=j))
      (show ((j:ℝ)-δ)/γ≤((j:ℝ)+δ)/γ from
        (div_le_div_iff_of_pos_right hγ).mpr (by linarith)) (by
          intro d hd
          obtain ⟨hd,hf⟩ := mem_filter.mp hd
          have hn := abs_le.mp (hnear d hd)
          rw [hf] at hn
          constructor
          · apply (div_le_iff₀ hγ).mpr
            nlinarith [hn.2]
          · apply (le_div_iff₀ hγ).mpr
            nlinarith [hn.1])
    convert (preTransparency := .instances) hh using 1; ring
  have hsum : (S.card:ℝ)=∑ j∈S.image f,((S.filter (fun d => f d=j)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image f S
  calc
    _ = _ := hsum
    _ ≤ ∑ _j∈S.image f,(2*δ/γ+1) := sum_le_sum (fun j _ => hfcard j)
    _ = ((S.image f).card:ℝ)*(2*δ/γ+1) := by simp; ring
    _ ≤ (2*K*γ+2*δ+1)*(2*δ/γ+1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := by
      have hδ2 : 4*δ^2≤2*δ := by nlinarith
      have hγ0 : γ≠0 := ne_of_gt hγ
      apply (le_of_sub_nonneg ?_)
      field_simp
      nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowPairCount
namespace OAI

/-! Nearby pairs of moment frequencies are controlled by the zero moment
and a product of one-dimensional near-integer counts. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_integer_window_size (L : ℕ) {γ δ : ℝ}
    (hγ : 0<γ) (hδ : 0≤δ) (hδhalf : δ≤1/2) :
    ((halaszIntegerWindow L γ δ).card:ℝ)≤4*(L:ℝ)*δ+2*L*γ+4*δ/γ+2 := by
  apply halasz_integer_window_card _ (Nat.cast_nonneg _) hγ hδ hδhalf
  intro d hd
  obtain ⟨hd,hn⟩ := mem_filter.mp hd
  refine ⟨?_,hn⟩
  obtain ⟨hl,hu⟩ := mem_Icc.mp hd
  exact_mod_cast abs_le.mpr ⟨hl,hu⟩

lemma halasz_integer_window_trivial (L : ℕ) (γ δ : ℝ) :
    ((halaszIntegerWindow L γ δ).card:ℝ)≤2*(L:ℝ)+1 := by
  have h := card_filter_le (Icc (-(L:ℤ)) L)
    (fun d => ‖((γ*(d:ℝ):ℝ):AddCircle (1:ℝ))‖≤δ)
  have he : ((Icc (-(L:ℤ)) (L:ℤ)).card:ℤ)=2*(L:ℤ)+1 := by
    rw [Int.card_Icc_of_le]
    · ring
    · omega
  have heR : ((Icc (-(L:ℤ)) (L:ℤ)).card:ℝ)=2*(L:ℝ)+1 := by exact_mod_cast he
  change ((halaszIntegerWindow L γ δ).card:ℝ)≤_
  rw [← heR]
  exact_mod_cast h

theorem halasz_near_pair_count {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (L : Fin k → ℕ) (γ δ : Fin k → ℝ)
    (hγ : ∀ j,0<γ j) (hδ : ∀ j,0≤δ j) (hδquarter : ∀ j,δ j≤1/4)
    (hdiff : ∀ x y j, |f x j-f y j|≤(L j:ℤ)) :
    ((univ.filter (fun xy : ι×ι => HalaszWindowNear δ
      (halaszScaledFrequency γ (f xy.1)) (halaszScaledFrequency γ (f xy.2)))).card:ℝ)≤
      (halaszRepresentationCount f 0:ℝ)*
        ∏ j,min (2*(L j:ℝ)+1) (8*(L j:ℝ)*δ j+2*L j*γ j+8*δ j/γ j+2) := by
  let W := Fintype.piFinset (fun j => halaszIntegerWindow (L j) (γ j) (2*δ j))
  have hsub : univ.filter (fun xy : ι×ι => HalaszWindowNear δ
      (halaszScaledFrequency γ (f xy.1)) (halaszScaledFrequency γ (f xy.2))) ⊆
      univ.filter (fun xy : ι×ι => f xy.1-f xy.2∈W) := by
    intro xy hxy
    have hn := (mem_filter.mp hxy).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,Fintype.mem_piFinset.mpr ?_⟩
    intro j
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr (abs_le.mp (hdiff xy.1 xy.2 j)),?_⟩
    have hh := hn j
    simpa only [halaszScaledFrequency,Pi.sub_apply,← AddCircle.coe_sub,
      ← mul_sub,← Int.cast_sub] using hh
  have hcount := (card_le_card hsub).trans (halasz_difference_set_count f W)
  have hW : (W.card:ℝ)≤∏ j,min (2*(L j:ℝ)+1) (8*(L j:ℝ)*δ j+2*L j*γ j+8*δ j/γ j+2) := by
    simp only [W,Fintype.card_piFinset,Nat.cast_prod]
    apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    intro j _
    have hh := halasz_integer_window_size (L j) (hγ j)
      (show 0≤2*δ j from mul_nonneg (by norm_num) (hδ j)) (show 2*δ j≤1/2 by linarith [hδquarter j])
    apply le_min (halasz_integer_window_trivial (L j) (γ j) (2*δ j))
    convert (preTransparency := .instances) hh using 1; ring
  calc
    _ ≤ (W.card:ℝ)*(halaszRepresentationCount f 0:ℝ) := by exact_mod_cast hcount
    _ ≤ (∏ j,min (2*(L j:ℝ)+1) (8*(L j:ℝ)*δ j+2*L j*γ j+8*δ j/γ j+2))*
        (halaszRepresentationCount f 0:ℝ) :=
      mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

/-- The lattice count depends only on the absolute coefficient; alternating
Taylor signs therefore incur no additional factor. -/
theorem halasz_near_pair_count_abs {ι : Type*} [Fintype ι] {k : ℕ}
    (f : ι → Fin k → ℤ) (L : Fin k → ℕ) (γ δ : Fin k → ℝ)
    (hγ : ∀ j,γ j≠0) (hδ : ∀ j,0≤δ j) (hδquarter : ∀ j,δ j≤1/4)
    (hdiff : ∀ x y j, |f x j-f y j|≤(L j:ℤ)) :
    ((univ.filter (fun xy : ι×ι => HalaszWindowNear δ
      (halaszScaledFrequency γ (f xy.1)) (halaszScaledFrequency γ (f xy.2)))).card:ℝ)≤
      (halaszRepresentationCount f 0:ℝ)*
        ∏ j,min (2*(L j:ℝ)+1)
          (8*(L j:ℝ)*δ j+2*L j* |γ j| +8*δ j/ |γ j| +2) := by
  have he : (univ.filter (fun xy : ι×ι => HalaszWindowNear δ
      (halaszScaledFrequency γ (f xy.1)) (halaszScaledFrequency γ (f xy.2)))) =
      univ.filter (fun xy : ι×ι => HalaszWindowNear δ
        (halaszScaledFrequency (fun j => |γ j|) (f xy.1))
        (halaszScaledFrequency (fun j => |γ j|) (f xy.2))) := by
    ext xy
    simp only [mem_filter,halasz_scaled_near_abs γ δ]
  rw [he]
  exact halasz_near_pair_count f L (fun j => |γ j|) δ
    (fun j => abs_pos.mpr (hγ j)) hδ hδquarter hdiff

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentSampling
namespace OAI

/-! Fourier sampling of the second complete-system moment. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem halasz_moment_sampling {k M : ℕ} (s : ℕ) (S : Finset (Fin k → ℤ))
    (a : Fin M → ℂ) (γ δ : Fin k → ℝ) (ha : ∀ b,‖a b‖≤1)
    (hγ : ∀ j,γ j≠0) (hδ : ∀ j,0≤δ j) (hδquarter : ∀ j,δ j≤1/4)
    (hphase : ∀ m∈S,∀ j,2*Real.pi*|(m j:ℝ)| * δ j≤1) :
    (∏ j,δ j)^2*(∑ m∈S,
      ‖∑ b : Fin M,a b*halaszVinogradovCharacter m
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*s))≤
      (∏ j,2*δ j)*(halaszVinogradovCount s k M:ℝ)*
        ∏ j,min (2*((s*M^(j.val+1):ℕ):ℝ)+1)
          (8*((s*M^(j.val+1):ℕ):ℝ)*δ j+2*((s*M^(j.val+1):ℕ):ℝ)* |γ j| +
            8*δ j/ |γ j| +2) := by
  let F : (Fin s → Fin M) → Fin k → ℤ := halaszVinogradovFrequency k
  let A : (Fin s → Fin M) → ℂ := fun x => ∏ i,a (x i)
  let β : (Fin s → Fin M) → Fin k → AddCircle (1:ℝ) :=
    fun x => halaszScaledFrequency γ (F x)
  have hA (x : Fin s → Fin M) : ‖A x‖≤1 := by
    change ‖∏ i,a (x i)‖≤1
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin s,(1:ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => ha _)
      _ = 1 := by simp
  have hh := halasz_window_sampling (univ : Finset (Fin s → Fin M)) S β A δ
    (fun x _ => hA x) hδ (fun j => (hδquarter j).trans (by norm_num)) hphase
  have hc := halasz_near_pair_count_abs F (fun j => s*M^(j.val+1)) γ δ hγ hδ hδquarter
    (fun x y j => halasz_vinogradov_difference_abs x y j)
  rw [← halasz_fiber_energy_representation,halasz_frequency_energy] at hc
  have hV : 0≤∏ j,2*δ j := prod_nonneg (fun j _ =>
    mul_nonneg (by norm_num) (hδ j))
  have hp := mul_le_mul_of_nonneg_left hc hV
  simp only [univ_product_univ] at hh
  have hs := hh.trans hp
  have he (m : Fin k → ℤ) :
      ‖∑ x : Fin s → Fin M,A x*halaszVinogradovCharacter m (β x)‖^2=
      ‖∑ b : Fin M,a b*halaszVinogradovCharacter m
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*s) := by
    rw [show (∑ x : Fin s → Fin M,A x*halaszVinogradovCharacter m (β x))=
      (∑ b : Fin M,a b*halaszVinogradovCharacter m
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ))))^s from
      (halasz_scaled_power s γ a m).symm]
    rw [norm_pow,← pow_mul,Nat.mul_comm s 2]
  simpa only [he,mul_assoc] using hs

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleMeanValue
namespace OAI

/-! The double mean-value bound with two complete Vinogradov systems.
The explicit coordinate minimum is retained for logarithmic Taylor phases. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem halasz_double_mean_value (k M₁ M₂ r s : ℕ) (hr : 1≤ r) (hs : 1≤ s)
    (γ δ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) (hδ : ∀ j,0≤δ j)
    (hδquarter : ∀ j,δ j≤1/4)
    (hphase : ∀ j,2*Real.pi*((r*M₁^(j.val+1):ℕ):ℝ)*δ j≤1) :
    (∏ j,δ j)^2*
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s) ≤
      (M₂:ℝ)^((r-1)*(2*s))*(M₁:ℝ)^(r*(2*s-2))*
        (halaszVinogradovCount r k M₁:ℝ)*(∏ j,2*δ j)*
          (halaszVinogradovCount s k M₂:ℝ)*
            ∏ j,min (2*((s*M₂^(j.val+1):ℕ):ℝ)+1)
              (8*((s*M₂^(j.val+1):ℕ):ℝ)*δ j+
                2*((s*M₂^(j.val+1):ℕ):ℝ)* |γ j| +8*δ j/ |γ j| +2) := by
  let α : Fin M₂ → Fin k → AddCircle (1:ℝ) := fun b =>
    halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ))
  let S := (univ : Finset (Fin r → Fin M₁)).image (halaszVinogradovFrequency k)
  obtain ⟨ε,hε,hd⟩ := halasz_double_holder (univ : Finset (Fin M₂)) k M₁ r s hr hs α
  have hm := halasz_moment_sampling s S ε γ δ (fun b => (hε b).le) hγ hδ hδquarter (by
    intro m hm j
    obtain ⟨x,_,rfl⟩ := mem_image.mp hm
    have hx : |(halaszVinogradovFrequency k x j:ℝ)|≤((r*M₁^(j.val+1):ℕ):ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast halasz_vinogradov_frequency_nonneg x j)]
      exact_mod_cast halasz_vinogradov_frequency_le x j
    have hpi : 0≤2*Real.pi*δ j := mul_nonneg (by positivity) (hδ j)
    nlinarith [mul_le_mul_of_nonneg_left hx hpi,hphase j])
  let C := (M₂:ℝ)^((r-1)*(2*s))*(M₁:ℝ)^(r*(2*s-2))*
    (halaszVinogradovCount r k M₁:ℝ)
  have hC : 0≤ C := by dsimp only [C]; positivity
  have hd' :
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁ (α b)‖^(2*r*s)≤
        C*∑ m∈S,‖∑ b : Fin M₂,ε b*halaszVinogradovCharacter m (α b)‖^(2*s) := by
    simpa only [card_univ,Fintype.card_fin,C,S] using hd
  calc
    _ ≤ (∏ j,δ j)^2*(C*∑ m∈S,
          ‖∑ b : Fin M₂,ε b*halaszVinogradovCharacter m (α b)‖^(2*s)) :=
      mul_le_mul_of_nonneg_left hd' (sq_nonneg _)
    _ = C*((∏ j,δ j)^2*∑ m∈S,
          ‖∑ b : Fin M₂,ε b*halaszVinogradovCharacter m (α b)‖^(2*s)) := by ring
    _ ≤ C*((∏ j,2*δ j)*(halaszVinogradovCount s k M₂:ℝ)*
          ∏ j,min (2*((s*M₂^(j.val+1):ℕ):ℝ)+1)
            (8*((s*M₂^(j.val+1):ℕ):ℝ)*δ j+
              2*((s*M₂^(j.val+1):ℕ):ℝ)* |γ j| +8*δ j/ |γ j| +2)) :=
      mul_le_mul_of_nonneg_left hm hC
    _ = _ := by dsimp only [C]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleWindow
namespace OAI

/-! The coefficient window used in the double mean-value specialization. -/
namespace TwoPointCorrelations

open _root_.Finset


lemma halasz_double_window_pos {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M) (j : Fin k) :
    0< halaszDoubleWindow r M j := by
  have hrR : 0<(r:ℝ) := by exact_mod_cast (show 0< r by omega)
  have hMR : 0<(M:ℝ) := by exact_mod_cast (show 0< M by omega)
  unfold halaszDoubleWindow
  positivity

lemma halasz_double_window_small {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M) (j : Fin k) :
    halaszDoubleWindow r M j≤1/4 := by
  have hrR : 1≤(r:ℝ) := by exact_mod_cast hr
  have hMR : 1≤(M:ℝ) := by exact_mod_cast hM
  have hp : 1≤(M:ℝ)^(j.val+1) := one_le_pow₀ hMR
  have hd : 16≤16*(r:ℝ)*(M:ℝ)^(j.val+1) := by nlinarith
  unfold halaszDoubleWindow
  apply (div_le_iff₀ (by linarith : 0<16*(r:ℝ)*(M:ℝ)^(j.val+1))).mpr
  linarith

lemma halasz_double_window_phase {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M) (j : Fin k) :
    2*Real.pi*((r*M^(j.val+1):ℕ):ℝ)*halaszDoubleWindow r M j≤1 := by
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have hM0 : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have he : 2*Real.pi*((r*M^(j.val+1):ℕ):ℝ)*halaszDoubleWindow r M j=Real.pi/8 := by
    unfold halaszDoubleWindow
    push_cast
    field_simp [hr0,hM0]
    ring
  rw [he]
  linarith [Real.pi_lt_four]

lemma halasz_double_window_product {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M) :
    (∏ j : Fin k,halaszDoubleWindow r M j)*
      ((16*(r:ℝ))^k*(M:ℝ)^(∑ j : Fin k, (j.val+1)))=1 := by
  have hr0 : (r:ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have hM0 : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have he (j : Fin k) : halaszDoubleWindow r M j*(16*(r:ℝ)*(M:ℝ)^(j.val+1))=1 := by
    unfold halaszDoubleWindow
    exact one_div_mul_cancel (mul_ne_zero (mul_ne_zero (by norm_num) hr0) (pow_ne_zero _ hM0))
  calc
    _ = (∏ j : Fin k,halaszDoubleWindow r M j)*
        (∏ j : Fin k,16*(r:ℝ)*(M:ℝ)^(j.val+1)) := by
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,prod_pow_eq_pow_sum]
    _ = ∏ j : Fin k,halaszDoubleWindow r M j*(16*(r:ℝ)*(M:ℝ)^(j.val+1)) :=
      (prod_mul_distrib).symm
    _ = 1 := by simp only [he,prod_const_one]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleSpecialization
namespace OAI

/-! Removing the localization volume from the double mean-value estimate. -/
namespace TwoPointCorrelations

open _root_.Finset


theorem halasz_double_specialized (k M₁ M₂ r s : ℕ) (hr : 1≤ r) (hs : 1≤ s)
    (hM₁ : 1≤ M₁) (γ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) :
    ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s) ≤
      (32*(r:ℝ))^k*(M₁:ℝ)^(∑ j : Fin k, (j.val+1))*
        (M₂:ℝ)^((r-1)*(2*s))*(M₁:ℝ)^(r*(2*s-2))*
          (halaszVinogradovCount r k M₁:ℝ)*(halaszVinogradovCount s k M₂:ℝ)*
            ∏ j,halaszDoubleWeight r s M₁ M₂ γ j := by
  let δ : Fin k → ℝ := halaszDoubleWindow r M₁
  let P := ∏ j,δ j
  let Q := (16*(r:ℝ))^k*(M₁:ℝ)^(∑ j : Fin k, (j.val+1))
  let C := (M₂:ℝ)^((r-1)*(2*s))*(M₁:ℝ)^(r*(2*s-2))*
    (halaszVinogradovCount r k M₁:ℝ)
  let U := (halaszVinogradovCount s k M₂:ℝ)*∏ j,halaszDoubleWeight r s M₁ M₂ γ j
  have hP : 0< P := prod_pos (fun j _ => halasz_double_window_pos hr hM₁ j)
  have hPQ : P*Q=1 := halasz_double_window_product hr hM₁
  have hQ : 0≤ Q := by
    dsimp only [Q]
    positivity
  have htwo : (∏ j : Fin k,2*δ j)=(2:ℝ)^k*P := by
    rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
  have hd := halasz_double_mean_value k M₁ M₂ r s hr hs γ δ hγ
    (fun j => (halasz_double_window_pos hr hM₁ j).le)
    (fun j => halasz_double_window_small hr hM₁ j)
    (fun j => halasz_double_window_phase hr hM₁ j)
  have hscaled : P^2*
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s) ≤
      C*((2:ℝ)^k*P)*U := by
    convert (preTransparency := .instances) hd using 1
    dsimp only [C,U,halaszDoubleWeight]
    rw [htwo]
    ring
  have hcancel : P*
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s) ≤
      C*(2:ℝ)^k*U := by
    apply (mul_le_mul_iff_right₀ hP).mp
    convert (preTransparency := .instances) hscaled using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hcancel hQ
  have hpw : (16*(r:ℝ))^k*(2:ℝ)^k=(32*(r:ℝ))^k := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = Q*(P*‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s)) := by
      rw [← mul_assoc,mul_comm Q P,hPQ,one_mul]
    _ ≤ Q*(C*(2:ℝ)^k*U) := hmul
    _ = ((16*(r:ℝ))^k*(2:ℝ)^k)*(M₁:ℝ)^(∑ j : Fin k, (j.val+1))*C*U := by
      dsimp only [Q]
      ring
    _ = _ := by rw [hpw]; dsimp only [C,U]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWeightNormalization
namespace OAI

/-! Normalized coordinate weights when both short variables have the same
length. The three terms exhibit the triangular saving in the degree. -/
namespace TwoPointCorrelations


lemma halasz_weight_normalized {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M)
    (γ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) (j : Fin k) :
    halaszDoubleWeight r r M M γ j≤
      (M:ℝ)^(j.val+1)*halaszNormalizedWeight r M γ j := by
  let m : ℝ := (M:ℝ)^(j.val+1)
  let g := |γ j|
  have hrR : 0<(r:ℝ) := by exact_mod_cast (show 0< r by omega)
  have hMR : 1≤(M:ℝ) := by exact_mod_cast hM
  have hm : 1≤ m := one_le_pow₀ hMR
  have hm0 : 0< m := by linarith
  have hg : 0< g := abs_pos.mpr (hγ j)
  have htriv : 2*(r:ℝ)*m+1≤ m*(2*r+1) := by nlinarith
  have he : 8*(r:ℝ)*m*(1/(16*r*m))+2*r*m*g+8*(1/(16*r*m))/g+2=
      m*((5/2:ℝ)/m+2*r*g+1/(2*r*m^2*g)) := by
    field_simp
    ring
  unfold halaszDoubleWeight halaszDoubleWindow halaszNormalizedWeight
  push_cast
  change min (2*((r:ℝ)*m)+1)
      (8*((r:ℝ)*m)*(1/(16*r*m))+2*((r:ℝ)*m)*g+8*(1/(16*r*m))/g+2)≤
    m*min (2*(r:ℝ)+1) ((5/2:ℝ)/m+2*r*g+1/(2*r*m^2*g))
  rw [show 8*((r:ℝ)*m)*(1/(16*r*m))+2*((r:ℝ)*m)*g+8*(1/(16*r*m))/g+2=
      8*(r:ℝ)*m*(1/(16*r*m))+2*r*m*g+8*(1/(16*r*m))/g+2 by ring,he,
    mul_min_of_nonneg _ _ hm0.le]
  apply min_le_min _ le_rfl
  simpa only [mul_assoc] using htriv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNormalizedDoubleMoment
namespace OAI

/-! Cancellation of the two complete-system degree costs against the
coordinate volumes in the double moment. -/
namespace TwoPointCorrelations

open _root_.Finset



lemma halasz_normalized_weight_nonneg {k r M : ℕ} (γ : Fin k → ℝ) (j : Fin k) :
    0≤ halaszNormalizedWeight r M γ j := by
  unfold halaszNormalizedWeight
  positivity

lemma halasz_double_weight_nonneg {k r s M₁ M₂ : ℕ} (γ : Fin k → ℝ) (j : Fin k) :
    0≤ halaszDoubleWeight r s M₁ M₂ γ j := by
  unfold halaszDoubleWeight halaszDoubleWindow
  positivity

theorem halasz_normalized_double_moment {k r M : ℕ} (hr : 1≤ r) (hM : 1≤ M)
    (γ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) {C ε : ℝ}
    (hJ : (halaszVinogradovCount r k M:ℝ)≤
      C*(M:ℝ)^(2*(r:ℝ)-((∑ j : Fin k,(j.val+1):ℕ):ℝ)+ε)) :
    ‖∑ b : Fin M,halaszVinogradovPolynomial k M
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*r) ≤
      (32*(r:ℝ))^k*C^2*(M:ℝ)^(4*(r:ℝ)^2+2*ε)*
        ∏ j,halaszNormalizedWeight r M γ j := by
  let K := ∑ j : Fin k,(j.val+1)
  let e : ℝ := 2*(r:ℝ)-(K:ℝ)+ε
  let W := ∏ j,halaszNormalizedWeight r M γ j
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (show 0< M by omega)
  have hW0 : 0≤ W := prod_nonneg (fun j _ => halasz_normalized_weight_nonneg γ j)
  have hweights : (∏ j,halaszDoubleWeight r r M M γ j)≤(M:ℝ)^K*W := by
    calc
      _ ≤ ∏ j : Fin k,(M:ℝ)^(j.val+1)*halaszNormalizedWeight r M γ j :=
        Finset.prod_le_prod (fun j _ => halasz_double_weight_nonneg γ j)
          (fun j _ => halasz_weight_normalized hr hM γ hγ j)
      _ = _ := by rw [prod_mul_distrib,prod_pow_eq_pow_sum]
  have hJ2 : (halaszVinogradovCount r k M:ℝ)^2≤(C*(M:ℝ)^e)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 2
  have hbase := halasz_double_specialized k M M r r hr hr hM γ hγ
  have hbound :
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*r) ≤
      (32*(r:ℝ))^k*(M:ℝ)^K*(M:ℝ)^((r-1)*(2*r))*(M:ℝ)^(r*(2*r-2))*
        (C*(M:ℝ)^e)^2*((M:ℝ)^K*W) := by
    apply hbase.trans
    calc
      _ = (32*(r:ℝ))^k*(M:ℝ)^K*(M:ℝ)^((r-1)*(2*r))*(M:ℝ)^(r*(2*r-2))*
          (halaszVinogradovCount r k M:ℝ)^2*(∏ j,halaszDoubleWeight r r M M γ j) := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left hJ2 (by positivity)) hweights
        (prod_nonneg (fun j _ => halasz_double_weight_nonneg γ j)) (by positivity)
  apply hbound.trans_eq
  have hr2 : 2≤2*r := by omega
  have hexp : (K:ℝ)+(((r-1)*(2*r):ℕ):ℝ)+((r*(2*r-2):ℕ):ℝ)+2*e+(K:ℝ)=
      4*(r:ℝ)^2+2*ε := by
    dsimp only [e]
    push_cast [Nat.cast_sub hr,Nat.cast_sub hr2]
    ring
  calc
    _ = (32*(r:ℝ))^k*C^2*
        ((M:ℝ)^K*(M:ℝ)^((r-1)*(2*r))*(M:ℝ)^(r*(2*r-2))*
          ((M:ℝ)^e)^2*(M:ℝ)^K)*W := by ring
    _ = (32*(r:ℝ))^k*C^2*(M:ℝ)^(4*(r:ℝ)^2+2*ε)*W := by
      rw [← Real.rpow_natCast (M:ℝ) K,← Real.rpow_natCast (M:ℝ) ((r-1)*(2*r)),
        ← Real.rpow_natCast (M:ℝ) (r*(2*r-2)),
        ← Real.rpow_natCast ((M:ℝ)^e) 2,← Real.rpow_mul hM0.le]
      rw [← Real.rpow_add hM0,← Real.rpow_add hM0,← Real.rpow_add hM0,
        ← Real.rpow_add hM0]
      norm_num only [Nat.cast_ofNat]
      rw [show (K:ℝ)+(((r-1)*(2*r):ℕ):ℝ)+((r*(2*r-2):ℕ):ℝ)+e*2+(K:ℝ)=
        4*(r:ℝ)^2+2*ε by nlinarith only [hexp]]

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_normalized_double_moment := @OAI.TwoPointCorrelations.halasz_normalized_double_moment
