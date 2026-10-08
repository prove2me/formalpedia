-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_classical_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:53:21.350833+00:00
-- url     : https://prove2.me/submissions/c3a18ee5-9295-4274-9c10-ec62e17fd60b

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_residue_good_moment

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





lemma halasz_vinogradov_count_lower (s k N : ℕ) : N^s ≤ halaszVinogradovCount s k N := by
  classical
  have hx (x : Fin s → Fin N) : 1 ≤ (halaszVinogradovFiber x k).card := by
    apply card_pos.mpr
    refine ⟨x,?_⟩
    simp [halaszVinogradovFiber]
  unfold halaszVinogradovCount
  calc
    _ = ∑ _x : Fin s → Fin N, 1 := by simp
    _ ≤ _ := sum_le_sum (fun x _ => hx x)


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

lemma halasz_vinogradov_frequency_eq {s k N : ℕ} (x y : Fin s → Fin N) :
    halaszVinogradovFrequency k x = halaszVinogradovFrequency k y ↔
      y ∈ halaszVinogradovFiber x k := by
  classical
  constructor
  · intro h
    apply mem_halaszVinogradovFiber.mpr
    intro j hj
    have hj1 := (mem_Icc.mp hj).1
    have hjk := (mem_Icc.mp hj).2
    have hq := congrFun h (⟨j-1,by omega⟩ : Fin k)
    simp only [halaszVinogradovFrequency,Nat.sub_add_cancel hj1] at hq
    exact_mod_cast hq
  · intro h
    funext j
    have hj : j.val+1 ∈ Icc 1 k := mem_Icc.mpr ⟨by omega,by omega⟩
    have hq := (mem_halaszVinogradovFiber.mp h) (j.val+1) hj
    dsimp only [halaszVinogradovFrequency]
    exact_mod_cast hq

theorem halasz_vinogradov_moment (s k N : ℕ) :
    (∫ α, (halaszVinogradovPolynomial k N α)^s *
        conj ((halaszVinogradovPolynomial k N α)^s) ∂halaszVinogradovHaar k) =
      (halaszVinogradovCount s k N:ℂ) := by
  classical
  have hi (x y : Fin s → Fin N) :
      Integrable (fun α => halaszVinogradovCharacter (halaszVinogradovFrequency k x) α *
        conj (halaszVinogradovCharacter (halaszVinogradovFrequency k y) α))
        (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  simp_rw [halasz_vinogradov_power_expand,map_sum,sum_mul,mul_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  simp_rw [integral_finsetSum _ (fun y _ => hi _ y),halasz_vinogradov_character_inner,
    halasz_vinogradov_frequency_eq]
  simp only [sum_boole,filter_mem_eq_inter,univ_inter,halaszVinogradovCount,Nat.cast_sum]

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



theorem halasz_vinogradov_real_moment (s k N : ℕ) :
    (∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*s) ∂halaszVinogradovHaar k) =
      (halaszVinogradovCount s k N:ℝ) := by
  have hp (α : Fin k → AddCircle (1:ℝ)) :
      ((‖halaszVinogradovPolynomial k N α‖^(2*s):ℝ):ℂ) =
      (halaszVinogradovPolynomial k N α)^s *
        conj ((halaszVinogradovPolynomial k N α)^s) := by
    simpa only [norm_pow,← Complex.ofReal_pow,← pow_mul,Nat.mul_comm] using
      (Complex.mul_conj' ((halaszVinogradovPolynomial k N α)^s)).symm
  have hc : Complex.ofReal (∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*s)
      ∂halaszVinogradovHaar k) = (halaszVinogradovCount s k N:ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hp]
    exact halasz_vinogradov_moment s k N
  exact_mod_cast hc



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

lemma halasz_fiber_energy_mono {α β : Type*} {F G : Finset α} (hFG : F⊆G)
    (f : α → β) : halaszFiberEnergy F f ≤ halaszFiberEnergy G f := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows]
  calc
    _ ≤ ∑ x∈F, (G.filter (fun y => f y=f x)).card := by
      apply sum_le_sum
      intro x _
      exact card_le_card (filter_subset_filter _ hFG)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => Nat.zero_le _)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyImage
namespace OAI

/-! Reindexing finite energies by the residue-class quotient map. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_fiber_energy_image {α β γ : Type*} (F : Finset α)
    (g : α → β) (hg : Set.InjOn g F) (f : β → γ) :
    halaszFiberEnergy (F.image g) f = halaszFiberEnergy F (fun x => f (g x)) := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows,sum_image hg]
  apply sum_congr rfl
  intro x _
  rw [filter_image]
  exact card_image_of_injOn (hg.mono (filter_subset _ _))


lemma halasz_fiber_energy_transfer {α β γ : Type*} (F : Finset α)
    (g : α → β) (hg : Set.InjOn g F) (u : α → γ) (v : β → γ)
    (hv : ∀ x∈F, v (g x)=u x) :
    halaszFiberEnergy F u = halaszFiberEnergy (F.image g) v := by
  rw [halasz_fiber_energy_image F g hg v]
  apply halasz_fiber_energy_congr
  intro x hx y hy
  rw [hv x hx,hv y hy]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszFinitePhase
namespace OAI

/-! Exact Fourier formulas for the finite energies used when the short
variables are restricted to one residue class. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate


lemma halasz_finite_phase_continuous {ι : Type*} {k : ℕ}
    (F : Finset ι) (f : ι → Fin k → ℤ) : Continuous (halaszFinitePhase F f) := by
  exact continuous_finsetSum F (fun x _ => halasz_vinogradov_character_continuous (f x))


theorem halasz_finite_phase_energy {ι : Type*} {k : ℕ} (F : Finset ι)
    (f : ι → Fin k → ℤ) :
    (∫ α, ‖halaszFinitePhase F f α‖^2 ∂halaszVinogradovHaar k) =
      (halaszFiberEnergy F f : ℝ) := by
  have hi (x y : ι) : Integrable (fun α =>
      halaszVinogradovCharacter (f x) α * conj (halaszVinogradovCharacter (f y) α))
      (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  have hc : (∫ α, halaszFinitePhase F f α * conj (halaszFinitePhase F f α)
      ∂halaszVinogradovHaar k) = (halaszFiberEnergy F f : ℂ) := by
    unfold halaszFinitePhase
    simp_rw [map_sum,sum_mul,mul_sum]
    rw [integral_finsetSum F (fun x _ => integrable_finsetSum F (fun y _ => hi x y))]
    simp_rw [integral_finsetSum F (fun y _ => hi _ y),halasz_vinogradov_character_inner]
    rw [halasz_fiber_energy_rows,Nat.cast_sum]
    apply sum_congr rfl
    intro x _
    simp only [sum_boole]
    congr 2
    ext y
    simp only [mem_filter]
    exact and_congr_right (fun _ => eq_comm)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa only [Complex.mul_conj',Complex.ofReal_pow,Complex.ofReal_natCast] using hc

lemma halasz_finite_phase_product {ι κ : Type*} {k : ℕ} (F : Finset ι) (G : Finset κ)
    (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszFinitePhase (F×ˢG) (fun x => f x.1+g x.2) α =
      halaszFinitePhase F f α * halaszFinitePhase G g α := by
  simp only [halaszFinitePhase,sum_product,halasz_vinogradov_character_add,sum_mul,mul_sum]
  rw [sum_comm]

lemma halasz_finite_phase_power {ι : Type*} {k : ℕ} (F : Finset ι)
    (f : ι → Fin k → ℤ) (s : ℕ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszFinitePhase (Fintype.piFinset (fun _ : Fin s => F))
        (fun x => ∑ i, f (x i)) α = (halaszFinitePhase F f α)^s := by
  rw [halaszFinitePhase,halaszFinitePhase,sum_pow']
  apply sum_congr rfl
  intro x _
  exact halasz_vinogradov_character_sum univ (fun i => f (x i)) α


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyDiagonal
namespace OAI

/-! Diagonal pairs in the long variables retain a full copy of the
short-variable energy for each long tuple. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem halasz_energy_diagonal_lower {α β γ : Type*} [Add γ]
    (F : Finset α) (G : Finset β) (f : α → γ) (g : β → γ) :
    F.card * halaszFiberEnergy G g ≤
      halaszFiberEnergy (F×ˢG) (fun x => f x.1+g x.2) := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows,sum_product,mul_sum]
  have hl (a : α) (ha : a∈F) (b : β) :
      (G.filter (fun y => g y=g b)).card ≤
        ((F×ˢG).filter (fun y => f y.1+g y.2=f a+g b)).card := by
    calc
      _ = ({a}×ˢ(G.filter (fun y => g y=g b))).card := by simp
      _ ≤ _ := by
        apply card_le_card
        intro y hy
        obtain ⟨hy1,hy2⟩ := mem_product.mp hy
        have hy1' : y.1=a := mem_singleton.mp hy1
        obtain ⟨hyG,hyg⟩ := mem_filter.mp hy2
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hy1' ▸ ha,hyG⟩,by rw [hy1',hyg]⟩
  calc
    _ = ∑ _a∈F, ∑ b∈G, (G.filter (fun y => g y=g b)).card := by
      rw [← mul_sum]
      simp
    _ ≤ _ := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b _
      exact hl a ha b

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentInterpolation
namespace OAI

/-! The moment interpolation used to absorb colliding long variables.
All functions live on the same finite coefficient torus. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_torus_geometric_mean {k : ℕ}
    (F G : (Fin k → AddCircle (1:ℝ)) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ x, 0≤ F x) (hG0 : ∀ x, 0≤ G x)
    {θ : ℝ} (hθ0 : 0<θ) (hθ1 : θ<1) :
    (∫ x, (F x)^θ*(G x)^(1-θ) ∂halaszVinogradovHaar k) ≤
      (∫ x, F x ∂halaszVinogradovHaar k)^θ *
        (∫ x, G x ∂halaszVinogradovHaar k)^(1-θ) := by
  have hq0 : 0<1-θ := by linarith
  have hFc : Continuous (fun x => (F x)^θ) :=
    hF.rpow_const (fun x => Or.inr hθ0.le)
  have hGc : Continuous (fun x => (G x)^(1-θ)) :=
    hG.rpow_const (fun x => Or.inr hq0.le)
  have hpq : (1/θ).HolderConjugate (1/(1-θ)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_div hθ0).mpr hθ1
    · simp only [one_div,inv_inv]
      ring
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := halaszVinogradovHaar k) hpq
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hF0 x) _))
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hG0 x) _))
    (hFc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hGc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hp (x : Fin k → AddCircle (1:ℝ)) : ((F x)^θ)^(1/θ)=F x := by
    rw [← Real.rpow_mul (hF0 x),mul_one_div_cancel hθ0.ne',Real.rpow_one]
  have hq (x : Fin k → AddCircle (1:ℝ)) : ((G x)^(1-θ))^(1/(1-θ))=G x := by
    rw [← Real.rpow_mul (hG0 x),mul_one_div_cancel hq0.ne',Real.rpow_one]
  simp_rw [hp,hq] at h
  simpa only [one_div,inv_inv] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBalancedMoment
namespace OAI

/-! Equal total moments bound each mixed moment. This will be applied
to the ordinary polynomial sum and its doubled-frequency version. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory

theorem halasz_equal_moment_bound {k a b : ℕ} (ha : 0< a) (hb : 0< b)
    (F G : (Fin k → AddCircle (1:ℝ)) → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (he : (∫ x, ‖F x‖^(a+b) ∂halaszVinogradovHaar k) =
      ∫ x, ‖G x‖^(a+b) ∂halaszVinogradovHaar k) :
    (∫ x, ‖F x‖^a * ‖G x‖^b ∂halaszVinogradovHaar k) ≤
      ∫ x, ‖F x‖^(a+b) ∂halaszVinogradovHaar k := by
  let θ : ℝ := a/(a+b)
  have ha0 : (0:ℝ)< a := by exact_mod_cast ha
  have hb0 : (0:ℝ)< b := by exact_mod_cast hb
  have hab0 : (0:ℝ)< a+b := by positivity
  have hθ0 : 0<θ := div_pos ha0 hab0
  have hθ1 : θ<1 := (div_lt_one hab0).mpr (by linarith)
  have hpowF (x : Fin k → AddCircle (1:ℝ)) : (‖F x‖^(a+b))^θ=‖F x‖^a := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    have hbal : ((a+b:ℕ):ℝ)*θ=a := by
      dsimp [θ]
      push_cast
      field_simp
    rw [hbal,Real.rpow_natCast]
  have hpowG (x : Fin k → AddCircle (1:ℝ)) : (‖G x‖^(a+b))^(1-θ)=‖G x‖^b := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    have hbal : ((a+b:ℕ):ℝ)*(1-θ)=b := by
      dsimp [θ]
      push_cast
      field_simp
      ring
    rw [hbal,Real.rpow_natCast]
  have h := halasz_torus_geometric_mean (fun x => ‖F x‖^(a+b))
    (fun x => ‖G x‖^(a+b)) (hF.norm.pow _) (hG.norm.pow _)
    (fun _ => by positivity) (fun _ => by positivity) hθ0 hθ1
  simp_rw [hpowF,hpowG] at h
  rw [← he] at h
  have hJ : 0≤∫ x, ‖F x‖^(a+b) ∂halaszVinogradovHaar k :=
    integral_nonneg (fun _ => by positivity)
  exact h.trans (by simpa only [add_sub_cancel,Real.rpow_one] using
    Real.le_rpow_add hJ θ (1-θ))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszHolderPowers
namespace OAI

/-! Integer-power forms of the moment interpolation inequalities.
They avoid fractional powers in the final collision-absorption step. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory

theorem halasz_holder_integer_power {d k : ℕ} (hk : 2≤ k)
    (A B : (Fin d → AddCircle (1:ℝ)) → ℝ)
    (hA : Continuous A) (hB : Continuous B)
    (hA0 : ∀ x, 0≤ A x) (hB0 : ∀ x, 0≤ B x) :
    (∫ x, (A x)^(1-1/(k:ℝ))*(B x)^(1/(k:ℝ)) ∂halaszVinogradovHaar d)^k ≤
      (∫ x, A x ∂halaszVinogradovHaar d)^(k-1) *
        (∫ x, B x ∂halaszVinogradovHaar d) := by
  have hk0 : (0:ℝ)< k := by exact_mod_cast (by omega : 0< k)
  have hk1 : (1:ℝ)< k := by exact_mod_cast (by omega : 1< k)
  have hθ0 : 0<1-1/(k:ℝ) := by
    have : 1/(k:ℝ)<1 := (div_lt_one hk0).mpr hk1
    linarith
  have hθ1 : 1-1/(k:ℝ)<1 := by
    have := one_div_pos.mpr hk0
    linarith
  have h := halasz_torus_geometric_mean A B hA hB hA0 hB0 hθ0 hθ1
  simp only [sub_sub_cancel] at h
  have hI : 0≤∫ x, (A x)^(1-1/(k:ℝ))*(B x)^(1/(k:ℝ))
      ∂halaszVinogradovHaar d := integral_nonneg (fun x =>
    mul_nonneg (Real.rpow_nonneg (hA0 x) _) (Real.rpow_nonneg (hB0 x) _))
  have hAI : 0≤∫ x, A x ∂halaszVinogradovHaar d := integral_nonneg hA0
  have hBI : 0≤∫ x, B x ∂halaszVinogradovHaar d := integral_nonneg hB0
  have hexp : (1-1/(k:ℝ))*(k:ℝ)=((k-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤ k)]
    push_cast
    field_simp
  have hpow := pow_le_pow_left₀ hI h k
  rw [mul_pow,← Real.rpow_mul_natCast hAI,← Real.rpow_mul_natCast hBI,
    hexp,one_div_mul_cancel hk0.ne',Real.rpow_natCast,Real.rpow_one] at hpow
  exact hpow

lemma halasz_collision_power_absorb {k : ℕ} (hk : 1≤ k)
    {A B C : ℝ} (hA : 0< A)
    (h : A^k ≤ C^k*A^(k-1)*B) : A≤ C^k*B := by
  have hp : 0< A^(k-1) := pow_pos hA _
  apply le_of_mul_le_mul_right _ hp
  calc
    A*A^(k-1) = A^k := by rw [← pow_succ',Nat.sub_add_cancel hk]
    _ ≤ C^k*A^(k-1)*B := h
    _ = (C^k*B)*A^(k-1) := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszScaledMoment
namespace OAI

/-! Multiplying every frequency by a nonzero integer leaves each
complete-system moment unchanged. The doubled system occurs in the
collision estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma halasz_scaled_polynomial_continuous (k N : ℕ) (m : ℤ) :
    Continuous (halaszScaledPolynomial k N m) := halasz_finite_phase_continuous _ _

theorem halasz_scaled_moment (s k N : ℕ) (m : ℤ) (hm : m≠0) :
    (∫ α, ‖halaszScaledPolynomial k N m α‖^(2*s) ∂halaszVinogradovHaar k) =
      (halaszVinogradovCount s k N:ℝ) := by
  let f (x : Fin N) : Fin k → ℤ := fun j => m*((x.val+1)^(j.val+1):ℕ)
  let A := Fintype.piFinset (fun _ : Fin s => (univ : Finset (Fin N)))
  have h := halasz_finite_phase_energy A (fun x => ∑ i, f (x i))
  have hp (α : Fin k → AddCircle (1:ℝ)) :
      halaszFinitePhase A (fun x => ∑ i, f (x i)) α =
        (halaszScaledPolynomial k N m α)^s :=
    halasz_finite_phase_power univ f s α
  simp_rw [hp,norm_pow,← pow_mul,Nat.mul_comm s 2] at h
  have he : halaszFiberEnergy A (fun x => ∑ i, f (x i)) =
      halaszVinogradovCount s k N := by
    change halaszFiberEnergy (univ : Finset (Fin s → Fin N)) _ = _
    rw [← halasz_nat_power_energy s k N]
    apply halasz_fiber_energy_congr
    intro x _ y _
    constructor
    · intro hxy
      funext j
      have hj := congrFun hxy j
      simp only [Finset.sum_apply,f,← mul_sum,← Nat.cast_sum] at hj
      have hc := mul_left_cancel₀ hm hj
      exact_mod_cast hc
    · intro hxy
      funext j
      simp only [Finset.sum_apply,f,← mul_sum,← Nat.cast_sum]
      exact congrArg (fun t : ℕ => m*(t:ℤ)) (congrFun hxy j)
  rwa [he] at h

theorem halasz_scaled_mixed_moment {a b : ℕ} (ha : 0< a) (hb : 0< b)
    (k N : ℕ) (m : ℤ) (hm : m≠0) :
    (∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*a) *
      ‖halaszScaledPolynomial k N m α‖^(2*b) ∂halaszVinogradovHaar k) ≤
        (halaszVinogradovCount (a+b) k N : ℝ) := by
  have hF : Continuous (halaszVinogradovPolynomial k N) :=
    halasz_finite_phase_continuous _ _
  have h := halasz_equal_moment_bound (a := 2*a) (b := 2*b)
    (Nat.mul_pos (by decide : 0<2) ha) (Nat.mul_pos (by decide : 0<2) hb) (halaszVinogradovPolynomial k N)
    (halaszScaledPolynomial k N m) hF (halasz_scaled_polynomial_continuous k N m)
    (by rw [← Nat.mul_add,halasz_vinogradov_real_moment,halasz_scaled_moment _ _ _ _ hm])
  rwa [← Nat.mul_add,halasz_vinogradov_real_moment] at h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCollisionMoment
namespace OAI

/-! The analytic estimate for a repeated coordinate in a Vinogradov
system. The scaled polynomial records the repeated variable exactly. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_torus_cauchy {d : ℕ}
    (F G : (Fin d → AddCircle (1:ℝ)) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ x, 0≤ F x) (hG0 : ∀ x, 0≤ G x) :
    (∫ x, F x*G x ∂halaszVinogradovHaar d)^2 ≤
      (∫ x, (F x)^2 ∂halaszVinogradovHaar d) *
        (∫ x, (G x)^2 ∂halaszVinogradovHaar d) := by
  have h := halasz_holder_integer_power (by omega : 2≤2)
    (fun x => (F x)^2) (fun x => (G x)^2)
    (hF.pow 2) (hG.pow 2) (fun x => sq_nonneg _) (fun x => sq_nonneg _)
  have hs (x : ℝ) (hx : 0≤ x) : (x^2)^(1/(2:ℝ))=x := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx]
    norm_num
  norm_num only [Nat.cast_ofNat,show (1:ℝ)-1/2=1/2 by norm_num,
    hs _ (hF0 _),hs _ (hG0 _),Nat.reduceSub,pow_one] at h
  exact h

lemma halasz_collision_interpoland {s k : ℕ} (hk : 2≤ k)
    {f g : ℝ} (hf : 0≤ f) (hg : 0≤ g) :
    (f^(2*(s+k)))^(1-1/(k:ℝ)) *
        (f^(2*s)*g^k)^(1/(k:ℝ)) = f^(2*(s+k)-2)*g := by
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
  have he : ((2*(s+k):ℕ):ℝ)*(1-1/(k:ℝ)) + ((2*s:ℕ):ℝ)*(1/(k:ℝ)) =
      ((2*(s+k)-2:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 2≤2*(s+k))]
    push_cast
    field_simp
    ring
  rw [Real.mul_rpow (pow_nonneg hf _) (pow_nonneg hg _)]
  simp only [← Real.rpow_natCast,← Real.rpow_mul hf,← Real.rpow_mul hg]
  rw [← mul_assoc,← Real.rpow_add' hf]
  · rw [he,mul_one_div_cancel hk0,Real.rpow_one,Real.rpow_natCast]
  · rw [he]
    exact_mod_cast (by omega : 2*(s+k)-2≠0)


theorem halasz_collision_moment_bound {s k : ℕ} (hs : 0< s) (hk : 2≤ k) (N : ℕ) :
    (halaszCollisionMoment s k N)^(2*k) ≤
      (halaszVinogradovCount (s+k) k N:ℝ)^(2*k-1) *
        (halaszVinogradovCount s k N:ℝ) := by
  let F := fun α => ‖halaszVinogradovPolynomial k N α‖
  let G := fun α => ‖halaszScaledPolynomial k N 2 α‖
  have hF : Continuous F := (halasz_finite_phase_continuous _ _).norm
  have hG : Continuous G := (halasz_scaled_polynomial_continuous k N 2).norm
  have hF0 : ∀ α, 0≤ F α := fun _ => norm_nonneg _
  have hG0 : ∀ α, 0≤ G α := fun _ => norm_nonneg _
  let B := fun α => (F α)^(2*s)*(G α)^k
  have hB : Continuous B := (hF.pow _).mul (hG.pow _)
  have hB0 : ∀ α, 0≤ B α := fun α => mul_nonneg (pow_nonneg (hF0 α) _)
    (pow_nonneg (hG0 α) _)
  have hI := halasz_holder_integer_power hk (fun α => (F α)^(2*(s+k))) B
    (hF.pow _) hB (fun α => pow_nonneg (hF0 α) _) hB0
  have heq (α : Fin k → AddCircle (1:ℝ)) :
      ((F α)^(2*(s+k)))^(1-1/(k:ℝ))*(B α)^(1/(k:ℝ)) =
        (F α)^(2*(s+k)-2)*G α :=
    halasz_collision_interpoland hk (hF0 α) (hG0 α)
  simp_rw [heq] at hI
  change (halaszCollisionMoment s k N)^k ≤ _ at hI
  rw [halasz_vinogradov_real_moment] at hI
  have hC := halasz_torus_cauchy (fun α => (F α)^s*(G α)^k)
    (fun α => (F α)^s) ((hF.pow _).mul (hG.pow _)) (hF.pow _)
    (fun α => mul_nonneg (pow_nonneg (hF0 α) _) (pow_nonneg (hG0 α) _))
    (fun α => pow_nonneg (hF0 α) _)
  have hprod (α : Fin k → AddCircle (1:ℝ)) :
      ((F α)^s*(G α)^k)*(F α)^s=B α := by dsimp [B]; ring
  simp_rw [hprod,mul_pow,← pow_mul,Nat.mul_comm s 2,Nat.mul_comm k 2] at hC
  rw [halasz_vinogradov_real_moment] at hC
  have hM := halasz_scaled_mixed_moment hs (by omega : 0< k) k N 2 (by norm_num)
  have hC' : (∫ α, B α ∂halaszVinogradovHaar k)^2 ≤
      (halaszVinogradovCount (s+k) k N:ℝ)*(halaszVinogradovCount s k N:ℝ) :=
    hC.trans (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _))
  have hpow := pow_le_pow_left₀ (pow_nonneg
    (integral_nonneg (fun α => mul_nonneg (pow_nonneg (hF0 α) _) (hG0 α))) _) hI 2
  rw [mul_pow] at hpow
  have h := hpow.trans (mul_le_mul_of_nonneg_left hC'
    (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _))
  rw [← pow_mul,← pow_mul,← mul_assoc,← pow_succ,
    show k*2=2*k by omega,show (k-1)*2+1=2*k-1 by omega] at h
  exact h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCrossMoment
namespace OAI

/-! Fourier counting with two different collections of tuples, applied
to a prescribed repeated coordinate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate


theorem halasz_cross_integral {ι κ : Type*} {k : ℕ}
    (F : Finset ι) (G : Finset κ) (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) :
    (∫ α, halaszFinitePhase F f α * conj (halaszFinitePhase G g α)
      ∂halaszVinogradovHaar k) = (halaszCrossCount F G f g:ℂ) := by
  have hi (x : ι) (y : κ) : Integrable (fun α =>
      halaszVinogradovCharacter (f x) α * conj (halaszVinogradovCharacter (g y) α))
      (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  unfold halaszFinitePhase
  simp_rw [map_sum,sum_mul,mul_sum]
  rw [integral_finsetSum F (fun x _ => integrable_finsetSum G (fun y _ => hi x y))]
  simp_rw [integral_finsetSum G (fun y _ => hi _ y),halasz_vinogradov_character_inner]
  simp only [halaszCrossCount,card_eq_sum_ones,sum_filter,sum_product,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem halasz_cross_count_bound {ι κ : Type*} {k : ℕ}
    (F : Finset ι) (G : Finset κ) (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) :
    (halaszCrossCount F G f g:ℝ) ≤
      ∫ α, ‖halaszFinitePhase F f α‖ * ‖halaszFinitePhase G g α‖
        ∂halaszVinogradovHaar k := by
  have h := norm_integral_le_integral_norm
    (fun α => halaszFinitePhase F f α * conj (halaszFinitePhase G g α))
    (μ := halaszVinogradovHaar k)
  rw [halasz_cross_integral,Complex.norm_natCast] at h
  simpa only [norm_mul,Complex.norm_conj] using h



lemma halasz_repeated_phase (n k N : ℕ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszFinitePhase univ (halaszRepeatedFrequency n k N) α =
      halaszScaledPolynomial k N 2 α * (halaszVinogradovPolynomial k N α)^n := by
  let f (x : Fin N) : Fin k → ℤ := fun j => 2*((x.val+1)^(j.val+1):ℕ)
  let g (x : Fin N) : Fin k → ℤ := fun j => ((x.val+1)^(j.val+1):ℕ)
  have h := halasz_finite_phase_product (univ : Finset (Fin N))
    (Fintype.piFinset (fun _ : Fin n => (univ : Finset (Fin N)))) f
    (fun x => ∑ i, g (x i)) α
  rw [halasz_finite_phase_power] at h
  have hf : (fun x : Fin N × (Fin n → Fin N) => f x.1+∑ i, g (x.2 i)) =
      halaszRepeatedFrequency n k N := by
    funext x j
    simp only [Pi.add_apply,Finset.sum_apply,halaszRepeatedFrequency,
      halaszVinogradovFrequency,f,g]
  rw [hf] at h
  simpa only [Fintype.piFinset_univ,univ_product_univ,halaszScaledPolynomial,
    halaszVinogradovPolynomial,halaszFinitePhase,f,g] using h

theorem halasz_repeated_count_bound {s k : ℕ} (hk : 2≤ k) (N : ℕ) :
    (halaszRepeatedCount (s+k-2) k N:ℝ) ≤ halaszCollisionMoment s k N := by
  have hn : s+k-2+2=s+k := by omega
  have h := halasz_cross_count_bound (univ : Finset (Fin N × (Fin (s+k-2) → Fin N)))
    (univ : Finset (Fin (s+k-2+2) → Fin N)) (halaszRepeatedFrequency (s+k-2) k N)
    (halaszVinogradovFrequency k)
  simp_rw [halasz_repeated_phase,show ∀ α, halaszFinitePhase univ
      (halaszVinogradovFrequency (s := s+k-2+2) (N := N) k) α =
        (halaszVinogradovPolynomial k N α)^(s+k-2+2) by
    intro α
    exact (halasz_vinogradov_power_expand _ _ _ α).symm,
    norm_mul,norm_pow] at h
  change (halaszRepeatedCount (s+k-2) k N:ℝ) ≤ _ at h
  convert (preTransparency := .instances) h using 1
  unfold halaszCollisionMoment
  apply integral_congr_ae
  filter_upwards [] with α
  rw [mul_comm,mul_assoc,← pow_add]
  congr 2
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyRestriction
namespace OAI

/-! Removing a bad collection of tuples costs at most twice its
cross-count with all tuples. This keeps both sides of the system good. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical _root_.ComplexConjugate

lemma halasz_cross_count_self {α : Type*} {k : ℕ}
    (F : Finset α) (f : α → Fin k → ℤ) :
    halaszCrossCount F F f f=halaszFiberEnergy F f := by
  have h := halasz_cross_integral F F f f
  simp_rw [Complex.mul_conj'] at h
  simp_rw [← Complex.ofReal_pow] at h
  rw [integral_complex_ofReal,halasz_finite_phase_energy] at h
  exact_mod_cast h.symm

lemma halasz_cross_count_symm {α β : Type*} {k : ℕ}
    (F : Finset α) (G : Finset β) (f : α → Fin k → ℤ) (g : β → Fin k → ℤ) :
    halaszCrossCount F G f g=halaszCrossCount G F g f := by
  unfold halaszCrossCount
  simp only [card_eq_sum_ones,sum_filter,sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  simp only [eq_comm]


theorem halasz_energy_restriction {α : Type*} {k : ℕ}
    (F G : Finset α) (f : α → Fin k → ℤ) :
    halaszFiberEnergy F f ≤ 2*halaszCrossCount (F\G) F f f + halaszFiberEnergy G f := by
  let A := (((F\G)×ˢF).filter (fun x => f x.1=f x.2))
  let B := ((F×ˢ(F\G)).filter (fun x => f x.1=f x.2))
  let C := ((G×ˢG).filter (fun x => f x.1=f x.2))
  have hc : ((F×ˢF).filter (fun x => f x.1=f x.2)) ⊆ A∪B∪C := by
    intro x hx
    have hx' := mem_filter.mp hx
    have hxF := mem_product.mp hx'.1
    by_cases h1 : x.1∈G
    · by_cases h2 : x.2∈G
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_product.mpr ⟨h1,h2⟩,hx'.2⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr
          ⟨mem_product.mpr ⟨hxF.1,mem_sdiff.mpr ⟨hxF.2,h2⟩⟩,hx'.2⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_sdiff.mpr ⟨hxF.1,h1⟩,hxF.2⟩,hx'.2⟩))
  have hcard : halaszCrossCount F F f f ≤ A.card+B.card+C.card := by
    exact (card_le_card hc).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le A B) _))
  have hb : B.card=A.card := halasz_cross_count_symm F (F\G) f f
  have hC : C.card=halaszFiberEnergy G f := halasz_cross_count_self G f
  rw [halasz_cross_count_self,hb,hC] at hcard
  change _ ≤ 2*A.card+_
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszRepeatedCoordinates
namespace OAI

/-! A repeated coordinate in any two prescribed positions is counted
by the same doubled-variable system. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_equiv_two_points {α : Type*} [DecidableEq α]
    {a b i j : α} (hab : a≠b) (hij : i≠j) :
    ∃ e : Equiv.Perm α, e a=i ∧ e b=j := by
  let e := Equiv.swap a i
  have hea : e a=i := Equiv.swap_apply_left _ _
  have hne : a≠e.symm j := by
    intro h
    apply hij
    calc
      i = e a := hea.symm
      _ = e (e.symm j) := congrArg e h
      _ = j := e.apply_symm_apply j
  refine ⟨e.setValue b j,?_,Equiv.setValue_eq _ _ _⟩
  change e (Equiv.swap b (e.symm j) a)=i
  rw [Equiv.swap_apply_of_ne_of_ne hab hne,hea]

lemma halasz_frequency_permute {n k N : ℕ} (e : Equiv.Perm (Fin n))
    (x : Fin n → Fin N) :
    halaszVinogradovFrequency k (x ∘ e)=halaszVinogradovFrequency k x := by
  funext j
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)


lemma halasz_repeat_tuple_frequency {n k N : ℕ} (a : Fin N) (x : Fin n → Fin N) :
    halaszVinogradovFrequency k (halaszRepeatTuple a x)=
      halaszRepeatedFrequency n k N (a,x) := by
  funext j
  simp only [halaszVinogradovFrequency,halaszRepeatTuple,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,halaszRepeatedFrequency]
  ring


lemma halasz_repeat_recover {n N : ℕ} (x : Fin (n+2) → Fin N) (hx : x 0=x 1) :
    halaszRepeatTuple (x 0) (fun a : Fin n => x a.succ.succ)=x := by
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · rfl
  · refine Fin.cases ?_ (fun c => ?_) b
    · exact hx
    · rfl

lemma halasz_canonical_collision_bound (n k N : ℕ) :
    (halaszPairCollision n k N 0 1).card ≤ halaszRepeatedCount n k N := by
  let f (xy : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N)) :=
    ((xy.1 0,fun a : Fin n => xy.1 a.succ.succ),xy.2)
  let T : Finset ((Fin N × (Fin n → Fin N)) × (Fin (n+2) → Fin N)) :=
    univ.filter (fun x => halaszRepeatedFrequency n k N x.1=halaszVinogradovFrequency k x.2)
  have hmap : Set.MapsTo f (halaszPairCollision n k N 0 1) T := by
    intro xy hxy
    obtain ⟨hc,hv⟩ := (mem_filter.mp hxy).2
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change halaszRepeatedFrequency n k N (xy.1 0,fun a => xy.1 a.succ.succ) = _
    rw [← halasz_repeat_tuple_frequency,halasz_repeat_recover xy.1 hc]
    exact hv
  have hinj : Set.InjOn f (halaszPairCollision n k N 0 1) := by
    intro xy hxy uv huv heq
    have hc := (mem_filter.mp hxy).2.1
    have hd := (mem_filter.mp huv).2.1
    have ha := congrArg (fun z => z.1.1) heq
    have ht := congrArg (fun z => z.1.2) heq
    have hy := congrArg Prod.snd heq
    change xy.1 0=uv.1 0 at ha
    change (fun a : Fin n => xy.1 a.succ.succ)=
      (fun a : Fin n => uv.1 a.succ.succ) at ht
    change xy.2=uv.2 at hy
    apply Prod.ext _ hy
    rw [← halasz_repeat_recover xy.1 hc,← halasz_repeat_recover uv.1 hd]
    exact congrArg₂ halaszRepeatTuple ha ht
  have h := card_le_card_of_injOn f hmap hinj
  simpa only [T,halaszRepeatedCount,halaszCrossCount,univ_product_univ] using h

theorem halasz_pair_collision_bound {n k N : ℕ} (i j : Fin (n+2)) (hij : i≠j) :
    (halaszPairCollision n k N i j).card ≤ halaszRepeatedCount n k N := by
  obtain ⟨e,he0,he1⟩ := halasz_equiv_two_points
    (show (0 : Fin (n+2))≠1 by
      intro h
      have h' : (0:ℕ)=1 := congrArg Fin.val h
      omega) hij
  let f (xy : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N)) := (xy.1 ∘ e,xy.2)
  apply le_trans (b := (halaszPairCollision n k N 0 1).card)
  · apply card_le_card_of_injOn f
    · intro xy hxy
      obtain ⟨hc,hv⟩ := (mem_filter.mp hxy).2
      change f xy ∈ halaszPairCollision n k N 0 1
      simp only [halaszPairCollision,mem_filter,mem_univ,true_and,f,
        Function.comp_apply,he0,he1]
      exact ⟨hc,(halasz_frequency_permute e xy.1).trans hv⟩
    · intro xy _ uv _ heq
      have hy := congrArg (fun z : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N) => z.2) heq
      change xy.2=uv.2 at hy
      apply Prod.ext _ hy
      funext a
      have ha := congrFun (congrArg Prod.fst heq) (e.symm a)
      simpa only [f,Function.comp_apply,e.apply_symm_apply] using ha
  · exact halasz_canonical_collision_bound n k N

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovProduct
namespace OAI

/-! Splitting the complete system into long and short tuples, and the
diagonal lower bound used to absorb colliding long variables. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_join_frequency {a b k N : ℕ} (x : (Fin a → Fin N) × (Fin b → Fin N)) :
    halaszNatPowerFrequency k (halaszTupleJoin a b N x) =
      halaszNatPowerFrequency k x.1+halaszNatPowerFrequency k x.2 := by
  funext j
  unfold halaszNatPowerFrequency halaszTupleJoin
  rw [Fin.sum_univ_add]
  simp only [Equiv.coe_fn_mk,Fin.append_left,Fin.append_right,Pi.add_apply]

theorem halasz_vinogradov_product_count (a b k N : ℕ) :
    halaszFiberEnergy ((univ : Finset (Fin a → Fin N))×ˢ(univ : Finset (Fin b → Fin N)))
      (fun x => halaszNatPowerFrequency k x.1+halaszNatPowerFrequency k x.2) =
      halaszVinogradovCount (a+b) k N := by
  let e := halaszTupleJoin a b N
  have he := halasz_fiber_energy_image
    (univ : Finset ((Fin a → Fin N) × (Fin b → Fin N))) e e.injective.injOn
    (halaszNatPowerFrequency k)
  have he' : halaszFiberEnergy (univ : Finset (Fin (a+b) → Fin N))
      (halaszNatPowerFrequency k) =
      halaszFiberEnergy (univ : Finset ((Fin a → Fin N) × (Fin b → Fin N)))
        (fun x => halaszNatPowerFrequency k (e x)) := by
    convert (preTransparency := .instances) he using 1
    congr 1
    ext y
    simp only [mem_image,mem_univ,true_and,true_iff]
    exact e.surjective y
  rw [halasz_nat_power_energy] at he'
  rw [he']
  simp only [univ_product_univ]
  apply halasz_fiber_energy_congr
  intro x _ y _
  rw [halasz_join_frequency,halasz_join_frequency]

theorem halasz_vinogradov_diagonal_extension (s k N : ℕ) :
    N^k*halaszVinogradovCount s k N ≤ halaszVinogradovCount (k+s) k N := by
  have h := halasz_energy_diagonal_lower
    (univ : Finset (Fin k → Fin N)) (univ : Finset (Fin s → Fin N))
    (halaszNatPowerFrequency k) (halaszNatPowerFrequency k)
  rw [halasz_nat_power_energy,halasz_vinogradov_product_count] at h
  simpa using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCollisionAbsorption
namespace OAI

/-! Absorbing the contribution of repeated long coordinates by the
diagonal lower bound for the complete mean value. -/
namespace TwoPointCorrelations

lemma halasz_collision_algebra {k : ℕ} (hk : 0< k) {A B I C R : ℝ}
    (hA : 0< A) (hB : 0< B) (hC : 0≤ C) (hR : C^2< R)
    (hdiag : R^k*B≤ A) (hmoment : I^(2*k)≤ A^(2*k-1)*B) : C*I< A := by
  by_contra hn
  have hAI : A≤ C*I := le_of_not_gt hn
  have hpow := pow_le_pow_left₀ hA.le hAI (2*k)
  rw [mul_pow] at hpow
  have ha : A^(2*k) ≤ C^(2*k)*A^(2*k-1)*B := by
    calc
      A^(2*k) ≤ C^(2*k)*I^(2*k) := hpow
      _ ≤ C^(2*k)*(A^(2*k-1)*B) :=
        mul_le_mul_of_nonneg_left hmoment (pow_nonneg hC _)
      _ = _ := by ring
  have hb := halasz_collision_power_absorb (by omega : 1≤2*k) hA ha
  have hRpow : C^(2*k)< R^k := by
    rw [pow_mul]
    exact pow_lt_pow_left₀ hR (sq_nonneg C) (by omega)
  have hstrict : C^(2*k)*B< R^k*B := mul_lt_mul_of_pos_right hRpow hB
  linarith

theorem halasz_collision_moment_small {s k N : ℕ} (hs : 0< s) (hk : 2≤ k)
    {C : ℝ} (hC : 0≤ C) (hN : C^2< N) :
    C*halaszCollisionMoment s k N < (halaszVinogradovCount (s+k) k N:ℝ) := by
  have hN0 : 0< N := by exact_mod_cast lt_of_le_of_lt (sq_nonneg C) hN
  have hJs : 0<(halaszVinogradovCount s k N:ℝ) := by
    exact_mod_cast lt_of_lt_of_le (Nat.pow_pos hN0) (halasz_vinogradov_count_lower s k N)
  have hJ : 0<(halaszVinogradovCount (s+k) k N:ℝ) := by
    exact_mod_cast lt_of_lt_of_le (Nat.pow_pos hN0)
      (halasz_vinogradov_count_lower (s+k) k N)
  have hdiag : (N:ℝ)^k*(halaszVinogradovCount s k N:ℝ) ≤
      (halaszVinogradovCount (s+k) k N:ℝ) := by
    exact_mod_cast (by simpa only [Nat.add_comm k s] using
      halasz_vinogradov_diagonal_extension s k N)
  exact halasz_collision_algebra (by omega : 0< k) hJ hJs hC hN hdiag
    (halasz_collision_moment_bound hs hk N)

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



theorem halasz_bad_long_count_bound {n k N ℓ : ℕ} (L : Fin ℓ → Fin (n+2))
    (hL : Function.Injective L) :
    halaszBadLongCount (k := k) (N := N) L ≤ ℓ^2*halaszRepeatedCount n k N := by
  let P := (univ : Finset (Fin ℓ × Fin ℓ)).filter (fun ij => ij.1≠ij.2)
  let S := fun ij : Fin ℓ × Fin ℓ => halaszPairCollision n k N (L ij.1) (L ij.2)
  have hsub : (univ.filter (fun xy : (Fin (n+2) → Fin N) × (Fin (n+2) → Fin N) =>
      ¬Function.Injective (xy.1 ∘ L) ∧
      halaszVinogradovFrequency k xy.1=halaszVinogradovFrequency k xy.2)) ⊆
      P.biUnion S := by
    intro xy hxy
    obtain ⟨hbad,hfreq⟩ := (mem_filter.mp hxy).2
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hbad
    apply mem_biUnion.mpr
    refine ⟨(i,j),mem_filter.mpr ⟨mem_univ _,hne⟩,?_⟩
    exact mem_filter.mpr ⟨mem_univ _,hij,hfreq⟩
  have hP : P.card≤ℓ^2 := by
    calc
      P.card ≤ (univ : Finset (Fin ℓ × Fin ℓ)).card := card_filter_le _ _
      _ = ℓ^2 := by simp [pow_two]
  calc
    halaszBadLongCount (k := k) (N := N) L ≤ (P.biUnion S).card := card_le_card hsub
    _ ≤ ∑ ij∈P, (S ij).card := card_biUnion_le
    _ ≤ ∑ _ij∈P, halaszRepeatedCount n k N := by
      apply sum_le_sum
      intro ij hij
      exact halasz_pair_collision_bound _ _ (fun h => (mem_filter.mp hij).2 (hL h))
    _ = P.card*halaszRepeatedCount n k N := by simp
    _ ≤ ℓ^2*halaszRepeatedCount n k N := Nat.mul_le_mul_right _ hP

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

theorem halasz_long_collision_partition {n k N ℓ : ℕ} (L : Fin ℓ → Fin (n+2))
    (hL : Function.Injective L) :
    halaszVinogradovCount (n+2) k N ≤ 2*(ℓ^2*halaszRepeatedCount n k N) +
      halaszFiberEnergy (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k) := by
  have h := halasz_energy_restriction (univ : Finset (Fin (n+2) → Fin N))
    (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k)
  rw [halasz_frequency_energy] at h
  apply h.trans
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left 2
  convert (preTransparency := .instances) halasz_bad_long_count_bound (k := k) (N := N) L hL using 1
  unfold halaszCrossCount halaszBadLongCount
  congr 1
  ext xy
  simp only [mem_filter,mem_product,mem_sdiff,mem_univ,true_and,
    halaszGoodLongTuples,and_true]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDistinctMoment
namespace OAI

/-! At least half the complete-system solutions have distinct chosen
long coordinates on both sides, once the elementary size threshold holds. -/
namespace TwoPointCorrelations

theorem halasz_distinct_moment {s k n N ℓ : ℕ} (hs : 0< s) (hk : 2≤ k)
    (hn : n+2=s+k) (L : Fin ℓ → Fin (n+2)) (hL : Function.Injective L)
    (hN : (4*(ℓ:ℝ)^2)^2<(N:ℝ)) :
    halaszVinogradovCount (n+2) k N ≤
      2*halaszFiberEnergy (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k) := by
  have hp := halasz_long_collision_partition (k := k) (N := N) L hL
  have hpR : (halaszVinogradovCount (n+2) k N:ℝ) ≤
      2*((ℓ:ℝ)^2*(halaszRepeatedCount n k N:ℝ)) +
        (halaszFiberEnergy (halaszGoodLongTuples (N := N) L)
          (halaszVinogradovFrequency k):ℝ) := by exact_mod_cast hp
  have hn' : n=s+k-2 := by omega
  have hr : (halaszRepeatedCount n k N:ℝ) ≤ halaszCollisionMoment s k N := by
    rw [hn']
    exact halasz_repeated_count_bound hk N
  have hc : 0≤4*(ℓ:ℝ)^2 := by positivity
  have hsmall := halasz_collision_moment_small hs hk hc hN
  rw [← hn] at hsmall
  have hbad := mul_le_mul_of_nonneg_left hr hc
  have he : (halaszVinogradovCount (n+2) k N:ℝ) <
      2*(halaszFiberEnergy (halaszGoodLongTuples (N := N) L)
        (halaszVinogradovFrequency k):ℝ) := by
    nlinarith only [hpR,hsmall,hbad]
  exact_mod_cast he.le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszAvoidPrimes
namespace OAI

/-! A small family of primes contains a prime preserving distinctness
of both long tuples. Only the prime supply is analytic. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_large_prime_divisors {L r m : ℕ} (hL : 0< L) (hm : 0< m)
    (hbound : m< L^r) (P : Finset ℕ)
    (hP : ∀ p∈P, p.Prime ∧ L≤ p) :
    (P.filter (fun p => p∣m)).card< r := by
  let D := P.filter (fun p => p∣m)
  have hsub : D⊆m.primeFactors := by
    intro p hp
    obtain ⟨hpP,hpm⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(hP p hpP).1,hpm,hm.ne'⟩
  have hdvd : (∏ p∈D, p)∣m :=
    (prod_dvd_prod_of_subset D m.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd m)
  have hprod : L^D.card≤∏ p∈D, p := by
    calc
      L^D.card = ∏ _p∈D, L := by simp
      _ ≤ ∏ p∈D, p := prod_le_prod' (fun p hp => (hP p (mem_filter.mp hp).1).2)
  by_contra! hn
  change r≤ D.card at hn
  have hpow : L^r≤ L^D.card := Nat.pow_le_pow_right hL hn
  have hle := Nat.le_of_dvd hm hdvd
  exact (not_lt_of_ge (hpow.trans (hprod.trans hle))) hbound

lemma halasz_congruent_prime_count {L r N : ℕ} (hL : 0< L) (hN : N≤ L^r)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ L≤ p)
    (a b : Fin N) (hab : a≠b) :
    (P.filter (fun p => (((a.val+1:ℕ):ZMod p)=((b.val+1:ℕ):ZMod p)))).card≤ r := by
  let m := Nat.dist (a.val+1) (b.val+1)
  have hm : 0< m := Nat.dist_pos_of_ne (fun h => hab (Fin.ext (by omega)))
  have hmN : m< N := by dsimp [m,Nat.dist]; have := a.isLt; have := b.isLt; omega
  have hd := halasz_large_prime_divisors hL hm (hmN.trans_le hN) P hP
  apply le_trans _ hd.le
  apply card_le_card
  intro p hp
  obtain ⟨hp,hcong⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨hp,?_⟩
  have hmod := (ZMod.natCast_eq_natCast_iff (a.val+1) (b.val+1) p).mp hcong
  change p∣Nat.dist (a.val+1) (b.val+1)
  rcases le_total (a.val+1) (b.val+1) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    exact (Nat.modEq_iff_dvd' h).mp hmod
  · rw [Nat.dist_eq_sub_of_le_right h]
    exact (Nat.modEq_iff_dvd' h).mp hmod.symm

theorem halasz_bad_residue_prime_count {L r N ℓ : ℕ} (hL : 0< L) (hN : N≤ L^r)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ L≤ p)
    (x : Fin ℓ → Fin N) (hx : Function.Injective x) :
    (P.filter (fun p => ¬Function.Injective
      (fun i => (((x i).val+1:ℕ):ZMod p)))).card≤ℓ^2*r := by
  let I := (univ : Finset (Fin ℓ × Fin ℓ)).filter (fun ij => ij.1≠ij.2)
  let B := fun ij : Fin ℓ × Fin ℓ => P.filter (fun p =>
    ((((x ij.1).val+1:ℕ):ZMod p)=(((x ij.2).val+1:ℕ):ZMod p)))
  have hsub : (P.filter (fun p => ¬Function.Injective
      (fun i => (((x i).val+1:ℕ):ZMod p))))⊆I.biUnion B := by
    intro p hp
    obtain ⟨hpP,hbad⟩ := mem_filter.mp hp
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hbad
    exact mem_biUnion.mpr ⟨(i,j),mem_filter.mpr ⟨mem_univ _,hne⟩,
      mem_filter.mpr ⟨hpP,hij⟩⟩
  have hI : I.card≤ℓ^2 := by
    calc
      I.card ≤ (univ : Finset (Fin ℓ × Fin ℓ)).card := card_filter_le _ _
      _ = ℓ^2 := by simp [pow_two]
  calc
    _ ≤ (I.biUnion B).card := card_le_card hsub
    _ ≤ I.card*r := card_biUnion_le_card_mul I B r (fun ij hij =>
      halasz_congruent_prime_count hL hN P hP _ _ (fun h => (mem_filter.mp hij).2 (hx h)))
    _ ≤ ℓ^2*r := Nat.mul_le_mul_right _ hI

theorem halasz_exists_good_prime {L r N ℓ : ℕ} (hL : 0< L) (hN : N≤ L^r)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ L≤ p) (hcard : 2*(ℓ^2*r)< P.card)
    (x y : Fin ℓ → Fin N) (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ p∈P, Function.Injective (fun i => (((x i).val+1:ℕ):ZMod p)) ∧
      Function.Injective (fun i => (((y i).val+1:ℕ):ZMod p)) := by
  let Bx := P.filter (fun p => ¬Function.Injective (fun i => (((x i).val+1:ℕ):ZMod p)))
  let By := P.filter (fun p => ¬Function.Injective (fun i => (((y i).val+1:ℕ):ZMod p)))
  by_contra! hn
  have hsub : P⊆Bx∪By := by
    intro p hp
    by_cases hxp : Function.Injective (fun i => (((x i).val+1:ℕ):ZMod p))
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,hn p hp hxp⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,hxp⟩)
  have hbX := halasz_bad_residue_prime_count hL hN P hP x hx
  have hbY := halasz_bad_residue_prime_count hL hN P hP y hy
  have hbad := (card_le_card hsub).trans (card_union_le Bx By)
  change P.card≤ Bx.card+By.card at hbad
  change Bx.card≤ℓ^2*r at hbX
  change By.card≤ℓ^2*r at hbY
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeEnergyCover
namespace OAI

/-! Cover each pair of good long tuples by a prime at which both
remain nonsingular. This is a cover of solutions, not just of tuples. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_fiber_energy_cover {α ι : Type*} {k : ℕ}
    (F : Finset α) (S : Finset ι) (G : ι → Finset α) (f : α → Fin k → ℤ)
    (hcover : ∀ x∈F, ∀ y∈F, f x=f y → ∃ i∈S, x∈G i ∧ y∈G i) :
    halaszFiberEnergy F f≤∑ i∈S, halaszFiberEnergy (G i) f := by
  let T := fun i => ((G i×ˢG i).filter (fun xy => f xy.1=f xy.2))
  have hsub : ((F×ˢF).filter (fun xy => f xy.1=f xy.2))⊆S.biUnion T := by
    intro xy hxy
    obtain ⟨hxy,hf⟩ := mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    obtain ⟨i,hi,hxi,hyi⟩ := hcover xy.1 hx xy.2 hy hf
    exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_product.mpr ⟨hxi,hyi⟩,hf⟩⟩
  calc
    halaszFiberEnergy F f = ((F×ˢF).filter (fun xy => f xy.1=f xy.2)).card :=
      (halasz_cross_count_self F f).symm
    _ ≤ (S.biUnion T).card := card_le_card hsub
    _ ≤ ∑ i∈S, (T i).card := card_biUnion_le
    _ = _ := sum_congr rfl (fun i _ => halasz_cross_count_self (G i) f)


theorem halasz_distinct_energy_prime_cover {n k N ℓ R r : ℕ} (hR : 0< R)
    (hN : N≤ R^r) (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ R≤ p)
    (hcard : 2*(ℓ^2*r)< P.card) (L : Fin ℓ → Fin n) :
    halaszFiberEnergy (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k) ≤
      ∑ p∈P, halaszFiberEnergy (halaszResidueGoodTuples (N := N) L p)
        (halaszVinogradovFrequency k) := by
  apply halasz_fiber_energy_cover
  intro x hx y hy _
  have hxI := (mem_filter.mp hx).2
  have hyI := (mem_filter.mp hy).2
  obtain ⟨p,hp,hxp,hyp⟩ := halasz_exists_good_prime hR hN P hP hcard
    (x ∘ L) (y ∘ L) hxI hyI
  exact ⟨p,hp,mem_filter.mpr ⟨mem_univ _,hxp⟩,mem_filter.mpr ⟨mem_univ _,hyp⟩⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeRecurrence
namespace OAI

/-! The classical mean-value recurrence from a finite supply of primes.
All analytic prime-supply requirements appear as elementary bounds on P. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_distinct_moment_total {s k m N ℓ : ℕ} (hs : 0< s) (hk : 2≤ k)
    (hm : m=s+k) (L : Fin ℓ → Fin m) (hL : Function.Injective L)
    (hN : (4*(ℓ:ℝ)^2)^2<(N:ℝ)) :
    halaszVinogradovCount m k N ≤
      2*halaszFiberEnergy (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k) := by
  obtain ⟨n,hn⟩ : ∃ n, m=n+2 := ⟨m-2,by omega⟩
  have hnk : n+2=s+k := hn.symm.trans hm
  clear hm
  subst m
  exact halasz_distinct_moment hs hk hnk L hL hN

theorem halasz_vinogradov_prime_sum {s k N R : ℕ} (hs : 0< s) (hk : 2≤ k)
    (hsize : (4*(k:ℝ)^2)^2<(N:ℝ)) (hkR : k< R) (hNR : N< R^k)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ R≤ p)
    (hcard : 2*(k^2*k)< P.card) :
    halaszVinogradovCount (k+s) k N ≤
      2*∑ p∈P, p^(2*s)*((k^k*p^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/p+1))) := by
  let L : Fin k → Fin (k+s) := fun i => i.castAdd s
  have hL : Function.Injective L := Fin.castAdd_injective k s
  have hD := halasz_distinct_moment_total hs hk (Nat.add_comm k s) L hL hsize
  have hC := halasz_distinct_energy_prime_cover (k := k) (N := N)
    (by omega : 0< R) hNR.le P hP hcard L
  apply hD.trans
  apply Nat.mul_le_mul_left 2
  apply hC.trans
  apply sum_le_sum
  intro p hp
  have : Fact p.Prime := ⟨(hP p hp).1⟩
  have hNp : N< p^k := hNR.trans_le (Nat.pow_le_pow_left (hP p hp).2 k)
  exact halasz_residue_good_moment hs (by omega) (lt_of_lt_of_le hkR (hP p hp).2) hNp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCountMonotone
namespace OAI

/-! Monotonicity in the summation endpoint, needed to give the short
moment one common endpoint after summing over the selected primes. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem halasz_vinogradov_count_mono (s k : ℕ) {N M : ℕ} (hNM : N≤ M) :
    halaszVinogradovCount s k N≤ halaszVinogradovCount s k M := by
  let e : (Fin s → Fin N) → (Fin s → Fin M) := fun x i => (x i).castLE hNM
  have he : Function.Injective e := by
    intro x y h
    funext i
    exact Fin.castLE_injective hNM (congrFun h i)
  have hf (x : Fin s → Fin N) :
      halaszNatPowerFrequency k (e x)=halaszNatPowerFrequency k x := rfl
  have hm := halasz_fiber_energy_mono
    (subset_univ ((univ : Finset (Fin s → Fin N)).image e)) (halaszNatPowerFrequency k)
  rw [halasz_nat_power_energy] at hm
  have ht := halasz_fiber_energy_transfer (univ : Finset (Fin s → Fin N)) e he.injOn
    (halaszNatPowerFrequency k) (halaszNatPowerFrequency k) (fun x _ => hf x)
  rw [halasz_nat_power_energy] at ht
  apply ht.trans_le
  convert (preTransparency := .instances) hm using 1
  congr 1
  ext x
  simp only [mem_image]

theorem halasz_vinogradov_prime_recurrence {s k N R B : ℕ} (hs : 0< s) (hk : 2≤ k)
    (hsize : (4*(k:ℝ)^2)^2<(N:ℝ)) (hkR : k< R) (hNR : N< R^k)
    (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ R≤ p ∧ p≤ B)
    (hcard : 2*(k^2*k)< P.card) :
    halaszVinogradovCount (k+s) k N ≤
      2*P.card*(B^(2*s)*((k^k*B^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/R+1)))) := by
  have h := halasz_vinogradov_prime_sum hs hk hsize hkR hNR P
    (fun p hp => ⟨(hP p hp).1,(hP p hp).2.1⟩) hcard
  have hb : ∀ p∈P, p^(2*s)*((k^k*p^(k*(k-1)/2))*
      (N^k*halaszVinogradovCount s k (N/p+1))) ≤
      B^(2*s)*((k^k*B^(k*(k-1)/2))*(N^k*halaszVinogradovCount s k (N/R+1))) := by
    intro p hp
    have hpB := (hP p hp).2.2
    have hdiv : N/p+1≤ N/R+1 := Nat.add_le_add_right
      (Nat.div_le_div_left (hP p hp).2.1 (by omega : 0< R)) 1
    have hcount := halasz_vinogradov_count_mono s k hdiv
    gcongr
  apply h.trans
  have hsum := sum_le_sum hb
  simp only [sum_const,nsmul_eq_mul] at hsum
  calc
    _ ≤ 2*(P.card*(B^(2*s)*((k^k*B^(k*(k-1)/2))*
      (N^k*halaszVinogradovCount s k (N/R+1))))) := Nat.mul_le_mul_left 2 hsum
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeSupply
namespace OAI

/-! An elementary supply of primes in a fixed multiplicative interval.
Chebyshev's bounds suffice; no prime number theorem is needed here. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

lemma halasz_theta_eventually_lower :
    ∀ᶠ x : ℝ in atTop, x/4≤ Chebyshev.theta x := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlog := Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ)<1/32)
  have hshift : Tendsto (fun x : ℝ => x+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hroot : Tendsto Real.sqrt atTop atTop := Real.tendsto_sqrt_atTop
  have hlog2 : (1:ℝ)/2≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  filter_upwards [hshift.eventually hlog,hroot.eventually (eventually_ge_atTop (16*|C|)),
    eventually_ge_atTop (4:ℝ)] with x hl hs hx
  have hx0 : 0≤ x := by linarith
  have hxs := Real.sq_sqrt hx0
  have hlogx : Real.log (x+2)≤ x/16 := by
    change ‖Real.log (x+2)‖≤(1/32:ℝ)*‖x+2‖ at hl
    rw [Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith)),
      abs_of_nonneg (by linarith : 0≤ x+2)] at hl
    have ha := le_abs_self (Real.log (x+2))
    linarith
  have hsC : C*Real.sqrt x≤ x/16 := by
    have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
    have hc := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg x)
    nlinarith only [hm,hc,hxs]
  have hpsi := Chebyshev.psi_ge' hx0
  have htheta := hC x
  have hhalf := mul_le_mul_of_nonneg_left hlog2 (by linarith : 0≤ x-1)
  linarith

lemma halasz_theta_upper {x : ℝ} (hx : 0≤ x) : Chebyshev.theta x≤2*x := by
  have hl : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have h4 : Real.log 4≤2 := by
    have he : Real.log 4=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    linarith
  exact (Chebyshev.theta_le_log4_mul_x hx).trans (mul_le_mul_of_nonneg_right h4 hx)


lemma halasz_prime_supply_mem {R p : ℕ} (hp : p∈halaszPrimeSupply R) :
    p.Prime ∧ R< p ∧ p≤16*R := by
  have h := mem_sdiff.mp hp
  have ha := Nat.mem_primesLE.mp h.1
  have hb : ¬p≤ R := by intro he; exact h.2 (Nat.mem_primesLE.mpr ⟨he,ha.2⟩)
  exact ⟨ha.2,by omega,ha.1⟩

lemma halasz_prime_supply_mass (R : ℕ) :
    (∑ p∈halaszPrimeSupply R, Real.log (p:ℝ)) =
      Chebyshev.theta (16*(R:ℝ))-Chebyshev.theta (R:ℝ) := by
  rw [show 16*(R:ℝ)=((16*R:ℕ):ℝ) by push_cast; rfl,
    Chebyshev.theta_eq_sum_primesLE_log,Chebyshev.theta_eq_sum_primesLE_log]
  apply (eq_sub_iff_add_eq).mpr
  exact sum_sdiff (f := fun p : ℕ => Real.log (p:ℝ))
    (Nat.primesLE_mono (by omega : R≤16*R))

theorem halasz_prime_supply_card :
    ∀ᶠ R : ℕ in atTop, Real.sqrt (R:ℝ)≤(halaszPrimeSupply R).card := by
  have ht : Tendsto (fun R : ℕ => 16*(R:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<16)
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1/4)
  filter_upwards [ht.eventually halasz_theta_eventually_lower,ht.eventually hlog,
    eventually_ge_atTop (1:ℕ)] with R htheta hl hR
  have hR0 : (0:ℝ)< R := by exact_mod_cast (by omega : 0< R)
  have hs0 : 0< Real.sqrt (R:ℝ) := Real.sqrt_pos.mpr hR0
  have hlogBound : Real.log (16*(R:ℝ))≤ Real.sqrt (R:ℝ) := by
    change ‖Real.log (16*(R:ℝ))‖≤(1/4:ℝ)*‖(16*(R:ℝ))^(1/2:ℝ)‖ at hl
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg
      (Real.rpow_nonneg (by positivity) _),← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤16)] at hl
    norm_num at hl
    linarith [le_abs_self (Real.log (16*(R:ℝ)))]
  have hmass : 2*(R:ℝ)≤∑ p∈halaszPrimeSupply R, Real.log (p:ℝ) := by
    rw [halasz_prime_supply_mass]
    have hu := halasz_theta_upper hR0.le
    linarith
  have hsum : (∑ p∈halaszPrimeSupply R, Real.log (p:ℝ)) ≤
      ((halaszPrimeSupply R).card:ℝ)*Real.sqrt (R:ℝ) := by
    calc
      _ ≤ ∑ _p∈halaszPrimeSupply R, Real.sqrt (R:ℝ) := by
        apply sum_le_sum
        intro p hp
        have h := halasz_prime_supply_mem hp
        exact (Real.log_le_log (by exact_mod_cast h.1.pos)
          (by exact_mod_cast h.2.2)).trans hlogBound
      _ = _ := by simp
  have hs := Real.sq_sqrt hR0.le
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszClassicalStep
namespace OAI

/-! The classical mean-value step using a finite supply of primes.
The absolute lower threshold for R comes only from Chebyshev's bounds. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem halasz_classical_step : ∃ R₀ : ℕ, ∀ s k N R : ℕ,
    0< s → 2≤ k → (4*(k:ℝ)^2)^2<(N:ℝ) → k< R → N< R^k →
    R₀≤ R → (2*(k^2*k)+1)^2≤ R →
    halaszVinogradovCount (k+s) k N ≤
      2*(2*(k^2*k)+1)*((16*R)^(2*s)*((k^k*(16*R)^(k*(k-1)/2))*
        (N^k*halaszVinogradovCount s k (N/R+1)))) := by
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp halasz_prime_supply_card
  refine ⟨R₀,?_⟩
  intro s k N R hs hk hsize hkR hNR hR0 hmany
  have hroot : ((2*(k^2*k)+1:ℕ):ℝ)≤ Real.sqrt (R:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hmany
  have hcard : 2*(k^2*k)+1≤(halaszPrimeSupply R).card := by
    exact_mod_cast hroot.trans (hR₀ R hR0)
  obtain ⟨P,hP,hPcard⟩ := exists_subset_card_eq hcard
  have hb : ∀ p∈P, p.Prime ∧ R≤ p ∧ p≤16*R := by
    intro p hp
    have hh := halasz_prime_supply_mem (hP hp)
    exact ⟨hh.1,hh.2.1.le,hh.2.2⟩
  have h := halasz_vinogradov_prime_recurrence hs hk hsize hkR hNR P hb
    (by rw [hPcard]; omega)
  simpa only [hPcard] using h

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_classical_step := @OAI.TwoPointCorrelations.halasz_classical_step
