-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSlicedCubeSource_good_kernel_residue_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:05:49.946886+00:00
-- url     : https://prove2.me/submissions/c83a1df1-0ecf-41d6-9b01-ac157be8739e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B214
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_scalarKernel_explicit_probability_le_of_card_le_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_congr_support {f g : X → ℂ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.complexMean f = p.complexMean g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
  · rw [h x hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_nonneg {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : 0 ≤ p.eventProbability E := by
  classical
  exact p.mean_nonneg (fun x => by split_ifs <;> norm_num)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem eventProbability_le_of_weight_le {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (C : ℝ)
    (hw : ∀ x, p.weight x ≤ C * q.weight x) (E : Ω → Prop) :
    p.eventProbability E ≤ C * q.eventProbability E := by
  classical
  unfold eventProbability mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x <;> simp [hx, hw x]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

theorem dependent_fin_cons_map {n : ℕ} {X E : Fin (n + 1) → Type*}
    (a : ∀ i, X i → E i) (x : X 0) (y : ∀ i : Fin n, X i.succ) :
    (fun i => a i (Fin.cons x y i)) = Fin.cons (a 0 x) (fun i => a i.succ (y i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

namespace FiniteProbabilityWeights

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

theorem complexMean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (F : (∀ i, X i) → ℂ) :
    p.complexMean F = F (fun i => Fin.elim0 i) := by
  have hF : F = fun _ => F (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg F (Subsingleton.elim _ _)
  rw [hF, p.complexMean_const]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateDeterminant
namespace OAI

section

namespace Erdos3

theorem coordinateDeterminantVariation_nonneg (I X : Type*) [Fintype I] [Fintype X] :
    0 ≤ coordinateDeterminantVariation I X := by
  unfold coordinateDeterminantVariation
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductDomination
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem pi_weight_le {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) (C : J → ℝ)
    (hw : ∀ j x, (p j).weight x ≤ C j * (q j).weight x) (x : ∀ j, Ω j) :
    (pi p).weight x ≤ (∏ j, C j) * (pi q).weight x := by
  change (∏ j, (p j).weight (x j)) ≤ (∏ j, C j) * (∏ j, (q j).weight (x j))
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun j _ => (p j).nonneg (x j)) (fun j _ => hw j (x j))

theorem pi_eventProbability_le {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) (C : J → ℝ)
    (hw : ∀ j x, (p j).weight x ≤ C j * (q j).weight x) (E : (∀ j, Ω j) → Prop) :
    (pi p).eventProbability E ≤ (∏ j, C j) * (pi q).eventProbability E :=
  eventProbability_le_of_weight_le _ _ _ (pi_weight_le p q C hw) E

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

theorem integerScalarCubeSet_card_lower (I : Type*) [Fintype I] [DecidableEq I] (L H : ℕ)
    (hH : 0 < H) (hHL : (Fintype.card I + 1) * H ≤ L) :
    H ^ (Fintype.card I + 1) ≤ (integerScalarCubeSet I L).card := by
  classical
  have hHL' : H ≤ L := by nlinarith
  let point (x : Option I → Fin H) : IntegerScalarCubeBox I L := fun i =>
    ⟨((x i).val : ℤ), Finset.mem_Ico.mpr ⟨by omega, by have := (x i).isLt; omega⟩⟩
  have hpoint (x : Option I → Fin H) : point x ∈ integerScalarCubeSet I L :=
    (mem_integerScalarCubeSet L _).mpr (integerScalarCube_small_positive hH hHL x)
  let e : (Option I → Fin H) → ↥(integerScalarCubeSet I L) := fun x => ⟨point x, hpoint x⟩
  have he : Function.Injective e := by
    intro x y h
    funext i
    apply Fin.ext
    have hi := congrArg (fun z : ↥(integerScalarCubeSet I L) => (z.val i : ℤ)) h
    change ((x i).val : ℤ) = ((y i).val : ℤ) at hi
    exact_mod_cast hi
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_coe] using hc

theorem integerScalarCubeDensityCap_pos (I : Type*) [Fintype I] :
    0 < integerScalarCubeDensityCap I := by
  unfold integerScalarCubeDensityCap
  positivity


open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointKernelCutoffBudget
namespace OAI


namespace Erdos3

theorem jointKernelCutoff_bounds (n b : ℕ) {K T ε κ : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 0 < κ) :
    0 < jointKernelCutoff n b K T ε κ ∧
    n ≤ jointKernelCutoff n b K T ε κ ∧
    b ≤ jointKernelCutoff n b K T ε κ ∧
    1 / κ ≤ (jointKernelCutoff n b K T ε κ : ℝ) ∧
    K / κ ≤ (jointKernelCutoff n b K T ε κ : ℝ) ∧
    2 * T / ε ≤ (jointKernelCutoff n b K T ε κ : ℝ) := by
  have h1 : 0 < 1 / κ := one_div_pos.mpr hκ
  have h2 : 0 ≤ K / κ := div_nonneg hK hκ.le
  have h3 : 0 ≤ 2 * T / ε := div_nonneg (by positivity) hε.le
  have hc := Nat.le_ceil (1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε)
  change 1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε ≤
    (jointKernelCutoff n b K T ε κ : ℝ) at hc
  rw [add_div] at hc
  have hn : (n : ℝ) ≤ jointKernelCutoff n b K T ε κ := by linarith
  have hb : (b : ℝ) ≤ jointKernelCutoff n b K T ε κ := by linarith
  have hp : (0 : ℝ) < jointKernelCutoff n b K T ε κ := by
    have := Nat.cast_nonneg n (α := ℝ)
    have := Nat.cast_nonneg b (α := ℝ)
    linarith
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hn, by exact_mod_cast hb,
    by linarith, by linarith, by linarith⟩

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

theorem scalarKernelConditioningConstant_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D) : 0 < scalarKernelConditioningConstant I J M D :=
  pow_pos (scalarCubeResidueDensityCap_pos I (M * D) (Nat.mul_pos hM hD)) _

theorem scalarKernelTailConstant_pos (I J : Type*) [Fintype I] [Fintype J] :
    0 < scalarKernelTailConstant I J := by
  unfold scalarKernelTailConstant
  exact pow_pos (mul_pos (integerScalarCubeDensityCap_pos I) (by positivity)) _

theorem scalarKernelAdjustedAccuracy_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelAdjustedAccuracy I J M D η :=
  div_pos hη (scalarKernelConditioningConstant_pos I J hM hD)

theorem scalarKernelThreshold_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelThreshold I J M D η := by
  unfold scalarKernelThreshold discreteScalarMinorThreshold
  apply polynomialSublevelThreshold_pos
  · apply mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  · positivity
  · exact scalarKernelAdjustedAccuracy_pos I J hM hD hη

theorem scalarKernelCutoff_bounds (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelCutoff I J M D η ∧
    Fintype.card I + 1 ≤ scalarKernelCutoff I J M D η ∧
    D * ((Fintype.card I + 1) * M) ≤ scalarKernelCutoff I J M D η ∧
    1 / scalarKernelThreshold I J M D η ≤ (scalarKernelCutoff I J M D η : ℝ) ∧
    coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) /
        scalarKernelThreshold I J M D η ≤ (scalarKernelCutoff I J M D η : ℝ) ∧
    2 * scalarKernelTailConstant I J / scalarKernelAdjustedAccuracy I J M D η ≤
      (scalarKernelCutoff I J M D η : ℝ) :=
  jointKernelCutoff_bounds _ _ (coordinateDeterminantVariation_nonneg _ _)
    (scalarKernelTailConstant_pos I J).le (scalarKernelAdjustedAccuracy_pos I J hM hD hη)
    (scalarKernelThreshold_pos I J hM hD hη)


end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem complexMean_goodPart_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (Good : X → Prop)
    (f : X → ℂ) (g : ∀ x, Good x → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hgood : ∀ x (hx : Good x), ‖f x - g x hx‖ ≤ ε) :
    ‖p.complexMean f - p.complexMean (fun x => if hx : Good x then g x hx else 0)‖ ≤
      ε + p.eventProbability (fun x => ¬Good x) := by
  have hpoint (x : X) :
      ‖f x - (if hx : Good x then g x hx else 0)‖ ≤ ε + if ¬Good x then 1 else 0 := by
    by_cases hx : Good x
    · simpa only [hx, dif_pos, not_true_eq_false, ite_false, add_zero] using hgood x hx
    · simpa only [hx, dif_neg, not_false_eq_true, ite_true, sub_zero] using
        (hf x).trans (by linarith : (1 : ℝ) ≤ ε + 1)
  apply (p.norm_complexMean_sub_le _ _ _ (fun x _ => hpoint x)).trans_eq
  unfold eventProbability mean
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, p.total, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Good x <;> simp [hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeWindowLaw
namespace OAI

section

namespace Erdos3

theorem scalarCubeWindow_size {D n L K : ℕ} (hD : 0 < D)
    (hlarge : D * n ≤ L) (hDK : L ≤ D * K) : n ≤ K := by
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound
namespace OAI

section

namespace Erdos3

theorem scalarKernelCutoff_window_size (I J : Type*) [Fintype I] [Fintype J]
    {M D L K : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) (hDK : L ≤ D * K) :
    (Fintype.card I + 1) * M ≤ K :=
  scalarCubeWindow_size hD ((scalarKernelCutoff_bounds I J hM hD hη).2.2.1.trans hlarge) hDK

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productComplexMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℂ) :
    (FiniteProbabilityWeights.pi μ).complexMean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).complexMean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change ((∏ i, (μ i).weight (x i) : ℝ) : ℂ) * g (fun j => x (e j)) =
    ((∏ j, (μ (e j)).weight (x (e j)) : ℝ) : ℂ) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_pi_transport {n : ℕ} {X Y Z : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  induction n with
  | zero =>
      rw [complexMean_empty_tuple, complexMean_empty_tuple]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [complexMean_pi_fin_cons, complexMean_pi_fin_cons]
      simp only [dependent_fin_cons_map]
      calc
        _ = (p 0).complexMean (fun a => (pi (fun i : Fin n => q i.succ)).complexMean
            (fun y => f (Fin.cons (F 0 a) (fun i => G i.succ (y i))))) := by
          congr 1
          funext a
          exact ih (fun i => p i.succ) (fun i => q i.succ)
            (fun i => F i.succ) (fun i => G i.succ) (fun i => h i.succ) (fun z => f (Fin.cons (F 0 a) z))
        _ = _ := h 0 (fun z => (pi (fun i : Fin n => q i.succ)).complexMean
          (fun y => f (Fin.cons z (fun i => G i.succ (y i)))))

theorem complexMean_pi_transport_fintype {I : Type*} [Fintype I] [DecidableEq I]
    {X Y Z : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f' : (∀ j, Z (e j)) → ℂ := fun z => f ((Equiv.piCongrLeft Z e) z)
  have hp := productComplexMean_reindex p e
    (fun x => f' (fun j => F (e j) (x j)))
  have hq := productComplexMean_reindex q e
    (fun x => f' (fun j => G (e j) (x j)))
  have ht := complexMean_pi_transport (fun j => p (e j)) (fun j => q (e j))
    (fun j => F (e j)) (fun j => G (e j)) (fun j => h (e j)) f'
  have hcomp (z : ∀ i, Z i) : f' (fun j => z (e j)) = f z := by
    change f ((Equiv.piCongrLeft Z e) ((Equiv.piCongrLeft Z e).symm z)) = f z
    rw [Equiv.apply_symm_apply]
  calc
    _ = (pi p).complexMean (fun x => f' (fun j => F (e j) (x (e j)))) := by
      congr 1
      funext x
      exact (hcomp (fun i => F i (x i))).symm
    _ = (pi q).complexMean (fun x => f' (fun j => G (e j) (x (e j)))) :=
      hp.trans (ht.trans hq.symm)
    _ = _ := by
      congr 1
      funext x
      exact hcomp (fun i => G i (x i))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_subset_le_card_ratio {X : Type*} [DecidableEq X]
    (A B : Finset X) (hA : A.Nonempty) (hAB : A ⊆ B)
    (f : X → ℝ) (hf : ∀ x ∈ B, 0 ≤ f x) :
    (𝔼 x ∈ A, f x) ≤ ((B.card : ℝ) / A.card) * (𝔼 x ∈ B, f x) := by
  have hB0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast (hA.mono hAB).card_ne_zero
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  calc
    _ ≤ (∑ x ∈ B, f x) / (A.card : ℝ) := div_le_div_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x hx _ => hf x hx)) (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem expect_injective_le_card_ratio {X Y : Type*} [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (g : X → Y)
    (hg : Set.InjOn g A) (hB : ∀ x ∈ A, g x ∈ B)
    (f : Y → ℝ) (hf : ∀ y ∈ B, 0 ≤ f y) :
    (𝔼 x ∈ A, f (g x)) ≤ ((B.card : ℝ) / A.card) * (𝔼 y ∈ B, f y) := by
  have h := expect_subset_le_card_ratio (A.image g) B (hA.image g)
    (Finset.image_subset_iff.mpr hB) f hf
  simpa only [Finset.expect_image hg, Finset.card_image_of_injOn hg] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityRetained
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem fiberMean_zero (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (hr : (p.fiberLaw F).weight r = 0) (f : X → ℝ) : p.fiberMean F r f = 0 := by
  rw [fiberLaw_weight_eq_mass] at hr
  calc
    _ = p.mean (fun x => if x ∈ Finset.univ.filter (fun x => F x = r) then f x else 0) := by
      unfold fiberMean
      congr 1
      funext x
      by_cases hx : F x = r <;> simp [hx]
    _ = 0 := p.mean_mask_zero _ hr f

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSupportedComplexMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem fiberComplexMean_zero (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (hr : (p.fiberLaw F).weight r = 0) (f : X → ℂ) : p.fiberComplexMean F r f = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  calc
    ‖p.fiberComplexMean F r f‖ ≤ p.mean (fun x => ‖if F x = r then f x else 0‖) :=
      p.norm_complexMean_le_mean_norm _
    _ = p.fiberMean F r (fun x => ‖f x‖) := by
      unfold fiberMean
      apply congrArg p.mean
      funext x
      by_cases hx : F x = r <;> simp [hx]
    _ = 0 := p.fiberMean_zero F r hr _

theorem fiberComplexMean_condition_error (p : FiniteProbabilityWeights X) (F : X → R) (r : R)
    (f : X → ℂ) {target : ℂ} {ε : ℝ}
    (he : ∀ hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)),
      ‖(p.condition _ hr).complexMean f - target‖ ≤ ε) :
    ‖p.fiberComplexMean F r f - ((p.fiberLaw F).weight r : ℂ) * target‖ ≤
      (p.fiberLaw F).weight r * ε := by
  by_cases hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))
  · rw [p.fiberComplexMean_eq_condition F r f hr, p.fiberLaw_weight_eq_mass,
      ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.mass_nonneg _)]
    exact mul_le_mul_of_nonneg_left (he hr) (p.mass_nonneg _)
  · have hz : (p.fiberLaw F).weight r = 0 := by
      rw [p.fiberLaw_weight_eq_mass]
      exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
    rw [p.fiberComplexMean_zero F r hz f, hz]
    simp

theorem complexMean_supported_fiber_error (p : FiniteProbabilityWeights X) (F : X → R)
    (f : X → ℂ) (target : R → ℂ) {ε : ℝ}
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      ‖(p.condition _ hr).complexMean f - target r‖ ≤ ε) :
    ‖p.complexMean f - (p.fiberLaw F).complexMean target‖ ≤ ε := by
  have hsplit : p.complexMean f = ∑ r, p.fiberComplexMean F r f := by
    simpa only [Finset.mem_univ, ite_true] using
      (p.sum_fiberComplexMean_on F Finset.univ f).symm
  rw [hsplit, complexMean, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r, (p.fiberLaw F).weight r * ε :=
      Finset.sum_le_sum (fun r _ => p.fiberComplexMean_condition_error F r f (he r))
    _ = ε := by rw [← Finset.sum_mul, (p.fiberLaw F).total, one_mul]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedComplexSelection
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem complexMean_disintegrate_supported (p : FiniteProbabilityWeights X)
    (F : X → R) (f : X → ℂ) :
    p.complexMean f = (p.fiberLaw F).complexMean (fun r =>
      if hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)) then
        (p.condition _ hr).complexMean f else 0) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply p.complexMean_supported_fiber_error F
  intro r hr
  simp only [dif_pos hr, sub_self, norm_zero, le_refl]

theorem exists_positive_fiber_ge_complexMean_re (p : FiniteProbabilityWeights X)
    (F : X → R) (f : X → ℂ) :
    ∃ (r : R) (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      (p.complexMean f).re ≤ ((p.condition _ hr).complexMean f).re := by
  rw [p.complexMean_disintegrate_supported F f]
  obtain ⟨r, hr, hv⟩ := (p.fiberLaw F).exists_positive_weight_ge_complexMean_re
    (fun r => if hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)) then
      (p.condition _ hr).complexMean f else 0)
  rw [p.fiberLaw_weight_eq_mass] at hr
  exact ⟨r, hr, by simpa only [dif_pos hr] using hv⟩

omit [DecidableEq X] in
theorem exists_good_ge_complexMean_re_sub_bad [DecidableEq X] (p : FiniteProbabilityWeights X)
    (Good : X → Prop) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ η : ℝ} (hδ : 0 < δ) (hbad : p.eventProbability (fun x => ¬Good x) ≤ η)
    (hlarge : δ + η ≤ (p.complexMean f).re) :
    ∃ x, 0 < p.weight x ∧ Good x ∧ δ ≤ (f x).re := by
  have herr := p.complexMean_goodPart_comparison Good f (fun x _ => f x)
    (show (0 : ℝ) ≤ 0 from le_rfl) hf (fun _ _ => by simp)
  rw [zero_add] at herr
  have hre := (Complex.re_le_norm _).trans (herr.trans hbad)
  rw [Complex.sub_re] at hre
  have hgood : δ ≤ (p.complexMean (fun x => if _ : Good x then f x else 0)).re := by
    linarith only [hre, hlarge]
  obtain ⟨x, hx, hv⟩ := p.exists_positive_weight_ge_complexMean_re
    (fun x => if _ : Good x then f x else 0)
  have hselected := hgood.trans hv
  by_cases hg : Good x
  · exact ⟨x, hx, hg, by simpa only [dif_pos hg] using hselected⟩
  · simp only [dif_neg hg, Complex.zero_re] at hselected
    exact (not_le_of_gt hδ hselected).elim

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

theorem pi_weight_pos_component {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (x : ∀ j, Ω j) (hx : 0 < (pi p).weight x) (j : J) : 0 < (p j).weight (x j) := by
  apply lt_of_le_of_ne ((p j).nonneg (x j))
  intro he
  have hz : (pi p).weight x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) he.symm
  linarith

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

theorem containedProgressionCubeMap_cube (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) :
    IntegerScalarCube L (fun i => (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ)) := by
  by_cases hz : IntegerScalarCube H (fun i => (z i : ℤ))
  · simp_rw [containedProgressionCubeMap_value I L H step c hL hsubset z hz]
    exact integerScalarCube_progression c hsubset _ hz
  · simp only [containedProgressionCubeMap, dif_neg hz]
    intro t
    simp only [integerScalarCubeValue, Finset.sum_const_zero, add_zero]
    exact ⟨le_rfl, Nat.cast_pos.mpr hL⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem complexMean_pi_sum {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {X : I ⊕ J → Type*} [∀ i, Fintype (X i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (f : (∀ i, X i) → ℂ) :
    (pi p).complexMean f =
      (pi (fun i => p (.inl i))).complexMean (fun a =>
        (pi (fun j => p (.inr j))).complexMean (fun b => f (Sum.rec a b))) := by
  classical
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * f x) = _
  calc
    _ = ∑ ab : (∀ i, X (.inl i)) × (∀ j, X (.inr j)),
        ((∏ i, (p i).weight (Sum.rec ab.1 ab.2 i) : ℝ) : ℂ) *
          f (Sum.rec ab.1 ab.2) := by
      apply Fintype.sum_equiv (Equiv.sumPiEquivProdPi X)
      intro x
      have he : (fun i => Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i) = x := by
        funext i
        cases i <;> rfl
      change ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * f x =
        ((∏ i, (p i).weight (Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i) : ℝ) : ℂ) *
          f (fun i => Sum.rec (fun j => x (.inl j)) (fun j => x (.inr j)) i)
      simp only [he]
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.prod_sum_type,
        Complex.ofReal_mul, complexMean, pi, Finset.mul_sum, mul_assoc]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {K α : Type*} [Fintype K] [DecidableEq K] [Fintype α] [DecidableEq α]
variable (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
variable (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ) (L k : ℤ))

theorem containedProgressionCubeLaw_complexMean
    (f : (K → Option α → ℤ) → ℂ) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).complexMean
        (fun y => f (fun k i => (y k i : ℤ))) =
      (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (H k) (hH k))).complexMean
        (fun y => f (fun k i => (if i = none then c k else 0) + (step k : ℤ) * (y k i : ℤ))) := by
  rw [containedProgressionCubeLaw, FiniteProbabilityWeights.fiberLaw_complexMean]
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro y hy
  apply congrArg f
  funext k i
  have hpos := lt_of_le_of_ne ((FiniteProbabilityWeights.pi
    (fun k => integerScalarCubeWeights α (H k) (hH k))).nonneg y) hy.symm
  have hk := FiniteProbabilityWeights.pi_weight_pos_component
    (fun k => integerScalarCubeWeights α (H k) (hH k)) y hpos k
  have hc := (mem_integerScalarCubeSet (H k) (y k)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y k)).mp hk).1
  exact containedProgressionCubeMap_value α (L k) (H k) (step k) (c k) (hL k) (hsubset k) (y k) hc i

theorem containedProgressionCubeLaw_sum
    {G P : Type*} [Fintype G] [DecidableEq G] [Fintype P] [DecidableEq P]
    (L H step : G ⊕ P → ℕ) (c : G ⊕ P → ℤ)
    (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L k : ℤ))
    (f : (∀ k, IntegerScalarCubeBox α (L k)) → ℂ) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).complexMean f =
      (containedProgressionCubeLaw (α := α) (fun g => L (.inl g)) (fun g => H (.inl g))
        (fun g => step (.inl g)) (fun g => c (.inl g))
        (fun g => hL (.inl g)) (fun g => hH (.inl g)) (fun g => hsubset (.inl g))).complexMean
      (fun x => (containedProgressionCubeLaw (α := α) (fun j => L (.inr j)) (fun j => H (.inr j))
        (fun j => step (.inr j)) (fun j => c (.inr j))
        (fun j => hL (.inr j)) (fun j => hH (.inr j)) (fun j => hsubset (.inr j))).complexMean
        (fun y => f (Sum.rec x y))) := by
  simp only [containedProgressionCubeLaw, FiniteProbabilityWeights.fiberLaw_complexMean]
  rw [FiniteProbabilityWeights.complexMean_pi_sum]
  congr 1
  funext x
  congr 1
  funext y
  apply congrArg f
  funext k
  cases k <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B K I Y : Type*} [Fintype K] [Fintype I] [Fintype Y]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
variable (hD : 0 < selectedJointDensityMass A modulus T W D)

theorem selectedJointFiniteLaw_weighted_expectation (f : B → (K × I → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).complexMean
      (fun z => f z.1.val z.2.val) =
      (𝔼 a ∈ A, ∑' z, ((selectedResidueSmoothPMF modulus T W hW hZ z).toReal : ℂ) *
        (f a z * (D a z : ℂ))) / (selectedJointDensityMass A modulus T W D : ℂ) := by
  rw [selectedJointFiniteLaw_complexMean, FiniteProbabilityWeights.normalizedDensityTest,
    selectedJointReference_densityMass, selectedJointReference,
    FiniteProbabilityWeights.complexMean_prod]
  rw [FiniteProbabilityWeights.uniformFinset_complexMean A hA
    (fun a => (selectedResidueFiniteLaw modulus T W hW hZ).complexMean
      (fun z => (D a z.val : ℂ) * f a z.val))]
  congr 1
  apply Finset.expect_congr rfl
  intro a _
  rw [selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun z => (D a z : ℂ) * f a z)]
  apply tsum_congr
  intro z
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedRowsProjectedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {L H step : ℕ} (c : ℤ) (hL : 0 < L) (hH : 0 < H) (hstep : 0 < step)
variable (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))

include hstep in
theorem containedProgressionCubeMap_injOn :
    Set.InjOn (containedProgressionCubeMap α L H step c hL hsubset) (integerScalarCubeSet α H) := by
  intro x hx y hy hxy
  have hx' := (mem_integerScalarCubeSet H x).mp hx
  have hy' := (mem_integerScalarCubeSet H y).mp hy
  funext i
  apply Subtype.ext
  have hi := congrArg (fun z : IntegerScalarCubeBox α L => (z i : ℤ)) hxy
  rw [containedProgressionCubeMap_value α L H step c hL hsubset x hx',
    containedProgressionCubeMap_value α L H step c hL hsubset y hy'] at hi
  have hs : (step : ℤ) ≠ 0 := by exact_mod_cast hstep.ne'
  exact mul_left_cancel₀ hs (add_left_cancel hi)

theorem integerScalarCubeWeights_mean_finset (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox α L → ℝ) :
    (integerScalarCubeWeights α L hL).mean f = 𝔼 x ∈ integerScalarCubeSet α L, f x := by
  let : Nonempty (IntegerScalarCubeBox α L) := ⟨integerScalarCubeBoxZero α L hL⟩
  have h := FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet α L)
    (integerScalarCubeReference_mass_pos α L hL) f
  simpa only [integerScalarCubeWeights, integerScalarCubeReference,
    Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    Finset.sum_coe_sort, Finset.card_univ, Fintype.card_coe] using h

include hstep in
theorem containedScalarProgression_mean_le_card_ratio
    (f : IntegerScalarCubeBox α L → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ((integerScalarCubeWeights α H hH).fiberLaw
      (containedProgressionCubeMap α L H step c hL hsubset)).mean f ≤
      ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card *
        (integerScalarCubeWeights α L hL).mean f := by
  rw [FiniteProbabilityWeights.fiberLaw_mean,
    integerScalarCubeWeights_mean_finset, integerScalarCubeWeights_mean_finset]
  apply expect_injective_le_card_ratio _ _ (integerScalarCubeSet_nonempty α H hH)
    _ (containedProgressionCubeMap_injOn c hL hstep hsubset)
  · intro x _
    exact (mem_integerScalarCubeSet L _).mpr (containedProgressionCubeMap_cube α L H step c hL hsubset x)
  · intro y _
    exact hf y

include hstep in
theorem containedScalarProgression_weight_le_card_ratio (y : IntegerScalarCubeBox α L) :
    ((integerScalarCubeWeights α H hH).fiberLaw
      (containedProgressionCubeMap α L H step c hL hsubset)).weight y ≤
      ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card *
        (integerScalarCubeWeights α L hL).weight y := by
  have h := containedScalarProgression_mean_le_card_ratio c hL hH hstep hsubset
    (fun z => if z = y then 1 else 0) (fun z => by split <;> norm_num)
  simpa only [FiniteProbabilityWeights.mean, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

theorem integerScalarCubeSet_card_ratio_le {L H D : ℕ}
    (hH : 0 < H) (hsize : Fintype.card α + 1 ≤ H) (hLH : L ≤ D * H) :
    ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card ≤
      scalarCubeResidueDensityCap α D := by
  let n := Fintype.card α + 1
  let h := H / n
  have hn : 0 < n := Nat.succ_pos _
  have hh : 0 < h := Nat.div_pos hsize hn
  have hlow := integerScalarCubeSet_card_lower α H h hh (Nat.mul_div_le H n)
  have hfloor : (H : ℝ) ≤ 2 * (n : ℝ) * h := by
    exact_mod_cast nat_div_half_lower hn hsize
  have hLH' : (L : ℝ) ≤ D * (H : ℝ) := by exact_mod_cast hLH
  have hscale : 2 * (L : ℝ) ≤ (4 * (n : ℝ) * D) * h := by
    nlinarith only [hLH', mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg D)]
  have hpow := pow_le_pow_left₀ (mul_nonneg (by norm_num) (Nat.cast_nonneg L)) hscale n
  rw [mul_pow (4 * (n : ℝ) * D) (h : ℝ)] at hpow
  have hupper : ((integerScalarCubeSet α L).card : ℝ) ≤ (2 * (L : ℝ)) ^ n := by
    have h := Finset.card_le_univ (integerScalarCubeSet α L)
    rw [integerScalarCubeBox_card] at h
    exact_mod_cast h
  have hcard : 0 < ((integerScalarCubeSet α H).card : ℝ) := by
    exact_mod_cast (integerScalarCubeSet_nonempty α H hH).card_pos
  apply (div_le_iff₀ hcard).mpr
  apply (hupper.trans hpow).trans
  change (4 * (n : ℝ) * D) ^ n * (h : ℝ) ^ n ≤ _
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlow)
    (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (Nat.cast_nonneg D)) n)

theorem containedProgressionCubeLaw_eventProbability_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
    (hstep : ∀ k, 0 < step k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L k : ℤ))
    (E : (∀ k, IntegerScalarCubeBox α (L k)) → Prop) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).eventProbability E ≤
      (∏ k, ((integerScalarCubeSet α (L k)).card : ℝ) / (integerScalarCubeSet α (H k)).card) *
        (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (L k) (hL k))).eventProbability E := by
  let p := fun k => integerScalarCubeWeights α (H k) (hH k)
  let F := fun k => containedProgressionCubeMap α (L k) (H k) (step k) (c k) (hL k) (hsubset k)
  let q := fun k => (p k).fiberLaw (F k)
  have ht := FiniteProbabilityWeights.complexMean_pi_transport_fintype p q F (fun _ y => y)
    (fun k φ => ((p k).fiberLaw_complexMean (F k) φ).symm)
    (fun y => ((if E y then 1 else 0 : ℝ) : ℂ))
  have he := congrArg Complex.re ht
  simp only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re] at he
  have hlaw : (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).eventProbability E =
      (FiniteProbabilityWeights.pi q).eventProbability E := by
    unfold FiniteProbabilityWeights.eventProbability containedProgressionCubeLaw
    rw [FiniteProbabilityWeights.fiberLaw_mean]
    exact he
  rw [hlaw]
  exact FiniteProbabilityWeights.pi_eventProbability_le q
    (fun k => integerScalarCubeWeights α (L k) (hL k)) _
    (fun k y => containedScalarProgression_weight_le_card_ratio
      (c k) (hL k) (hH k) (hstep k) (hsubset k) y) E

theorem containedProgressionKernel_explicit_probability_le
    {K : Type*} [Fintype K] [DecidableEq K] [Nonempty α]
    (hK : Fintype.card α * (Fintype.card α + 2) ≤ Fintype.card K) (selection : α ↪ K)
    {L D : ℕ} {η : ℝ} (hL : 0 < L) (hD : 0 < D) (hη : 0 < η)
    (hlarge : scalarKernelCutoff α K 1 D η ≤ L)
    (H step : K → ℕ) (c : K → ℤ) (hH : ∀ k, 0 < H k) (hstep : ∀ k, 0 < step k)
    (hLH : ∀ k, L ≤ D * H k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L : ℤ)) :
    (containedProgressionCubeLaw (α := α) (fun _ => L) H step c (fun _ => hL) hH hsubset).eventProbability
      (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
        (scalarKernelCutoff α K 1 D η) x) ≤ η := by
  let C := scalarKernelConditioningConstant α K 1 D
  have hC : 0 < C := scalarKernelConditioningConstant_pos α K (by norm_num) hD
  have hsize (k) : Fintype.card α + 1 ≤ H k := by
    simpa only [Nat.mul_one] using scalarKernelCutoff_window_size α K
      (show 0 < 1 by norm_num) hD hη hlarge (hLH k)
  have hcap : (∏ k, ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α (H k)).card) ≤ C := by
    calc
      _ ≤ ∏ _k : K, scalarCubeResidueDensityCap α D := Finset.prod_le_prod
        (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (fun k _ => integerScalarCubeSet_card_ratio_le (hH k) (hsize k) (hLH k))
      _ = C := by simp only [C, scalarKernelConditioningConstant, Nat.one_mul,
          Finset.prod_const, Finset.card_univ]
  have h := containedProgressionCubeLaw_eventProbability_le (fun _ => L) H step c
    (fun _ => hL) hH hstep hsubset
    (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
      (scalarKernelCutoff α K 1 D η) x)
  apply h.trans
  calc
    _ ≤ C * (FiniteProbabilityWeights.pi (fun _ : K => integerScalarCubeWeights α L hL)).eventProbability
        (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
          (scalarKernelCutoff α K 1 D η) x) := mul_le_mul_of_nonneg_right hcap
            (FiniteProbabilityWeights.eventProbability_nonneg _ _)
    _ ≤ C * scalarKernelAdjustedAccuracy α K 1 D η := mul_le_mul_of_nonneg_left
      (scalarKernel_explicit_probability_le_of_card_le_s2 α K hK selection (by norm_num) hD hη hL hlarge) hC.le
    _ = η := by
      change C * (η / C) = η
      exact mul_div_cancel₀ η hC.ne'

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "hSides" => (Sum.rec (fun _ : G => S.positive) (allocatedPrincipalSides_pos B U b S))

variable (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
variable (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ)
variable (hsubset : ∀ k : LayerSamplerVariables G I n B,
  integerProgressionSupport (c k) (step : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ)
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k : ℕ) : ℤ))

local notation "kernelLaw" => containedProgressionCubeLaw (α := Fin dim)
  (fun _ : G => S.value) (fun g => H (Sum.inl g)) (fun _ => step) (fun g => c (Sum.inl g))
  (fun _ => S.positive) (fun g => hH (Sum.inl g)) (fun g => hsubset (Sum.inl g))
local notation "principalLaw" => containedProgressionCubeLaw (α := Fin dim)
  (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step) (fun j => c (Sum.inr j))
  (allocatedPrincipalSides_pos B U b S) (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j))

omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)]
    [∀ index, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
private theorem allocatedSlicedTupleValue_coordinates
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) :
    allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f =
    (𝔼 base ∈ bases, ∑' z,
      ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest (integerSelfSiteTest dim f)
          (physicalCubeRootDifferences
            (fun k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) none : ℤ))
            (fun j k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) (some j) : ℤ)) base z) *
          (baseDensity base z : ℂ))) /
      (selectedJointDensityMass bases stride cells widths baseDensity : ℂ) := by
  have hroot : allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y =
      (fun k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) none : ℤ)) := by
    funext k
    cases k <;> exact zero_add _
  have hdirs : allocatedPhysicalCubeDirections B U b S x y =
      (fun j k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) (some j) : ℤ)) := by
    funext j k
    cases k <;> rfl
  unfold allocatedSlicedTupleValue
  rw [hroot, hdirs]

omit [∀ index, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
theorem allocatedSlicedCubeSource_disintegrate (f : (X → ℤ) → ℂ) :
    allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f =
    (kernelLaw).complexMean (fun x => (principalLaw).complexMean (fun y =>
      allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases x y f)) := by
  let value := fun t : LayerSamplerVariables G I n B → Option (Fin dim) → ℤ =>
    (𝔼 base ∈ bases, ∑' z,
      ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest (integerSelfSiteTest dim f)
          (physicalCubeRootDifferences (fun k => t k none) (fun j k => t k (some j)) base z) *
          (baseDensity base z : ℂ))) /
      (selectedJointDensityMass bases stride cells widths baseDensity : ℂ)
  have ht := containedProgressionCubeLaw_complexMean (α := Fin dim)
    sides H (fun _ => step) c hSides hH hsubset value
  have hsource : allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f =
      (containedProgressionCubeLaw (α := Fin dim) sides H (fun _ => step) c hSides hH hsubset).complexMean
        (fun y => value (fun k i => (y k i : ℤ))) := by
    refine Eq.trans ?_ ht.symm
    unfold allocatedSlicedCubeSource
    apply congrArg (FiniteProbabilityWeights.pi
      (fun k => integerScalarCubeWeights (Fin dim) (H k) (hH k))).complexMean
    funext y
    dsimp only [value]
    have hroot : (fun k => (if (none : Option (Fin dim)) = none then c k else 0) +
        (step : ℤ) * (y k none : ℤ)) = commonStridePoint c step (fun k => (y k none : ℤ)) := rfl
    have hdir : (fun j k => (if some j = (none : Option (Fin dim)) then c k else 0) +
        (step : ℤ) * (y k (some j) : ℤ)) = (fun j k => (step : ℤ) * (y k (some j) : ℤ)) := by
      funext j k
      exact zero_add _
    rw [hroot, hdir]
  refine hsource.trans ((containedProgressionCubeLaw_sum sides H (fun _ => step) c hSides hH
    hsubset (fun y => value (fun k i => (y k i : ℤ)))).trans ?_)
  apply congrArg (kernelLaw).complexMean
  funext x
  apply congrArg (principalLaw).complexMean
  funext y
  exact (allocatedSlicedTupleValue_coordinates B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases x y f).symm

include hbases htotal in
omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedSlicedTupleValue_pathLaw
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) :
    allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f =
    (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal).complexMean (fun z =>
      physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val)) := by
  exact (selectedJointFiniteLaw_weighted_expectation bases hbases stride cells widths hwidths hmass
    baseDensity (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal _).symm

include hbases htotal in
omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedSlicedTupleValue_norm_le
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1) :
    ‖allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f‖ ≤ 1 := by
  rw [allocatedSlicedTupleValue_pathLaw B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal]
  let law := allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal
  apply (law.norm_complexMean_le_mean_norm _).trans
  exact (law.mean_mono (fun _ => physicalCubeSiteTest_norm_le _
    (integerSelfSiteTest_norm_le dim f hf) _)).trans_eq (law.mean_const 1)

include hbases htotal in

theorem allocatedSlicedCubeSource_good_residue_selection
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1)
    (Good : (G → IntegerScalarCubeBox (Fin dim) S.value) → Prop)
    {δ η : ℝ} (hδ : 0 < δ)
    (hbad : (kernelLaw).eventProbability (fun x => ¬Good x) ≤ η)
    (hlarge : δ + η ≤ (allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re)
    (q : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℕ) [∀ x, NeZero (q x)] :
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value),
      0 < (kernelLaw).weight x ∧ Good x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (q x))
      (hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r))),
      δ ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
        (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j)) (q x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  let value := fun x y => allocatedSlicedTupleValue (dim := dim) B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases x y f
  have hbound (x) : ‖(principalLaw).complexMean (value x)‖ ≤ 1 := by
    apply ((principalLaw).norm_complexMean_le_mean_norm _).trans
    exact ((principalLaw).mean_mono (fun y => allocatedSlicedTupleValue_norm_le B U b hb o hR hσ S
      X poly hmem N hN hW hτ hξ stride cells hmass bases hbases htotal x y f hf)).trans_eq
        ((principalLaw).mean_const 1)
  rw [allocatedSlicedCubeSource_disintegrate B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases H hH c step hsubset] at hlarge
  obtain ⟨x, hx, hg, hv⟩ := (kernelLaw).exists_good_ge_complexMean_re_sub_bad Good
    (fun x => (principalLaw).complexMean (value x)) hbound hδ hbad hlarge
  let raw := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))
  let transport := containedProgressionTupleMap (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
    (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S) (fun j => hsubset (Sum.inr j))
  have hraw : raw.complexMean (fun y => value x (transport y)) =
      (principalLaw).complexMean (value x) :=
    (raw.fiberLaw_complexMean transport (value x)).symm
  obtain ⟨r, hr, hc⟩ := raw.exists_positive_fiber_ge_complexMean_re
    (principalResidueLabel (q x)) (fun y => value x (transport y))
  refine ⟨x, hx, hg, r, hr, ?_⟩
  have hcond := (raw.condition (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r)) hr).fiberLaw_complexMean
    transport (value x)
  exact ((hv.trans_eq (congrArg Complex.re hraw.symm)).trans hc).trans_eq
    (congrArg Complex.re hcond.symm)

include hbases htotal in

theorem allocatedSlicedCubeSource_good_kernel_residue_s2_oai
    [Nonempty (Fin dim)]
    (selection : Fin dim ↪ G) (hG : dim * (dim + 2) ≤ Fintype.card G)
    {D : ℕ} (hD : 0 < D) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hkernel : scalarKernelCutoff (Fin dim) G 1 D η ≤ S.value)
    (hstep : 0 < step) (hLH : ∀ g, S.value ≤ D * H (Sum.inl g))
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1)
    (hlarge : δ + η ≤ (allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re)
    (q : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℕ) [∀ x, NeZero (q x)] :
    let Mk := scalarKernelCutoff (Fin dim) G 1 D η
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value),
      0 < (kernelLaw).weight x ∧ GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (q x))
      (hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r))),
      δ ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
        (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j)) (q x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  intro Mk
  have hbad := containedProgressionKernel_explicit_probability_le
    (by simpa only [Fintype.card_fin] using hG) selection S.positive hD hη hkernel
    (fun g => H (Sum.inl g)) (fun _ => step) (fun g => c (Sum.inl g))
    (fun g => hH (Sum.inl g)) (fun _ => hstep) hLH (fun g => hsubset (Sum.inl g))
  exact allocatedSlicedCubeSource_good_residue_selection B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H hH c step hsubset f hf
    (GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk) hδ hbad hlarge q

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSlicedCubeSource_good_kernel_residue_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSlicedCubeSource_good_kernel_residue_s2_oai.{u_1, u_2, u_3, u_4, u_5}
