-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:48:11.801343+00:00
-- url     : https://prove2.me/submissions/682c5fb2-c6f2-4e5c-b970-fc736032a234

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B252
import Definitions.Def_OAIE3v2B262
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_uniform_budget_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_relativePatchSliceConclusion_of_primitive_retained_forecast_score_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactive_sliced_fixed_grid_mass_le_s2
import Theorems.Thm_OAI_Erdos3_fixedSpatialKernelDensity_probability_density_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedIntervalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory _root_.Set

theorem intervalWindow_mem_Icc (a b t : ℝ) : intervalWindow a b t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ Ioc a b <;> simp [intervalWindow, ht]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3


open scoped BigOperators

theorem integerScalarCubeWeights_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L : ℕ) (hL : 0 < L) (f : IntegerScalarCubeBox I L → ℝ) :
    (integerScalarCubeWeights I L hL).mean f = 𝔼 x : integerScalarCubeSet I L, f x := by
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  exact FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) f

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_nonneg (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (x : (Σ d, I d) → ℝ) : 0 ≤ sigmaAxisWeight w x :=
  tensorCutoffWeight_nonneg w hw _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_toReal (p : FiniteProbabilityWeights X) (x : X) :
    (p.toPMF x).toReal = p.weight x := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.complexMean_im {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (F : X → ℂ) :
    (p.complexMean F).im = p.mean (fun x => (F x).im) := by
  simp [complexMean, mean, Complex.mul_im]

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerBoxZeroCube
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem FiniteProbabilityWeights.pi_uniform_complexMean
    {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (f : (∀ i, A i) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (A i))).complexMean f =
      𝔼 x, f x := by
  change (∑ x : ∀ i, A i, ((∏ i, (Fintype.card (A i) : ℝ)⁻¹ : ℝ) : ℂ) * f x) = _
  have hcard : (∏ i, (Fintype.card (A i) : ℝ)⁻¹) =
      (Fintype.card (∀ i, A i) : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    simp only [Fintype.card_pi, Nat.cast_prod]
  rw [hcard]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped Classical NNReal

theorem FiniteProbabilityWeights.toPMF_injective {X : Type*} [Fintype X] :
    Function.Injective (fun p : FiniteProbabilityWeights X => p.toPMF) := by
  intro p q hpq
  change p.toPMF = q.toPMF at hpq
  have hw : p.weight = q.weight := by
    funext x
    exact (FiniteProbabilityWeights.toPMF_toReal p x).symm.trans
      ((congrArg (fun μ : PMF X => (μ x).toReal) hpq).trans
        (FiniteProbabilityWeights.toPMF_toReal q x))
  cases p
  cases q
  cases hw
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)

variable (hH : ∀ j, 0 < H j)

theorem principalAffineIntervalLaw_mean (f : PrincipalIntegerTuples B h Empty L → ℝ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).mean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalAffineIntervalPoint B h L H step start hinside t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

private theorem zeroScalar_fin_mean (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox Empty L → ℝ) :
    (integerScalarCubeWeights Empty L hL).mean f = 𝔼 t : Fin L, f (zeroScalarFinPoint L t) := by
  rw [integerScalarCubeWeights_mean]
  apply Fintype.expect_equiv
    ((zeroScalarCubeIntervalEquiv Empty L).trans (finIntegerIntervalEquiv L).symm)
  intro x
  congr 1
  funext a
  apply Subtype.ext
  cases a with
  | none =>
    have hx := ((mem_integerScalarCubeSet L x.val).mp x.property) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hx
    exact (Int.toNat_of_nonneg hx.1).symm
  | some a => exact isEmptyElim a

theorem zeroScalar_fin_complexMean (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox Empty L → ℂ) :
    (integerScalarCubeWeights Empty L hL).complexMean f =
      𝔼 t : Fin L, f (zeroScalarFinPoint L t) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  rw [← FiniteProbabilityWeights.uniform_complexMean]
  apply Complex.ext
  · simpa only [FiniteProbabilityWeights.complexMean_re, FiniteProbabilityWeights.uniform_mean]
      using zeroScalar_fin_mean L hL (fun z => (f z).re)
  · simpa only [FiniteProbabilityWeights.complexMean_im, FiniteProbabilityWeights.uniform_mean]
      using zeroScalar_fin_mean L hL (fun z => (f z).im)

theorem integerScalarCubeWeights_pi_fin_complexMean
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : X → ℕ) (hH : ∀ i, 0 < H i)
    (f : (∀ i, IntegerScalarCubeBox Empty (H i)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights Empty (H i) (hH i))).complexMean f =
      𝔼 t : (∀ i, Fin (H i)), f (fun i => zeroScalarFinPoint (H i) (t i)) := by
  let : ∀ i, Nonempty (Fin (H i)) := fun i => ⟨⟨0, hH i⟩⟩
  have htransport := FiniteProbabilityWeights.complexMean_pi_transport_fintype
    (fun i => integerScalarCubeWeights Empty (H i) (hH i))
    (fun i => FiniteProbabilityWeights.uniform (Fin (H i)))
    (fun _ x => x) (fun i => zeroScalarFinPoint (H i))
    (fun i g => (zeroScalar_fin_complexMean (H i) (hH i) g).trans
      (FiniteProbabilityWeights.uniform_complexMean _).symm) f
  exact htransport.trans (FiniteProbabilityWeights.pi_uniform_complexMean _)

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

theorem principalTupleWeights_fin_complexMean (f : PrincipalIntegerTuples B h Empty H → ℂ) :
    (principalTupleWeights (α := Empty) B h H hH).complexMean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalFinTuplePoint B h H t) := by
  exact integerScalarCubeWeights_pi_fin_complexMean H hH f

theorem principalTupleWeights_fin_mean (f : PrincipalIntegerTuples B h Empty H → ℝ) :
    (principalTupleWeights (α := Empty) B h H hH).mean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalFinTuplePoint B h H t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  have he := congrArg Complex.re (principalTupleWeights_fin_complexMean B h H hH (fun z => (f z : ℂ)))
  rw [← FiniteProbabilityWeights.uniform_complexMean] at he
  simpa only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re,
    FiniteProbabilityWeights.uniform_mean] using he

variable (L step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hsubset : ∀ j, integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
theorem containedProgressionTupleMap_finPoint [Fintype D] [DecidableEq D]
    [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)]
    (t : ∀ j, Fin (H j)) :
    containedProgressionTupleMap B h L H step start hL hsubset (principalFinTuplePoint B h H t) =
      principalAffineIntervalPoint B h L H step start hinside t := by
  funext j a
  apply Subtype.ext
  have hc : IntegerScalarCube (H j) (fun a => (principalFinTuplePoint B h H t j a : ℤ)) := by
    intro row
    have he : row = ∅ := Subsingleton.elim _ _
    simp only [he, integerScalarCubeValue, Finset.sum_empty, add_zero,
      principalFinTuplePoint, zeroScalarFinPoint]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (t j).isLt⟩
  rw [containedProgressionTupleMap,
    containedProgressionCubeMap_value Empty _ _ _ _ _ _ _ hc]
  cases a with
  | none => rfl
  | some a => exact isEmptyElim a

theorem principalAffineIntervalLaw_eq_contained :
    principalAffineIntervalLaw B h L H step start hinside hH =
      (principalTupleWeights (α := Empty) B h H hH).fiberLaw
        (containedProgressionTupleMap B h L H step start hL hsubset) := by
  have he (f : PrincipalIntegerTuples B h Empty L → ℝ) :
      (principalAffineIntervalLaw B h L H step start hinside hH).mean f =
        ((principalTupleWeights (α := Empty) B h H hH).fiberLaw
          (containedProgressionTupleMap B h L H step start hL hsubset)).mean f := by
    rw [principalAffineIntervalLaw_mean, FiniteProbabilityWeights.fiberLaw_mean,
      principalTupleWeights_fin_mean]
    apply Finset.expect_congr rfl
    intro t _
    rw [containedProgressionTupleMap_finPoint B h H L step start hL hinside hsubset]
  apply FiniteProbabilityWeights.toPMF_injective
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [FiniteProbabilityWeights.toPMF_toReal, FiniteProbabilityWeights.toPMF_toReal]
  simpa [FiniteProbabilityWeights.mean] using he (fun y => if y = z then 1 else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR hσ in
theorem allocatedOriginalSampleInactiveCoefficients_supported
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) :
    ∀ a d, allocatedOriginalSampleInactiveCoefficients B selected sample a d ∈
      (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2 d).support := by
  intro a d
  exact ((mixedArraySupported_iff_rows _ _ _ (sample (selected a).1)).mp
    (hs (selected a).1)).2 (selected a).2 d

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem principalLaw_eq_contained :
    slice.principalLaw =
      (principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
        slice.principalLength slice.principalLength_pos).fiberLaw
      (containedProgressionTupleMap B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) slice.principalLength slice.principalStep
        slice.principalStart (allocatedPrincipalSides_pos B U b S) slice.principalSupport) := by
  exact principalAffineIntervalLaw_eq_contained B (layerSamplerDegree I n)
    slice.principalLength slice.principalLength_pos (allocatedPrincipalSides B U b S)
    slice.principalStep slice.principalStart (allocatedPrincipalSides_pos B U b S)
    slice.principalInside slice.principalSupport

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ActualSlicedNumericsRecoveredBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

omit [DecidableEq X] [Fintype A] in
theorem actualSlicedForecastDensityBudget_ge_one (v : ℝ) :
    1 ≤ actualSlicedForecastDensityBudget s v := by
  apply Real.one_le_exp_iff.mpr
  unfold forecastOriginalSmoothBudget
  positivity

namespace ActualFixedSpatialSlicedForecastNumerics

variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

omit [DecidableEq X] in

theorem joint_density_grid_cap_le_exp :
    s.κ * actualSlicedForecastDensityBudget s qnum.v * qnum.Ctail ^ Fintype.card A ≤
      Real.exp qnum.capLog := by
  have hbase : 0 ≤ s.κ * actualSlicedForecastDensityBudget s qnum.v *
      qnum.Ctail ^ Fintype.card A :=
    mul_nonneg (mul_nonneg s.hκ (Real.exp_nonneg _)) (pow_nonneg qnum.hCtail _)
  have hdecay : 0 ≤ actualSlicedForecastDecayBudget s := Real.exp_nonneg _
  apply le_trans _ qnum.hcap
  nlinarith

omit [DecidableEq X] in

theorem spatial_inverse_factor_le_exp : 8 / τ ≤ Real.exp qnum.Pnative := by
  have hD := actualSlicedForecastDensityBudget_ge_one s qnum.v
  have htail : 0 ≤ (Fintype.card A : ℝ) * (qnum.Lt : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) qnum.Lt.coe_nonneg
  have hmax : 0 ≤ max (8 / τ) 1 := zero_le_one.trans (le_max_right _ _)
  calc
    _ ≤ max (8 / τ) 1 := le_max_left _ _
    _ ≤ (actualSlicedForecastDensityBudget s qnum.v +
        (Fintype.card A : ℝ) * (qnum.Lt : ℝ)) * max (8 / τ) 1 := by nlinarith
    _ ≤ _ := qnum.hfactor

end ActualFixedSpatialSlicedForecastNumerics
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedInactiveGridCap
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

namespace ActualFixedSpatialSlicedForecastPath

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)

omit [Fintype Tsp] in

theorem inactive_grid_mass_le
    (δ : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : s.Pcap ≤ Ptail)
    (hstrideTail : ∀ a i v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ) ≤ Ptail)
    (hCtail : 0 ≤ Ctail)
    (htailactual : ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree Ptail V V) ≤ Ctail)
    (z : A → ℤ) :
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      slice.principalLaw.fiberMean
        (forecastInactiveFixedOutput B U b S selected
          (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample)
          slice.path.commonTuple)
        (fun a _ => z a) (fun _ => 1) ≤ Ctail ^ Fintype.card A := by
  have hgrid (a : A) : allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
    exact (s.hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  have hc := allocatedOriginalSampleInactiveCoefficients_supported
    B selected U b hR hσ S slice.path.sample slice.path.hs
  rw [slice.principalLaw_eq_contained]
  exact forecastInactive_sliced_fixed_grid_mass_le_s2 B U b hR hσ S
    slice.principalLength slice.principalStep slice.principalStart slice.principalLength_pos
    slice.principalSupport selected s.hselected δ Ptail Hchild hδ hreg s.hsmall hgrid
    (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) hc
    s.L s.hL hPtail (s.hprimitiveCap.trans hsPtail) hstrideTail s.hB
    Ctail hCtail htailactual slice.path.commonTuple z

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedNumericalGridCap
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

omit [Fintype Tsp] in

theorem inactive_grid_mass_le (z : A → ℤ) :
    (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
      member.slice.principalLaw.fiberMean
        (forecastInactiveFixedOutput B U b S selected
          (allocatedOriginalSampleInactiveCoefficients B selected member.slice.path.sample)
          member.slice.path.commonTuple)
        (fun a _ => z a) (fun _ => 1) ≤ qnum.Ctail ^ Fintype.card A := by
  exact member.slice.inactive_grid_mass_le s qnum.δ qnum.Hchild qnum.hδ member.regular
    qnum.Ptail qnum.Ctail qnum.hPtail qnum.hprimitive member.stride qnum.hCtail qnum.htailactual z

end ActualFixedSpatialSlicedAdmissiblePath

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialSlicedNumericalDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem SlicedProductBlock.pairDensity_nonneg {ι : Type*} [Fintype ι]
    (A B : SlicedProductBlock ι) (x : ℝ) : 0 ≤ SlicedProductBlock.pairDensity A B x := by
  unfold pairDensity affinePairDensity randomIntervalDensity densityMixture
  apply integral_nonneg
  intro p
  unfold normalizedIntervalWindow affinePairWidth
  exact div_nonneg (intervalWindow_mem_Icc _ _ _).1
    (le_max_of_le_left (abs_nonneg _))

theorem SlicedProductBlock.fourDensity_nonneg {ι : Type*} [Fintype ι]
    (A B C D : SlicedProductBlock ι) (x : ℝ) :
    0 ≤ SlicedProductBlock.fourDensity A B C D x := by
  unfold fourDensity scalarDensityConvolution
  exact integral_nonneg (fun t =>
    mul_nonneg (pairDensity_nonneg A B _) (pairDensity_nonneg C D _))

theorem principalFourRemainderDensity_nonneg {J ι : Type*}
    [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]
    (c : Fin 4 ⊕ J → ℝ) (lower width : (Fin 4 ⊕ J) × Option ι → ℝ) (x : ℝ) :
    0 ≤ principalFourRemainderDensity c lower width x := by
  unfold principalFourRemainderDensity independentShiftDensity densityMixture
  exact integral_nonneg (fun t => SlicedProductBlock.fourDensity_nonneg _ _ _ _ _)

theorem canonicalSlicedPrincipalDensity_nonneg {B F : Type*}
    [Fintype B] [Fintype F] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ)
    (lower width : B × F → ℝ) (x : ℝ) :
    0 ≤ canonicalSlicedPrincipalDensity hB i c lower width x :=
  principalFourRemainderDensity_nonneg _ _ _ _

theorem jointSlicedPrincipalDensity_nonneg {D : Type*} [Fintype D]
    {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    (hB : ∀ d, 4 ≤ Fintype.card (B d)) (i : ∀ d, F d)
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
    (shift : D → ℝ) (y : (Σ _d : D, Unit) → ℝ) :
    0 ≤ jointSlicedPrincipalDensity hB i c lower width shift y := by
  exact sigmaAxisWeight_nonneg _
    (fun d v => canonicalSlicedPrincipalDensity_nonneg (hB d) (i d)
      (c d) (lower d) (width d) _) y

end Erdos3

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

theorem density_nonneg
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    0 ≤ slice.density hBactive y := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  classical
  unfold density fixedSpatialKernelSliceOriginalForecastDensity
    fixedSpatialKernelOriginalForecastDensity binaryDensity allocatedFixedPathLiftDensity
  apply mul_nonneg
  · exact (fixedSpatialKernelDensity_probability_density_s2 _ _ _ _ _ _).1 _
  · exact jointSlicedPrincipalDensity_nonneg _ _ _ _ _ _ _

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

theorem density_mem_Icc
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    member.slice.density s.hBactive y ∈
      Set.Icc (0 : ℝ) (actualSlicedForecastDensityBudget s qnum.v) := by
  have hbound := (member.slice.density_uniform_budget_s2 s.hBactive s.hP s.hδslice
    s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks qnum.hv member.kernelWidth).2.2.1 y
  have hn := member.slice.density_nonneg s.hBactive y
  rw [Real.norm_eq_abs, abs_of_nonneg hn] at hbound
  exact ⟨hn, hbound⟩

theorem density_lipschitz :
    LipschitzWith (Real.toNNReal (actualSlicedForecastDensityBudget s qnum.v))
      (member.slice.density s.hBactive) :=
  (member.slice.density_uniform_budget_s2 s.hBactive s.hP s.hδslice
    s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks qnum.hv member.kernelWidth).2.2.2

theorem density_lipschitz_nnreal :
    LipschitzWith
      (⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩ : ℝ≥0)
      (member.slice.density s.hBactive) := by
  have hbudget : Real.toNNReal (actualSlicedForecastDensityBudget s qnum.v) =
      (⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩ : ℝ≥0) := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ (Real.exp_nonneg _)
  rw [← hbudget]
  exact member.density_lipschitz s qnum

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialNumericalPatchEndpoint
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem relativePatchSliceConclusion_of_numerical_retained_forecast_score_s2_oai
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    {degree r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ degree) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) degree E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (member.slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (member.slice.path.referenceRetainedCRTModulus cutoff : ℤ) ∣ M i a)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (member.slice.targetAt selected s.hBactive o bW hb poly hm s.κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (member.slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hr : (r : ℝ) ≤ budget) (hE : (E : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hKbudget : (K : ℝ) ≤ Real.exp budget)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp budget)
    (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hqbudget : (member.slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion degree physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  let D : ℝ≥0 := ⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩
  let Icap : ℝ≥0 := ⟨qnum.Ctail ^ Fintype.card A, pow_nonneg qnum.hCtail _⟩
  have hN (i : X) : 0 < physicalN i := Nat.cast_pos.mp
    ((Real.exp_pos (spatialPatchExtractionCost (recoveredKernelScalarBudget budget))).trans_le
      (hlarge i))
  have hXnat : Fintype.card X ≤ Dmod :=
    (Nat.le_add_right (Fintype.card X) _).trans s.hDmod
  have hX : (Fintype.card X : ℝ) ≤ budget := (Nat.cast_le.mpr hXnat).trans hDmodBudget
  have hOutNat : Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) ≤ Dmod := by
    rw [Fintype.card_sigma]
    exact (allocatedCongruenceRankOutput_sum_card_le (X := X) (E := Eout)
      s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
  have hOut : (Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) : ℝ) ≤ budget :=
    (Nat.cast_le.mpr hOutNat).trans hDmodBudget
  exact member.slice.relativePatchSliceConclusion_of_primitive_retained_forecast_score_s2
    selected s.hBactive o bW hb e s.hm s.hDmod cutoff hcutoff hsmall ⟨s.κ, s.hκ⟩
    poly hm hN w hw hws hmono Pscalar hP p Bpatch χ M K hM hweight hcoords hcol hdiv
    D Icap (member.density_mem_Icc s qnum) (member.density_lipschitz_nnreal s qnum)
    (member.inactive_grid_mass_le s qnum) s.forward s.hforward s.K s.hK s.hτ f hf
    hlam hδ haccuracy hε hdiscount hscore hbudget hr hE hX hOut
    hKbudget hχbudget hBbudget
    ((qnum.joint_density_grid_cap_le_exp s).trans (Real.exp_le_exp.mpr hcapLog))
    hqbudget (qnum.hcoord.trans (Real.exp_le_exp.mpr hPnative))
    ((qnum.spatial_inverse_factor_le_exp s).trans (Real.exp_le_exp.mpr hPnative))
    hscoreLower hlarge hrank

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedAdmissiblePath.relativePatchSliceConclusion_of_numerical_retained_forecast_score_s2_oai
