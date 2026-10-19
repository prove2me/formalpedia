-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_actualSlicedForecast_late_data_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:41:45.631776+00:00
-- url     : https://prove2.me/submissions/5bf157ef-f2fd-4e51-9977-c5ac0a7e96d8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B197
import Definitions.Def_OAIE3v2B244
import Definitions.Def_OAIE3v2B245
import Definitions.Def_OAIE3v2B247
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_active_support_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_bounds_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_density_uniform_budget_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_target_norm_le_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedForecastPolynomial_crt_decay_of_bad_product_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastDensityBufferedNativeExpansion_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalTarget_cutoff_of_active_support_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

theorem restrictedComplexChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedComplexChartDensity q S c f (q x) = (c : ℂ) * f x := by
  have he : Function.Injective (fun x : S => q x.val) := fun a b h => Subtype.ext (hinj a.property b.property h)
  exact congrArg (fun z : ℂ => (c : ℂ) * z) (he.extend_apply (fun x => f x.val) (fun _ => 0) ⟨x, hx⟩)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

theorem modularForecastRankConstant_decay (s D : ℕ) :
    modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) = (D + 2 : ℕ) := by
  unfold modularRankDecayExponent modularForecastRankConstant
  push_cast
  have htwo : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem modularForecastRankConstant_dimension (s D d : ℕ) (hd : d ≤ D) :
    ((d + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) := by
  rw [modularForecastRankConstant_decay]
  exact_mod_cast Nat.add_le_add_right hd 2

end Erdos3

end

section

namespace Erdos3

theorem forecastModularCharge_exp_bound (m D Rbad Qpres : ℕ)
    {Pbad Ppres : ℝ} (hR : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hQ : (Qpres : ℝ) ≤ Real.exp Ppres) :
    ((Rbad * Qpres : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) *
        modularRankChargeFactor m) ≤
      Real.exp ((Pbad + Ppres) * ((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) := by
  rw [modularForecastRankConstant_decay]
  have hbase : ((Rbad * Qpres : ℕ) : ℝ) ≤ Real.exp (Pbad + Ppres) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hR hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ (Real.exp (Pbad + Ppres)) ^
        (((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hbase (by positivity)
    _ = _ := by rw [← Real.exp_mul, mul_assoc]

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelLiftChart
namespace OAI

section

namespace Erdos3

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) (s : X → G) (q : X → H)

theorem kernelLiftChart_injOn (hproj : ∀ x, C (s x) = q x)
    {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × C.ker => s p.1 + p.2.val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  change s x.1 + x.2.val = s y.1 + y.2.val at he
  have hkx : C x.2.val = 0 := x.2.property
  have hky : C y.2.val = 0 := y.2.property
  have hb : q x.1 = q y.1 := by
    have ht := congrArg C he
    simpa only [map_add, hproj, hkx, hky, add_zero] using ht
  have hxy : x.1 = y.1 := hq hx.1 hy.1 hb
  apply Prod.ext hxy
  apply Subtype.ext
  rw [hxy] at he
  exact add_left_cancel he

theorem kernelLiftChart_relabel_injOn {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × R => s p.1 + (e p.2).val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  have hp := kernelLiftChart_injOn C s q hproj hq
    (show (x.1, e x.2) ∈ S ×ˢ Set.univ from ⟨hx.1, Set.mem_univ _⟩)
    (show (y.1, e y.2) ∈ S ×ˢ Set.univ from ⟨hy.1, Set.mem_univ _⟩) he
  exact Prod.ext (congrArg (fun z : X × C.ker => z.1) hp)
    (e.injective (congrArg (fun z : X × C.ker => z.2) hp))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_injOn
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedCoveredChart W b hb bW d)
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) :=
  kernelLiftChart_relabel_injOn _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)))
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) := by
  intro x hx y hy he
  funext j t
  exact normalizedCoveredChart_injOn _ (b j) (hb j) (bW j) d (hΩ j t)
    (hx j (Set.mem_univ j) t (Set.mem_univ t)) (hy j (Set.mem_univ j) t (Set.mem_univ t))
    (congrFun (congrFun he j) t)

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (mixedCoveredJetChart U o b hb bW d) (mixedCoveredJetRegion U o b d Ω) := by
  intro z hz w hw he
  apply (mixedCoveredJetCoordinatesEquiv U o d).injective
  exact coveredJetChart_injOn U b hb bW d Ω hΩ hz hw he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)

theorem commonSitePeriod_le_pow {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    {D : ℝ} (hD : ∀ a, V a ≤ D) (k : ∀ a, (e a).Term) :
    (commonSitePeriod e k : ℝ) ≤ D ^ Fintype.card A := by
  rw [commonSitePeriod, Nat.cast_prod]
  calc
    _ ≤ ∏ _a : A, D := Finset.prod_le_prod (fun a _ => Nat.cast_nonneg _)
      (fun a _ => ((he a).period_le (k a)).trans (hD a))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalSiteProjection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem physicalSingleSiteValue_eq_mk (d : ℕ) (w : X → ℝ) (j : Fin m) :
    physicalSingleSiteValue U d p hm w j () =
      QuotientAddGroup.mk ((d : ℝ)⁻¹ • physicalEuclideanSitePoint U p hm w j) := by
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  change euclideanSubspaceTorusEquiv (U j)
    ((euclideanSubspaceTorusEquiv (U j)).symm _) =
      euclideanSubspaceTorusEquiv (U j) (QuotientAddGroup.mk' _
        ((d : ℝ)⁻¹ • physicalEuclideanSitePoint U p hm w j))
  rw [AddEquiv.apply_symm_apply, euclideanSubspaceTorusEquiv_mk]
  congr 1

end Erdos3.BooleanCubeKernel

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

omit [∀ j, Fintype (I j)] in

theorem allocatedCongruenceForecastRankConstant_dimension
    (hm : 0 < m) (D : ℕ)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D) :
    ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) := by
  apply modularForecastRankConstant_dimension
  rw [Fintype.card_sigma]
  exact (allocatedCongruenceRankOutput_sum_card_le hm inactive).trans hD

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPhysicalQuarterRecovery
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D E : Type*} [Fintype D] [Fintype E] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedCoveredChart_of_integer_deck
    (M : ℕ) [NeZero M] (u : W) (x : W × (Fin n → ℤ)) (deck : E → ℤ)
    (hdeck : normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm deck).val = u) :
    (QuotientAddGroup.mk ((M : ℝ)⁻¹ • u) : W ⧸
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
        normalizedCoveredChart W b hb bW M (x, integerResidueMap E M deck) := by
  have h := normalizedCoverLift_add_deck W bW b hb M (NeZero.pos M) x deck
  rw [hdeck] at h
  exact h.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastDensityPhysicalApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem forecastPhysicalBufferedCoefficientMass
    {T : Type*} [Fintype T] (coefficient : T → ℂ) {mass : ℝ}
    (hmass : (∑ t, ‖coefficient t‖) ≤ mass) :
    (∑ t, ‖(2 : ℂ) * coefficient t‖) ≤ 2 * mass := by
  calc
    _ = ∑ t, 2 * ‖coefficient t‖ := by norm_num [norm_mul]
    _ = 2 * ∑ t, ‖coefficient t‖ := (Finset.mul_sum ..).symm
    _ ≤ 2 * mass := mul_le_mul_of_nonneg_left hmass (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

local notation "deckSource" => forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

local notation "target" => forecastLawDensityPhysicalTarget B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawDensityPhysicalTarget_integer_deck
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    target poly hpoly u = deckSource u w deck := by
  let z : MixedCoveredJetSource I single Eout n N :=
    (fun j => (fun i _ => (w j).1 i, fun i _ => (w j).2 i),
      fun j _ => integerResidueMap (Eout j) N (deck j))
  have hz : z ∈ region := by
    intro j _ t _
    exact ⟨hquarter j, Set.mem_univ _⟩
  have hchart : chart z = physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)) := by
    funext j t
    cases t
    rw [physicalSingleSiteValue_eq_mk]
    exact (normalizedCoveredChart_of_integer_deck (euclideanSubspace (U j))
      (bW j) (basis j) (hb j) N _ (orthonormalMixedChart (o j) (w j))
      (deck j) (hdeck j)).symm
  unfold forecastLawDensityPhysicalTarget
  rw [← hchart, restrictedComplexChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o basis hb bW N _
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
    Complex.ofReal_one, one_mul]
  have houtput : (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (fun i => (((deck j i : ZMod N).val : ℕ) : ℤ)))
        output : ZMod N)) =
      (fun output => (forecastCongruenceOutput (R := ℤ) short u
        (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N)) := by
    funext output
    rcases output with ⟨j, a | a | a⟩
    · rfl
    · simpa only [forecastCongruenceOutput, Sum.elim_inr, Int.cast_natCast]
        using ZMod.natCast_zmod_val (deck j a : ZMod N)
    · rfl
  change deckSource u w (fun j i => ((deck j i : ZMod N).val : ℤ)) = _
  unfold forecastLawDensityPhysicalDeckSource
  rw [houtput]

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

private theorem forecast_density_physical_atom_reassociate_p1 (d c f h : ℂ) :
    d * c * f / h = (c * (d / h)) * f := by ring

theorem forecastLawDensityPhysicalApproximation
    {Term Site : Type*} [Fintype Term]
    (χ : Term → AddChar (Out → ZMod N) ℂ)
    (e : Term → A → ScalarSiteExpansion Site) (k : ∀ t a, (e t a).Term) (site : Site)
    (coefficient : Term → ℂ) (cap : ℝ≥0) {ε : ℝ}
    (herror : ∀ (z : A → ℤ) (out : Out → ZMod N)
        (y : ((Spatial → ℝ) × (Active → ℝ))),
      ‖(density y : ℂ) * (rationalInactiveForecast law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N volume (fun a _ => z a) out : ℂ) -
        ∑ t, coefficient t * ((star (χ t out) * ((density y : ℂ) /
          (((cap : ℝ) + 1 : ℝ) : ℂ))) *
          siteFamilyFactor (e t) (k t) site
            (fun a => (z a : ZMod ((e t a).period (k t a))))
            (fun a => (z a : ℝ) / basisAxisScale (basis (selected a).1) (selected a).2))‖ ≤ ε)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hdeck : ∀ j, normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
      (orthonormalMixedChart (o j) (w j)) + ((bW j).equivFun.symm (deck j)).val =
        physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j)
    (hquarter : ∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
      (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4) :
    ‖forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume
        base physicalN τ o hb bW poly hpoly u -
      ∑ t, coefficient t * forecastDensityNormalizedAtom B U basis S density cap selected
        (χ t) (e t) (k t) site base physicalN τ u deck w‖ ≤ ε := by
  rw [forecastLawDensityPhysicalTarget_integer_deck B U basis S law density selected sample x active Y
    N volume base physicalN τ o hb bW poly hpoly u w deck hdeck hquarter]
  have h := herror (fun a => (w (selected a).1).2 (selected a).2)
    (fun output => (forecastCongruenceOutput (R := ℤ) short u
      (fun j => Sum.elim (w j).2 (deck j)) output : ZMod N))
    ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w))
  simpa only [forecastLawDensityPhysicalDeckSource, forecastDensityNormalizedAtom,
    forecast_density_physical_atom_reassociate_p1] using h

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualSlicedForecastLateData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact : Type*} [Fintype Vact] [DecidableEq Vact]
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedSeparateTailCharOrderNeZero
theorem exists_forecastInactive_sliced_separateTail_native_source
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
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
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    (density : ((Spatial → ℝ) × (Active → ℝ)) → ℝ)
    (cap lip : ℝ≥0) (hbound : ∀ y, |density y| ≤ (cap : ℝ))
    (hLips : LipschitzWith lip density)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (hR1 : ∀ a, R (selected a).1 ≤ 1)
    (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ) (hτ : 0 < τ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) w‖ ≤ forward j * ‖w‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (radius : ℝ≥0) (hr : 0 < radius) (hr3 : (3 : ℝ) ≤ radius)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm w‖ ≤ inverse j * ‖w‖)
    (hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    let Hdensity : ℝ := (cap : ℝ) + 1
    let Lspatial : ℝ≥0 := max ⟨8 / τ, by positivity⟩ 1
    let Lfactor := (lip + Fintype.card A * Lt) * Lspatial
    let Lcoord := K * ∑ j, forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * radius)) * Lcoord
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
      (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      ∃ twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩,
        (∀ t, (twists t).modulus = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 ∧
          (twists t).cover = orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2) ∧
        (∑ t : Term, ‖(2 : ℂ) * coeff t‖) ≤
          2 * Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
        ∀ (x : G → IntegerScalarCubeBox Empty S.value)
          (physicalPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hphysical : ∀ j v, coefficients (physicalPoly j) v ∈ U j) (u : X → ℤ),
          ‖forecastLawDensityPhysicalTarget B U basis S law density selected sample x (fun _ => pRat)
            (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
            N (∏ a, (height a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical u -
              ∑ t : Term, ((2 : ℂ) * coeff t) * (twists t).eval physicalN physicalPoly u‖ ≤
            Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
              (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  intro p map law Ch Pos height weight Hdensity Lspatial Lfactor Lcoord Lcut
    Pnative hPnative hperiod hfactor hcoord hcut
  have hHdensity : 1 ≤ Hdensity := by dsimp only [Hdensity]; linarith [cap.property]
  have hdensity : ∀ y, ‖density y‖ ≤ Hdensity := fun y =>
    (show ‖density y‖ ≤ (cap : ℝ) by simpa only [Real.norm_eq_abs] using hbound y).trans
      (by dsimp only [Hdensity]; linarith)
  have hcoefficients := allocatedOriginalSampleInactiveCoefficients_supported
    B selected U basis hR hσ S sample hs
  obtain ⟨e, he, hmass, _, _, herror⟩ :=
    exists_forecastInactive_sliced_separateTail_continuous_rational_source_s2
      B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
      δ P Hchild hδ hreg hsmall hgrid
      (allocatedOriginalSampleInactiveCoefficients B selected sample) hcoefficients
      hσ1 L hL hP hsP hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
      Ptail Ctail hPtail hsPtail hstrideTail hCtail htailactual
      hCdecay hPdecay hdecay density Hdensity hHdensity hdensity lip hLips
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by dsimp only [Pos]; infer_instance
  let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
  let _ : Fintype Term := by dsimp only [Term]; infer_instance
  let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
  have hperiodTerm (t : Term) :
      ((orderOf t.1.val * commonSitePeriod (e t.1 t.2.1) t.2.2 : ℕ) : ℝ) ≤ Real.exp Pnative := by
    have horder : (orderOf t.1.val : ℝ) ≤ T :=
      Nat.cast_le.mpr (Finset.mem_filter.mp t.1.property).2
    have hsite := commonSitePeriod_le_pow (e t.1 t.2.1) (he t.1 t.2.1)
      (fun _ => le_rfl) t.2.2
    rw [Nat.cast_mul]
    exact (mul_le_mul horder hsite (Nat.cast_nonneg _) (Nat.cast_nonneg T)).trans hperiod
  obtain ⟨twists, hmod, htransfer⟩ := exists_forecastDensityBufferedNativeExpansion_s2
    B U basis hR S density cap lip hbound hLips selected hR1
    (fun t : Term => t.1.val) (fun t : Term => e t.1 t.2.1)
    (fun t a => he t.1 t.2.1 a) (fun t : Term => t.2.2) ∅ base physicalN τ hτ
    o bW hb forward hforward K hK radius hr inverse hinverse hchart hbudget
    hPnative hperiodTerm hfactor hcoord hcut
  refine ⟨e, he, twists, hmod, ?_, ?_⟩
  · simpa only [mul_assoc] using forecastPhysicalBufferedCoefficientMass coeff hmass
  · intro x physicalPoly hphysical
    let target := forecastLawDensityPhysicalTarget B U basis S law density selected sample x (fun _ => pRat)
      (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
      N (∏ a, (height a : ℝ)) base physicalN τ o hb bW physicalPoly hphysical
    have hε : 0 ≤ Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
        (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by positivity
    apply (htransfer physicalPoly hphysical coeff target
      (Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A))
      (Hdensity * (Ctail ^ Fintype.card A * (Cdecay / T) +
        (T : ℝ) ^ (Fintype.card Out + 1) * δout))
      hmass hε ?_ ?_).2
    · intro u hu
      exact forecastLawDensityPhysicalTarget_cutoff_of_active_support_s2
        B U basis S law density selected sample x (fun _ => pRat)
        (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
        N (∏ a, (height a : ℝ)) base physicalN τ o hb bW
        hR hσ hs hσ1 hexhaustive hactive radius hr hr3 hradius
        inverse hinverse hchart hbudget physicalPoly hphysical u hu
    · intro u w deck hdeck hquarter
      exact forecastLawDensityPhysicalApproximation B U basis S law density selected sample x
        (fun _ => pRat)
        (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
        N (∏ a, (height a : ℝ)) base physicalN τ o hb bW
        (fun t : Term => t.1.val) (fun t : Term => e t.1 t.2.1)
        (fun t : Term => t.2.2) ∅ coeff cap (herror x)
        physicalPoly hphysical u w deck hdeck hquarter

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))

attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_actualFixedSpatialSlicedForecast_universal_native_source
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice s.P s.Pbad s.Ppres)
    (T : ℕ) (hT : 0 < T) (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ i v, δ * allocatedPrincipalSides B U b S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ ≤
        (slice.principalLength ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ : ℝ)) ∧
       (∀ i v, 0 < slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩)))
    (hP : 1 ≤ P) (hprimitive : scalarCubePrimitiveEnvelope Empty s.L 1 0 T ≤ P)
    (hstride : ∀ a b0 v, ((slice.principalStep
      ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v⟩ * T : ℕ) : ℝ) ≤ P)
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCt : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    (Ptail Ctail : ℝ) (hPtail : 1 ≤ Ptail)
    (hsPtail : scalarCubePrimitiveEnvelope Empty s.L 1 0 1 ≤ Ptail)
    (hstrideTail : ∀ a b v,
      (slice.principalStep ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ Ptail)
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
    :
    let cap := fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice
    let lip := fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) s.hδslice
    let H : ℝ := cap + 1
    let Lfactor := (lip + Fintype.card A * Lt) * max ⟨8 / τ, div_nonneg (by norm_num) s.hτ.le⟩ 1
    let Lcoord := s.K * ∑ j, s.forward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * Lcoord
    let Out := Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
    let Cdecay := (((slice.path.Rbad * ∏ p : slice.path.primes,
      p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m))
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
      (T : ℝ) * Vt ^ Fintype.card A ≤ Real.exp Pnative →
      (Lfactor : ℝ) ≤ Real.exp Pnative → (Lcoord : ℝ) ≤ Real.exp Pnative →
      (Lcut : ℝ) ≤ Real.exp Pnative →
    ∃ (Term : Type) (_ : Fintype Term) (coeff : Term → ℂ)
      (twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩),
      (∑ t, ‖coeff t‖) ≤ s.κ * (2 * H * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A)) ∧
      ∀ (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (u : X → ℤ),
        ‖slice.targetAt selected s.hBactive o bW hb originalpoly hmem s.κ u -
          ∑ t, coeff t * (twists t).eval physicalN
            (slice.path.physicalPolynomial originalpoly) u‖ ≤
          s.κ * (H * (Ctail ^ Fintype.card A * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout)) := by
  classical
  intro cap lip H Lfactor Lcoord Lcut Out Cdecay Pnative hPnative hperiod hfactor hcoord hcut
  let path := slice.path
  let _ := path.primeNeZero
  let N := ∏ p : path.primes, p.val ^ path.exponent p.val
  let _ : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let _ (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
    ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    path.base path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : path.primes => p.val)
    (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin
  have hgrid (a : A) : allocatedGridAxis (I := I) U b S.value
      ⟨(selected a).1, Sum.inr (selected a).2⟩ := by
    exact (s.hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
  have hdecay (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S)) (χ : AddChar (Out → ZMod N) ℂ) :=
    allocatedForecastPolynomial_crt_decay_of_bad_product_s2
      (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
      (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩) spatial kernel block
      s.hm path.primes path.exponent path.prescribed path.prime
      (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _) path.Rbad path.hbad
      path.base path.origin (fun k => (y k.1 k.2 : ℤ)) χ
  have hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) :=
    allocatedCongruenceForecastRankConstant_dimension
      (allocatedShortAxis (I := I) U b S.value) s.hm Dmod s.hDmod
  obtain ⟨hbound, hLips⟩ := slice.density_bounds_s2 s.hBactive s.hδslice
  have habs : ∀ y, |slice.density s.hBactive y| ≤ (cap : ℝ) := by
    simpa only [Real.norm_eq_abs] using hbound
  obtain ⟨e, he, twists, hmod, hmass, herror⟩ :=
    exists_forecastInactive_sliced_separateTail_native_source
      B U b hR hσ S slice.principalLength slice.principalStep slice.principalStart
      slice.principalLength_pos slice.principalSupport selected s.hselected poly N pRat T hT
      δ P Hchild hδ hreg s.hsmall hgrid path.sample path.hs s.hσ1 s.L s.hL
      hP hprimitive hstride s.hB Cactual δout Q Nt Vt Ct Ht Lt
      hCactual hCt hδout hQ hnumerics
      Ptail Ctail hPtail hsPtail hstrideTail hCtail htailactual
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) hPdecay hdecay
      (slice.density s.hBactive) cap lip habs hLips
      (slice.density_active_support_s2 s.hBactive s.hδslice)
      s.hR1 path.base physicalN τ s.hτ o bW hb s.forward s.hforward s.K s.hK
      s.radius (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ)<3) s.hr3))
      s.hr3 s.hradius s.inverse s.hinverse s.hchart s.hbudget s.hexhaustive
      hPnative hperiod hfactor hcoord hcut
  let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
    slice.principalLength slice.principalLength_pos
  let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
  let Pos := fun χ : Ch =>
    {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
      0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by dsimp only [Pos]; infer_instance
  let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
  let _ : Fintype Term := by dsimp only [Term]; infer_instance
  let weight := fun (χ : Ch) (r : Pos χ) =>
    (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
      forecastInactiveCharacterCoefficient poly N pRat χ.val
        (progressionPrincipalResidue B (layerSamplerDegree I n)
          slice.principalStep slice.principalStart (orderOf χ.val) r.val)
  let coeff₀ := fun t : Term => (2 : ℂ) * ((H : ℂ) *
    forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2)
  refine ⟨Term, inferInstance, fun t => (s.κ : ℂ) * coeff₀ t, twists, ?_, ?_⟩
  · calc
      _ = s.κ * ∑ t, ‖coeff₀ t‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.hκ,
          Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass s.hκ
  · intro originalpoly hmem u
    have hh := herror path.commonTuple (path.physicalPolynomial originalpoly)
      (path.physicalPolynomial_mem originalpoly hmem) u
    have heq := slice.principalLaw_eq_contained
    rw [← heq] at hh
    have scaled := mul_le_mul_of_nonneg_left hh s.hκ
    simpa only [ActualFixedSpatialSlicedForecastPath.targetAt, coeff₀, H, mul_assoc,
      ← Finset.mul_sum, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg s.hκ] using scaled

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
variable (q : ActualFixedSpatialSlicedForecastNumerics s)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

theorem exists_actualFixedSpatialSlicedForecastUniversalFamily_of_numerics :
    let Path := ActualFixedSpatialSlicedAdmissiblePath
      (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
      (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s q
    ∃ data : Path → ActualForecastData physicalN originalpoly q.Pnative q.massLog q.capLog q.E,
      ∀ path, (data path).target =
        path.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        (data path).centerConstant = (fun j => (path.slice.path.center j).val) ∧
        ∀ (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (u : X → ℤ),
          ‖path.slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ u -
            ∑ t, (data path).coefficient t * ((data path).twists t).eval physicalN
              (fun j => subtractConstant ((data path).centerConstant j) (poly' j)) u‖ ≤
            Real.exp (-q.E) := by
  classical
  intro Path
  have hT1 : (1 : ℝ) ≤ q.T := by exact_mod_cast q.hT
  have hPsite : 1 ≤ q.Ptail * q.T := by
    simpa only [one_mul] using mul_le_mul q.hPtail hT1 (by norm_num : (0 : ℝ) ≤ 1)
      (zero_le_one.trans q.hPtail)
  have hprimitive : scalarCubePrimitiveEnvelope Empty s.L 1 0 q.T ≤ q.Ptail * q.T := by
    have hx := scalarCubePrimitiveEnvelope_le_scaled Empty s.L 1 0 (show 1 ≤ q.T from q.hT)
    simp only [Fintype.card_empty, zero_add, pow_one] at hx
    exact hx.trans (mul_le_mul_of_nonneg_right
      (s.hprimitiveCap.trans q.hprimitive) (Nat.cast_nonneg _))
  let Out := Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U b S.value))
  have hOut : Fintype.card Out + 1 ≤ Dmod + 1 := by
    apply Nat.add_le_add_right
    change Fintype.card (Sigma _) ≤ Dmod
    rw [Fintype.card_sigma]
    exact (allocatedCongruenceRankOutput_sum_card_le (X := X) (E := Eout)
      s.hm (allocatedShortAxis (I := I) U b S.value)).trans s.hDmod
  have hpow : (q.T : ℝ) ^ (Fintype.card Out + 1) ≤ (q.T : ℝ) ^ (Dmod + 1) :=
    pow_le_pow_right₀ hT1 hOut
  have hdata : ∀ member : Path, ∃ data : ActualForecastData physicalN originalpoly
      q.Pnative q.massLog q.capLog q.E,
      data.target = member.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
        data.centerConstant = (fun j => (member.slice.path.center j).val) ∧
        ∀ (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (u : X → ℤ),
          ‖member.slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ u -
            ∑ t, data.coefficient t * (data.twists t).eval physicalN
              (fun j => subtractConstant (data.centerConstant j) (poly' j)) u‖ ≤
            Real.exp (-q.E) := by
    intro member
    let slice := member.slice
    let cap := fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) s.hδslice
    let lip := fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) s.hδslice
    let H : ℝ := cap + 1
    let Cdecay := (((slice.path.Rbad * ∏ p : slice.path.primes,
      p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) * modularRankChargeFactor m))
    have hH0 : 0 ≤ H := by dsimp only [H]; positivity
    have hC0 : 0 ≤ Cdecay := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hC : Cdecay ≤ actualSlicedForecastDecayBudget s :=
      forecastModularCharge_exp_bound m Dmod slice.path.Rbad
        (∏ p : slice.path.primes, p.val ^ slice.path.prescribed p.val)
        slice.path.RbadBound slice.path.presBound
    obtain ⟨hH, hlip, _, _⟩ := slice.density_uniform_budget_s2 s.hBactive s.hP s.hδslice
      s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks q.hv member.kernelWidth
    change H ≤ actualSlicedForecastDensityBudget s q.v at hH
    change (lip : ℝ) ≤ actualSlicedForecastDensityBudget s q.v at hlip
    have hstride : ∀ a i v, ((slice.principalStep
        ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,i,v⟩ * q.T : ℕ) : ℝ) ≤ q.Ptail * q.T := by
      intro a i v
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right (member.stride a i v) (Nat.cast_nonneg _)
    have hfactor : (((lip + Fintype.card A * q.Lt) *
        max ⟨8 / τ, div_nonneg (by norm_num) s.hτ.le⟩ 1 : ℝ≥0) : ℝ) ≤ Real.exp q.Pnative := by
      change ((lip : ℝ) + Fintype.card A * (q.Lt : ℝ)) * max (8 / τ) 1 ≤ _
      exact (mul_le_mul_of_nonneg_right (add_le_add hlip le_rfl)
        (le_trans zero_le_one (le_max_right (8 / τ) 1))).trans q.hfactor
    obtain ⟨Term, hTerm, coeff, twists, hmass, herror⟩ :=
      exists_actualFixedSpatialSlicedForecast_universal_native_source selected s o bW hb slice
        q.T q.hT q.δ (q.Ptail * q.T) q.Hchild q.hδ member.regular hPsite hprimitive hstride
        q.Cactual q.δout q.Q q.Nt q.Vt q.Ct q.Ht q.Lt q.hCactual q.hCt q.hδout q.hQ q.hnumerics
        q.Ptail q.Ctail q.hPtail (s.hprimitiveCap.trans q.hprimitive)
        member.stride q.hCtail q.htailactual q.hPnative q.hperiod hfactor q.hcoord q.hcut
    let _ := hTerm
    have hmfinal : (∑ t, ‖coeff t‖) ≤ Real.exp q.massLog := hmass.trans (le_trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num : (0 : ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_right hpow (pow_nonneg q.hCt _))
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg q.hCt _))
          (mul_nonneg (by norm_num) (Real.exp_nonneg _))) s.hκ) q.hmass)
    have hcap : ∀ u, ‖slice.target selected s.hBactive o bW hb originalpoly hmem s.κ u‖ ≤
        Real.exp q.capLog := by
      intro u
      have hc := ActualFixedSpatialSlicedForecastPath.target_norm_le_s2 s slice q.δ q.Hchild q.hδ member.regular
        q.Ptail q.Ctail q.hPtail q.hprimitive member.stride q.hCtail q.htailactual
        o bW hb originalpoly hmem u
      have hcapH : (cap : ℝ) ≤ actualSlicedForecastDensityBudget s q.v := by
        exact (le_add_of_nonneg_right zero_le_one).trans hH
      exact hc.trans ((mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcapH s.hκ)
          (pow_nonneg q.hCtail _))
        (add_le_add le_rfl hC) (add_nonneg zero_le_one hC0)
        (mul_nonneg (mul_nonneg s.hκ (Real.exp_nonneg _)) (pow_nonneg q.hCtail _))).trans q.hcap)
    have hefinal : ∀ (poly' : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hm' : ∀ j d, coefficients (poly' j) d ∈ U j) (u : X → ℤ),
        ‖slice.targetAt selected s.hBactive o bW hb poly' hm' s.κ u -
          ∑ t, coeff t * (twists t).eval physicalN
            (slice.path.physicalPolynomial poly') u‖ ≤ Real.exp (-q.E) := by
      intro poly' hm' u
      apply (herror poly' hm' u).trans
      apply le_trans _ q.herror
      apply mul_le_mul_of_nonneg_left _ s.hκ
      apply mul_le_mul hH
      · exact add_le_add
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC (Nat.cast_nonneg _))
            (pow_nonneg q.hCtail _))
          (mul_le_mul_of_nonneg_right hpow q.hδout.le)
      · exact add_nonneg (mul_nonneg (pow_nonneg q.hCtail _)
          (div_nonneg hC0 (Nat.cast_nonneg _)))
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) q.hδout.le)
      · exact Real.exp_nonneg _
    refine ⟨{
      target := slice.target selected s.hBactive o bW hb originalpoly hmem s.κ
      centerConstant := fun j => (slice.path.center j).val
      Term := Term
      coefficient := coeff
      twists := twists
      cap := hcap
      mass := hmfinal
      approximation := fun u => hefinal originalpoly hmem u.val }, rfl, rfl, hefinal⟩
  choose data hdataSpec using hdata
  exact ⟨data, hdataSpec⟩

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
variable (qEarly qLate : ActualFixedSpatialSlicedForecastNumerics s)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qEarly)
variable (hδ : qEarly.δ = qLate.δ) (hH : qEarly.Hchild = qLate.Hchild)
variable (hv : qEarly.v = qLate.v) (hPtail : qEarly.Ptail = qLate.Ptail)

include hδ hH hv hPtail in

theorem exists_actualSlicedForecast_late_data_s2_oai :
    ∃ data : ActualForecastData physicalN originalpoly qLate.Pnative qLate.massLog qLate.capLog qLate.E,
      data.target = member.slice.target selected s.hBactive o bW hb originalpoly hmem s.κ ∧
      data.centerConstant = (fun j => (member.slice.path.center j).val) ∧
      ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
        ‖member.slice.targetAt selected s.hBactive o bW hb poly hm s.κ u -
          ∑ t, data.coefficient t * (data.twists t).eval physicalN
            (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-qLate.E) := by
  obtain ⟨family, hfamily⟩ := exists_actualFixedSpatialSlicedForecastUniversalFamily_of_numerics
    (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
    (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN)
    s qLate o bW hb originalpoly hmem
  let lateMember := member.withNumerics qLate hδ hH hv hPtail
  exact ⟨family lateMember, hfamily lateMember⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_actualSlicedForecast_late_data_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_actualSlicedForecast_late_data_s2_oai
