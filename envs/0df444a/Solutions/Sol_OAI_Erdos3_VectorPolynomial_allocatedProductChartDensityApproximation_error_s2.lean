-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedProductChartDensityApproximation_error_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:21:13.402582+00:00
-- url     : https://prove2.me/submissions/c1931b5d-695f-4cd2-8c26-01e134b44652

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedBufferedRowIdealProduct_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductChartIdealApproximation_zero_outside_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductPrefactor_masked_density_error_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductSiteCutoff_sites_quarter_s2

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

theorem restrictedComplexChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) {y : Y} (hy : y ∉ q '' S) :
    restrictedComplexChartDensity q S c f y = 0 := by
  have hy' : y ∉ Set.range (fun x : S => q x.val) := by
    rintro ⟨x, rfl⟩
    exact hy ⟨x.val, x.property, rfl⟩
  simp only [restrictedComplexChartDensity, Function.extend_apply' _ _ _ hy', mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mixedArrayRegroup_apply {I Z J : Type*} (x : (I → J → ℝ) × (Z → J → ℤ)) (j : J) :
    mixedArrayRegroup I Z J x j = (fun i => x.1 i j, fun z => x.2 z j) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem orthonormalMixedChart_sum_zsmul (o : OrthonormalBasis I ℝ W)
    {S : Type*} (s : Finset S) (a : S → ℤ)
    (x : S → (I → ℝ) × (Fin n → ℤ)) :
    orthonormalMixedChart o (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • orthonormalMixedChart o (x i) := by
  change orthonormalMixedChartHom W o _ = _
  simp only [map_sum, map_zsmul, orthonormalMixedChartHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D I J O Z : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

omit [Fintype I] in
theorem mixedArrayIntegerImage_regroup (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Z → J → ℤ)) (r : O) :
    mixedArrayRegroup I Z O (mixedArrayIntegerImage A x) r =
      ∑ j, A r j • mixedArrayRegroup I Z J x j := by
  apply Prod.ext
  · funext i
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.fst_sum,
      Finset.sum_apply]
    change (∑ j, (A r j : ℝ) * x.1 i j) = ∑ j, A r j • x.1 i j
    exact Finset.sum_congr rfl (fun j _ => Int.cast_smul_eq_zsmul ℝ (A r j) (x.1 i j))
  · funext z
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.snd_sum,
      Finset.sum_apply]
    change (∑ j, A r j * x.2 z j) = ∑ j, A r j • x.2 z j
    simp only [smul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeRepresentative_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedLatticeRepresentative W b hb (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedLatticeRepresentative W b hb (x i) := by
  change normalizedLatticeRepresentativeHom W b hb _ = _
  simp only [map_sum, map_zsmul, normalizedLatticeRepresentativeHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]

theorem normalizedCoverLift_sum_zsmul (d : ℕ) {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedCoverLift W b hb d (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedCoverLift W b hb d (x i) := by
  have he (i) : (d : ℝ)⁻¹ • (a i • normalizedLatticeRepresentative W b hb (x i)) =
      a i • ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb (x i)) := smul_comm _ _ _
  simp only [normalizedCoverLift, normalizedLatticeRepresentative_sum_zsmul,
    Finset.smul_sum, he]
  change QuotientAddGroup.mk' _ (∑ i ∈ s, a i • ((d : ℝ)⁻¹ •
    normalizedLatticeRepresentative W b hb (x i))) = _
  simp only [map_sum, map_zsmul]
  rfl

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedCoveredIntegerReconstruction
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D Q : Type*} [Fintype D] [Fintype Q] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis Q ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) (r : S → Q → ZMod d) :
    normalizedCoveredChart W b hb bW d (∑ i ∈ s, a i • x i, ∑ i ∈ s, a i • r i) =
      ∑ i ∈ s, a i • normalizedCoveredChart W b hb bW d (x i, r i) := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (Nat.pos_of_ne_zero (NeZero.ne d))
  let deck : (Q → ZMod d) →+ W ⧸ Γ := (quotientIntegerCover Γ d).ker.subtype.comp e.toAddMonoidHom
  change normalizedCoverLift W b hb d (∑ i ∈ s, a i • x i) + deck (∑ i ∈ s, a i • r i) =
    ∑ i ∈ s, a i • (normalizedCoverLift W b hb d (x i) + deck (r i))
  rw [normalizedCoverLift_sum_zsmul]
  simp only [map_sum, map_zsmul, smul_add, Finset.sum_add_distrib]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I O P J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]

variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredJetIntegerImage_chart
    (A : ∀ j, Matrix (P j) (O j) ℤ) (z : MixedCoveredJetSource I O Q n d)
    (j : Fin m) (t : P j) :
    mixedCoveredJetChart U o b hb bW d (mixedCoveredJetIntegerImage d A z) j t =
      ∑ r, A j t r • mixedCoveredJetChart U o b hb bW d z j r := by
  change normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
    (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (mixedArrayIntegerImage (A j) (z.1 j)) t),
      fun k => ∑ r, A j t r • z.2 j r k) = _
  rw [mixedArrayIntegerImage_regroup, orthonormalMixedChart_sum_zsmul]
  have hdeck : (fun k => ∑ r, A j t r • z.2 j r k) = ∑ r, A j t r • z.2 j r := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [hdeck]
  exact normalizedCoveredChart_sum_zsmul (euclideanSubspace (U j)) (b j) (hb j) (bW j) d
      Finset.univ (A j t) (fun r => orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z.1 j) r))
      (z.2 j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

omit [Fintype α] in
theorem mixedCoveredRowsSiteValue_chart (z : MixedCoveredJetSource I rows E n d) (s : Finset α) :
    mixedCoveredJetChart U o b hb bW d (mixedCoveredRowsSiteValue rowSets d z s) =
      coveredRowsSiteValue rowSets U (mixedCoveredJetChart U o b hb bW d z) s := by
  funext j t
  exact mixedCoveredJetIntegerImage_chart U o b hb bW d
    (fun j (_ : Unit) => rowRestrictedSiteMatrix (rowSets j) s) z j t

end VectorPolynomial
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedComplexChartSupport
namespace OAI

section

namespace Erdos3

variable {X Y : Type*}

theorem restrictedComplexChartDensity_norm_le (q : X → Y) (S : Set X)
    (hinj : Set.InjOn q S) (f : X → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C) (y : Y) : ‖restrictedComplexChartDensity q S 1 f y‖ ≤ C := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply q S 1 f hinj hx, Complex.ofReal_one, one_mul]
    exact hf x
  · rw [restrictedComplexChartDensity_zero q S 1 f hy, norm_zero]
    exact hC

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoordinateCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem normalizedCoordinateCutoff_spec (D : Type*) [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) :
    ContDiff ℝ ∞ (normalizedCoordinateCutoff D r hr) ∧
      HasCompactSupport (normalizedCoordinateCutoff D r hr) ∧
      (∀ v, 0 ≤ normalizedCoordinateCutoff D r hr v ∧ normalizedCoordinateCutoff D r hr v ≤ 1) ∧
      (∀ v, (∀ d, |v d| ≤ (r : ℝ)) → normalizedCoordinateCutoff D r hr v = 1) ∧
      (∀ v, normalizedCoordinateCutoff D r hr v ≠ 0 → ∀ d, |v d| ≤ 2 * (r : ℝ)) ∧
      LipschitzWith (Fintype.card D * normalizedSiteCutoffBound / (2 * r))
        (normalizedCoordinateCutoff D r hr) :=
  Classical.choose_spec (exists_normalized_site_cutoff (D := D) r hr)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BufferedCoordinateProjection
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]
variable (r : ℝ≥0) (hr : 0 < r) (f : (D → ℝ) → ℂ)

theorem bufferedCoordinateProjection_norm_le (hf : ∀ z, ‖f z‖ ≤ 1) (z : D → ℝ) :
    ‖bufferedCoordinateProjection P r hr f z‖ ≤ 1 := by
  have hc := (normalizedCoordinateCutoff_spec D r hr).2.2.1 z
  rw [bufferedCoordinateProjection, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc.1]
  exact (mul_le_mul hc.2 (hf _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedFullMixedSiteValue_projection
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) :
    coordinateZeroProjection (allocatedGridAxis (I := I) U b S.value)
      (allocatedFullMixedSiteValue (R := R) U b w) = allocatedNormalizedMixedSiteValue B U b S w := by
  funext a
  rcases a with ⟨j, i | i⟩ <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (r : ℝ≥0) (hr : 0 < r) (f : (LayerSamplerAxis I n → ℝ) → ℂ)

theorem allocatedBufferedMixedSiteFactor_norm_le (hf : ∀ z, ‖f z‖ ≤ 1)
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) :
    ‖allocatedBufferedMixedSiteFactor B U b S r hr f w‖ ≤ 1 :=
  bufferedCoordinateProjection_norm_le _ r hr f hf _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := Q) U o b d quarter

theorem allocatedBufferedSiteChartFactor_norm_le
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (hf : ∀ v, ‖f v‖ ≤ 1)
    (y : EuclideanJetLayers U single) : ‖allocatedBufferedSiteChartFactor B U b S o hb bW d r hr f y‖ ≤ 1 :=
  restrictedComplexChartDensity_norm_le chart region
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) _ zero_le_one
    (fun _ => allocatedBufferedMixedSiteFactor_norm_le B U b S r hr f hf _) y

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductIdealCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

theorem allocatedProductSiteCutoff_norm (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y‖ ≤ 1 := by
  rw [allocatedProductSiteCutoff, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro s _
  exact allocatedBufferedSiteChartFactor_norm_le B U b S o hb bW d r hr (fun _ => 1)
    (fun _ => by simp) _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFullGridChartModelMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedProductFullGridPrefactor_zero (y : EuclideanJetLayers U rowTypes)
    (hy : y ∉ chart '' region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y = 0 := by
  have hp : allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f y = 0 := by
    unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
    exact restrictedChartDensity_zero _ _ _ _ hy
  rw [allocatedProductFullGridPrefactor, hp, Complex.ofReal_zero, mul_zero, mul_zero]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalNormalizer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "siteChart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "siteRegion" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "factor" => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr

theorem allocatedBufferedSiteChartFactor_on_chart
    (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (w : MixedCoveredJetSource I single E n d) (hw : w ∈ siteRegion) :
    factor f (siteChart w) = factor (fun _ => 1) (siteChart w) *
      f (allocatedNormalizedMixedSiteValue B U b S (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  simp only [allocatedBufferedSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _ hinj hw,
    Complex.ofReal_one, one_mul, allocatedBufferedMixedSiteFactor, bufferedCoordinateProjection,
    allocatedFullMixedSiteValue_projection, mul_one]

theorem allocatedBufferedSiteChartFactor_zero_of_cutoff_zero
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (y : EuclideanJetLayers U single)
    (hy : factor (fun _ => 1) y = 0) : factor f y = 0 := by
  by_cases hmem : y ∈ siteChart '' siteRegion
  · obtain ⟨w, hw, rfl⟩ := hmem
    rw [allocatedBufferedSiteChartFactor_on_chart B U b S o hb bW d r hr f w hw, hy, zero_mul]
  · unfold allocatedBufferedSiteChartFactor
    exact restrictedComplexChartDensity_zero _ _ _ _ hmem

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedMaskedChartProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d quarter

theorem allocatedMaskedSiteChartFactor_apply
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (w : MixedCoveredJetSource I single E n d) (hw : w ∈ region) :
    allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f (chart w) =
      if mixedCoveredSiteResidue d period w = label then
        allocatedBufferedSiteChartFactor B U b S o hb bW d r hr f (chart w) else 0 := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  simp only [allocatedMaskedSiteChartFactor, allocatedBufferedSiteChartFactor,
    restrictedComplexChartDensity_apply _ _ _ _ hinj hw, Complex.ofReal_one, one_mul]

theorem allocatedMaskedSiteChartFactor_zero_of_cutoff_zero
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (y : EuclideanJetLayers U single)
    (hy : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y = 0) :
    allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y = 0 := by
  by_cases hmem : y ∈ chart '' region
  · obtain ⟨w, hw, rfl⟩ := hmem
    rw [allocatedMaskedSiteChartFactor_apply B U b S o hb bW d r hr period label f w hw]
    split_ifs
    · exact allocatedBufferedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr f _ hy
    · rfl
  · unfold allocatedMaskedSiteChartFactor
    exact restrictedComplexChartDensity_zero _ _ _ _ hmem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

omit [Fintype α] [DecidableEq α] in
theorem allocatedProductMaskedIdealSiteFactor_zero
    {K : Type*} (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (k : K) (s : Finset α) (w : MixedCoveredJetSource I (fun _ => Unit) E n d)
    (hw : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) (chart w) = 0) :
    allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s w = 0 := by
  unfold allocatedProductMaskedIdealSiteFactor maskedSiteFactor
  dsimp only
  rw [allocatedBufferedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr (f k s) _ hw]
  split_ifs <;> rfl

theorem allocatedMaskedChartProduct_zero_of_cutoff_zero
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (y : EuclideanJetLayers U rowTypes) (hy : cutoff y = 0) :
    (∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f s)
      (coveredRowsSiteValue rowSets U y s)) = 0 := by
  change (∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
    (coveredRowsSiteValue rowSets U y s)) = 0 at hy
  obtain ⟨s, hs, hsite⟩ := Finset.prod_eq_zero_iff.mp hy
  exact Finset.prod_eq_zero hs
    (allocatedMaskedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr period (label s) (f s) _ hsite)

theorem allocatedMaskedMixedProduct_zero_of_cutoff_zero
    {K : Type*} (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (k : K) (z : MixedCoveredJetSource I rowTypes E n d) (hz : cutoff (chart z) = 0) :
    (∏ s, allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s
      (mixedCoveredRowsSiteValue rowSets d z s)) = 0 := by
  change (∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
    (coveredRowsSiteValue rowSets U (chart z) s)) = 0 at hz
  obtain ⟨s, hs, hsite⟩ := Finset.prod_eq_zero_iff.mp hz
  refine Finset.prod_eq_zero hs (allocatedProductMaskedIdealSiteFactor_zero B U b S o hb bW d r hr period f label k s _ ?_)
  simpa only [mixedCoveredRowsSiteValue_chart] using hsite

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedMaskedChartProduct_eq_mixed
    {K : Type*} (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (k : K) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    (∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f k s)
      (coveredRowsSiteValue rowSets U (chart z) s)) =
    ∏ s, allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s
      (mixedCoveredRowsSiteValue rowSets d z s) := by
  by_cases hc : cutoff (chart z) = 0
  · rw [allocatedMaskedChartProduct_zero_of_cutoff_zero B U b S o hb bW d r hr period rowSets (f k) label _ hc,
      allocatedMaskedMixedProduct_zero_of_cutoff_zero B U b S o hb bW d r hr period rowSets f label k z hc]
  · have hsites := allocatedProductSiteCutoff_sites_quarter_s2 B U b S rowSets o hb bW d r hr
      hR C hC hchart hbudget z hz hc
    apply Finset.prod_congr rfl
    intro s _
    rw [← mixedCoveredRowsSiteValue_chart rowSets U o b hb bW d z s,
      allocatedMaskedSiteChartFactor_apply B U b S o hb bW d r hr period (label s) (f k s) _ (hsites s)]
    simp only [mixedCoveredSiteResidue, allocatedProductMaskedIdealSiteFactor, maskedSiteFactor]
    split_ifs with hlabel <;> simp_all

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedProductChartIdealApproximation_eq_mixed {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f (chart z) =
      ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
          ∏ s, allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s
            (mixedCoveredRowsSiteValue rowSets d z s) := by
  unfold allocatedProductChartIdealApproximation
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  rw [allocatedMaskedChartProduct_eq_mixed B U b S o hb bW d r hr period rowSets hR C hC hchart hbudget f label k z hz]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedGlobalMaskedDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "factor" => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

include hR hC hchart hbudget in
theorem allocatedBufferedRowDensityProduct_error {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ) -
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s)‖ ≤ ε) :
    ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
      ∑ k, a k * ∏ s, factor (f k s) (coveredRowsSiteValue rowSets U (chart z) s)‖ ≤ ε := by
  have hsum : (∑ k, a k * ∏ s, factor (f k s) (coveredRowsSiteValue rowSets U (chart z) s)) =
      cutoff (chart z) *
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s) := by
    simp_rw [allocatedBufferedRowIdealProduct_s2 B U b S o hb bW d r hr rowSets hR C hC hchart hbudget _ z hz]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right (allocatedProductSiteCutoff_norm B U b S rowSets o hb bW d r hr _)
    (norm_nonneg _)).trans (by simpa only [one_mul] using herr)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hperiod hM hm hR hC hchart hbudget in
theorem allocatedProductChartDensityApproximation_error_s2_oai {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ v : AllocatedLongJetRows B U b S rowTypes,
      ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D (allocatedLongJetRealCoordinates B U b S v) : ℂ) -
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets v s)‖ ≤ ε)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ D y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
      ‖inverseNormalizer‖ *
        (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * ε := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedProductChartIdealApproximation_eq_mixed B U b S rowSets x y₀ q d period r hr hb o bW
      hR C hC hchart hbudget a f z hz]
    apply allocatedProductPrefactor_masked_density_error_s2 B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR a
      (fun k s v => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (f k s) (chart v)) D ε z hz
    have he := allocatedBufferedRowDensityProduct_error B U b S o hb bW d r hr rowSets
      hR C hC hchart hbudget a f D ε z hz (herr (split z.1).2)
    simpa only [mixedCoveredRowsSiteValue_chart] using he
  · rw [allocatedProductFullGridPrefactor_zero B U b S rowSets d r hr x hb o bW q y₀ D y hy,
      allocatedProductChartIdealApproximation_zero_outside_s2 B U b S rowSets x y₀ q d period r hr hb o bW
        hR C hC hchart hbudget a f y hy,
      sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _)
        (coefficientDeckPeriodCap_nonneg rowTypes E period))) hε

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedProductChartDensityApproximation_error_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedProductChartDensityApproximation_error_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
