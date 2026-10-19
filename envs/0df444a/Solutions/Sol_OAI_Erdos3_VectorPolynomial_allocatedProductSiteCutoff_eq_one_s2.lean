-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_eq_one_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:03:59.967081+00:00
-- url     : https://prove2.me/submissions/8a4a91e5-d408-4c03-8010-2eb67d28ce45

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216

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

theorem bufferedCoordinateProjection_eq (z : D → ℝ) (hz : ∀ d, |z d| ≤ (r : ℝ)) :
    bufferedCoordinateProjection P r hr f z = f (coordinateZeroProjection P z) := by
  rw [bufferedCoordinateProjection, (normalizedCoordinateCutoff_spec D r hr).2.2.2.1 z hz,
    Complex.ofReal_one, one_mul]

theorem bufferedCoordinateProjection_nonzero_box (z : D → ℝ)
    (hz : bufferedCoordinateProjection P r hr f z ≠ 0) : ∀ d, |z d| ≤ 2 * (r : ℝ) := by
  apply (normalizedCoordinateCutoff_spec D r hr).2.2.2.2.1 z
  intro hc
  apply hz
  rw [bufferedCoordinateProjection, hc, Complex.ofReal_zero, zero_mul]

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

theorem allocatedFullMixedSiteValue_point_bound
    (hR : ∀ j, 0 < R j) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ))
    {r : ℝ} (hr : 0 ≤ r) (hw : ∀ a, |allocatedFullMixedSiteValue (R := R) U b w a| ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j))‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (r * R j)) := by
  have hreal (i : I j) : |(w j).1 i| ≤ r * R j := by
    have h := hw ⟨j, Sum.inl i⟩
    change |(w j).1 i / R j| ≤ r at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have hint (i : Fin (n j)) : |((w j).2 i : ℝ) / basisAxisScale (b j) i| ≤ r * R j := by
    have h := hw ⟨j, Sum.inr i⟩
    change |((w j).2 i : ℝ) / basisAxisScale (b j) i / R j| ≤ r at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  exact mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg hr (hR j).le) (hchart j) (w j).1
    (fun i => ((w j).2 i : ℝ) / basisAxisScale (b j) i) hreal hint

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

theorem allocatedBufferedMixedSiteFactor_eq
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ))
    (hw : ∀ a, |allocatedFullMixedSiteValue (R := R) U b w a| ≤ (r : ℝ)) :
    allocatedBufferedMixedSiteFactor B U b S r hr f w =
      f (allocatedNormalizedMixedSiteValue B U b S w) := by
  rw [allocatedBufferedMixedSiteFactor, bufferedCoordinateProjection_eq _ r hr f _ hw,
    allocatedFullMixedSiteValue_projection]

theorem allocatedBufferedMixedSiteFactor_nonzero_point_bound
    (hR : ∀ j, 0 < R j) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ))
    (hw : allocatedBufferedMixedSiteFactor B U b S r hr f w ≠ 0)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w j))‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) := by
  exact allocatedFullMixedSiteValue_point_bound U b hR o w
    (mul_nonneg (by norm_num) r.coe_nonneg)
    (bufferedCoordinateProjection_nonzero_box _ r hr f _ hw) C hC hchart j

theorem allocatedBufferedMixedSiteFactor_nonzero_mem_quarter
    (hR : ∀ j, 0 < R j) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} (d : ℕ)
    (z : MixedCoveredJetSource I (fun _ => Unit) Q n d)
    (hz : allocatedBufferedMixedSiteFactor B U b S r hr f
      (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()) ≠ 0)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4) :
    z ∈ mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
  intro j _ t _
  refine ⟨?_, Set.mem_univ _⟩
  intro i
  cases t
  have h := (allocatedBufferedMixedSiteFactor_nonzero_point_bound B U b S r hr f
    hR o (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()) hz C hC hchart j).trans (hbudget j)
  exact (PiLp.norm_apply_le (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z.1 j) ()))) i).trans h

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
local notation "chart" => mixedCoveredJetChart U o b hb bW d

theorem allocatedProductSiteCutoff_eq_one_s2_oai (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hbox : ∀ s a, |allocatedFullMixedSiteValue (R := R) U b
      (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) a| ≤ (r : ℝ)) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) = 1 := by
  unfold allocatedProductSiteCutoff
  apply Finset.prod_eq_one
  intro s _
  have hval : allocatedBufferedMixedSiteFactor B U b S r hr (fun _ => 1)
      (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) = 1 := by
    rw [allocatedBufferedMixedSiteFactor_eq B U b S r hr (fun _ => 1) _ (hbox s)]
  have hs := allocatedBufferedMixedSiteFactor_nonzero_mem_quarter B U b S r hr (fun _ => 1)
    hR o d (mixedCoveredRowsSiteValue rowSets d z s) (by rw [hval]; exact one_ne_zero) C hC hchart hbudget
  rw [← mixedCoveredRowsSiteValue_chart rowSets U o b hb bW d z s,
    allocatedBufferedSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d
        (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hs,
    Complex.ofReal_one, one_mul, hval]

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_eq_one_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_eq_one_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
