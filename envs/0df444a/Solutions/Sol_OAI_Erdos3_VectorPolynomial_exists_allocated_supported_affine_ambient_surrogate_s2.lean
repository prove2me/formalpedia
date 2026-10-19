-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_ambient_surrogate_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:28:00.973987+00:00
-- url     : https://prove2.me/submissions/8c68e27e-94f3-4e1c-bcae-ddf4808e0be1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineRowIdeal_cutoff_fixes_mean_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductChartIdealApproximation_zero_outside_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedMaskedProfile_chart_mean_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_chart_ideal_ambient_lift_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_sliced_ambient_grid_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem ambient_nsmul_lipschitz {J : Type*} [Fintype J] (a : ℕ) :
    LipschitzWith (a : ℝ≥0) (fun z : J → UnitAddCircle => a • z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← smul_sub, dist_eq_norm]
  exact norm_nsmul_le

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNaturalChartScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i

include hR in
theorem allocatedPrincipalGridScale_pos_of_radius : 0 < scale := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (principalProfileSize_pos (hR j) _)
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

local notation "ig" => allocatedGridIntegerAxis B U b S

local notation "axisN" => allocatedGridNaturalScale B U b S

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridNaturalScale_pos (a : gridAxes) : 0 < axisN a :=
  allocatedPrincipalGridScale_pos_of_radius B U b hR (ig a).1 (ig a).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

omit [∀ j, Fintype (O j)] in
theorem allocatedChartGridMultiplier_apply (g : AllocatedFrozenJetRows B U b S O → ℝ)
    (z : MixedCoveredJetSource I O Q n d) (hz : z ∈ region) :
    allocatedChartGridMultiplier B U b S O hb o bW d g (chart z) = g ((split z.1).1) := by
  rw [allocatedChartGridMultiplier, restrictedChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz, one_mul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedFullGridNaturalVolume_pos : 0 < allocatedFullGridNaturalVolume B U b S rowSets :=
  Finset.prod_pos (fun a _ => pow_pos (Nat.cast_pos.mpr (allocatedGridNaturalScale_pos B U b hR S a)) _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {O J : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_nsmul_output (d : ℕ) (y : EuclideanJetLayers U O) :
    coveredJetAmbientTorus U d y = d • coveredJetAmbientTorus U 1 y := by
  funext a
  simp [coveredJetAmbientTorus, quotientIntegerCover, map_nsmul]

theorem ambient_nsmul_lipschitz {A : Type*} [Fintype A] (d : ℕ) :
    LipschitzWith (d : ℝ≥0) (fun z : A → UnitAddCircle => d • z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, ← smul_sub]
  simpa only [dist_eq_norm, NNReal.coe_natCast] using (norm_nsmul_le (a := z - w) (n := d))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedAmbientGrid
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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem exists_allocated_grid_times_ambient_lift
    (gridDensity : AllocatedFrozenJetRows B U b S O → ℝ)
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ) {Lg : ℝ≥0}
    (hg : LipschitzWith Lg g) (hgb : ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hgv : ∀ z : MixedCoveredJetSource I O Q n d,
      z ∈ mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)) →
      g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
        gridDensity ((coefficientJetAxisSplit O I n grid z.1).1))
    (model : EuclideanJetLayers U O → ℂ)
    (F : (JetAmbientIndex O J → UnitAddCircle) → ℂ) {Lf Cf : ℝ≥0}
    (hF : LipschitzWith Lf F) (hFb : ∀ z, ‖F z‖ ≤ Cf)
    (hFv : ∀ y, model y = F (coveredJetAmbientTorus U 1 y))
    (hzero : ∀ y, y ∉ mixedCoveredJetChart U o b hb bW d ''
      mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j)) → model y = 0) :
    ∃ G : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith (Cf * (Lg * d) + Lf) G ∧ (∀ z, ‖G z‖ ≤ Cf) ∧
      ∀ y, model y * (allocatedChartGridMultiplier B U b S O hb o bW d gridDensity y : ℂ) =
        G (coveredJetAmbientTorus U 1 y) := by
  have hgC : LipschitzWith (Lg * d)
      (fun z : JetAmbientIndex O J → UnitAddCircle => (g (d • z) : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp (hg.comp (ambient_nsmul_lipschitz d))
  have hgbC (z : JetAmbientIndex O J → UnitAddCircle) : ‖(g (d • z) : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgb _).1]
    exact (hgb _).2
  refine ⟨fun z => F z * (g (d • z) : ℂ), ?_, ?_, ?_⟩
  · simpa only [one_mul] using lipschitz_mul_of_bounds _ _ hF hgC hFb hgbC
  · intro z
    rw [norm_mul]
    exact (mul_le_mul (hFb z) (hgbC z) (norm_nonneg _) (NNReal.coe_nonneg _)).trans_eq (mul_one _)
  · intro y
    dsimp only
    by_cases hy : y ∈ mixedCoveredJetChart U o b hb bW d ''
        mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j))
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [← coveredJetAmbientTorus_nsmul_output, hgv z hz,
        allocatedChartGridMultiplier_apply B U b S O hb o bW d gridDensity z hz, hFv]
    · rw [← hFv, hzero y hy, zero_mul, zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include hu₀ hperiod in

theorem allocatedSupportedSlicedProfile_ambient_surrogate_error
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (rad : ℝ≥0) (hrad : 0 < rad)
    (g : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℝ)
    (hgb : ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hgv : ∀ z : MixedCoveredJetSource I rowTypes Q n d, z ∈ region →
      g (coveredJetAmbientTorus U d (chart z)) =
        gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1))
    (model : EuclideanJetLayers U rowTypes → ℂ)
    (F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ)
    (hFv : ∀ y, model y = F (coveredJetAmbientTorus U 1 y))
    (hzero : ∀ y, y ∉ chart '' region → model y = 0)
    {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y -
      model y‖ ≤ η)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ) -
      (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        F (coveredJetAmbientTorus U 1 y) * (g (coveredJetAmbientTorus U d y) : ℂ)‖ ≤
      allocatedFullGridNaturalVolume B U b S rowSets * η := by
  let N : ℂ := (allocatedFullGridNaturalVolume B U b S rowSets : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).ne'
  have hNnorm : ‖N‖ = allocatedFullGridNaturalVolume B U b S rowSets := by
    rw [Complex.norm_real, Real.norm_of_nonneg (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le]
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedSupportedSlicedMaskedProfile_chart_mean_s2 B U b hR hσ S rowSets
      H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod hb o bW f z hz,
      Complex.ofReal_mul, ← hFv, hgv z hz]
    have heq : allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad (chart z) *
        ((gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) : ℂ) *
          (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) : ℂ)) -
        N * model (chart z) * (gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1) : ℂ) =
        N * (allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f (chart z) -
          model (chart z)) * (gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1) : ℂ) := by
      unfold allocatedProductFullGridPrefactor
      let cv := allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad (chart z)
      let wv : ℂ := allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z)
      let gv : ℂ := gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1)
      change cv * (gv * wv) - N * model (chart z) * gv =
        N * (cv * (1 / N * wv) - model (chart z)) * gv
      field_simp
    rw [heq, norm_mul, norm_mul, hNnorm]
    have hg1 : ‖(gridDensity ((coefficientJetAxisSplit rowTypes I n grid z.1).1) : ℂ)‖ ≤ 1 := by
      rw [← hgv z hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgb _).1]
      exact (hgb _).2
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (happrox _) (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le)
      hg1 (norm_nonneg _) (mul_nonneg (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le hη)).trans_eq (mul_one _)
  · have hpzero (u) : allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y = 0 := by
      unfold allocatedWholeMaskedCoveredProfile allocatedCoveredProfileDensity
      exact restrictedChartDensity_zero _ _ _ _ hy
    rw [← hFv, hzero y hy]
    simp only [hpzero, FiniteProbabilityWeights.mean_const, Complex.ofReal_zero,
      mul_zero, zero_mul, sub_self, norm_zero]
    exact mul_nonneg (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le hη

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineBoundedAmbient
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "quarter" => (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter
local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include hu₀ hperiod in
theorem exists_allocated_supported_affine_ambient_surrogate_s2_oai
    (period : ℕ) [NeZero period] (hdiv : period ∣ d)
    (rad : ℝ≥0) (hrad : 0 < rad)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (rad : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (rad : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Kmodel : Type*} [Fintype Kmodel] (a : Kmodel → ℂ)
    (f : Kmodel → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hfb : ∀ k s z, ‖f k s z‖ ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period rad hrad hb o bW a f y‖ ≤ η) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * rad)) * Lcoord
    let Lsite := Lcut * d + max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let mass := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)),
      ∑ k, ‖(2 : ℂ) ^ Fintype.card (Finset α) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖₊
    let Lgrid := (Fintype.card gridAxes *
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) *
        (2 * ((S.value : ℝ≥0) ^ (layerTailDegree m + 1)) ^ 2))) *
      (∑ j, Cforward j * Fintype.card (J j))
    let N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (N * (mass * (Lgrid * d) +
        mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) F ∧
      (∀ z, ‖F z‖ ≤ (N * mass : ℝ≥0)) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u v₀) q (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤
          allocatedFullGridNaturalVolume B U b S rowSets * η := by
  intro Lcoord Lcut Lsite Lrows mass Lgrid N
  have hb0 (j : Fin m) : C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (rad : ℝ) * R j)) ≤ 1 / 4 := by
    have hp0 : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (rad : ℝ) * R j)) :=
      mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
    have hcard : (1 : ℝ) ≤ Fintype.card (Finset α) := by
      exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Finset α))
    have hfac : (1 : ℝ) ≤ ((rowSets j).card + 1 : ℝ) * Fintype.card (Finset α) :=
      one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α := ℝ) (rowSets j).card; linarith) hcard
    exact (le_mul_of_one_le_left hp0 hfac).trans (by simpa only [mul_assoc] using hbudget j)
  let model := allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period rad hrad hb o bW a f
  obtain ⟨F, hF, hFb, hFv⟩ := exists_allocated_chart_ideal_ambient_lift_s2 B U b S rowSets x y₀ q d period
    rad hrad hb o bW hdiv hR C hC hchart hb0 Cforward hforward K hK a f hf hfb
  change ∀ y, model y = F (coveredJetAmbientTorus U 1 y) at hFv
  obtain ⟨g, hg, hgb, hgv⟩ := exists_allocated_supported_sliced_ambient_grid_s2 B U b hR hσ S rowSets
    H step c hH hsubset q r hcell x v₀ Q d hb o bW Cforward hforward
  have hzero (y) (hy : y ∉ chart '' region) : model y = 0 :=
    allocatedProductChartIdealApproximation_zero_outside_s2 B U b S rowSets x y₀ q d period rad hrad hb o bW
      hR C hC hchart hbudget a f y hy
  obtain ⟨G₀, hG₀, hG₀b, hG₀v⟩ := exists_allocated_grid_times_ambient_lift B U b S o hb bW d
    gridDensity g hg hgb hgv model F hF hFb hFv hzero
  change LipschitzWith (mass * (Lgrid * d) +
    mass * (Fintype.card (Finset α) * (Lsite * Lrows))) G₀ at hG₀
  let Fout := fun z => (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * G₀ z
  have hFN : LipschitzWith (N * (mass * (Lgrid * d) +
      mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) Fout := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm]
    change ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * G₀ z -
      (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * G₀ w‖ ≤ _
    rw [← mul_sub, norm_mul]
    have hh := mul_le_mul_of_nonneg_left (hG₀.dist_le_mul z w)
      (norm_nonneg (allocatedFullGridNaturalVolume B U b S rowSets : ℂ))
    simpa only [N, dist_eq_norm, NNReal.coe_mul, coe_nnnorm, mul_assoc] using hh
  refine ⟨Fout, hFN, ?_, ?_⟩
  · intro z
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hG₀b z) (norm_nonneg _))
  · intro y
    have hh := allocatedSupportedSlicedProfile_ambient_surrogate_error B U b hR hσ S rowSets
      H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod hb o bW
      (allocatedRowSlicedIdeal B U b S rowSets ρ center width) rad hrad g hgb hgv
      model F hFv hzero hη happrox y
    have hfix := allocatedAffineRowIdeal_cutoff_fixes_mean_s2 B U b S rowSets o hb bW d rad hrad hR hσ
      T hT hsource hradius C hC hchart hb0 hσ1 hTideal ρ hρ hρ1 center width hw x gridLaw
      (fun u => principalAxisJoin grid u v₀) q y
    rw [hfix] at hh
    have heq : G₀ (coveredJetAmbientTorus U 1 y) =
        F (coveredJetAmbientTorus U 1 y) * (g (coveredJetAmbientTorus U d y) : ℂ) := by
      rw [← hG₀v]
      by_cases hy : y ∈ chart '' region
      · obtain ⟨z, hz, rfl⟩ := hy
        rw [allocatedChartGridMultiplier_apply B U b S rowTypes hb o bW d gridDensity z hz, hgv z hz, hFv]
      · rw [← hFv, hzero y hy, zero_mul, zero_mul]
    simpa only [Fout, heq, mul_assoc] using hh

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_ambient_surrogate_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_ambient_surrogate_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5, u_6}
