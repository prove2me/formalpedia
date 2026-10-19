-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedProductProfile_combined_error_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:21:42.245054+00:00
-- url     : https://prove2.me/submissions/0576de9d-8200-4882-9a3c-bbe38bc96516

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedMaskedProfile_chart_mean_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

theorem finite_site_product_expansion (c : ∀ a, I a → ℂ)
    (f : ∀ a, I a → S → ℂ) :
    (∏ a, ∑ k, c a k * ∏ s, f a k s) =
      ∑ k : ∀ a, I a, (∏ a, c a (k a)) * ∏ s, ∏ a, f a (k a) s := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.prod_mul_distrib, Finset.prod_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

universe u v

attribute [local instance] ScalarSiteExpansion.termFinite

namespace ScalarSiteExpansion

variable {S : Type u} [Fintype S]

theorem eval_norm_le (e : ScalarSiteExpansion.{u,v} S) {T D C H : ℝ} {L : ℝ≥0}
    (h : e.Bounds T D C L H) (y : S → ℤ) (x : S → ℝ) : ‖e.eval y x‖ ≤ C := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun i _ => ?_)).trans h.coefficient_le
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [norm_prod]
  exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun s _ => h.factor_bound i s _ _)).trans_eq
    Finset.prod_const_one

end ScalarSiteExpansion
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

theorem siteFamilyEval_eq (y : S → A → ℤ) (x : S → A → ℝ) :
    siteFamilyEval e y x = ∏ a, (e a).eval (fun s => y s a) (fun s => x s a) := by
  symm
  exact finite_site_product_expansion (fun a => (e a).coefficient)
    (fun a k s => (e a).factor k s (y s a : ZMod ((e a).period k)) (x s a))

end Erdos3

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
theorem allocatedComplexGridMultiplier_apply (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (z : MixedCoveredJetSource I O Q n d) (hz : z ∈ region) :
    allocatedComplexGridMultiplier B U b S O hb o bW d g (chart z) = g ((split z.1).1) := by
  simp only [allocatedComplexGridMultiplier,
    allocatedChartGridMultiplier_apply B U b S O hb o bW d _ z hz, Complex.re_add_im]

omit [∀ j, Fintype (O j)] in
theorem allocatedComplexGridMultiplier_zero (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (y : EuclideanJetLayers U O) (hy : y ∉ chart '' region) :
    allocatedComplexGridMultiplier B U b S O hb o bW d g y = 0 := by
  simp only [allocatedComplexGridMultiplier, allocatedChartGridMultiplier,
    restrictedChartDensity_zero _ _ _ _ hy, Complex.ofReal_zero, zero_mul, zero_add]

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

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "split" => coefficientJetAxisSplit O I n grid

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell

theorem allocatedFullGridSiteProfile_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I O E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))) :
    allocatedFullGridSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e (chart z) =
      allocatedFullGridSiteChartPrefactor B U b S rowSets d x hb o bW q y₀ f z *
        allocatedFullGridSiteApproximation B U b S rowSets e
          (allocatedFullGridRowsOfMixed B U b S rowSets z.1) := by
  rw [allocatedFullGridSiteProfile, allocatedComplexGridMultiplier_apply B U b S O hb o bW d _ z hz]
  have hprod : (∏ a : {a : gridAxes // ¬True},
      (laws a.val ((split z.1).1 a.val)).toReal) = 1 := by
    apply Finset.prod_eq_one
    intro a _
    exact False.elim (a.property True.intro)
  unfold allocatedSelectedGridExtension selectedProductExtension allocatedFullGridSiteChartPrefactor
    allocatedFullGridRowsOfMixed allocatedFullGridSelectedApproximation
  rw [hprod]
  simp only [Complex.ofReal_one, mul_one]
  ring

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
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
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

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

theorem allocatedProductFullGridProfile_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e (chart z) =
      allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) *
        allocatedFullGridSiteApproximation B U b S rowSets e
          (allocatedFullGridRowsOfMixed B U b S rowSets z.1) := by
  rw [allocatedProductFullGridProfile,
    allocatedFullGridSiteProfile_mixed B U b S rowSets d hR hσ x hb o bW q y₀ hcell f e z hz]
  unfold allocatedProductFullGridPrefactor allocatedFullGridSiteChartPrefactor
  exact (mul_assoc _ _ _).symm

theorem allocatedProductFullGridProfile_zero
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (y : EuclideanJetLayers U rowTypes) (hy : y ∉ chart '' region) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y = 0 := by
  rw [allocatedProductFullGridProfile, allocatedFullGridSiteProfile,
    allocatedComplexGridMultiplier_zero B U b S rowTypes hb o bW d _ y hy, zero_mul, mul_zero]

end Erdos3.VectorPolynomial

end

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
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedFullGridChartModel_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedFullGridChartModel B U b S rowSets d hb o bW e (chart z) =
      allocatedFullGridSiteApproximation B U b S rowSets e
        (allocatedFullGridRowsOfMixed B U b S rowSets z.1) :=
  allocatedComplexGridMultiplier_apply B U b S rowTypes hb o bW d _ z hz

theorem allocatedFullGridChartModel_norm_le
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤ ∏ a, Cc a := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedFullGridChartModel_mixed B U b S rowSets d hb o bW e z hz,
      allocatedFullGridSiteApproximation, siteFamilyEval_eq, norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun axis _ => (e axis).eval_norm_le (he axis) _ _)
  · rw [allocatedFullGridChartModel, allocatedComplexGridMultiplier_zero B U b S rowTypes hb o bW d _ y hy, norm_zero]
    exact Finset.prod_nonneg (fun a _ => (Finset.sum_nonneg (fun k _ => norm_nonneg _)).trans (he a).coefficient_le)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

theorem allocatedProductFullGridProfile_eq_model
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) (y : EuclideanJetLayers U rowTypes) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y =
      allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y *
        allocatedFullGridChartModel B U b S rowSets d hb o bW e y := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedProductFullGridProfile_mixed B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e z hz,
      allocatedFullGridChartModel_mixed B U b S rowSets d hb o bW e z hz]
  · rw [allocatedProductFullGridProfile_zero B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y hy,
      allocatedProductFullGridPrefactor_zero B U b S rowSets d r hr x hb o bW q y₀ f y hy, zero_mul]

theorem allocatedProductFullGridProfile_prefactor_error
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (F : EuclideanJetLayers U rowTypes → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (herr : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y - F y‖ ≤ η)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y -
      F y * allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤ η * ∏ a, Cc a := by
  rw [allocatedProductFullGridProfile_eq_model B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y,
    ← sub_mul, norm_mul]
  exact mul_le_mul (herr y) (allocatedFullGridChartModel_norm_le B U b S rowSets d hb o bW e he y)
    (norm_nonneg _) hη

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedUniformPhysicalSource
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

theorem allocatedSupportedSlicedProductProfile_chart_error
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hfullcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (rad : ℝ≥0) (hrad : 0 < rad)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε : ℝ}
    (z : MixedCoveredJetSource I rowTypes Q n d) (hz : z ∈ region)
    (he : ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        (gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e
          (allocatedFullGridRowsOfMixed B U b S rowSets z.1)‖ ≤ ε) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad (chart z) *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f (chart z)) : ℂ) -
      allocatedProductFullGridProfile B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e (chart z)‖ ≤
    ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f (chart z)‖ * ε := by
  rw [allocatedSupportedSlicedMaskedProfile_chart_mean_s2 B U b hR hσ S rowSets
    H step c hH hsubset q r hcell x u₀ hu₀ v₀ Q d hperiod hb o bW f z hz,
    allocatedProductFullGridProfile_mixed B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e z hz,
    Complex.ofReal_mul]
  let N : ℂ := (allocatedFullGridNaturalVolume B U b S rowSets : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).ne'
  have heq :
      allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad (chart z) *
        ((gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) : ℂ) *
          (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) : ℂ)) -
        allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f (chart z) *
          allocatedFullGridSiteApproximation B U b S rowSets e (allocatedFullGridRowsOfMixed B U b S rowSets z.1) =
      allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f (chart z) *
        (N * (gridDensity (allocatedFullGridRowsOfMixed B U b S rowSets z.1) : ℂ) -
          allocatedFullGridSiteApproximation B U b S rowSets e (allocatedFullGridRowsOfMixed B U b S rowSets z.1)) := by
    unfold allocatedProductFullGridPrefactor
    change _ - _ * (1 / N * _) * _ = (_ * (1 / N * _)) * (N * _ - _)
    field_simp
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left he (norm_nonneg _)

include hu₀ hperiod in

theorem allocatedSupportedSlicedProductProfile_error
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hfullcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (rad : ℝ≥0) (hrad : 0 < rad)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ) -
      allocatedProductFullGridProfile B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e y‖ ≤
    ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y‖ * ε := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    exact allocatedSupportedSlicedProductProfile_chart_error B U b hR hσ S rowSets H step c hH hsubset q r hcell
      x u₀ hu₀ v₀ Q d hperiod hb o bW f hfullcell rad hrad e z hz (he _)
  · have hzero (u) : allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y = 0 := by
      unfold allocatedWholeMaskedCoveredProfile allocatedCoveredProfileDensity
      exact restrictedChartDensity_zero _ _ _ _ hy
    simp only [hzero, FiniteProbabilityWeights.mean_const, Complex.ofReal_zero, mul_zero,
      allocatedProductFullGridProfile_zero B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e y hy,
      allocatedProductFullGridPrefactor_zero B U b S rowSets d rad hrad x hb o bW q y₀ f y hy,
      sub_zero, norm_zero, zero_mul, le_refl]

include hu₀ hperiod in

theorem allocatedSupportedSlicedProductProfile_combined_error_s2_oai
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hfullcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (rad : ℝ≥0) (hrad : 0 < rad)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε η : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε)
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (heb : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (F : EuclideanJetLayers U rowTypes → ℂ) (hη : 0 ≤ η)
    (hF : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y - F y‖ ≤ η)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ) -
      F y * allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
    ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y‖ * ε + η * ∏ a, Cc a := by
  have hg := allocatedSupportedSlicedProductProfile_error B U b hR hσ S rowSets H step c hH hsubset q r hcell
    x u₀ hu₀ v₀ Q d hperiod hb o bW f hfullcell rad hrad e he y
  have hl := allocatedProductFullGridProfile_prefactor_error B U b S rowSets d rad hrad x hb o bW q y₀ f
    hR hσ hfullcell e heb F hη hF y
  have ht := dist_triangle
    (allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ))
    (allocatedProductFullGridProfile B U b S rowSets d rad hrad x hb o bW q y₀ f hR hσ hfullcell e y)
    (F y * allocatedFullGridChartModel B U b S rowSets d hb o bW e y)
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add hg hl)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedProductProfile_combined_error_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedProductProfile_combined_error_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5}
