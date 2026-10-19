-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_finite_model_uniform_physical_expansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:10:27.41499+00:00
-- url     : https://prove2.me/submissions/b6b1b30d-7969-4370-8d78-9ca9adbae9d6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_physicalRowChart_base_matching_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductChartIdealApproximation_zero_outside_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductSiteCutoff_sites_quarter_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_cover_site_expansion_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_long_physical_expansion_identity_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

theorem finiteSiteExpansion_product {A B S : Type*} [Fintype A] [Fintype B] [Fintype S]
    (a : A → ℂ) (b : B → ℂ) (f : A → S → ℂ) (g : B → S → ℂ) :
    (∑ i, a i * ∏ s, f i s) * (∑ j, b j * ∏ s, g j s) =
      ∑ i, ∑ j, (a i * b j) * ∏ s, f i s * g j s := by
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteSiteExpansion_product_factor {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℂ) (g : Y → ℂ) {L K : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hfb : ∀ x, ‖f x‖ ≤ 1) (hgb : ∀ y, ‖g y‖ ≤ 1) :
    LipschitzWith (L + K) (fun z : X × Y => f z.1 * g z.2) ∧
      ∀ z : X × Y, ‖f z.1 * g z.2‖ ≤ 1 := by
  constructor
  · simpa only [one_mul, mul_one, add_comm, Function.comp_def] using
      lipschitz_mul_of_bounds (fun z : X × Y => f z.1) (fun z : X × Y => g z.2)
        (hf.comp LipschitzWith.prod_fst) (hg.comp LipschitzWith.prod_snd)
        (Bf := 1) (Bg := 1) (fun z => hfb z.1) (fun z => hgb z.2)
  · intro z
    rw [norm_mul]
    exact (mul_le_mul (hfb _) (hgb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem finiteNestedSiteExpansion_transport {A B C S : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype S]
    (a : A → B → ℂ) (b : C → ℂ) (f : A → B → S → ℂ) (g : C → S → ℂ)
    {z y : ℂ} (hz : z = ∑ i, ∑ j, a i j * ∏ s, f i j s)
    (hy : z * y = z * ∑ k, b k * ∏ s, g k s) :
    z * y = ∑ i, ∑ j, ∑ k, (a i j * b k) * ∏ s, f i j s * g k s := by
  rw [hy, hz, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => finiteSiteExpansion_product _ _ _ _)

theorem siteBudget_of_rowBudget {a b t E : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) (ht : 0 ≤ t)
    (h : (a + 1) * (b * t) ≤ E) : t ≤ E := by
  have hbt : t ≤ b * t := (one_mul t).symm.le.trans (mul_le_mul_of_nonneg_right hb ht)
  exact hbt.trans ((le_mul_of_one_le_left (mul_nonneg (by linarith) ht) (by linarith)).trans h)

theorem finiteNestedSiteExpansion_product_functions {A B C S X Y : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype S]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : A → B → S → X → ℂ) (g : C → S → Y → ℂ)
    {L : ℝ≥0} {K : C → ℝ≥0}
    (hf : ∀ i j s, LipschitzWith L (f i j s)) (hg : ∀ k s, LipschitzWith (K k) (g k s))
    (hfb : ∀ i j s x, ‖f i j s x‖ ≤ 1) (hgb : ∀ k s y, ‖g k s y‖ ≤ 1) :
    ∃ h : A → B → C → S → X × Y → ℂ,
      (∀ i j k s, LipschitzWith (L + K k) (h i j k s)) ∧
      (∀ i j k s z, ‖h i j k s z‖ ≤ 1) ∧
      ∀ (a : A → B → ℂ) (b : C → ℂ) (x : S → X) (y : C → S → Y) (z w : ℂ),
        z = ∑ i, ∑ j, a i j * ∏ s, f i j s (x s) →
        z * w = z * ∑ k, b k * ∏ s, g k s (y k s) →
        z * w = ∑ i, ∑ j, ∑ k, (a i j * b k) * ∏ s, h i j k s (x s, y k s) := by
  refine ⟨fun i j k s z => f i j s z.1 * g k s z.2, ?_, ?_, ?_⟩
  · intro i j k s
    exact (finiteSiteExpansion_product_factor _ _ (hf i j s) (hg k s) (hfb i j s) (hgb k s)).1
  · intro i j k s z
    exact (finiteSiteExpansion_product_factor _ _ (hf i j s) (hg k s) (hfb i j s) (hgb k s)).2 z
  · intro a b x y z w hz hw
    exact finiteNestedSiteExpansion_transport a b (fun i j s => f i j s (x s))
      (fun k s => g k s (y k s)) hz hw

end Erdos3

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integerBooleanSitesFromRows_eq_mulVec (rows : Finset (Finset α))
    (z : rows → ℤ) :
    integerBooleanSitesFromRows rows z = rowRestrictedSiteMatrix rows *ᵥ z := by
  funext s
  let F := fun t => booleanReconstructionMatrix α s t *
    (if ht : t ∈ rows then z ⟨t, ht⟩ else 0)
  have hsub : (∑ t ∈ rows, F t) = ∑ t : Finset α, F t := by
    apply Finset.sum_subset (Finset.subset_univ rows)
    intro t _ ht
    simp only [F, dif_neg ht, mul_zero]
  calc
    _ = ∑ t : Finset α, F t := rfl
    _ = ∑ t ∈ rows, F t := hsub.symm
    _ = ∑ t : rows, F t := Finset.sum_subtype rows (by simp) F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [F, dif_pos t.property, rowRestrictedSiteMatrix]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

omit [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)] in
theorem mixedCoveredRowsSiteValue_integer (d : ℕ)
    (z : MixedCoveredJetSource I rows E n d) (s : Finset α) (j : Fin m) (i : Fin (n j)) :
    ((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () =
      integerBooleanSitesFromRows (rowSets j) ((z.1 j).2 i) s := by
  rw [integerBooleanSitesFromRows_eq_mulVec]
  rfl

end VectorPolynomial
end Erdos3

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

end Erdos3.VectorPolynomial

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

omit [∀ j, Fintype (J j)] in
theorem physicalEuclideanSitePoint_apply (w : X → ℝ) (j : Fin m) (i : J j) :
    (physicalEuclideanSitePoint U p hm w j).val i = eval w (p j) i := by
  change (eval w (restrictCoefficients (U j) (p j) (hm j))).val i = _
  rw [eval_restrictCoefficients]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

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
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "ig" => allocatedGridIntegerAxis B U b S

omit [Fintype α] [DecidableEq α] in
theorem allocatedFullGridRowsOfMixed_integer
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) (a : gridAxes) :
    allocatedGridIntegerValues B U b S rowSets a
        (allocatedFullGridRowsOfMixed B U b S rowSets z a) = (z (ig a).1).2 (ig a).2 := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ)

omit [∀ j, Fintype (E j)] in
theorem allocatedFullGridSiteValues_mixed (z : MixedCoveredJetSource I O E n d)
    (s : Finset α) (a : gridAxes) :
    allocatedFullGridSiteValues B U b S rowSets
        (allocatedFullGridRowsOfMixed B U b S rowSets z.1) s a =
      ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a).1).2 (ig a).2 () := by
  rw [mixedCoveredRowsSiteValue_integer]
  unfold allocatedFullGridSiteValues
  rw [allocatedFullGridRowsOfMixed_integer]

omit [∀ j, Fintype (E j)] in
theorem allocatedFullGridSiteApproximation_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I O E n d) :
    allocatedFullGridSiteApproximation B U b S rowSets e
        (allocatedFullGridRowsOfMixed B U b S rowSets z.1) =
      siteFamilyEval e
        (fun s a => ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a).1).2 (ig a).2 ())
        (fun s a => (((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a).1).2 (ig a).2 () : ℝ) /
          allocatedGridNaturalScale B U b S a) := by
  have hy : allocatedFullGridSiteValues B U b S rowSets
      (allocatedFullGridRowsOfMixed B U b S rowSets z.1) =
      fun s a => ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a).1).2 (ig a).2 () := by
    funext s a
    exact allocatedFullGridSiteValues_mixed B U b S rowSets d z s a
  unfold allocatedFullGridSiteApproximation
  rw [hy]

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
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

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
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem join_allocated_physical_expansions
    (gl : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → Finset (Fin dim) → LongSpace → ℂ)
    (gg : (∀ a, (e a).Term) → Finset (Fin dim) → GridSpace → ℂ)
    {LL : ℝ≥0} {LG : (∀ a, (e a).Term) → ℝ≥0}
    (hgl : ∀ label i s, LipschitzWith LL (gl label i s))
    (hgg : ∀ k s, LipschitzWith (LG k) (gg k s))
    (hglb : ∀ label i s z, ‖gl label i s z‖ ≤ 1)
    (hggb : ∀ k s z, ‖gg k s z‖ ≤ 1)
    (hlong : AllocatedLongPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW a f p hm gl)
    (hgrid : AllocatedGridPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm gg) :
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ,
      (∀ label i k s, LipschitzWith (LL + LG k) (g label i k s)) ∧
      (∀ label i k s z, ‖g label i k s z‖ ≤ 1) ∧
      AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  obtain ⟨g, hgL, hgb, hgv⟩ := finiteNestedSiteExpansion_product_functions gl gg hgl hgg hglb hggb
  refine ⟨g, hgL, hgb, ?_⟩
  intro v
  exact hgv
    (fun label i => (2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) (coverSiteCoefficient e)
    (fun s => physicalMaskedFactorInput period p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))
    (fun k s => physicalGridFactorInput (commonSitePeriod e k) p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))
    _ _ (hlong v) (hgrid v)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFiniteModelGridCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem exists_allocated_finite_model_grid_cover
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : gridAxes, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a).1 (ig a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (r : ℝ≥0) (hr : 0 < r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) *
      (Fintype.card (Finset (Fin dim)) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card gridAxes * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
        (q period : ℕ) [NeZero period] {K₀ : Type*} [Fintype K₀]
        (a₀ : K₀ → ℂ) (f : K₀ → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
        {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
          (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
          ∀ (hm : ∀ j a, coefficients (p j) a ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a₀ f
                (physicalCubeRowSample U d rows p hm v) *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e
                (physicalCubeRowSample U d rows p hm v) =
              allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a₀ f
                (physicalCubeRowSample U d rows p hm v) *
                ∑ k, coverSiteCoefficient e k * ∏ s,
                  g k s (fun a => (((eval (fun z => (physicalCubeVertexValue v s z : ℝ))
                    (p a.1) a.2) / commonSitePeriod e k : ℝ) : UnitAddCircle)) := by
  obtain ⟨g, hg, hc, hv⟩ := exists_allocated_cover_site_expansion_s2 (G := G)
    (A := gridAxes) (S := Finset (Fin dim)) B U b e ig hR he Q hQ
    o Cforward hforward K hK hb bW
  refine ⟨g, hg, hc, ?_⟩
  intro x y₀ q period _ K₀ _ a₀ f X p hp hm v
  let model := allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a₀ f
  by_cases hy : physicalCubeRowSample U d rows p hm v ∈ chart '' region
  · obtain ⟨z, hz, hzy⟩ := hy
    rw [← hzy, allocatedFullGridChartModel_mixed B U b S rowSets d hb o bW e z hz]
    by_cases hzero : model (chart z) = 0
    · change model (chart z) * _ = model (chart z) * _
      rw [hzero, zero_mul, zero_mul]
    · have hcut : allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) ≠ 0 := by
        intro hcut
        apply hzero
        unfold model allocatedProductChartIdealApproximation
        apply Finset.sum_eq_zero
        intro label _
        apply Finset.sum_eq_zero
        intro k _
        rw [allocatedMaskedChartProduct_zero_of_cutoff_zero B U b S o hb bW d r hr period rowSets
          (f k) label _ hcut, mul_zero]
      have hs := allocatedProductSiteCutoff_sites_quarter_s2 B U b S rowSets o hb bW d r hr hR
        C hC hchart hbudget z hz hcut
      have hmatch := physicalRowChart_base_matching_s2 U o b hb bW d p hp hm v z hzy
      have hval := hv
        (fun s => physicalEuclideanSitePoint U p hm (fun z => (physicalCubeVertexValue v s z : ℝ)))
        (fun s j => mixedArrayRegroup (I j) (Fin (n j)) Unit
          ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) hmatch
        (fun s j i => (hs s j (Set.mem_univ j) () (Set.mem_univ ())).1 i)
      apply congrArg (fun c : ℂ => model (chart z) * c)
      rw [allocatedFullGridSiteApproximation_mixed B U b S rowSets d e z]
      simpa only [allocatedGridNaturalScale, physicalEuclideanSitePoint_apply,
        mixedArrayRegroup_apply] using hval.symm
  · rw [allocatedProductChartIdealApproximation_zero_outside_s2 B U b S rowSets x y₀ q d period r hr hb o bW
      hR C hC hchart hbudget a₀ f _ hy, zero_mul, zero_mul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion
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
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_grid_physical_expansion_identity
    (hR : ∀ j, 0 < R j)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) *
      (Fintype.card (Finset (Fin dim)) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    ∃ g : (∀ a, (e a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ k s, LipschitzWith (max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * L) * Q) *
        (K * ∑ j, Cforward j * Fintype.card (J j)) * commonSitePeriod e k)
          (4 * commonSitePeriod e k)) (g k s) ∧ ∀ v, ‖g k s v‖ ≤ 1) ∧
      AllocatedGridPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  classical
  obtain ⟨g, hg, _hcoeff, hv⟩ := exists_allocated_finite_model_grid_cover B U b hR S d hb o bW e he Q hQ
    Cforward hforward K hK r hr C hC hchart hbudget
  exact ⟨g, hg, hv x y₀ q period a f p hp hm⟩

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
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

theorem exists_allocated_finite_model_physical_expansion
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    let Lgrid := fun k => max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * commonSitePeriod e k) (4 * commonSitePeriod e k)
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → (∀ a, (e a).Term) → Finset (Fin dim) →
        (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
          ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label i k s, LipschitzWith (Llong + Lgrid k) (g label i k s)) ∧
      (∀ label i k s z, ‖g label i k s z‖ ≤ 1) ∧
      AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  classical
  intro Lcoord Llong Lgrid
  have hsite (j : Fin m) : C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4 := by
    exact siteBudget_of_rowBudget (Nat.cast_nonneg _) (by exact_mod_cast Fintype.card_pos)
      (mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))) (hbudget j)
  obtain ⟨gl, hgl, hglb, hlong⟩ := exists_allocated_long_physical_expansion_identity_s2 B U b S x y₀ q d period r hr hb o bW
    hdiv hR C hC hchart hsite Cforward hforward K hK a f hf hf1 p hp hm
  obtain ⟨gg, hgg, hgrid⟩ := exists_allocated_grid_physical_expansion_identity B U b S x y₀ q d period r hr hb o bW e hR he Q hQ
    Cforward hforward K hK C hC hchart hbudget a f p hp hm
  exact join_allocated_physical_expansions B U b S x y₀ q d period r hr hb o bW e a f p hm gl gg hgl
    (fun k s => (hgg k s).1) hglb (fun k s => (hgg k s).2)
    hlong hgrid

theorem exists_allocated_finite_model_uniform_physical_expansion_s2_oai
    (hdiv : period ∣ d) (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Q : ℝ≥0) (hQ : ∀ a, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Q)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (Pperiod Vmax : ℝ≥0) (hPperiod : (period : ℝ≥0) ≤ Pperiod)
    (hVmax : ∀ a, V a ≤ Vmax) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Llong := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * Pperiod) (4 * Pperiod)
    let Lgrid := max (((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Lg) * Q) *
      Lcoord * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}) (4 * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → (∀ a, (e a).Term) → Finset (Fin dim) →
        (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
          ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label i k s, LipschitzWith (Llong + Lgrid) (g label i k s)) ∧
      (∀ label i k s z, ‖g label i k s z‖ ≤ 1) ∧
      AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  intro Lcoord Llong Lgrid
  obtain ⟨g, hg, hgb, hidentity⟩ := exists_allocated_finite_model_physical_expansion
    B U b S x y₀ q d period r hr hb o bW e hdiv hR C hC hchart hbudget
    Cforward hforward K hK a f hf hf1 he Q hQ p hp hm
  refine ⟨g, ?_, hgb, hidentity⟩
  intro label i k s
  apply (hg label i k s).weaken
  have hk : (commonSitePeriod e k : ℝ≥0) ≤ Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} := by
    exact_mod_cast commonSitePeriod_le_pow e he hVmax k
  apply add_le_add
  · exact add_le_add le_rfl (max_le_max (mul_le_mul_of_nonneg_left hPperiod zero_le) (mul_le_mul_of_nonneg_left hPperiod zero_le))
  · exact max_le_max (mul_le_mul_of_nonneg_left hk zero_le) (mul_le_mul_of_nonneg_left hk zero_le)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_finite_model_uniform_physical_expansion_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.exists_allocated_finite_model_uniform_physical_expansion_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
