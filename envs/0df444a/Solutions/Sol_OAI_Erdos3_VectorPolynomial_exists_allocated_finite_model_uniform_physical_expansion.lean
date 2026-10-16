-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_finite_model_uniform_physical_expansion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-15T22:16:27.653076+00:00
-- url     : https://prove2.me/submissions/027c4bf2-a195-416f-8046-bb6a7c0e60ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_grid_physical_expansion_identity
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_physical_masked_factor

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

open scoped NNReal BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators NNReal

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {S T U D : Type*} [Fintype S] [Fintype T]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (d period : ℕ) [NeZero d] [NeZero period]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J Q : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]


variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))


variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α (Fin.val j + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem arrayCoordinateEquiv_integerMatrixTorusMap {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (A : Matrix S I ℤ) (x : SubspaceArrayTorus I U) (s : S) :
    arrayCoordinateEquiv U (integerMatrixTorusMap U A x) s =
      ∑ i, A s i • arrayCoordinateEquiv U x i := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U)
      (fun _ : Unit => ∑ i, (A s i : ℝ) • v i) =
    ∑ i, A s i • QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) (fun _ : Unit => v i)
  simp only [← map_zsmul, ← map_sum]
  congr 1
  funext u
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl (fun i _ => Int.cast_smul_eq_zsmul ℝ (A s i) (v i))

namespace VectorPolynomial

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

theorem coveredBooleanSiteValue_eq_siteFromLow
    (y : EuclideanJetLayers U jets) (s : Finset α) (j : Fin m) :
    coveredBooleanSiteValue U y s j () =
      (euclideanSubspaceTorusEquiv (U j)).symm
        (arrayCoordinateEquiv (U j) (siteFromLowBooleanJets U ((euclideanJetEquiv U).symm y) j) s) := by
  change (∑ r, boundedBooleanReconstructionMatrix α (j.val + 1) s r • y j r) =
    (euclideanSubspaceTorusEquiv (U j)).symm
      (arrayCoordinateEquiv (U j) (integerMatrixTorusMap (U j)
        (boundedBooleanReconstructionMatrix α (j.val + 1)) ((euclideanJetEquiv U).symm y j)) s)
  rw [arrayCoordinateEquiv_integerMatrixTorusMap]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  change y j r = (euclideanSubspaceTorusEquiv (U j)).symm
    (arrayCoordinateEquiv (U j) ((arrayCoordinateEquiv (U j)).symm
      (fun t => euclideanSubspaceTorusEquiv (U j) (y j t))) r)
  rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (root : K → ℤ) (D : Matrix α K ℤ)
variable (rowSets : Fin m → Finset (Finset α))
variable (d period : ℕ) [NeZero d] [NeZero period]

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoundedBooleanRowTransport
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem boundedBooleanJetRows_family_transport
    {ι α : Type*} [Fintype α] (h : ι → ℕ)
    (P : (O : ι → Type _) → [∀ i, Fintype (O i)] →
      (∀ i, O i → Finset α) → Prop)
    (hyp : P (fun i => BoundedBooleanJet α (h i)) (fun _ => Subtype.val))
    (inst : ∀ i, Fintype {s : Finset α // s ∈ boundedBooleanJetRows α (h i)}) :
    @P (fun i => {s : Finset α // s ∈ boundedBooleanJetRows α (h i)}) inst
      (fun _ => Subtype.val) := by
  let inst0 : ∀ i, Fintype (BoundedBooleanJet α (h i)) := inferInstance
  let Q (O : ι → Type _) (v : ∀ i, O i → Finset α) : Prop :=
    ∀ inst : ∀ i, Fintype (O i), @P O inst v
  have hq : Q (fun i => BoundedBooleanJet α (h i)) (fun _ => Subtype.val) := by
    intro inst
    exact (congrArg (fun ft : ∀ i, Fintype (BoundedBooleanJet α (h i)) =>
      @P (fun i => BoundedBooleanJet α (h i)) ft (fun _ => Subtype.val))
      (Subsingleton.elim inst0 inst)).mp hyp
  have he : (fun i (s : Finset α) => s.card ≤ h i) =
      (fun i s => s ∈ boundedBooleanJetRows α (h i)) := by
    funext i s
    exact propext (mem_boundedBooleanJetRows (h i) s).symm
  have hnew := (congrArg (fun R : ι → Finset α → Prop =>
    Q (fun i => {s // R i s}) (fun _ => Subtype.val)) he).mp hq
  exact hnew inst

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem physicalCubeRowSample_standard {X : Type*} {m dim : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    physicalCubeRowSample U d
      (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))
      p hm v = physicalCubeEuclideanSample U d p hm v := rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem physicalCubeEuclideanSample_site_reconstruction
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    siteFromLowBooleanJets U ((euclideanJetEquiv U).symm (physicalCubeEuclideanSample U d p hm v)) =
      physicalCubeCoveredSample U d p hm v := by
  rw [physicalCubeEuclideanSample_frame U d p hp hm v]
  change siteFromLowBooleanJets U ((euclideanJetEquiv U).symm (euclideanJetEquiv U
    (coefficientBooleanJetTorusMap U (fun _ : Fin q => 0) (1 : Matrix (Fin q) (Fin q) ℤ)
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      (affineCoefficientCoverSample U p hm d
        (fun k x => (standardPhysicalCubeFrame v (k, x) : ℝ)))))) = _
  rw [AddEquiv.symm_apply_apply, siteFromLowBooleanJets_coefficient]
  let D : Fin q → Fin q → ℤ := fun i j => if i = j then 1 else 0
  have hD : Matrix.of D = (1 : Matrix (Fin q) (Fin q) ℤ) := by
    ext i j
    simp [D, Matrix.one_apply]
  have h := coefficientCoverSample_sites U (fun _ : Fin q => 0) D d p hp hm
    (fun k x => (standardPhysicalCubeFrame v (k, x) : ℝ))
  rw [affineCoveredSiteSample_zero_base_physical, hD, physicalCubeRootDifferences_standard,
    standardPhysicalCubeOutput_frame] at h
  exact h

theorem coveredBooleanSiteValue_physical
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (v : X → (Unit ⊕ Fin q) → ℤ) (s : Finset (Fin q)) :
    coveredBooleanSiteValue U (physicalCubeEuclideanSample U d p hm v) s =
      physicalSingleSiteValue U d p hm (fun x => (physicalCubeVertexValue v s x : ℝ)) := by
  funext j t
  cases t
  rw [coveredBooleanSiteValue_eq_siteFromLow, physicalCubeEuclideanSample_site_reconstruction U d p hm hp v]
  rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem coveredRowsSiteValue_physical
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (v : X → (Unit ⊕ Fin dim) → ℤ) (s : Finset (Fin dim)) :
    coveredRowsSiteValue (fun j : Fin m => boundedBooleanJetRows (Fin dim) (j.val + 1)) U
      (physicalCubeRowSample U d (fun _ => Subtype.val) p hm v) s =
        physicalSingleSiteValue U d p hm (fun x => (physicalCubeVertexValue v s x : ℝ)) := by
  let P (O : Fin m → Type) [∀ j, Fintype (O j)]
      (rows : ∀ j, O j → Finset (Fin dim)) : Prop :=
    ∀ (v : X → (Unit ⊕ Fin dim) → ℤ) (s : Finset (Fin dim)) (j : Fin m),
      (∑ t : O j, (if rows j t ⊆ s then (1 : ℤ) else 0) •
        physicalCubeRowSample U d rows p hm v j t) =
          physicalSingleSiteValue U d p hm (fun x => (physicalCubeVertexValue v s x : ℝ)) j ()
  have hstd : P (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) (fun _ => Subtype.val) := by
    intro v s j
    have h := congrArg (fun y => y j ()) (coveredBooleanSiteValue_physical U d p hm hp v s)
    simpa only [coveredBooleanSiteValue, boundedBooleanReconstructionMatrix,
      physicalCubeRowSample_standard] using h
  have h := boundedBooleanJetRows_family_transport (fun j : Fin m => j.val + 1) P hstd
    (fun j => Finset.Subtype.fintype (boundedBooleanJetRows (Fin dim) (j.val + 1)))
  funext j t
  cases t
  exact h v s j

end Erdos3.BooleanCubeKernel

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

universe u v

attribute [local instance] ScalarSiteExpansion.termFinite

namespace ScalarSiteExpansion

variable {S : Type u} [Fintype S]

end ScalarSiteExpansion
end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion

open scoped NNReal

universe u v

variable {S : Type u} {e : ScalarSiteExpansion.{u,v} S}

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]
attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

variable {T D C H : A → ℝ} {L : ℝ≥0}
variable (h : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {A D S : Type*} [Fintype A] [Fintype D]

variable (e : A → ScalarSiteExpansion S) (selected : A → D) (scale : A → ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {α : Type*} [Fintype α] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {X A V : Type*} [Fintype X] [Fintype A]
variable (spatialPeriod : ℕ) (q : X → ℕ) (e : A → ScalarSiteExpansion V)
variable (k : ∀ a, (e a).Term) (idealPeriod : ℕ)

namespace BooleanCubeKernel

variable {K α : Type*} [Fintype K] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) {spatialPeriod M : ℕ}
variable (hM : ∀ x, q x * spatialPeriod ∣ M)
variable (t : X → SpatialSiteLabel α spatialPeriod b r) (s : Finset α)

end BooleanCubeKernel
end Erdos3

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
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


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
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


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

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

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

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period] (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

variable {K : Type*} [Fintype K] (a : K → ℂ)
variable (f : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (v : X → (Unit ⊕ Fin dim) → ℤ)

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
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "r" => allocatedProductIdealSiteRadius (G := G) B rowSets

variable (hR : ∀ j, 0 < R j)

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

variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q : ℕ) (δ : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (hperiod : ∀ j, integerScalarLattice {t : Finset (Fin dim) // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable {X : Type*} [Fintype X]
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (stride N : X → ℕ) (hs : ∀ t, 0 < stride t) (hN : ∀ t, 0 < N t)
variable (modulus : ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value) (base : X → ℤ)
variable {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N stride
local notation "T" => trimmedSpatialSlopeScale W τ N stride


end Erdos3.BooleanCubeKernel

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

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

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
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

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
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

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
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]

local notation "single" => (fun _ : Fin m => Unit)

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

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


theorem exists_allocated_physical_masked_expansion
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lout := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → Finset (Fin dim) →
        ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label k s, LipschitzWith Lout (g label k s)) ∧
      (∀ label k s z, ‖g label k s z‖ ≤ 1) ∧
      ∀ {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
        (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ),
        allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
          (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
          ∑ label, ∑ k, ((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k) *
              ∏ s, g label k s
                ((fun a => (eval (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)) (p a.1) a.2.2 : UnitAddCircle)),
                  (fun a => ((eval (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)) (p a.1) a.2 / period : ℝ) : UnitAddCircle))) := by
  intro Lcoord Lout
  have hex (label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
      (k : T) (s : Finset (Fin dim)) :=
    exists_allocated_physical_masked_factor B U b S o hb bW d r hr period hdiv hR C hC hchart hbudget
      Cforward hforward K hK (label s) (f k s) (hf k s) (hf1 k s)
  choose g hL hg hv using hex
  refine ⟨g, hL, hg, ?_⟩
  intro X p hp hm v
  unfold allocatedProductChartIdealApproximation
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  have hs (s : Finset (Fin dim)) := hv label k s p hm
    (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ))
  simp_rw [BooleanCubeKernel.coveredRowsSiteValue_physical U d p hm hp v, hs]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

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

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

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

theorem exists_allocated_long_physical_expansion_identity
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {T : Type*} [Fintype T] (a : T → ℂ)
    (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s z, ‖f k s z‖ ≤ 1)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lout := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
      max (L * Lcoord * period) (4 * period)
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
        T → Finset (Fin dim) →
        ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) → ℂ,
      (∀ label k s, LipschitzWith Lout (g label k s)) ∧
      (∀ label k s z, ‖g label k s z‖ ≤ 1) ∧
      AllocatedLongPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW a f p hm g := by
  intro Lcoord Lout
  obtain ⟨g, hg, hbnd, hv⟩ := exists_allocated_physical_masked_expansion B U b S x y₀ q d period r hr hb o bW
    hdiv hR C hC hchart hbudget Cforward hforward K hK a f hf hf1
  exact ⟨g, hg, hbnd, hv p hp hm⟩

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

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

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
  obtain ⟨gl, hgl, hglb, hlong⟩ := exists_allocated_long_physical_expansion_identity B U b S x y₀ q d period r hr hb o bW
    hdiv hR C hC hchart hsite Cforward hforward K hK a f hf hf1 p hp hm
  obtain ⟨gg, hgg, hgrid⟩ := exists_allocated_grid_physical_expansion_identity B U b S x y₀ q d period r hr hb o bW e hR he Q hQ
    Cforward hforward K hK C hC hchart hbudget a f p hp hm
  exact join_allocated_physical_expansions B U b S x y₀ q d period r hr hb o bW e a f p hm gl gg hgl
    (fun k s => (hgg k s).1) hglb (fun k s => (hgg k s).2)
    hlong hgrid

theorem exists_allocated_finite_model_uniform_physical_expansion
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

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_finite_model_uniform_physical_expansion.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.exists_allocated_finite_model_uniform_physical_expansion.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
