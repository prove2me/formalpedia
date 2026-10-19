-- Prove2me | solution 1 for OAI.Erdos3.BooleanCubeKernel.physicalRowChart_base_matching_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:09:15.253772+00:00
-- url     : https://prove2.me/submissions/93ef183e-d825-4c99-8351-f60503d72158

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B113
import Definitions.Def_OAIE3v2B178

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.StandardJetFourier
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical

theorem normalizedCoveredChart_projection {D Q : Type*} [Fintype D] [Fintype Q]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) {n : ℕ} (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (bW : Basis Q ℤ (latticeSection (standardEuclideanLattice D) W))
    (d : ℕ) [NeZero d] (x : (W × (Fin n → ℤ)) × (Q → ZMod d)) :
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d
      (normalizedCoveredChart W b hb bW d x) = normalizedLatticeQuotient W b hb x.1 := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (Nat.pos_of_ne_zero (NeZero.ne d))
  have hk : quotientIntegerCover Γ d (e x.2).val = 0 := (e x.2).property
  change quotientIntegerCover Γ d (normalizedCoverLift W b hb d x.1 + (e x.2).val) = _
  rw [map_add,
    normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)), hk, add_zero]

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

theorem physicalSingleSiteValue_projection (d : ℕ) [NeZero d] (w : X → ℝ) (j : Fin m) :
    quotientIntegerCover
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d
      (physicalSingleSiteValue U d p hm w j ()) =
        QuotientAddGroup.mk (physicalEuclideanSitePoint U p hm w j) := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  change euclideanSubspaceTorusEquiv (U j)
    (d • (euclideanSubspaceTorusEquiv (U j)).symm
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
        (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j))))) = _
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  change quotientIntegerCover (subspaceArrayIntegerLattice Unit (U j)) d
      (QuotientAddGroup.mk' _ ((d : ℝ)⁻¹ •
        (fun _ : Unit => eval w (restrictCoefficients (U j) (p j) (hm j))))) =
      euclideanSubspaceTorusEquiv (U j) (QuotientAddGroup.mk' _ (physicalEuclideanSitePoint U p hm w j))
  rw [euclideanSubspaceTorusEquiv_mk, quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ hd, one_smul]
  congr 1

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalRowChartMatching
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule VectorPolynomial
open scoped Classical

variable {X : Type*} {m dim : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

theorem physicalRowChart_base_matching_s2_oai
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (z : MixedCoveredJetSource I O E n d)
    (hz : mixedCoveredJetChart U o b hb bW d z =
      physicalCubeRowSample U d (fun _ => Subtype.val) p hm v)
    (s : Finset (Fin dim)) (j : Fin m) :
    (QuotientAddGroup.mk (physicalEuclideanSitePoint U p hm
      (fun x => (physicalCubeVertexValue v s x : ℝ)) j) : euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j)
          (mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()).1 := by
  have hs : mixedCoveredJetChart U o b hb bW d (mixedCoveredRowsSiteValue rowSets d z s) =
      physicalSingleSiteValue U d p hm (fun x => (physicalCubeVertexValue v s x : ℝ)) := by
    rw [mixedCoveredRowsSiteValue_chart, hz]
    exact coveredRowsSiteValue_physical U d p hm hp v s
  have h := congrArg (fun y : EuclideanJetLayers U (fun _ => Unit) =>
    quotientIntegerCover
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d
      (y j ())) hs
  rw [physicalSingleSiteValue_projection] at h
  change quotientIntegerCover _ d (normalizedCoveredChart (euclideanSubspace (U j))
    (b j) (hb j) (bW j) d (mixedCoveredJetCoordinates U o d
      (mixedCoveredRowsSiteValue rowSets d z s) j ())) = _ at h
  rw [normalizedCoveredChart_projection] at h
  exact h.symm

end Erdos3.BooleanCubeKernel

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.BooleanCubeKernel.physicalRowChart_base_matching_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.BooleanCubeKernel.physicalRowChart_base_matching_s2_oai.{u_1, u_2, u_3, u_4}
