-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_long_physical_expansion_identity_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:10:28.351986+00:00
-- url     : https://prove2.me/submissions/cf8730a4-ab1d-4a91-8ff7-0c3ea7a13fd8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_masked_cover_factor_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealPoint_coordinates (x : EuclideanSpace ℝ D) :
    mixedRealPoint W b o (mixedRealCoordinates W b o x) = x := by
  change (normalizedOrthogonalChart W b).symm
    ((orthonormalChart o) ((orthonormalChart o).symm ((normalizedOrthogonalChart W b) x).1),
      ((normalizedOrthogonalChart W b) x).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteAmbient
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ) [NeZero d]
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem physicalSingleSiteValue_ambient (w : X → ℝ) :
    coveredJetAmbientTorus U d (physicalSingleSiteValue U d p hm w) =
      fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
        ((eval w (p a.1)) a.2.2 : UnitAddCircle) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  funext a
  rcases a with ⟨j, t, i⟩
  cases t
  change subspaceAmbientTorus (U j) (euclideanSubspaceTorusEquiv (U j)
    (d • (euclideanSubspaceTorusEquiv (U j)).symm
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
        (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j)))))) i = _
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  change subspaceAmbientTorus (U j) (quotientIntegerCover _ d
    (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
      (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j))))) i = _
  rw [quotientIntegerCover_mk, subspaceAmbientTorus_mk]
  simp only [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [eval_restrictCoefficients]

end Erdos3.BooleanCubeKernel

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

theorem allocatedFullAmbientSiteCoordinates_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  let pz := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => z ⟨a.1, (), k⟩))
  let pw := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => w ⟨a.1, (), k⟩))
  have hout : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤ dist pz pw := by
    rcases a.2 with i | i
    · exact (dist_le_pi_dist pz.1 pw.1 i).trans (le_max_left _ _)
    · exact (dist_le_pi_dist pz.2 pw.2 i).trans (le_max_right _ _)
  have hrow := ((mixedRealCoordinates_lipschitz (euclideanSubspace (U a.1)) (b a.1) (o a.1) (hC a.1)).comp
    (euclideanFromCoordinates_lipschitz (D := J a.1))).dist_le_mul
      (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩)
  have hin : dist (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mpr (fun k => dist_le_pi_dist z w ⟨a.1, (), k⟩)
  have hc : C a.1 * Fintype.card (J a.1) ≤ ∑ j, C j * Fintype.card (J j) :=
    Finset.single_le_sum (f := fun j => C j * Fintype.card (J j))
      (fun _ _ => by positivity) (Finset.mem_univ a.1)
  have hd : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤
      ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w :=
    (hout.trans hrow).trans ((mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg))
  change |Sum.elim pz.1 pz.2 a.2 / R a.1 - Sum.elim pw.1 pw.2 a.2 / R a.1| ≤ _
  rw [← sub_div, abs_div, abs_of_pos (hR a.1)]
  calc
    _ ≤ (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) / R a.1 :=
      div_le_div_of_nonneg_right hd (hR a.1).le
    _ = (R a.1)⁻¹ * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) := by ring
    _ ≤ (K : ℝ) * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) :=
      mul_le_mul_of_nonneg_right (hK a.1) (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)
    _ = _ := by rw [NNReal.coe_mul, mul_assoc]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedBufferedAmbientCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

theorem allocatedFullAmbientSiteCoordinates_norm_bound
    (hR : ∀ j, 0 < R j) (z : ambient → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ a, |allocatedFullAmbientSiteCoordinates (R := R) U b o z a| ≤ T)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖(EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (T * R j)) := by
  let v := (EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)
  let w := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j) v
  have hu (i : I j) : |w.1 i| ≤ T * R j := by
    have h := hz ⟨j, .inl i⟩
    change |w.1 i / R j| ≤ T at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have hv (i : Fin (n j)) : |w.2 i| ≤ T * R j := by
    have h := hz ⟨j, .inr i⟩
    change |w.2 i / R j| ≤ T at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have h := mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg hT (hR j).le) (hchart j) w.1 w.2 hu hv
  dsimp only [w] at h
  rw [Prod.mk.eta, mixedRealPoint_coordinates] at h
  exact h

variable (r : ℝ≥0) (hr : 0 < r)

theorem allocatedBufferedAmbientCutoff_range (z : ambient → ℝ) :
    0 ≤ allocatedBufferedAmbientCutoff (R := R) U b o r hr z ∧
      allocatedBufferedAmbientCutoff (R := R) U b o r hr z ≤ 1 :=
  (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.1 _

theorem allocatedBufferedAmbientCutoff_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith ((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
      (K * ∑ j, C j * Fintype.card (J j)))
      (allocatedBufferedAmbientCutoff (R := R) U b o r hr) :=
  (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.2.2.comp
    (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR C hC K hK)

theorem allocatedBufferedAmbientCutoff_support (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (z : ambient → ℝ) (hz : allocatedBufferedAmbientCutoff (R := R) U b o r hr z ≠ 0) :
    ∀ a, |z a| ≤ 1 / 4 := by
  have hcoord := (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.2.1
    (allocatedFullAmbientSiteCoordinates (R := R) U b o z) hz
  rintro ⟨j, t, k⟩
  cases t
  have h := (allocatedFullAmbientSiteCoordinates_norm_bound U b o hR z (by positivity)
    hcoord C hC hchart j).trans (hbudget j)
  exact (PiLp.norm_apply_le ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)) k).trans h

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_range (x : ambient → UnitAddCircle) :
    0 ≤ allocatedBufferedTorusCutoff (R := R) U b o r hr x ∧
      allocatedBufferedTorusCutoff (R := R) U b o r hr x ≤ 1 := by
  apply smallBoxTorusKernel_range _ zero_le_one (allocatedBufferedAmbientCutoff_range U b o r hr)
  intro z hz i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget z hz i).trans_lt (by norm_num)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_lipschitz
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith ((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
      (K * ∑ j, Cforward j * Fintype.card (J j))) (allocatedBufferedTorusCutoff (R := R) U b o r hr) := by
  apply smallBoxTorusKernel_lipschitz _
    (allocatedBufferedAmbientCutoff_lipschitz U b o r hr hR Cforward hforward K hK)
    (fun z => (allocatedBufferedAmbientCutoff_range U b o r hr z).1)
  intro z hz i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget z hz i).trans_lt (by norm_num)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion
namespace OAI

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
local notation "ambient" => JetAmbientIndex single J

theorem exists_allocated_physical_masked_factor
    (hdiv : period ∣ d)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ z, ‖f z‖ ≤ 1) :
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lcut := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord
    let Lout := Lcut + max (L * Lcoord * period) (4 * period)
    ∃ g : (ambient → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle) → ℂ,
      LipschitzWith Lout g ∧ (∀ z, ‖g z‖ ≤ 1) ∧
      ∀ {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (hm : ∀ j e, coefficients (p j) e ∈ U j) (t : X → ℝ),
        allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f
          (BooleanCubeKernel.physicalSingleSiteValue U d p hm t) =
          2 * g ((fun a => (eval t (p a.1) a.2.2 : UnitAddCircle)),
            (fun a => ((eval t (p a.1) a.2 / period : ℝ) : UnitAddCircle))) := by
  intro Lcoord Lcut Lout
  obtain ⟨g₀, hg₀, hgb, hgv⟩ := exists_allocated_masked_cover_factor_s2 B U b S o hb bW d r hr period
    hdiv hR C hC hchart hbudget Cforward hforward K hK label f hf hf1
  let χ := allocatedBufferedTorusCutoff (R := R) U b o r hr
  have hχ := allocatedBufferedTorusCutoff_range U b o r hr hR C hC hchart hbudget
  have hχL : LipschitzWith Lcut χ :=
    allocatedBufferedTorusCutoff_lipschitz U b o r hr hR C hC hchart hbudget Cforward hforward K hK
  have hχCL : LipschitzWith Lcut
      (fun z : (ambient → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle) => (χ z.1 : ℂ)) := by
    simpa only [one_mul, mul_one, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp (hχL.comp LipschitzWith.prod_fst)
  have hχb (z : (ambient → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) : ‖(χ z.1 : ℂ)‖ ≤ (1 : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ z.1).1]
    exact (hχ z.1).2
  refine ⟨fun z => (χ z.1 : ℂ) * g₀ z.2, ?_, ?_, ?_⟩
  · simpa only [one_mul, mul_one, add_comm, Function.comp_def] using
      lipschitz_mul_of_bounds _ _ hχCL (hg₀.comp LipschitzWith.prod_snd)
        (Bf := 1) (Bg := 1) hχb (fun z => hgb z.2)
  · intro z
    rw [norm_mul]
    exact (mul_le_mul (hχb z) (hgb z.2) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro X p hm t
    have h := hgv (BooleanCubeKernel.physicalEuclideanSitePoint U p hm t)
      (BooleanCubeKernel.physicalSingleSiteValue U d p hm t)
      (fun j => (BooleanCubeKernel.physicalSingleSiteValue_eq_mk U p hm d t j).symm)
    rw [BooleanCubeKernel.physicalSingleSiteValue_ambient] at h
    simpa only [BooleanCubeKernel.physicalEuclideanSitePoint_apply, χ, mul_assoc] using h

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

theorem exists_allocated_long_physical_expansion_identity_s2_oai
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

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_long_physical_expansion_identity_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.exists_allocated_long_physical_expansion_identity_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
