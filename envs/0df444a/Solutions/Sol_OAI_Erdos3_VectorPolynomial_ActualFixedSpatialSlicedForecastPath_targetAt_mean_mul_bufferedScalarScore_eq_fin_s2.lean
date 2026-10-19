-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.targetAt_mean_mul_bufferedScalarScore_eq_fin_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:01:34.85099+00:00
-- url     : https://prove2.me/submissions/73c528b9-ad7c-4217-b346-a99706e02ad6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B303
import Definitions.Def_OAIE3v2B262

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerBox_subtype_mean_eq_fin {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (F : (X → ℤ) → ℝ) :
    (𝔼 u : ↥(integerBox N), F u.val) =
      (𝔼 u : (∀ i, Fin (N i)), F (fun i => ((u i).val : ℤ))) := by
  classical
  symm
  let lift : (∀ i, Fin (N i)) → ↥(integerBox N) := fun u =>
    ⟨(fun i => ((u i).val : ℤ)), (mem_integerBox N _).mpr (fun i =>
      ⟨by positivity, by exact_mod_cast (u i).isLt⟩)⟩
  apply Finset.expect_nbij lift
  · intro u _
    exact Finset.mem_univ _
  · intro u _
    rfl
  · intro u _ v _ huv
    funext i
    apply Fin.ext
    have h := congrFun (congrArg Subtype.val huv) i
    change ((u i).val : ℤ) = ((v i).val : ℤ) at h
    exact_mod_cast h
  · intro u _
    have hu := (mem_integerBox N u.val).mp u.property
    let v : ∀ i, Fin (N i) := fun i => ⟨(u.val i).toNat, by
      have hi := hu i
      omega⟩
    refine ⟨v, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    funext i
    exact Int.toNat_of_nonneg (hu i).1

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BufferedIntegerLift
namespace OAI

section

namespace Erdos3

namespace PatchKernel

theorem buffered_sum_eq_nearest {m : ℕ} (Ψ : PatchKernel m) (x : Fin m → ℝ)
    (f : (Fin m → ℤ) → ℝ) :
    (∑' β, Ψ.value (fun i => x i - (β i : ℝ)) * f β) =
      Ψ.value (fun i => x i - (nearestIntegerLift x i : ℝ)) * f (nearestIntegerLift x) := by
  classical
  apply tsum_eq_single (nearestIntegerLift x)
  intro γ hγ
  have hzero : Ψ.value (fun i => x i - (γ i : ℝ)) = 0 := by
    by_contra hn
    exact hγ (Ψ.buffered_lift_unique x _ γ (nearestIntegerLift_close x) hn)
  rw [hzero, zero_mul]

end PatchKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SignedSplitCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {R E F I J : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [Fintype I] [Fintype J]

theorem signedSplitCoordinates_symm_apply (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F)
    (z : J → R) (w : I → R) :
    (signedSplitCoordinates q s hs bK bI).symm (z, w) =
      (bK.equivFun.symm w).val - s (bI.equivFun.symm z) := by
  change (bK.equivFun.symm w).val + s (bI.equivFun.symm (-z)) = _
  rw [map_neg, map_neg, sub_eq_add_neg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem standardEuclideanLinearEquiv_apply (J : Type*) [Fintype J] (z : J → ℤ) (i : J) :
    (standardEuclideanLinearEquiv J z).val i = (z i : ℝ) := by
  have h := latticeBasisEquiv_coordinates (standardEuclideanLattice J)
    (EuclideanSpace.basisFun J ℝ).toBasis rfl z i
  have he : (latticeBasisEquiv (standardEuclideanLattice J)
      (EuclideanSpace.basisFun J ℝ).toBasis rfl z).val =
      (standardEuclideanLinearEquiv J z).val := rfl
  rw [he] at h
  simpa only [Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using h

theorem standardEuclideanLinearEquiv_eq_point (J : Type*) [Fintype J] (z : J → ℤ) :
    standardEuclideanLinearEquiv J z = standardEuclideanPoint J z := by
  apply Subtype.ext
  ext i
  exact standardEuclideanLinearEquiv_apply J z i

end Erdos3

end

section

namespace Erdos3

open Module

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

variable [Fintype I] [Fintype J]

theorem latticeSignedCoordinates_symm_apply (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ))
    (z : J → ℤ) (w : I → ℤ) :
    ((latticeSignedCoordinates Λ W bW bP).symm (z, w)).val =
      (bW.equivFun.symm w).val.val - (latticeIntegerLift Λ W bP z).val := by
  rw [latticeSignedCoordinates, signedSplitCoordinates_symm_apply]
  simp only [Submodule.coe_sub, Basis.map_equivFun, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  rfl

theorem latticeSignedCoordinates_reconstruction (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (bW : Basis I ℤ (latticeSection Λ W)) (bP : Basis J ℤ (orthogonalLatticeImage Λ Wᗮ)) (x : Λ) :
    x.val + (latticeIntegerLift Λ W bP (latticeSignedCoordinates Λ W bW bP x).1).val =
      (bW.equivFun.symm (latticeSignedCoordinates Λ W bW bP x).2).val.val := by
  have h := latticeSignedCoordinates_symm_apply Λ W bW bP
    (latticeSignedCoordinates Λ W bW bP x).1 (latticeSignedCoordinates Λ W bW bP x).2
  change ((latticeSignedCoordinates Λ W bW bP).symm (latticeSignedCoordinates Λ W bW bP x)).val = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact eq_sub_iff_add_eq.mp h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J]

theorem standardLatticeCoordinates_reconstruction (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (β : D → ℤ) :
    (standardEuclideanPoint D β).val +
        (standardLatticeIntegerLift W bP hP
          (fun j => standardLatticeCoordinates W bW bP hP β (Sum.inl j))).val =
      (bW.equivFun.symm (fun i => standardLatticeCoordinates W bW bP hP β (Sum.inr i))).val.val := by
  rw [← standardEuclideanLinearEquiv_eq_point]
  exact latticeSignedCoordinates_reconstruction (standardEuclideanLattice D) W bW
    (integerBasisOfReal (projectedIntegerLattice W) bP hP) (standardEuclideanLinearEquiv D β)

theorem standardLatticeCoordinates_projection (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
    (bP : Basis J ℝ Wᗮ) (hP : span ℤ (Set.range bP) = projectedIntegerLattice W) (β : D → ℤ) :
    Wᗮ.orthogonalProjectionOnto (standardEuclideanPoint D β).val =
      -bP.equivFun.symm (fun j => (standardLatticeCoordinates W bW bP hP β (Sum.inl j) : ℝ)) := by
  have h := congrArg Wᗮ.orthogonalProjectionOnto
    (standardLatticeCoordinates_reconstruction W bW bP hP β)
  rw [map_add, standardLatticeIntegerLift_projection,
    W.orthogonalProjectionOnto_orthogonal_apply_eq_zero
      (bW.equivFun.symm (fun i => standardLatticeCoordinates W bW bP hP β (Sum.inr i))).val.property] at h
  exact eq_neg_of_add_eq_zero_left h

end Erdos3

end

end OAI
end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem latticeDeckInteger_coordinates (z : Fin n → ℤ) (w : I → ℤ) :
    standardLatticeCoordinates W bW b hb (latticeDeckInteger W bW b hb z w) =
      Sum.elim z w := LinearEquiv.apply_symm_apply _ _

theorem latticeDeckInteger_reconstruction (z : Fin n → ℤ) (w : I → ℤ) :
    (standardEuclideanPoint D (latticeDeckInteger W bW b hb z w)).val +
        (standardLatticeIntegerLift W b hb z).val =
      (bW.equivFun.symm w).val.val := by
  have h := standardLatticeCoordinates_reconstruction W bW b hb
    (latticeDeckInteger W bW b hb z w)
  simpa only [latticeDeckInteger_coordinates, Sum.elim_inl, Sum.elim_inr] using h

theorem normalizedLatticePoint_linear_lift (x : W × (Fin n → ℤ)) :
    normalizedLatticePoint W b x = x.1.val +
      (Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val := by
  rw [normalizedLatticePoint_eq_sheet W b hb, standardLatticeIntegerLift_projection]
  unfold latticeSheetPoint
  rw [latticeBasisEquiv_synthesis]

theorem normalizedDeckPoint_identity (x : W × (Fin n → ℤ)) (w : I → ℤ) :
    (normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val).val =
      normalizedLatticePoint W b x +
        (standardEuclideanPoint D (latticeDeckInteger W bW b hb x.2 w)).val := by
  have hβ := latticeDeckInteger_reconstruction W bW b hb x.2 w
  have hs := W.starProjection_add_starProjection_orthogonal
    (standardLatticeIntegerLift W b hb x.2).val
  change (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val +
    (Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val = _ at hs
  rw [normalizedLatticePoint_linear_lift W b hb]
  change x.1.val - (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val +
    (bW.equivFun.symm w).val.val = _
  rw [← hs] at hβ
  rw [← hβ]
  abel

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

theorem forecastCongruenceOutput_intCast (q : ℕ) (u : X → ℤ)
    (label : ∀ j, Fin (n j) ⊕ E j → ℤ) :
    (fun o => (forecastCongruenceOutput (R := ℤ) inactive u label o : ZMod q)) =
      forecastCongruenceOutput inactive (fun x => (u x : ZMod q))
        (fun j i => (label j i : ZMod q)) := by
  funext o
  rcases o with ⟨j, x | i | a⟩ <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem forecastNormalizedSpatialCoordinates_eval (base u : X → ℤ) (N : X → ℕ)
    (τ : ℝ) (a : Σ _ : X, Unit ⊕ Empty) :
    forecastNormalizedSpatialCoordinates base N τ (fun i => (u i : ℝ) / N i) a =
      ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8) := by
  unfold forecastNormalizedSpatialCoordinates
  ring

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

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

theorem targetAt_eq_rawTarget
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j) (κ : ℝ) (u : X → ℤ) :
    slice.targetAt selected hB o bW hb poly hm κ u =
      slice.rawTarget selected hB o bW hb κ (slice.path.physicalPolynomial poly)
        (slice.path.physicalPolynomial_mem poly hm) u := by
  rfl

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RecoveredLatticeMatrixInvariance
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I E : Type*} [Fintype D] [Fintype I] [Fintype E] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem recoveredIntegerTransverse_projection (β : D → ℤ) :
    Wᗮ.orthogonalProjectionOnto (standardEuclideanPoint D β).val =
      -b.equivFun.symm (fun i => (recoveredIntegerTransverse W bW b hb β i : ℝ)) :=
  standardLatticeCoordinates_projection W bW b hb β

variable (o : OrthonormalBasis I ℝ W)

theorem recoveredMixedCoordinates_real (y : EuclideanSpace ℝ D) (β : D → ℤ)
    (hy : y + (standardEuclideanPoint D β).val ∈ W) :
    mixedRealCoordinates W b o y =
      ((recoveredMixedCoordinates W bW b hb o y β).1,
        fun i => ((recoveredMixedCoordinates W bW b hb o y β).2 i : ℝ) /
          basisAxisScale b i) := by
  refine Prod.ext (by rfl) ?_
  have hp := W.orthogonalProjectionOnto_orthogonal_apply_eq_zero hy
  rw [map_add, recoveredIntegerTransverse_projection W bW b hb β] at hp
  have hp' := eq_of_sub_eq_zero (show Wᗮ.orthogonalProjectionOnto y -
      b.equivFun.symm (fun i => (recoveredIntegerTransverse W bW b hb β i : ℝ)) = 0 by
    simpa only [sub_eq_add_neg] using hp)
  funext i
  change (normalizedOrthogonalChart W b y).2 i = _
  rw [normalizedOrthogonalChart_apply, hp', LinearEquiv.apply_symm_apply]
  rfl

theorem recoveredMixedCoordinates_point (y : EuclideanSpace ℝ D) (β : D → ℤ)
    (hy : y + (standardEuclideanPoint D β).val ∈ W) :
    normalizedLatticePoint W b
      (orthonormalMixedChart o (recoveredMixedCoordinates W bW b hb o y β)) = y := by
  rw [← mixedRealPoint_integer]
  rw [← recoveredMixedCoordinates_real W bW b hb o y β hy]
  exact mixedRealPoint_coordinates W b o y

theorem recoveredMixedCoordinates_deck (y : EuclideanSpace ℝ D) (β : D → ℤ)
    (hy : y + (standardEuclideanPoint D β).val ∈ W) :
    normalizedLatticeRepresentative W b hb
        (orthonormalMixedChart o (recoveredMixedCoordinates W bW b hb o y β)) +
        (bW.equivFun.symm (recoveredIntegerDeck W bW b hb β)).val =
      ⟨y + (standardEuclideanPoint D β).val, hy⟩ := by
  apply Subtype.ext
  rw [normalizedDeckPoint_identity,
    recoveredMixedCoordinates_point W bW b hb o y β hy]
  congr 3
  apply (standardLatticeCoordinates W bW b hb).injective
  rw [latticeDeckInteger_coordinates]
  funext i
  cases i <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawRecoveredRationalCardinalityCap
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

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW
local notation "labels" => forecastRecoveredIntegerLabels U basis hb bW
local notation "mixed" => forecastFrozenIntegerMixedValue U basis o

theorem forecastLawDensityPhysicalDeckSource_eq_recoveredKernel
    (u : X → ℤ) (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ) :
    forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x active Y N volume
      base physicalN τ u
      (mixed (fun j i => labels β j (Sum.inl i)) y)
      (fun j i => labels β j (Sum.inr i)) =
      (kernel (fun i => (u i : ℝ) / physicalN i) (fun i => (u i : ZMod N)) β y : ℂ) := by
  unfold forecastLawDensityPhysicalDeckSource forecastLawRecoveredKernel
  rw [Complex.ofReal_mul]
  apply congrArg₂ (fun v w : ℝ => (v : ℂ) * (w : ℂ))
  · apply congrArg density
    apply Prod.ext
    · funext a
      exact (forecastNormalizedSpatialCoordinates_eval base u physicalN τ a).symm
    · rfl
  · unfold forecastLawRecoveredRationalFactor
    apply congrArg (rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => labels β (selected a).1 (Sum.inl (selected a).2)))
    rw [forecastCongruenceOutput_intCast]
    apply congrArg (forecastCongruenceOutput short (fun i => (u i : ZMod N)))
    funext j i
    cases i <;> rfl

omit [Fintype X] in
theorem forecastRecoveredPhysicalDeck
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ)
    (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ)
    (hpoint : ∀ j i, y ⟨j,i⟩ + (β ⟨j,i⟩ : ℝ) =
      eval (fun i => (u i : ℝ)) (poly j) i) (j : Fin m) :
    normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
        (orthonormalMixedChart (o j)
          (forecastFrozenIntegerMixedValue U basis o
            (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y j)) +
        ((bW j).equivFun.symm
          (fun i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inr i))).val =
      physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j := by
  let v : EuclideanSpace ℝ (J j) :=
    (EuclideanSpace.equiv (J j) ℝ).symm (fun i => y ⟨j,i⟩)
  have hv : v + (standardEuclideanPoint (J j) (fun i => β ⟨j,i⟩)).val =
      (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j).val := by
    ext i
    rw [physicalEuclideanSitePoint_apply]
    exact hpoint j i
  have hm : v + (standardEuclideanPoint (J j) (fun i => β ⟨j,i⟩)).val ∈
      euclideanSubspace (U j) := by
    rw [hv]
    exact (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j).property
  change normalizedLatticeRepresentative _ _ _
      (orthonormalMixedChart (o j)
        (recoveredMixedCoordinates (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
          (o j) v (fun i => β ⟨j,i⟩))) +
      ((bW j).equivFun.symm
        (recoveredIntegerDeck (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
          (fun i => β ⟨j,i⟩))).val = _
  rw [recoveredMixedCoordinates_deck _ _ _ _ _ _ _ hm]
  apply Subtype.ext
  exact hv

omit [Fintype X] in
theorem forecastRecoveredPhysicalPoint
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ)
    (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ)
    (hpoint : ∀ j i, y ⟨j,i⟩ + (β ⟨j,i⟩ : ℝ) =
      eval (fun i => (u i : ℝ)) (poly j) i) (j : Fin m) :
    normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
        (orthonormalMixedChart (o j)
          (forecastFrozenIntegerMixedValue U basis o
            (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y j)) =
      (EuclideanSpace.equiv (J j) ℝ).symm (fun i => y ⟨j,i⟩) := by
  let v : EuclideanSpace ℝ (J j) :=
    (EuclideanSpace.equiv (J j) ℝ).symm (fun i => y ⟨j,i⟩)
  have hv : v + (standardEuclideanPoint (J j) (fun i => β ⟨j,i⟩)).val =
      (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j).val := by
    ext i
    rw [physicalEuclideanSitePoint_apply]
    exact hpoint j i
  have hm : v + (standardEuclideanPoint (J j) (fun i => β ⟨j,i⟩)).val ∈
      euclideanSubspace (U j) := by
    rw [hv]
    exact (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j).property
  exact recoveredMixedCoordinates_point (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
    (o j) v (fun i => β ⟨j,i⟩) hm

theorem forecastLawDensityPhysicalTarget_eq_recoveredKernel
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ)
    (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ)
    (hpoint : ∀ j i, y ⟨j,i⟩ + (β ⟨j,i⟩ : ℝ) = eval (fun i => (u i : ℝ)) (poly j) i)
    (hquarter : ∀ a, |y a| ≤ 1 / 4) :
    forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume
      base physicalN τ o hb bW poly hpoly u =
      (kernel (fun i => (u i : ℝ) / physicalN i) (fun i => (u i : ZMod N)) β y : ℂ) := by
  let w := mixed (fun j i => labels β j (Sum.inl i)) y
  let deck := fun j i => labels β j (Sum.inr i)
  have hdeck := forecastRecoveredPhysicalDeck U basis o hb bW poly hpoly u β y hpoint
  have hsmall (j : Fin m) (i : J j) :
      |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
        (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4 := by
    have hp := forecastRecoveredPhysicalPoint U basis o hb bW poly hpoly u β y hpoint j
    change |normalizedLatticePoint _ _ _ i| ≤ _
    rw [hp]
    exact hquarter ⟨j, i⟩
  exact (forecastLawDensityPhysicalTarget_integer_deck B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW poly hpoly u w deck hdeck hsmall).trans
      (forecastLawDensityPhysicalDeckSource_eq_recoveredKernel B U basis S law density selected
        sample x active Y N volume base physicalN τ o hb bW u β y)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualFixedSpatialSlicedRetainedKernelComparison
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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem rawTarget_eq_recoveredG (κ : ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j) (u : X → ℤ)
    (β : Fin d → ℤ) (y : Fin d → ℝ)
    (hpoint : ∀ j i, y (e.symm ⟨j,i⟩) + (β (e.symm ⟨j,i⟩) : ℝ) =
      eval (fun a => (u a : ℝ)) (poly j) i)
    (hquarter : ∀ i, |y i| ≤ 1 / 4) :
    slice.rawTarget selected hB o bW hb κ poly hm u =
      (κ : ℂ) * (slice.recoveredG selected hB o bW hb e
        (fun i => (u i : ℝ) / physicalN i)
        (fun i => (u i : ZMod slice.path.referenceModulus)) β y : ℂ) := by
  let : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  apply congrArg (fun z : ℂ => (κ : ℂ) * z)
  exact forecastLawDensityPhysicalTarget_eq_recoveredKernel B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceInputLaw)
    (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (z k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW poly hm u
    (fun a => β (e.symm a)) (fun a => y (e.symm a)) hpoint
    (fun a => hquarter (e.symm a))

theorem targetAt_eq_recoveredG
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j) (κ : ℝ) (u : X → ℤ)
    (β : Fin d → ℤ) (y : Fin d → ℝ)
    (hpoint : ∀ i, y i + (β i : ℝ) =
      fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val) u i)
    (hquarter : ∀ i, |y i| ≤ 1 / 4) :
    slice.targetAt selected hB o bW hb poly hm κ u =
      (κ : ℂ) * (slice.recoveredG selected hB o bW hb e
        (fun i => (u i : ℝ) / physicalN i)
        (fun i => (u i : ZMod slice.path.referenceModulus)) β y : ℂ) := by
  rw [slice.targetAt_eq_rawTarget selected hB o bW hb poly hm κ u]
  apply slice.rawTarget_eq_recoveredG selected hB o bW hb e κ
    (slice.path.physicalPolynomial poly) (slice.path.physicalPolynomial_mem poly hm) u β y
    ?_ hquarter
  intro j i
  have hp := hpoint (e.symm ⟨j, i⟩)
  simp only [fullTaggedBufferedCoordinates] at hp
  rw [e.apply_symm_apply] at hp
  simpa only [ActualFixedSpatialForecastPath.physicalPolynomial,
    eval_subtractConstant, Pi.sub_apply] using hp

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialBufferedScore
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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem targetAt_mul_bufferedScalarScore
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (κ : ℝ) (χ : PatchKernel d)
    (T : (X → ℤ) → (Fin d → ℤ) → ℝ) (f : (X → ℤ) → ℝ) (lam : ℝ) (u : X → ℤ) :
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val)
    (slice.targetAt selected hB o bW hb poly hm κ u).re *
        bufferedScalarScore χ coords T f lam u =
      (f u - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords u i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => (u i : ℝ) / physicalN i)
            (fun i => (u i : ZMod slice.path.referenceModulus)) β
            (fun i => coords u i - (β i : ℝ))) * T u β := by
  intro coords
  let β := nearestIntegerLift (coords u)
  let y := fun i => coords u i - (β i : ℝ)
  have hsum := χ.buffered_sum_eq_nearest (coords u) (fun β =>
    (κ * slice.recoveredG selected hB o bW hb e
      (fun i => (u i : ℝ) / physicalN i)
      (fun i => (u i : ZMod slice.path.referenceModulus)) β
      (fun i => coords u i - (β i : ℝ))) * T u β)
  simp only [mul_assoc] at hsum ⊢
  rw [hsum]
  change (slice.targetAt selected hB o bW hb poly hm κ u).re *
    ((f u - lam) * χ.value y * T u β) =
    (f u - lam) * (χ.value y * (κ * (slice.recoveredG selected hB o bW hb e
      (fun i => (u i : ℝ) / physicalN i)
      (fun i => (u i : ZMod slice.path.referenceModulus)) β y * T u β)))
  by_cases hχ : χ.value y = 0
  · simp only [hχ, mul_zero, zero_mul]
  · have ht := slice.targetAt_eq_recoveredG selected hB o bW hb e poly hm κ u β y
      (fun i => by dsimp only [y]; ring) (χ.support y hχ)
    have hre := congrArg Complex.re ht
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
    rw [hre]
    ring

theorem targetAt_mean_mul_bufferedScalarScore
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (κ : ℝ) (χ : PatchKernel d)
    (T : (X → ℤ) → (Fin d → ℤ) → ℝ) (f : (X → ℤ) → ℝ) (lam : ℝ) :
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val)
    (𝔼 u : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ u.val).re *
        bufferedScalarScore χ coords T f lam u.val) =
      (𝔼 u : ↥(integerBox physicalN), (f u.val - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords u.val i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => (u.val i : ℝ) / physicalN i)
            (fun i => (u.val i : ZMod slice.path.referenceModulus)) β
            (fun i => coords u.val i - (β i : ℝ))) * T u.val β) := by
  intro coords
  apply Finset.expect_congr rfl
  intro u _
  exact slice.targetAt_mul_bufferedScalarScore selected hB o bW hb e poly hm κ χ T f lam u.val

theorem targetAt_mean_mul_bufferedScalarScore_eq_fin_s2_oai
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (κ : ℝ) (χ : PatchKernel d)
    (T : (X → ℤ) → (Fin d → ℤ) → ℝ) (f : (X → ℤ) → ℝ) (lam : ℝ) :
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val)
    (𝔼 u : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ u.val).re *
        bufferedScalarScore χ coords T f lam u.val) =
      (𝔼 u : (∀ i, Fin (physicalN i)),
        (f (fun i => ((u i).val : ℤ)) - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords (fun j => ((u j).val : ℤ)) i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => ((u i).val : ℝ) / physicalN i)
            (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
            (fun i => coords (fun j => ((u j).val : ℤ)) i - (β i : ℝ))) *
          T (fun i => ((u i).val : ℤ)) β) := by
  intro coords
  rw [slice.targetAt_mean_mul_bufferedScalarScore selected hB o bW hb e poly hm κ χ T f lam]
  simpa only [Int.cast_natCast] using
    (integerBox_subtype_mean_eq_fin physicalN (fun u : X → ℤ =>
      (f u - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords u i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => (u i : ℝ) / physicalN i)
            (fun i => (u i : ZMod slice.path.referenceModulus)) β
            (fun i => coords u i - (β i : ℝ))) * T u β))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.targetAt_mean_mul_bufferedScalarScore_eq_fin_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.targetAt_mean_mul_bufferedScalarScore_eq_fin_s2_oai
