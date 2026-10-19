-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_primitive_retained_forecast_score_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:55:34.566122+00:00
-- url     : https://prove2.me/submissions/d4f54336-1639-4d43-8906-0287ed867095

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B247
import Definitions.Def_OAIE3v2B303
import Definitions.Def_OAIE3v2B262
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_relativePatchSliceConclusion_of_actual_retained_forecast_score_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_scaledRetainedRecoveredG_lift_lipschitz_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalOutputDensity_nonneg {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) : 0 ≤ rationalOutputDensity p Y N b := by
  unfold rationalOutputDensity finiteImageMass
  exact mul_nonneg (Nat.cast_nonneg _) (p.mean_nonneg (fun _ => by split_ifs <;> norm_num))

theorem rationalInactiveForecast_nonneg {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : 0 ≤ gridVolume) (z : Z) (b : J → ZMod N) :
    0 ≤ rationalInactiveForecast inactive active gridPoint Y N gridVolume z b :=
  mul_nonneg hV (inactive.fiberMean_nonneg gridPoint z _
    (fun i => rationalOutputDensity_nonneg (active i) (Y i) N b))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer
namespace OAI

section

namespace Erdos3

theorem recoveredIntegerLift_eq_add_sum {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (c : Fin m → ℤ) (k : Fin d → ℤ) :
    recoveredIntegerLift M c k = c + ∑ j, k j • (fun i => M i j) := by
  ext i
  simp [recoveredIntegerLift, Finset.sum_apply, mul_comm]

theorem recoveredIntegerLift_projection {A : Type*} [AddCommGroup A] {d m : ℕ}
    (M : Fin m → Fin d → ℤ) (π : (Fin m → ℤ) →+ A)
    (hπ : ∀ j, π (fun i => M i j) = 0) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    π (recoveredIntegerLift M c k) = π c := by
  rw [recoveredIntegerLift_eq_add_sum, map_add, map_sum]
  simp only [map_zsmul, hπ, zsmul_zero, Finset.sum_const_zero, add_zero]

theorem recoveredIntegerLift_residue {d m : ℕ} (M : Fin m → Fin d → ℤ) (q : ℕ)
    (hM : ∀ i j, (q : ℤ) ∣ M i j) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    (fun i => (recoveredIntegerLift M c k i : ZMod q)) = fun i => (c i : ZMod q) := by
  funext i
  have hzero (j) : (M i j : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hM i j)
  simp only [recoveredIntegerLift, Int.cast_add, Int.cast_sum, Int.cast_mul, hzero,
    zero_mul, Finset.sum_const_zero, add_zero]

end Erdos3

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

theorem forecastNormalizedSpatialCoordinates_lipschitz (base : X → ℤ) (N : X → ℕ)
    {τ : ℝ} (hτ : 0 < τ) :
    LipschitzWith ⟨8 / τ, by positivity⟩ (forecastNormalizedSpatialCoordinates base N τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (div_nonneg (by norm_num) hτ.le) dist_nonneg)).mpr
  intro a
  change |8 * (x a.1 - (base a.1 : ℝ) / N a.1) / τ -
    8 * (y a.1 - (base a.1 : ℝ) / N a.1) / τ| ≤ (8 / τ) * dist x y
  rw [show 8 * (x a.1 - (base a.1 : ℝ) / N a.1) / τ -
    8 * (y a.1 - (base a.1 : ℝ) / N a.1) / τ = (8 / τ) * (x a.1 - y a.1) by ring,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 / τ)]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y a.1) (by positivity)

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

theorem recoveredIntegerTransverse_of_mem (ℓ : D → ℤ)
    (hℓ : (standardEuclideanPoint D ℓ).val ∈ W) :
    recoveredIntegerTransverse W bW b hb ℓ = 0 := by
  have hp := recoveredIntegerTransverse_projection W bW b hb ℓ
  rw [W.orthogonalProjectionOnto_orthogonal_apply_eq_zero hℓ] at hp
  have hz : (fun i => (recoveredIntegerTransverse W bW b hb ℓ i : ℝ)) = 0 := by
    apply b.equivFun.symm.injective
    simpa only [map_zero] using neg_eq_zero.mp hp.symm
  funext i
  have hi := congrFun hz i
  simp only [Pi.zero_apply] at hi ⊢
  exact_mod_cast hi

end Erdos3

end

section

namespace Erdos3

open Module Submodule

theorem recoveredIntegerLift_linear_residue {T : Type*} {d a : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] (T → ℤ))
    (M : Fin d → Fin a → ℤ) (N : ℕ) [NeZero N]
    (hM : ∀ i j, (N : ℤ) ∣ M i j) (β : Fin d → ℤ) (k : Fin a → ℤ) :
    integerResidueMap T N (f (recoveredIntegerLift M β k)) =
      integerResidueMap T N (f β) := by
  obtain ⟨A, _, hA⟩ := exists_bounded_integerMap_residue_matrix f N
  rw [hA, hA]
  congr 1
  exact recoveredIntegerLift_residue M N hM β k

variable {m d a : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

variable {E : Fin m → Type*} [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

theorem recoveredIntegerTransverse_layer_matrix
    (e : Fin d ≃ Sigma J) (M : Fin d → Fin a → ℤ)
    (hcol : ∀ j t, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j, i⟩) t)).val ∈ euclideanSubspace (U j))
    (β : Sigma J → ℤ) (k : Fin a → ℤ) (j : Fin m) :
    recoveredIntegerTransverse (euclideanSubspace (U j)) (bW j) (b j) (hb j)
        (fun i => recoveredLayeredIntegerLift e M β k ⟨j, i⟩) =
      recoveredIntegerTransverse (euclideanSubspace (U j)) (bW j) (b j) (hb j)
        (fun i => β ⟨j, i⟩) := by
  let π : (Fin d → ℤ) →+ (Fin (n j) → ℤ) :=
    (recoveredIntegerTransverse (euclideanSubspace (U j)) (bW j) (b j) (hb j)).toAddMonoidHom.comp
      (layerIntegerRestriction e j).toAddMonoidHom
  have hπ (t : Fin a) : π (fun i => M i t) = 0 :=
    recoveredIntegerTransverse_of_mem (euclideanSubspace (U j)) (bW j) (b j) (hb j)
      (fun i => M (e.symm ⟨j, i⟩) t) (hcol j t)
  have h := recoveredIntegerLift_projection M π hπ (fun i => β (e i)) k
  simpa only [π, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    layerIntegerRestriction, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply,
    recoveredLayeredIntegerLift] using h

theorem standardLatticeCoordinates_layer_matrix_residue
    (e : Fin d ≃ Sigma J) (M : Fin d → Fin a → ℤ) (N : ℕ) [NeZero N]
    (hdiv : ∀ i t, (N : ℤ) ∣ M i t)
    (β : Sigma J → ℤ) (k : Fin a → ℤ) (j : Fin m) :
    integerResidueMap (Fin (n j) ⊕ E j) N
        (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)
          (fun i => recoveredLayeredIntegerLift e M β k ⟨j, i⟩)) =
      integerResidueMap (Fin (n j) ⊕ E j) N
        (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)
          (fun i => β ⟨j, i⟩)) := by
  let f := (standardLatticeCoordinates (euclideanSubspace (U j))
    (bW j) (b j) (hb j)).toLinearMap.comp (layerIntegerRestriction e j)
  have h := recoveredIntegerLift_linear_residue f M N hdiv (fun i => β (e i)) k
  simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
    layerIntegerRestriction, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply,
    recoveredLayeredIntegerLift] using h

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

local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW
local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawRecoveredRationalFactor_nonneg (hV : 0 ≤ volume)
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) : 0 ≤ rat r β :=
  rationalInactiveForecast_nonneg _ _ _ _ N hV _ _

theorem forecastLawRecoveredKernel_mem_Icc
    {Dcap Rcap : ℝ≥0} (hdensity : ∀ y, density y ∈ Set.Icc (0 : ℝ) Dcap)
    (hV : 0 ≤ volume) (hcap : ∀ r β, rat r β ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ)
    (y : (Σ j, J j) → ℝ) :
    kernel v r β y ∈ Set.Icc (0 : ℝ) (Dcap * Rcap : ℝ≥0) := by
  exact ⟨mul_nonneg (hdensity _).1
    (forecastLawRecoveredRationalFactor_nonneg B U basis S law selected sample x active Y N
      volume hb bW hV r β),
    mul_le_mul (hdensity _).2 (hcap r β)
      (forecastLawRecoveredRationalFactor_nonneg B U basis S law selected sample x active Y N
        volume hb bW hV r β) Dcap.coe_nonneg⟩

theorem forecastLawRecoveredKernel_spatial_lipschitz
    (hτ : 0 < τ) {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip density)
    (hcap : ∀ r β, |rat r β| ≤ Rcap)
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ) :
    LipschitzWith (Rcap * (Dlip * ⟨8 / τ, by positivity⟩)) (fun v => kernel v r β y) := by
  have hc := forecastNormalizedSpatialCoordinates_lipschitz base physicalN hτ
  have hpair := hc.prodMk (LipschitzWith.const
    (forecastNormalizedActiveCoordinates short
      (allocatedFullMixedSiteValue (R := R) U basis
        (forecastFrozenIntegerMixedValue U basis o
          (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y))))
  have hd := hdensity.comp hpair
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change |density _ * rat r β - density _ * rat r β| ≤ _
  rw [← sub_mul, abs_mul, mul_comm]
  calc
    _ ≤ (Rcap : ℝ) * |density _ - density _| :=
      mul_le_mul_of_nonneg_right (hcap r β) (abs_nonneg _)
    _ ≤ (Rcap : ℝ) * ((Dlip * ⟨8 / τ, by positivity⟩ : ℝ≥0) * dist v w) := by
      apply mul_le_mul_of_nonneg_left _ Rcap.coe_nonneg
      simpa only [Function.comp_apply, max_eq_left (show (0 : ℝ≥0) ≤ ⟨8 / τ, by positivity⟩ from bot_le), Real.dist_eq] using hd.dist_le_mul v w
    _ = _ := by simp only [NNReal.coe_mul]; ring

end Erdos3.VectorPolynomial

end

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

local notation "labels" => forecastRecoveredIntegerLabels U basis hb bW
local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW
local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawRecoveredRationalFactor_eq_of_labels
    (β γ : (Σ j, J j) → ℤ)
    (htrans : ∀ j i, labels β j (Sum.inl i) = labels γ j (Sum.inl i))
    (hres : ∀ j i, (labels β j i : ZMod N) = (labels γ j i : ZMod N))
    (r : X → ZMod N) : rat r β = rat r γ := by
  have hg : (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
      labels β (selected a).1 (Sum.inl (selected a).2)) =
      (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
        labels γ (selected a).1 (Sum.inl (selected a).2)) := by
    funext a t
    exact htrans (selected a).1 (selected a).2
  have hr : (fun j i => (labels β j i : ZMod N)) =
      (fun j i => (labels γ j i : ZMod N)) := by
    funext j i
    exact hres j i
  unfold forecastLawRecoveredRationalFactor
  rw [hg, hr]

theorem forecastLawRecoveredKernel_eq_of_labels
    (β γ : (Σ j, J j) → ℤ)
    (htrans : ∀ j i, labels β j (Sum.inl i) = labels γ j (Sum.inl i))
    (hres : ∀ j i, (labels β j i : ZMod N) = (labels γ j i : ZMod N))
    (v : X → ℝ) (r : X → ZMod N) : kernel v r β = kernel v r γ := by
  have hz : (fun j i => labels β j (Sum.inl i)) =
      (fun j i => labels γ j (Sum.inl i)) := by
    funext j i
    exact htrans j i
  funext y
  unfold forecastLawRecoveredKernel
  rw [hz, forecastLawRecoveredRationalFactor_eq_of_labels B U basis S law selected sample x
    active Y N volume hb bW β γ htrans hres r]

theorem forecastLawRecoveredKernel_recovered_invariant {d d' : ℕ}
    (e : Fin d ≃ Σ j, J j) (M : Fin d → Fin d' → ℤ)
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (N : ℤ) ∣ M i a)
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ) (k : Fin d' → ℤ) :
    kernel v r (recoveredLayeredIntegerLift e M β k) = kernel v r β := by
  apply forecastLawRecoveredKernel_eq_of_labels B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW
  · intro j i
    exact congrFun (recoveredIntegerTransverse_layer_matrix U bW basis hb e M hcol β k j) i
  · intro j i
    exact congrFun (standardLatticeCoordinates_layer_matrix_residue U bW basis hb e M N
      hdiv β k j) i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawCenteredRecoveredKernel
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

local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW

variable {d : ℕ} (e : Fin d ≃ Σ j, J j) (c : (Σ j, J j) → ℝ)

local notation "centered" => forecastLawCenteredRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW e c

theorem forecastLawCenteredRecoveredKernel_spatial_lipschitz
    (hτ : 0 < τ) {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip density)
    (hcap : ∀ r β, |rat r β| ≤ Rcap)
    (r : X → ZMod N) (β : Fin d → ℤ) (y : Fin d → ℝ) :
    LipschitzWith (Rcap * (Dlip * ⟨8 / τ, by positivity⟩))
      (fun v => centered v r β y) :=
  forecastLawRecoveredKernel_spatial_lipschitz B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW hτ hdensity hcap r
    (fun a => β (e.symm a)) (fun a => y (e.symm a) + c a)

theorem forecastLawCenteredRecoveredKernel_mem_Icc
    {Dcap Rcap : ℝ≥0} (hdensity : ∀ y, density y ∈ Set.Icc (0 : ℝ) Dcap)
    (hV : 0 ≤ volume) (hcap : ∀ r β, rat r β ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) (y : Fin d → ℝ) :
    centered v r β y ∈ Set.Icc (0 : ℝ) (Dcap * Rcap : ℝ≥0) :=
  forecastLawRecoveredKernel_mem_Icc B U basis S law density selected sample x active Y N volume
    base physicalN τ o hb bW hdensity hV hcap v r
    (fun a => β (e.symm a)) (fun a => y (e.symm a) + c a)

theorem forecastLawCenteredRecoveredKernel_recovered_invariant {d' : ℕ}
    (M : Fin d → Fin d' → ℤ)
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (N : ℤ) ∣ M i a)
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) (k : Fin d' → ℤ) :
    centered v r (recoveredIntegerLift M β k) = centered v r β := by
  have heq : (fun a => recoveredIntegerLift M β k (e.symm a)) =
      recoveredLayeredIntegerLift e M (fun a => β (e.symm a)) k := by
    funext a
    change recoveredIntegerLift M β k (e.symm a) =
      recoveredIntegerLift M (fun i => β (e.symm (e i))) k (e.symm a)
    have hb : (fun i => β (e.symm (e i))) = β := by
      funext i
      rw [e.symm_apply_apply]
    rw [hb]
  unfold forecastLawCenteredRecoveredKernel
  rw [heq, forecastLawRecoveredKernel_recovered_invariant B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW e M hcol hdiv]

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

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedBoundsReferenceNonzero
variable (cutoff : ℕ)
local notation "q" => slice.path.referenceRetainedCRTModulus cutoff
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "Y" => (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
  (fun k => (z (Prod.fst k) (Prod.snd k) : ℤ)) q t j)
local notation "rat" => forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
  slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
  Y q vol hb bW
local notation "centered" => forecastLawCenteredRecoveredKernel B U b S slice.principalLaw
  (slice.density hB) selected slice.path.sample slice.path.commonTuple
  (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
  slice.path.base physicalN τ o hb bW e (fun _ => 0)

private theorem retainedRecoveredG_eq_centered :
    slice.retainedRecoveredG selected hB o bW hb e cutoff = centered := by
  funext v r β y
  change forecastLawRecoveredKernel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a => y (e.symm a)) =
    forecastLawRecoveredKernel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a => y (e.symm a) + 0)
  simp only [add_zero]

omit [Fintype Tsp] in
private theorem retainedRational_abs_le_layered {Rcap : ℝ≥0}
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (r : X → ZMod q) (β : (Σ j, J j) → ℤ) : |rat r β| ≤ Rcap := by
  have h := hcap r (fun i => β (e i))
  simpa only [retainedRecoveredRationalFactor, Equiv.apply_symm_apply] using h

theorem retainedRecoveredG_mem_Icc {Dcap Rcap : ℝ≥0}
    (hdensity : ∀ y, slice.density hB y ∈ Set.Icc (0 : ℝ) Dcap)
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod q) (β : Fin d → ℤ) (y : Fin d → ℝ) :
    slice.retainedRecoveredG selected hB o bW hb e cutoff v r β y ∈
      Set.Icc (0 : ℝ) (Dcap * Rcap : ℝ≥0) := by
  rw [slice.retainedRecoveredG_eq_centered selected hB o bW hb e cutoff]
  apply forecastLawCenteredRecoveredKernel_mem_Icc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hdensity (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
  intro r β
  exact (le_abs_self _).trans (slice.retainedRational_abs_le_layered selected bW hb e cutoff hcap r β)

theorem retainedRecoveredG_spatial_lipschitz
    (hτ : 0 < τ) {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (r : X → ZMod q) (β : Fin d → ℤ) (y : Fin d → ℝ) :
    LipschitzWith (Rcap * (Dlip * ⟨8 / τ, by positivity⟩))
      (fun v => slice.retainedRecoveredG selected hB o bW hb e cutoff v r β y) := by
  simp only [slice.retainedRecoveredG_eq_centered selected hB o bW hb e cutoff]
  exact forecastLawCenteredRecoveredKernel_spatial_lipschitz B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
    slice.path.base physicalN τ o hb bW e (fun _ => 0) hτ hdensity
    (slice.retainedRational_abs_le_layered selected bW hb e cutoff hcap) r β y

theorem retainedRecoveredG_recovered_invariant {d' : ℕ}
    (M : Fin d → Fin d' → ℤ)
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (q : ℤ) ∣ M i a)
    (v : X → ℝ) (r : X → ZMod q) (β : Fin d → ℤ) (k : Fin d' → ℤ) :
    slice.retainedRecoveredG selected hB o bW hb e cutoff v r (recoveredIntegerLift M β k) =
      slice.retainedRecoveredG selected hB o bW hb e cutoff v r β := by
  simp only [slice.retainedRecoveredG_eq_centered selected hB o bW hb e cutoff]
  exact forecastLawCenteredRecoveredKernel_recovered_invariant B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
    slice.path.base physicalN τ o hb bW e (fun _ => 0) M hcol hdiv v r β k

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualFixedSpatialScaledRetainedKernelBounds
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

private theorem lipschitzWith_nnreal_mul {Y : Type*} [PseudoMetricSpace Y]
    {F : Y → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (κ : ℝ≥0) :
    LipschitzWith (κ * L) (fun y => (κ : ℝ) * F y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist ((κ : ℝ) * F x) ((κ : ℝ) * F y) = (κ : ℝ) * dist (F x) (F y) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg κ.coe_nonneg]
    _ ≤ (κ : ℝ) * ((L : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hF.dist_le_mul x y) κ.coe_nonneg
    _ = ((κ * L : ℝ≥0) : ℝ) * dist x y := by rw [NNReal.coe_mul, mul_assoc]

variable (cutoff : ℕ) (κ : ℝ≥0)

theorem scaledRetainedRecoveredG_mem_Icc {Dcap Rcap : ℝ≥0}
    (hdensity : ∀ y, slice.density hB y ∈ Set.Icc (0 : ℝ) Dcap)
    (hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap)
    (v : X → ℝ) (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) :
    slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y ∈
      Set.Icc (0 : ℝ) (κ * (Dcap * Rcap) : ℝ≥0) := by
  have h := slice.retainedRecoveredG_mem_Icc selected hB o bW hb e cutoff hdensity hcap
    v residue β y
  refine ⟨mul_nonneg κ.coe_nonneg h.1, ?_⟩
  exact mul_le_mul_of_nonneg_left h.2 κ.coe_nonneg

theorem scaledRetainedRecoveredG_spatial_lipschitz
    (hτ : 0 < τ) {Dlip Rcap : ℝ≥0}
    (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap)
    (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) :
    LipschitzWith (κ * (Rcap * (Dlip * ⟨8 / τ, by positivity⟩)))
      (fun v => slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y) :=
  lipschitzWith_nnreal_mul
    (slice.retainedRecoveredG_spatial_lipschitz selected hB o bW hb e cutoff hτ
      hdensity hcap residue β y) κ

theorem scaledRetainedRecoveredG_recovered_invariant {r : ℕ}
    (M : Fin d → Fin r → ℤ)
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (slice.path.referenceRetainedCRTModulus cutoff : ℤ) ∣ M i a)
    (v : X → ℝ) (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (k : Fin r → ℤ) :
    slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue
      (recoveredIntegerLift M β k) =
    slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β := by
  funext y
  exact congrArg (fun t : ℝ => (κ : ℝ) * t)
    (congrFun (slice.retainedRecoveredG_recovered_invariant selected hB o bW hb e cutoff
      M hcol hdiv v residue β k) y)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RecoveredKernelScalarBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem recoveredKernelScalarBudget_ge {B : ℝ} (hB : 1 ≤ B) :
    1 ≤ recoveredKernelScalarBudget B ∧ B ≤ recoveredKernelScalarBudget B := by
  unfold recoveredKernelScalarBudget
  constructor <;> nlinarith [sq_nonneg B]

theorem recoveredKernelScalarBudget_discounted_score {B score δ : ℝ}
    (hB : 1 ≤ B) (hscore : Real.exp (-B) ≤ score)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Real.exp (-recoveredKernelScalarBudget B) ≤ (score / 2) / (1 + δ) := by
  have hL : B + 4 ≤ recoveredKernelScalarBudget B := by
    unfold recoveredKernelScalarBudget
    nlinarith [sq_nonneg B]
  have hexp4 : (4 : ℝ) ≤ Real.exp 4 := by
    linarith only [Real.add_one_le_exp (4 : ℝ)]
  have hfour : 4 * Real.exp (-recoveredKernelScalarBudget B) ≤ score := by
    calc
      _ ≤ Real.exp 4 * Real.exp (-recoveredKernelScalarBudget B) :=
        mul_le_mul_of_nonneg_right hexp4 (Real.exp_nonneg _)
      _ = Real.exp (4 - recoveredKernelScalarBudget B) := by rw [← Real.exp_add]; rfl
      _ ≤ Real.exp (-B) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ score := hscore
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < 1 + δ)).mpr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have he := Real.exp_nonneg (-recoveredKernelScalarBudget B)
  nlinarith

private theorem mul_exp_bound {x y a b : ℝ} (hx : x ≤ Real.exp a)
    (hy : y ≤ Real.exp b) (hy0 : 0 ≤ y) : x * y ≤ Real.exp (a + b) := by
  calc
    _ ≤ Real.exp a * Real.exp b := mul_le_mul hx hy hy0 (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

theorem recoveredKernel_joint_constants_le_exp {B : ℝ} (hB : 1 ≤ B)
    (κ Dcap Dlip D Icap H Tinverse : ℝ≥0) (q r : ℕ)
    (hDcap : Dcap ≤ D) (hDlip : Dlip ≤ D)
    (hjoint : (κ : ℝ) * (D : ℝ) * (Icap : ℝ) ≤ Real.exp B)
    (hq : (q : ℝ) ≤ Real.exp B) (hr : (r : ℝ) ≤ B)
    (hH : (H : ℝ) ≤ Real.exp B) (hTinverse : (Tinverse : ℝ) ≤ Real.exp B) :
    let Rcap : ℝ≥0 := Icap * (q : ℝ≥0) ^ r
    ((κ * (Dcap * Rcap) : ℝ≥0) : ℝ) ≤ Real.exp (recoveredKernelScalarBudget B) ∧
    ((κ * (Rcap * (Dlip * Tinverse)) : ℝ≥0) : ℝ) ≤
      Real.exp (recoveredKernelScalarBudget B) ∧
    ((κ * (Rcap * (Dlip * H)) : ℝ≥0) : ℝ) ≤
      Real.exp (recoveredKernelScalarBudget B) := by
  have hpow : (q : ℝ) ^ r ≤ Real.exp (B ^ 2) := by
    calc
      _ ≤ (Real.exp B) ^ r := pow_le_pow_left₀ (Nat.cast_nonneg _) hq r
      _ = Real.exp ((r : ℝ) * B) := (Real.exp_nat_mul B r).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hbaseCap : (κ : ℝ) * (Dcap : ℝ) * (Icap : ℝ) ≤ Real.exp B := by
    apply le_trans _ hjoint
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDcap κ.coe_nonneg) Icap.coe_nonneg
  have hbaseLip : (κ : ℝ) * (Dlip : ℝ) * (Icap : ℝ) ≤ Real.exp B := by
    apply le_trans _ hjoint
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDlip κ.coe_nonneg) Icap.coe_nonneg
  have hcap := mul_exp_bound hbaseCap hpow (pow_nonneg (Nat.cast_nonneg _) _)
  have hlip := mul_exp_bound hbaseLip hpow (pow_nonneg (Nat.cast_nonneg _) _)
  have hspace := mul_exp_bound hlip hTinverse Tinverse.coe_nonneg
  have hactive := mul_exp_bound hlip hH H.coe_nonneg
  have hexp : Real.exp (B + B ^ 2) ≤ Real.exp (recoveredKernelScalarBudget B) := by
    apply Real.exp_le_exp.mpr
    unfold recoveredKernelScalarBudget
    nlinarith [sq_nonneg B]
  have hexp' : Real.exp (B + B ^ 2 + B) ≤ Real.exp (recoveredKernelScalarBudget B) := by
    apply Real.exp_le_exp.mpr
    unfold recoveredKernelScalarBudget
    nlinarith [sq_nonneg B]
  dsimp only
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast]
  constructor
  · convert hcap.trans hexp using 1
    all_goals first | rfl | ring
  constructor
  · convert hspace.trans hexp' using 1
    all_goals first | rfl | ring
  · convert hactive.trans hexp' using 1
    all_goals first | rfl | ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialNumericalPatchEndpoint
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

theorem relativePatchSliceConclusion_of_primitive_retained_forecast_score_s2_oai
    (hmpos : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (κ : ℝ≥0)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (hN : ∀ i, 0 < physicalN i)
    {s r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (slice.path.referenceRetainedCRTModulus cutoff : ℤ) ∣ M i a)
    (D Icap : ℝ≥0)
    (hdensity : ∀ y, slice.density hB y ∈ Set.Icc (0 : ℝ) D)
    (hDlip : LipschitzWith D (slice.density hB))
    (hgrid : ∀ z : A → ℤ,
      (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ)) *
        slice.principalLaw.fiberMean
          (forecastInactiveFixedOutput B U b S selected
            (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample)
            slice.path.commonTuple)
          (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (Cchart : Fin m → ℝ≥0)
    (hchart : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤
      Cchart j * ‖z‖)
    (Kchart : ℝ≥0) (hKchart : ∀ j, (R j)⁻¹ ≤ Kchart) (hτ : 0 < τ)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε score budget : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : score / 2 ≤ 𝔼 x : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hbudget : 1 ≤ budget)
    (hr : (r : ℝ) ≤ budget) (hE : (E : ℝ) ≤ budget)
    (hn : (Fintype.card X : ℝ) ≤ budget)
    (hOut : (Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value))) : ℝ) ≤ budget)
    (hKbudget : (K : ℝ) ≤ Real.exp budget)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp budget)
    (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp budget)
    (hjoint : (κ : ℝ) * (D : ℝ) * (Icap : ℝ) ≤ Real.exp budget)
    (hqbudget : (slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp budget)
    (hchartBudget : ((Kchart * ∑ j, Cchart j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
      Real.exp budget)
    (hτBudget : 8 / τ ≤ Real.exp budget)
    (hscoreLower : Real.exp (-budget) ≤ score)
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion s physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  let q := slice.path.referenceRetainedCRTModulus cutoff
  let outDim := Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
    (allocatedShortAxis (I := I) U b S.value)))
  let Rcap : ℝ≥0 := Icap * (q : ℝ≥0) ^ outDim
  let L := recoveredKernelScalarBudget budget
  let C : ℝ≥0 := ⟨Real.exp L, Real.exp_nonneg _⟩
  have hL := (recoveredKernelScalarBudget_ge hbudget).1
  have hbudgetL := (recoveredKernelScalarBudget_ge hbudget).2
  have hexp : Real.exp budget ≤ Real.exp L := Real.exp_le_exp.mpr hbudgetL
  have hC : 1 ≤ C := Real.one_le_exp_iff.mpr (le_trans zero_le_one hL)
  have hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap := by
    intro residue β
    simpa only [Rcap, q, outDim, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using
      (slice.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2 selected bW hb e
        cutoff hgrid residue β)
  have hconstants := recoveredKernel_joint_constants_le_exp hbudget κ D D D Icap
    (Kchart * ∑ j, Cchart j * Fintype.card (J j)) ⟨8 / τ, by positivity⟩ q outDim
    le_rfl le_rfl hjoint hqbudget hOut hchartBudget hτBudget
  have hCcap : κ * (D * Rcap) ≤ C := hconstants.1
  have hCspace : κ * (Rcap * (D * ⟨8 / τ, by positivity⟩)) ≤ C := hconstants.2.1
  have hClift : κ * (Rcap * (D * (Kchart * ∑ j, Cchart j * Fintype.card (J j)))) ≤ C :=
    hconstants.2.2
  apply slice.relativePatchSliceConclusion_of_actual_retained_forecast_score_s2
    selected hB o bW hb e hmpos hD cutoff hcutoff hsmall κ κ.coe_nonneg poly hm hN
    w hw hws hmono Pscalar hP p Bpatch χ M K hM hweight hcoords
    C C C hC ?_ ?_ ?_ ?_ f hf hlam hδ.1 haccuracy hε hdiscount hscore
    hL (hr.trans hbudgetL) (hE.trans hbudgetL) (hn.trans hbudgetL)
    (hKbudget.trans hexp) le_rfl le_rfl le_rfl (hχbudget.trans hexp) (hBbudget.trans hexp)
    (hqbudget.trans hexp)
    (recoveredKernelScalarBudget_discounted_score hbudget hscoreLower hδ.1 hδ.2) hlarge hrank
  · intro residue β y
    exact (slice.scaledRetainedRecoveredG_spatial_lipschitz selected hB o bW hb e cutoff κ
      hτ hDlip hcap residue β y).weaken hCspace
  · intro v residue β
    exact (slice.scaledRetainedRecoveredG_lift_lipschitz_s2 selected hB o bW hb e cutoff κ
      Cchart hchart Kchart hKchart hDlip hcap v residue β).weaken hClift
  · intro v residue β y
    have h := slice.scaledRetainedRecoveredG_mem_Icc selected hB o bW hb e cutoff κ
      hdensity hcap v residue β y
    exact ⟨h.1, h.2.trans hCcap⟩
  · exact slice.scaledRetainedRecoveredG_recovered_invariant selected hB o bW hb e cutoff κ
      M hcol hdiv

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_primitive_retained_forecast_score_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.relativePatchSliceConclusion_of_primitive_retained_forecast_score_s2_oai
