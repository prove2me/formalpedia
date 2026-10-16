-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_witness_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-15T22:22:02.697681+00:00
-- url     : https://prove2.me/submissions/7ba4522e-4fb7-46ee-b048-a4d0b965681b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B050
import Definitions.Def_OAIErdos3B141
import Definitions.Def_OAIErdos3B161
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoefficientDeckSample_density_law
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_spatial_chart_event_comparison

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

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Submodule _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

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

variable (J : Type*) [Fintype J]

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

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open MeasureTheory

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
open scoped BigOperators ENNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem mixedScalarArrayLaw_probability {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    IsProbabilityMeasure (mixedScalarArrayLaw c w p) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  unfold mixedScalarArrayLaw
  infer_instance

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators ENNReal

variable {E I Z O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [Fintype I] [Fintype Z] (o : OrthonormalBasis I ℝ E)

variable [Fintype O]

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

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Matrix NNReal

variable {J R I : Type*} [Fintype J] [Fintype R]

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open Module Submodule BohrLattice.MinkowskiSecondBox
open scoped BigOperators

end Erdos3

end

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedArraySourceSupport
namespace OAI

section

namespace Erdos3

open Module Submodule _root_.Set
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem mixedScalarArrayLaw_support {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    ∀ᵐ x ∂mixedScalarArrayLaw c w p, mixedArraySupported c w p x := by
  let μ := fun j => mixedCoefficientLaw (fun i => c i j) (fun i => w i j) (fun z => p z j)
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    mixedCoefficientLaw_probability _ _ (fun i => hw i j) _
  have h (j) : ∀ᵐ x ∂μ j,
      mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun z => p z j) x ≠ 0 := by
    dsimp only [μ]
    rw [mixedCoefficientLaw_density _ _ (fun i => hw i j)]
    apply realDensityMeasure_ae_of_support
    · exact ((affineProductProfile_contDiff (fun i => c i j)
        (fun i => w i j)).continuous.measurable.comp measurable_fst).mul
        ((measurable_of_countable (fun z : Z → ℤ => ∏ i, (p i j (z i)).toReal)).comp measurable_snd)
    · exact fun _ hx => hx
  have hall : ∀ᵐ x ∂Measure.pi μ, ∀ j,
      mixedCoefficientDensity (fun i => c i j) (fun i => w i j) (fun z => p z j) (x j) ≠ 0 :=
    ae_all_iff.mpr (fun j => (Measure.quasiMeasurePreserving_eval μ j).ae (h j))
  rw [show Measure.pi μ = (mixedScalarArrayLaw c w p).map (mixedArrayRegroup I Z J) from
    (mixedScalarArrayLaw_regroup c w hw p).symm] at hall
  exact ae_of_ae_map (mixedArrayRegroup I Z J).measurable.aemeasurable hall

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CanonicalDensityFourier
namespace OAI

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

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

omit [Fintype D] in
theorem smallBoxTorusKernel_local (H : (D → ℝ) → ℝ)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ)
    (hx : ∀ i, |x i| < 1/2) :
    smallBoxTorusKernel H (fun i => (x i : UnitAddCircle)) = H x := by
  rw [smallBoxTorusKernel, realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  exact positiveIntegerPeriodization_local H hs x hx

end Erdos3

end

section

namespace Erdos3
open scoped Classical

variable {D : Type*} [Fintype D]

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

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

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem canonicalCoefficientDeckSample_ambient_integer_chart
    (q : ℕ) (hq : 0 < q) (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    coefficientAmbientTorus U (canonicalCoefficientDeckSample U bW b hb o q hq x
      (fun j e => integerResidueMap (E j) q (w j e))) =
    fun a => (((coefficientSamplerAmbientPoint U b o x a +
      (coefficientSamplerDeckInteger U bW b hb x w a : ℝ)) / q : ℝ) : UnitAddCircle) := by
  funext a
  have he := canonicalCoefficientDeckSample_coordinate U bW b hb o q hq x
    (fun j e => integerResidueMap (E j) q (w j e)) a.1.1 a.1.2
  rw [normalizedCoverLift_add_deck] at he
  have he' := congrArg (euclideanSubspaceTorusEquiv (U a.1.1)) he
  rw [euclideanCoefficientEquiv_apply, AddEquiv.apply_symm_apply,
    euclideanSubspaceTorusEquiv_mk] at he'
  change subspaceAmbientTorus (U a.1.1) _ a.2 = _
  rw [he', subspaceAmbientTorus_mk]
  change (((q : ℝ)⁻¹ * _ : ℝ) : UnitAddCircle) = _
  apply congrArg (fun r : ℝ => (r : UnitAddCircle))
  rw [div_eq_inv_mul]
  congr 1
  exact congrArg (fun v : EuclideanSpace ℝ (J a.1.1) => v a.2)
    (normalizedDeckPoint_identity (euclideanSubspace (U a.1.1)) (bW a.1.1)
      (b a.1.1) (hb a.1.1) _ (w a.1.1 a.1.2))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [Fintype K]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_integral_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℂ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, (f x : ℂ) * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), Complex.real_smul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MaskedIntegerPeriodization
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

omit [Fintype D] in
theorem masked_shift_nonzero (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) (n : D → ℤ)
    (h : mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ)) ≠ 0) :
    H (fun i => x i + (n i : ℝ)) ≠ 0 := (mul_ne_zero_iff.mp h).2

theorem maskedIntegerPeriodization_lipschitz (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {L : ℝ≥0} (hH : LipschitzWith L H)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (maskedIntegerPeriodization q mask H) := by
  apply separated_tsum_lipschitz
  · intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hH.dist_le_mul (x + fun i => (n i : ℝ)) (y + fun i => (n i : ℝ))
    rw [dist_add_right] at h
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (hmask _).1]
    calc
      _ ≤ 1 * |H (fun i => x i + (n i : ℝ)) - H (fun i => y i + (n i : ℝ))| :=
        mul_le_mul_of_nonneg_right (hmask _).2 (abs_nonneg _)
      _ ≤ L * dist x y := by simpa only [one_mul, Real.dist_eq, Pi.add_def] using h
  · intro n x
    exact mul_nonneg (hmask _).1 (h0 _)
  · intro x n k hn hk
    exact integer_shifts_small_box_injective x n k
      (hs _ (masked_shift_nonzero q mask H x n hn))
      (hs _ (masked_shift_nonzero q mask H x k hk))

omit [Fintype D] in
theorem maskedIntegerPeriodization_local (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (x : D → ℝ) (hx : ∀ i, |x i| < 1/2) (k : D → ℤ) :
    maskedIntegerPeriodization q mask H (fun i => x i + (k i : ℝ)) =
      mask (fun i => (-k i : ZMod q)) * H x := by
  unfold maskedIntegerPeriodization
  rw [tsum_eq_single (-k)]
  · simp
  · intro n hn
    by_contra hnonzero
    have hH := masked_shift_nonzero q mask H (fun i => x i + (k i : ℝ)) n hnonzero
    have he := integer_shifts_small_box_injective (fun i => x i + (k i : ℝ)) n (-k)
      (hs _ hH) (by simpa using hx)
    exact hn he

omit [Fintype D] in
theorem maskedIntegerPeriodization_range (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) :
    maskedIntegerPeriodization q mask H x ∈ Set.Icc (0 : ℝ) B := by
  refine ⟨tsum_nonneg (fun n => mul_nonneg (hmask _).1 (hH _).1), ?_⟩
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    unfold maskedIntegerPeriodization
    rw [tsum_eq_single n]
    · exact (mul_le_of_le_one_left (hH _).1 (hmask _).2).trans (hH _).2
    · intro k hk
      have hz : H (fun i => x i + (k i : ℝ)) = 0 := by
        by_contra hh
        exact hk (integer_shifts_small_box_injective x k n (hs _ hh) (hs _ hn))
      rw [hz, mul_zero]
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 := by simpa using hx
    simpa only [maskedIntegerPeriodization, hz, mul_zero, tsum_zero] using hB

omit [Fintype D] in
theorem maskedIntegerPeriodization_periodic (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) (k : D → ℤ) :
    maskedIntegerPeriodization q mask H (fun i => x i + q * (k i : ℝ)) =
      maskedIntegerPeriodization q mask H x := by
  unfold maskedIntegerPeriodization
  let v : D → ℤ := fun i => q * k i
  have h := (Equiv.addRight v).tsum_eq (fun n : D → ℤ =>
    mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ)))
  convert h using 1
  apply tsum_congr
  intro n
  congr 1
  · congr 1
    funext i
    simp [v]
  · congr 1
    funext i
    simp [v]
    ring

omit [Fintype D] in
theorem maskedIntegerPeriodization_rescale_periodic (q : ℕ)
    (mask : (D → ZMod q) → ℝ) (H : (D → ℝ) → ℝ)
    (x : D → ℝ) (k : D → ℤ) :
    maskedIntegerPeriodization q mask H (fun i => q * (x i + (k i : ℝ))) =
      maskedIntegerPeriodization q mask H (fun i => q * x i) := by
  simp_rw [mul_add]
  exact maskedIntegerPeriodization_periodic q mask H _ k

omit [Fintype D] in
theorem maskedIntegerTorusKernel_coe (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) :
    maskedIntegerTorusKernel q mask H (fun i => (x i : UnitAddCircle)) =
      maskedIntegerPeriodization q mask H (fun i => q * x i) :=
  realPeriodicTorusLift_coe _ (maskedIntegerPeriodization_rescale_periodic q mask H) x

theorem maskedIntegerTorusKernel_lipschitz (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {L : ℝ≥0} (hH : LipschitzWith L H)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith ((q : ℝ≥0) * L) (maskedIntegerTorusKernel q mask H) := by
  apply realPeriodicTorusLift_lipschitz _ _ (maskedIntegerPeriodization_rescale_periodic q mask H)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (maskedIntegerPeriodization_lipschitz q mask hmask H hH h0 hs).dist_le_mul
    ((q : ℝ) • x) ((q : ℝ) • y)
  rw [dist_smul₀] at h
  simpa only [Pi.smul_def, smul_eq_mul, Real.norm_natCast, NNReal.coe_mul,
    NNReal.coe_natCast, mul_assoc, mul_left_comm] using h

omit [Fintype D] in
theorem maskedIntegerTorusKernel_range (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → UnitAddCircle) :
    maskedIntegerTorusKernel q mask H x ∈ Set.Icc (0 : ℝ) B :=
  realPeriodicTorusLift_range _ (fun y =>
    maskedIntegerPeriodization_range q mask hmask H hB hH hs (fun i => q * y i)) x

omit [Fintype D] in
theorem maskedIntegerPeriodization_le (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ≤ 1) (H : (D → ℝ) → ℝ)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (x : D → ℝ) :
    maskedIntegerPeriodization q mask H x ≤ positiveIntegerPeriodization H x := by
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    have hz (k : D → ℤ) (hk : k ≠ n) : H (fun i => x i + (k i : ℝ)) = 0 := by
      by_contra hh
      exact hk (integer_shifts_small_box_injective x k n (hs _ hh) (hs _ hn))
    unfold maskedIntegerPeriodization positiveIntegerPeriodization
    rw [tsum_eq_single n (fun k hk => by rw [hz k hk, mul_zero]), tsum_eq_single n hz]
    exact mul_le_of_le_one_left (h0 _) (hmask _)
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 := by simpa using hx
    simp only [maskedIntegerPeriodization, positiveIntegerPeriodization, hz, mul_zero, tsum_zero, le_refl]

omit [Fintype D] in
theorem maskedIntegerTorusKernel_le (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ≤ 1) (H : (D → ℝ) → ℝ)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (z : D → UnitAddCircle) :
    maskedIntegerTorusKernel q mask H z ≤ smallBoxTorusKernel H (q • z) := by
  let x : D → ℝ := fun i => centeredCircleLift (z i)
  have hx : (fun i => (x i : UnitAddCircle)) = z := funext (fun i => coe_centeredCircleLift _)
  have hqx : (fun i => (((q : ℝ) * x i : ℝ) : UnitAddCircle)) = q • z := by
    funext i
    simp only [← nsmul_eq_mul, AddCircle.coe_nsmul, x, coe_centeredCircleLift, Pi.smul_apply]
  rw [← hx, maskedIntegerTorusKernel_coe, hx, ← hqx]
  rw [smallBoxTorusKernel, realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  exact maskedIntegerPeriodization_le q mask hmask H h0 hs _

omit [Fintype D] in
theorem maskedIntegerTorusKernel_local (q : ℕ) (hq : 0 < q)
    (mask : (D → ZMod q) → ℝ) (H : (D → ℝ) → ℝ)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (x : D → ℝ) (hx : ∀ i, |x i| < 1/2) (k : D → ℤ) :
    maskedIntegerTorusKernel q mask H
      (fun i => (((x i + (k i : ℝ)) / q : ℝ) : UnitAddCircle)) =
      mask (fun i => (-k i : ZMod q)) * H x := by
  rw [maskedIntegerTorusKernel_coe]
  have he : (fun i => (q : ℝ) * ((x i + (k i : ℝ)) / q)) =
      (fun i => x i + (k i : ℝ)) := by
    funext i
    field_simp
  rw [he]
  exact maskedIntegerPeriodization_local q mask H hs x hx k

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaProductPeriodization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A : Type*} [Fintype A] {D : A → Type*}

theorem sigmaProductKernel_small_box (H : ∀ a, (D a → ℝ) → ℝ)
    (hs : ∀ a x, H a x ≠ 0 → ∀ i, |x i| < 1 / 2)
    (x : (Σ a, D a) → ℝ) (hx : sigmaProductKernel H x ≠ 0) :
    ∀ i, |x i| < 1 / 2 := by
  classical
  intro ⟨a, i⟩
  apply hs a _ _ i
  exact Finset.prod_ne_zero_iff.mp hx a (Finset.mem_univ a)

theorem positiveIntegerPeriodization_eq_nonzero_shift {I : Type*}
    (H : (I → ℝ) → ℝ) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1 / 2)
    (x : I → ℝ) (n : I → ℤ) (hn : H (fun i => x i + (n i : ℝ)) ≠ 0) :
    positiveIntegerPeriodization H x = H (fun i => x i + (n i : ℝ)) := by
  apply tsum_eq_single n
  intro m hm
  by_contra hnonzero
  exact hm (integer_shifts_small_box_injective x m n (hs _ hnonzero) (hs _ hn))

theorem positiveIntegerPeriodization_sigmaProductKernel
    (H : ∀ a, (D a → ℝ) → ℝ)
    (hs : ∀ a x, H a x ≠ 0 → ∀ i, |x i| < 1 / 2)
    (x : (Σ a, D a) → ℝ) :
    positiveIntegerPeriodization (sigmaProductKernel H) x =
      ∏ a, positiveIntegerPeriodization (H a) (fun i => x ⟨a, i⟩) := by
  classical
  by_cases hall : ∀ a, ∃ n : D a → ℤ,
      H a (fun i => x ⟨a, i⟩ + (n i : ℝ)) ≠ 0
  · choose n hn using hall
    let N : (Σ a, D a) → ℤ := fun i => n i.1 i.2
    have hN : sigmaProductKernel H (fun i => x i + (N i : ℝ)) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (fun a _ => hn a)
    rw [positiveIntegerPeriodization_eq_nonzero_shift _
      (sigmaProductKernel_small_box H hs) x N hN]
    unfold sigmaProductKernel
    apply Finset.prod_congr rfl
    intro a _
    exact (positiveIntegerPeriodization_eq_nonzero_shift (H a) (hs a)
      (fun i => x ⟨a, i⟩) (n a) (hn a)).symm
  · push Not at hall
    obtain ⟨a, ha⟩ := hall
    have hleft : positiveIntegerPeriodization (sigmaProductKernel H) x = 0 := by
      have hz (n : (Σ a, D a) → ℤ) :
          sigmaProductKernel H (fun i => x i + (n i : ℝ)) = 0 := by
        unfold sigmaProductKernel
        exact Finset.prod_eq_zero (Finset.mem_univ a) (ha (fun i => n ⟨a, i⟩))
      simp only [positiveIntegerPeriodization, hz, tsum_zero]
    have hright : positiveIntegerPeriodization (H a) (fun i => x ⟨a, i⟩) = 0 := by
      simp only [positiveIntegerPeriodization, ha, tsum_zero]
    rw [hleft]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ a) hright

theorem smallBoxTorusKernel_sigmaProductKernel
    (H : ∀ a, (D a → ℝ) → ℝ)
    (hs : ∀ a x, H a x ≠ 0 → ∀ i, |x i| < 1 / 2)
    (z : (Σ a, D a) → UnitAddCircle) :
    smallBoxTorusKernel (sigmaProductKernel H) z =
      ∏ a, smallBoxTorusKernel (H a) (fun i => z ⟨a, i⟩) := by
  have hcoe (x : (Σ a, D a) → ℝ) :
      smallBoxTorusKernel (sigmaProductKernel H) (fun i => (x i : UnitAddCircle)) =
        ∏ a, smallBoxTorusKernel (H a) (fun i => (x ⟨a, i⟩ : UnitAddCircle)) := by
    simp only [smallBoxTorusKernel,
      realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic _)]
    exact positiveIntegerPeriodization_sigmaProductKernel H hs x
  simpa only [coe_centeredCircleLift] using hcoe (fun i => centeredCircleLift (z i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedJointAmbientKernel
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

theorem coefficientJointAmbientKernel_support (v : CoefficientAmbientIndex K J → ℝ)
    (hv : coefficientJointAmbientKernel U b o c w f v ≠ 0) :
    ∀ i, |v i| < 1/2 := by
  rintro ⟨s,i⟩
  exact canonicalAmbientKernel_support _ _ _ _ _ _ _
    ((Finset.prod_ne_zero_iff.mp hv) s (Finset.mem_univ s)) i

theorem coefficientJointAmbientKernel_bounds {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ (s : CoefficientSlot K m) x,
      0 ≤ canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2) x ∧
      canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2) x ≤ B)
    (hlip : ∀ s : CoefficientSlot K m, LipschitzWith L
      (canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2))) :
    (∀ x, 0 ≤ coefficientJointAmbientKernel U b o c w f x ∧
      coefficientJointAmbientKernel U b o c w f x ≤ (B : ℝ)^Fintype.card (CoefficientSlot K m)) ∧
    LipschitzWith (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (coefficientJointAmbientKernel U b o c w f) := by
  let H := fun (s : CoefficientSlot K m) (x : CoefficientAmbientIndex K J → ℝ) =>
    canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
      (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)
      (fun i => x ⟨s,i⟩)
  have hL : ∀ s, LipschitzWith L (H s) := by
    intro s
    apply LipschitzWith.of_dist_le_mul
    intro x y
    refine ((hlip s).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    exact dist_le_pi_dist x y ⟨s,i⟩
  obtain ⟨hbnd, hprod⟩ := bounded_lipschitz_real_prod H hB hL
    (fun s x => by rw [abs_of_nonneg (hcap s _).1]; exact (hcap s _).2)
  refine ⟨?_, hprod⟩
  intro x
  have h0 : 0 ≤ coefficientJointAmbientKernel U b o c w f x :=
    Finset.prod_nonneg (fun s _ => (hcap s _).1)
  exact ⟨h0, (le_abs_self _).trans (hbnd x)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedAmbientKernelFactor_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) :
    (∀ x, 0 ≤ canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2) x ∧
      canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2) x ≤
          allocatedAmbientFactorCap (G := G) B R σ S.value V) ∧
    LipschitzWith (allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V)
      (canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2)) := by
  obtain ⟨hcap, hlip⟩ := allocatedLayerMixedInterpolation_bounds B U b S hR hσ s.1 s.2
  obtain ⟨ha, hl⟩ := canonicalAmbientKernel_bounds (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    _ _ _ hcap hlip (hC s.1) (hV s.1)
  have hcaple : V s.1 * allocatedLayerMixedCap (G := G) B R σ S.value s.1 ≤
      allocatedAmbientFactorCap (G := G) B R σ S.value V := by
    apply le_trans (Finset.single_le_sum
      (f := fun j => V j * allocatedLayerMixedCap (G := G) B R σ S.value j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1))
    exact le_add_of_nonneg_left (by norm_num)
  have hliple : allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V s.1 ≤
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V := by
    unfold allocatedAmbientFactorLip
    exact Finset.single_le_sum
      (f := fun j => allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1)
  refine ⟨fun x => ⟨(ha x).1, (ha x).2.trans ?_⟩, hl.weaken hliple⟩
  exact_mod_cast hcaple

include hC hV in
theorem allocatedCoefficientJointAmbientKernel_bounds
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) :
    let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
    let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    (∀ x, 0 ≤ allocatedCoefficientJointAmbientKernel B U b S o x ∧
      allocatedCoefficientJointAmbientKernel B U b S o x ≤ (A : ℝ)^N) ∧
    LipschitzWith (N * L * A^N) (allocatedCoefficientJointAmbientKernel B U b S o) := by
  have h := allocatedAmbientKernelFactor_bounds B U b S o C V hC hV hR hσ
  exact coefficientJointAmbientKernel_bounds U b o _ _ _
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2)

theorem allocatedCoefficientJointAmbientKernel_support
    (x : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℝ)
    (hx : allocatedCoefficientJointAmbientKernel B U b S o x ≠ 0) :
    ∀ i, |x i| < 1/2 := coefficientJointAmbientKernel_support U b o _ _ _ x hx

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointAmbientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

theorem coefficientJointAmbientKernel_periodization
    (x : CoefficientAmbientIndex K J → UnitAddCircle) :
    smallBoxTorusKernel (coefficientJointAmbientKernel U b o c w f) x =
      coefficientAmbientDensity U b o c w f x := by
  exact smallBoxTorusKernel_sigmaProductKernel
    (fun s : CoefficientSlot K m => canonicalAmbientKernel (euclideanSubspace (U s.1))
      (b s.1) (o s.1) (fun i => c s.1 i s.2) (fun i => w s.1 i s.2)
      (fun i => f s.1 i s.2))
    (fun s => canonicalAmbientKernel_support _ _ _ _ _ _) x

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientJointAmbientKernel_density
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    smallBoxTorusKernel (allocatedCoefficientJointAmbientKernel B U b S o)
      (coefficientAmbientTorus U x) = allocatedCoefficientDensity B U b hb o hR hσ S x := by
  change smallBoxTorusKernel (coefficientJointAmbientKernel U b o _ _ _)
    (coefficientAmbientTorus U x) = _
  rw [coefficientJointAmbientKernel_periodization]
  exact allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1 C hC hchart hsmall x

end Erdos3.VectorPolynomial

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

theorem euclideanAmbientTorus_normalized {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) {n : ℕ}
    (b : Basis (Fin n) ℝ (euclideanSubspace U)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace U))
    (x : euclideanSubspace U × (Fin n → ℤ)) (i : D) :
    subspaceAmbientTorus U (euclideanSubspaceTorusEquiv U
      (normalizedLatticeQuotient (euclideanSubspace U) b hb x)) i =
        (normalizedLatticePoint (euclideanSubspace U) b x i : UnitAddCircle) := by
  let u := normalizedLatticeRepresentative (euclideanSubspace U) b hb x
  have hu : QuotientAddGroup.mk' _ u = normalizedLatticeQuotient (euclideanSubspace U) b hb x :=
    normalizedLatticeRepresentative_mk (euclideanSubspace U) b hb x
  rw [← hu, euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk, euclideanSubspaceArrayEquiv_apply]
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  obtain ⟨z, hz⟩ := (mem_standardEuclideanLattice D _).mp
    (normalizedLatticePoint_sub_mem_of_mk_eq (euclideanSubspace U) b hb u x hu) i
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨z, by simpa only [zsmul_eq_mul, mul_one, PiLp.sub_apply] using hz⟩

namespace VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ}
variable {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical Matrix

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientSource_supported :
    ∀ᵐ x ∂allocatedCoefficientSource B U b hR hσ S,
      ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (x j) := by
  let μ := fun j => mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
    (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _
  exact ae_all_iff.mpr (fun j => (Measure.quasiMeasurePreserving_eval μ j).ae
    (mixedScalarArrayLaw_support _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _))

theorem allocatedCoefficientSource_ambient_small
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) :
    ∀ᵐ x ∂allocatedCoefficientSource B U b hR hσ S,
      ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1 / 2 := by
  filter_upwards [allocatedCoefficientSource_supported B U b hR hσ S] with x hx
  intro a
  exact allocatedLayerColumns_chart B U b hR hσ S o hσ1 C hC hchart hsmall
    a.1.1 a.1.2 _ (hx a.1.1 a.1.2) a.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoefficientDeckResidueMask
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Matrix

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

theorem normalizedDeckResidueRead_neg_integer (β : D → ℤ) :
    normalizedDeckResidueRead W bW b hb q (fun i => -(β i : ZMod q)) =
      integerResidueMap (Fin n ⊕ I) q (standardLatticeCoordinates W bW b hb β) := by
  have hres := (Classical.choose_spec (standardLatticeCoordinates_residue W bW b hb q)).2 β
  unfold normalizedDeckResidueRead
  rw [show -(fun i => -(β i : ZMod q)) = integerResidueMap D q β by
    funext i
    exact neg_neg _]
  exact hres.symm

theorem normalizedDeckResidueRead_latticeDeckInteger (z : Fin n → ℤ) (w : I → ℤ) :
    normalizedDeckResidueRead W bW b hb q
        (fun i => -(latticeDeckInteger W bW b hb z w i : ZMod q)) =
      Sum.elim (fun i => (z i : ZMod q)) (fun i => (w i : ZMod q)) := by
  rw [normalizedDeckResidueRead_neg_integer, latticeDeckInteger_coordinates]
  funext i
  cases i <;> rfl

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

omit [Fintype K] [∀ j, Fintype (I j)] in
theorem coefficientDeckResidueRead_integer_chart (q : ℕ) [NeZero q]
    (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    coefficientDeckResidueRead U bW b hb q
      (fun a => (-coefficientSamplerDeckInteger U bW b hb x w a : ZMod q)) =
      coefficientSamplerChartResidues q x (fun j e => integerResidueMap (E j) q (w j e)) := by
  funext j e
  exact normalizedDeckResidueRead_latticeDeckInteger (euclideanSubspace (U j))
    (bW j) (b j) (hb j) q (fun i => (x j).2 i e) (w j e)

omit [Fintype K] [∀ j, Fintype (I j)] in
theorem coefficientDeckResidueMask_integer_chart (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues K n E q → ℝ)
    (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    coefficientDeckResidueMask U bW b hb q test
      (fun a => (-coefficientSamplerDeckInteger U bW b hb x w a : ZMod q)) =
      test (coefficientSamplerChartResidues q x (fun j e => integerResidueMap (E j) q (w j e))) := by
  unfold coefficientDeckResidueMask
  rw [coefficientDeckResidueRead_integer_chart]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CoefficientJointAmbientKernelChart
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem coefficientAmbientTorus_canonicalSample (x : CoefficientSamplerArrays (K := K) I n) :
    coefficientAmbientTorus U (canonicalCoefficientSample U b hb o x) =
      fun a => (coefficientSamplerAmbientPoint U b o x a : UnitAddCircle) := by
  funext a
  rcases a with ⟨⟨j, e⟩, i⟩
  have he : coefficientCoordinateTorus U (canonicalCoefficientSample U b hb o x) ⟨j, e⟩ =
      euclideanSubspaceTorusEquiv (U j)
        (mixedArrayQuotient (euclideanSubspace (U j)) (b j) (hb j) (o j) (x j) e) := by
    apply (euclideanSubspaceTorusEquiv (U j)).symm.injective
    rw [← euclideanCoefficientEquiv_apply, canonicalCoefficientSample,
      AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  change subspaceAmbientTorus (U j)
    (coefficientCoordinateTorus U (canonicalCoefficientSample U b hb o x) ⟨j, e⟩) i = _
  rw [he]
  exact euclideanAmbientTorus_normalized (U j) (b j) (hb j)
    (orthonormalMixedChart (o j)
      (mixedArrayRegroup (I j) (Fin (n j)) (BoundedCoefficientExponent K (j.val + 1)) (x j) e)) i

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientPairCover
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {K : Type*} [finiteK : Fintype K] {m : ℕ} {J : Fin m → Type*}
  [finiteCoordinates : ∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

omit finiteK finiteCoordinates in
theorem coefficientAmbientTorus_cover [Fintype K] [∀ j, Fintype (J j)]
    (a : ℕ) (z : CoefficientTorus (K := K) U) :
    coefficientAmbientTorus U (quotientIntegerCover (coefficientIntegerLattice U) a z) =
      a • coefficientAmbientTorus U z := by
  funext t
  change subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U (a • z) t.1) t.2 =
    a • subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U z t.1) t.2
  simp only [map_nsmul, Pi.smul_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem dominatedDensityRatio_mul {X : Type*} (D A : X → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hAD : ∀ x, A x ≤ D x) (x : X) :
    (D x : ℂ) * dominatedDensityRatio D A x = (A x : ℂ) := by
  by_cases hD : D x = 0
  · have hAx : A x = 0 := le_antisymm (by simpa [hD] using hAD x) (hA x)
    simp [dominatedDensityRatio, hD, hAx]
  · simp only [dominatedDensityRatio, Complex.ofReal_div]
    field_simp [hD]

theorem dominatedDensityRatio_measurable {X : Type*} [MeasurableSpace X]
    (D A : X → ℝ) (hD : Measurable D) (hA : Measurable A) :
    Measurable (dominatedDensityRatio D A) :=
  Complex.measurable_ofReal.comp (hA.div hD)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem maskedDensity_integral_of_sample_law
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure X) (μ : Measure Y) (sample : X → Y) (hsample : Measurable sample)
    (D A : Y → ℝ) (hDm : Measurable D) (hAm : Measurable A)
    (hA0 : ∀ y, 0 ≤ A y) (hAD : ∀ y, A y ≤ D y)
    (hlaw : ρ.map sample = realDensityMeasure μ D)
    (f : X → ℝ) (hmask : ∀ᵐ x ∂ρ, A (sample x) = f x * D (sample x)) :
    (∫ y, A y ∂μ) = ∫ x, f x ∂ρ := by
  have hD0 : ∀ y, 0 ≤ D y := fun y => (hA0 y).trans (hAD y)
  have hDae : ∀ᵐ y ∂realDensityMeasure μ D, D y ≠ 0 :=
    realDensityMeasure_ae_of_support μ D hDm _ (fun y hy => hy)
  rw [← hlaw] at hDae
  have hDs : ∀ᵐ x ∂ρ, D (sample x) ≠ 0 :=
    ae_of_ae_map hsample.aemeasurable hDae
  let φ := dominatedDensityRatio D A
  have hφ : Measurable φ := dominatedDensityRatio_measurable D A hDm hAm
  have hφsample : (fun x => φ (sample x)) =ᵐ[ρ] fun x => (f x : ℂ) := by
    filter_upwards [hDs, hmask] with x hx hAx
    simp only [φ, dominatedDensityRatio, hAx, mul_div_cancel_right₀ _ hx]
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (∫ y, A y ∂μ) = ∫ y, (A y : ℂ) ∂μ := integral_ofReal.symm
    _ = ∫ y, (D y : ℂ) * φ y ∂μ := by
      simp only [φ, dominatedDensityRatio_mul D A hA0 hAD]
    _ = ∫ y, φ y ∂realDensityMeasure μ D :=
      (realDensityMeasure_integral_complex μ D hDm hD0 φ).symm
    _ = ∫ x, φ (sample x) ∂ρ := by
      rw [← hlaw]
      exact integral_map hsample.aemeasurable hφ.aestronglyMeasurable
    _ = ∫ x, (f x : ℂ) ∂ρ := integral_congr_ae hφsample
    _ = Complex.ofReal (∫ x, f x ∂ρ) := integral_ofReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedMaskedCoefficientDensity_continuous
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (q : ℕ) (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1) :
    Continuous (allocatedMaskedCoefficientDensity B U b o S q mask) := by
  have hk := allocatedCoefficientJointAmbientKernel_bounds B U b S o C V hC hV hR hσ
  exact (maskedIntegerTorusKernel_lipschitz q mask hmask _ hk.2 (fun x => (hk.1 x).1)
    (allocatedCoefficientJointAmbientKernel_support B U b S o)).continuous.comp
    (coefficientAmbientTorus_continuous U)

include hC hV in
theorem allocatedMaskedCoefficientDensity_le_density
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    0 ≤ allocatedMaskedCoefficientDensity B U b o S q mask x ∧
      allocatedMaskedCoefficientDensity B U b o S q mask x ≤
        allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  have hk := allocatedCoefficientJointAmbientKernel_bounds B U b S o C V hC hV hR hσ
  have hrange := maskedIntegerTorusKernel_range q mask hmask
    (allocatedCoefficientJointAmbientKernel B U b S o)
    (show 0 ≤ (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) by positivity)
    hk.1 (allocatedCoefficientJointAmbientKernel_support B U b S o) (coefficientAmbientTorus U x)
  refine ⟨hrange.1, ?_⟩
  have hle := maskedIntegerTorusKernel_le q mask (fun r => (hmask r).2)
    (allocatedCoefficientJointAmbientKernel B U b S o) (fun z => (hk.1 z).1)
    (allocatedCoefficientJointAmbientKernel_support B U b S o) (coefficientAmbientTorus U x)
  rw [← coefficientAmbientTorus_cover,
    allocatedCoefficientJointAmbientKernel_density B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall] at hle
  exact hle

theorem allocatedMaskedCoefficientDensity_local
    (q : ℕ) (hq : 0 < q)
    (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (y : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℝ)
    (hy : ∀ i, |y i| < 1/2)
    (k : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℤ)
    (hx : coefficientAmbientTorus U x =
      fun i => (((y i + (k i : ℝ)) / q : ℝ) : UnitAddCircle)) :
    allocatedMaskedCoefficientDensity B U b o S q mask x =
      mask (fun i => (-k i : ZMod q)) * allocatedCoefficientJointAmbientKernel B U b S o y := by
  rw [allocatedMaskedCoefficientDensity, hx]
  exact maskedIntegerTorusKernel_local q hq mask _
    (allocatedCoefficientJointAmbientKernel_support B U b S o) y hy k

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedMaskedCoefficientSampleAE
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedMaskedCoefficientDensity_sample
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hx : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q) :
    allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test)
      (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) x r) =
      test (coefficientSamplerChartResidues q x r) *
        allocatedCoefficientDensity B U b hb o hR hσ S (canonicalCoefficientSample U b hb o x) := by
  classical
  choose w hw using fun j e => integerResidueMap_surjective (E j) q (r j e)
  have hr : (fun j e => integerResidueMap (E j) q (w j e)) = r := by
    funext j e
    exact hw j e
  rw [← hr]
  rw [allocatedMaskedCoefficientDensity_local B U b o S q (NeZero.pos q) _ _ _ hx _
    (canonicalCoefficientDeckSample_ambient_integer_chart U bW b hb o q (NeZero.pos q) x w),
    coefficientDeckResidueMask_integer_chart]
  congr 1
  rw [← allocatedCoefficientJointAmbientKernel_density B U b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall, coefficientAmbientTorus_canonicalSample]
  exact (smallBoxTorusKernel_local _ (allocatedCoefficientJointAmbientKernel_support B U b S o) _ hx).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedMaskedCoefficientDensity_sample_ae
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ) :
    ∀ᵐ z ∂(allocatedCoefficientSource B U b hR hσ S).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues
        (K := LayerSamplerVariables G I n B) E q)).toMeasure,
      allocatedMaskedCoefficientDensity B U b o S q
          (coefficientDeckResidueMask U bW b hb q test)
          (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) z.1 z.2) =
        test (coefficientSamplerChartResidues q z.1 z.2) *
          allocatedCoefficientDensity B U b hb o hR hσ S
            (quotientIntegerCover (coefficientIntegerLattice U) q
              (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) z.1 z.2)) := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (allocatedCoefficientSource_ambient_small B U b o hR hσ S hσ1 Cinv hCinv
      hchart hsmall)] with z hz
  rw [canonicalCoefficientDeckSample_projection]
  exact allocatedMaskedCoefficientDensity_sample B U bW b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall q test z.1 hz z.2

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckMaskedIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U))

theorem CoefficientDeckDensityLaw.masked_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    (hdensity : Measurable density)
    (A : CoefficientTorus (K := K) U → ℝ) (hA : Measurable A)
    (hA0 : ∀ y, 0 ≤ A y)
    (hAD : ∀ y, A y ≤ density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y))
    (f : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d → ℝ)
    (hmask : ∀ᵐ p ∂source.prod (PMF.uniformOfFintype
      (CoefficientDeckResidues (K := K) B d)).toMeasure,
      A (canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2) =
        f p * density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d
          (canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2))) :
    (∫ y, A y ∂μ) = ∫ p, f p ∂source.prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure := by
  exact maskedDensity_integral_of_sample_law
    (source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) μ
    (fun p => canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2)
    (canonicalCoefficientDeckSample_measurable U bW b hb o d)
    (fun y => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y)) A
    (hdensity.comp (quotientIntegerCover_continuous _ d).measurable) hA hA0 hAD hlaw f hmask

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMaskedCoefficientHaarLaw
namespace OAI

section

namespace Erdos3

theorem allocatedUniformPMF_fintype_transport (α : Type*) [Fintype α] [Nonempty α] :
    PMF.uniformOfFintype α = allocatedUniformPMFCanonical α := by
  unfold allocatedUniformPMFCanonical
  congr 1
  exact Subsingleton.elim _ _

end Erdos3

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped NNReal Classical
attribute [local irreducible] coefficientDeckKernelEquiv canonicalCoefficientDeckSample coefficientSamplerAmbientPoint allocatedMaskedCoefficientDensity allocatedCoefficientSource allocatedCoefficientDensity

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
include hC hV in
theorem allocatedMaskedCoefficientDensity_haar_data
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ)
    (htest : ∀ r, test r ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test)) ∧
    ∀ y, 0 ≤ allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test) y ∧
      allocatedMaskedCoefficientDensity B U b o S q
        (coefficientDeckResidueMask U bW b hb q test) y ≤
      allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice U) q y) := by
  let mask := coefficientDeckResidueMask U bW b hb q test
  have hm : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1 := fun r => htest _
  refine ⟨?_, ?_⟩
  · exact (allocatedMaskedCoefficientDensity_continuous B U b o S C V hC hV hR hσ q mask hm).measurable
  · exact allocatedMaskedCoefficientDensity_le_density B U b o S C V hC hV hb hR hσ hσ1
      Cinv hCinv hchart hsmall q mask hm

include hC hV ν in
theorem allocatedMaskedCoefficientDensity_haar_integral
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ)
    (htest : ∀ r, test r ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y, allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test) y ∂μ) =
    ∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
        CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
      test (coefficientSamplerChartResidues q p.1 p.2)
      ∂(allocatedCoefficientSource B U b hR hσ S).prod
        (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure := by
  have hdata := allocatedMaskedCoefficientDensity_haar_data B U bW b hb o S C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall q test htest
  have hdm := (allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1
    Cinv hCinv hchart hsmall μ ν).1
  have hlaw := allocatedCoefficientDeckSample_density_law B U b hR hσ S E hb o bW q μ ν
    hσ1 Cinv hCinv hchart hsmall
  have hae := allocatedMaskedCoefficientDensity_sample_ae B U bW b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall q test
  have hresult := CoefficientDeckDensityLaw.masked_integral (K := LayerSamplerVariables G I n B)
    U bW b hb o μ (allocatedCoefficientSource B U b hR hσ S)
    (allocatedCoefficientDensity B U b hb o hR hσ S) q hlaw hdm
    (allocatedMaskedCoefficientDensity B U b o S q (coefficientDeckResidueMask U bW b hb q test))
    hdata.1 (fun y => (hdata.2 y).1) (fun y => (hdata.2 y).2)
    (fun p => test (coefficientSamplerChartResidues q p.1 p.2))
    (by simpa only [allocatedUniformPMF_fintype_transport] using hae)
  simpa only [allocatedUniformPMF_fintype_transport] using hresult

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialWitnessComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_spatial_witness_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q] (hq : 0 < q)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hqPs : (q : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * q : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (event : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
          (if coefficientDeckChartEvent U bW b hb o q (event (fun v => (z v : ZMod q))) (sample z) then 1 else 0)) -
        ∑' z, (selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal *
          ∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
              CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
            (if event (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q p.1 p.2) then (1 : ℝ) else 0)
            ∂(allocatedCoefficientSource B U b hR hσ S).prod
              (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure| ≤
        12 * (2 * δ + ε) := by
  dsimp only
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩ :=
    exists_allocated_spatial_chart_event_comparison B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells event width hwidth hwide
      hfreqPs hmassPs hsmallError
  have hhaar (r) := allocatedMaskedCoefficientDensity_haar_integral B U bW b hb o S C V hC hV μ ν
    hR hσ hσ1 Cinv hCinv hchart hsmall q
    (fun a => if event r a then (1 : ℝ) else 0)
    (fun a => by split_ifs <;> constructor <;> norm_num)
  simp_rw [hhaar] at he
  exact ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_witness_comparison := @OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_witness_comparison
