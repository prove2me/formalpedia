-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedMaskedCoefficientDensity_sample_ae_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:41.843016+00:00
-- url     : https://prove2.me/submissions/26301169-1583-4b51-ac48-605668f13310

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B138

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedArraySourceSupport
namespace OAI

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
private theorem masked_shift_nonzero (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) (n : D → ℤ)
    (h : mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ)) ≠ 0) :
    H (fun i => x i + (n i : ℝ)) ≠ 0 := (mul_ne_zero_iff.mp h).2

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
private theorem maskedIntegerPeriodization_rescale_periodic (q : ℕ)
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

end Erdos3

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
namespace OAI

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

theorem allocatedMaskedCoefficientDensity_sample_ae_s2_oai
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

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedMaskedCoefficientDensity_sample_ae_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedMaskedCoefficientDensity_sample_ae_s2_oai.{u_1, u_2, u_3, u_4, u_5}
