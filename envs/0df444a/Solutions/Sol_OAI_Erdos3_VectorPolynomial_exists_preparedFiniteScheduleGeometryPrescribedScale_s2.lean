-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleGeometryPrescribedScale_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:24:37.839319+00:00
-- url     : https://prove2.me/submissions/15483553-86b6-4ef2-acf6-046e2d4ddd2d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B272
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedUniformDegreeComparison_s2
import Theorems.Thm_OAI_Erdos3_slicedDetection_kernel_cutoff_bound_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalDetectedScaleInputBudget
namespace OAI

section

namespace Erdos3

theorem slicedDetectionGain_lower (s C count : ℕ) {p q a α : ℝ}
    (hα : Real.exp (-a) ≤ α) :
    Real.exp (-slicedDetectionGainLog s C count p q a) ≤
      (Real.exp (-((5 * p + 20) * count + p + 2)) * (α / 2)) *
        Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
  have hhalf : Real.exp (-(a + 1)) ≤ α / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh : 2 * Real.exp (-(a + 1)) ≤ Real.exp (-a) := by
      calc
        _ ≤ Real.exp 1 * Real.exp (-(a + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    linarith
  calc
    _ = (Real.exp (-((5 * p + 20) * count + p + 2)) * Real.exp (-(a + 1))) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold slicedDetectionGainLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhalf (Real.exp_nonneg _)) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedAffineLengthLog_kernel_bound {m : ℕ} (hm : 0 < m)
    {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T) :
    Pk ≤ allocatedAffineLengthLog m D P Prho Pk target F T := by
  let L := allocatedAffineL1Log m D P Prho Pk
  have hL : 0 ≤ L := allocatedAffineL1Log_nonneg m hD hP hr hk
  have hd := allocatedDensityEnvelope_nonneg m hD hP
  have hs := allocatedSupportEnvelope_nonneg m hD hP
  have hi : 0 ≤ allocatedIdealLipEnvelope D P Prho := by
    unfold allocatedIdealLipEnvelope
    positivity
  have hb : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
  have hc : (1 : ℝ) ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos hm (pow_pos (by decide : 0 < (2 : ℕ)) _))
  have hkL : Pk ≤ L := by
    have hprod := mul_le_mul_of_nonneg_right hc hk
    dsimp only [L, allocatedAffineL1Log]
    have hrad : 0 ≤ ((m + 1 : ℕ) : ℝ) * D := mul_nonneg (Nat.cast_nonneg _) hD
    nlinarith
  have hLE : L ≤ allocatedAffineReferenceAccuracyLog m D P Prho Pk target := by
    have hp := mul_nonneg hD (add_nonneg hL zero_le_one)
    dsimp only [allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]
    change L ≤ target + 1 + 8 * (D + 1) * (L + 1) + 4
    nlinarith
  exact hkL.trans (hLE.trans (allocatedAffineLengthLog_bounds m hD hP hr hk ht hF hT).2.2.2.1)

theorem allocatedAffineLength_kernel_ready {m : ℕ} (hm : 0 < m)
    {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T)
    {Mk S : ℕ} (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ (S : ℝ)) : Mk ≤ S := by
  exact_mod_cast hMk.trans ((Real.exp_le_exp.mpr
    (allocatedAffineLengthLog_kernel_bound hm hD hP hr hk ht hF hT)).trans hS)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeTolerance
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem preparedUniformDegreeTolerance_bounds (t Ptail : ι → ℝ)
    {pRadius Qσ : ℝ} (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1)
    (hPtail : ∀ i, 0 ≤ Ptail i) (hinv : ∀ i, (t i)⁻¹ ≤ Real.exp (Ptail i))
    (hQσ : 0 ≤ Qσ) (hpRadius : 0 ≤ pRadius) :
    let σ := preparedUniformDegreeTolerance t Qσ
    let Pscale := preparedUniformDegreeScaleLog pRadius Ptail Qσ
    0 < σ ∧ σ ≤ 1 ∧ (∀ i, σ ≤ t i) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ (∀ i, Ptail i ≤ Pscale) := by
  classical
  dsimp only
  have hprod : 0 < ∏ i, t i := Finset.prod_pos (fun i _ => ht i)
  have hprod1 : ∏ i, t i ≤ 1 :=
    Finset.prod_le_one (fun i _ => (ht i).le) (fun i _ => ht1 i)
  have hprodi (i : ι) : ∏ j, t j ≤ t i := by
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ {i})
        (fun j _ => (ht j).le) (fun j _ _ => ht1 j))
  have hsum : 0 ≤ ∑ i, Ptail i := Finset.sum_nonneg (fun i _ => hPtail i)
  have hsumScale : (∑ i, Ptail i) ≤ preparedUniformDegreeScaleLog pRadius Ptail Qσ := by
    unfold preparedUniformDegreeScaleLog
    linarith only [hpRadius, hQσ]
  have hQScale : Qσ ≤ preparedUniformDegreeScaleLog pRadius Ptail Qσ := by
    unfold preparedUniformDegreeScaleLog
    linarith only [hpRadius, hsum]
  have hprodInv : (∏ i, t i)⁻¹ ≤ Real.exp (∑ i, Ptail i) := by
    rw [← Finset.prod_inv_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (ht i).le) (fun i _ => hinv i)
  refine ⟨lt_min hprod (Real.exp_pos _), (min_le_left _ _).trans hprod1,
    fun i => (min_le_left _ _).trans (hprodi i), min_le_right _ _, ?_,
    hsum.trans hsumScale, ?_⟩
  · unfold preparedUniformDegreeTolerance
    rcases le_total (∏ i, t i) (Real.exp (-Qσ)) with h | h
    · rw [min_eq_left h]
      exact hprodInv.trans (Real.exp_le_exp.mpr hsumScale)
    · rw [min_eq_right h, ← Real.exp_neg, neg_neg]
      exact Real.exp_le_exp.mpr hQScale
  · intro i
    exact (Finset.single_le_sum (fun j _ => hPtail j) (Finset.mem_univ i)).trans hsumScale

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedDetectedCanonicalNativeSource
namespace OAI

section

namespace Erdos3
open scoped NNReal

private theorem prepared_jointAffineSourceEnvelope_ge_accuracy {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    E ≤ jointAffineSourceEnvelope D P E F := by
  have hInv : 0 ≤ jointAffineInverseEnvelope D P E F := by
    have := affineInverseAxisEnvelope_nonneg hD hP hE hF
    unfold jointAffineInverseEnvelope
    positivity
  have hDer : 0 ≤ jointAffineDerivativeEnvelope D P := by
    have := affineDerivativeAxisEnvelope_nonneg hD hP
    unfold jointAffineDerivativeEnvelope
    positivity
  have hWeight : 0 ≤ jointAffineWeightEnvelope D P E F := by
    have := affineWeightAxisEnvelope_nonneg hD hP hE hF
    unfold jointAffineWeightEnvelope
    positivity
  have hOut := mul_nonneg hD hD
  have hParam := mul_nonneg hD (affineMinorVariableEnvelope_nonneg hD)
  dsimp only [jointAffineSourceEnvelope]
  linarith

theorem prepared_affineProfileToleranceEnvelope_ge_accuracy (degree : ℕ)
    {D N E F : ℝ} (A T : ℝ≥0)
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    E ≤ affineProfileToleranceEnvelope degree D N (A : ℝ) (T : ℝ) E F := by
  have hC : 0 ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold affineProfileCoefficientEnvelope
    positivity
  have hInput : E ≤ affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F := by
    exact (by linarith : E ≤ E + D + 4).trans
      (prepared_jointAffineSourceEnvelope_ge_accuracy hD hC (by positivity) hF)
  have hRest : 0 ≤ 3 * N * (degree + 2 : ℕ) +
      (2 * (D + affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) + degree * D) + 1) := by
    positivity
  unfold affineProfileToleranceEnvelope
  linarith

namespace VectorPolynomial

theorem allocatedAffineLengthLog_mono_density (m : ℕ)
    {D P Prho Pk target F F' Tmod : ℝ} (hF : F ≤ F') :
    allocatedAffineLengthLog m D P Prho Pk target F Tmod ≤
      allocatedAffineLengthLog m D P Prho Pk target F' Tmod := by
  dsimp only [allocatedAffineLengthLog, progressionSliceLengthLog]
  linarith

theorem allocatedAffineLengthLog_prepared_density (m : ℕ)
    (D P Prho Pk target p Tmod : ℝ) :
    allocatedAffineLengthLog m D P Prho Pk target (p + 1) Tmod ≤
      allocatedAffineLengthLog m D P Prho Pk target (p + 2) Tmod :=
  allocatedAffineLengthLog_mono_density m (by linarith)

theorem prepared_affineProfileToleranceEnvelope_kernel_bound {m : ℕ} (hm : 0 < m)
    {D Pk target p : ℝ} (A T : ℝ≥0)
    (hD : 1 ≤ D) (hk : 0 ≤ Pk) (ht : 0 ≤ target) (hp : 0 ≤ p) :
    Pk ≤ affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (A : ℝ) (T : ℝ) (target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5) (p + 2) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hc : (1 : ℝ) ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos hm (pow_pos (by decide : 0 < (2 : ℕ)) _))
  have hkC : Pk ≤ (m * 2 ^ (m + 1) : ℕ) * Pk := by
    simpa using mul_le_mul_of_nonneg_right hc hk
  have hCD : (m * 2 ^ (m + 1) : ℕ) * Pk ≤
      D * ((m * 2 ^ (m + 1) : ℕ) * Pk) := by
    simpa using mul_le_mul_of_nonneg_right hD (by positivity :
      0 ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk)
  have hE : Pk ≤ target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5 := by
    linarith
  exact hE.trans (prepared_affineProfileToleranceEnvelope_ge_accuracy m A T hD0
    (by positivity) (hk.trans hE) (by positivity))

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralProductivityEarlyGain
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

private theorem allocatedAffineCoveredComparison_instances
    {m : ℕ} {G : Type} [fG : Fintype G] [dG : DecidableEq G]
    {I : Fin m → Type} [fI : ∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [fB : ∀ a, Fintype (B a)]
    {α : Type} [fα : Fintype α] [dα : DecidableEq α] {O : Fin m → Type}
    {dB₁ dB₂ : ∀ a, DecidableEq (B a)}
    {fO₁ fO₂ : ∀ j, Fintype (O j)} {dO₁ dO₂ : ∀ j, DecidableEq (O j)}
    {rows : ∀ j, O j → Finset α} {δ η : ℝ}
    {ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0} {t : ℝ} {htone : t ≤ 1}
    (h : @AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} m G fG dG I fI n B fB dB₁
      α fα dα O fO₁ dO₁ rows δ η ρ t htone) :
    @AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} m G fG dG I fI n B fB dB₂
      α fα dα O fO₂ dO₂ rows δ η ρ t htone := by
  have hB : dB₁ = dB₂ := Subsingleton.elim _ _
  have hF : fO₁ = fO₂ := Subsingleton.elim _ _
  have hO : dO₁ = dO₂ := Subsingleton.elim _ _
  cases hB
  cases hF
  cases hO
  exact @h

theorem allocatedEarlyNativeSourceGeometryGeneral_of_fields
    {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (Pchart P D target Pk Prho Qstride pDetect : ℝ) (K : ℝ≥0)
    (hP : 0 ≤ P)
    (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hPk : 0 ≤ Pk) (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1)
      (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    (η : ℝ) (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} (G := G) B
      (fun j : Fin m => (Subtype.val : boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
      (Real.exp (-(pDetect + 1))) η ρ t htone)
    (hρ : ∀ partition, 0 < ρ partition)
    (hρ1 : ∀ partition, ρ partition ≤ 1)
    (hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho)
    (hσsmall : ∀ j, σ j ≤ t)
    (T : Fin m → ℝ)
    (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
          ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hradius : ∀ j, (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card * T j ≤ (siteRadius : ℝ))
    (hbudgets : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
      (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
      (∀ j, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin (s + 1))) *
          (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4))
    (hK : ∀ j, (R j)⁻¹ ≤ K) :
    Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B)
      (U := U) (basis := basis) (S := S) (nX := nX)
      Pchart P D target Pk Prho Qstride pDetect K) := by
  refine ⟨{
    hP := hP
    hRP := hRP
    hRi := hRi
    hσi := hσi
    hcount := hcount
    hdimensions := hdimensions
    hPk := hPk
    hPrho := hPrho
    htarget := htarget
    hlength := hlength
    η := η
    hη0 := hη0
    hηsmall := hηsmall
    ρ := ρ
    t := t
    htone := htone
    hs := ?_
    hρ := hρ
    hρ1 := hρ1
    hρlog := hρlog
    hσsmall := hσsmall
    T := T
    hT := hT
    hsource := hsource
    siteRadius := siteRadius
    hrone := hrone
    hradius := hradius
    hbudgets := hbudgets
    hK := hK }⟩
  exact @allocatedAffineCoveredComparison_instances m G _ _ I _ n B _
    (Fin (s + 1)) _ _ (fun j => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type))
    _ _ _ _ _ _ _ (Real.exp (-(pDetect + 1))) η ρ t htone (@hs)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

theorem preparedUniformDegreeGeometryAt_of_prescribedScale
    {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {Bstruct pnum pDetect aDetect Qstride Pscale target Prho Ptail : ℝ}
    (Cdetect nX : ℕ)
    (hm : 0 < m) (hs : s ≤ m)
    (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum)
    (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hp : 0 ≤ pDetect) (ha : 0 ≤ aDetect) (hQstride : 0 ≤ Qstride)
    (htarget : 0 ≤ target) (hPrho : 0 ≤ Prho)
    (hPscale : 0 ≤ Pscale)
    (hDscale : allocatedComparisonDimension m pnum ≤ Pscale)
    (hRadiusScale : allocatedCommonProductRadiusLog m Bstruct Bstruct ≤ Pscale) :
    let D := allocatedComparisonDimension m pnum
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let gainLog := slicedDetectionGainLog s Cdetect
      (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
    ∀ (comparison : PreparedUniformDegreeComparison (G := G) B s D target Pk Prho Ptail pDetect)
      {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ comparison.t) →
      (∀ j, (σ j)⁻¹ ≤ Real.exp Pscale) →
      Real.exp (allocatedAffineLengthLog m D Pscale Prho Pk target (pDetect + 2)
        (((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride)) ≤ S.value →
      PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
        Bstruct Pscale D target Pk Prho Qstride pDetect pRadius aDetect gainLog := by
  intro D pRadius R gainLog Pk comparison σ S hσt hσinv hlength
  obtain ⟨hRadius, hR, hgeometry⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius.{0,0,0,0} m)).2 hB hB
  have hD : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum.1).1
  have hgain : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s Cdetect _ hp hp ha
  have hPk : 0 ≤ Pk := by
    change 0 ≤ scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
    rw [scalarKernelLogarithmicBudget_eq]
    positivity
  have hTmod : 0 ≤ ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hPk)
      (mul_nonneg (Nat.cast_nonneg _) hQstride)
  have hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ hs)
      (fun _ => Subtype.val_injective) hnum.1 hvars hI hn
  let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
  let : ∀ j : Fin m, Nonempty (rowSets j) := fun j =>
    ⟨⟨∅, (mem_boundedBooleanJetRows (j.val + 1) ∅).mpr (by simp)⟩⟩
  obtain ⟨hrone, _, hT, hsource, hradius, hbudgets⟩ :=
    hgeometry (G := G) B rowSets
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ hs)
      (hvars.trans hnum.2) (fun j => (hI j).trans hnum.2) (fun j => (hn j).trans hnum.2)
  have hRi (j) : (R j)⁻¹ ≤ Real.exp Pscale :=
    (hR j).2.2.trans (Real.exp_le_exp.mpr hRadiusScale)
  have hcount (j : Fin m) : (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale :=
    ((add_le_add (hdimensions.coefficients j) (le_refl (1 : ℝ))).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDscale)
  refine ⟨?_, ?_⟩
  · refine allocatedEarlyNativeSourceGeometryGeneral_of_fields B U basis S
      Bstruct Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))
      hPscale (fun j => (hR j).2.1.trans (Real.one_le_exp hPscale))
      hRi hσinv hcount hdimensions hPk hPrho htarget ?_
      (Real.exp (-(target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5)))
      (Real.exp_pos _).le ?_ comparison.ρ comparison.t comparison.htone comparison.hs
      comparison.hρ comparison.hρ1 comparison.hρlog hσt
      (allocatedIdealCoverSupport (G := G) B rowSets) hT hsource
      (allocatedProductIdealSiteRadius (G := G) B rowSets) hrone hradius hbudgets
      (fun j => (hR j).2.2.trans (Real.le_coe_toNNReal _))
    · apply le_trans _ hlength
      simp only [Fintype.card_fin]
      exact Real.exp_le_exp.mpr
        (allocatedAffineLengthLog_prepared_density m D Pscale Prho Pk target pDetect _)
    · apply Real.exp_le_exp.mpr
      linarith only
  · intro α hα gain
    have hcutoff := slicedDetection_kernel_cutoff_bound_s2 s Cdetect
      (Fintype.card (LayerSamplerVariables G I n B)) G hp hp ha hα
    exact ⟨slicedDetectionGain_lower s Cdetect _ hα, hcutoff,
      allocatedAffineLength_kernel_ready hm hD hPscale hPrho hPk htarget
        (by linarith only [hp]) hTmod hcutoff hlength⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleGeometryPrescribedScale_s2_oai (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
    (hm : 0 < m) (hdegree : ∀ s, degree s ≤ m) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ s : K, ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin ((degree s) + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (hp : ∀ s, 0 ≤ pDetect s) (ha : ∀ s, 0 ≤ aDetect s) (hQstride : 0 ≤ Qstride)
    (htarget : ∀ s, 0 ≤ target s) :
    PreparedFiniteScheduleGeometryPrescribedScaleStatement (G := G) m degree Cdetect B
      (Bstruct := Bstruct) (pnum := pnum) (Qstride := Qstride) nX pDetect aDetect target := by
  delta PreparedFiniteScheduleGeometryPrescribedScaleStatement
  intro Aradius pRadius R D gainLog Pk E Prho Ptail Tmod
  obtain ⟨hRadius, hR, hgeometry⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius.{0,0,0,0} m)).2 hB hB
  have hD : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum.1).1
  have hD1 : 1 ≤ D := by
    have hd := (allocatedComparisonDimension_bounds m hnum.1).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    exact hm1.trans hd
  have hgain (s) : 0 ≤ gainLog s :=
    slicedDetectionGainLog_nonneg (degree s) (Cdetect s) _ (hp s) (hp s) (ha s)
  have hPk (s) : 0 ≤ Pk s := by
    change 0 ≤ scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgain s
    have := hp s
    positivity
  have hcompare (s : K) : 0 ≤ Prho s ∧ 0 ≤ Ptail s ∧
      Nonempty (PreparedUniformDegreeComparison (G := G) B (degree s) D (target s)
        (Pk s) (Prho s) (Ptail s) (pDetect s)) :=
    exists_preparedUniformDegreeComparison_s2 B hm (hdegree s) hnum.1
      hvars hI hn (hblocks s) (hp s) (ha s) (htarget s) hQstride (Cdetect s) nX
  let data := fun s => Classical.choice (hcompare s).2.2
  let t := fun s => (data s).t
  have hTail (s) : 0 ≤ Ptail s := (hcompare s).2.1
  refine ⟨hRadius, hR, hD, fun s => ⟨hgain s, hPk s, (hcompare s).1, hTail s⟩,
    t, fun s => ⟨(data s).ht, (data s).htone, (data s).htinv⟩, ?_⟩
  intro Qσ hQσ σ Pscale lengthLogs
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hTailScale⟩ :=
    preparedUniformDegreeTolerance_bounds t Ptail (fun s => (data s).ht)
      (fun s => (data s).htone) hTail (fun s => (data s).htinv)
      hQσ (add_nonneg hD hRadius.1)
  have hsum : 0 ≤ ∑ s, Ptail s := Finset.sum_nonneg (fun s _ => hTail s)
  have hDscale : D ≤ Pscale := by
    change D ≤ D + pRadius + ∑ s, Ptail s + Qσ
    linarith only [hRadius.1, hsum, hQσ]
  have hRadiusScale : pRadius ≤ Pscale := by
    change pRadius ≤ D + pRadius + ∑ s, Ptail s + Qσ
    linarith only [hD, hsum, hQσ]
  have hPkScale (s) : Pk s ≤ Pscale :=
    (prepared_affineProfileToleranceEnvelope_kernel_bound hm canonicalSublevelCutoffLip
      canonicalTransitionLip hD1 (hPk s) (htarget s) (hp s)).trans (hTailScale s)
  refine ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, ?_⟩
  intro J _ U basis S hlengths s
  exact preparedUniformDegreeGeometryAt_of_prescribedScale B U basis (Cdetect s) nX
    hm (hdegree s) hB hnum hvars hI hn (hp s) (ha s) hQstride (htarget s)
    (hcompare s).1 hPscale hDscale hRadiusScale (data s) S
    (fun _ => hσt s) (fun _ => hσinv) (hlengths s)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleGeometryPrescribedScale_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleGeometryPrescribedScale_s2_oai
