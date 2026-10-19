-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSource_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T08:44:46.377984+00:00
-- url     : https://prove2.me/submissions/d572d277-9142-490a-981c-f5bef75afb24

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B290
import Definitions.Def_OAIE3v2B291
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeDirectSource_of_geometry_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeModelChain_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeProductiveSourceRawBounds_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem smoothSpatialDisplacementCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) :
    0 ≤ smoothSpatialDisplacementCost N s M := by
  unfold smoothSpatialDisplacementCost spatialKernelErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem spatialKernelErrorConstant_le_exp (j e : ℕ) {U P : ℝ} (K : ℝ≥0)
    (hU0 : 0 ≤ U) (hU : U ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P) :
    spatialKernelErrorConstant j e U 1 K ≤
      Real.exp ((j : ℝ)^2+(j+2)*P+2*e) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold spatialKernelErrorConstant
  norm_num only [mul_one]
  calc
    _ ≤ (Real.exp ((j : ℝ)^2)*(Real.exp P)^j)*(Real.exp 2)^e*Real.exp P*Real.exp P := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem smoothSpatialDisplacementCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    smoothSpatialDisplacementCost N s M ≤
      Real.exp (spatialDisplacementLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
        (Fintype.card N) p) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let e := Fintype.card (UnselectedColumn s)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, _, hK⟩ := spatialProfileLog_bounds N s hp hM
  have he : (e : ℝ) ≤ d := by
    simp only [d, e, Fintype.card_sum, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsmall : ((e+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
    apply le_trans _ hK
    gcongr
  have hc := spatialKernelErrorConstant_le_exp j e ((e+j)*probabilityProfileLipschitz)
    (by unfold scalarSpatialInverseAllowance; positivity) hU
    (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hsmall)
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  unfold smoothSpatialDisplacementCost
  calc
    _ ≤ Real.exp P * Real.exp ((j : ℝ)^2+(j+2)*P+2*e) * Real.exp (Fintype.card N : ℝ) := by
      apply mul_le_mul _ hn (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hG hc (by unfold spatialKernelErrorConstant scalarSpatialInverseAllowance; positivity)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [spatialDisplacementLog, P]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

theorem spatialPrimitiveEnvelope_bounds {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) :
    let R := spatialPrimitiveEnvelope p E l
    0 ≤ R ∧ p ≤ R ∧ E + 3 ≤ R ∧ p ^ 3 + anisotropicSpatialCapLog p ≤ R ∧
      coefficientErrorVolumeLog p + 4 ≤ R ∧ spatialDisplacementEnvelope p ≤ R ∧
      spatialDiscretizationEnvelope p l ≤ R ∧ spatialLipschitzCostEnvelope p l ≤ R ∧
      spatialThresholdEnvelope p l ≤ R ∧ spatialBoundaryEnvelope p l ≤ R ∧
      spatialMovementEnvelope p l ≤ R := by
  obtain ⟨_, hd, ha, hm, hk⟩ := spatialCostEnvelopes_nonneg hp hl
  have hcap : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p := by
    have := anisotropicSpatialCapLog_nonneg hp
    positivity
  have hvol : 0 ≤ coefficientErrorVolumeLog p + 4 := by
    unfold coefficientErrorVolumeLog
    positivity
  have hK : 0 ≤ spatialLipschitzCostEnvelope p l := by
    unfold spatialLipschitzCostEnvelope
    positivity
  have hT : 0 ≤ spatialThresholdEnvelope p l := by
    unfold spatialThresholdEnvelope
    positivity
  have hQ : 0 ≤ spatialBoundaryEnvelope p l := by
    unfold spatialBoundaryEnvelope
    positivity
  have hD : 0 ≤ spatialMovementEnvelope p l := by
    unfold spatialMovementEnvelope
    positivity
  dsimp only [spatialPrimitiveEnvelope]
  repeat' constructor
  all_goals linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTupleParameterBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedSpatialShare_half_inv_le (E : ℝ) :
    (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
  unfold normalizedSpatialShare
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem normalizedTupleEarlyParameters_bound {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q M : ℕ} (s : Fin q ↪ G)
    {p E l : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hMp : (M : ℝ) ≤ Real.exp p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    let R := spatialPrimitiveEnvelope p E l
    (normalizedTupleTolerance X p E)⁻¹ ≤ Real.exp (spatialTupleToleranceLog R) ∧
      (normalizedTupleNarrowWidth X N s M p E)⁻¹ ≤
        Real.exp (2 * (R + spatialTupleToleranceLog R) + 4) := by
  obtain ⟨hR, hpR, hER, hcapR, hvolR, hdispR, _⟩ :=
    spatialPrimitiveEnvelope_bounds hp hE hl
  obtain ⟨he, hd, _⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hI : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hB := (smoothSpatialDisplacementCost_le_exp N s hp hMp).trans
    (Real.exp_le_exp.mpr ((spatialDisplacementLog_le_envelope _ _ _ _ hp hI hd he hN).trans hdispR))
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεR := (normalizedSpatialShare_half_inv_le E).trans (Real.exp_le_exp.mpr hER)
  exact ⟨spatialTupleTolerance_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
    hε hR (hX.trans hpR) (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hεR,
    spatialTupleEarlyWidth_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
      (smoothSpatialDisplacementCost_nonneg N s M) hε hR (hX.trans hpR)
      (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hB hεR⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ b, Fintype (B b)]

theorem preparedModularDetector_narrow_width {q Mk nX : ℕ} (selection : Fin q ↪ G)
    {Pphysical coarseTarget : ℝ} (hp : 0 ≤ Pphysical) (htarget : 0 ≤ coarseTarget)
    (hMk : (Mk : ℝ) ≤ Real.exp Pphysical) (hq : ((q + 1 : ℕ) : ℝ) ≤ Pphysical)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (hnX : (nX : ℝ) ≤ Pphysical) :
    let R := spatialPrimitiveEnvelope Pphysical coarseTarget 0
    let ξLog := 2 * (R + spatialTupleToleranceLog R) + 4
    0 ≤ ξLog ∧
      (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection Mk Pphysical coarseTarget)⁻¹ ≤ Real.exp ξLog := by
  intro R ξLog
  have hG := (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hN := (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical := by simpa only [Fintype.card_fin] using hnX
  have hR : 0 ≤ R := (spatialPrimitiveEnvelope_bounds hp htarget (le_refl 0)).1
  have ht := spatialTupleToleranceLog_nonneg hR
  refine ⟨by dsimp only [ξLog]; positivity, ?_⟩
  exact (normalizedTupleEarlyParameters_bound
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := Fin nX)
    selection hp htarget (le_refl 0) hMk hq hG hN hX).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

theorem forecastAugmentedUnitThreshold_half_source_precision {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) :
    Real.exp (-(2 * (u + 1) + 4 * p + 7)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / 2 := by
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 1 := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / 2 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
        (by linarith [Real.add_one_le_exp (1 : ℝ)])
    _ ≤ _ := div_le_div_of_nonneg_right
      (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2 (by norm_num)

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_separate_source_precision {u p pSource K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hSource : 0 ≤ pSource)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    0 ≤ u + 2 * p + 1 ∧
      Real.exp (-(2 * (u + 2 * p + 1) + 4 * pSource + 7)) ≤
        forecastAugmentedUnitThreshold u p K C Fcap / 2 := by
  refine ⟨by positivity, ?_⟩
  apply (Real.exp_le_exp.mpr
    (show -(2 * (u + 2 * p + 1) + 4 * pSource + 7) ≤
      -(2 * (u + 1) + 4 * p + 7) by linarith)).trans
  exact forecastAugmentedUnitThreshold_half_source_precision hu hp hK hC hKp hCp hFp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem enlargedPreparedCommonSamplerBlock_positiveModerate (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  dsimp only
  apply le_trans _ ((le_max_left _ _).trans
    (enlargedPreparedCommonSamplerBlock_spectrum L Jalloc s hs a))
  unfold positiveModerateSpectrumBlockCount
  apply Nat.succ_le_succ
  apply max_le_max (le_refl _)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastGoodInterface
namespace OAI

section

namespace Erdos3

theorem preparedForecastGoodBudgets (Asp : ℕ) {baseB₀ Pchart Pwidth g V : ℝ}
    (hbase : 0 ≤ baseB₀) (hchart : 0 ≤ Pchart) (hwidth : 0 ≤ Pwidth)
    (hg : 0 ≤ g) (hV : 0 ≤ V) :
    let Bcert := preparedForecastGoodCertificateBudget baseB₀ Pchart Pwidth g V
    let Pgood := preparedForecastGoodAnalyticBudget Asp baseB₀ Pchart Pwidth g V
    0 ≤ Bcert ∧ baseB₀ ≤ Bcert ∧ Pchart ≤ Bcert ∧
      jointPhysicalBaseLog Pwidth (g + 8) V ≤ Bcert ∧
      0 ≤ Pgood ∧ Bcert ≤ Pgood ∧ Pwidth ≤ Pgood ∧
      (Pchart + Asp) ^ Asp ≤ Pgood ∧ g + 8 ≤ Pgood := by
  intro Bcert Pgood
  have hphysical : 0 ≤ jointPhysicalBaseLog Pwidth (g + 8) V := by
    unfold jointPhysicalBaseLog
    positivity
  have hcert : 0 ≤ Bcert := by
    dsimp only [Bcert, preparedForecastGoodCertificateBudget]
    positivity
  have hpower : 0 ≤ (Pchart + Asp) ^ Asp := by positivity
  have hgood : 0 ≤ Pgood := by
    change 0 ≤ Bcert + Pwidth + (Pchart + Asp) ^ Asp + g + 9
    positivity
  have hdef : Bcert = 1 + baseB₀ + Pchart + jointPhysicalBaseLog Pwidth (g + 8) V := rfl
  have hgdef : Pgood = Bcert + Pwidth + (Pchart + Asp) ^ Asp + g + 9 := rfl
  refine ⟨hcert, ?_, ?_, ?_, hgood, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hdef, hgdef, hbase, hchart, hwidth, hg, hphysical, hcert, hpower]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedShortForecastRawSourceBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

theorem preparedShortForecastSourceRawBounds_to_good
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget : ℝ)
    (baseB0 Vlog gainLog gain Pwidth : ℝ) (Qgood : ℕ) (D : ℝ)
    (H : PreparedShortForecastSourceRawBounds prep U b S selection Pdetect uSource pModel pSlice Vtail u p forecastCap
      Pchart Qstride Pmaster Plate Pphysical coarseTarget baseB0 Vlog gainLog gain Pwidth Qgood D) :
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget
      (preparedCenteredShortForecastSpatialExponent m) baseB0 Pchart Pwidth gainLog Vlog
    PreparedCenteredShortForecastGoodBounds prep U b S selection Pdetect uSource pModel pSlice
      Vtail u p forecastCap Pchart Qstride Pmaster Plate Pphysical coarseTarget
      Bcert Vlog gainLog gain Pwidth Pchart Pgood Qgood D := by
  intro Bcert Pgood
  obtain ⟨_, hbaseCert, hchartCert, hphysicalCert, _, hcertGood, hwidthGood,
      hcutoffGood, hgainGood⟩ :=
    preparedForecastGoodBudgets (preparedCenteredShortForecastSpatialExponent m)
      H.hbase H.hchart H.hwidth H.hg H.hVlog
  exact {
    hcert := H.hcert Bcert hbaseCert
    hnX := H.hnX
    hσ1 := H.hσ1
    hsmall := H.hsmall
    hMaster := H.hMaster
    hLate := H.hLate
    hd := H.hd
    hD := H.hD
    hnMaster := H.hnMaster
    hRi := H.hRi
    hσi := H.hσi
    hS := H.hS
    hchartB := hchartCert
    hprojection := H.hprojection
    hphysical := hphysicalCert
    hVlog := H.hVlog
    hQexp := H.hQexp
    hP₀ := H.hchart
    hnP₀ := H.hnChart
    hgP₀ := H.hgChart
    hcutoffP := hcutoffGood
    hBP := hcertGood
    hwidthP := hwidthGood
    hg := H.hg
    hgP := hgainGood
    hgain := H.hgain
    hstrideWidth := H.hstrideWidth
    hτWidth := H.hτWidth
    hξWidth := H.hξWidth }

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastSourceModelAttachment
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem sharedWidthPreparedShortForecastSourceModelAttachment
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (baseB0 Vlog gainLog gain Pwidth : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : PreparedShortForecastSourceRawBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      baseB0 Vlog gainLog gain Pwidth Qgood D)
    (hLateWidth : Plate ≤ Pwidth)
    (hModel : SharedWidthPreparedCenteredForecastModelInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget
      (preparedCenteredShortForecastSpatialExponent m) baseB0 Pchart Pwidth gainLog Vlog
    SharedWidthPreparedCenteredShortForecastGoodModelInterface (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      Bcert gainLog gain Pgood Qgood spatialEmbedding := by
  intro Bcert Pgood
  have Hgood := preparedShortForecastSourceRawBounds_to_good
    (m := m) (nX := nX) (M := M) prep U b S selection
    Pdetect uSource pModel pSlice Vtail u p forecastCap
    Pchart Qstride Pmaster Plate Pphysical coarseTarget
    baseB0 Vlog gainLog gain Pwidth Qgood D H
  have Hshared : SharedWidthPreparedCenteredShortForecastGoodBounds prep U b S selection
      Pdetect uSource pModel pSlice Vtail u p forecastCap
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      Bcert Vlog gainLog gain Pwidth Pchart Pgood Qgood D := {
    hcert := Hgood.hcert
    hnX := Hgood.hnX
    hσ1 := Hgood.hσ1
    hsmall := Hgood.hsmall
    hMaster := Hgood.hMaster
    hLate := Hgood.hLate
    hd := Hgood.hd
    hD := Hgood.hD
    hnMaster := Hgood.hnMaster
    hRi := Hgood.hRi
    hσi := Hgood.hσi
    hS := Hgood.hS
    hchartB := Hgood.hchartB
    hprojection := Hgood.hprojection
    hphysical := Hgood.hphysical
    hVlog := Hgood.hVlog
    hQexp := Hgood.hQexp
    hP₀ := Hgood.hP₀
    hnP₀ := Hgood.hnP₀
    hgP₀ := Hgood.hgP₀
    hcutoffP := Hgood.hcutoffP
    hBP := Hgood.hBP
    hwidthP := Hgood.hwidthP
    hg := Hgood.hg
    hgP := Hgood.hgP
    hgain := Hgood.hgain
    hstrideWidth := Hgood.hstrideWidth
    hτWidth := Hgood.hτWidth
    hξWidth := hLateWidth }
  exact sharedWidthPreparedCenteredShortForecastGoodModelInterface_of_model_s2
    (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀)
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    Bcert Vlog gainLog gain Pwidth Pchart Pgood Qgood spatialEmbedding
    (D := D) Hshared hModel

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSourceModel
namespace OAI


namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (u p : ℝ)
local notation "uSource" => u + 2 * p + 1
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

include ν bW μrows in

theorem preparedUniformDegreeGeometryModel
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius uSource pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * uSource + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (0 + 1) * (0 + 3) ≤ Fintype.card G)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget ∧
    (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect pDetect (α / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate := by
  have hKp : Kslice ≤ Real.exp p := Real.exp_le_exp.mpr hSliceLog
  have hCap := marginalCap_max_one_exp_bound hp hCtail
  have hC : 0 ≤ max 1 Ctail := zero_le_one.trans hCap.1
  have hαlower := (forecastAugmented_separate_source_precision hu hp scalar.model_master.1
    (Real.exp_nonneg _) hC hKp hCap.2 hForecastCapP).2
  have hαone : α / 2 ≤ 1 := by
    have h := (forecastAugmentedUnitThreshold_bounds hu hp
      (Real.exp_nonneg _) hC hKp hCap.2 hForecastCapP).2.1
    linarith only [h]
  have hDirect := preparedUniformDegreeDirectSource_of_geometry_s2
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) («α» := α / 2) (τ := τ)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    (Nat.zero_le m) Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain
    Pphysical coarseTarget pRadius scalar geometryAt hRone hRinv hσone hSLate
    hBa hBi hcapacity hαlower hαone
  obtain ⟨⟨geometry⟩, hgainKernel⟩ := geometryAt
  constructor
  · exact preparedUniformDegreeModelChain_s2
      (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (ν := ν) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
      scalar.master_nonneg scalar.late geometry.hdimensions scalar.dimension_master
      scalar.ambient_master scalar.chart_master scalar.stride_master.2 scalar.physical_master.2
      (fun j => (hRinv j).trans (Real.exp_le_exp.mpr scalar.radius_master))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr scalar.scale_late))
      hSLate hσone (fun C hC hBound => (geometry.hbudgets C hC hBound).1)
      hu hp hSliceLog hCtail hForecastCap hForecastCapP
  · have hMk := (hgainKernel (α / 2) hαlower).2.1
    have hCoarse : 0 ≤ coarseTarget := by
      linarith only [scalar.gain_master.1, scalar.coarse_lower]
    have hwidth := preparedModularDetector_narrow_width B selection scalar.physical_master.1
      hCoarse (hMk.trans (Real.exp_le_exp.mpr scalar.kernel_physical))
      scalar.detector_physical scalar.variables_physical scalar.ambient_physical
    exact hwidth.2.trans (Real.exp_le_exp.mpr scalar.xi_late)

end Erdos3.VectorPolynomial

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastProductiveModelAttachment
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem sharedWidthPreparedShortForecastProductiveModelAttachment
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (baseB0 Vlog gainLog gain Pwidth : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    {D : ℝ}
    (H : PreparedShortForecastSourceRawBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S)
      (selection := selection) (Pdetect := Pdetect) (uSource := uSource)
      (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
      (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget
      baseB0 Vlog gainLog gain Pwidth Qgood D)
    (hLateWidth : Plate ≤ Pwidth)
    (hchartMaster : Pchart ≤ Pmaster) (hstrideMaster : Qstride ≤ Pmaster)
    (hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster)
    (hτeq : τ = Real.exp (-(gainLog + (nX : ℝ) + 8)))
    (hξLate : (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate)
    (hModel : SharedWidthPreparedCenteredForecastModelInterface
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget
      (preparedCenteredShortForecastSpatialExponent m) baseB0 Pchart Pwidth gainLog Vlog
    SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      Bcert gainLog gain Pgood Qgood spatialEmbedding (4 * (Plate + 8) ^ 2) := by
  intro Bcert Pgood
  have hGood := sharedWidthPreparedShortForecastSourceModelAttachment
    (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀)
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    baseB0 Vlog gainLog gain Pwidth Qgood spatialEmbedding (D := D) H hLateWidth hModel
  have hBounds : PreparedCenteredForecastProductiveBounds
      prep U b S selection Pdetect uSource pModel pSlice Vtail τ u p forecastCap
      Pchart Qstride Pmaster Plate Pphysical coarseTarget gainLog (4 * (Plate + 8) ^ 2) D := {
    hnX := H.hnX
    hσ1 := H.hσ1
    hsmall := H.hsmall
    hMaster := H.hMaster
    hLate := H.hLate
    hd := H.hd
    hD := H.hD
    hnMaster := H.hnMaster
    hRi := H.hRi
    hσi := H.hσi
    hS := H.hS
    hchartMaster := hchartMaster
    hstrideMaster := hstrideMaster
    hProd := le_rfl
    hg := H.hg
    hGainMaster := hGainMaster
    hτeq := hτeq
    hξLate := hξLate }
  exact sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2
    (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀)
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    Bcert gainLog gain Pgood Qgood spatialEmbedding (4 * (Plate + 8) ^ 2)
    (D := D) hBounds hGood

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedUniformDegreeProductiveSource_s2_oai
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius (u + 2 * p + 1) pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt (m := m) («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog (u + 2 * p + 1) pModel) pRadius
      (2 * (u + 2 * p + 1) + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p)
    (hCtail : (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p)
    {Pseed Qw Vlog gainLog gain : ℝ} (Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hVlog : 0 ≤ Vlog) (hg : 0 ≤ gainLog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hchart : 0 ≤ Pchart) (hnChart : (nX : ℝ) ≤ Pchart)
    (hgChart : gainLog ≤ Pchart) (hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster)
    (hτeq : τ = Real.exp (-(gainLog + (nX : ℝ) + 8)))
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
          (gainLog + 8) Vlog Qgood ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedUniformDegreeProductiveSourceConclusion
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (stride := stride) (N := N) (Pdetect := Pdetect) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius Pscale
      Pseed Qw gainLog gain Vlog Qgood := by
  classical
  unfold PreparedUniformDegreeProductiveSourceConclusion
  intro baseB0 Pwidth Bcert Pgood
  obtain ⟨geometry⟩ := geometryAt.1
  have hσone (j) : σ j ≤ 1 := (geometry.hσsmall j).trans geometry.htone
  have hSLate := hS.trans (Real.exp_le_exp.mpr hWitnessLate)
  obtain ⟨hModel, hξLate⟩ := preparedUniformDegreeGeometryModel
    («B» := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    («selection» := (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))) (stride := stride) (N := N) (Pdetect := Pdetect) (pModel := pModel)
    (pSlice := pSlice) (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius
    scalar geometryAt hRone hRinv hσone hSLate
    (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep (modularInitialBlockCount m (nX + m * M)) 0
      (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep (modularInitialBlockCount m (nX + m * M)) 0
      (Nat.zero_le m) ⟨j, Sum.inr i⟩)
    (enlargedPreparedCommonKernel_analytic_capacity m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
    hu hp hSliceLog hCtail hForecastCap hForecastCapP
  obtain ⟨hRaw, hLateWidth⟩ := preparedUniformDegreeProductiveSourceRawBounds_s2
    prep U b S (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m)) Pdetect (u + 2 * p + 1) pModel pSlice Vtail u p forecastCap Qgood geometry
    hm hnX hCoord hpRadius hPseed hQw hVlog hg hQgood hQexp
    scalar.master_nonneg scalar.late scalar.dimension_master scalar.ambient_master
    scalar.radius_master scalar.scale_late hWitnessLate scalar.stride_master.2
    scalar.physical_master.2 hgain hchart hnChart hgChart hS hprincipal hξLate
  exact sharedWidthPreparedShortForecastProductiveModelAttachment
    (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
    («selection» := (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))) (stride := stride) (N := N) (Pdetect := Pdetect)
    («uSource» := (u + 2 * p + 1)) (pModel := pModel) (pSlice := pSlice) (Vtail := Vtail)
    (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    baseB0 Vlog gainLog gain Pwidth Qgood (preparedSpatialKernelBlocks m M nX)
    (D := D) hRaw hLateWidth scalar.chart_master scalar.stride_master.2
    hGainMaster hτeq hξLate hModel

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSource_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSource_s2_oai
