-- Prove2me | solution 1 for GlobalTheory.HolZeros.exists_implicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:33:13.850033+00:00
-- url     : https://prove2.me/submissions/2b0a0412-04ca-4b8f-9e56-e7da8e3df8b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SimpleZerosMoveHolomorphically
import Theorems.Thm_GlobalTheory_KeyPow_ClauseH_mono
import Theorems.Thm_GlobalTheory_KeyPow_KeyRule_mono
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open Filter Topology
open GlobalTheory GlobalTheory.HolZeros
namespace GlobalTheory.HolZeros
theorem _root_.solution {g : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [CompleteSpace P] (F : Fin g → P → (Fin g → ℂ) → ℂ) (p₀ : P) (z₀ : Fin g → ℂ)
    (hF : ∀ i, ContDiffAt ℂ 1 (fun q : P × (Fin g → ℂ) => F i q.1 q.2) (p₀, z₀))
    (h0 : ∀ i, F i p₀ z₀ = 0)
    (hd : (Matrix.of fun i k => fderiv ℂ (F i p₀) z₀ (Pi.single k 1)).det ≠ 0) :
    ∃ z : P → Fin g → ℂ, z p₀ = z₀ ∧ (∀ᶠ p in 𝓝 p₀, DifferentiableAt ℂ z p) ∧
      (∀ᶠ p in 𝓝 p₀, ∀ i, F i p (z p) = 0) ∧
      (∀ᶠ p in 𝓝 p₀, (Matrix.of fun i k => fderiv ℂ (F i p) (z p) (Pi.single k 1)).det ≠ 0) ∧
      ∀ᶠ q in 𝓝 (p₀, z₀), (∀ i, F i q.1 q.2 = 0) → z q.1 = q.2 := by
  set f : P × (Fin g → ℂ) → Fin g → ℂ := fun q i => F i q.1 q.2 with hf
  have cdf : ContDiffAt ℂ 1 f (p₀, z₀) := contDiffAt_pi.2 hF
  have key : ∀ q : P × (Fin g → ℂ), DifferentiableAt ℂ f q → ∀ i v,
      fderiv ℂ (F i q.1) q.2 v = fderiv ℂ f q (0, v) i := by
    intro q hq i v
    have h1 := HasFDerivAt.comp (f := fun y => (q.1, y)) q.2
      (hasFDerivAt_pi'.1 hq.hasFDerivAt i) (hasFDerivAt_prodMk_right (𝕜 := ℂ) q.1 q.2)
    have h2 : fderiv ℂ (F i q.1) q.2 = _ := h1.fderiv
    rw [h2]
    simp
  have hinv : (fderiv ℂ f (p₀, z₀) ∘L ContinuousLinearMap.inr ℂ P (Fin g → ℂ)).IsInvertible := by
    set L := fderiv ℂ f (p₀, z₀) ∘L ContinuousLinearMap.inr ℂ P (Fin g → ℂ) with hL
    have hdet : L.det ≠ 0 := by
      rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix' ]
      convert hd using 2
      ext i k
      rw [Matrix.of_apply, key (p₀, z₀) (cdf.differentiableAt one_ne_zero)]
      simp [hL, LinearMap.toMatrix'_apply]
    exact ⟨L.toContinuousLinearEquivOfDetNeZero hdet, rfl⟩
  have hf0 : f (p₀, z₀) = 0 := funext h0
  have hz := cdf.contDiffAt_implicitFunction one_ne_zero hinv
  have hz0 := cdf.implicitFunction_apply_self one_ne_zero hinv
  set z := cdf.implicitFunction one_ne_zero hinv with hzdef
  refine ⟨z, hz0, ?_, ?_, ?_, ?_⟩
  · exact (hz.eventually (by simp)).mono fun p hp => hp.differentiableAt one_ne_zero
  · filter_upwards [cdf.eventually_apply_implicitFunction one_ne_zero hinv] with p hp i
    exact congrFun (hp.trans hf0) i
  · have ht : Tendsto (fun p => (p, z p)) (𝓝 p₀) (𝓝 (p₀, z₀)) := by
      have := (continuousAt_id.prodMk hz.continuousAt).tendsto
      simp only [id] at this hz0
      rwa [hz0] at this
    have hc : ContinuousAt (fderiv ℂ f) (p₀, z₀) := cdf.continuousAt_fderiv one_ne_zero
    have hc2 : ContinuousAt (fun q => (Matrix.of fun i k =>
        fderiv ℂ f q (0, Pi.single k 1) i).det) (p₀, z₀) := by
      refine (continuous_id.matrix_det).continuousAt.comp (f := fun q => (Matrix.of fun i k =>
        fderiv ℂ f q (0, Pi.single k 1) i)) ?_
      refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun k => ?_
      exact continuousAt_pi.1 (hc.clm_apply continuousAt_const) i
    have hne : ∀ᶠ q in 𝓝 (p₀, z₀), (Matrix.of fun i k =>
        fderiv ℂ f q (0, Pi.single k 1) i).det ≠ 0 := by
      refine hc2.eventually_ne ?_
      simpa only [← key (p₀, z₀) (cdf.differentiableAt one_ne_zero)] using hd
    filter_upwards [ht.eventually hne, ht.eventually (cdf.eventually (by simp))] with p h1 h2
    simpa only [← key (p, z p) (h2.differentiableAt one_ne_zero)] using h1
  · filter_upwards [cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv] with q hq h
    exact hq.1 ((funext h).trans hf0.symm)
end GlobalTheory.HolZeros
