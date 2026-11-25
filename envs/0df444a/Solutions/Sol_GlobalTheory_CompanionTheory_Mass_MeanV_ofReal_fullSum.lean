-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.ofReal_fullSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:13.448829+00:00
-- url     : https://prove2.me/submissions/2f82b9ec-a2cc-43f2-80ec-1daad701daa2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlacesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmallStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultipliableLocalFactorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApproxStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingletonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeanValueFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_exists_zero_place
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_support_finite
import Theorems.Thm_GlobalTheory_T_multipliable_local_factors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (C : ℝ)
    (hGc : HasCompactSupport G) (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0)
    (hb2 : ∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2)
    (δ : ℝ) (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ Module.finrank ℚ F) * ∑' β : {β : F // β ≠ 0},
        ENNReal.ofReal (G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1)) =
      ENNReal.ofReal (fullSum θ G g δ) := by
  have hfin := support_finite hC F hF θ hθ S (tsupport G) hGc (fun v => tsupport (g v))
    (fun v hv => (hgS v hv).2) δ hδ
  have hnn : ∀ β : {β : F // β ≠ 0},
      0 ≤ G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1) := by
    intro β
    refine mul_nonneg (hG0 _) ?_
    refine ge_of_tendsto' (GlobalTheory.T.multipliable_local_factors F S C g hb2 β.1 β.2).hasProd fun U => ?_
    exact Finset.prod_nonneg fun v _ => hg0 v _
  have hsum : Summable fun β : {β : F // β ≠ 0} =>
      G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1) := by
    refine summable_of_ne_finset_zero (s := hfin.toFinset.subtype (fun x => x ≠ 0)) ?_
    intro b hb
    have hb' : b.1 ∉ hfin.toFinset := by simpa [Finset.mem_subtype] using hb
    by_cases h1 : θ δ * algebraMap F (Ainf F) b.1 ∈ tsupport G
    · obtain ⟨v, hv, -⟩ := exists_zero_place (x := b.1) S g hz fun h2 =>
        hb' ((hfin.mem_toFinset).2 ⟨b.2, h2.1, h1, h2.2⟩)
      rw [tprod_of_exists_eq_zero (f := fun v => g v (algebraMap F (Fv F v) b.1)) ⟨v, hv⟩, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  unfold fullSum
  rw [ENNReal.ofReal_mul (pow_nonneg hδ.le _), ENNReal.ofReal_tsum_of_nonneg hnn hsum]
end GlobalTheory.CompanionTheory.Mass.MeanV
