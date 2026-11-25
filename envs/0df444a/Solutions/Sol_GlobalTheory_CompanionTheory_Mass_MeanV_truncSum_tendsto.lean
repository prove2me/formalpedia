-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.truncSum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:58:31.838364+00:00
-- url     : https://prove2.me/submissions/f5f88c44-88f1-4dd5-8371-7fd3e7d4f225

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tendsto_of_sandwich
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_exists_small
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_truncTerm_summable
import Theorems.Thm_GlobalTheory_T_adelic_sandwich_approximation
import Theorems.Thm_GlobalTheory_T_local_factor_sandwich_approx
import Theorems.Thm_GlobalTheory_T_local_haar_measure_singleton
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
theorem _root_.solution (hE : Equi) (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hli : IsStdInf li) (hlam : ∀ v, IsStdV v (lam v))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (C : ℝ) (hG : Continuous G) (hGc : HasCompactSupport G) (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (hgo : ∀ v, v ∉ S → GoodFac v (lam v) C (g v)) (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : S ⊆ T) :
    Tendsto (truncSum θ G T g) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))) := by
  have hI : 0 ≤ ∫ y, G y ∂li := integral_nonneg hG0
  have hP : 0 ≤ ∏ v ∈ S, ∫ s, g v s ∂(lam v) := Finset.prod_nonneg fun v _ => integral_nonneg (hg0 v)
  refine tendsto_of_sandwich fun η hη => ?_
  obtain ⟨e, he, he1, hup, hlo⟩ := exists_small ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v)) (T \ S).card hη
  have hex : ∀ v, ∃ lo up : Fv F v → ℝ, (v ∈ S → lo = g v ∧ up = g v) ∧ (v ∉ S → Continuous lo ∧
      HasCompactSupport lo ∧ Continuous up ∧ HasCompactSupport up ∧ (∀ s, 0 ≤ lo s) ∧
      (∀ s, s ≠ 0 → lo s ≤ g v s ∧ g v s ≤ up s) ∧ 1 - e ≤ ∫ s, lo s ∂(lam v) ∧ ∫ s, up s ∂(lam v) ≤ 1 + e) := by
    intro v
    by_cases hv : v ∈ S
    · exact ⟨g v, g v, fun _ => ⟨rfl, rfl⟩, fun h => absurd hv h⟩
    · obtain ⟨a, b, h⟩ := GlobalTheory.T.local_factor_sandwich_approx F v (lam v) C (g v) (hlam v) (hg0 v) (hgo v hv) e he
      exact ⟨a, b, fun h' => absurd h' hv, fun _ => h⟩
  choose lo up hS hO using hex
  have hcl : ∀ v ∈ T, Continuous (lo v) ∧ HasCompactSupport (lo v) := by
    intro v _
    by_cases hv : v ∈ S
    · rw [(hS v hv).1]; exact hgS v hv
    · exact ⟨(hO v hv).1, (hO v hv).2.1⟩
  have hcu : ∀ v ∈ T, Continuous (up v) ∧ HasCompactSupport (up v) := by
    intro v _
    by_cases hv : v ∈ S
    · rw [(hS v hv).2]; exact hgS v hv
    · exact ⟨(hO v hv).2.2.1, (hO v hv).2.2.2.1⟩
  have hpt : ∀ v (s : Fv F v), s ≠ 0 → 0 ≤ lo v s ∧ lo v s ≤ g v s ∧ g v s ≤ up v s := by
    intro v s hs
    by_cases hv : v ∈ S
    · rw [(hS v hv).1, (hS v hv).2]; exact ⟨hg0 v s, le_rfl, le_rfl⟩
    · have h := hO v hv
      exact ⟨h.2.2.2.2.1 s, (h.2.2.2.2.2.1 s hs).1, (h.2.2.2.2.2.1 s hs).2⟩
  have hemb : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F), x ≠ 0 → algebraMap F (Fv F v) x ≠ 0 := by
    intro v x hx
    simpa using hx
  have hup0 : ∀ v, 0 ≤ ∫ s, up v s ∂(lam v) := by
    intro v
    refine integral_nonneg_of_ae ?_
    have h0 : ∀ᵐ s ∂(lam v), s ≠ (0 : Fv F v) := by
      rw [ae_iff]
      simpa using GlobalTheory.T.local_haar_measure_singleton F v (lam v) (hlam v)
    filter_upwards [h0] with s hs
    exact (hg0 v s).trans (hpt v s hs).2.2
  have hsplit : ∀ ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ,
      ∏ v ∈ T, ∫ s, ψ v s ∂(lam v) = (∏ v ∈ T \ S, ∫ s, ψ v s ∂(lam v)) * ∏ v ∈ S, ∫ s, ψ v s ∂(lam v) :=
    fun ψ => (Finset.prod_sdiff hT).symm
  have hSlo : ∏ v ∈ S, ∫ s, lo v s ∂(lam v) = ∏ v ∈ S, ∫ s, g v s ∂(lam v) :=
    Finset.prod_congr rfl fun v hv => by rw [(hS v hv).1]
  have hSup : ∏ v ∈ S, ∫ s, up v s ∂(lam v) = ∏ v ∈ S, ∫ s, g v s ∂(lam v) :=
    Finset.prod_congr rfl fun v hv => by rw [(hS v hv).2]
  have hlop : (1 - e) ^ (T \ S).card ≤ ∏ v ∈ T \ S, ∫ s, lo v s ∂(lam v) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by linarith)
      fun v hv => (hO v (Finset.mem_sdiff.1 hv).2).2.2.2.2.2.2.1
  have hupp : ∏ v ∈ T \ S, ∫ s, up v s ∂(lam v) ≤ (1 + e) ^ (T \ S).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun v _ => hup0 v)
      fun v hv => (hO v (Finset.mem_sdiff.1 hv).2).2.2.2.2.2.2.2
  refine ⟨truncSum θ G T lo, truncSum θ G T up, _, _,
    GlobalTheory.T.adelic_sandwich_approximation hE hC F hF θ hθ li lam hli hlam T G lo hG hGc hcl,
    GlobalTheory.T.adelic_sandwich_approximation hE hC F hF θ hθ li lam hli hlam T G up hG hGc hcu, ?_, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    have hsl := truncTerm_summable hC F hF θ hθ T G lo hGc (fun v hv => (hcl v hv).2) δ hδ0
    have hsu := truncTerm_summable hC F hF θ hθ T G up hGc (fun v hv => (hcu v hv).2) δ hδ0
    have hterm : ∀ β : {β : F // β ≠ 0},
        0 ≤ (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) β.1 := by
      intro β
      refine Set.indicator_nonneg (fun x _ => mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => hg0 v _)) _
    have hl : ∀ β : {β : F // β ≠ 0},
        (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, lo v (algebraMap F (Fv F v) x)) β.1 ≤
        (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) β.1 := by
      intro β
      by_cases hb : β.1 ∈ IntOut T
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _ => (hpt v _ (hemb v _ β.2)).1)
          fun v _ => (hpt v _ (hemb v _ β.2)).2.1) (hG0 _)
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    have hu : ∀ β : {β : F // β ≠ 0},
        (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) β.1 ≤
        (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, up v (algebraMap F (Fv F v) x)) β.1 := by
      intro β
      by_cases hb : β.1 ∈ IntOut T
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _ => hg0 v _)
          fun v _ => (hpt v _ (hemb v _ β.2)).2.2) (hG0 _)
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    have hsg := Summable.of_nonneg_of_le hterm hu hsu
    have hpow : 0 ≤ δ ^ Module.finrank ℚ F := pow_nonneg hδ0.le _
    exact ⟨mul_le_mul_of_nonneg_left (hsl.tsum_le_tsum hl hsg) hpow,
      mul_le_mul_of_nonneg_left (hsg.tsum_le_tsum hu hsu) hpow⟩
  · rw [hsplit lo, hSlo]
    refine hlo.trans ?_
    have h2 := mul_le_mul_of_nonneg_left hlop (mul_nonneg hI hP)
    nlinarith [h2]
  · rw [hsplit up, hSup]
    refine le_trans ?_ hup
    have h2 := mul_le_mul_of_nonneg_left hupp (mul_nonneg hI hP)
    nlinarith [h2]
end GlobalTheory.CompanionTheory.Mass.MeanV
