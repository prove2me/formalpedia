-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:00:55.011435+00:00
-- url     : https://prove2.me/submissions/5e5d9199-c45d-4eb7-84f8-c4c86d05efe8

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimit
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tsum_unitVec_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tsum_eq_zero_add_of_finset
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_integral_unitVec_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_truncTerm_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFv_isLocR_Fv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_isLocR_Ainf
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
theorem _root_.solution : Equi → CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ T, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) →
    Tendsto (truncSum θ G T ψ) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ T, ∫ s, ψ v s ∂(lam v))) := by
  intro hE hC F _ _ hF θ hθ li lam hli hlam T G ψ hG hGc hψ
  have hlocI : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : LocallyCompactSpace (Ainf F) := hlocI.2.1
  have : SecondCountableTopology (Ainf F) := hlocI.2.2.1
  have := hli.1
  have : SigmaFinite li := inferInstance
  have hsf : ∀ v, SigmaFinite (lam v) := fun v => by
    have hloc : IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    have : LocallyCompactSpace (Fv F v) := hloc.2.1
    have : SecondCountableTopology (Fv F v) := hloc.2.2.1
    have := (hlam v).1
    infer_instance
  have key := hE F hF θ hθ li lam hli hlam Unit T (fun y => G (y ())) (fun v y => ψ v (y ()))
    (hG.comp (continuous_apply ())) (hGc.comp_homeomorph (Homeomorph.funUnique Unit (Ainf F)))
    (fun v hv => ⟨(hψ v hv).1.comp (continuous_apply ()),
      (hψ v hv).2.comp_homeomorph (Homeomorph.funUnique Unit (Fv F v))⟩)
  rw [integral_unitVec_eq li G,
    Finset.prod_congr rfl (fun v _ => haveI := hsf v; integral_unitVec_eq (lam v) (ψ v))] at key
  simp only [Fintype.card_unit, mul_one] at key
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hpow : Tendsto (fun ε : ℝ => ε ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0)) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ Module.finrank ℚ F * (G 0 * ∏ v ∈ T, ψ v 0))) :=
      ((continuous_pow _).mul continuous_const).tendsto 0
    rw [zero_pow hd.ne', zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hsub := key.sub hpow
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨B, hB, hh⟩ := truncTerm_finite hC F hF θ hθ T G ψ hGc (fun v hv => (hψ v hv).2) ε hε
  have h0mem : (0 : F) ∈ IntOut T := fun v _ => by
    rw [map_zero]
    exact zero_mem _
  have e := (tsum_unitVec_eq T (fun x => G (θ ε * algebraMap F (Ainf F) x) *
    ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x))).trans (tsum_eq_zero_add_of_finset _ B hB hh)
  rw [Set.indicator_of_mem h0mem] at e
  rw [e]
  simp only [truncSum, map_zero, mul_zero]
  ring
end GlobalTheory.CompanionTheory.Mass.MeanV
