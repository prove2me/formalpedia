-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SplitExtLat.exists_haar_fundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:02.154287+00:00
-- url     : https://prove2.me/submissions/29e6649d-2c8f-4769-902b-9726e4a4b2b4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainSplitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModularCharacterTrivialFiniteCovolumeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicHaarDecompositionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicQuotientMeasureStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainVolumeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicIntegralUnfoldingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLeviIntegralFormulaStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitExtensionFundamentalDomain
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_splitHomeo_apply
import Theorems.Thm_GlobalTheory_T_modular_character_trivial_finite_covolume
import Theorems.Thm_GlobalTheory_T_parabolic_fundamental_domain_split
import Theorems.Thm_GlobalTheory_T_parabolic_fundamental_domain_volume
import Theorems.Thm_GlobalTheory_T_parabolic_haar_decomposition
import Theorems.Thm_GlobalTheory_T_parabolic_integral_unfolding
import Theorems.Thm_GlobalTheory_T_parabolic_levi_integral_formula
import Theorems.Thm_GlobalTheory_T_parabolic_quotient_measure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply



set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitExtLat
namespace GlobalTheory.CompanionTheory.SplitExtLat
theorem _root_.solution : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁), Continuous ι → Continuous π → (∀ u, π (ι u) = u) → ∀ (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ u ∈ Γ₁, ι u ∈ Γ) → (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ (ν : Measure π.ker) (𝓕N : Set π.ker) (μP : Measure P) (𝓕P : Set P), ν.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf π.ker) 𝓕N ν ∧ ν 𝓕N ≠ 0 ∧ ν 𝓕N < ⊤ ∧ μP.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕P μP ∧ μP 𝓕P < ⊤ ∧ ∀ f : P → ℝ≥0∞, Measurable f → ∫⁻ p in 𝓕P, f p ∂μP = ∫⁻ u in 𝓕₁, ∫⁻ m in 𝓕N, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hU hΓ₁ hΓ μ₁ _ 𝓕₁ h𝓕₁ hfin hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by ext; simp [MonoidHom.mem_ker]
    rw [this]; exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨D, hDm, hDu, hD⟩ := GlobalTheory.T.parabolic_fundamental_domain_split P G₁ ι π hι hπ hπι Γ hU hK
  let ν : Measure π.ker := Measure.haar
  obtain ⟨hνF, hν0, hνfin⟩ := hD ν
  obtain ⟨δ, hδm, hδΓ, hδ⟩ := GlobalTheory.T.parabolic_haar_decomposition P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν D hDm hνF hν0 hνfin
  have hδ1 := GlobalTheory.T.modular_character_trivial_finite_covolume G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin δ hδm hδΓ
  have hmap : ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = ν := by
    intro u; rw [hδ u, hδ1 u, one_smul]
  have hH := GlobalTheory.T.parabolic_quotient_measure P G₁ ι π hι hπ hπι ν μ₁ hmap
  obtain ⟨hnull, hint⟩ := GlobalTheory.T.parabolic_levi_integral_formula P G₁ ι π hι hπ hπι ν μ₁ D 𝓕₁ hDm h𝓕₁.nullMeasurableSet
  have hcov := GlobalTheory.T.parabolic_fundamental_domain_volume P G₁ ι π hι hπ hπι Γ Γ₁ hΓ₁ ν μ₁ D 𝓕₁ hDu h𝓕₁
  have hdis := GlobalTheory.T.parabolic_integral_unfolding P G₁ ι π hι hπ hπι Γ Γ₁ hΓ ν μ₁ D 𝓕₁ hDu h𝓕₁
  refine ⟨ν, D, _, _, inferInstance, hνF, hν0, hνfin, hH,
    IsFundamentalDomain.mk'' hnull hcov hdis (fun γ => (measurePreserving_smul γ _).quasiMeasurePreserving), ?_, hint⟩
  have h1 := hint (fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, setLIntegral_one] at h1
  rw [h1]
  exact ENNReal.mul_lt_top hνfin hfin
end GlobalTheory.CompanionTheory.SplitExtLat
