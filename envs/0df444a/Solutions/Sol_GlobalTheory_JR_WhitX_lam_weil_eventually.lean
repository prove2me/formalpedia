-- Prove2me | solution 1 for GlobalTheory.JR.WhitX.lam_weil_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:01.542461+00:00
-- url     : https://prove2.me/submissions/f4088ad8-6687-4c2c-a9dc-b1da14a1e7d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralPsiKOverScaledIntegersEqVolumeIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ScaledIntegersKAnnihilatorSmallNearZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOpenCompactAnnihilatorScaledIntegersKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleExistsSqRootNearOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsOneEtaleAlgebraMulInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedSetEmptyOutsideNormCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleHermitianPairNormPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScalingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedIntegralEqVolMulOrbitalIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerWeilRepEventually
import Theorems.Thm_GlobalTheory_JR_WhitX_u_formula
import Theorems.Thm_GlobalTheory_JR_WhitX_M_sub
import Theorems.Thm_GlobalTheory_T_absK_multiplicative_unitOne_haarScaling
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_exists_nhds_one_etaleAlgebra_mul_invariant
import Theorems.Thm_GlobalTheory_T_exists_openCompact_annihilator_scaled_integersK
import Theorems.Thm_GlobalTheory_T_finiteEtaleHermitianPair_norm_properties
import Theorems.Thm_GlobalTheory_T_finiteEtale_exists_sq_root_near_one
import Theorems.Thm_GlobalTheory_T_integral_psiK_over_scaled_integers_eq_volume_indicator
import Theorems.Thm_GlobalTheory_T_scaledIntegersK_annihilator_small_near_zero
import Theorems.Thm_GlobalTheory_T_selfDual_iff_lattice_volume_and_plancherel_alt
import Theorems.Thm_GlobalTheory_T_setIntegral_integral_psiK_swap
import Theorems.Thm_GlobalTheory_T_truncatedIntegral_eq_vol_mul_orbitalIntegral
import Theorems.Thm_GlobalTheory_T_truncated_set_empty_outside_norm_coset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WhitX
namespace GlobalTheory.JR.WhitX
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (γ : ℂ) W, A.IsWeil ψ x A.etaK (m.μL x) γ W → ∀ φ, IsTest φ → ∀ a : A.K, IsUnit a → (∀ y : A.L, IsUnit y → a = x * A.NL y → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = γ * A.orbL m.ν φ y) ∧ ((¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = 0) := by
  intro F E _ _ _ _ _ A ψ hψ m x γ W hW φ hφ a ha
  haveI := m.sdK.1
  haveI := (m.sdL x).1
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOo, -, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have key : ∀ c : F, c ≠ 0 → A.abelian₂ m.μK ψ a (fun g => W g φ 0) c =
      γ * ((m.μK {z | c • z ∈ A.OK}).toReal : ℂ) *
        ∫ y, φ y * Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => (1 : ℂ))
          ((x : A.K) * A.NL y - a) ∂(m.μL x) := by
    intro c hc
    unfold Et.abelian₂
    simp_rw [u_formula F E A ψ x A.etaK (m.μL x) γ W hW φ hφ, mul_assoc γ]
    rw [integral_const_mul, GlobalTheory.T.setIntegral_integral_psiK_swap F E A ψ hψ m.μK inferInstance (m.μL x) inferInstance φ hφ x a c hc]
    simp_rw [GlobalTheory.T.integral_psiK_over_scaled_integers_eq_volume_indicator F E A ψ hψ m.μK inferInstance c hc]
    congr 1
    rw [← integral_const_mul]
    congr 1; funext y
    simp only [Set.indicator]
    split_ifs <;> ring
  obtain ⟨U1, hU1, hinv⟩ := GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant F E A φ hφ
  have hOK1 : A.OK ∈ 𝓝 (1 : A.K) := hOo.mem_nhds (by rw [← hR]; exact R.one_mem)
  have hsq := GlobalTheory.T.finiteEtale_exists_sq_root_near_one F E A (U1 ∩ A.OK) (inter_mem hU1 hOK1)
  have hcont : Tendsto (fun b : A.K => 1 + Ring.inverse a * b) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun b : A.K => 1 + Ring.inverse a * b) := by fun_prop
    simpa using this.tendsto 0
  have hU : {b : A.K | ∃ s ∈ U1 ∩ A.OK, ∃ s' ∈ U1 ∩ A.OK, s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse a * b} ∈ 𝓝 (0 : A.K) :=
    hcont hsq
  have hev := GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero F E A ψ hψ _ hU
  have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
  constructor
  · intro y hy hay
    filter_upwards [hev, hne] with c hc hc0
    rw [key c hc0]
    obtain ⟨D, hDset, hDo, hDc⟩ := GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK F E A ψ hψ c hc0
    obtain ⟨M, hMset, hMo, hMc⟩ := M_sub F E A c hc0
    have hMD : m.μK M * m.μK D = 1 := by
      have h := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd m.μK
        inferInstance).1 M hMo hMc).1
      have hk : A.kerK ψ = fun x y => ψ (Algebra.traceForm F A.K x y) := by
        funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]
      have hsd : SelfDual m.μK (fun x y => ψ (Algebra.traceForm F A.K x y)) := hk ▸ m.sdK
      have hDeq : (D : Set A.K) = {y | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} := by
        rw [hDset]; ext b; simp [← SetLike.mem_coe, hMset, Et.psiK, Algebra.traceForm_apply]
      rw [hDeq]; exact h.1 hsd
    rw [← hDset, ← hMset]
    subst hay
    rw [GlobalTheory.T.truncatedIntegral_eq_vol_mul_orbitalIntegral F E A (GlobalTheory.T.finiteEtaleHermitianPair_norm_properties F E A) (GlobalTheory.T.absK_multiplicative_unitOne_haarScaling F E A) ψ hψ m x y hy D hDo hDc φ hφ ?_]
    · have : (m.μK M).toReal * (m.μK D).toReal = 1 := by rw [← ENNReal.toReal_mul, hMD]; simp
      have : ((m.μK M).toReal : ℂ) * ((m.μK D).toReal : ℂ) = 1 := by exact_mod_cast this
      linear_combination (γ * A.orbL m.ν φ y) * this
    · intro b hb
      have hb' := hc b (by rw [← SetLike.mem_coe, hDset] at hb; exact hb)
      obtain ⟨s, ⟨hsU, hsO⟩, s', ⟨hsU', hsO'⟩, hss, hs2⟩ := hb'
      exact ⟨s, s', hsO, hsO', hss, hs2, hinv s hsU s' hsU' hss⟩
  · intro hno
    filter_upwards [hev, hne] with c hc hc0
    rw [key c hc0]
    have hz := GlobalTheory.T.truncated_set_empty_outside_norm_coset F E A (GlobalTheory.T.finiteEtaleHermitianPair_norm_properties F E A) x a {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
      (fun b hb => by
        obtain ⟨s, -, s', -, hss, hs2⟩ := hc b hb
        exact ⟨s, s', hss, hs2⟩) ha hno
    have : (fun y => φ y * Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
        (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - a)) = fun _ => 0 := by
      funext y; rw [Set.indicator_of_notMem (hz y)]; simp
    rw [this]; simp
end GlobalTheory.JR.WhitX
