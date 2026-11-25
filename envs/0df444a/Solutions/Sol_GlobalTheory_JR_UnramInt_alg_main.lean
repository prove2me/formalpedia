-- Prove2me | solution 1 for GlobalTheory.JR.UnramInt.alg_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:56.968398+00:00
-- url     : https://prove2.me/submissions/5ce8e749-083d-4070-9a57-afef6775c499

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOne
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsNonarchimedeanLocalFieldSpectralNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RamificationIndexEqOneOfAdjoinRangeEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticUniformizerTraceNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpectralNormClosedBallIsOpenIsCompactNhdsBasisAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticExistsIntegersUniformiser
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NormSign_exists_valuativeRel_of_normed
import Theorems.Thm_GlobalTheory_T_exists_localField_structure_spectralNorm
import Theorems.Thm_GlobalTheory_T_ramificationIndex_eq_one_of_adjoin_range_eq_top_alt
import Theorems.Thm_GlobalTheory_T_unramified_quadratic_norm_trace_surjective
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_ord_algebraMap
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.UnramInt
open ValuativeRel GroundTheory.LocalField
namespace GlobalTheory.JR.UnramInt
theorem _root_.solution : ∀ (F E K L : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [LocallyCompactSpace F] [NontriviallyNormedField E] [NormedAlgebra F E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L]
    [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F K] [FiniteDimensional F E]
    [FiniteDimensional K L],
    (∀ y : E, ∃ x : F, ‖y‖ = ‖x‖) → Module.finrank K L = 2 →
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    ∃ (ϖ : Kˣ) (O : Subring L), (O : Set L) = {y | spectralNorm F L y ≤ 1} ∧
      (¬ ∃ y : L, Algebra.norm K y = (ϖ : K)) ∧ algebraMap K L (ϖ : K) ∈ O ∧
      (¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1) ∧
      (∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧
      (∀ s : K, algebraMap K L s ∈ O → ∃ z ∈ O, Algebra.trace K L z = s) ∧
      (∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, Algebra.norm K w = s) ∧
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ z ∈ O, spectralNorm F L (algebraMap K L ((ϖ : K) ^ n) * z) < r) ∧
      ∀ y : L, ∃ n : ℕ, algebraMap K L ((ϖ : K) ^ n) * y ∈ O := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hunr h2 hgen
  haveI : FiniteDimensional F L := Module.Finite.trans K L
  have nmulL : ∀ x y : L, spectralNorm F L (x * y) = spectralNorm F L x * spectralNorm F L y :=
    fun x y => map_mul (spectralMulAlgNorm F L) x y
  have npowK : ∀ (x : K) (n : ℕ), spectralNorm F K (x ^ n) = spectralNorm F K x ^ n :=
    fun x n => map_pow (spectralMulAlgNorm F K) x n
  have ntow : ∀ a : K, spectralNorm F L (algebraMap K L a) = spectralNorm F K a :=
    fun a => (spectralNorm.eq_of_tower a).symm
  obtain ⟨vF, hFloc, hFv⟩ := NormSign.exists_valuativeRel_of_normed F
  obtain ⟨vE, hEloc, hEv⟩ := NormSign.exists_valuativeRel_of_normed E
  obtain ⟨vK, tK, hKloc, hKv⟩ := GlobalTheory.T.exists_localField_structure_spectralNorm F K
  obtain ⟨vL, tL, hLloc, hLv⟩ := GlobalTheory.T.exists_localField_structure_spectralNorm F L
  haveI : ValuativeExtension F E := ⟨fun a b => by rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
  haveI : ValuativeExtension F K := ⟨fun a b => by
    rw [hKv, hFv, spectralNorm_extends, spectralNorm_extends]⟩
  haveI : ValuativeExtension K L := ⟨fun a b => by rw [hLv, hKv, ntow, ntow]⟩
  have heF : ramificationIndex F E = 1 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hunr (ϖ : E)
    have h1 : (ϖ : E) ≤ᵥ algebraMap F E x := by rw [hEv, norm_algebraMap', hx]
    have h2 : algebraMap F E x ≤ᵥ (ϖ : E) := by rw [hEv, norm_algebraMap', hx]
    have hv : valuation E (ϖ : E) = valuation E (algebraMap F E x) :=
      le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)
    have hord : ord (ϖ : E) = ord (algebraMap F E x) := by
      simp only [ord]
      rw [(normalizedValuation_eq_iff (K := E)).2 hv]
    rw [ord_uniformizer hϖ, ord_algebraMap] at hord
    have hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1 := ⟨ord x, hord⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd
  have heKL := GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt F E K L heF hgen
  obtain ⟨ϖ, hϖ0, hϖ1, hϖ1', hN, hunif, htr, hnrm⟩ := GlobalTheory.T.unramified_quadratic_norm_trace_surjective K L heKL h2
  have hleL : ∀ y : L, y ≤ᵥ 1 ↔ spectralNorm F L y ≤ 1 := fun y => by rw [hLv, spectralNorm_one]
  have hleK : ∀ s : K, s ≤ᵥ 1 ↔ spectralNorm F K s ≤ 1 := fun s => by rw [hKv, spectralNorm_one]
  have hgeK : ∀ s : K, (1 : K) ≤ᵥ s ↔ 1 ≤ spectralNorm F K s := fun s => by rw [hKv, spectralNorm_one]
  have hϖlt : spectralNorm F K ϖ < 1 := lt_of_not_ge fun h => hϖ1' ((hgeK ϖ).2 h)
  let O : Subring L :=
    { carrier := {y | spectralNorm F L y ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [nmulL]
        exact mul_le_one₀ ha (spectralNorm_nonneg _) hb
      one_mem' := by simp [spectralNorm_one]
      add_mem' := fun {a b} ha hb => (isNonarchimedean_spectralNorm a b).trans (max_le ha hb)
      zero_mem' := by simp [spectralNorm_zero]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rwa [spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic a)] }
  have hmem : ∀ y : L, y ∈ O ↔ y ≤ᵥ 1 := fun y => (hleL y).symm
  refine ⟨Units.mk0 ϖ hϖ0, O, rfl, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show spectralNorm F L _ ≤ 1
    rw [Units.val_mk0, ntow]
    exact hϖlt.le
  · rintro ⟨z, hz, hz1⟩
    have h := congrArg (spectralNorm F L) hz1
    rw [nmulL, spectralNorm_one, Units.val_mk0, ntow] at h
    have hz' : spectralNorm F L z ≤ 1 := hz
    have : spectralNorm F K ϖ * spectralNorm F L z < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (spectralNorm_nonneg _) hz') hϖlt
    linarith
  · intro y hy
    rcases hunif y ((hmem y).1 hy) with ⟨z, hz, hyz⟩ | ⟨z, hz, hyz⟩
    · exact Or.inl ⟨z, (hmem z).2 hz, by rw [Units.val_mk0]; exact hyz⟩
    · exact Or.inr ⟨z, (hmem z).2 hz, hyz⟩
  · intro s hs
    have hs' : s ≤ᵥ 1 := by
      rw [hleK, ← ntow]
      exact hs
    obtain ⟨z, hz, hzs⟩ := htr s hs'
    exact ⟨z, (hmem z).2 hz, hzs⟩
  · rintro s hs ⟨r, hr, hsr⟩
    have hs1 : spectralNorm F K s ≤ 1 := by rw [← ntow]; exact hs
    have hr1 : spectralNorm F L r ≤ 1 := hr
    have h := congrArg (spectralNorm F L) hsr
    rw [nmulL, spectralNorm_one, ntow] at h
    have hge : 1 ≤ spectralNorm F K s := by
      nlinarith [spectralNorm_nonneg (K := F) s, spectralNorm_nonneg (K := F) r]
    obtain ⟨w, hw, hws⟩ := hnrm s ((hleK s).2 hs1) ((hgeK s).2 hge)
    exact ⟨w, (hmem w).2 hw, hws⟩
  · intro r hr
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hϖlt
    refine ⟨n, fun z hz => ?_⟩
    have hz' : spectralNorm F L z ≤ 1 := hz
    rw [nmulL, ntow, Units.val_mk0, npowK]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg (spectralNorm_nonneg _) _) hz') hn
  · intro y
    by_cases hy : spectralNorm F L y ≤ 1
    · refine ⟨0, ?_⟩
      show spectralNorm F L _ ≤ 1
      simpa using hy
    · have hpos : 0 < spectralNorm F L y := lt_of_lt_of_le one_pos (le_of_not_ge hy)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hϖlt
      refine ⟨n, ?_⟩
      show spectralNorm F L _ ≤ 1
      rw [nmulL, ntow, Units.val_mk0, npowK]
      calc spectralNorm F K ϖ ^ n * spectralNorm F L y ≤ (spectralNorm F L y)⁻¹ * spectralNorm F L y :=
            mul_le_mul_of_nonneg_right hn.le (spectralNorm_nonneg _)
        _ = 1 := inv_mul_cancel₀ hpos.ne'
end GlobalTheory.JR.UnramInt
