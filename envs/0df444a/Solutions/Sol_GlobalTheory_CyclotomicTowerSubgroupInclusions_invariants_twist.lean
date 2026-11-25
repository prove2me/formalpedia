-- Prove2me | solution 1 for GlobalTheory.CyclotomicTowerSubgroupInclusions.invariants_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:56:06.615553+00:00
-- url     : https://prove2.me/submissions/58bc804b-9b06-41c6-835c-da0da446de60

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateInvariantsCyclotomicTwist
import Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified
import Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_Hinf_le_Gj
import Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_mem_inC_iff
import Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_algebraMap_mem_inC
import Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_act_fix
import Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_exists_scale
import Theorems.Thm_GlobalTheory_CycPerturb_act_fix
import Theorems.Thm_GlobalTheory_CycPerturb_mem_inC_iff
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Hinf_le_Gj
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_fix
import Theorems.Thm_GlobalTheory_T_cyclotomicCharacterPadic_basic_properties
import Theorems.Thm_GlobalTheory_T_cyclotomicTower_fixed_iff_mem_completedIntegers
import Theorems.Thm_GlobalTheory_T_cyclotomic_tower_generator_matrix_perturbation
import Theorems.Thm_GlobalTheory_T_exists_cyclotomicTowerLevelGenerator_properties
import Theorems.Thm_GlobalTheory_T_padic_norm_zpow_sub_one_padicValInt
import Theorems.Thm_GlobalTheory_T_tate_decomposition_completed_cyclotomic_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CyclotomicTowerSubgroupInclusions
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.CyclotomicTowerSubgroupInclusions
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ Gj K j, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC (Ks K j)) := by
  intro l _ act χ ha hχ K j hj i y hy
  obtain ⟨hnorm, -, hker⟩ := GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ
  obtain ⟨⟨g, hg⟩, -⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K j hj
  obtain ⟨hdec, hdir, -, hmul, hact, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K j hj.1
  obtain ⟨n, hn⟩ := exists_scale y
  have hl0 : (l : PadicComplex l) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  set z := (l : PadicComplex l) ^ n * y with hz
  have hzinv : ∀ σ ∈ Gj K j, chiC χ i σ * act σ z = z := by
    intro σ hσ
    rw [hz, map_mul, map_pow, map_natCast, mul_left_comm, hy σ hσ]
  have hzO : z ∈ Ohat K := by
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K z hn).mp fun h hh => ?_
    have h1 : χ h = 1 := (hker K h (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j (Hinf_le_Gj K j hh))).2.mp hh
    have h2 := hzinv h (Hinf_le_Gj K j hh)
    simpa [chiC, h1] using h2
  obtain ⟨a, haK, x, hx, hax⟩ := hdec z hzO
  set c := chiC χ i g with hc
  have hcK : c ∈ inC (Ks K j) := algebraMap_mem_inC _ _
  have hc1 : ‖c‖ = 1 := by
    rw [hc, chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]
  have hga : act g a = a := act_fix ha hg.1 haK.1
  have heq : c * (a + act g x) = a + x := by
    have := hzinv g hg.1
    rwa [hax, map_add, hga] at this
  have hX : x - c * act g x ∈ Xj K j :=
    (Xj K j).sub_mem hx (hmul c ⟨hcK, hc1.le⟩ _ (hact g (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j hg.1) x hx))
  have hK : (c - 1) * a ∈ inC (Ks K j) := by
    rw [mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.sub_mem _ hcK (Subfield.one_mem _)) haK.1
  have h0 : (c - 1) * a = 0 := hdir _ hK _ hX 0 (by linear_combination heq)
  have hrho : 0 < rho1 l :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
  have hx0 : x = 0 := by
    have h := (GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation l act χ ha hχ K j hj g hg 1 (fun _ => 1) (by
      intro a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      refine ⟨?_, by simp⟩
      rw [mem_inC_iff]
      exact Subfield.one_mem _) (by intro a b; simpa using hrho) i).1 (fun _ => x) (fun _ => hx) (by
      funext b
      simp only [twAct, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
      linear_combination heq - h0)
    exact congrFun h 0
  rw [hx0, add_zero] at hax
  refine ⟨fun hi => ?_, fun _ => ?_⟩
  · have hv := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj (χ g : ℚ_[l]) hg.2 i hi
    have hne : c - 1 ≠ 0 := by
      intro h
      have h2 : c - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
        rw [hc, chiC, Units.val_zpow_eq_zpow_val, map_sub, map_one]
      rw [h2, map_eq_zero] at h
      rw [h, norm_zero] at hv
      exact (zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos : (0 : ℝ) < l) _).ne hv
    have ha0 : a = 0 := (mul_eq_zero.mp h0).resolve_left hne
    rw [ha0, hz] at hax
    exact (mul_eq_zero.mp hax).resolve_left hl0
  · have : y = ((l : PadicComplex l) ^ n)⁻¹ * a := by
      rw [← hax, hz, inv_mul_cancel_left₀ hl0]
    rw [this, mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (natCast_mem _ l) n)) haK.1
end GlobalTheory.CyclotomicTowerSubgroupInclusions
