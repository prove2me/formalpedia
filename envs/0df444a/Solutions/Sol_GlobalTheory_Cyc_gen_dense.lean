-- Prove2me | solution 1 for GlobalTheory.Cyc.gen_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:43.419852+00:00
-- url     : https://prove2.me/submissions/c721388f-83b8-4e55-af76-074179c3d868

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Theorems.Thm_GlobalTheory_Cyc_norm_pow_pow_sub_one
import Theorems.Thm_GlobalTheory_Cyc_exists_norm_sub_pow_le
import Theorems.Thm_GlobalTheory_Cyc_cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base
import Theorems.Thm_GlobalTheory_T_cyclotomicCharacterPadic_basic_properties
import Theorems.Thm_GlobalTheory_T_finrank_cyclotomicExt_and_cyclotomicChar_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → (∃ g, IsGen χ K j g) ∧ ∀ g, IsGen χ K j g → ((∀ b : ℕ, IsGen χ K (j + b) (g ^ (l ^ b))) ∧ (∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n) ∧ (Gj K j : Set (GQ l)) ⊆ closure {x | ∃ h ∈ Hinf K, ∃ a : ℕ, x = h * g ^ a}) := by
  intro l _ act χ _ hχ K j hj
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hn, hcont, hG⟩ := GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ
  refine ⟨?_, fun g hg => ?_⟩
  · have hp : ‖(l : ℚ_[l]) ^ j‖ = (l : ℝ) ^ (-(j : ℤ)) := by
      rw [norm_pow, Padic.norm_p]; simp
    have hlt : ‖(l : ℚ_[l]) ^ j‖ < 1 := by
      rw [hp]; apply zpow_lt_one_of_neg₀ hl1; have := hj.1; omega
    have hu : ‖(1 : ℚ_[l]) + (l : ℚ_[l]) ^ j‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'),
        norm_one, max_eq_left hlt.le]
    obtain ⟨g, hg0, hg⟩ := (GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective l K).2 χ hχ _ hu
    have : ‖(χ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by rw [hg, add_sub_cancel_left, hp]
    exact ⟨g, ((hG K g hg0).1 j).2 this.le, this⟩
  have hg0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K j hg.1
  have hcos : ∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n := by
    intro σ hσ n
    have hσ0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K j hσ
    obtain ⟨a, ha⟩ := exists_norm_sub_pow_le j hj _ _ (hn g) hg.2 (((hG K σ hσ0).1 j).1 hσ) n
    refine ⟨a, ((hG K _ (mul_mem hσ0 (inv_mem (pow_mem hg0 a)))).1 n).2 ?_⟩
    have h0 : (χ g : ℚ_[l]) ≠ 0 := Units.ne_zero _
    have h : ((χ (σ * (g ^ a)⁻¹) : ℚ_[l]ˣ) : ℚ_[l]) - 1
        = ((χ σ : ℚ_[l]) - (χ g : ℚ_[l]) ^ a) / (χ g : ℚ_[l]) ^ a := by
      simp only [map_mul, map_inv, map_pow, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val]
      field_simp
    rw [h, norm_div, norm_pow, hn, one_pow, div_one]
    refine ha.trans (zpow_le_zpow_right₀ hl1.le ?_)
    push_cast; omega
  refine ⟨fun b => ?_, hcos, fun σ hσ => ?_⟩
  · have : ‖(χ (g ^ (l ^ b)) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-((j + b : ℕ) : ℤ)) := by
      rw [map_pow, Units.val_pow_eq_pow_val]
      exact norm_pow_pow_sub_one j hj _ hg.2 b
    exact ⟨((hG K _ (pow_mem hg0 _)).1 _).2 this.le, this⟩
  · rw [mem_closure_iff]
    intro U hU hσU
    have hW : IsOpen (⋃ h ∈ Hinf K, {x : GQ l | h * x⁻¹ * σ ∈ U}) :=
      isOpen_biUnion fun h _ => hU.preimage (by fun_prop)
    have hcl : ∀ n : ℕ, IsClosed (Gj K n : Set (GQ l)) := fun n =>
      InfiniteGalois.fixingSubgroup_isClosed _
    have hanti : Antitone fun n : ℕ => (Gj K n : Set (GQ l)) := by
      intro m n hmn x hx
      have hx0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K n hx
      refine ((hG K x hx0).1 m).2 ((((hG K x hx0).1 n).1 hx).trans
        (zpow_le_zpow_right₀ hl1.le (by omega)))
    have hint : ∀ x ∈ ⋂ n : ℕ, (Gj K n : Set (GQ l)),
        (⋃ h ∈ Hinf K, {x : GQ l | h * x⁻¹ * σ ∈ U}) ∈ nhds x := by
      intro x hx
      rw [Set.mem_iInter] at hx
      have hx0 := cyclotomicTowerLevelGaloisSubgroup_le_fixingSubgroup_base K 0 (hx 0)
      have hxH : x ∈ Hinf K := by
        refine (hG K x hx0).2.2 (Units.ext ?_)
        rw [Units.val_one, ← sub_eq_zero, ← norm_le_zero_iff]
        by_contra hne
        obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one (not_le.1 hne) (inv_lt_one_of_one_lt₀ hl1)
        have := ((hG K x hx0).1 n).1 (hx n)
        rw [zpow_neg, zpow_natCast, ← inv_pow] at this
        linarith
      exact hW.mem_nhds (Set.mem_biUnion hxH (by simpa using hσU))
    obtain ⟨n, hn'⟩ := exists_subset_nhds_of_compactSpace hanti.directed_ge hcl
      hint
    obtain ⟨a, ha⟩ := hcos σ hσ n
    obtain ⟨h, hh, hU'⟩ := Set.mem_iUnion₂.1 (hn' ha)
    refine ⟨h * g ^ a, ?_, h, hh, a, rfl⟩
    simpa [mul_assoc] using hU'
end GlobalTheory.Cyc
