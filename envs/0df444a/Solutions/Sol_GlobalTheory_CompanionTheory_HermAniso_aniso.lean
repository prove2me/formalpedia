-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermAniso.aniso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:44.185027+00:00
-- url     : https://prove2.me/submissions/fc8b97d0-3e6b-4036-b00e-7b642c821d72

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_norm_q_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_pair_le
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_exists_ball
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_coord_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermAniso
namespace GlobalTheory.CompanionTheory.HermAniso
theorem _root_.solution : StHensel → StSandwich → StAniso := by
  intro hH hS
  unfold StAniso ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh hani Λ hΛ x
  have h1 := hh.2.2.1
  have hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1 :=
    fun x y hx hy => pair_le hH hs hh hani hx hy
  obtain ⟨V₀, hV₀⟩ := exists_ball hs hh hp
  have hsmul : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ V₀, a • x ∈ V₀ := by
    intro a ha x hx
    rw [hV₀] at hx ⊢
    rw [norm_q_smul hs hh]
    have := norm_nonneg a
    have h2 := norm_nonneg (h x x)
    calc ‖a‖ * ‖a‖ * ‖h x x‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hδle : ∀ x ∈ V₀, ∀ y ∈ V₀, ‖h x y‖ ≤ ‖δ‖ := by
    intro x hx y hy
    refine (hδ.2.1 (h x y)).mp fun a ha => ?_
    have hay := hsmul a ha y hy
    have := hp x (a • y) ((hV₀ x).mp hx) ((hV₀ _).mp hay)
    rw [h1 x (a • y), hh.2.1] at this
    rwa [mul_comm]
  have hle : Λ ≤ V₀ := fun y hy => (hV₀ y).mpr (hΛ.2.1 y hy)
  obtain ⟨m, b, hb⟩ := hΛ.1
  have hbΛ : ∀ j, b j ∈ Λ := by
    intro j
    rw [hb]
    intro i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  obtain ⟨M, hM⟩ := coord_comb hh b
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ V₀, ∀ i, ‖b.repr x i‖ ≤ C := by
    refine ⟨∑ i, ∑ j, ‖M i j‖ * ‖δ‖ + 1, ?_, fun x hx i => ?_⟩
    · have : 0 ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖ :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
      linarith
    · have e1 : ‖b.repr x i‖ ≤ ∑ j, ‖M i j‖ * ‖δ‖ := by
        rw [hM]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hδle _ (hle (hbΛ j)) x hx) (norm_nonneg _)
      have e2 : ∑ j, ‖M i j‖ * ‖δ‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ * ‖δ‖)
          (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)
      linarith
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt L (inv_pos.mpr hC0)
  have hcne : c ≠ 0 := norm_pos_iff.mp hc0
  have hbound : ∀ x ∈ V₀, c • x ∈ Λ := by
    intro x hx
    rw [hb]
    intro i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
    have e := hC x hx i
    have e2 : ‖c‖ * C ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hc1.le hC0.le
      rwa [inv_mul_cancel₀ hC0.ne'] at this
    calc ‖c‖ * ‖b.repr x i‖ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left e hc0.le
      _ ≤ 1 := e2
  have hab : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ V₀ := by
    intro x
    have hpos : (0 : ℝ) < (1 + ‖h x x‖)⁻¹ := by positivity
    obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt L hpos
    refine ⟨a, norm_pos_iff.mp ha0, ?_⟩
    rw [hV₀, norm_q_smul hs hh]
    have hq := norm_nonneg (h x x)
    have e1 : ‖a‖ * (1 + ‖h x x‖) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ha1.le (by positivity : (0 : ℝ) ≤ 1 + ‖h x x‖)
      rwa [inv_mul_cancel₀ (by positivity)] at this
    have e2 : ‖a‖ ≤ 1 := by nlinarith
    have e3 : ‖a‖ * ‖h x x‖ ≤ 1 := by nlinarith
    calc ‖a‖ * ‖a‖ * ‖h x x‖ = ‖a‖ * (‖a‖ * ‖h x x‖) := by ring
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hlat : IsLat L V₀ :=
    hS L V Λ V₀ c ⟨m, b, hb⟩ hcne hbound hab hsmul
  have heq : V₀ = Λ := hΛ.2.2 V₀ hlat (fun x hx => (hV₀ x).mp hx) hle
  rw [← heq]
  exact hV₀ x
end GlobalTheory.CompanionTheory.HermAniso
