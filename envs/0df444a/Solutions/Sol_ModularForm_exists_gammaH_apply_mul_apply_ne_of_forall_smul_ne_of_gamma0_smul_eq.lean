-- Prove2me | solution 1 for ModularForm.exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5bae12bb-8f58-5741-9309-7f6a19f5e2a2

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
import Theorems.Thm_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq
import Theorems.Thm_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq
import Theorems.Thm_PeriodPair_g2_ofTau_and_g3_ofTau
import Theorems.Thm_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane ModularForm P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq.ModularForm"
open scoped MatrixGroups Real

namespace ModularForm
p2m_export "ModularForm" "SL_slash_apply translate coe_mul holo' discriminant_eq_E₄_cube_sub_E₆_sq SL_slash ext bdd_at_cusps' E₄ mcast E₆ discriminant_ne_zero coe_mcast mul exists_gamma1_coe_eq_pow_of_forall_slash_eq exists_gammaH_coe_eq_sum_of_forall_slash_eq"
namespace GammaHDiamondSeparation
p2m_open "ModularForm"

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k) (h : Γ' ≤ Γ) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := by
    simpa using f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[scoped simp] lemma restrict_apply {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k)
    (h : Γ' ≤ Γ) (τ : ℍ) : restrict f h τ = f τ := rfl

def mpow {k : ℤ} (f : ModularForm 𝒮ℒ k) : (n : ℕ) → ModularForm 𝒮ℒ ((n : ℤ) * k)
  | 0 => (1 : ModularForm 𝒮ℒ 0).mcast (by simp)
  | (n + 1) => ((mpow f n).mul f).mcast (by push_cast; ring)

@[scoped simp] lemma coe_mpow {k : ℤ} (f : ModularForm 𝒮ℒ k) (n : ℕ) : ⇑(mpow f n) = (⇑f) ^ n := by
  induction n with
  | zero =>
    ext τ
    simp [mpow]
  | succ n ih =>
    ext τ
    change ((mpow f n).mul f) τ = ((⇑f) ^ (n + 1)) τ
    simp [ModularForm.coe_mul, ih, pow_succ]

theorem E₄_cube_sub_E₆_sq_ne_zero (z : ℍ) : E₄ z ^ 3 - E₆ z ^ 2 ≠ 0 := fun h0 => by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [h0, zero_div] at h
  exact ModularForm.discriminant_ne_zero z h

theorem eq_of_sq_eq_of_cube_eq {x y : ℂ} (h2 : x ^ 2 = y ^ 2) (h3 : x ^ 3 = y ^ 3) : x = y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact h
  · rw [h] at h3 ⊢
    have hy : y ^ 3 = 0 := by linear_combination (-1 / 2 : ℂ) * h3
    have : y = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 hy
    simp [this]

end ModularForm.GammaHDiamondSeparation
p2m_reactivate "P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq.ModularForm P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq.ModularForm.GammaHDiamondSeparation"
p2m_reactivate "P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq.ModularForm"

open ModularForm.GammaHDiamondSeparation in
theorem solution (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) (τ τ' : ℍ)
    (hτ : ∀ γ ∈ CohCarrier.GammaH N H, γ • τ ≠ τ')
    (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ CongruenceSubgroup.Gamma0 N) (hτ' : γ₀ • τ = τ') :
    ∃ (k : ℤ) (g h : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k),
      (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' ≠ (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ := by
  classical
  subst hτ'
  by_contra hcon
  push Not at hcon
  letI : Fintype H := Fintype.ofFinite H

  have hle : ((CohCarrier.GammaH N H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
    Subgroup.map_le_range _ _
  have hγ₀SL : (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ₀))
      ∈ 𝒮ℒ := ⟨γ₀, rfl⟩

  set D : ℂ := denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ₀)) (τ : ℂ) with hD
  have hD0 : D ≠ 0 := denom_ne_zero _ _

  have step : ∀ (k : ℤ) (g : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k)
      (A : ModularForm 𝒮ℒ k) (y : ℂ), g (γ₀ • τ) = D ^ k * y → A τ ≠ 0 → g τ = y := by
    intro k g A y hg hA
    have h1 := hcon k g (restrict A hle)
    simp only [restrict_apply] at h1
    have hAsl : (⇑A : ℍ → ℂ) ∣[k] γ₀ = ⇑A := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq A _ hγ₀SL
    have hAγ : A (γ₀ • τ) = D ^ k * A τ := by
      have h2 := congrFun hAsl τ
      rw [ModularForm.SL_slash_apply, ← hD, _root_.zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero k hD0)] at h2
      rw [h2]; ring
    rw [hAγ, hg] at h1
    have h3 : (g τ - y) * (D ^ k * A τ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (mul_ne_zero (zpow_ne_zero _ hD0) hA)

  obtain ⟨W, hWval, hWslash, -⟩ :=
    PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff N
  have hWv : ∀ (t : ZMod N) (z : ℍ), W t z =
      12 * ((2 * π * Complex.I) ^ 2)⁻¹ * (PeriodPair.ofTau z).weierstrassP ((t.val : ℂ) / N) :=
    hWval (fun z => PeriodPair.ofTau z) (fun z => ⟨PeriodPair.ofTau_ω₁ z, PeriodPair.ofTau_ω₂ z⟩)
  set c : ℂ := 12 * ((2 * π * Complex.I) ^ 2)⁻¹ with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine mul_ne_zero (by norm_num) (inv_ne_zero (pow_ne_zero _ ?_))
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

  set x : ℕ → ℂ := fun i => ∑ h : H, (W ((h : (ZMod N)ˣ) : ZMod N) τ) ^ i with hx
  set y : ℕ → ℂ := fun i => ∑ h : H, (W (((γ₀ 1 1 : ℤ) : ZMod N) * ((h : (ZMod N)ˣ) : ZMod N)) τ) ^ i with hy
  have forms : ∀ i : ℕ, ∃ g : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) ((i : ℤ) * 2),
      g τ = x i ∧ g (γ₀ • τ) = D ^ ((i : ℤ) * 2) * y i := by
    intro i
    obtain ⟨P, hPval, hPslash⟩ :=
      ModularForm.exists_gamma1_coe_eq_pow_of_forall_slash_eq N 2 i W hWslash
    obtain ⟨V, hVval, hVslash⟩ :=
      ModularForm.exists_gammaH_coe_eq_sum_of_forall_slash_eq N H ((i : ℤ) * 2) P hPslash
    refine ⟨V 1, ?_, ?_⟩
    · have hv := congrFun (hVval 1) τ
      simp only [Finset.sum_apply, one_mul, hPval, Pi.pow_apply] at hv
      rw [hv]
    · have hs := congrFun (hVslash 1 γ₀ hγ₀) τ
      rw [ModularForm.SL_slash_apply, ← hD, one_mul, _root_.zpow_neg,
        mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hD0)] at hs
      have hv := congrFun (hVval ((γ₀ 1 1 : ℤ) : ZMod N)) τ
      simp only [Finset.sum_apply, hPval, Pi.pow_apply] at hv
      rw [hs, hv, hy]
      ring
  have key : ∀ (i : ℕ) (A : ModularForm 𝒮ℒ ((i : ℤ) * 2)), A τ ≠ 0 → x i = y i := by
    intro i A hA
    obtain ⟨g, hg1, hg2⟩ := forms i
    rw [← hg1]
    exact step _ g A _ hg2 hA

  have anchor : ∀ (a b i : ℕ), 2 * a + 3 * b = i → (E₄ τ ≠ 0 ∨ a = 0) → (E₆ τ ≠ 0 ∨ b = 0) →
      ∃ A : ModularForm 𝒮ℒ ((i : ℤ) * 2), A τ ≠ 0 := by
    intro a b i hi h4 h6
    refine ⟨((mpow E₄ a).mul (mpow E₆ b)).mcast (by rw [← hi]; push_cast; ring), ?_⟩
    simp only [ModularForm.coe_mcast, ModularForm.coe_mul, Pi.mul_apply, coe_mpow, Pi.pow_apply]
    refine mul_ne_zero ?_ ?_
    · rcases h4 with h | rfl
      · exact pow_ne_zero _ h
      · simp
    · rcases h6 with h | rfl
      · exact pow_ne_zero _ h
      · simp
  have hE := E₄_cube_sub_E₆_sq_ne_zero τ

  have hxP : ∀ i, x i = c ^ i * ∑ h : H,
      (PeriodPair.ofTau τ).weierstrassP ((((h : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^ i := by
    intro i
    rw [hx]
    simp only [hWv, mul_pow, Finset.mul_sum]
  have hyP : ∀ i, y i = c ^ i * ∑ h : H, (PeriodPair.ofTau τ).weierstrassP
      ((((CohCarrier.gamma0Units N ⟨γ₀, hγ₀⟩ * (h : (ZMod N)ˣ) : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^ i := by
    intro i
    rw [hy]
    simp only [hWv, mul_pow, Finset.mul_sum, Units.val_mul]
    rfl
  have keyP : ∀ (i : ℕ) (A : ModularForm 𝒮ℒ ((i : ℤ) * 2)), A τ ≠ 0 →
      ∑ h : H, (PeriodPair.ofTau τ).weierstrassP ((((h : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^ i =
      ∑ h : H, (PeriodPair.ofTau τ).weierstrassP
        ((((CohCarrier.gamma0Units N ⟨γ₀, hγ₀⟩ * (h : (ZMod N)ˣ) : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^ i := by
    intro i A hA
    apply mul_left_cancel₀ (pow_ne_zero i hc0)
    rw [← hxP, ← hyP]
    exact key i A hA

  obtain ⟨hg2, hg3⟩ := PeriodPair.g2_ofTau_and_g3_ofTau τ
  by_cases h6 : E₆ τ = 0
  ·
    have h4 : E₄ τ ≠ 0 := fun h4 => hE (by rw [h4, h6]; ring)
    have hg3' : (PeriodPair.ofTau τ).g₃ = 0 := by rw [hg3, h6, mul_zero]
    obtain ⟨γ, hγ, hγτ⟩ :=
      CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq N H τ γ₀ hγ₀ 2
        (Or.inr (Or.inl ⟨rfl, hg3'⟩)) (fun j _ => by
          obtain ⟨A, hA⟩ := anchor j 0 (2 * j) (by ring) (Or.inl h4) (Or.inr rfl)
          exact keyP (2 * j) A hA)
    exact hτ γ hγ hγτ
  · by_cases h4 : E₄ τ = 0
    ·
      have hg2' : (PeriodPair.ofTau τ).g₂ = 0 := by rw [hg2, h4, mul_zero]
      obtain ⟨γ, hγ, hγτ⟩ :=
        CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq N H τ γ₀ hγ₀ 3
          (Or.inr (Or.inr ⟨rfl, hg2'⟩)) (fun j _ => by
            obtain ⟨A, hA⟩ := anchor 0 j (3 * j) (by ring) (Or.inr rfl) (Or.inl h6)
            exact keyP (3 * j) A hA)
      exact hτ γ hγ hγτ
    ·
      have hx1 : x 1 = y 1 := by
        obtain ⟨g, hg1, hgγ⟩ := forms 1
        have hgγ' : g (γ₀ • τ) = D ^ (2 : ℕ) * y 1 := by
          rw [hgγ, show ((1 : ℕ) : ℤ) * 2 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        have hsq : ((g.mul g).mcast (by norm_num) :
            ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) 4) τ = (y 1) ^ 2 := by
          refine step 4 _ E₄ ((y 1) ^ 2) ?_ h4
          simp only [ModularForm.coe_mcast, ModularForm.coe_mul, Pi.mul_apply, hgγ']
          rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
          ring
        have hcu : (((g.mul g).mul g).mcast (by norm_num) :
            ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) 6) τ = (y 1) ^ 3 := by
          refine step 6 _ E₆ ((y 1) ^ 3) ?_ h6
          simp only [ModularForm.coe_mcast, ModularForm.coe_mul, Pi.mul_apply, hgγ']
          rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast]
          ring
        simp only [ModularForm.coe_mcast, ModularForm.coe_mul, Pi.mul_apply, hg1] at hsq hcu
        exact eq_of_sq_eq_of_cube_eq (by rw [← hsq]; ring) (by rw [← hcu]; ring)
      obtain ⟨γ, hγ, hγτ⟩ :=
        CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq N H τ γ₀ hγ₀ 1
          (Or.inl rfl) (fun j hj => by
            rw [one_mul]
            obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
            · obtain ⟨A, hA⟩ := anchor m 0 (2 * m) (by ring) (Or.inl h4) (Or.inl h6)
              exact keyP (2 * m) A hA
            · rcases Nat.eq_zero_or_pos m with rfl | hm
              ·
                apply mul_left_cancel₀ (pow_ne_zero 1 hc0)
                rw [← hxP, ← hyP]
                simpa using hx1
              · obtain ⟨A, hA⟩ := anchor (m - 1) 1 (2 * m + 1) (by omega) (Or.inl h4) (Or.inl h6)
                exact keyP (2 * m + 1) A hA)
      exact hτ γ hγ hγτ

end
end S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq
end P2MW
export P2MW.S_ModularForm_exists_gammaH_apply_mul_apply_ne_of_forall_smul_ne_of_gamma0_smul_eq (solution)
