-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a4982a79-6cf5-5541-b3ec-4c4d9ec5ef74

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_FullLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma_of_dvd

set_option autoImplicit false

namespace C3KitH1

theorem natCard_closure_dvd {Γ M Q : Type*} [Group Γ] [Group M] [Group Q] [Finite Q]
    (S Δ₁ Δ₂ : Subgroup Γ) (hΔS : Δ₁ ⊓ Δ₂ ≤ S)
    (Att : Γ → M → Prop)
    (huniq : ∀ γ ∈ S, ∀ τ τ' : M, Att γ τ → Att γ τ' → τ = τ')
    (hmul : ∀ γ δ : Γ, γ ∈ S → δ ∈ S → ∀ τ σ : M, Att γ τ → Att δ σ → Att (δ * γ) (τ * σ))
    (hex : ∀ γ ∈ S, ∃ τ : M, Att γ τ)
    (ψ : ↥(Δ₁ ⊓ Δ₂) →* Q)
    (hker : ∀ γ : ↥(Δ₁ ⊓ Δ₂), ψ γ = 1 → Att ((γ : Γ)⁻¹) 1) :
    Nat.card ↥(Subgroup.closure {τ : M | ∃ γ : Γ, γ ∈ Δ₁ ∧ γ ∈ Δ₂ ∧ Att γ⁻¹ τ}) ∣ Nat.card Q := by
  classical

  have hexΔ : ∀ γ : ↥(Δ₁ ⊓ Δ₂), ∃ τ : M, Att ((γ : Γ)⁻¹) τ := fun γ => hex _ (S.inv_mem (hΔS γ.2))
  choose T hT using hexΔ
  have hSinv : ∀ γ : ↥(Δ₁ ⊓ Δ₂), ((γ : Γ)⁻¹) ∈ S := fun γ => S.inv_mem (hΔS γ.2)
  let Φ : ↥(Δ₁ ⊓ Δ₂) →* M :=
    { toFun := T
      map_one' := by
        have h1 : Att ((1 : ↥(Δ₁ ⊓ Δ₂)) : Γ)⁻¹ 1 := hker 1 (map_one ψ)
        exact huniq _ (hSinv 1) _ _ (hT 1) h1
      map_mul' := fun γ δ => by
        have h := hmul ((γ : Γ)⁻¹) ((δ : Γ)⁻¹) (hSinv γ) (hSinv δ) (T γ) (T δ) (hT γ) (hT δ)
        have e : ((δ : Γ)⁻¹ * (γ : Γ)⁻¹) = ((γ * δ : ↥(Δ₁ ⊓ Δ₂)) : Γ)⁻¹ := by
          rw [Subgroup.coe_mul, mul_inv_rev]
        rw [e] at h
        exact huniq _ (hSinv (γ * δ)) _ _ (hT (γ * δ)) h }
  have hΦ : ∀ γ, Φ γ = T γ := fun _ => rfl

  have hrange : Subgroup.closure {τ : M | ∃ γ : Γ, γ ∈ Δ₁ ∧ γ ∈ Δ₂ ∧ Att γ⁻¹ τ} = Φ.range := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro τ ⟨γ, h1, h2, hτ⟩
      refine ⟨⟨γ, Subgroup.mem_inf.mpr ⟨h1, h2⟩⟩, ?_⟩
      rw [hΦ]
      exact huniq _ (hSinv ⟨γ, _⟩) _ _ (hT _) hτ
    · rintro τ ⟨γ, rfl⟩
      apply Subgroup.subset_closure
      exact ⟨γ, (Subgroup.mem_inf.mp γ.2).1, (Subgroup.mem_inf.mp γ.2).2, by rw [hΦ]; exact hT γ⟩
  rw [hrange]

  have hkerle : ψ.ker ≤ Φ.ker := by
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ ⊢
    rw [hΦ]
    exact huniq _ (hSinv γ) _ _ (hT γ) (hker γ hγ)
  have h1 : Nat.card ↥Φ.range = Φ.ker.index := (Subgroup.index_ker Φ).symm
  have h2 : Φ.ker.index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hkerle
  have h3 : ψ.ker.index = Nat.card ↥ψ.range := Subgroup.index_ker ψ
  rw [h1]
  exact h2.trans (h3 ▸ Subgroup.card_subgroup_dvd_card ψ.range)

end C3KitH1

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (G : Subgroup (↥K ≃ₐ[L] ↥K))
    (hG : G = Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ}) :
    Finite ↥G ∧ Nat.card ↥G ∣ (ℓ - 1) := by
  classical
  haveI hqne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨huniq, hmul, htriv⟩ :=
    ModularCurve.FullLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L ζ hζ hι
      H₁ hH₁ K hK
  have hex := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM' ℓ hℓM' L ζ hζ
    H₁ hH₁ K hK
  set Att : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K) → Prop := fun γ τ =>
    ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ K τ with hAtt

  let Δ : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M'
  have hΔℓ : Δ ≤ CongruenceSubgroup.Gamma0 ℓ := by
    intro γ hγ
    have h := CongruenceSubgroup.Gamma0_mem.mp (Subgroup.mem_inf.mp hγ).2
    rw [CongruenceSubgroup.Gamma0_mem]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓM') h
  let ψ : ↥Δ →* (ZMod ℓ)ˣ := (CohCarrier.gamma0Units ℓ).comp (Subgroup.inclusion hΔℓ)
  have hψ : ∀ γ : ↥Δ, ((ψ γ : (ZMod ℓ)ˣ) : ZMod ℓ) = (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) := fun γ => by
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, CohCarrier.val_gamma0Units]
    rfl
  have hdvd : Nat.card ↥(Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧ Att γ⁻¹ τ}) ∣ Nat.card (ZMod ℓ)ˣ := by
    refine C3KitH1.natCard_closure_dvd (CongruenceSubgroup.Gamma0 M') (CongruenceSubgroup.Gamma q)
      (CongruenceSubgroup.Gamma0 M') inf_le_right Att ?_ ?_ ?_ ψ ?_
    · intro γ hγ τ τ' h h'
      exact huniq γ hγ τ τ' h h'
    · intro γ δ hγ hδ τ σ h h'
      exact hmul γ δ hγ hδ τ σ h h'
    · intro γ hγ
      have := hex γ⁻¹ ((CongruenceSubgroup.Gamma0 M').inv_mem hγ)
      rwa [inv_inv] at this
    · intro γ hγ
      have hγq : (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma q := (Subgroup.mem_inf.mp γ.2).1
      have hγ0 : (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M' := (Subgroup.mem_inf.mp γ.2).2

      have hd : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) = 1 := by
        rw [← hψ γ, hγ, Units.val_one]
      have hc : (((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod ℓ) = 0 := CongruenceSubgroup.Gamma0_mem.mp (hΔℓ γ.2)
      have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
      rw [Matrix.det_fin_two] at hdet
      have ha : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod ℓ) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod ℓ)) hdet
        simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, hd, mul_one, mul_zero, sub_zero] at this
        exact this
      have hinv : ((((γ : SL(2, ℤ))⁻¹) 1 1 : ℤ) : ZMod ℓ) = 1 := by
        have e : (((γ : SL(2, ℤ))⁻¹) 1 1 : ℤ) = (γ : SL(2, ℤ)) 0 0 := by
          rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; rfl
        rw [e]; exact ha
      exact htriv (γ : SL(2, ℤ))⁻¹ ((CongruenceSubgroup.Gamma q).inv_mem hγq)
        ((CongruenceSubgroup.Gamma0 M').inv_mem hγ0) hinv
  have hcard : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  rw [hcard] at hdvd
  have hG' : G = Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧ Att γ⁻¹ τ} := hG
  subst hG'
  refine ⟨?_, hdvd⟩
  apply Nat.finite_of_card_ne_zero
  intro h0
  rw [h0, zero_dvd_iff] at hdvd
  have hℓ1 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  omega

end S_ModularCurve_FullLevel_AuxLevelOne_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma_of_dvd (solution)
