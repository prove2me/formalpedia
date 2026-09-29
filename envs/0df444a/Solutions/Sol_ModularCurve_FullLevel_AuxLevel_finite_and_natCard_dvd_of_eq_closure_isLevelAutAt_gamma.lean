-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/8a7e8f5a-6594-59b5-81b1-57f8f1b9da73

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

namespace C3Kit

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

end C3Kit

open scoped MatrixGroups

theorem GCard.mem_Gamma_mul {q ℓ : ℕ} (hcop : Nat.Coprime q ℓ) {γ : SL(2, ℤ)}
    (hq : γ ∈ CongruenceSubgroup.Gamma q) (hℓ : γ ∈ CongruenceSubgroup.Gamma ℓ) :
    γ ∈ CongruenceSubgroup.Gamma (q * ℓ) := by
  rw [CongruenceSubgroup.Gamma_mem] at hq hℓ ⊢
  have hcop' : IsCoprime (q : ℤ) (ℓ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop

  have key1 : ∀ x : ℤ, (x : ZMod q) = 1 → (x : ZMod ℓ) = 1 → (x : ZMod (q * ℓ)) = 1 := by
    intro x h1 h2
    have e1 : ((x - 1 : ℤ) : ZMod q) = 0 := by rw [Int.cast_sub, Int.cast_one, h1, sub_self]
    have e2 : ((x - 1 : ℤ) : ZMod ℓ) = 0 := by rw [Int.cast_sub, Int.cast_one, h2, sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at e1 e2
    have e3 : ((q * ℓ : ℕ) : ℤ) ∣ x - 1 := by push_cast; exact hcop'.mul_dvd e1 e2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, sub_eq_zero] at e3
    exact e3
  have key0 : ∀ x : ℤ, (x : ZMod q) = 0 → (x : ZMod ℓ) = 0 → (x : ZMod (q * ℓ)) = 0 := by
    intro x h1 h2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
    have e3 : ((q * ℓ : ℕ) : ℤ) ∣ x := by push_cast; exact hcop'.mul_dvd h1 h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at e3
    exact e3
  exact ⟨key1 _ hq.1 hℓ.1, key0 _ hq.2.1 hℓ.2.1, key0 _ hq.2.2.1 hℓ.2.2.1, key1 _ hq.2.2.2 hℓ.2.2.2⟩

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (G : Subgroup (↥K ≃ₐ[L] ↥K))
    (hG : G = Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ}) :
    Finite ↥G ∧ Nat.card ↥G ∣ ℓ * (ℓ ^ 2 - 1) := by
  classical

  obtain ⟨huniq, hmul, htriv⟩ :=
    ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  have hex := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  set Att : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K) → Prop := fun γ τ =>
    ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ K τ with hAtt

  let Δ : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M'
  let red : SL(2, ℤ) →* SL(2, ZMod ℓ) :=
    @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod ℓ))
  let ψ : ↥Δ →* SL(2, ZMod ℓ) := red.comp Δ.subtype
  have hcop : Nat.Coprime q ℓ := (Nat.coprime_primes (Fact.out) (Fact.out)).mpr (Ne.symm hℓq)
  have hdvd : Nat.card ↥(Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧ Att γ⁻¹ τ}) ∣ Nat.card (SL(2, ZMod ℓ)) := by
    refine C3Kit.natCard_closure_dvd (CongruenceSubgroup.Gamma0 M') (CongruenceSubgroup.Gamma q)
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
      have hγℓ : (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma ℓ := by
        rw [CongruenceSubgroup.Gamma_mem']
        exact hγ
      have hγqℓ : (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma (q * ℓ) := GCard.mem_Gamma_mul hcop hγq hγℓ
      exact htriv (γ : SL(2, ℤ))⁻¹ ((CongruenceSubgroup.Gamma (q * ℓ)).inv_mem hγqℓ)
        ((CongruenceSubgroup.Gamma0 M').inv_mem hγ0)
  rw [Matrix.SpecialLinearGroup.natCard_fin_two_zmod_eq_of_prime ℓ] at hdvd
  have hG' : G = Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧ Att γ⁻¹ τ} := hG
  subst hG'
  refine ⟨?_, hdvd⟩
  apply Nat.finite_of_card_ne_zero
  intro h0
  rw [h0, zero_dvd_iff] at hdvd
  have hℓ1 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have : 0 < ℓ * (ℓ ^ 2 - 1) := Nat.mul_pos (by omega) (Nat.sub_pos_of_lt (by nlinarith))
  omega

end S_ModularCurve_FullLevel_AuxLevel_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma (solution)
