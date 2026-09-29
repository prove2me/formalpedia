-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3cc67f64-7739-5c3a-9c34-83a5ffc329c8

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

namespace NormK0Sol

section Frame

variable {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {M' : ℕ} [NeZero M'] (hqM' : ¬ q ∣ M')
  {ℓ : ℕ} [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
  {L : Type} [Field L] [CharZero L]
  {ξ : L} (hξ : IsPrimitiveRoot ξ (q * ℓ))
  (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
  {K : IntermediateField L (LaurentSeries L)}
  (hK : K = ModularCurve.laurentBaseChange L
    (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M')))

def Att (q M' ℓ : ℕ) [Fact q.Prime] [NeZero M'] [Fact ℓ.Prime] (L : Type) [Field L] [CharZero L] (ξ : L)
    (K : IntermediateField L (LaurentSeries L)) (γ : SL(2, ℤ)) (τ : ↥K ≃ₐ[L] ↥K) : Prop :=
  ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
    (ModularCurve.FullLevel.levelH (q * ℓ) M') γ K τ

include hq hqM' hℓ3 hℓq hℓM' hξ hι hK

theorem uniq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {τ τ' : ↥K ≃ₐ[L] ↥K}
    (h : Att q M' ℓ L ξ K γ τ) (h' : Att q M' ℓ L ξ K γ τ') : τ = τ' :=
  (ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3
    hℓq hℓM' L ξ hξ hι K hK).1 γ hγ τ τ' h h'

theorem mul {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (hδ : δ ∈ Gamma0 M') {τ σ : ↥K ≃ₐ[L] ↥K}
    (h : Att q M' ℓ L ξ K γ τ) (h' : Att q M' ℓ L ξ K δ σ) : Att q M' ℓ L ξ K (δ * γ) (τ * σ) :=
  (ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3
    hℓq hℓM' L ξ hξ hι K hK).2.1 γ δ hγ hδ τ σ h h'

theorem one : Att q M' ℓ L ξ K 1 1 :=
  (ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3
    hℓq hℓM' L ξ hξ hι K hK).2.2 1 (one_mem _) (one_mem _)

theorem exists_att_inv {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') : ∃ τ : ↥K ≃ₐ[L] ↥K, Att q M' ℓ L ξ K γ⁻¹ τ :=
  ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom q hq M' hqM' ℓ hℓ3
    hℓq hℓM' L ξ hξ hι K hK γ hγ

theorem att_inv {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {τ : ↥K ≃ₐ[L] ↥K} (hτ : Att q M' ℓ L ξ K γ⁻¹ τ) :
    Att q M' ℓ L ξ K γ τ⁻¹ := by
  obtain ⟨τ', hτ'⟩ := exists_att_inv hq hqM' hℓ3 hℓq hℓM' hξ hι hK (inv_mem hγ)
  rw [inv_inv] at hτ'

  have hprod : Att q M' ℓ L ξ K (γ * γ⁻¹) (τ * τ') :=
    mul hq hqM' hℓ3 hℓq hℓM' hξ hι hK (inv_mem hγ) hγ hτ hτ'
  rw [mul_inv_cancel] at hprod
  have h1 : τ * τ' = 1 := uniq hq hqM' hℓ3 hℓq hℓM' hξ hι hK (one_mem _) hprod
    (one hq hqM' hℓ3 hℓq hℓM' hξ hι hK)
  have : τ⁻¹ = τ' := inv_eq_of_mul_eq_one_right h1
  rw [this]
  exact hτ'

def genSet (q M' ℓ : ℕ) [Fact q.Prime] [NeZero M'] [Fact ℓ.Prime] (L : Type) [Field L] [CharZero L] (ξ : L)
    (K : IntermediateField L (LaurentSeries L)) : Set (↥K ≃ₐ[L] ↥K) :=
  {σ | ∃ γ₁ : SL(2, ℤ), γ₁ ∈ Gamma q ∧ γ₁ ∈ Gamma0 M' ∧ Att q M' ℓ L ξ K γ₁⁻¹ σ}

theorem conj_mem_genSet {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {τ : ↥K ≃ₐ[L] ↥K} (hτ : Att q M' ℓ L ξ K γ⁻¹ τ)
    {σ : ↥K ≃ₐ[L] ↥K} (hσ : σ ∈ genSet q M' ℓ L ξ K) : τ * σ * τ⁻¹ ∈ genSet q M' ℓ L ξ K := by
  obtain ⟨γ₁, hγ₁q, hγ₁M, hσ⟩ := hσ
  refine ⟨γ * γ₁ * γ⁻¹, (Gamma_normal q).conj_mem γ₁ hγ₁q γ, mul_mem (mul_mem hγ hγ₁M) (inv_mem hγ), ?_⟩
  have h1 : Att q M' ℓ L ξ K (γ₁⁻¹ * γ⁻¹) (τ * σ) :=
    mul hq hqM' hℓ3 hℓq hℓM' hξ hι hK (inv_mem hγ) (inv_mem hγ₁M) hτ hσ
  have h2 : Att q M' ℓ L ξ K (γ * (γ₁⁻¹ * γ⁻¹)) (τ * σ * τ⁻¹) :=
    mul hq hqM' hℓ3 hℓq hℓM' hξ hι hK (mul_mem (inv_mem hγ₁M) (inv_mem hγ)) hγ h1
      (att_inv hq hqM' hℓ3 hℓq hℓM' hξ hι hK hγ hτ)
  have hrw : (γ * γ₁ * γ⁻¹)⁻¹ = γ * (γ₁⁻¹ * γ⁻¹) := by group
  rw [hrw]
  exact h2

theorem conj_mem_closure {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {τ : ↥K ≃ₐ[L] ↥K} (hτ : Att q M' ℓ L ξ K γ⁻¹ τ)
    {σ : ↥K ≃ₐ[L] ↥K} (hσ : σ ∈ Subgroup.closure (genSet q M' ℓ L ξ K)) :
    τ * σ * τ⁻¹ ∈ Subgroup.closure (genSet q M' ℓ L ξ K) := by
  have hle : Subgroup.closure (genSet q M' ℓ L ξ K) ≤
      (Subgroup.closure (genSet q M' ℓ L ξ K)).comap (MulAut.conj τ).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro s hs
    simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      SetLike.mem_coe]
    exact Subgroup.subset_closure (conj_mem_genSet hq hqM' hℓ3 hℓq hℓM' hξ hι hK hγ hτ hs)
  have := hle hσ
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem inv_conj_mem_closure {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') {τ : ↥K ≃ₐ[L] ↥K}
    (hτ : Att q M' ℓ L ξ K γ⁻¹ τ)
    {σ : ↥K ≃ₐ[L] ↥K} (hσ : σ ∈ Subgroup.closure (genSet q M' ℓ L ξ K)) :
    τ⁻¹ * σ * τ ∈ Subgroup.closure (genSet q M' ℓ L ξ K) := by

  have hτ' : Att q M' ℓ L ξ K (γ⁻¹)⁻¹ τ⁻¹ := by
    rw [inv_inv]
    exact att_inv hq hqM' hℓ3 hℓq hℓM' hξ hι hK hγ hτ
  simpa only [inv_inv] using conj_mem_closure hq hqM' hℓ3 hℓq hℓM' hξ hι hK (inv_mem hγ) hτ' hσ

end Frame

theorem map_mem_fixedField {L E : Type} [Field L] [Field E] [Algebra L E]
    (H : Subgroup (E ≃ₐ[L] E)) (τ : E ≃ₐ[L] E)
    (hnorm : ∀ σ ∈ H, τ⁻¹ * σ * τ ∈ H) {f : E} (hf : f ∈ IntermediateField.fixedField H) :
    τ f ∈ IntermediateField.fixedField H := by
  rw [IntermediateField.mem_fixedField_iff] at hf ⊢
  intro σ hσ
  have h := hf _ (hnorm σ hσ)

  have h' : τ ((τ⁻¹ * σ * τ) f) = τ f := by rw [h]
  simpa only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] using h'

end NormK0Sol

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
    (hG : G = Subgroup.closure {τ : ↥K ≃ₐ[L] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ})
    (K₀ : IntermediateField L ↥K) (hK₀ : K₀ = IntermediateField.fixedField G)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ) :
    (∀ σ : ↥K ≃ₐ[L] ↥K, σ ∈ G → τ * σ * τ⁻¹ ∈ G) ∧
    (∀ σ : ↥K ≃ₐ[L] ↥K, σ ∈ G → τ⁻¹ * σ * τ ∈ G) ∧
    (∀ f : ↥K, f ∈ K₀ → τ f ∈ K₀) ∧
    (∀ f : ↥K, f ∈ K₀ → τ.symm f ∈ K₀) := by
  have hGF : G = Subgroup.closure (NormK0Sol.genSet q M' ℓ L ξ K) := hG
  have hτF : NormK0Sol.Att q M' ℓ L ξ K γ⁻¹ τ := hτ
  have h1 : ∀ σ : ↥K ≃ₐ[L] ↥K, σ ∈ G → τ * σ * τ⁻¹ ∈ G := by
    intro σ hσ
    rw [hGF] at hσ ⊢
    exact NormK0Sol.conj_mem_closure hq hqM' hℓ3 hℓq hℓM' hξ hι hK hγ hτF hσ
  have h2 : ∀ σ : ↥K ≃ₐ[L] ↥K, σ ∈ G → τ⁻¹ * σ * τ ∈ G := by
    intro σ hσ
    rw [hGF] at hσ ⊢
    exact NormK0Sol.inv_conj_mem_closure hq hqM' hℓ3 hℓq hℓM' hξ hι hK hγ hτF hσ
  refine ⟨h1, h2, ?_, ?_⟩
  · intro f hf
    subst hK₀
    exact NormK0Sol.map_mem_fixedField G τ h2 hf
  · intro f hf
    subst hK₀
    have h1' : ∀ σ ∈ G, τ⁻¹⁻¹ * σ * τ⁻¹ ∈ G := by
      intro σ hσ
      simpa only [inv_inv] using h1 σ hσ
    have := NormK0Sol.map_mem_fixedField G τ⁻¹ h1' hf
    simpa only [AlgEquiv.aut_inv] using this

end S_ModularCurve_FullLevel_AuxLevel_mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_mul_mul_inv_mem_and_map_fixedField_of_isLevelAutAt_gamma0 (solution)
