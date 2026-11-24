-- Prove2me | solution 1 for GlobalTheory.UTrans.tvGen_adjust
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:20:18.512947+00:00
-- url     : https://prove2.me/submissions/87ba0455-b92d-4505-8845-f1b56ee2b74b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTraceZeroAdjustmentOfHermitianLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidAdjustIntegralAway
import Theorems.Thm_GlobalTheory_T_exists_traceZero_adjustment_of_hermitian_lattice
import Theorems.Thm_GlobalTheory_T_transvection_identities_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans
namespace GlobalTheory.UTrans
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ m ∈ TvGen (c : E →+* E) G, ∀ b : ℕ, 0 < b → ∀ N : ℕ, ∃ m' ∈ TvGen (c : E →+* E) G, ∃ k e : ℕ, k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (m' *ᵥ v - m *ᵥ v) = b ^ N • w) ∧ b ^ e • (m' *ᵥ v) ∈ L ∧ b ^ e • (m'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hFE hG L hL hsp m hm b hb
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    intro N
    obtain ⟨x, t, hx, ht, rfl⟩ := hm
    obtain ⟨t', k, e, ht', hk, H⟩ := GlobalTheory.T.exists_traceZero_adjustment_of_hermitian_lattice F E c n G hFE hG L hL hsp x t (b ^ (N + 1)) (by positivity) ht
    have hinv : (tv (c : E →+* E) G x t')⁻¹ = tv (c : E →+* E) G x (-t') := by
      apply Matrix.inv_eq_right_inv
      rw [(GlobalTheory.T.transvection_identities_unitary E n (c : E →+* E) G hG.invol hG.herm).2.2.1, hx]
      ext i j
      simp [tv]
    refine ⟨_, Submonoid.subset_closure ⟨x, t', hx, ht', rfl⟩, k, (N + 1) * e,
      (Nat.coprime_pow_right_iff (Nat.succ_pos N) _ _).1 hk, fun v hv => ?_⟩
    obtain ⟨⟨w, hw, h1⟩, h2, h3⟩ := H v hv
    refine ⟨⟨b • w, L.smul_of_tower_mem _ hw, ?_⟩, ?_, ?_⟩
    · rw [h1, smul_smul, pow_succ]
    · rwa [pow_mul]
    · rwa [pow_mul, hinv]
  | one =>
    intro N
    refine ⟨1, one_mem _, 1, 0, by simp, fun v hv => ⟨⟨0, zero_mem _, by simp⟩, ?_, ?_⟩⟩ <;> simpa using hv
  | mul m₁ m₂ _ _ ih₁ ih₂ =>
    intro N
    obtain ⟨p, -, k₀, e₀, hk₀, H₀⟩ := ih₁ 0
    have hden : ∀ v ∈ L, (k₀ * b ^ e₀) • (m₁ *ᵥ v) ∈ L := by
      intro v hv
      obtain ⟨⟨w, hw, h1⟩, h2, -⟩ := H₀ v hv
      have : (k₀ * b ^ e₀) • (m₁ *ᵥ v) = k₀ • b ^ e₀ • (p *ᵥ v) - b ^ e₀ • (b ^ 0 • w) := by
        rw [← h1]; module
      rw [this]
      exact sub_mem (L.smul_of_tower_mem _ h2) (L.smul_of_tower_mem _ (L.smul_of_tower_mem _ hw))
    obtain ⟨q₂, hq₂, k₂, e₂, hk₂, H₂⟩ := ih₂ (N + e₀)
    obtain ⟨q₁, hq₁, k₁, e₁, hk₁, H₁⟩ := ih₁ (N + e₂)
    refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, k₀ * k₁ * k₂, e₁ + e₂,
      Nat.Coprime.mul_left (Nat.Coprime.mul_left hk₀ hk₁) hk₂, fun v hv => ⟨?_, ?_, ?_⟩⟩
    · obtain ⟨⟨w₂, hw₂, a1⟩, a2, -⟩ := H₂ v hv
      obtain ⟨⟨w₁, hw₁, b1⟩, -, -⟩ := H₁ _ a2
      have hb' : ((b : E) ^ e₂) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hb.ne')
      have b2 : k₁ • (q₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (q₂ *ᵥ v)) = b ^ N • w₁ := by
        apply smul_right_injective (Fin n → E) hb'
        simp only [Matrix.mulVec_smul] at b1
        linear_combination (norm := module) b1
      have a3 : k₂ • (m₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (m₂ *ᵥ v)) = b ^ (N + e₀) • (m₁ *ᵥ w₂) := by
        rw [← Matrix.mulVec_smul, ← a1, Matrix.mulVec_smul, Matrix.mulVec_sub]
      refine ⟨(k₀ * k₂) • w₁ + k₁ • (k₀ * b ^ e₀) • (m₁ *ᵥ w₂),
        add_mem (L.smul_of_tower_mem _ hw₁) (L.smul_of_tower_mem _ (hden _ hw₂)), ?_⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      linear_combination (norm := module) (k₀ * k₂) • b2 + (k₀ * k₁) • a3
    · have := (H₁ _ (H₂ v hv).2.1).2.1
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec] at this
    · have := (H₂ _ (H₁ v hv).2.2).2.2
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev, add_comm] at this
end GlobalTheory.UTrans
