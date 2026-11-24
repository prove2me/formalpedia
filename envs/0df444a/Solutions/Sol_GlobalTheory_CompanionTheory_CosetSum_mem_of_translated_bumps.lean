-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:15.616944+00:00
-- url     : https://prove2.me/submissions/36f0b5bf-7fab-45ab-b596-d1483f06215c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InducedGeneratedByKFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetSum
namespace GlobalTheory.CompanionTheory.CosetSum
theorem _root_.solution : ∀ {Γ J : Type} [Group Γ] [AddCommGroup J] [Module ℂ J] (Q K K₁ : Subgroup Γ) (π : Representation ℂ Q J) (M : Submodule ℂ (Γ → J)) (Gf : Γ → J), K₁ ≤ K → K₁.relIndex K ≠ 0 → (∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) → (∀ g : Γ, ∃ q : Q, ∃ κ ∈ K, g = (q : Γ) * κ) → (∀ φ ∈ M, ∀ x : Γ, (fun g => φ (g * x)) ∈ M) → (∀ φ ∈ M, ∀ (q : Q) (g : Γ), φ ((q : Γ) * g) = π q (φ g)) → (∀ (q : Q) (g : Γ), Gf ((q : Γ) * g) = π q (Gf g)) → (∀ (g : Γ), ∀ b ∈ K₁, Gf (g * b) = Gf g) → (∀ κ ∈ K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧ ∀ g : Γ, (¬ ∃ q : Q, ∃ b ∈ K₁, g = (q : Γ) * b) → φ g = 0) → Gf ∈ M := by
  intro Γ J _ _ _ Q K K₁ π M Gf hle hidx hconj hdec htr hlawM hlaw hinv hb
  classical
  let H : Subgroup K := K₁.subgroupOf K
  haveI hHn : H.Normal := ⟨fun n hn g => by
    have hn' : (n : Γ) ∈ K₁ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ?_
    simpa using hconj g g.2 n hn'⟩
  haveI : H.FiniteIndex := ⟨hidx⟩
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let P : Γ → Prop := fun x => ∃ q : Q, ∃ b ∈ K₁, x = (q : Γ) * b
  have hPmul : ∀ x, ∀ b ∈ K₁, P x → P (x * b) := by
    rintro x b hb' ⟨q, c, hc, rfl⟩
    exact ⟨q, c * b, K₁.mul_mem hc hb', by simp [mul_assoc]⟩
  have hb2 : ∀ κ : K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧
      ∀ g : Γ, (¬ P g) → φ g = 0 := fun κ => hb κ κ.2
  choose φ hφM hφ1 hφ0 using hb2
  have key : ∀ κ' κ : K, φ κ ((κ' : Γ) * (κ : Γ)⁻¹) =
      if P ((κ' : Γ) * (κ : Γ)⁻¹) then Gf κ' else 0 := by
    intro κ' κ
    split_ifs with h
    · obtain ⟨q, b, hbm, e⟩ := h
      rw [e, hφ1 κ q b hbm, ← hlaw]
      have hκ' : (κ' : Γ) = q * b * κ := by rw [← e]; group
      have e2 : (q : Γ) * κ = κ' * ((κ : Γ)⁻¹ * b⁻¹ * κ) := by rw [hκ']; group
      have hm : (κ : Γ)⁻¹ * b⁻¹ * κ ∈ K₁ := by
        simpa using hconj _ (K.inv_mem κ.2) _ (K₁.inv_mem hbm)
      rw [e2, hinv _ _ hm]
    · exact hφ0 κ _ h
  let r : K ⧸ H → K := Quotient.out
  have hr : ∀ δ : K ⧸ H, ((r δ : K) : K ⧸ H) = δ := fun δ => QuotientGroup.out_eq' δ
  have hPcl : ∀ x y : K, (x : K ⧸ H) = y → P x → P y := by
    intro x y hxy hx
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    have hm' : (x : Γ)⁻¹ * y ∈ K₁ := by simpa using Subgroup.mem_subgroupOf.1 hm
    have := hPmul _ _ hm' hx
    simpa using this
  let Pd : K ⧸ H → Prop := fun ε => P (r ε)
  have hPd : ∀ x : K, P x ↔ Pd (x : K ⧸ H) := fun x =>
    ⟨hPcl _ _ (hr _).symm, hPcl _ _ (hr _)⟩
  let Φ : Γ → J := ∑ δ : K ⧸ H, (fun g => φ (r δ) (g * ((r δ : K) : Γ)⁻¹))
  have hΦM : Φ ∈ M := M.sum_mem fun δ _ => htr _ (hφM _) _
  let n : ℕ := (Finset.univ.filter Pd).card
  have hΦ : ∀ κ' : K, Φ κ' = n • Gf κ' := by
    intro κ'
    have h1 : Φ κ' = ∑ δ : K ⧸ H, if Pd ((κ' : K ⧸ H) * δ⁻¹) then Gf κ' else 0 := by
      simp only [Φ, Finset.sum_apply]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [key]
      have hcl : (((κ' * (r δ)⁻¹ : K)) : K ⧸ H) = (κ' : K ⧸ H) * δ⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hr]
      have := hPd (κ' * (r δ)⁻¹)
      rw [hcl] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      simp only [this]
    rw [h1]
    have h2 := Equiv.sum_comp ((Equiv.inv (K ⧸ H)).trans (Equiv.mulLeft (κ' : K ⧸ H)))
      (fun ε => if Pd ε then Gf κ' else 0)
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at h2
    rw [h2, ← Finset.sum_filter, Finset.sum_const]
  have hn : n ≠ 0 := by
    have h1 : Pd 1 := by
      have : (r 1 : Γ) ∈ K₁ := by
        have : r 1 ∈ H := (QuotientGroup.eq_one_iff _).1 (hr 1)
        exact Subgroup.mem_subgroupOf.1 this
      exact ⟨1, _, this, by simp⟩
    exact (Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hΨM : (n : ℂ)⁻¹ • Φ ∈ M := M.smul_mem _ hΦM
  have hEq : (n : ℂ)⁻¹ • Φ = Gf := by
    funext g
    obtain ⟨q, κ, hκ, rfl⟩ := hdec g
    have hK : ((n : ℂ)⁻¹ • Φ) κ = Gf κ := by
      have := hΦ ⟨κ, hκ⟩
      simp only at this
      rw [Pi.smul_apply, this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]
    rw [hlawM _ hΨM, hK, hlaw]
  exact hEq ▸ hΨM
end GlobalTheory.CompanionTheory.CosetSum
