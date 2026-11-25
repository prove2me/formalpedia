-- Prove2me | solution 1 for GlobalTheory.WeilOpenFin.exists_finset_fix_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:47:28.57279+00:00
-- url     : https://prove2.me/submissions/24b5b914-b309-4b83-8cef-6b90a50d318c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingLeFiniteIndexWeilSubgroup
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilOpenFin
namespace GlobalTheory.WeilOpenFin
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x) → (∀ k : ℕ, 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ) → (∀ M : Subgroup (Ine (F := E) A), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M) → ∀ H : Subgroup (Weil h), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ s : Finset Ω, ∀ σ : Weil h, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ H := by
  intro E Ω _ _ _ _ _ A w h h1 h2 h3 H hH hopen
  classical

  have hfix : ∀ (g : G E Ω) (t : Finset Ω), (∀ x ∈ t, g x = x) → ∀ n : ℤ, ∀ x ∈ t, (g ^ n) x = x := by
    intro g t hg n x hx
    have hm : g ∈ MulAction.stabilizer (G E Ω) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hg x hx
    have := (MulAction.mem_stabilizer_iff).mp (Subgroup.zpow_mem _ hm n)
    rwa [AlgEquiv.smul_def] at this
  obtain ⟨s₁, hs₁⟩ := h3 (H.comap (ineIncl h)) hopen
  let φ : Weil h := frob h
  obtain ⟨m, hm0, hm⟩ := h1 (φ : G E Ω) s₁
  have hN : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  set k : ℕ := m * H.normalCore.index with hk
  have hk0 : 0 < k := Nat.mul_pos hm0 (Nat.pos_of_ne_zero hN)
  let ψ : Weil h := φ ^ k
  have hψH : ψ ∈ H := by
    apply Subgroup.normalCore_le
    show φ ^ (m * H.normalCore.index) ∈ H.normalCore
    rw [pow_mul]; exact Subgroup.pow_index_mem _ _
  have hψdeg : deg ψ = k := by simp [ψ, φ]
  have hψfix : ∀ x ∈ s₁, (ψ : G E Ω) x = x := by
    intro x hx
    have := hfix _ s₁ hm (H.normalCore.index : ℤ) x hx
    simpa [ψ, φ, hk, pow_mul] using this
  obtain ⟨ζ, hζ⟩ := h2 k hk0
  refine ⟨insert ζ s₁, fun τ hτ => ?_⟩
  obtain ⟨i, hi⟩ := hζ τ (hτ ζ (Finset.mem_insert_self _ _))
  let ρ : Weil h := τ * ψ ^ (-i)
  have hρdeg : deg ρ = 0 := by
    simp only [ρ, deg_mul, deg_zpow, hψdeg, hi]; ring
  have hρIne : (ρ : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp hρdeg
  have hρfix : ∀ x ∈ s₁, (ρ : G E Ω) x = x := by
    intro x hx
    have e1 := hfix _ s₁ hψfix (-i) x hx
    show ((τ : G E Ω) * ((ψ ^ (-i) : Weil h) : G E Ω)) x = x
    rw [AlgEquiv.mul_apply, Subgroup.coe_zpow, e1]
    exact hτ x (Finset.mem_insert_of_mem hx)
  have hρM := hs₁ ⟨ρ, hρIne⟩ hρfix
  have hρH : ρ ∈ H := by
    have : ineIncl h ⟨ρ, hρIne⟩ ∈ H := hρM
    exact this
  have : τ = ρ * ψ ^ i := by simp [ρ]
  rw [this]
  exact H.mul_mem hρH (H.zpow_mem hψH i)
end GlobalTheory.WeilOpenFin
