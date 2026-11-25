-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilCoinv.exists_eq_mul_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:42.792874+00:00
-- url     : https://prove2.me/submissions/2050b741-2597-4c08-8b39-591d397dfbd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilCoinv_exists_dotProduct_ne_one
import Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_addChar
import Theorems.Thm_GlobalTheory_WeilM_nonarch_field
import Theorems.Thm_GlobalTheory_WeilM_nonarch_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilCoinv
namespace GlobalTheory.CompanionTheory.WeilCoinv
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ,
    (∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (0, y) φ) = l φ) → ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l φ = a * φ 0 := by
  intro k _ _ _ _ _ κ _ ψ hψc hψ l hl
  classical
  haveI : NonarchimedeanAddGroup k := GlobalTheory.WeilM.nonarch_field k
  haveI : NonarchimedeanAddGroup (κ → k) := GlobalTheory.WeilM.nonarch_pi k κ
  have hψlc : IsLocallyConstant ψ := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψc
  have hχ : ∀ y : κ → k, IsLocallyConstant (fun x : κ → k => ψ (x ⬝ᵥ y)) := fun y =>
    hψlc.comp_continuous (continuous_id.dotProduct continuous_const)
  have key : ∀ t : Finset (κ → k), ∀ φ ∈ SB (κ → k),
      (∀ x, φ x ≠ 0 → ∃ y ∈ t, ψ (x ⬝ᵥ y) ≠ 1) → l φ = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro φ _ h
      have hz : φ = 0 := funext fun x => by
        by_contra hx
        obtain ⟨y, hy, -⟩ := h x hx
        simp at hy
      rw [hz, map_zero]
    | @insert y t hyt ih =>
      intro φ hφ h
      obtain ⟨hφl, hφc⟩ := hφ
      obtain ⟨φ₁, hφ₁⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if ψ (x ⬝ᵥ y) = 1 then φ x else 0 := ⟨_, rfl⟩
      obtain ⟨g, hg⟩ : ∃ f : (κ → k) → ℂ,
          f = fun x => if ψ (x ⬝ᵥ y) = 1 then 0 else φ x / (ψ (x ⬝ᵥ y) - 1) := ⟨_, rfl⟩
      have hφ₁SB : φ₁ ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hφ₁]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then b else 0)
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hφ₁, h0]
      have hgSB : g ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hg]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then 0 else b / (a - 1))
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hg, h0]
      have hsch : schr ψ ((0 : κ → k), y) g = fun x => ψ (x ⬝ᵥ y) * g x := by
        funext x
        simp [GlobalTheory.WeilM.schr]
      have hdiff : φ = φ₁ + (schr ψ ((0 : κ → k), y) g - g) := by
        rw [hsch]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, hφ₁, hg]
        split_ifs with h1
        · simp
        · have hne : ψ (x ⬝ᵥ y) - 1 ≠ 0 := sub_ne_zero.mpr h1
          rw [zero_add, ← sub_one_mul]
          field_simp
      rw [hdiff, map_add, map_sub, hl y g hgSB, sub_self, add_zero]
      refine ih φ₁ hφ₁SB ?_
      intro x hx
      have hx1 : ψ (x ⬝ᵥ y) = 1 := by
        by_contra hne
        apply hx
        simp [hφ₁, hne]
      have hx2 : φ x ≠ 0 := by
        intro h0
        apply hx
        simp [hφ₁, h0]
      obtain ⟨y', hy', hy'ne⟩ := h x hx2
      rcases Finset.mem_insert.mp hy' with rfl | hy't
      · exact absurd hx1 hy'ne
      · exact ⟨y', hy't, hy'ne⟩
  have vanish : ∀ φ ∈ SB (κ → k), φ 0 = 0 → l φ = 0 := by
    intro φ hφ h0
    obtain ⟨hφl, hφc⟩ := hφ
    have hsupp : IsClosed (Function.support φ) := (hφl.isOpen_fiber 0).isClosed_compl
    have hK : IsCompact (Function.support φ) := by
      have hc := hφc.isCompact
      rwa [tsupport, hsupp.closure_eq] at hc
    have hcov : Function.support φ ⊆ ⋃ y : κ → k, {x | ψ (x ⬝ᵥ y) ≠ 1} := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx h0
      obtain ⟨y, hy⟩ := exists_dotProduct_ne_one hψ hx0
      exact Set.mem_iUnion.mpr ⟨y, hy⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : κ → k => {x | ψ (x ⬝ᵥ y) ≠ 1})
      (fun y => ((hχ y).isClosed_fiber 1).isOpen_compl) hcov
    refine key t φ ⟨hφl, hφc⟩ ?_
    intro x hx
    have hxt := ht hx
    simp only [Set.mem_iUnion] at hxt
    obtain ⟨y, hy, hxy⟩ := hxt
    exact ⟨y, hy, hxy⟩
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : κ → k)
  obtain ⟨O, hO⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  have hOc : IsCompact (O : Set (κ → k)) := hC.of_isClosed_subset O.isClosed hO
  have hO0 : (0 : κ → k) ∈ O := O.zero_mem
  obtain ⟨φ₀, hφ₀d⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if x ∈ O then 1 else 0 := ⟨_, rfl⟩
  have hφ₀ : φ₀ ∈ SB (κ → k) := by
    refine ⟨?_, HasCompactSupport.intro' hOc O.isClosed fun x hx => ?_⟩
    · rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ O
      · refine ⟨O, O.isOpen, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∈ O := hx'
        simp [hφ₀d, hx, hx'']
      · refine ⟨(O : Set (κ → k))ᶜ, O.isClosed.isOpen_compl, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∉ O := hx'
        simp [hφ₀d, hx, hx'']
    · have hx' : x ∉ O := hx
      simp [hφ₀d, hx']
  refine ⟨l φ₀, fun φ hφ => ?_⟩
  have h1 : φ - φ 0 • φ₀ ∈ SB (κ → k) := Submodule.sub_mem _ hφ (Submodule.smul_mem _ _ hφ₀)
  have h2 : (φ - φ 0 • φ₀) 0 = 0 := by simp [hφ₀d, hO0]
  have h3 := vanish _ h1 h2
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h3
  rw [h3, mul_comm]
end GlobalTheory.CompanionTheory.WeilCoinv
