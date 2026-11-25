-- Prove2me | solution 1 for GlobalTheory.EigenLine.line_hyperplane_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:41:20.674041+00:00
-- url     : https://prove2.me/submissions/bf34915b-36da-479e-baba-fa269acc3440

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LineHyperplaneCut
import Theorems.Thm_GlobalTheory_EigenLine_action_mem
import Theorems.Thm_GlobalTheory_EigenLine_action_eigen_right
import Theorems.Thm_GlobalTheory_EigenLine_action_eigen_left
import Theorems.Thm_GlobalTheory_EigenLine_twist_twist
import Theorems.Thm_GlobalTheory_EigenLine_form_action
import Theorems.Thm_GlobalTheory_EigenLine_finrank_ker_add_one
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.EigenLine
variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]
namespace GlobalTheory.EigenLine
theorem _root_.solution (K : Type) [Field K] (O : Type) [CommRing O] (L : Type)
    [AddCommGroup L] [Module K L]
    [FiniteDimensional K L] (ρ : O →+* Module.End K L) (c : O →+* O) (B : LinearMap.BilinForm K L)
    (χ : O →+* K) (ε : K ⊗[ℤ] O) (M M' : Submodule K L) (n₀ : L)
    (hcc : ∀ a, c (c a) = a) (hadj : ∀ a x y, B x (ρ a y) = B (ρ (c a) x) y)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hε : ∀ a, ε * ((1 : K) ⊗ₜ[ℤ] a) = χ a • ε) (hε0 : ε ≠ 0) (hMM : IsCompl M M')
    (hM : ∀ a, ∀ x ∈ M, ρ a x ∈ M) (hM' : ∀ a, ∀ x ∈ M', ρ a x ∈ M')
    (hspan : M = Submodule.span K (Set.range fun a => ρ a n₀))
    (hinj : ∀ t : K ⊗[ℤ] O, tensorAction ρ t n₀ = 0 → t = 0) :
    Module.finrank K ↥(M ⊓ LinearMap.range (tensorAction ρ ε)) = 1 ∧
    Module.finrank K ↥(B.orthogonal M ⊓ LinearMap.range (tensorAction ρ ε)) + 1 =
      Module.finrank K ↥(LinearMap.range (tensorAction ρ ε)) := by
  set T := tensorAction ρ ε with hT
  set E := LinearMap.range T with hE
  have hn₀ : n₀ ∈ M := by
    rw [hspan]
    exact Submodule.subset_span ⟨1, by simp⟩
  have hTn : T n₀ ≠ 0 := fun h => hε0 (hinj ε h)

  have hTM : ∀ m ∈ M, T m ∈ K ∙ T n₀ := by
    intro m hm
    rw [hspan] at hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have : T (ρ a n₀) = χ a • T n₀ := action_eigen_right ρ χ ε hε a n₀
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hline : M ⊓ E = K ∙ T n₀ := by
    apply le_antisymm
    · rintro x ⟨hxM, z, rfl⟩
      have hz : z ∈ M ⊔ M' := by rw [hMM.sup_eq_top]; trivial
      obtain ⟨m, hm, m', hm', rfl⟩ := Submodule.mem_sup.1 hz
      have h1 : T m' ∈ M' := action_mem ρ M' hM' ε m' hm'
      have h2 : T m ∈ M := action_mem ρ M hM ε m hm
      have h3 : T m' ∈ M := by
        have : T m' = T (m + m') - T m := by rw [map_add]; abel
        rw [this]
        exact M.sub_mem hxM h2
      have h4 : T m' = 0 := by
        have : T m' ∈ M ⊓ M' := ⟨h3, h1⟩
        rwa [hMM.inf_eq_bot, Submodule.mem_bot] at this
      rw [map_add, h4, add_zero]
      exact hTM m hm
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨action_mem ρ M hM ε n₀ hn₀, n₀, rfl⟩
  refine ⟨by rw [hline]; exact finrank_span_singleton hTn, ?_⟩

  let f : E →ₗ[K] K := (B n₀).comp E.subtype
  have hf : f ≠ 0 := by
    have h1 : twist c ε ≠ 0 := by
      intro h
      apply hε0
      rw [← twist_twist c hcc ε, h, map_zero]
    have h2 : tensorAction ρ (twist c ε) n₀ ≠ 0 := fun h => h1 (hinj _ h)
    obtain ⟨z, hz⟩ : ∃ z, B (tensorAction ρ (twist c ε) n₀) z ≠ 0 := by
      by_contra h
      push_neg at h
      exact h2 (hnd _ h)
    intro h0
    apply hz
    rw [← form_action ρ c B hadj]
    exact LinearMap.congr_fun h0 ⟨T z, z, rfl⟩
  have hmap : (LinearMap.ker f).map E.subtype = B.orthogonal M ⊓ E := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyk, rfl⟩
      refine ⟨?_, hy⟩
      change y ∈ B.orthogonal M
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hy0 : B n₀ y = 0 := hyk
      rw [hspan] at hn
      induction hn using Submodule.span_induction with
      | mem n hn =>
        obtain ⟨a, rfl⟩ := hn
        obtain ⟨z, rfl⟩ := hy
        have h1 := hadj (c a) n₀ (T z)
        rw [hcc] at h1
        show B (ρ a n₀) (T z) = 0
        rw [← h1, action_eigen_left ρ χ ε hε, map_smul, hy0, smul_zero]
      | zero => simp [LinearMap.BilinForm.IsOrtho]
      | add u v _ _ hu hv =>
        simp only [LinearMap.BilinForm.IsOrtho, map_add, LinearMap.add_apply] at *
        rw [hu, hv, add_zero]
      | smul r u _ hu =>
        simp only [LinearMap.BilinForm.IsOrtho, map_smul, LinearMap.smul_apply] at *
        rw [hu, smul_zero]
    · rintro ⟨hx, hxE⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      have hx' : x ∈ B.orthogonal M := hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx'
      exact hx' n₀ hn₀
  rw [← hmap, Submodule.finrank_map_subtype_eq]
  exact finrank_ker_add_one f hf
end GlobalTheory.EigenLine
