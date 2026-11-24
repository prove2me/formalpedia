-- Prove2me | solution 1 for GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:51.502403+00:00
-- url     : https://prove2.me/submissions/66905446-79a4-46b8-906b-a184fae24988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A))
    (h₁ : IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)))
    (h₂ : IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A))) : IsLat K.O K.E M := by
  obtain ⟨f₁, s₁⟩ := h₁
  obtain ⟨f₂, s₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd K.O B₁.A B₂.A) f₂ ?_
    have : M ⊓ LinearMap.ker (LinearMap.snd K.O B₁.A B₂.A) =
        (M.comap (LinearMap.inl K.O B₁.A B₂.A)).map (LinearMap.inl K.O B₁.A B₂.A) := by
      ext ⟨a, b⟩
      simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
        Submodule.mem_comap, LinearMap.inl_apply]
      constructor
      · rintro ⟨hM, rfl⟩
        exact ⟨a, hM, rfl⟩
      · rintro ⟨c, hc, he⟩
        rw [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨hc, rfl⟩
    rw [this]
    exact f₁.map _
  · set S := Submodule.span K.E (M : Set (B₁.A × B₂.A)) with hS
    have hinl : ∀ a : B₁.A, ((a, 0) : B₁.A × B₂.A) ∈ S := by
      intro a
      have ha : a ∈ Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A) := by
        rw [s₁]; trivial
      have hle : (Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A)).map
          (LinearMap.inl K.E B₁.A B₂.A) ≤ S := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨c, hc, rfl⟩
        exact hc
      exact hle ⟨a, ha, rfl⟩
    have hsnd : S.map (LinearMap.snd K.E B₁.A B₂.A) = ⊤ := by
      rw [hS, Submodule.map_span, ← s₂]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd K.E B₁.A B₂.A) := by rw [hsnd]; trivial
    obtain ⟨y, hy, hyb⟩ := hb
    have : ((a, b) : B₁.A × B₂.A) = y + (a - y.1, 0) := by
      ext
      · simp
      · simp [← hyb]
    rw [this]
    exact S.add_mem hy (hinl _)
end GlobalTheory.UnitLemma
