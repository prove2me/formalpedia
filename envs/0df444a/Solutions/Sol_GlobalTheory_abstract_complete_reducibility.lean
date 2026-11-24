-- Prove2me | solution 1 for GlobalTheory.abstract_complete_reducibility
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:13.982948+00:00
-- url     : https://prove2.me/submissions/2f8b93ae-aa7b-4ae6-87d1-9e3e1986baa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AbstractCompleteReducibility
import Theorems.Thm_GlobalTheory_exists_mem_sub_orth_of_finiteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  classical
  intro E _ _ P hInf N hN b hpos _hherm hperp e he hidem hsa hfin ψ hψN hψe
  let S := ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A
  show ψ ∈ S
  let V := N.map e
  have hVN : V ≤ N := by rintro _ ⟨x, hx, rfl⟩; exact he N le_rfl hN x hx
  have heV : ∀ v ∈ V, e v = v := by rintro _ ⟨x, hx, rfl⟩; exact hidem x hx
  have hψV : ψ ∈ V := ⟨ψ, hψN, hψe⟩
  have hIrrS : ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → A ≤ S :=
    fun A hA => le_iSup₂_of_le (f := fun A (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) => A) A hA le_rfl
  have hpos0 : ∀ x ∈ N, b x x = 0 → x = 0 := by
    intro x hx h0
    by_contra hne
    have := hpos x hx hne
    rw [h0] at this
    simp at this
  have hGen : ∀ x : E, ∃ G : Submodule ℂ E, x ∈ G ∧ P G ∧ ∀ A, x ∈ A → P A → G ≤ A := fun x =>
    ⟨sInf {A | x ∈ A ∧ P A}, Submodule.mem_sInf.2 fun A hA => hA.1, hInf _ fun A hA => hA.2,
      fun A hx hA => sInf_le ⟨hx, hA⟩⟩
  let C : Submodule ℂ E := sInf (insert N {X | ∃ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) ∧ X = N ⊓ ⨅ a ∈ A, LinearMap.ker (b a)})
  have hCP : P C := by
    apply hInf
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hN
    · exact hperp A hA.1 hA.2.1
  have hCorth : ∀ x ∈ C, ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0 := by
    intro x hx A hA a ha
    have : x ∈ N ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
      Submodule.mem_sInf.1 hx _ (Set.mem_insert_of_mem _ ⟨A, hA, rfl⟩)
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this.2 a ha
  have hCmem : ∀ x ∈ N, (∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0) → x ∈ C := by
    intro x hx h
    refine Submodule.mem_sInf.2 ?_
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hx
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      exact ⟨hx, fun a ha => h A hA a ha⟩
  have hfinT : FiniteDimensional ℂ ↥(S ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hsT, hsorth⟩ := exists_mem_sub_orth_of_finiteDimensional b (S ⊓ V)
    (fun t ht h0 => hpos0 t (hVN ht.2) h0) ψ
  have hcV : ψ - s ∈ V := V.sub_mem hψV hsT.2
  have hcC : ψ - s ∈ C := by
    refine hCmem _ (hVN hcV) fun A hA a ha => ?_
    have haN : a ∈ N := hA.1 ha
    have heaT : e a ∈ S ⊓ V := ⟨hIrrS A hA (he A hA.1 hA.2.1 a ha), ⟨a, haN, rfl⟩⟩
    rw [← heV _ hcV, ← hsa a haN _ (hVN hcV)]
    exact hsorth _ heaT
  suffices hc0 : ψ - s = 0 by
    rw [sub_eq_zero] at hc0
    rw [hc0]
    exact hsT.1
  by_contra hc0
  obtain ⟨D, hcD, hDP, hDmin⟩ := hGen (ψ - s)
  have hDC : D ≤ C := hDmin C hcC hCP
  have hDN : D ≤ N := hDmin N (hVN hcV) hN
  have hex : ∃ n, ∃ B : Submodule ℂ E, B ≤ D ∧ P B ∧ B ⊓ V ≠ ⊥ ∧ finrank ℂ ↥(B ⊓ V) = n :=
    ⟨_, D, le_rfl, hDP, (Submodule.ne_bot_iff _).2 ⟨ψ - s, ⟨hcD, hcV⟩, hc0⟩, rfl⟩
  obtain ⟨B, hBD, hBP, hBV, hBn⟩ := Nat.find_spec hex
  have hmin : ∀ B₁ : Submodule ℂ E, B₁ ≤ D → P B₁ → B₁ ⊓ V ≠ ⊥ →
      Nat.find hex ≤ finrank ℂ ↥(B₁ ⊓ V) :=
    fun B₁ h1 h2 h3 => Nat.find_min' hex ⟨B₁, h1, h2, h3, rfl⟩
  obtain ⟨β, hβBV, hβ0⟩ := (Submodule.ne_bot_iff _).1 hBV
  obtain ⟨G, hβG, hGP, hGmin⟩ := hGen β
  have hGB : G ≤ B := hGmin B hβBV.1 hBP
  have hGN : G ≤ N := hGB.trans (hBD.trans hDN)
  have hβV : β ∈ V := hβBV.2
  have hβe : e β = β := heV β hβV
  have hGirr : G ≤ N ∧ P G ∧ G ≠ ⊥ ∧ ∀ B'' : Submodule ℂ E, B'' ≤ G → P B'' → B'' = ⊥ ∨ B'' = G := by
    refine ⟨hGN, hGP, (Submodule.ne_bot_iff _).2 ⟨β, hβG, hβ0⟩, fun B'' hle hP => ?_⟩
    have hB''N : B'' ≤ N := hle.trans hGN
    by_cases hV'' : B'' ⊓ V = ⊥
    · left
      have hey : ∀ y ∈ B'', e y = 0 := by
        intro y hy
        have : e y ∈ B'' ⊓ V := ⟨he B'' hB''N hP y hy, ⟨y, hB''N hy, rfl⟩⟩
        rw [hV''] at this
        exact (Submodule.mem_bot ℂ).1 this
      have hβperp : β ∈ N ⊓ ⨅ a ∈ B'', LinearMap.ker (b a) := by
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
        refine ⟨hVN hβV, fun y hy => ?_⟩
        rw [← hβe, ← hsa y (hB''N hy) β (hVN hβV), hey y hy, map_zero, LinearMap.zero_apply]
      have hGperp := hGmin _ hβperp (hperp B'' hB''N hP)
      rw [eq_bot_iff]
      intro y hy
      have hyp := hGperp (hle hy)
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyp
      exact (Submodule.mem_bot ℂ).2 (hpos0 y (hB''N hy) (hyp.2 y hy))
    · right
      have hle' : B'' ⊓ V ≤ B ⊓ V := inf_le_inf_right _ (hle.trans hGB)
      have hfinBV : FiniteDimensional ℂ ↥(B ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
      have heq : B'' ⊓ V = B ⊓ V := Submodule.eq_of_le_of_finrank_le hle' (by
        rw [hBn]; exact hmin B'' (hle.trans (hGB.trans hBD)) hP hV'')
      have hβB'' : β ∈ B'' := by
        have h2 := hβBV
        rw [← heq] at h2
        exact h2.1
      exact le_antisymm hle (hGmin B'' hβB'' hP)
  exact hβ0 (hpos0 β (hVN hβV) (hCorth β (hDC (hBD hβBV.1)) G hGirr β hβG))
end GlobalTheory
