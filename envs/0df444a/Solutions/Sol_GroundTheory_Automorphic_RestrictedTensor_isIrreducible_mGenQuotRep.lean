-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isIrreducible_mGenQuotRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:28.488802+00:00
-- url     : https://prove2.me/submissions/294c4a94-0879-4e5f-abc5-408876c30ffa

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mGenSubrep_le
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mGenQuotMk_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
variable (ρ : Representation ℂ M V)
variable (e : End ℂ V) (N : Submodule ℂ V)
variable {ρ e N}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (he : IsWinProj ρ e) (hNe : N ≤ LinearMap.range e)
    (hNst : ∀ g, ∀ n ∈ N, e (ρ g n) ∈ N) (hN0 : N ≠ ⊥)
    (hNmin : ∀ N₁ : Submodule ℂ V, N₁ ≤ N → N₁ ≠ ⊥ → (∀ g, ∀ n ∈ N₁, e (ρ g n) ∈ N₁) → N₁ = N) :
    (mGenQuotRep ρ e N).IsIrreducible := by
  set U := mGenSubrep ρ N
  set U₀ := mGenKernel ρ e N
  set π := mGenQuotRep ρ e N
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hmk0 : mGenQuotMk ρ e N ⟨n, hn⟩ ≠ 0 := by
    intro h
    have := mGenQuotMk_injective he hNe (a₁ := ⟨n, hn⟩) (a₂ := 0) (by rw [h, map_zero])
    exact hn0 (congrArg Subtype.val this)
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h0
    have : mGenQuotMk ρ e N ⟨n, hn⟩ ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← h0] at this
    exact hmk0 this

  have hUN : ∀ u ∈ U.toSubmodule, e u ∈ N := by
    intro u hu
    have : U.toSubmodule ≤ N.comap e := by
      refine iSup_le fun g => ?_
      rintro _ ⟨m, hm, rfl⟩
      exact hNst g m hm
    exact this hu
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }
  let Y : Subrepresentation ρ :=
    { toSubmodule := (X.toSubmodule.comap U₀.mkQ).map U.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨u, hu, rfl⟩
        refine ⟨U.toRepresentation g u, ?_, rfl⟩
        have hu' : U₀.mkQ u ∈ X.toSubmodule := hu
        have := X.apply_mem_toSubmodule g hu'
        exact this }
  have hYU : ∀ {x : V}, x ∈ Y.toSubmodule → x ∈ U.toSubmodule := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  have hst : ∀ g, ∀ m ∈ Y.toSubmodule ⊓ N, e (ρ g m) ∈ Y.toSubmodule ⊓ N := by
    rintro g m ⟨hmY, hmN⟩
    exact ⟨he.mem Y _ (Y.apply_mem_toSubmodule g hmY), hNst g m hmN⟩
  by_cases hYN : Y.toSubmodule ⊓ N = ⊥
  · left
    ext q
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      show Submodule.Quotient.mk u = (0 : U.toSubmodule ⧸ U₀)
      rw [Submodule.Quotient.mk_eq_zero]
      intro g
      have hY : (U.toRepresentation g u : V) ∈ Y.toSubmodule :=
        ⟨U.toRepresentation g u, X.apply_mem_toSubmodule g hq, rfl⟩
      have h1 := he.mem Y _ hY
      have h2 : e (ρ g u) ∈ N := hUN _ (hYU hY)
      have h3 : e (ρ g u) ∈ Y.toSubmodule ⊓ N := ⟨h1, h2⟩
      rw [hYN, Submodule.mem_bot] at h3
      exact h3
    · have : q = 0 := hq
      rw [this]
      exact X.toSubmodule.zero_mem
  · right
    have heq := hNmin _ inf_le_right hYN hst
    have hNY : N ≤ Y.toSubmodule := heq ▸ inf_le_left
    have hUY := mGenSubrep_le ρ hNY
    ext q
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u', hu', hu'u⟩ := hUY u.2
    have : u' = u := Subtype.ext hu'u
    rw [← this]
    exact hu'
end GroundTheory.Automorphic.RestrictedTensor
