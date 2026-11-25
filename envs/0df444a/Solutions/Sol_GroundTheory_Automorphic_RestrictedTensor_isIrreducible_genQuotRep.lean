-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isIrreducible_genQuotRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:39.65994+00:00
-- url     : https://prove2.me/submissions/a5824b6d-c402-40a9-bed9-11b340828443

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_genSubrep_le
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_of_mem_genSubrep_fixed
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_genQuotMk_injective
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_fixedProj_mem


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
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}
variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)
variable {N}
variable (hNK : N ≤ fixedVectors σ K)
  (hNst : ∀ g, ∀ n ∈ N, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N)
include hNK hNst
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (hN0 : N ≠ ⊥)
    (hNmin : ∀ N₁ : Submodule ℂ V, N₁ ≤ N → N₁ ≠ ⊥ →
      (∀ g, ∀ n ∈ N₁, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N₁) → N₁ = N) :
    (genQuotRep hσ hKc hKo N).IsIrreducible := by
  set U := genSubrep σ N
  set U₀ := genKernel hσ hKc hKo N
  set π := genQuotRep hσ hKc hKo N
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hmk0 : genQuotMk hσ hKc hKo N ⟨n, hn⟩ ≠ 0 := by
    intro h
    have := genQuotMk_injective hσ hKc hKo hNK (a₁ := ⟨n, hn⟩) (a₂ := 0) (by rw [h, map_zero])
    exact hn0 (congrArg Subtype.val this)
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h0
    have : genQuotMk hσ hKc hKo N ⟨n, hn⟩ ∈ (⊤ : Subrepresentation π).toSubmodule :=
      Submodule.mem_top
    rw [← h0] at this
    exact hmk0 this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }

  let Y : Subrepresentation σ :=
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

  have hst : ∀ g, ∀ m ∈ Y.toSubmodule ⊓ N, (fixedProj σ hσ hKc hKo (σ g m) : V) ∈
      Y.toSubmodule ⊓ N := by
    rintro g m ⟨hmY, hmN⟩
    exact ⟨fixedProj_mem hσ hKc hKo Y (Y.apply_mem_toSubmodule g hmY), hNst g m hmN⟩
  by_cases hYN : Y.toSubmodule ⊓ N = ⊥
  ·
    left
    ext q
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      show Submodule.Quotient.mk u = (0 : U.toSubmodule ⧸ U₀)
      rw [Submodule.Quotient.mk_eq_zero]
      intro g
      have hY : (U.toRepresentation g u : V) ∈ Y.toSubmodule :=
        ⟨U.toRepresentation g u, X.apply_mem_toSubmodule g hq, rfl⟩
      have h1 := fixedProj_mem hσ hKc hKo Y hY
      have h2 : (fixedProj σ hσ hKc hKo (σ g u) : V) ∈ N :=
        mem_of_mem_genSubrep_fixed hσ hKc hKo hNK hNst (hYU h1) (fixedProj σ hσ hKc hKo _).2
      have h3 : (fixedProj σ hσ hKc hKo (σ g u) : V) ∈ Y.toSubmodule ⊓ N := ⟨h1, h2⟩
      rw [hYN, Submodule.mem_bot] at h3
      exact Subtype.ext h3
    · have : q = 0 := hq
      rw [this]
      exact X.toSubmodule.zero_mem
  ·
    right
    have hle : Y.toSubmodule ⊓ N ≤ N := inf_le_right
    have heq := hNmin _ hle hYN hst
    have hNY : N ≤ Y.toSubmodule := heq ▸ inf_le_left
    have hUY := genSubrep_le hNY
    ext q
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u', hu', hu'u⟩ := hUY u.2
    have : u' = u := Subtype.ext hu'u
    rw [← this]
    exact hu'
end GroundTheory.Automorphic.RestrictedTensor
