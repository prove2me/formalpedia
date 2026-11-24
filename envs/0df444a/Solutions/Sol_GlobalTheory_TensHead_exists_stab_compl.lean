-- Prove2me | solution 1 for GlobalTheory.TensHead.exists_stab_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:37.495484+00:00
-- url     : https://prove2.me/submissions/75b30b43-e346-4312-8f23-b633da2d61c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
variable {W : Type} [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.TensHead
theorem _root_.solution {A : Set (Module.End ℂ W)}
    (htop : sSup {T | MinStab A T} = ⊤) (K : Submodule ℂ W) (hK : Stab A K) :
    ∃ C : Submodule ℂ W, Stab A C ∧ C ⊓ K = ⊥ ∧ C ⊔ K = ⊤ := by
  have hsup : ∀ N N' : Submodule ℂ W, Stab A N → Stab A N' → Stab A (N ⊔ N') := by
    intro N N' hN hN' a ha x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hN a ha y hy) (hN' a ha z hz)
  let S : Set (Submodule ℂ W) := {C | Stab A C ∧ C ⊓ K = ⊥}
  obtain ⟨C, hCmax⟩ : ∃ C, Maximal (· ∈ S) C := by
    refine zorn_le₀ S ?_
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨?_, bot_inf_eq _⟩, by simp⟩
      intro a _ x hx
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun z hz => le_sSup hz⟩
      · intro a ha x hx
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx ⊢
        obtain ⟨y, hy, hxy⟩ := hx
        exact ⟨y, hy, (hcS hy).1 a ha x hxy⟩
      · rw [eq_bot_iff]
        intro x hx0
        obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hx' : x ∈ y ⊓ K := ⟨hxy, hxK⟩
        rwa [(hcS hy).2] at hx'
  obtain ⟨⟨hCs, hCK⟩, hCm⟩ := hCmax
  refine ⟨C, hCs, hCK, ?_⟩
  by_contra hne
  have hex : ∃ T, MinStab A T ∧ ¬ T ≤ C ⊔ K := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (top_unique (by rw [← htop]; exact sSup_le fun T hT => h T hT))
  obtain ⟨T, ⟨hTs, hTmin⟩, hTn⟩ := hex
  have hI : Stab A (T ⊓ (C ⊔ K)) := fun a ha x hx =>
    ⟨hTs a ha x hx.1, hsup C K hCs hK a ha x hx.2⟩
  rcases hTmin _ hI inf_le_left with h | h
  · have hmem : C ⊔ T ∈ S := by
      refine ⟨hsup C T hCs hTs, ?_⟩
      rw [eq_bot_iff]
      intro x hx0
      obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
      obtain ⟨c, hc, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
      have ht' : t ∈ T ⊓ (C ⊔ K) := by
        refine ⟨ht, ?_⟩
        simpa using Submodule.sub_mem _ (Submodule.mem_sup_right hxK : c + t ∈ C ⊔ K)
          (Submodule.mem_sup_left hc : c ∈ C ⊔ K)
      have ht0 : t = 0 := by
        rw [h] at ht'
        exact (Submodule.mem_bot ℂ).mp ht'
      subst ht0
      rw [add_zero] at hxK ⊢
      have hc' : c ∈ C ⊓ K := ⟨hc, hxK⟩
      rwa [hCK] at hc'
    have hle : C ⊔ T ≤ C := hCm hmem le_sup_left
    exact hTn ((le_sup_right.trans hle).trans le_sup_left)
  · exact hTn (inf_eq_left.mp h)
end GlobalTheory.TensHead
