-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.primIn_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:17.94984+00:00
-- url     : https://prove2.me/submissions/b0b5f713-e324-4f02-8b4f-c6f6bd0d834c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_dInv_one
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_map_mem_dOne
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_int_mul_mem
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_splitLat
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_pairLat_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {g : ℕ} (hg : g ≠ 0) {a b : 𝓞 E}
    (hab : differentIdeal ℤ (𝓞 E) = Ideal.span {a, b}) :
    PrimIn (pairLat g (splitP E) (splitQ σ g (a : E) (b : E))) (splitLat E) := by
  have ha : (a : E) ∈ dOne E := FractionalIdeal.mem_coeIdeal_of_mem _
    (hab ▸ Ideal.subset_span (by simp))
  have hb : (b : E) ∈ dOne E := FractionalIdeal.mem_coeIdeal_of_mem _
    (hab ▸ Ideal.subset_span (by simp))
  constructor
  · intro v hv
    obtain ⟨α, hα, β, hβ, γ, hγ, δ, hδ, rfl⟩ := (mem_pairLat_split σ hg _ _ v).1 hv
    have h1 := (mem_dInv_one γ).1 hγ _ ha
    have h2 := (mem_dInv_one γ).1 hγ _ hb
    refine (mem_splitLat _).2 ⟨hα, ?_, h1, h1, h2, h2, hδ, add_mem hβ hδ⟩
    have h3 := Submodule.add_mem (dOne E : Submodule (𝓞 E) E)
      (int_mul_mem h1 (map_mem_dOne σ hσ ha)) (int_mul_mem h2 (map_mem_dOne σ hσ hb))
    have h4 := int_mul_mem (I := dOne E) (neg_mem (natCast_mem (Int' E) g)) h3
    convert h4 using 1
    simp [splitC]
    ring
  · intro v hv hs
    have hv' : ∃ α β γ δ : E,
        v = ![α, γ * splitC σ g (a : E) (b : E), γ * a, γ * a, γ * b, γ * b, δ, β + δ] := by
      clear hv
      induction hs using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨α, -, β, -, γ, -, δ, -, rfl⟩ := (mem_pairLat_split σ hg _ _ v).1 hv
        exact ⟨α, β, γ, δ, rfl⟩
      | zero => exact ⟨0, 0, 0, 0, by ext i; fin_cases i <;> simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨α, β, γ, δ, rfl⟩ := hv
        obtain ⟨α', β', γ', δ', rfl⟩ := hw
        exact ⟨α + α', β + β', γ + γ', δ + δ', by ext i; fin_cases i <;> simp <;> ring⟩
      | smul c v _ hv =>
        obtain ⟨α, β, γ, δ, rfl⟩ := hv
        exact ⟨c * α, c * β, c * γ, c * δ, by ext i; fin_cases i <;> simp <;> ring⟩
    obtain ⟨α, β, γ, δ, rfl⟩ := hv'
    obtain ⟨h0, -, h2, -, h4, -, h6, h7⟩ := (mem_splitLat _).1 hv
    refine (mem_pairLat_split σ hg _ _ _).2
      ⟨α, h0, β, by simpa using sub_mem h7 h6, γ, (mem_dInv_one γ).2 fun t ht => ?_, δ, h6, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ht
    rw [hab, Ideal.mem_span_pair] at hs
    obtain ⟨p, q, rfl⟩ := hs
    convert add_mem (mul_mem (⟨p, rfl⟩ : _ ∈ Int' E) h2) (mul_mem (⟨q, rfl⟩ : _ ∈ Int' E) h4) using 1
    simp
    ring
end GlobalTheory.SgGlob.Inhab
