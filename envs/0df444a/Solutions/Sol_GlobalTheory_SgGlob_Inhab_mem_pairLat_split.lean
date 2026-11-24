-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_pairLat_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:36.951213+00:00
-- url     : https://prove2.me/submissions/06091fa2-4053-4755-b747-555a06152039

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_frameLat_one

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
theorem _root_.solution (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) (a b : E) (v : Fin 8 → E) :
    v ∈ pairLat g (splitP E) (splitQ σ g a b) ↔
      ∃ α ∈ dInv E 1, ∃ β ∈ Int' E, ∃ γ ∈ dInv E 1, ∃ δ ∈ Int' E,
        v = ![α, γ * splitC σ g a b, γ * a, γ * a, γ * b, γ * b, δ, β + δ] := by
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have key (α β γ δ : E) : ((fun i => α * splitP E i 0 + β * splitP E i 1) +
      fun i => γ * ((g : E)⁻¹ • (splitQ σ g a b - splitP E)) i 0 +
        δ * ((g : E)⁻¹ • (splitQ σ g a b - splitP E)) i 1) =
      ![α, γ * splitC σ g a b, γ * a, γ * a, γ * b, γ * b, δ, β + δ] := by
    ext i
    fin_cases i <;> simp [splitP, splitQ, hg']
  simp only [pairLat, Submodule.mem_sup, mem_frameLat_one]
  constructor
  · rintro ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, δ, hδ, rfl⟩, rfl⟩
    exact ⟨α, hα, β, hβ, γ, hγ, δ, hδ, key α β γ δ⟩
  · rintro ⟨α, hα, β, hβ, γ, hγ, δ, hδ, rfl⟩
    exact ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, δ, hδ, rfl⟩, key α β γ δ⟩
end GlobalTheory.SgGlob.Inhab
