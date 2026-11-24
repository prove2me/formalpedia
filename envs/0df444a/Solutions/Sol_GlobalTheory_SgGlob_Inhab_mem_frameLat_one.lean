-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_frameLat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:47:02.690292+00:00
-- url     : https://prove2.me/submissions/dc9b19b4-021b-476b-a35e-92919ac0b782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_smul_eq
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_dInv_zero
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_int_mul_mem

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
theorem _root_.solution {n : ℕ} (P : Matrix (Fin n) (Fin (1 + 1)) E) (v : Fin n → E) :
    v ∈ frameLat P ↔ ∃ α ∈ dInv E 1, ∃ β ∈ Int' E, v = fun i => α * P i 0 + β * P i 1 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, a, ha, rfl⟩ := hv
      fin_cases b
      · exact ⟨a, ha, 0, zero_mem _, by ext i; simp⟩
      · exact ⟨0, FractionalIdeal.zero_mem _, a, (mem_dInv_zero a).1 ha, by ext i; simp⟩
    | zero => exact ⟨0, FractionalIdeal.zero_mem _, 0, zero_mem _, by ext i; simp⟩
    | add v w _ _ hv hw =>
      obtain ⟨α, hα, β, hβ, rfl⟩ := hv
      obtain ⟨α', hα', β', hβ', rfl⟩ := hw
      exact ⟨α + α', Submodule.add_mem (dInv E 1 : Submodule (𝓞 E) E) hα hα', β + β',
        add_mem hβ hβ', by ext i; simp; ring⟩
    | smul c v _ hv =>
      obtain ⟨α, hα, β, hβ, rfl⟩ := hv
      exact ⟨algebraMap _ E c * α, int_mul_mem ⟨c, rfl⟩ hα, algebraMap _ E c * β,
        mul_mem ⟨c, rfl⟩ hβ, by ext i; simp [smul_eq]; ring⟩
  · rintro ⟨α, hα, β, hβ, rfl⟩
    have h0 : (α • fun i => P i 0) ∈ frameLat P := Submodule.subset_span ⟨0, α, hα, rfl⟩
    have h1 : (β • fun i => P i 1) ∈ frameLat P :=
      Submodule.subset_span ⟨1, β, (mem_dInv_zero β).2 hβ, rfl⟩
    exact add_mem h0 h1
end GlobalTheory.SgGlob.Inhab
