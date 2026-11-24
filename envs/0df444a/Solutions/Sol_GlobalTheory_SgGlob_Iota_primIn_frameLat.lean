-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.primIn_frameLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:28.576967+00:00
-- url     : https://prove2.me/submissions/3de640de-35a0-409f-9bb5-01c454b96493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mem_frameLat
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mem_span_frameLat
import Theorems.Thm_GlobalTheory_SgGlob_Iota_coeff_mem
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mulVec_mem

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
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
namespace GlobalTheory.SgGlob.Iota
theorem _root_.solution (hg : (g : E) ≠ 0) (hΛ : PrimIn (pairLat g P P') Λ)
    (hind : ∀ a a', P *ᵥ a + P' *ᵥ a' = 0 → a = 0 ∧ a' = 0) :
    PrimIn (frameLat P) Λ ∧ PrimIn (frameLat P') Λ := by
  refine ⟨⟨fun v hv => ?_, fun v hv hs => ?_⟩, fun v hv => ?_, fun v hv hs => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (mem_frameLat _ _).1 hv
    exact (mulVec_mem hg hΛ.1 ha).1
  · obtain ⟨a, rfl⟩ := (mem_span_frameLat _ _).1 hs
    exact (mem_frameLat _ _).2 ⟨a, fun b => by
      simpa using coeff_mem hg hΛ hind (a := a) (a' := 0) (by simpa using hv) b, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := (mem_frameLat _ _).1 hv
    exact (mulVec_mem hg hΛ.1 ha).2.1
  · obtain ⟨a, rfl⟩ := (mem_span_frameLat _ _).1 hs
    exact (mem_frameLat _ _).2 ⟨a, fun b => by
      simpa using coeff_mem hg hΛ hind (a := 0) (a' := a) (by simpa using hv) b, rfl⟩
end GlobalTheory.SgGlob.Iota
