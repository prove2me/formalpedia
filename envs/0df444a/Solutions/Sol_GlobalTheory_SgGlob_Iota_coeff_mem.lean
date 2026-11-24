-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:20:21.702248+00:00
-- url     : https://prove2.me/submissions/626110a2-98d9-495c-a92a-873543e0d68c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mem_frameLat
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mem_span_frameLat
import Theorems.Thm_GlobalTheory_SgGlob_Iota_mulVec_eq_add

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
    (hind : ∀ a a', P *ᵥ a + P' *ᵥ a' = 0 → a = 0 ∧ a' = 0) {a a' : Fin (r + 1) → E}
    (h : P *ᵥ a + P' *ᵥ a' ∈ Λ) (b : Fin (r + 1)) : a b + a' b ∈ dInv E (r - (b : ℕ)) := by
  have hs : P *ᵥ a + P' *ᵥ a' ∈ Submodule.span E (pairLat g P P' : Set (Fin n → E)) := by
    have h1 (c) : P *ᵥ c ∈ Submodule.span E (pairLat g P P' : Set (Fin n → E)) :=
      Submodule.span_mono (fun _ hx => Submodule.mem_sup_left hx) ((mem_span_frameLat P _).2 ⟨c, rfl⟩)
    rw [mulVec_eq_add hg P P']
    exact add_mem (h1 _) (add_mem (h1 _) (Submodule.smul_mem _ _
      (Submodule.span_mono (fun _ hx => Submodule.mem_sup_right hx)
        ((mem_span_frameLat _ _).2 ⟨a', rfl⟩))))
  obtain ⟨x, hx, y, hy, e⟩ := Submodule.mem_sup.1 (hΛ.2 _ h hs)
  obtain ⟨s, hs, rfl⟩ := (mem_frameLat _ _).1 hx
  obtain ⟨t, -, rfl⟩ := (mem_frameLat _ _).1 hy
  obtain ⟨e1, e2⟩ := hind (s - (g : E)⁻¹ • t - a) ((g : E)⁻¹ • t - a') (by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec] at e
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [← sub_eq_zero.2 e, smul_sub]
    abel)
  have e3 : a b + a' b = s b := by
    have f1 := congrFun e1 b
    have f2 := congrFun e2 b
    simp only [Pi.sub_apply, Pi.zero_apply] at f1 f2
    linear_combination -f1 - f2
  exact e3 ▸ hs b
end GlobalTheory.SgGlob.Iota
