-- Prove2me | solution 1 for GlobalTheory.SgGlob.Iota.one_mem_dInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:00:11.032319+00:00
-- url     : https://prove2.me/submissions/56ae6ab7-7003-4090-8e01-9b4c163cbd10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_gq_zero
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_genConf_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
namespace GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
private theorem one_le_inv_differentIdeal :
    (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
  have h := FractionalIdeal.inv_anti_mono (K := E)
    (I := (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) (J := 1)
    (by simp [differentIdeal_ne_bot]) one_ne_zero FractionalIdeal.coeIdeal_le_one
  simpa using h
section Pair
variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
end Pair
section Gram
end Gram
example (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    IsHermU σ (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) E) ∧
      Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] ≠ 0 ∧
      (GenConf (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)]).Nonempty :=
  ⟨⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [cT], by simp [Matrix.det_fin_two]⟩,
    by rw [Inhab.gq_zero]; exact pow_ne_zero _ (Nat.cast_ne_zero.2 hg), _, Inhab.mem_genConf_zero σ hg⟩
end GlobalTheory.SgGlob.Iota
end
end

set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Iota
namespace _root_.GlobalTheory.SgGlob.Iota
theorem _root_.solution (j : ℕ) : (1 : E) ∈ _root_.GlobalTheory.SgGlob.dInv E j := by
  unfold _root_.GlobalTheory.SgGlob.dInv
  have hpow : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ ^ j := by
    simpa using pow_le_pow_left' (one_le_inv_differentIdeal (E := E)) j
  exact hpow (FractionalIdeal.one_mem_one _)
end _root_.GlobalTheory.SgGlob.Iota
end GlobalTheory.SgGlob.Iota
