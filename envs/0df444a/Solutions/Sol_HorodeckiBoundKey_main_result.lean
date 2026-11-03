-- Prove2me | solution 1 for HorodeckiBoundKey.main_result
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T16:18:54.242567+00:00
-- url     : https://prove2.me/submissions/4b3abad1-8258-4bfd-aa96-6cefda5796e2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_finCut
import Definitions.Def_HorodeckiBoundKey_IsSeparable
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_hiding_ppt_region
import Theorems.Thm_HorodeckiBoundKey_near_private_bit_key
import Theorems.Thm_HorodeckiBoundKey_filter_key_rate
import Theorems.Thm_HorodeckiBoundKey_recurrence_output
import Theorems.Thm_HorodeckiBoundKey_corner_trace_norm
import Theorems.Thm_HorodeckiBoundKey_corner_norm_near_half
import Theorems.Thm_HorodeckiBoundKey_separable_no_key
import Theorems.Thm_HorodeckiBoundKey_ppt_undistillable

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (hidingFamily transposeBob Key)
open QAlgorithms.Papers.Independent.Gap48.P42 (distillableKey bipartiteDistillable)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace MainResultAux

open Matrix HorodeckiBoundKey

/-- `J†J ≤ 𝟙` for the repetition decoder on at least one copy. -/
lemma repetitionDecoder_contraction {n : ℕ} (hn : 1 ≤ n) (S : Type) [Fintype S] [DecidableEq S] :
    (1 - (repetitionDecoder n S)ᴴ * repetitionDecoder n S).PosSemidef := by
  classical
  set i0 : Fin n := ⟨0, hn⟩
  have hRR : (repetitionDecoder n S)ᴴ * repetitionDecoder n S =
      Matrix.diagonal (fun x : (Fin n → Fin 2) × (Fin n → S) =>
        if ∀ i, x.1 i = x.1 i0 then (1 : ℂ) else 0) := by
    ext x y
    simp only [Matrix.mul_apply, conjTranspose_apply, repetitionDecoder, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (x.1 i0, x.2)]
    · by_cases hxy : x = y
      · subst hxy
        by_cases hc : ∀ i, x.1 i = x.1 i0 <;> simp [hc]
      · rw [if_neg hxy]
        by_cases h1 : (∀ i, x.1 i = x.1 i0) ∧ x.2 = x.2
        · rw [if_pos h1, star_one, one_mul, if_neg]
          rintro ⟨h2, h3⟩
          apply hxy
          refine Prod.ext (funext fun i => ?_) h3.symm
          rw [h1.1 i, h2 i]
        · rw [if_neg h1, star_zero, zero_mul]
    · intro a _ ha
      by_cases h1 : (∀ i, x.1 i = a.1) ∧ x.2 = a.2
      · exfalso
        apply ha
        exact Prod.ext (h1.1 i0).symm h1.2.symm
      · rw [if_neg h1, star_zero, zero_mul]
    · simp
  rw [hRR, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  refine Matrix.PosSemidef.diagonal fun x => ?_
  split_ifs <;> simp

/-- PPT with respect to Bob (`transposeBob`) gives PPT with respect to Alice across `finCut`. -/
lemma ppt_finCut {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    {ρ : Op (Key 2 × (S × T))} (h : (transposeBob ρ).PosSemidef) :
    (Entanglement.partialTransposeFirst (finCut ρ)).PosSemidef := by
  have e : Entanglement.partialTransposeFirst (finCut ρ) =
      ((finCut (transposeBob ρ))ᵀ) := by
    ext x y
    simp only [Entanglement.partialTransposeFirst, Matrix.of_apply, Matrix.transpose_apply, finCut,
      QAlgorithms.Papers.Independent.Dependency50.P24.partyCut, transposeBob]
  rw [e]
  have h' : (finCut (transposeBob ρ)).PosSemidef := h.submatrix _
  exact h'.transpose

lemma finCut_density' {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    {ρ : Op (Key 2 × (S × T))} (hρ : IsDensityMatrix ρ) : IsDensityMatrix (finCut ρ) := by
  let e : Fin (Fintype.card (Fin 2 × S)) × Fin (Fintype.card (Fin 2 × T)) ≃ Key 2 × (S × T) :=
    ((Fintype.equivFin (Fin 2 × S)).symm.prodCongr (Fintype.equivFin (Fin 2 × T)).symm).trans
      { toFun := fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
        invFun := fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
        left_inv := fun p => rfl
        right_inv := fun p => rfl }
  have hf : finCut ρ = ρ.submatrix e e := rfl
  rw [hf]
  refine ⟨hρ.1.submatrix _, ?_⟩
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e (fun j => ρ j j)]
  exact hρ.2

end MainResultAux

open MainResultAux HorodeckiBoundKey in
theorem solution :
    ∀ p : ℝ, 1 / 4 < p → p ≤ 1 / 3 →
      ∃ l d : ℕ, 1 ≤ l ∧ 2 ≤ d ∧
        IsDensityMatrix (hidingFamily p d l) ∧
        (transposeBob (hidingFamily p d l)).PosSemidef ∧
        ¬ HorodeckiBoundKey.IsSeparable (HorodeckiBoundKey.finCut (hidingFamily p d l)) ∧
        bipartiteDistillable (HorodeckiBoundKey.finCut (hidingFamily p d l)) = 0 ∧
        0 < distillableKey (HorodeckiBoundKey.finCut (hidingFamily p d l)) := by
  intro p hp1 hp2
  obtain ⟨ε₀, hε₀, hkey⟩ := near_private_bit_key
  obtain ⟨n₀, hn₀⟩ := corner_norm_near_half p hp1 (by linarith) ε₀ hε₀
  obtain ⟨l₀, hl₀⟩ := hn₀ (max n₀ 1) (le_max_left _ _)
  have hcorner := hl₀ (max l₀ 1) (le_max_left _ _)
  have hn1 : 1 ≤ max n₀ 1 := le_max_right _ _
  have hl1 : 1 ≤ max l₀ 1 := le_max_right _ _
  obtain ⟨d, hd, hppt⟩ :=
    QAlgorithms.Papers.Independent.Dependency50.P24.hiding_ppt_region.2 p (by linarith) hp2
      (max l₀ 1) hl1
  have hdens : IsDensityMatrix (hidingFamily p d (max l₀ 1)) := by
    have := (QAlgorithms.Papers.Independent.Dependency50.P24.hiding_ppt_region.1 d (max l₀ 1) hd hl1
      p (by linarith) (by linarith)).1
    convert this using 1
  obtain ⟨hfilt, hN, hout⟩ := recurrence_output p d (max l₀ 1) (max n₀ 1) hd hl1 hn1
    (by linarith) (by linarith)
  have hct := corner_trace_norm p d (max l₀ 1) (max n₀ 1) hd hl1 hn1 (by linarith) (by linarith)
  have hK' : 0 < distillableKey (finCut (recurrenceOutput p d (max l₀ 1) (max n₀ 1))) :=
    hkey _ _ (recurrenceOutput p d (max l₀ 1) (max n₀ 1)) hout (by rw [hct]; exact hcorner)
  have hFK := filter_key_rate (hidingFamily p d (max l₀ 1)) hdens (max n₀ 1) hn1
    (repetitionDecoder (max n₀ 1) (Fin (max l₀ 1) → Fin d))
    (repetitionDecoder (max n₀ 1) (Fin (max l₀ 1) → Fin d))
    (repetitionDecoder_contraction hn1 _) (repetitionDecoder_contraction hn1 _)
    (recurrenceNorm p (max n₀ 1)) hN (recurrenceOutput p d (max l₀ 1) (max n₀ 1)) hout hfilt
  have hpos : 0 < ENNReal.ofReal (recurrenceNorm p (max n₀ 1) / (max n₀ 1 : ℕ)) :=
    ENNReal.ofReal_pos.mpr (div_pos hN (by exact_mod_cast hn1))
  have hK : 0 < distillableKey (finCut (hidingFamily p d (max l₀ 1))) :=
    lt_of_lt_of_le (ENNReal.mul_pos hpos.ne' hK'.ne') hFK
  refine ⟨max l₀ 1, d, hl1, hd, hdens, hppt, ?_, ?_, hK⟩
  · intro hsep
    have := separable_no_key _ hsep
    rw [this] at hK
    exact lt_irrefl _ hK
  · exact ppt_undistillable _ (finCut_density' hdens) (ppt_finCut hppt)
