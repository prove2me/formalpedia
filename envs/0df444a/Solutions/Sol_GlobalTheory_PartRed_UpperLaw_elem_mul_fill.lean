-- Prove2me | solution 1 for GlobalTheory.PartRed.UpperLaw.elem_mul_fill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:24:58.89433+00:00
-- url     : https://prove2.me/submissions/67946a08-453f-4246-91ba-5fc80dc00626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLaw
import Theorems.Thm_GlobalTheory_PartRed_UpperLaw_embA_elem_mul
import Theorems.Thm_GlobalTheory_PartRed_UpperLaw_fill_low

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.UpperLaw
open GlobalTheory.PartRed
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {ρ : ℕ} {I : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))}
namespace GlobalTheory.PartRed.UpperLaw
theorem _root_.solution (l m : Fin c) (i : Fin (c + 1)) (h : l ≠ m) (hmi : m.val = i.val) (hl : l.val < i.val)
    (hi : i.val ≤ ρ) (h1 : transSet ρ ⊆ I) (h2 : (upSet ρ).filter (fun e => i.val < colIx e) ⊆ I)
    (hI : I ⊆ transSet ρ ∪ upSet ρ) (hli : (Sum.inr l, Sum.inr i) ∉ I) (a : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : I → k) :
    (embA n (elem l m h a)).val * fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I x y
      = fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) I (x + Matrix.single (Sum.inr l) (Sum.inr i) a)
          (y + shear ρ I l m a x y) := by
  ext r q
  rw [embA_elem_mul]
  by_cases hr : (r, q) ∈ I
  · conv_rhs => rw [fillAt, Matrix.of_apply, dif_pos hr]
    conv_lhs => enter [1]; rw [fillAt, Matrix.of_apply, dif_pos hr]
    rfl
  · conv_rhs => rw [fillAt, Matrix.of_apply, dif_neg hr]
    conv_lhs => enter [1]; rw [fillAt, Matrix.of_apply, dif_neg hr]
    by_cases hrl : r = Sum.inr l
    · subst hrl
      rw [if_pos rfl]
      have hT : ∀ q : n' ⊕ Fin (c + 1), Free (ρ + 1) ((Sum.inr l, q) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) →
          (∀ j, q = Sum.inr j → ρ < j.val) → (Sum.inr l, q) ∈ I := by
        intro q hq hq'
        apply h1
        simp only [transSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hq, hq'⟩
      rcases q with s | j
      · exact absurd (hT (Sum.inl s) (show l.val + 1 < ρ + 1 by omega) (by simp)) hr
      · have hj : j.val ≤ i.val := by
          by_contra hj
          apply hr
          by_cases hρ : ρ < j.val
          · refine hT _ (show l.val < j.val by omega) ?_
            intro j' e
            cases e
            exact hρ
          · apply h2
            simp only [upSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨l, j, rfl, by omega, by omega⟩, by simp only [colIx, Sum.elim_inr]; omega⟩
        rw [fill_low hI x y m j (by omega) (by omega)]
        by_cases hE : ((Sum.inr l, Sum.inr j) : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) ∈ fixSet ρ ∪ lowSet ρ
        · rw [if_pos hE, if_pos hE]
          have : j.val ≤ l.val := by
            rcases Finset.mem_union.1 hE with h | h
            · simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
              rcases h with ⟨j', e, -, hf⟩ | ⟨_, _, -, -, e⟩
              · have : ¬ (l.val < j.val) := hf
                omega
              · cases e
            · simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
              obtain ⟨l', j', e, -, hf⟩ := h
              cases e
              exact hf
          rw [if_neg (by omega)]
          simp
        · rw [if_neg hE, if_neg hE, Matrix.add_apply]
          congr 1
          by_cases hij : i = j
          · subst hij
            simp [hmi]
          · have : ¬ m.val = j.val := fun e => hij (Fin.ext (by omega))
            simp [this, hij]
    · rw [if_neg hrl, add_zero, Matrix.add_apply, Matrix.single_apply_of_ne _ _ _ _ _ (fun e => hrl e.1.symm), add_zero]
end GlobalTheory.PartRed.UpperLaw
