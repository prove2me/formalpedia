-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:55:21.274071+00:00
-- url     : https://prove2.me/submissions/1f6f7fe1-32b5-4ce5-bf85-0e11eed01a76

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}
namespace GlobalTheory.CompanionTheory.PatGrp
theorem _root_.solution (h : IsPat Φ) {N : Matrix ι ι K} (hN : Supp Φ N) : (1 + N).det = 1 := by
  classical
  let b : ι → ℕ := fun i => (Finset.univ.filter fun k => Φ k i).card
  have hb : ∀ i j, Φ i j → b i < b j := by
    intro i j hij
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact h.2 k i j hk hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.1 i
  have hN0 : ∀ i j, b j ≤ b i → N i j = 0 := by
    intro i j hle
    by_contra hne
    exact absurd (hb i j (hN i j hne)) (not_lt.2 hle)
  have hT : (1 + N).BlockTriangular b := by
    intro i j hlt
    have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, hN0 i j hlt.le, add_zero]
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have hblk : (1 + N).toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    show (1 + N) i j = (1 : Matrix {a' // b a' = a} {a' // b a' = a} K) ⟨i, hi⟩ ⟨j, hj⟩
    have hNij : N i j = 0 := hN0 i j (by rw [hi, hj])
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.add_apply, hNij, add_zero, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.add_apply, Matrix.one_apply_ne hij, hNij, add_zero,
        Matrix.one_apply_ne (fun e => hij (congrArg Subtype.val e))]
  rw [hblk, Matrix.det_one]
end GlobalTheory.CompanionTheory.PatGrp
