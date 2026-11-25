-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.exists_flip_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:26.835218+00:00
-- url     : https://prove2.me/submissions/e8c31567-75c8-415f-925b-73a832235029

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
import Theorems.Thm_GlobalTheory_SplitFlip_Model_squareFlip_ne_zero
import Theorems.Thm_GlobalTheory_SplitFlip_Grid_IsGood_exists_isAdmissible
import Theorems.Thm_GlobalTheory_SplitFlip_Grid_exists_isGood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip.Model
theorem _root_.solution (t s : ℕ) (ht : Odd t) (hs : Odd s) (a : Assignment) :
    ∃ (G : Grid k) (ϖ : kˣ) (ψ : AddChar k Circle) (S : G.PiLocalization₂), G.m = 1 ∧ G.t = t ∧ G.s = s ∧ G.IsGood ϖ ψ 2 ∧
      S.path = givenPath 1 ∧ S.IsAdmissible a ϖ 2 ∧ PassesThrough 0 0 S.path ∧
      (S.flip a ψ ϖ 2 (0, 0)).path = oppositePath 1 ∧ (S.flip a ψ ϖ 2 (0, 0)).tensor ≠ 0 := by
  obtain ⟨G, ϖ, ψ, hm, hr, ht', hs', hG⟩ := Grid.exists_isGood (k := k) 1 0 t s ht hs
  have hset := hG.square 0 (by omega) 0 (by omega)
  obtain ⟨S, hp, hS, h0⟩ := hG.exists_isAdmissible hset.unif a (γ := givenPath 1) (by unfold IsPath; decide)
    (by rw [hm]; intro b hb; simp [givenPath] at hb; rcases hb with rfl | rfl <;> simp [Edge.InGrid])
  refine ⟨G, ϖ, ψ, S, hm, ht', hs', hG, hp, hS, by rw [hp]; unfold PassesThrough; decide,
    by show flipPath 0 0 S.path = _; rw [hp]; decide, fun H => ?_⟩
  haveI : IsEmpty (Fin (G.rank (0, 0))) := by simp [Grid.rank, hr]; infer_instance
  have hJ : (S.level (0, 0)).map invT = KO k _ := Subsingleton.elim _ _
  have hB : ∀ x, G.sliceB 0 0 S.tensor x = fun _ => 1 := fun x => by
    funext Z
    rw [← h0]
    refine hS.tensor.1 fun b hb => ?_
    rw [hp] at hb
    simp [givenPath] at hb
    rcases hb with rfl | rfl
    · exact Subsingleton.elim _ _
    · ext i j; exact isEmptyElim j
  refine squareFlip_ne_zero hset.unif hset.cond one_le_two (stdSplit (G.rank_square 0 0)) (G.nu 0 0)
    (a.block _ _) (fun _ => 1) one_ne_zero ?_
  funext X
  have := congrFun H (Function.update (Function.update 0 (.ex 0 1) X.toCols₁) (.theta 1 0) X.toCols₂ᵀ)
  simp only [Grid.PiLocalization₂.flip, Grid.flipTensor, hJ, hB] at this
  convert this using 2
  · simp [Grid.joinA]
  · rfl
end GlobalTheory.SplitFlip.Model
