-- Prove2me | solution 1 for Light.MergeSort.join_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:19.054367+00:00
-- url     : https://prove2.me/submissions/c549100f-1125-4217-beac-04de5137631d

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Theorems.Thm_Light_copy_meets
import Definitions.Def_WeightedCache3SUM_Alias_5f97b32ad428d244
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort
variable {pSort pHalf pMerge pCopy : ℕ}
namespace Light.MergeSort
theorem _root_.solution (C : Procs P pSort pHalf pMerge pCopy) (hw : (lim.space : ℤ) ≤ lim.word) {d a fr h n : ℕ}
    {r : ℤ} {S₁ S₂ : List ℤ} {μ : ℕ → ℤ} (hl₁ : S₁.length = h) (hl₂ : S₂.length = n - h) (hh : h ≤ n) (hn : 1 ≤ n)
    (hS₁ : Seg μ a S₁) (hS₂ : Seg μ (a + h) S₂) (haf : a + n ≤ fr) (hfr : fr + n ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (sortJoin pMerge pCopy) ⟨frame [n, a, fr, h, r], μ⟩ (56 * n + 34) fun σ' =>
      ∃ μ' : ℕ → ℤ, SameOutside μ μ' fr n ∧ Seg σ'.mem a (S₁.merge S₂) ∧ SameOutside μ' σ'.mem a n :=
  by
  have hlm : (S₁.merge S₂).length = n := by
    rw [List.length_merge]
    omega
      -- merge(a, h, a + h, n - h, fr)
      
  have hmerge :=
    merge_meets (d := d + 1) C.merge (a := a) (b := a + h) (dst := fr) (l := S₁) (r := S₂)
      ⟨hw, hS₁, hS₂, by omega, by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
  rw [hl₁, hl₂, show h + (n - h) = n by omega] at hmerge
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hmerge _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hmerge ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 =>
      (rintro _ μ₁
          ⟨hseg, hk₁⟩
              -- copy(fr, a, n)
              ;
        try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((copy_meets C.copy (src := fr) (dst := a) (n := n) hw (by omega) (by omega) (by omega)) _ (by omega)) ?_ ?_
          ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (copy_meets C.copy (src := fr) (dst := a) (n := n) hw (by omega) (by omega) (by omega)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro _ μ₂ ⟨hcopy, hk₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  exact ⟨μ₁, hk₁, fun i hi => (hcopy i (by omega)).trans (hseg i hi), hk₂⟩
end Light.MergeSort
