-- Prove2me | solution 1 for Light.MergeSort.body_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:13.984094+00:00
-- url     : https://prove2.me/submissions/6afac186-eec9-4500-9349-fe134fa1dced

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Theorems.Thm_Light_MergeSort_time_split
import Theorems.Thm_Light_MergeSort_sorted_refl
import Theorems.Thm_Light_MergeSort_sorted_merge
import Theorems.Thm_Light_MergeSort_join_ends
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_Seg_congr
import Definitions.Def_WeightedCache3SUM_Alias_11e81edb1af807be
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort
variable {pSort pHalf pMerge pCopy : ℕ}
namespace Light.MergeSort
theorem _root_.solution (C : Procs P pSort pHalf pMerge pCopy) (hw : (lim.space : ℤ) ≤ lim.word)
    (h1 : (1 : ℤ) ≤ lim.word) {d a fr : ℕ} {L : List ℤ} {μ : ℕ → ℤ} (hseg : Seg μ a L) (haf : a + L.length ≤ fr)
    (hfr : fr + L.length ≤ lim.space) (hd : d < lim.depth)
    (ih :
      ∀ (a' : ℕ) (L' : List ℤ) (μ' : ℕ → ℤ),
        1 < L.length →
          2 * L'.length ≤ L.length + 1 →
            Seg μ' a' L' →
              a' + L'.length ≤ fr →
                Meets lim P pSort (d + 1) [L'.length, a', fr] μ' (sortTime L'.length) fun _ => Sorted μ' a' fr L') :
    Ends lim P d (sortBody pSort pHalf pMerge pCopy) ⟨frame [L.length, a, fr], μ⟩ (sortTime L.length) fun σ' =>
      Sorted μ a fr L σ'.mem :=
  by
  -- if 1 < n
  
  refine
    Ends.iteLast (fun hc => ?_) (fun hc => Ends.skip (sorted_refl hseg (by simpa using hc))) (hT := by simp [sortTime])
  have hn : 1 < L.length := by simpa using hc
  have htime := time_split hn
  have hhalf :=
    half_meets (d := d + 1) C.half μ (h := L.length)
      (le_trans (by exact_mod_cast (by omega : L.length + 1 ≤ lim.space)) hw)
  have hlt : (L.length + 1) / 2 < L.length := by omega
  have hpos : 1 ≤ (L.length + 1) / 2 := by omega
  have htwice : 2 * ((L.length + 1) / 2) ≤ L.length + 1 := by omega
  have htwice' : L.length ≤ 2 * ((L.length + 1) / 2) := by omega
  generalize (L.length + 1) / 2 = h at *
  have hl₁ : (L.take h).length = h := by simp; omega
  have hl₂ : (L.drop h).length = L.length - h := by
    simp
      -- h := half(n)
      
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
    | refine _root_.Light.Ends.callToThen (hhalf _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hhalf ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro _ μ₀ ⟨rfl, hμ₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  obtain rfl : μ = μ₀ := hμ₀.symm
  have hsort₁ := ih a (L.take h) μ hn (by omega) (hseg.take h) (by omega)
  rw [hl₁] at hsort₁
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
    | refine _root_.Light.Ends.callToThen (hsort₁ _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsort₁ ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro _ μ₁ ⟨⟨S₁, hS₁, hP₁, hO₁⟩, hk₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hseg₂ : Seg μ₁ (a + h) (L.drop h) :=
    (hseg.drop h).congr fun i hi =>
      hk₁ _
        ⟨by omega, Or.inr (by omega)⟩
          -- sort(n - h, a + h, fr)
          
  have hsort₂ := ih (a + h) (L.drop h) μ₁ hn (by omega) hseg₂ (by omega)
  rw [hl₂] at hsort₂
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
    | refine _root_.Light.Ends.callToThen (hsort₂ _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsort₂ ?_ ?_ ?_ ?_
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
    on_goal -1 => (rintro _ μ₂ ⟨⟨S₂, hS₂, hP₂, hO₂⟩, hk₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hlS₁ := hP₁.length_eq
  have hS₁' : Seg μ₂ a S₁ :=
    hS₁.congr fun i hi =>
      hk₂ _
        ⟨by omega, Or.inl (by omega)⟩
          -- merge and copy
          
  refine
    (join_ends C hw (hP₁.length_eq.trans hl₁) (hP₂.length_eq.trans hl₂) hlt.le hn.le hS₁' hS₂ haf hfr hd).mono
      (by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega)))
      ?_
  rintro _ ⟨μ₃, hk₃, hS₄, hk₄⟩
  exact sorted_merge hlt.le hP₁ hO₁ hk₁ hP₂ hO₂ hk₂ hk₃ hS₄ hk₄
end Light.MergeSort
