-- Prove2me | solution 1 for Light.powTable_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:33.074021+00:00
-- url     : https://prove2.me/submissions/6b00f435-8537-46bd-b3b0-22f0d6e5a8e1

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Int.SuccPred
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
public import Theorems.Thm_Light_length_powList
public import Theorems.Thm_Light_getElem_powList
public import Theorems.Thm_Light_LocalsBut_update
public import Theorems.Thm_Light_SameOn_refl
public import Theorems.Thm_Light_SameOutside2_refl
public import Theorems.Thm_Light_SameOutside_refl
public import Theorems.Thm_Light_sameFrame_cons_cons
public import Theorems.Thm_Light_sameFrame_cons_nil
public import Theorems.Thm_Light_sameFrame_nil
public import Theorems.Thm_Light_sameFrame_nil_cons
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] Light.length_powList
attribute [local simp] Light.getElem_powList
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open PowTable
namespace Light
theorem _root_.solution {μ : ℕ → ℤ} {dst L b : ℕ} (e p : ℤ) (t : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst + L ≤ lim.space) (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d powTableBody ⟨frame (dst :: L :: b :: e :: p :: t), μ⟩ (powTableTime L) fun σ' =>
      Seg σ'.mem dst (powList b L) ∧ SameOutside μ σ'.mem dst L :=
  by
  have h1 : (1 : ℤ) ≤ lim.word := by simpa using hpow 0 (Nat.zero_le _)
  unfold powTableBody powTableTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine
      _root_.Light.Ends.setToThen
        1
          -- for j < L
          
        ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.for (Filled μ dst L b t) L powTableRound.blockCost ?start ?round ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, powTableRound]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [powTableRound] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start => exact ⟨μ, by simp [update_frame_setLocal], fun i hi => absurd hi (by omega), .refl⟩
  case bound =>
    rintro j _ - - ⟨μ', rfl, -⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case done =>
    rintro _ - ⟨μ', rfl, powers, same⟩
    exact ⟨fun i hi => by rw [getElem_powList]; exact powers i (by simpa using hi), same⟩
  case round =>
    rintro j _ hj - ⟨μ', rfl, powers, same⟩
    have hfits : (b : ℤ) ^ (j + 1) ≤ lim.word := by exact_mod_cast hpow (j + 1) (by omega)
    have hnonneg : 0 ≤ (b : ℤ) ^ (j + 1) := by positivity
    unfold powTableRound
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine
        _root_.Light.Ends.storeToThen (dst + j)
          (b ^ j : ℕ)
            -- p := p * b
            
          ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (b ^ (j + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ← pow_succ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [← pow_succ] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ← pow_succ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, Function.update μ' (dst + j) (b ^ j : ℕ), by simp [update_frame_setLocal], fun i hi => ?_, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_14373936225166793766 hx_p2m_14373936225166793766
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_4739198435379076829);
                    (try have := h_p2m_4739198435379076829 x_p2m_14373936225166793766 (by omega));
                    revert h_p2m_4739198435379076829)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_14373936225166793766;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_116123989352023125);
                    (try have := h_p2m_116123989352023125 x_p2m_14373936225166793766 (by omega));
                    revert h_p2m_116123989352023125)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_1486791567891234285);
                    (try have := h_p2m_1486791567891234285 x_p2m_14373936225166793766 (by omega));
                    revert h_p2m_1486791567891234285)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
    obtain hi | rfl := Nat.lt_succ_iff_lt_or_eq.1 hi
    · rw [Function.update_of_ne (by omega)]
      exact powers i hi
    · exact Function.update_self ..
end Light
