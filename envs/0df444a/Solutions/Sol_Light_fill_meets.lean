-- Prove2me | solution 1 for Light.fill_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:20:00.072199+00:00
-- url     : https://prove2.me/submissions/7ee5f813-98a6-40f4-bf89-3a2d4a9c7dad

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_seg_wrote
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution {p : ℕ} (hp : P[p]? = some fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    Meets lim P p d [(dst : ℤ), n, x] μ (fillTime n) fun _ μ' =>
      Seg μ' dst (List.replicate n x) ∧ SameOutside μ μ' dst n :=
  .of_body hp
    (Ends.pass (fun _ => x)
      (fun i hi => by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
      ⟨seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_1132823296770828513 hx_p2m_1132823296770828513
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_14502293486340571814);
                    (try have := h_p2m_14502293486340571814 x_p2m_1132823296770828513 (by omega));
                    revert h_p2m_14502293486340571814)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_1132823296770828513;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_15716175634531661341);
                    (try have := h_p2m_15716175634531661341 x_p2m_1132823296770828513 (by omega));
                    revert h_p2m_15716175634531661341)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9316579308682453010);
                    (try have := h_p2m_9316579308682453010 x_p2m_1132823296770828513 (by omega));
                    revert h_p2m_9316579308682453010)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
      hw hdst rfl rfl (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, fillTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [fillTime] <;>
            first
            | omega
            | (ring_nf; omega))))
end Light
