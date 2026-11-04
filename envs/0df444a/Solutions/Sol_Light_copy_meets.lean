-- Prove2me | solution 1 for Light.copy_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:08.016026+00:00
-- url     : https://prove2.me/submissions/cd2026cc-0f5f-4d9b-b426-d921c0e8c04e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution {p : ℕ} (hp : P[p]? = some copyBody) {μ : ℕ → ℤ} {src dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space)
    (hsep : Apart src n dst n) :
    Meets lim P p d [(src : ℤ), dst, n] μ (copyTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n :=
  by
  refine
    .of_body hp
      (Ends.pass (fun i => μ (src + i)) (fun i hi => ?_)
        ⟨fun i hi => wrote_done (f := fun i => μ (src + i)) hi, by
          ( try refine _root_.Light.SameOn.cell ?_
            intro x_p2m_2703705270436036299 hx_p2m_2703705270436036299
            first
            | ((  repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_11942631147979316701);
                      (try have := h_p2m_11942631147979316701 x_p2m_2703705270436036299 (by omega));
                      revert h_p2m_11942631147979316701)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            |
              (simp [] at hx_p2m_2703705270436036299;
                ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_13964949475349883320);
                      (try have := h_p2m_13964949475349883320 x_p2m_2703705270436036299 (by omega));
                      revert h_p2m_13964949475349883320)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            | ( ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_8574144571344391899);
                      (try have := h_p2m_8574144571344391899 x_p2m_2703705270436036299 (by omega));
                      revert h_p2m_8574144571344391899)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                            its condition K x does not follow from the hypotheses."))⟩
        hw hdst rfl rfl (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, copyTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [copyTime] <;>
              first
              | omega
              | (ring_nf; omega))))
        -- Round i reads src[i], which no earlier round has written.
        
  have hread : wrote μ dst (fun i => μ (src + i)) i (src + i) = μ (src + i) :=
    wrote_rest
      (by
        have hsep_cases := hsep
        change src + n ≤ dst ∨ dst + n ≤ src at hsep_cases
        rcases hsep_cases with hsep | hsep
        · left; omega
        · right; omega)
  simp [Limits.Addr, abs_le, -abs_mul, hread, wrote] <;> omega
end Light
