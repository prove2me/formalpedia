-- Prove2me | solution 1 for Light.Ends.pass_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:59.430663+00:00
-- url     : https://prove2.me/submissions/1203395c-cfd0-4d7f-803a-873ff8aece57

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Pass
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_Light_Ends_forMem
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_succ
import Theorems.Thm_Light_wrote_zero
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}
namespace Light
namespace Ends
theorem _root_.solution {c x y n T : ℕ} {e : Expr} {loc : ℕ → ℤ} {Q : State → Prop} (f : ℕ → ℤ)
    (round :
      ∀ j < n,
        e.Safe lim ⟨Function.update loc c j, wrote μ dst f j⟩ ∧ e.val ⟨Function.update loc c j, wrote μ dst f j⟩ = f j)
    (done : Q ⟨Function.update loc c n, wrote μ dst f n⟩) (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space)
    (hlen : loc x = n) (haddr : loc y = dst) (hx : x ≠ c := by decide) (hy : y ≠ c := by decide)
    (hT : n * (e.cost + 12) + 6 ≤ T := by
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
            | (ring_nf; omega))) :
    Ends lim P d (pass c (v x) (v y) e) ⟨loc, μ⟩ T Q :=
  by
  refine
    Ends.forMem (fun j μ' => μ' = wrote μ dst f j) n _ wrote_zero.symm (fun j μ' hj hμ' => Ends.block ?round le_rfl)
      (fun μ' h => by rw [h]; exact done) (fun j μ' _ _ => ⟨trivial, (Function.update_of_ne hx _ _).trans hlen⟩)
      (by omega)
      (le_trans (le_of_eq (by simp only [Stmt.blockCost, Expr.cost]; ring)) hT)
        -- Round j: dst[j] := e.
        
  subst hμ'
  obtain ⟨hs, hv⟩ := round j hj
  have qc : Function.update loc c (j : ℤ) c = j := Function.update_self ..
  have qy : Function.update loc c (j : ℤ) y = dst := by rw [Function.update_of_ne hy, haddr]
  refine ⟨⟨?_, hs, ?_⟩, rfl, ?_⟩
  · simp only [Expr.Safe, Expr.val, Op.eval, qc, qy, true_and, abs_le]
    omega
  · simp only [Expr.val, Op.eval, qc, qy, Limits.Addr]
    omega
  · simp only [Stmt.after, Expr.val, Op.eval, qc, qy, hv, toNat_natCast_add_natCast, wrote_succ]
end Ends
end Light
