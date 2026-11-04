-- Prove2me | solution 1 for Light.Ends.pieceToThen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:34:13.826891+00:00
-- url     : https://prove2.me/submissions/894580c5-0580-4f68-a473-3e65d4f3ed3c

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_Ends_pieceTo
public import Theorems.Thm_Light_Ends_next
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}
namespace Light
namespace Ends
theorem _root_.solution (xs : List ℕ) (h : Ends lim P d s₁ ⟨frame l, μ⟩ T₁ R)
    (rest : ∀ loc' μ', R ⟨loc', μ'⟩ → Ends lim P d s₂ ⟨frame (refreshLocals l loc' xs), μ'⟩ (T - T₁) Q)
    (hxs : s₁.assigns ⊆ xs := by simp)
    (hT : T₁ ≤ T := by
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
    Ends lim P d (_root_.Light.Stmt.seq s₁ s₂) ⟨frame l, μ⟩ T Q :=
  Ends.next T₁ (Ends.pieceTo xs h rest hxs le_rfl) hT
end Ends
end Light
