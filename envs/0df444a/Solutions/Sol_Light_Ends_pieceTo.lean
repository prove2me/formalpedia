-- Prove2me | solution 1 for Light.Ends.pieceTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:33:36.746681+00:00
-- url     : https://prove2.me/submissions/b4a4b4ac-1e13-4d94-9bd3-f4aaed7941ef

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_LocalsBut_eq_frame
public import Theorems.Thm_Light_Ends_keeping
public import Theorems.Thm_Light_Ends_mono
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
theorem _root_.solution (xs : List ℕ) (h : Ends lim P d s ⟨frame l, μ⟩ T₁ R)
    (done : ∀ loc' μ', R ⟨loc', μ'⟩ → Q ⟨frame (refreshLocals l loc' xs), μ'⟩) (hxs : s.assigns ⊆ xs := by simp)
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
    Ends lim P d s ⟨frame l, μ⟩ T Q := by
  refine h.keeping.mono hT ?_
  rintro ⟨loc', μ'⟩ ⟨hR, hkeep⟩
  have hloc : LocalsBut xs l loc' := fun y hy => hkeep y fun hmem => hy (hxs hmem)
  rw [hloc.eq_frame]
  exact done loc' μ' hR
end Ends
end Light
