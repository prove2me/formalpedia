-- Prove2me | solution 1 for Light.Ends.forScratch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:55.005202+00:00
-- url     : https://prove2.me/submissions/28576b58-fc62-4927-8b9a-2ed06a88fd8f

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_frame_refreshLocals
public import Theorems.Thm_Light_sameFrame_nil
public import Theorems.Thm_Light_sameFrame_cons_cons
public import Theorems.Thm_Light_sameFrame_cons_nil
public import Theorems.Thm_Light_sameFrame_nil_cons
public import Theorems.Thm_Light_Ends_keeping
public import Theorems.Thm_Light_Ends_mono
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil_cons
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}
namespace Light
namespace Ends
theorem _root_.solution {i : ℕ} {hi : Expr} {body : Stmt} (xs : List ℕ) (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ)
    (start : I 0 μ)
    (round :
      ∀ (j : ℕ) (loc' μ' : ℕ → ℤ),
        j < n →
          I j μ' → Ends lim P d body ⟨frame (setLocal (refreshLocals l loc' xs) i j), μ'⟩ b fun σ' => I (j + 1) σ'.mem)
    (done : ∀ loc' μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal (refreshLocals l loc' xs) i n), μ'⟩)
    (bound :
      ∀ (j : ℕ) (loc' μ' : ℕ → ℤ),
        j ≤ n → I j μ' → hi.Gives lim ⟨frame (setLocal (refreshLocals l loc' xs) i j), μ'⟩ n := by
      intros;
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hxs : body.assigns ⊆ xs := by simp) (hcounter : i ∉ xs := by simp) (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by
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
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q :=
  by
  have shape (j : ℕ) {σ : State} (hσ : LocalsBut (i :: xs) l σ.loc) (hj : σ.loc i = j) :
    σ = ⟨frame (setLocal (refreshLocals l σ.loc xs) i j), σ.mem⟩ :=
    by
    refine congrArg (State.mk · σ.mem) (funext fun y => ?_)
    rw [frame_setLocal, frame_refreshLocals]
    split_ifs with hy hy'
    · rw [hy, hj]
    · rfl
    · exact hσ y (by simp [hy, hy'])
  refine
    Ends.for (fun j σ => LocalsBut (i :: xs) l σ.loc ∧ I j σ.mem) n b
      ⟨fun y hy => Function.update_of_ne (by simp at hy; exact hy.1) _ _, start⟩ ?_ ?_ ?_ hn hT
  · rintro j σ hj hc ⟨hσ, hI⟩
    rw [shape j hσ hc]
    refine (round j σ.loc σ.mem hj hI).keeping.mono le_rfl ?_
    rintro σ' ⟨hI', hkeep⟩
    have hsame (y : ℕ) (hy : y ∉ xs) : σ'.loc y = σ.loc y := by rw [hkeep y fun hmem => hy (hxs hmem), ← shape j hσ hc]
    refine ⟨(hsame i hcounter).trans hc, fun y hy => ?_, hI'⟩
    simp only [List.mem_cons, not_or] at hy
    exact ((Function.update_of_ne hy.1 _ _).trans (hsame y hy.2)).trans (hσ y (by simp [hy.1, hy.2]))
  · rintro σ hc ⟨hσ, hI⟩
    rw [shape n hσ hc]
    exact done σ.loc σ.mem hI
  · rintro j σ hj hc ⟨hσ, hI⟩
    rw [shape j hσ hc]
    exact bound j σ.loc σ.mem hj hI
end Ends
end Light
