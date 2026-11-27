-- Prove2me | solution 1 for InterpOptStop.SAA.Supplement.lemma_EC_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:53.986978+00:00
-- url     : https://prove2.me/submissions/0b461878-7126-40a4-8ef0-8cc407a784fc

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_Boxes

open InterpOptStop
open InterpOptStop.SAA
open InterpOptStop.SAA.Supplement

theorem solution {n K : ℕ} (X : Set (Fin n → ℝ))
    (a b : Fin K → Fin n → ℝ) :
    ∃ (S : Tree n) (θ : Thresholds), ∀ x ∈ X, policy S θ x = boxesPolicy a b x := by
      classical
      let R : ((Fin n → ℝ) → Act) → Prop :=
        fun f => ∃ (S : Tree n) (θ : Thresholds), ∀ x, policy S θ x = f x
      have hconst (c : Act) : R (fun _ => c) := by
        exact ⟨Tree.leaf c, fun _ => 0, fun _ => rfl⟩
      have hshift : ∀ (S : Tree n) (θ : Thresholds) (p q : List Bool) (x : Fin n → ℝ),
          S.act (fun r => θ (p ++ r)) q x = S.act θ (p ++ q) x := by
        intro S
        induction S with
        | leaf c => intros; rfl
        | split i l r hl hr =>
          intro θ p q x
          simp only [Tree.act, hl, hr, List.append_assoc]
      have hnode (i : Fin n) (t : ℝ) (f g : (Fin n → ℝ) → Act)
          (hf : R f) (hg : R g) :
          R (fun x => if x i ≤ t then f x else g x) := by
        obtain ⟨l, θl, hl⟩ := hf
        obtain ⟨r, θr, hr⟩ := hg
        let θ : Thresholds := fun p => match p with
          | [] => t
          | true :: q => θl q
          | false :: q => θr q
        refine ⟨Tree.split i l r, θ, ?_⟩
        intro x
        have hleft : l.act θ [true] x = f x := by
          have hs := hshift l θ [true] [] x
          simp only [List.append_nil, List.cons_append, List.nil_append, θ] at hs
          exact hs.symm.trans (hl x)
        have hright : r.act θ [false] x = g x := by
          have hs := hshift r θ [false] [] x
          simp only [List.append_nil, List.cons_append, List.nil_append, θ] at hs
          exact hs.symm.trans (hr x)
        change (if x i ≤ t then l.act θ [true] x else r.act θ [false] x) = _
        rw [hleft, hright]
      have hbox (u v : Fin n → ℝ) (f g : (Fin n → ℝ) → Act)
          (hf : R f) (hg : R g) :
          R (fun x => if x ∈ box u v then f x else g x) := by
        have hfinite : ∀ I : Finset (Fin n),
            R (fun x => if ∀ i ∈ I, u i < x i ∧ x i ≤ v i then f x else g x) := by
          intro I
          induction I using Finset.induction_on with
          | empty => simpa using hf
          | @insert i I hi ih =>
            have hu := hnode i (u i) g
              (fun x => if x i ≤ v i then
                (if ∀ j ∈ I, u j < x j ∧ x j ≤ v j then f x else g x)
                else g x) hg
              (hnode i (v i) _ g ih hg)
            convert hu using 1
            funext x
            simp only [Finset.mem_insert, forall_eq_or_imp]
            by_cases hlow : x i ≤ u i
            · simp [hlow, not_lt.mpr hlow]
            · have hlow' : u i < x i := lt_of_not_ge hlow
              by_cases hupp : x i ≤ v i <;> simp [hlow, hlow', hupp]
        convert hfinite Finset.univ using 1
        funext x
        by_cases hx : ∀ i, u i < x i ∧ x i ≤ v i <;> simp [box, hx]
      have hunion : ∀ J : Finset (Fin K),
          R (fun x => if ∃ j ∈ J, x ∈ box (a j) (b j) then Act.stop else Act.go) := by
        intro J
        induction J using Finset.induction_on with
        | empty => simpa using hconst Act.go
        | @insert j J hj ih =>
          have h := hbox (a j) (b j) (fun _ => Act.stop)
            (fun x => if ∃ k ∈ J, x ∈ box (a k) (b k) then Act.stop else Act.go)
            (hconst Act.stop) ih
          convert h using 1
          funext x
          simp only [Finset.mem_insert, exists_eq_or_imp]
          by_cases hx : x ∈ box (a j) (b j) <;> simp [hx]
      obtain ⟨S, θ, h⟩ := hunion Finset.univ
      refine ⟨S, θ, ?_⟩
      intro x hx
      simpa only [Finset.mem_univ, true_and, boxesPolicy] using h x
