-- Prove2me | solution 1 for MSKleene.subst_comp
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T16:12:25.239987+00:00
-- url     : https://prove2.me/submissions/1638d517-516d-4f40-9698-2fe91216f1c7

import Definitions.Def_MSKleene_Subst

open MSKleene
open Classical

theorem subst_comp_point {S : Type} {sig : Signature S} {X : SSet S}
    {u : S} (z : X u) (L L' : Set (Term sig X u)) :
    (∀ {s : S} (P R : Term sig X s),
      R ∈ (show Set (Term sig X s) from
          Term.eval (powerAlgebra (freeAlgebra sig X))
            (substAssign z (substP z L u L')) P) →
      R ∈ substP z L s
        (show Set (Term sig X s) from
          Term.eval (powerAlgebra (freeAlgebra sig X)) (substAssign z L') P)) ∧
    (∀ {w : List S} (ps : TermVec sig X w) (rs : Args (Term sig X) w),
      Args.pmem rs (show Args (fun r => Set (Term sig X r)) w from
        TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
          (substAssign z (substP z L u L')) ps) →
      ∃ qs : Args (Term sig X) w,
        Args.pmem qs (show Args (fun r => Set (Term sig X r)) w from
          TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
            (substAssign z L') ps) ∧
        Args.pmem rs (show Args (fun r => Set (Term sig X r)) w from
          TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
            (substAssign z L) (TermVec.ofArgs qs))) := by
  let motiveT := fun (s : S) (P : Term sig X s) => ∀ R : Term sig X s,
    R ∈ (show Set (Term sig X s) from
        Term.eval (powerAlgebra (freeAlgebra sig X))
          (substAssign z (substP z L u L')) P) →
    R ∈ substP z L s
      (show Set (Term sig X s) from
        Term.eval (powerAlgebra (freeAlgebra sig X)) (substAssign z L') P)
  let motiveV := fun (w : List S) (ps : TermVec sig X w) =>
    ∀ rs : Args (Term sig X) w,
      Args.pmem rs (show Args (fun r => Set (Term sig X r)) w from
        TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
          (substAssign z (substP z L u L')) ps) →
      ∃ qs : Args (Term sig X) w,
        Args.pmem qs (show Args (fun r => Set (Term sig X r)) w from
          TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
            (substAssign z L') ps) ∧
        Args.pmem rs (show Args (fun r => Set (Term sig X r)) w from
          TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
            (substAssign z L) (TermVec.ofArgs qs))
  have ht : ∀ {s : S} (P : Term sig X s), motiveT s P :=
    @Term.rec _ _ _ motiveT motiveV
      (fun {s} x R hR => by
        dsimp [motiveT]
        by_cases h : s = u
        · cases h
          by_cases hx : x = z
          · subst x
            change R ∈ (show Set (Term sig X u) from
              substAssign z (substP z L u L') u z) at hR
            simp [substAssign] at hR
            change R ∈ substP z L u
              (show Set (Term sig X u) from substAssign z L' u z)
            simpa [substAssign] using hR
          · change R ∈ (show Set (Term sig X u) from
              substAssign z (substP z L u L') u x) at hR
            have hRx : R = Term.var x := by
              simpa [substAssign, hx] using hR
            subst R
            unfold substP
            apply Set.mem_iUnion.mpr
            refine ⟨Term.var x, ?_⟩
            apply Set.mem_iUnion.mpr
            refine ⟨?_, ?_⟩
            · change Term.var x ∈
                (show Set (Term sig X u) from substAssign z L' u x)
              simp [substAssign, hx]
            · change Term.var x ∈
                (show Set (Term sig X u) from substAssign z L u x)
              simp [substAssign, hx]
        · change R ∈ (show Set (Term sig X s) from
            substAssign z (substP z L u L') s x) at hR
          have hRx : R = Term.var x := by
            simpa [substAssign, h] using hR
          subst R
          unfold substP
          apply Set.mem_iUnion.mpr
          refine ⟨Term.var x, ?_⟩
          apply Set.mem_iUnion.mpr
          refine ⟨?_, ?_⟩
          · change Term.var x ∈
              (show Set (Term sig X s) from substAssign z L' s x)
            simp [substAssign, h]
          · change Term.var x ∈
              (show Set (Term sig X s) from substAssign z L s x)
            simp [substAssign, h])
      (fun {w} {s} σ ps ih R hR => by
        dsimp [motiveT, motiveV] at ih ⊢
        change R ∈ powerOp (freeAlgebra sig X) σ
          (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
            (substAssign z (substP z L u L')) ps) at hR
        rcases hR with ⟨rs, hrs, rfl⟩
        rcases ih rs hrs with ⟨qs, hqs, hrsL⟩
        unfold substP
        apply Set.mem_iUnion.mpr
        refine ⟨Term.app σ (TermVec.ofArgs qs), ?_⟩
        apply Set.mem_iUnion.mpr
        refine ⟨?_, ?_⟩
        · change Term.app σ (TermVec.ofArgs qs) ∈
            powerOp (freeAlgebra sig X) σ
              (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
                (substAssign z L') ps)
          exact ⟨qs, hqs, rfl⟩
        · change Term.app σ (TermVec.ofArgs rs) ∈
            powerOp (freeAlgebra sig X) σ
              (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
                (substAssign z L) (TermVec.ofArgs qs))
          exact ⟨rs, hrsL, rfl⟩)
      (fun rs hrs => by
        exact ⟨PUnit.unit, trivial, trivial⟩)
      (fun p ps iht ihv rs hrs => by
        rcases rs with ⟨r, rs⟩
        rcases hrs with ⟨hr, hrs⟩
        have hrcomp := iht r hr
        unfold substP at hrcomp
        rcases Set.mem_iUnion.mp hrcomp with ⟨q, hq⟩
        rcases Set.mem_iUnion.mp hq with ⟨hqL', hrL⟩
        rcases ihv rs hrs with ⟨qs, hqsL', hrsL⟩
        exact ⟨(q, qs), ⟨hqL', hqsL'⟩, ⟨hrL, hrsL⟩⟩)
  have hv : ∀ {w : List S} (ps : TermVec sig X w), motiveV w ps :=
    @TermVec.rec _ _ _ motiveT motiveV
      (fun {s} x R hR => by
        dsimp [motiveT]
        by_cases h : s = u
        · cases h
          by_cases hx : x = z
          · subst x
            change R ∈ (show Set (Term sig X u) from
              substAssign z (substP z L u L') u z) at hR
            simp [substAssign] at hR
            change R ∈ substP z L u
              (show Set (Term sig X u) from substAssign z L' u z)
            simpa [substAssign] using hR
          · change R ∈ (show Set (Term sig X u) from
              substAssign z (substP z L u L') u x) at hR
            have hRx : R = Term.var x := by
              simpa [substAssign, hx] using hR
            subst R
            unfold substP
            apply Set.mem_iUnion.mpr
            refine ⟨Term.var x, ?_⟩
            apply Set.mem_iUnion.mpr
            refine ⟨?_, ?_⟩
            · change Term.var x ∈
                (show Set (Term sig X u) from substAssign z L' u x)
              simp [substAssign, hx]
            · change Term.var x ∈
                (show Set (Term sig X u) from substAssign z L u x)
              simp [substAssign, hx]
        · change R ∈ (show Set (Term sig X s) from
            substAssign z (substP z L u L') s x) at hR
          have hRx : R = Term.var x := by
            simpa [substAssign, h] using hR
          subst R
          unfold substP
          apply Set.mem_iUnion.mpr
          refine ⟨Term.var x, ?_⟩
          apply Set.mem_iUnion.mpr
          refine ⟨?_, ?_⟩
          · change Term.var x ∈
              (show Set (Term sig X s) from substAssign z L' s x)
            simp [substAssign, h]
          · change Term.var x ∈
              (show Set (Term sig X s) from substAssign z L s x)
            simp [substAssign, h])
      (fun {w} {s} σ ps ih R hR => by
        dsimp [motiveT, motiveV] at ih ⊢
        change R ∈ powerOp (freeAlgebra sig X) σ
          (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
            (substAssign z (substP z L u L')) ps) at hR
        rcases hR with ⟨rs, hrs, rfl⟩
        rcases ih rs hrs with ⟨qs, hqs, hrsL⟩
        unfold substP
        apply Set.mem_iUnion.mpr
        refine ⟨Term.app σ (TermVec.ofArgs qs), ?_⟩
        apply Set.mem_iUnion.mpr
        refine ⟨?_, ?_⟩
        · change Term.app σ (TermVec.ofArgs qs) ∈
            powerOp (freeAlgebra sig X) σ
              (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
                (substAssign z L') ps)
          exact ⟨qs, hqs, rfl⟩
        · change Term.app σ (TermVec.ofArgs rs) ∈
            powerOp (freeAlgebra sig X) σ
              (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
                (substAssign z L) (TermVec.ofArgs qs))
          exact ⟨rs, hrsL, rfl⟩)
      (fun rs hrs => by
        exact ⟨PUnit.unit, trivial, trivial⟩)
      (fun p ps iht ihv rs hrs => by
        rcases rs with ⟨r, rs⟩
        rcases hrs with ⟨hr, hrs⟩
        have hrcomp := iht r hr
        unfold substP at hrcomp
        rcases Set.mem_iUnion.mp hrcomp with ⟨q, hq⟩
        rcases Set.mem_iUnion.mp hq with ⟨hqL', hrL⟩
        rcases ihv rs hrs with ⟨qs, hqsL', hrsL⟩
        exact ⟨(q, qs), ⟨hqL', hqsL'⟩, ⟨hrL, hrsL⟩⟩)
  exact ⟨ht, hv⟩

theorem solution {S : Type} (sig : Signature S) (X : SSet S) {u s : S}
    (z : X u) (L L' : Set (Term sig X u)) (K : Set (Term sig X s)) :
    substP z (substP z L u L') s K ⊆ substP z L s (substP z L' s K) := by
  intro R hR
  unfold substP at hR ⊢
  rcases Set.mem_iUnion.mp hR with ⟨P, hP⟩
  rcases Set.mem_iUnion.mp hP with ⟨hPK, hPR⟩
  have hpoint := (subst_comp_point z L L').1 P R
  change R ∈ (show Set (Term sig X s) from
    Term.eval (powerAlgebra (freeAlgebra sig X))
      (substAssign z (substP z L u L')) P) at hPR
  have hcomp := hpoint hPR
  unfold substP at hcomp
  rcases Set.mem_iUnion.mp hcomp with ⟨Q, hQ⟩
  rcases Set.mem_iUnion.mp hQ with ⟨hQL', hRQ⟩
  apply Set.mem_iUnion.mpr
  refine ⟨Q, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, hRQ⟩
  apply Set.mem_iUnion.mpr
  refine ⟨P, ?_⟩
  apply Set.mem_iUnion.mpr
  exact ⟨hPK, hQL'⟩
