-- Prove2me | solution 1 for Monotonicity_Theorem.compl_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:06:39.920376+00:00
-- url     : https://prove2.me/submissions/94ebb95d-e2d3-4f72-8212-741f3cbc630b

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {A : Set (Power R 1)}
    (hA : M.S 1 A) :
    M.S 1 (fun x : Power R 1 => ¬ A x) := by
  obtain hFUI := (M.ominimal A).mp hA
  clear hA
  induction hFUI with
  | empty =>
    have hU : M.S 1 (openInterval D (Endpoint.negInf) (Endpoint.posInf)) :=
      (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
    have heq : (fun x : Power R 1 => ¬ (fun _ => False) x)
        = openInterval D Endpoint.negInf Endpoint.posInf := by
      funext x
      apply propext
      constructor
      · intro _
        show Endpoint.lt D Endpoint.negInf (Endpoint.finite (x 0)) ∧
          Endpoint.lt D (Endpoint.finite (x 0)) Endpoint.posInf
        exact ⟨trivial, trivial⟩
      · intro _ hE
        exact hE
    rw [heq]
    exact hU
  | point p =>
    have hL : M.S 1 (openInterval D Endpoint.negInf (Endpoint.finite p)) :=
      (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
    have hR : M.S 1 (openInterval D (Endpoint.finite p) Endpoint.posInf) :=
      (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
    have heq : (fun x : Power R 1 => ¬ pointSet p x)
        = setUnion (openInterval D Endpoint.negInf (Endpoint.finite p))
          (openInterval D (Endpoint.finite p) Endpoint.posInf) := by
      funext x
      apply propext
      constructor
      · intro h
        rcases D.trichotomy (x 0) p with ⟨hlt, _, _⟩ | ⟨heq2, _, _⟩ | ⟨hlt, _, _⟩
        · exact Or.inl ⟨trivial, hlt⟩
        · exact absurd heq2 h
        · exact Or.inr ⟨hlt, trivial⟩
      · intro h hpx
        have hpx' : x 0 = p := hpx
        cases h with
        | inl hL =>
          have hL' : D.lt (x 0) p := hL.right
          rw [hpx'] at hL'
          exact D.irrefl p hL'
        | inr hR =>
          have hR' : D.lt p (x 0) := hR.left
          rw [hpx'] at hR'
          exact D.irrefl p hR'
    rw [heq]
    exact M.union_mem hL hR
  | interval a b =>
    cases a with
    | negInf =>
      cases b with
      | negInf =>
        have hU : M.S 1 (openInterval D (Endpoint.negInf) (Endpoint.posInf)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have heq : (fun x : Power R 1 => ¬ openInterval D Endpoint.negInf Endpoint.negInf x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            show Endpoint.lt D Endpoint.negInf (Endpoint.finite (x 0)) ∧
              Endpoint.lt D (Endpoint.finite (x 0)) Endpoint.posInf
            exact ⟨trivial, trivial⟩
          · intro _ hE
            unfold openInterval Endpoint.lt at hE
            exact hE.right
        rw [heq]
        exact hU
      | finite v =>
        have hIv : M.S 1 (openInterval D (Endpoint.finite v) Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have hPt : M.S 1 (pointSet v) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point v)
        have heq : (fun x : Power R 1 => ¬ openInterval D Endpoint.negInf (Endpoint.finite v) x)
            = setUnion (openInterval D (Endpoint.finite v) Endpoint.posInf)
              (pointSet v) := by
          funext x
          apply propext
          constructor
          · intro h
            rcases D.trichotomy (x 0) v with ⟨hlt, _, _⟩ | ⟨heq2, _, _⟩ | ⟨hlt, _, _⟩
            · exact absurd ⟨trivial, hlt⟩ h
            · exact Or.inr heq2
            · exact Or.inl ⟨hlt, trivial⟩
          · intro h hI
            have hIr : D.lt (x 0) v := hI.right
            cases h with
            | inl hR =>
              have g1 : D.lt v (x 0) := hR.left
              exact D.irrefl v (D.trans g1 hIr)
            | inr heq2 =>
              have heq2' : x 0 = v := heq2
              rw [heq2'] at hIr
              exact D.irrefl v hIr
        rw [heq]
        exact M.union_mem hIv hPt
      | posInf =>
        have heq : (fun x : Power R 1 => ¬ openInterval D Endpoint.negInf Endpoint.posInf x)
            = (setEmpty : Set (Power R 1)) := by
          funext x
          apply propext
          constructor
          · intro h
            exact absurd ⟨trivial, trivial⟩ h
          · intro h
            unfold setEmpty at h
            cases h
        rw [heq]
        exact M.empty_mem 1
    | finite u =>
      cases b with
      | negInf =>
        have hU : M.S 1 (openInterval D (Endpoint.negInf) (Endpoint.posInf)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have heq : (fun x : Power R 1 => ¬ openInterval D (Endpoint.finite u) Endpoint.negInf x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            show Endpoint.lt D Endpoint.negInf (Endpoint.finite (x 0)) ∧
              Endpoint.lt D (Endpoint.finite (x 0)) Endpoint.posInf
            exact ⟨trivial, trivial⟩
          · intro _ hE
            unfold openInterval Endpoint.lt at hE
            exact hE.right
        rw [heq]
        exact hU
      | finite v =>
        have hL : M.S 1 (openInterval D Endpoint.negInf (Endpoint.finite u)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have hPtu : M.S 1 (pointSet u) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point u)
        have hPtv : M.S 1 (pointSet v) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point v)
        have hR : M.S 1 (openInterval D (Endpoint.finite v) Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have heq : (fun x : Power R 1 => ¬ openInterval D (Endpoint.finite u) (Endpoint.finite v) x)
            = setUnion (setUnion (openInterval D Endpoint.negInf (Endpoint.finite u)) (pointSet u))
              (setUnion (pointSet v) (openInterval D (Endpoint.finite v) Endpoint.posInf)) := by
          funext x
          apply propext
          constructor
          · intro h
            rcases D.trichotomy u (x 0) with ⟨hlt, _, _⟩ | ⟨heq2, _, _⟩ | ⟨hlt, _, _⟩
            · rcases D.trichotomy (x 0) v with ⟨h1, _, _⟩ | ⟨h2, _, _⟩ | ⟨h3, _, _⟩
              · exact absurd ⟨hlt, h1⟩ h
              · exact Or.inr (Or.inl h2)
              · exact Or.inr (Or.inr ⟨h3, trivial⟩)
            · exact Or.inl (Or.inr heq2.symm)
            · exact Or.inl (Or.inl ⟨trivial, hlt⟩)
          · intro h hI
            have hI1 : D.lt u (x 0) := hI.left
            have hI2 : D.lt (x 0) v := hI.right
            cases h with
            | inl hL =>
              cases hL with
              | inl hLi =>
                have g : D.lt (x 0) u := hLi.right
                exact D.irrefl u (D.trans hI1 g)
              | inr heq2 =>
                have heq2' : x 0 = u := heq2
                rw [heq2'] at hI1
                exact D.irrefl u hI1
            | inr hR =>
              cases hR with
              | inl heq2 =>
                have heq2' : x 0 = v := heq2
                rw [heq2'] at hI2
                exact D.irrefl v hI2
              | inr hRi =>
                have g : D.lt v (x 0) := hRi.left
                exact D.irrefl v (D.trans g hI2)
        rw [heq]
        exact M.union_mem (M.union_mem hL hPtu) (M.union_mem hPtv hR)
      | posInf =>
        have hL : M.S 1 (openInterval D Endpoint.negInf (Endpoint.finite u)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have hPt : M.S 1 (pointSet u) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point u)
        have heq : (fun x : Power R 1 => ¬ openInterval D (Endpoint.finite u) Endpoint.posInf x)
            = setUnion (openInterval D Endpoint.negInf (Endpoint.finite u)) (pointSet u) := by
          funext x
          apply propext
          constructor
          · intro h
            rcases D.trichotomy (x 0) u with ⟨hlt, _, _⟩ | ⟨heq2, _, _⟩ | ⟨hlt, _, _⟩
            · exact Or.inl ⟨trivial, hlt⟩
            · exact Or.inr heq2
            · exact absurd ⟨hlt, trivial⟩ h
          · intro h hI
            have hI1 : D.lt u (x 0) := hI.left
            cases h with
            | inl hLi =>
              have g : D.lt (x 0) u := hLi.right
              exact D.irrefl u (D.trans hI1 g)
            | inr heq2 =>
              have heq2' : x 0 = u := heq2
              rw [heq2'] at hI1
              exact D.irrefl u hI1
        rw [heq]
        exact M.union_mem hL hPt
    | posInf =>
      cases b with
      | negInf =>
        have hU : M.S 1 (openInterval D (Endpoint.negInf) (Endpoint.posInf)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have heq : (fun x : Power R 1 => ¬ openInterval D Endpoint.posInf Endpoint.negInf x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            show Endpoint.lt D Endpoint.negInf (Endpoint.finite (x 0)) ∧
              Endpoint.lt D (Endpoint.finite (x 0)) Endpoint.posInf
            exact ⟨trivial, trivial⟩
          · intro _ hE
            unfold openInterval Endpoint.lt at hE
            exact hE.left
        rw [heq]
        exact hU
      | finite v =>
        have hU : M.S 1 (openInterval D (Endpoint.negInf) (Endpoint.posInf)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have heq : (fun x : Power R 1 => ¬ openInterval D Endpoint.posInf (Endpoint.finite v) x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            show Endpoint.lt D Endpoint.negInf (Endpoint.finite (x 0)) ∧
              Endpoint.lt D (Endpoint.finite (x 0)) Endpoint.posInf
            exact ⟨trivial, trivial⟩
          · intro _ hE
            unfold openInterval Endpoint.lt at hE
            exact hE.left
        rw [heq]
        exact hU
      | posInf =>
        have hU : M.S 1 (openInterval D (Endpoint.negInf) (Endpoint.posInf)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
        have heq : (fun x : Power R 1 => ¬ openInterval D Endpoint.posInf Endpoint.posInf x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            show Endpoint.lt D Endpoint.negInf (Endpoint.finite (x 0)) ∧
              Endpoint.lt D (Endpoint.finite (x 0)) Endpoint.posInf
            exact ⟨trivial, trivial⟩
          · intro _ hE
            unfold openInterval Endpoint.lt at hE
            exact hE.left
        rw [heq]
        exact hU
  | union =>
    rename_i A B hFA hFB ihA ihB
    have heq : (fun x : Power R 1 => ¬ (A x ∨ B x))
        = setInter (fun x : Power R 1 => ¬ A x) (fun x : Power R 1 => ¬ B x) := by
      funext x
      apply propext
      constructor
      · intro h
        exact ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩
      · intro h hAB
        cases hAB with
        | inl ha => exact h.left ha
        | inr hb => exact h.right hb
    show M.S 1 (fun x : Power R 1 => ¬ (A x ∨ B x))
    rw [heq]
    exact M.inter_mem ihA ihB
