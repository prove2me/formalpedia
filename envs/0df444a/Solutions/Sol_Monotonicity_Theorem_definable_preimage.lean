-- Prove2me | solution 1 for Monotonicity_Theorem.definable_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T20:46:37.107668+00:00
-- url     : https://prove2.me/submissions/a1805de4-eb0e-471b-a5e2-15e72813a985

import Definitions.Def_Monotonicity_Theorem_Framework

set_option autoImplicit false

open Monotonicity_Theorem


variable {R : Type}

lemma power1_ext {a b : Power R 1} (h : a 0 = b 0) : a = b := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  exact h

/-- The preimage under a definable function of a definable subset of the codomain is definable. -/
theorem solution (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    {T : Set (Power R 1)} (hT : M.S 1 T) :
    M.S 1 (fun y : Power R 1 => ∃ hy : I y, T (f.toFun (Subtype.mk y hy)).1) := by
  have huniv : M.S 1 (setCompl (setEmpty : Set (Power R 1))) := M.compl_mem (M.empty_mem 1)
  have hP : M.S (1 + 1) (fun z : Power R (1 + 1) =>
      setCompl (setEmpty : Set (Power R 1)) (Power.left z) ∧ T (Power.right z)) :=
    M.product_mem huniv hT
  have hQ : M.S (1 + 1) (setInter (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)
      (fun z : Power R (1 + 1) =>
        setCompl (setEmpty : Set (Power R 1)) (Power.left z) ∧ T (Power.right z))) :=
    M.inter_mem f.graph_mem hP
  have hproj := M.project_mem (1 : Fin (1 + 1)) hQ
  have hEq : (fun y : Power R 1 => ∃ x : Power R (1 + 1),
      setInter (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)
        (fun z : Power R (1 + 1) =>
          setCompl (setEmpty : Set (Power R 1)) (Power.left z) ∧ T (Power.right z)) x ∧
      Power.deleteCoord (1 : Fin (1 + 1)) x = y)
      = (fun y : Power R 1 => ∃ hy : I y, T (f.toFun (Subtype.mk y hy)).1) := by
    funext y
    apply propext
    constructor
    · rintro ⟨z, ⟨⟨hx, hgr⟩, -, hTz⟩, hdel⟩
      have hleft : Power.left z = y := by
        apply power1_ext
        have : (Power.deleteCoord (1 : Fin (1 + 1)) z) 0 = y 0 := by rw [hdel]
        exact this
      have hy : I y := hleft ▸ hx
      refine ⟨hy, ?_⟩
      have hsub : (Subtype.mk y hy : {x : Power R 1 // I x}) = Subtype.mk (Power.left z) hx :=
        Subtype.ext hleft.symm
      have hval : (f.toFun (Subtype.mk y hy)).1 = Power.right z := by
        rw [hgr, hsub]
      rw [hval]
      exact hTz
    · rintro ⟨hy, hTy⟩
      refine ?_
      let z : Power R (1 + 1) :=
        fun i => if i.val = 0 then y 0 else (f.toFun (Subtype.mk y hy)).1 0
      have hleft : Power.left z = y := power1_ext rfl
      have hright : Power.right z = (f.toFun (Subtype.mk y hy)).1 := power1_ext rfl
      have hIz : I (Power.left z) := by rw [hleft]; exact hy
      refine ⟨z, ⟨⟨hIz, ?_⟩, ⟨fun h => False.elim h, ?_⟩⟩, power1_ext rfl⟩
      · have hsub : (Subtype.mk y hy : {x : Power R 1 // I x}) = Subtype.mk (Power.left z) hIz :=
          Subtype.ext hleft.symm
        rw [hright, hsub]
      · rw [hright]
        exact hTy
  rw [hEq] at hproj
  exact hproj

