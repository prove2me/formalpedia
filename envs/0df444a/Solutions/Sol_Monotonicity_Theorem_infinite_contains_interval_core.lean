-- Prove2me | solution 1 for Monotonicity_Theorem.infinite_contains_interval_core
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:06:43.33628+00:00
-- url     : https://prove2.me/submissions/d9da8043-2d82-4cc0-b3ab-5147cdc33f82

import Definitions.Def_Monotonicity_Theorem_Framework
open Monotonicity_Theorem
set_option autoImplicit false

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R) (A : Set (Power R 1)) (hDef : FiniteUnionOfPointsAndIntervals D A) (hInf : IsInfinite1 A) : exists a b : Endpoint R, Endpoint.lt D a b ∧ forall x, openInterval D a b x -> A x := by
  induction hDef with
  | empty =>
      have hFin : IsFinite1 (setEmpty : Set (Power R 1)) := by
        use []
        intro x
        constructor
        · intro hx; exact False.elim hx
        · intro hx; cases hx
      exact False.elim (hInf hFin)
  | point p =>
      have hFin : IsFinite1 (pointSet p) := by
        use [p]
        intro x
        constructor
        · intro hx
          change Power.coord1 x = p at hx
          rw [hx]
          exact List.Mem.head _
        · intro hx
          cases hx with
          | head => rfl
          | tail _ h_false => cases h_false
      exact False.elim (hInf hFin)
  | interval a b =>
      cases a with
      | posInf =>
          have hFin : IsFinite1 (openInterval D Endpoint.posInf b) := by
            use []
            intro x
            constructor
            · intro hx; exact False.elim hx.left
            · intro hx; cases hx
          exact False.elim (hInf hFin)
      | negInf =>
          cases b with
          | negInf =>
              have hFin : IsFinite1 (openInterval D Endpoint.negInf Endpoint.negInf) := by
                use []
                intro x
                constructor
                · intro hx; exact False.elim hx.right
                · intro hx; cases hx
              exact False.elim (hInf hFin)
          | finite val_b => exact ⟨Endpoint.negInf, Endpoint.finite val_b, trivial, fun x hx => hx⟩
          | posInf => exact ⟨Endpoint.negInf, Endpoint.posInf, trivial, fun x hx => hx⟩
      | finite val_a =>
          cases b with
          | negInf =>
              have hFin : IsFinite1 (openInterval D (Endpoint.finite val_a) Endpoint.negInf) := by
                use []
                intro x
                constructor
                · intro hx; exact False.elim hx.right
                · intro hx; cases hx
              exact False.elim (hInf hFin)
          | posInf => exact ⟨Endpoint.finite val_a, Endpoint.posInf, trivial, fun x hx => hx⟩
          | finite val_b =>
              by_cases hab : D.lt val_a val_b
              · exact ⟨Endpoint.finite val_a, Endpoint.finite val_b, hab, fun x hx => hx⟩
              ·
                have hFin : IsFinite1 (openInterval D (Endpoint.finite val_a) (Endpoint.finite val_b)) := by
                  use []
                  intro x
                  constructor
                  · intro hx
                    have htrans := D.trans hx.left hx.right
                    exact False.elim (hab htrans)
                  · intro hx; cases hx
                exact False.elim (hInf hFin)
  | union hA hB ihA ihB =>
      rename_i S1 S2
      by_cases hA_inf : IsInfinite1 S1
      · rcases ihA hA_inf with ⟨a, b, hab, hSub⟩
        exact ⟨a, b, hab, fun x hx => Or.inl (hSub x hx)⟩
      · by_cases hB_inf : IsInfinite1 S2
        · rcases ihB hB_inf with ⟨a, b, hab, hSub⟩
          exact ⟨a, b, hab, fun x hx => Or.inr (hSub x hx)⟩
        ·
          have hA_fin : IsFinite1 S1 := Classical.not_not.mp hA_inf
          have hB_fin : IsFinite1 S2 := Classical.not_not.mp hB_inf
          rcases hA_fin with ⟨LA, hLA⟩
          rcases hB_fin with ⟨LB, hLB⟩
          have hUnion_fin : IsFinite1 (setUnion S1 S2) := by
            use LA ++ LB
            intro x
            constructor
            · intro hx
              cases hx with
              | inl hAx => exact List.mem_append.mpr (Or.inl ((hLA x).mp hAx))
              | inr hBx => exact List.mem_append.mpr (Or.inr ((hLB x).mp hBx))
            · intro hx
              cases List.mem_append.mp hx with
              | inl hLAx => exact Or.inl ((hLA x).mpr hLAx)
              | inr hLBx => exact Or.inr ((hLB x).mpr hLBx)
          exact False.elim (hInf hUnion_fin)