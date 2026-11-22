-- Prove2me | solution 1 for Monotonicity_Theorem.exists_monotone_subinterval
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T06:05:37.971447+00:00
-- url     : https://prove2.me/submissions/fbb73961-34e9-4138-a260-9cb175fd7af0

import Theorems.Thm_Monotonicity_Theorem_constant_or_injective_subinterval
import Theorems.Thm_Monotonicity_Theorem_injective_implies_monotone_subinterval

set_option autoImplicit false

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I) :
    exists u1 v1 : R, D.lt u1 v1 ∧
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) ∧
      (ConstOnInterval f u1 v1 ∨ IncOnInterval f u1 v1 ∨ DecOnInterval f u1 v1) := by
  obtain ⟨u1, v1, h1, hs1, hcase⟩ :=
    Monotonicity_Theorem.constant_or_injective_subinterval D M f u v huv hsub
  rcases hcase with hconst | hinj
  · exact ⟨u1, v1, h1, hs1, Or.inl hconst⟩
  · have hsub1 : (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset I :=
      fun _ hx => hsub (hs1 hx)
    obtain ⟨u2, v2, h2, hs2, hmono⟩ :=
      Monotonicity_Theorem.injective_implies_monotone_subinterval D M f u1 v1 h1 hsub1 hinj
    exact ⟨u2, v2, h2, fun _ hx => hs1 (hs2 hx), Or.inr hmono⟩
