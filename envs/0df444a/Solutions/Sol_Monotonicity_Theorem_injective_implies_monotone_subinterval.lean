-- Prove2me | solution 1 for Monotonicity_Theorem.injective_implies_monotone_subinterval
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T06:38:04.571124+00:00
-- url     : https://prove2.me/submissions/a7ccec49-2c6b-4e18-a650-5d3d91634410

import Theorems.Thm_Monotonicity_Theorem_exists_uniform_germ_subinterval
import Theorems.Thm_Monotonicity_Theorem_increasing_of_uniform_below_above_on_interval
import Theorems.Thm_Monotonicity_Theorem_decreasing_of_uniform_above_below_on_interval

set_option autoImplicit false

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) :
    exists u1 v1 : R, D.lt u1 v1 ∧
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) ∧
      (IncOnInterval f u1 v1 ∨ DecOnInterval f u1 v1) := by
  obtain ⟨u1, v1, h1, hs1, hpat⟩ :=
    Monotonicity_Theorem.exists_uniform_germ_subinterval D M f u v huv hsub hinj
  have hsub1 : (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset I :=
    fun _ hx => hsub (hs1 hx)
  rcases hpat with hBA | hAB
  · exact ⟨u1, v1, h1, hs1,
      Or.inl (Monotonicity_Theorem.increasing_of_uniform_below_above_on_interval
        D M f u1 v1 h1 hsub1 hBA)⟩
  · exact ⟨u1, v1, h1, hs1,
      Or.inr (Monotonicity_Theorem.decreasing_of_uniform_above_below_on_interval
        D M f u1 v1 h1 hsub1 hAB)⟩
