-- Prove2me | solution 1 for Monotonicity_Theorem.exists_uniform_germ_subinterval
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T06:56:37.786633+00:00
-- url     : https://prove2.me/submissions/e1d95111-17fa-4133-9325-cf891083c821

import Theorems.Thm_Monotonicity_Theorem_exists_germ_class_subinterval
import Theorems.Thm_Monotonicity_Theorem_not_uniform_above_above
import Theorems.Thm_Monotonicity_Theorem_not_uniform_below_below

set_option autoImplicit false

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (u v : R) (huv : D.lt u v)
    (hsub : (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I)
    (hinj : ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) :
    ∃ u1 v1 : R, D.lt u1 v1 ∧
      (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset
        (openInterval D (Endpoint.finite u) (Endpoint.finite v)) ∧
      (UniformBelowAbove D f u1 v1 ∨ UniformAboveBelow D f u1 v1) := by
  obtain ⟨u1, v1, h1, hs1, hpat⟩ :=
    Monotonicity_Theorem.exists_germ_class_subinterval D M f u v huv hsub hinj
  have hsub1 : (openInterval D (Endpoint.finite u1) (Endpoint.finite v1)).Subset I :=
    fun _ hx => hsub (hs1 hx)
  have hinj1 : ∀ x (hx : I x), openInterval D (Endpoint.finite u1) (Endpoint.finite v1) x →
      ∀ y (hy : I y), openInterval D (Endpoint.finite u1) (Endpoint.finite v1) y →
        f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y :=
    fun x hx hx1 y hy hy1 he => hinj x hx (hs1 hx1) y hy (hs1 hy1) he
  rcases hpat with hBA | hAB | hAA | hBB
  · exact ⟨u1, v1, h1, hs1, Or.inl hBA⟩
  · exact ⟨u1, v1, h1, hs1, Or.inr hAB⟩
  · exact absurd hAA (fun h =>
      Monotonicity_Theorem.not_uniform_above_above D M f u1 v1 h1 hsub1 hinj1 h)
  · exact absurd hBB (fun h =>
      Monotonicity_Theorem.not_uniform_below_below D M f u1 v1 h1 hsub1 hinj1 h)
