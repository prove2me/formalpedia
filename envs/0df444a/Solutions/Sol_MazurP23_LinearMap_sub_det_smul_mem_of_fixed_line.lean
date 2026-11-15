-- Prove2me | solution 1 for MazurP23.LinearMap.sub_det_smul_mem_of_fixed_line
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:32:57.044384+00:00
-- url     : https://prove2.me/submissions/9a89de2e-f820-4ae3-9157-2c5c3eef5bfa

import Mathlib

namespace MazurP23.LinearMap

/-- An endomorphism fixing a line acts on the one-dimensional quotient by its determinant. -/
theorem _root_.solution
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (h2 : Module.finrank F V = 2) (f : V →ₗ[F] V)
    (C : Submodule F V) (hC : Module.finrank F C = 1)
    (hfix : ∀ x ∈ C, f x = x) (x : V) :
    f x - LinearMap.det f • x ∈ C := by
  have : FiniteDimensional F V := Module.finite_of_finrank_pos (by omega)
  have hstable : C ≤ C.comap f := by
    intro y hy
    change f y ∈ C
    rw [hfix y hy]
    exact hy
  have hrestrict : f.restrict hstable = LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact hfix y y.property
  have hquotient : Module.finrank F (V ⧸ C) = 1 := by
    have hd := C.finrank_quotient_add_finrank
    omega
  obtain ⟨a, ha, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hquotient (C.mapQ C f hstable)
  have hdet : LinearMap.det f = a := by
    rw [LinearMap.det_eq_det_mul_det C f hstable, hrestrict, ha]
    simp [LinearMap.det_smul, hquotient]
  rw [← C.ker_mkQ, LinearMap.mem_ker]
  change C.mkQ (f x - LinearMap.det f • x) = 0
  rw [map_sub, map_smul, hdet]
  have haction := congrArg (fun g : (V ⧸ C) →ₗ[F] (V ⧸ C) => g (C.mkQ x)) ha
  simpa using sub_eq_zero.mpr haction

end MazurP23.LinearMap
