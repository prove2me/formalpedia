-- Prove2me | solution 1 for MTT.Cohomology.integral_class_character_law
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T04:28:35.256999+00:00
-- url     : https://prove2.me/submissions/84e2ebb1-6a56-4547-be04-77c0959afc2b

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
import Theorems.Thm_MTT_Cohomology_integral_class_character_law_infty

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MCL

variable {N n : ℕ} {R : Type*} [CommRing R]

/-- The cocycle relation at a constant triple forces the diagonal to vanish. -/
theorem diag_zero (φ : Hc N n R) (z : Cusp) : φ.val (z, z) = 0 := by
  have h := φ.2.2.1 z z z
  have h2 : φ.val (z, z) + φ.val (z, z) - φ.val (z, z) = 0 := by rw [h]; simp
  simpa using h2

/-- Every path decomposes through any fixed base cusp. -/
theorem val_sub (φ : Hc N n R) (c a b : Cusp) :
    φ.val (a, b) = φ.val (c, b) - φ.val (c, a) := by
  have h := φ.2.2.1 c a b
  rw [← h]; ring

end P2MCL

open P2MCL in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (φ : Hc N (k-2) ℂ) (hφ : IntegralClass f.form φ)
    (γ : CongruenceSubgroup.Gamma0 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y)
      = ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (x, y)) := by
  have key : ∀ v : Cusp,
      φ.val (cuspAct γ.val OnePoint.infty, cuspAct γ.val v)
        = ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (OnePoint.infty, v)) := by
    intro v
    induction v using OnePoint.rec with
    | infty => rw [diag_zero, diag_zero, map_zero, smul_zero]
    | coe r =>
        exact MTT.Cohomology.integral_class_character_law_infty hN hk ι f φ hφ γ r
  rw [val_sub φ (cuspAct γ.val OnePoint.infty) (cuspAct γ.val x) (cuspAct γ.val y),
      key y, key x, val_sub φ OnePoint.infty x y, map_sub, smul_sub]
