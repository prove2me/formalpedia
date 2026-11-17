-- Prove2me | solution 1 for KeystoneLadder.xPair_double_sameP1
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:24.370217+00:00
-- url     : https://prove2.me/submissions/05070e89-ebe0-4ab9-960a-4cf62ec9c57d

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDiffAddCert
import Definitions.Def_KeystoneDoubling
import Definitions.Def_KeystoneLadder
import Definitions.Def_KeystoneCoprimality
import Definitions.Def_WardSomos
import Theorems.Thm_WeierstrassCurve_dupNumP_eval
import Theorems.Thm_WeierstrassCurve_dupDenP_eval
import Theorems.Thm_WeierstrassCurve_PsiSq_two_mul
import Theorems.Thm_WeierstrassCurve_Phi_two_mul

/-! Proofs of the lemmas stated in `Theorems.Thm_XOnlyLadder_SameProjectivePoint` and their helpers. -/
open Polynomial WeierstrassCurve

open scoped Classical

namespace KeystoneLadder

variable {k : Type*} [Field k]

/-- The x-coordinate doubling fact: `doubleVec (xPair m) ~ xPair (2m)` projectively (c = 1),
from the proven polynomial doubling identities `Phi_two_mul`/`PsiSq_two_mul` evaluated at `x`. -/
theorem _root_.solution (W : WeierstrassCurve k) (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec (XOnly.doubleVec (E := W⁄k) (xPair W m x)) (xPair W (2 * m) x) := by
  refine ⟨1, one_ne_zero, ?_⟩
  funext i
  fin_cases i <;>
    simp only [Pi.smul_apply, smul_eq_mul, one_mul, xPair, XOnly.doubleVec, XOnly.X, XOnly.Z,
      Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [W.Phi_two_mul h4 hψ_ne hc3 m, W.dupNumP_eval]
    simp only [XOnly.dupNumH, WeierstrassCurve.baseChange, WeierstrassCurve.map_b₄,
      WeierstrassCurve.map_b₆, WeierstrassCurve.map_b₈, Algebra.algebraMap_self_apply]
  · rw [W.PsiSq_two_mul h4 hψ_ne hc3 m, W.dupDenP_eval]
    simp only [XOnly.dupDenH, WeierstrassCurve.baseChange, WeierstrassCurve.map_b₂,
      WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, Algebra.algebraMap_self_apply]

end KeystoneLadder

namespace KeystoneLadder

namespace XOnly

open Polynomial

variable {k : Type*} [Field k]

@[simp] public theorem xPair_one_X (W : WeierstrassCurve k) (x : k) :
    X (xPair W 1 x) = x := by
  simp [xPair, X]

@[simp] public theorem xPair_one_Z (W : WeierstrassCurve k) (x : k) :
    Z (xPair W 1 x) = 1 := by
  simp [xPair, Z]

end XOnly

end KeystoneLadder
