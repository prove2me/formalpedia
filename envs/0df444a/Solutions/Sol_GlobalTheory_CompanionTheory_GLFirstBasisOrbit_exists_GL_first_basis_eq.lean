-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_GL_first_basis_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:43.402536+00:00
-- url     : https://prove2.me/submissions/daef3882-d568-44e8-aa00-e5fecd92875c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLFirstBasisOrbit
variable {k : Type} [Field k] {n : ℕ}
namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit
theorem _root_.solution (x : Fin (n + 1) → k) (hx : x ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, g.val *ᵥ e0 k n = x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) k := (1 : Matrix _ _ k).updateCol i x
  have hA : A.det = x i := by
    have := Matrix.cramer_apply (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) x i
    rw [← show (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol i x = A from rfl, ← this]
    simp
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) k := A.submatrix id (Equiv.swap 0 i)
  have hG : G.det ≠ 0 := by
    have := Matrix.det_permute' (Equiv.swap 0 i) A
    rw [show G = A.submatrix id (Equiv.swap 0 i) from rfl, this, hA]
    refine mul_ne_zero ?_ hi
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) i)) with h | h <;> rw [h] <;> simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, ?_⟩
  ext a
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, e0, G, A]
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
