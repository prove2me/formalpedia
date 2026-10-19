-- Prove2me | solution 1 for MIPRE.QLD.Honest.answerOp_con_var_reject
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:16:08.732606+00:00
-- url     : https://prove2.me/submissions/bd2e80a7-40fa-4fb3-9782-484ddc38115f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/HonestPauliEdges.lean (solution of MIPRE.QLD.Honest.answerOp_con_var_reject);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_constraint_disagreement
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_constraint_wrong_parity
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one
import Theorems.Thm_MIPRE_Weyl_eq_sum_proj
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ
import Theorems.Thm_MIPRE_Weyl_proj_mul_proj
import Theorems.Thm_MIPRE_Weyl_sum_proj
import Theorems.Thm_MIPRE_Weyl_wX_mul_wZ
import Theorems.Thm_MIPRE_star_sgn

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The anticommuting case: when the form is nonzero the two operators anticommute. -/
theorem wX_mul_wZ_of_ne (a b : n → F) (h : trDot a b = 1) :
    wX a * wZ b = -(wZ b * wX a) := by
  rw [wX_mul_wZ, h, sgn_one, neg_one_smul]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The defining Fourier average, as a rewrite. -/
theorem proj_def (w : (n → F) → Matrix (n → F) (n → F) ℂ) (e : n → F) :
    proj w e = (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • w a := rfl
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- The projectors are self-adjoint. -/
theorem proj_conjTranspose (hw : IsWeylFamily w) (e : n → F) : (proj w e)ᴴ = proj w e := by
  classical
  rw [proj_def w e, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [Matrix.conjTranspose_smul, hw.selfAdjoint a, star_sgn]]
  congr 1
  simp
end
end MIPRE.Weyl

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  h.coarse e
end
end MIPRE

namespace MIPRE.LCS
section
/-- The `ZMod 2` counterpart of `Fin.sum_univ_two`. -/
lemma sum_univ_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ x, f x = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
end
end MIPRE.LCS

namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
omit [Algebra ℂ R] in
lemma isObservable_observableOfMeasurementSystem
  (f : ZMod 2 → R) (h : IsMeasurementSystem f) :
  IsObservable (observableOfMeasurementSystem f) where
  involutive := by
    dsimp [observableOfMeasurementSystem]
    rw [sub_mul, mul_sub, mul_sub, h.idempotent 0, h.idempotent 1]
    rw [h.orthogonal 0 1 (by decide), h.orthogonal 1 0 (by decide)]
    rw [sub_zero, zero_sub, sub_neg_eq_add]
    exact (sum_univ_zmod_two f).symm.trans h.sum_one
  self_adjoint := by
    dsimp [observableOfMeasurementSystem]
    rw [star_sub, h.self_adjoint 0, h.self_adjoint 1]
end
end MIPRE.LCS

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem cell_cellIdx {c : Fin layout.r} {j : Fin layout.s} (h : j ∈ layout.V c) :
    cell c (cellIdx c j) = j := by
  revert h; revert j; revert c; decide
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
/-- Both parts of the actual Magic Square incidence check are enforced. -/
theorem constraint_reject_zero {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (a : Fin 3 → ZMod 2) (j : Fin 3) (b : ZMod 2)
    (hr : ¬ (a 0 + a 1 + a 2 = game.b c ∧ a j = b)) :
    constraintOp A B c a * variableOp A B (cellIndex c j) b = 0 := by
  by_cases hp : a 0 + a 1 + a 2 = game.b c
  · exact constraint_disagreement hA hB hAB c a j b (fun h => hr ⟨hp, h⟩)
  · rw [constraint_wrong_parity hA hB hAB c a hp, zero_mul]
end
end MIPRE.Introspection.HonestMagicSquare

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem basis_isWeyl (W : Bas) : IsWeylFamily (basis (F := F) (m := m) W) := by
  cases W
  · exact isWeylFamily_wX
  · exact isWeylFamily_wZ
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem pauliOp_isPVM (W : Bas) : IsPVM (pauliOp (F := F) (m := m) W) where
  isSelfAdjoint := proj_conjTranspose (basis_isWeyl W)
  idem h := by rw [pauliOp, proj_mul_proj (basis_isWeyl W), if_pos rfl]
  sum_eq_one := sum_proj (basis_isWeyl W)
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
omit [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] in
theorem eval_ldEnc_dot (h : Register F m) (u : LIDT.Point F m) :
    MvPolynomial.eval u (LowDegree.ldEnc h) = ∑ y, h y * LowDegree.indVec u y := by
  simp [LowDegree.ldEnc, LowDegree.indVec]
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
omit [Fintype F] [DecidableEq F] in
theorem probeVector_trace (ω : Omega F m) (W : Bas) (h : Register F m) :
    trDot (probeVector ω W) h = probeLabel ω W h := by
  unfold probeLabel prb trDot probeVector
  rw [eval_ldEnc_dot, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probeOp_isPVM (ω : Omega F m) (W : Bas) : IsPVM (probeOp ω W) :=
  isPVM_fibSum (pauliOp_isPVM W) _
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
/-- The actual verifier probe is the binary spectral measurement of this Weyl operator. -/
theorem probe_observable (ω : Omega F m) (W : Bas) :
    observableOfMeasurementSystem (probeOp ω W) = basis W (probeVector ω W) := by
  rw [eq_sum_proj (w := basis W) (probeVector ω W)]
  simp only [probeVector_trace]
  have h := signed_fibre (pauliOp W) (probeLabel ω W)
  rw [sum_univ_zmod_two] at h
  simpa only [sgn_zero, sgn_one, one_smul, neg_smul, sub_eq_add_neg,
    probeOp, observableOfMeasurementSystem, pauliOp] using h
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probeOp_isMeasurementSystem (ω : Omega F m) (W : Bas) :
    IsMeasurementSystem (probeOp ω W) where
  sum_one := (probeOp_isPVM ω W).sum_eq_one
  idempotent := (probeOp_isPVM ω W).idem
  orthogonal _ _ hab := (probeOp_isPVM ω W).orthogonal hab
  self_adjoint := (probeOp_isPVM ω W).isSelfAdjoint
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probe_basis_isObservable (ω : Omega F m) (W : Bas) :
    IsObservable (basis W (probeVector ω W)) := by
  rw [← probe_observable]
  exact isObservable_observableOfMeasurementSystem _ (probeOp_isMeasurementSystem ω W)
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
omit [Fintype F] [DecidableEq F] in
/-- The phase tested by the verifier is precisely the Pauli commutation phase. -/
theorem probe_phase (ω : Omega F m) :
    trDot (probeVector ω .X) (probeVector ω .Z) = gam ω := by
  unfold trDot probeVector gam LowDegree.acGamma LowDegree.indPair
  congr 1
  simp only [Omega.r, Omega.pt, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Weyl LCS
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
theorem probe_basis_anticommute (ω : Omega F m) (h : gam ω ≠ 0) :
    basis .X (probeVector ω .X) * basis .Z (probeVector ω .Z) =
      -(basis .Z (probeVector ω .Z) * basis .X (probeVector ω .X)) := by
  apply wX_mul_wZ_of_ne
  rw [probe_phase]
  rcases zmod_two_eq_zero_or_one (gam ω) with h0 | h1
  · exact (h h0).elim
  · exact h1
end
end MIPRE.QLD.Honest

namespace MIPRE.QLD.Honest
noncomputable section
open Matrix Finset Introspection Classical
open scoped Kronecker
variable {I X Y A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B]
omit [DecidableEq I] in
theorem fibre_reject (M : X → Matrix I I ℂ) (N : Y → Matrix I I ℂ)
    (f : X → A) (g : Y → B) (D : A → B → Bool)
    (hz : ∀ x y, D (f x) (g y) = false → M x * N y = 0)
    (a : A) (b : B) (hr : D a b = false) : fibSum M f a * fibSum N g b = 0 := by
  unfold fibSum
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro y hy
  exact hz x y (by simpa only [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2] using hr)
end
end MIPRE.QLD.Honest

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.Honest
open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {m d : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (ω : Omega F m)
    (c : Fin LCS.MagicSquare.layout.r) (j : Fin LCS.MagicSquare.layout.s)
    (hj : j ∈ LCS.MagicSquare.layout.V c) (a b : Answer F m d)
    (hr : accepts hm (.con c ω) (.var j ω) a b = false) :
    answerOp hm (.con c ω) a * answerOp hm (.var j ω) b = 0 := by
  simp only [answerOp]
  apply fibre_reject _ _ _ _ (accepts hm (.con c ω) (.var j ω)) _ a b hr
  intro x y hxy
  by_cases h : gam ω = 0
  · simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h] at hxy
  · simp only [constraintBranch, variableBranch, if_neg h]
    have hb : ¬ (x 0 + x 1 + x 2 = LCS.MagicSquare.game.b c ∧ x (LCS.MagicSquare.cellIdx c j) = y) := by
      intro hh
      have ht : accepts (d := d) hm (.con c ω) (.var j ω) (.bitTriple x) (.bit y) = true := by
        simp [accepts, subtests, Question.ty, Question.fmtOk, pairTest, h, hj,
          Fin.sum_univ_three, hh.1, hh.2]
      rw [ht] at hxy
      contradiction
    have hh := HonestMagicSquare.constraint_reject_zero (probe_basis_isObservable ω .X)
      (probe_basis_isObservable ω .Z) (probe_basis_anticommute ω h)
      c x (LCS.MagicSquare.cellIdx c j) y hb
    simpa only [HonestMagicSquare.cellIndex, LCS.MagicSquare.cell_cellIdx hj] using hh
end MIPRE.QLD.Honest
