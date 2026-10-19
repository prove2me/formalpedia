-- Prove2me | solution 1 for MIPRE.QLD.PauliCL.pullbackStrategy_value
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:25.259121+00:00
-- url     : https://prove2.me/submissions/caa1f39e-68eb-4268-b724-a47d19729ee7

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/CLTransport.lean (solution of MIPRE.QLD.PauliCL.pullbackStrategy_value);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
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
import Mathlib.LinearAlgebra.Basis.Defs
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
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
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_QLD_PauliCL_canonicalVector_question

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- The value is the `μ`-average of the conditional success probability. -/
theorem value_eq_sum_succAt (S : TensorProductStrategy G) :
    S.value = ∑ x, ∑ y, G.μ x y * S.succAt x y := by
  unfold value succAt
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [born]; ring
end
end MIPRE.TensorProductStrategy

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
theorem compl_product_univ (S : Finset ι) :
    (S ×ˢ (Finset.univ : Finset κ))ᶜ = Sᶜ ×ˢ Finset.univ := by
  ext ⟨i, j⟩; simp
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable {ℓ : ℕ}
/-- `L^↓ = ↓ ∘ L ∘ ↓⁻¹`. -/
theorem eval_downsize (b : Module.Basis κ K F) (P : CLFun F ι ℓ) (x : ι → F) :
    (P.downsize b).eval (downsizeEquiv b x) = downsizeEquiv b (P.eval x) := by
  induction P generalizing x with
  | zero => simp
  | cons S L₁ next ih =>
    rw [downsize_cons, eval_cons, eval_cons, RegLinear.downsize_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, compl_product_univ,
      ← downsizeEquiv_proj, ih, map_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
/-- Full evaluation produces exactly the seeded question in `QLD.Game`,
including its seed-dependent diagonal direction and canonical base point. -/
theorem questionOfVector_presentation (hm : m ∣ Fintype.card F)
    (t : Ty) (c : Content F m) :
    questionOfVector t ((presentation hm t).eval (contentVector c)) = c.question hm t := by
  cases t <;> (try cases ‹Bas›) <;>
    simp only [questionOfVector, presentation, seedMap, secondMap, finalMap,
      CL.CLFun.eval, CL.RegLinear.zero_apply, CL.RegLinear.id_apply,
      pointMap_apply, directionMap_apply, Pi.add_apply, Pi.zero_apply,
      vectorContent, Content.question, Content.pt, Content.omega,
      LIDT.CL.rep]
  all_goals
    simp [CL.proj_apply, seedSet, directionSet, finalSet, contentVector]
  all_goals constructor <;> rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]
/-- Evaluation agrees with the actual field presentation under the binary
coordinate equivalence. -/
theorem binaryPresentation_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (x : Coord m → F) :
    (binaryPresentation hm b T).eval (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((presentation hm T).eval x) := by
  change (((presentation hm T).downsize b).reindex (binaryCoordEquiv m t)).eval
    (CL.reindexEquiv (binaryCoordEquiv m t) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.eval_reindex, CL.CLFun.eval_downsize]
  rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]
theorem binaryQuestion_presentation (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (c : Content F m) :
    binaryQuestion b T ((binaryPresentation hm b T).eval
      (binaryVectorEquiv b (contentVector c))) = c.question hm T := by
  rw [binaryPresentation_eval]
  unfold binaryQuestion
  rw [LinearEquiv.symm_apply_apply, questionOfVector_presentation]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] {m t : ℕ} [NeZero m]
/-- The existing Pauli game is exactly the decoded binary CL sampler law,
including its uniform ordered-edge choice. -/
theorem qldGame_mu_binaryPresentation {d : ℕ} (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (x y : Question F m) :
    (qldGame (d := d) hm).μ x y =
      SampledGame.dist
        (fun p : TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2) =>
          binaryQuestion b p.1.val.1 ((binaryPresentation hm b p.1.val.1).eval p.2))
        (fun p : TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2) =>
          binaryQuestion b p.1.val.2 ((binaryPresentation hm b p.1.val.2).eval p.2))
        x y := by
  change (∑ p : Sample F m, (Fintype.card (Sample F m) : ℝ)⁻¹ *
    if (p.2.question hm p.1.val.1, p.2.question hm p.1.val.2) = (x, y)
      then 1 else 0) = _
  unfold SampledGame.dist
  rw [← Finset.mul_sum, Fintype.card_congr (binarySampleEquiv (m := m) b)]
  congr 1
  refine Fintype.sum_equiv (binarySampleEquiv b) _ _ fun p => ?_
  simp only [binarySampleEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    Equiv.trans_apply, contentEquiv, Equiv.coe_fn_mk,
    LinearEquiv.coe_toEquiv, binaryQuestion_presentation]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}
theorem encodeQuestion_seed (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) (c : Content F m) :
    encodeQuestion b (c.question hm T) =
      (T, (binaryPresentation hm b T).eval (binaryVectorEquiv b (contentVector c))) := by
  simp only [encodeQuestion, Content.question_ty, canonicalVector_question,
    binaryPresentation_eval]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}
/-- The inverse law is restricted to actual CL outputs, as required. -/
theorem encode_decode_eval (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty)
    (x : Fin ((3 * m + 3) * t) → ZMod 2) :
    encodeQuestion b (decodeQuestion b (T, (binaryPresentation hm b T).eval x)) =
      (T, (binaryPresentation hm b T).eval x) := by
  obtain ⟨z, rfl⟩ := (binaryVectorEquiv (m := m) b).surjective x
  obtain ⟨c, rfl⟩ := (contentEquiv (F := F) (m := m)).surjective z
  change encodeQuestion b (binaryQuestion b T
    ((binaryPresentation hm b T).eval (binaryVectorEquiv b (contentVector c)))) = _
  rw [binaryQuestion_presentation, encodeQuestion_seed]
  rfl
end
end MIPRE.QLD.PauliCL

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.PauliCL
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}
theorem _root_.solution (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) :
    (pullbackStrategy hm b S).value = S.value := by
  rw [TensorProductStrategy.value_eq_sum_succAt, TensorProductStrategy.value_eq_sum_succAt]
  simp_rw [qldGame_mu_binaryPresentation hm b]
  rw [SampledGame.sum_dist_mul]
  change _ = ∑ x, ∑ y, SampledGame.dist (binaryQuery hm b false)
    (binaryQuery hm b true) x y * S.succAt x y
  rw [SampledGame.sum_dist_mul]
  apply congrArg (fun r : ℝ => r /
    (Fintype.card (TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2)) : ℝ))
  refine Finset.sum_congr rfl fun p _ => ?_
  have hA := encode_decode_eval hm b p.1.val.1 p.2
  have hB := encode_decode_eval hm b p.1.val.2 p.2
  simp only [decodeQuestion] at hA hB
  unfold TensorProductStrategy.succAt TensorProductStrategy.born
  simp only [pullbackStrategy, ProjectiveMeasurement.reindex_M, Equiv.refl_apply,
    binaryGame, SampledGame.game, binaryQuery, Bool.false_eq_true, ↓reduceIte,
    decodeQuestion, hA, hB, qldGame_D]
  rfl
end MIPRE.QLD.PauliCL
