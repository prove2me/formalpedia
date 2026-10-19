-- Prove2me | solution 1 for MIPRE.Introspection.BinaryComplete.strategy_value
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:20:27.240975+00:00
-- url     : https://prove2.me/submissions/7f5a7f49-29cb-4d0d-af62-069c56b5a3a8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/BinaryGame.lean (solution of MIPRE.Introspection.BinaryComplete.strategy_value);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
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
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCoreGame
import Definitions.Def_MIPRE_Foundations_Introspection_HonestReading
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsed
import Definitions.Def_MIPRE_Foundations_Introspection_HonestParsedHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCompleteAux
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliRegister
import Definitions.Def_MIPRE_Foundations_Introspection_HonestSampling
import Definitions.Def_MIPRE_Foundations_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliEdges
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliGame
import Definitions.Def_MIPRE_Background_Introspection_BinaryMeasurements
import Definitions.Def_MIPRE_Background_Introspection_BinaryAnchors
import Definitions.Def_MIPRE_Background_Introspection_BinarySampled
import Definitions.Def_MIPRE_Background_Introspection_BinaryGame
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_game_positive_content
import Theorems.Thm_MIPRE_Introspection_BinaryComplete_sampleOp_reject
import Theorems.Thm_MIPRE_tracialValue_eq_one_of_re_eq_zero

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
/-- `SyncStrategy.value` is the generic tracial value at the normalized trace, by definition.
Named so that the application below need not ask the unifier to see through `value`, which is
a `whnf` timeout when it does. -/
theorem value_eq_tracialValue (S : SyncStrategy G) :
    S.value = tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P := rfl
end
end MIPRE.SyncStrategy

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

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
variable (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem op_query (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (hL : ∀ w, (L w).SupportedOn univ) (p : QuestionType QLD.Ty ℓ)
    (c : QLD.Content F m) (a : Answer F A m t d) :
    op L D R hm b hL (query hm b p c) a = sampleOp b L D R hm hL c p a := by
  cases p with
  | inl p =>
    change pauliOp b L D R hm (QLD.PauliCL.binaryQuestion b p
      ((QLD.PauliCL.binaryPresentation hm b p).eval _)) a = _
    rw [QLD.PauliCL.binaryQuestion_presentation]
    rfl
  | inr p => rfl
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
variable (R : SyncStrategy (Honest.sourceGame L D).doubled)
set_option backward.isDefEq.respectTransparency false in
theorem check_query (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (p q : QuestionType QLD.Ty ℓ) (c : QLD.Content F m) (a a' : Answer F A m t d) :
    (game L D hm b).D (query hm b p c) (query hm b q c) a a' =
      sampleCheck b L D hm c p q a a' := by
  change TypedEstimates.questionCheck L (.pauli .X) (.pauli .Z) (project b) D (pauliCheck hm b)
    (query hm b p c) (query hm b q c) a a' = _
  cases p <;> cases q <;> cases a <;> cases a' <;>
    simp only [TypedEstimates.questionCheck, sampleCheck, TypedPredicate.check,
      query, TypedPresentation.family, pauliCheck, QLD.PauliCL.binaryQuestion_presentation]
end
end MIPRE.Introspection.BinaryComplete

namespace MIPRE.Introspection.BinaryComplete
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
variable (R : SyncStrategy (Honest.sourceGame L D).doubled)
theorem op_reject (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F) (hb : LowDegree.IsSelfDualBasis b)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1)
    (q r : Question m t ℓ) (h : 0 < (game (d := d) L D hm b).μ q r)
    (a a' : Answer F A m t d) (hr : (game L D hm b).D q r a a' = false) :
    op L D R hm b hL q a * op L D R hm b hL r a' = 0 := by
  obtain ⟨c,p,s,he,rfl,rfl⟩ := game_positive_content L D hm b q r h
  rw [op_query, op_query]
  rw [check_query] at hr
  exact sampleOp_reject b L D R hb hm hd hL hR hv c p s he a a' hr
end
end MIPRE.Introspection.BinaryComplete

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.BinaryComplete
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Fintype A] [DecidableEq A] {m d ℓ t : ℕ} [NeZero m]
  (L : Bool → CL.CLFun (ZMod 2) (Coord m t) ℓ)
  (D : Seed m t → Seed m t → A → A → Bool)
variable (R : SyncStrategy (Honest.sourceGame L D).doubled)
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F) (hb : LowDegree.IsSelfDualBasis b)
    (hd : 1 ≤ d) (hL : ∀ w, (L w).SupportedOn univ) (hR : R.IsPCC) (hv : R.value = 1) :
    (strategy (d := d) L D R hm b hL).value = 1 := by
  rw [SyncStrategy.value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro p q h a a' hr
  obtain ⟨ht,hμ⟩ := doubled_positive L D hm b p q h
  have hd' : (game L D hm b).D p.2 q.2 a a' = false := by
    change (if p.1 = false ∧ q.1 = true then (game L D hm b).D p.2 q.2 a a' else false) = false at hr
    simpa only [if_pos ht] using hr
  have hh := congrArg (registerOp (Fintype.equivFin (Space L D R)).symm)
    (op_reject L D R hm b hb hd hL hR hv p.2 q.2 hμ a a' hd')
  rw [show registerOp (Fintype.equivFin (Space L D R)).symm
    (0 : Matrix (Space L D R) (Space L D R) ℂ) = 0 from rfl] at hh
  have hz : (strategy (d := d) L D R hm b hL).P.M p a * (strategy L D R hm b hL).P.M q a' = 0 := by
    simpa only [strategy, registerOp_mul] using hh
  rw [hz, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]
end MIPRE.Introspection.BinaryComplete
