-- Prove2me | solution 1 for Light.Sec3.ChanHe.claim_CH20_Theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T17:22:32.846979+00:00
-- url     : https://prove2.me/submissions/bbfc4dc2-6556-4f08-a50e-a0501fb1b1c1

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_ThreeSumSource_CH20Contracts
import Definitions.Def_ThreeSumSource_ReductionClaims
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Init
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Iterate
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Sec3_ChanHe_frontEnd_contracts
import Theorems.Thm_Light_Sec3_claim_VW13_Theorem_3_3
import Theorems.Thm_Light_Sec3_claim_VW18_Theorem_4_2
import Theorems.Thm_Light_Sec3_claim_apspFromMinPlus
import Theorems.Thm_Light_Sec3_et17_spec
import Theorems.Thm_Light_Sec3_obeysBound17_hostTime
import Theorems.Thm_Light_Sec4_allInstances26_solves
import Theorems.Thm_Light_Sec4_allInstancesTime26_le
import Theorems.Thm_Light_Sec4_pre31_program31
import Theorems.Thm_Light_Sec4_queryAt_spec
import Theorems.Thm_Light_Sec4_specs40
import Theorems.Thm_Light_Wrap_realized
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_Theorem19_Choice_ceil_le_sqrt
import Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow
import Theorems.Thm_ThreeSumApsp_goodTime_uniformTime
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem Light.Sec3.ChanHe.emodSpec_of : ∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.emodBody → Light.Sec3.ChanHe.EmodSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).1
theorem Light.Sec3.ChanHe.clog2Spec_of : ∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.clog2Body → Light.Sec3.ChanHe.Clog2Spec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.1
theorem Light.Sec3.ChanHe.log2Spec_of : ∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.log2Body → Light.Sec3.ChanHe.Log2Spec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.1
theorem Light.Sec3.ChanHe.primesSpec_of : ∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ}, P[p]? = some Light.sieveBody → Light.Sec3.ChanHe.PrimesSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.1
theorem Light.Sec3.ChanHe.sortSpec_of : ∀ {lim : Light.Limits} {P : Light.Program} {p pHalf pMerge pCopy : ℕ},
  Light.MergeSort.Procs P p pHalf pMerge pCopy → Light.Sec3.ChanHe.SortSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.1
theorem Light.Sec3.ChanHe.distinct_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.distinctBody → Light.Sec3.ChanHe.DistinctSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.1
theorem Light.Sec3.ChanHe.bits_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.bitsBody → Light.Sec3.ChanHe.BitsSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.1
theorem Light.Sec3.ChanHe.resid_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p pEmod : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.residBody pEmod) →
    Light.Sec3.ChanHe.EmodSpec lim P pEmod → Light.Sec3.ChanHe.ResidSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.2.1
theorem Light.Sec3.ChanHe.tally_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p : ℕ},
  P[p]? = some Light.Sec3.ChanHe.tallyBody → Light.Sec3.ChanHe.TallySpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.2.2.1
theorem Light.Sec3.ChanHe.coll_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.collBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.CollSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.2.2.2.1
theorem Light.Sec3.ChanHe.heavy_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.heavyBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.HeavySpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.2.2.2.2.1
theorem Light.Sec3.ChanHe.modulusSpec_of : ∀ {lim : Light.Limits} {P : Light.Program} {pSearch pColl p : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.modulusBody pSearch pColl) →
    P[pSearch]? = some (Light.Sec3.ChanHe.searchBody pColl) →
      Light.Sec3.ChanHe.CollSpec lim P pColl → Light.Sec3.ChanHe.ModulusSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.2.2.2.2.2.1
theorem Light.Sec3.ChanHe.nodeArray_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p pResid pTally : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.nodeArrayBody pResid pTally) →
    Light.Sec3.ChanHe.ResidSpec lim P pResid →
      Light.Sec3.ChanHe.TallySpec lim P pTally → Light.Sec3.ChanHe.NodeArraySpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Light.Sec3.ChanHe.params_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p pLog2 pClog2 pSqrt : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.paramsBody pLog2 pClog2 pSqrt) →
    Light.Sec3.ChanHe.Log2Spec lim P pLog2 →
      Light.Sec3.ChanHe.Clog2Spec lim P pClog2 → P[pSqrt]? = some Light.sqrtBody → Light.Sec3.ChanHe.ParamsSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Light.Sec3.ChanHe.prep_spec : ∀ {lim : Light.Limits} {P : Light.Program} {p pPrimes pFill pCopy pSort pDistinct pBits : ℕ},
  P[p]? = some (Light.Sec3.ChanHe.prepBody pPrimes pFill pCopy pSort pDistinct pBits) →
    Light.Sec3.ChanHe.PrimesSpec lim P pPrimes →
      P[pFill]? = some Light.fillBody →
        P[pCopy]? = some Light.copyBody →
          Light.Sec3.ChanHe.SortSpec lim P pSort →
            Light.Sec3.ChanHe.DistinctSpec lim P pDistinct →
              Light.Sec3.ChanHe.BitsSpec lim P pBits → Light.Sec3.ChanHe.PrepSpec lim P p :=
  (Light.Sec3.ChanHe.frontEnd_contracts).2.2.2.2.2.2.2.2.2.2.2.2.2.2
section
@[expose] public section
section Sec2Definitions
open Finset
namespace ThreeSumApsp
end ThreeSumApsp
end Sec2Definitions
section Sec2Statements
open Finset
namespace PaperStatements
open ThreeSumApsp
end PaperStatements
end Sec2Statements
section Sec3Definitions
namespace ThreeSumApsp
attribute [instance] LopInstance.fintypeM
namespace TriangleInstance
end TriangleInstance
namespace TriangleInstance
end TriangleInstance
namespace TriangleInstance
end TriangleInstance
end ThreeSumApsp
end Sec3Definitions
section ChanHeDefinitions
namespace ThreeSumApsp
namespace ChanHe
open Finset
def nodes (Q : Finset ℕ) (Λ : ℕ) : ℕ → Finset ℤ → Finset ℤ → Finset ℤ → List Node
  | 0, _, _, _ => []
  | f + 1, S₁, S₂, S₃ =>
    if S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅ then [] else
      let M := modulus Q Λ S₁ S₂ S₃
      ⟨S₁, S₂, S₃, M⟩ ::
        (nodes Q Λ f (heavy S₁ M) S₂ S₃ ++ nodes Q Λ f S₁ (heavy S₂ M) S₃ ++
          nodes Q Λ f S₁ S₂ (heavy S₃ M))
def reduction (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) : List Node :=
  nodes (Nat.primesLE (mPar n U)) (Lam U) (fuel n) S₁ S₂ S₃
def splitA (U β : ℕ) (v : Bool) (S : Finset ℤ) : Finset ℤ := {x ∈ S | (lab U x).testBit β = v}
def splitB (U β β' : ℕ) (v w : Bool) (S : Finset ℤ) : Finset ℤ :=
  {x ∈ S | (lab U x).testBit β = !v ∧ (lab U x).testBit β' = w}
def zeroSet {n : ℕ} (x : Fin n → ℤ) : Finset ℤ := if 3 ≤ #{i : Fin n | x i = 0} then {0} else ∅
def allNodes (n U : ℕ) (x : Fin n → ℤ) : List Node :=
  ((List.range (Lam (2 * U))).flatMap fun β => (List.range (Lam (2 * U))).flatMap fun β' =>
    [false, true].flatMap fun v =>
      reduction n (2 * U) (splitA (2 * U) β v (univ.image x))
        (splitB (2 * U) β β' v false (univ.image x))
        (splitB (2 * U) β β' v true (univ.image x))) ++
  (reduction n (2 * U) (twiceSet x) {0} (univ.image x) ++ reduction n (2 * U) (zeroSet x) {0} {0})
def instances (n U : ℕ) (x : Fin n → ℤ) : List (ℕ → ℤ) :=
  (allNodes n U x).map fun ν => ν.oneArray (2 * U)
def lenOf (κ n : ℕ) : ℕ := 8 * mPar n (2 * n ^ κ) ^ 2
end ChanHe
end ThreeSumApsp
end ChanHeDefinitions
section Sec3Statements
namespace PaperStatements
open ThreeSumApsp
section ChanHe
open Finset
end ChanHe
end PaperStatements
end Sec3Statements
section Sec4Definitions
open Finset
namespace ThreeSumApsp
end ThreeSumApsp
end Sec4Definitions
section Sec4Statements
open Finset
namespace PaperStatements
open ThreeSumApsp
end PaperStatements
end Sec4Statements
section Sec5Definitions
open Finset
namespace ThreeSumApsp
namespace ComparisonCounts
end ComparisonCounts
namespace HintedMv
end HintedMv
end ThreeSumApsp
end Sec5Definitions
section Sec5Statements
open Finset Asymptotics Filter
namespace PaperStatements
open ThreeSumApsp
section ComparisonCounts
open ComparisonCounts
end ComparisonCounts
end PaperStatements
end Sec5Statements
section WordRamProblems
namespace ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
end ThreeSumApsp.WordRam
end WordRamProblems
section AgreementStatements
open ThreeSumApsp.WordRam
namespace PaperStatements
open ThreeSumApsp
end PaperStatements
end AgreementStatements
section WordRamItems
namespace ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace Items
end Items
end ThreeSumApsp.WordRam
end WordRamItems
end
end
section
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam
section
@[expose] public section
open Filter Asymptotics
namespace ThreeSumApsp
namespace Dominated
variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩
protected theorem const (c : ℝ) (hg : ∀ x, dom x → 1 ≤ g x) : Dominated dom (fun _ => c) g :=
  ⟨|c|, abs_nonneg c, fun x hx =>
    (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) (hg x hx))⟩
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC
theorem mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g :=
  (of_le hle).trans hfg
theorem mono_right (hfg : Dominated dom f g) (hle : ∀ x, dom x → g x ≤ g' x) : Dominated dom f g' :=
  hfg.trans (of_le hle)
protected theorem congr (hfg : Dominated dom f g) (hf : ∀ x, dom x → f x = f' x)
    (hg : ∀ x, dom x → g x = g' x) : Dominated dom f' g' :=
  (hfg.mono_left fun x hx => (hf x hx).ge).mono_right fun x hx => (hg x hx).le
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)
protected theorem mul (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hf₁ : ∀ x, dom x → 0 ≤ f₁ x) (hf₂ : ∀ x, dom x → 0 ≤ f₂ x) :
    Dominated dom (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => ?_⟩
  rw [mul_mul_mul_comm]
  exact mul_le_mul (h₁ x hx) (h₂ x hx) (hf₂ x hx) ((hf₁ x hx).trans (h₁ x hx))
protected theorem pow (hfg : Dominated dom f g) (hf : ∀ x, dom x → 0 ≤ f x) (e : ℕ) :
    Dominated dom (fun x => f x ^ e) fun x => g x ^ e := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine ⟨C ^ e, pow_nonneg hC e, fun x hx => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hf x hx) (hle x hx) e
end Dominated
end ThreeSumApsp
end
end
section
public section
open Filter Asymptotics
namespace ThreeSumApsp
theorem isBigO_of_abs_le {f g : ℕ → ℝ} (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * g n) :
    f =O[atTop] g := by
  refine IsBigO.of_bound |C| (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
  exact (h n hn).trans (le_abs_self _)
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter
end ThreeSumApsp.WordRam
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h
theorem getElem?_append_append {P₀ B : Program} (R : Program) {i : ℕ} {body : Stmt}
    (h : B[i]? = some body) : (P₀ ++ (B ++ R))[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩
theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩
theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩
theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩
theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩
theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩
theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩
attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]
end Light
end
end
section
@[expose] public section
namespace Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl
theorem SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)
theorem SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := fun c hc => by
  rw [Function.update_of_ne (by rintro rfl; exact hb hc)]; exact h c hc
variable {dst j : ℕ} {f : ℕ → ℤ}
end Light
end
end
section
public section
namespace Nat
theorem mul_add_le_mul {a b m n : ℕ} (ha : a < m) (hb : b ≤ n) : a * n + b ≤ m * n :=
  calc a * n + b ≤ a * n + n := Nat.add_le_add_left hb _
    _ = (a + 1) * n := (Nat.succ_mul a n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n ha
end Nat
namespace Int
end Int
end
end
section
@[expose] public section
namespace List
variable {α β : Type*}
section
variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
end
section Sorted
variable [LinearOrder α]
end Sorted
end List
namespace ThreeSumApsp
variable {α β : Type*}
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)
theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at h0,
      fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · have := h (l₁.length + i) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < l₁.length
    · rw [List.getElem_append_left hi₁, h₁ i hi₁]
    · have hi₂ : i - l₁.length < l₂.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega), ← h₂ _ hi₂]
      congr 1
      omega
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)
theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by first
                                  |
                                    ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                      (first
                                        | omega
                                        | ((ring_nf); (omega))))
                                  | omega
                                  |
                                    (simp [] <;>
                                        first
                                        | omega
                                        | ((ring_nf); (omega)))) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
                                                                                                                        |
                                                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                                            (first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega))))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _
end Light
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
namespace ListAt
end ListAt
namespace ArrayAt
end ArrayAt
namespace IndexAt
variable {l : List ℕ} {p : ℕ}
end IndexAt
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
section rules
variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT
end rules
section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}
end
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩
end
section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT
end
end Light
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp.WordRam
end Light
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
theorem Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩
theorem Solves.meets {task : Task} {P₀ : Program} {p : ℕ} {T₀ : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : _root_.Light.Solves task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ} (x : task.Inst) {μ : ℕ → ℤ}
    (fr : ℕ) (hpre : task.Pre x μ fr) (hok : (need (task.size x) (task.bound x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.size x) (task.bound x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩
theorem le_timeUpTo (Tn : ℕ → ℕ → ℕ) (n : ℕ) {U : ℕ} {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (Tn n U : ℝ) ≤ timeUpTo Tn n u :=
  Nat.cast_le.2 (Finset.le_sup (f := Tn n)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hu))))
theorem timeUpTo_le {Tn : ℕ → ℕ → ℕ} {n : ℕ} {u B : ℝ}
    (h : ∀ U : ℕ, (U : ℝ) ≤ max u 0 → (Tn n U : ℝ) ≤ B) : timeUpTo Tn n u ≤ B := by
  obtain ⟨U, hU, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊u⌋₊ + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (Tn n)
  rw [timeUpTo, hsup]
  refine h U ((Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hU))).trans ?_)
  rcases le_total 0 u with hu | hu
  · exact (Nat.floor_le hu).trans (le_max_left u 0)
  · rw [Nat.floor_of_nonpos hu, Nat.cast_zero]
    exact le_max_right u 0
theorem Solves.solvedIn {task : Task} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hs : Solves task P p Tn need) (hp : PolyNeed need) : SolvedIn task (timeUpTo Tn) :=
  ⟨P, p, Tn, need, hp, hs, fun n _ _ _ _ hu => le_timeUpTo Tn n hu⟩
end Light
end
end
section
@[expose] public section
namespace ThreeSumApsp
theorem flag_congr {p q : Prop} (h : p ↔ q) : flag p = flag q := by
  rw [propext h]
end ThreeSumApsp
end
end
section
public section
namespace Nat
end Nat
namespace Real
end Real
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Real
theorem one_half_lt_log_two : 1 / 2 < log 2 :=
  lt_trans (by norm_num) log_two_gt_d9
end Real
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
open Filter Asymptotics
namespace ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace IsBigOPow
end IsBigOPow
namespace IsPowPolylog
end IsPowPolylog
end ThreeSumApsp
end
end
section
@[expose] public section
open Filter Asymptotics
namespace ThreeSumApsp
variable {f f' g : ℕ → ℝ} {a b : ℝ}
namespace UpperBigOPow
end UpperBigOPow
namespace UpperPowPolylog
end UpperPowPolylog
namespace UpperPowLittleO
end UpperPowLittleO
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace Scale
variable {α ι : Type*} [Fintype ι] (s : Scale α ι)
theorem mon_zero (x : α) : s.mon 0 x = 1 := by simp [mon]
theorem mon_add (e e' : ι → ℕ) (x : α) : s.mon (e + e') x = s.mon e x * s.mon e' x := by
  simp only [mon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
theorem mon_smul (k : ℕ) (e : ι → ℕ) (x : α) : s.mon (k • e) x = s.mon e x ^ k := by
  simp only [mon, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm k]
theorem mon_single [DecidableEq ι] (i : ι) (x : α) : s.mon (Pi.single i 1) x = s.base i x := by
  simp [mon, Pi.single_apply, pow_ite]
variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}
theorem mon_le_mon (he : ∀ i, e i ≤ e' i) (hx : s.dom x) : s.mon e x ≤ s.mon e' x :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (s.one_le_base i x hx)) _)
    fun i _ => pow_le_pow_right₀ (s.one_le_base i x hx) (he i)
theorem one_le_mon (e : ι → ℕ) (hx : s.dom x) : 1 ≤ s.mon e x :=
  (s.mon_zero x).ge.trans (mon_le_mon (fun _ => Nat.zero_le _) hx)
theorem pow_mul_mon_le (hc : c ≤ c') (he : ∀ i, e i ≤ e' i) (hx : s.dom x) :
    s.hidden x ^ c * s.mon e x ≤ s.hidden x ^ c' * s.mon e' x :=
  mul_le_mul (pow_le_pow_right₀ (s.one_le_hidden x hx) hc) (mon_le_mon he hx)
    (zero_le_one.trans (one_le_mon e hx)) (pow_nonneg (zero_le_one.trans (s.one_le_hidden x hx)) _)
namespace SoftO
variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}
theorem of_le_hidden (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.hidden x) : s.SoftO t 0 :=
  ⟨1, .of_le fun x hx => by simpa only [pow_one, mon_zero, mul_one] using h x hx⟩
theorem of_dominated_base [DecidableEq ι] (i : ι)
    (h : Dominated s.dom (fun x => (t x : ℝ)) (s.base i)) : s.SoftO t (Pi.single i 1) :=
  ⟨0, h.congr (fun _ _ => rfl) fun x _ => by rw [pow_zero, mon_single, one_mul]⟩
theorem of_le_base [DecidableEq ι] (i : ι) (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.base i x) :
    s.SoftO t (Pi.single i 1) :=
  of_dominated_base i (.of_le h)
theorem exists_le (h : s.SoftO t e) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ x, s.dom x → (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) :=
  let ⟨c, C, hC, hle⟩ := h
  ⟨C, c, hC, hle⟩
theorem mono (h : s.SoftO t e) (he : ∀ i, e i ≤ e' i) : s.SoftO t e' :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_right fun _ hx => pow_mul_mon_le le_rfl he hx⟩
theorem of_le (h : s.SoftO t₂ e) (hle : ∀ x, s.dom x → t₁ x ≤ t₂ x) : s.SoftO t₁ e :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_left fun x hx => Nat.cast_le.2 (hle x hx)⟩
theorem of_forall_le {β : Type*} {f g : β → ℕ} (hle : ∀ y, f y ≤ g y) {u : α → β}
    (h : s.SoftO (fun x => g (u x)) e) : s.SoftO (fun x => f (u x)) e :=
  h.of_le fun _ _ => hle _
protected theorem const (k : ℕ) : s.SoftO (fun _ => k) 0 :=
  ⟨0, .const _ fun x _ => by rw [pow_zero, mon_zero, mul_one]⟩
protected theorem add (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x + t₂ x) (e₁ ⊔ e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨max c₁ c₂, ?_⟩
  simpa only [Nat.cast_add] using
    (h₁.mono_right fun _ hx =>
      pow_mul_mon_le (e' := e₁ ⊔ e₂) (le_max_left _ _) (fun _ => le_sup_left) hx).add
      (h₂.mono_right fun _ hx => pow_mul_mon_le (le_max_right _ _) (fun _ => le_sup_right) hx)
protected theorem mul (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x * t₂ x) (e₁ + e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, ?_⟩
  simpa only [Nat.cast_mul] using
    (h₁.mul h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_add, pow_add, mul_mul_mul_comm]
protected theorem pow (h : s.SoftO t e) (k : ℕ) : s.SoftO (fun x => t x ^ k) (k • e) := by
  obtain ⟨c, h⟩ := h
  refine ⟨c * k, ?_⟩
  simpa only [Nat.cast_pow] using
    (h.pow (fun _ _ => Nat.cast_nonneg _) k).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_smul, mul_pow, pow_mul]
protected theorem max (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => max (t₁ x) (t₂ x)) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
protected theorem log (h : s.SoftO t e) (b : ℕ) : s.SoftO (fun x => Nat.log b (t x)) e :=
  h.of_le fun _ _ => Nat.log_le_self _ _
protected theorem sqrt (h : s.SoftO t e) : s.SoftO (fun x => Nat.sqrt (t x)) e :=
  h.of_le fun _ _ => Nat.sqrt_le_self _
end SoftO
end Scale
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
namespace PolyBounded
variable {F : ℕ → ℕ → ℕ}
theorem fst : PolyBounded (fun n _ => n) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ p.2.succ_pos)).mono (by decide)
theorem snd : PolyBounded (fun _ U => U) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ p.1.succ_pos)).mono (by decide)
theorem of_le {G : ℕ → ℕ → ℕ} (h : PolyBounded G) (hle : ∀ n U, F n U ≤ G n U) : PolyBounded F :=
  Scale.SoftO.of_le h fun _ _ => hle _ _
theorem exists_nat_le (h : PolyBounded F) :
    ∃ K e : ℕ, ∀ n U, F n U ≤ K * ((n + 1) * (U + 1)) ^ e := by
  obtain ⟨C, e, hC, hle⟩ := h.exists_le
  refine ⟨⌈C⌉₊, e, fun n U => ?_⟩
  have hceil : (F n U : ℝ) ≤ ⌈C⌉₊ * (((n + 1) * (U + 1) : ℕ) : ℝ) ^ e := by
    simpa [polyScale, Scale.mon] using (hle (n, U) trivial).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by simp [polyScale, Scale.mon]; positivity))
  exact_mod_cast hceil
end PolyBounded
namespace PolyBounded
theorem polyBound {A B : ℕ → ℕ → ℕ} (hA : PolyBounded A) (hB : PolyBounded B) (s k : ℕ) :
    PolyBounded (fun n U => polyBound s k [A n U, B n U]) :=
  of_le (G := fun n U => 2 ^ s * ((A n U + 1) * (B n U + 1)) ^ k) (by first
                                                                      |
                                                                        ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                          (·
                                                                              repeat'
                                                                                with_reducible
                                                                                  first
                                                                                  | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                  | apply Light.PolyBounded.fst
                                                                                  | apply Light.PolyBounded.snd
                                                                                  | apply ThreeSumApsp.Scale.SoftO.log
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                  | apply hA
                                                                                  | apply hB
                                                                                  | apply ThreeSumApsp.Scale.SoftO.add
                                                                                  | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                  | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                  | apply ThreeSumApsp.Scale.SoftO.max
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                  | apply ThreeSumApsp.Scale.SoftO.div);
                                                                          (·
                                                                              first
                                                                              | decide
                                                                              | exact isEmptyElim))
                                                                      |
                                                                        ((fail_if_success
                                                                              (fail_if_success
                                                                                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                                    (on_goal 1 =>
                                                                                        ((repeat'
                                                                                              with_reducible
                                                                                                first
                                                                                                | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                                | apply Light.PolyBounded.fst
                                                                                                | apply Light.PolyBounded.snd
                                                                                                | apply ThreeSumApsp.Scale.SoftO.log
                                                                                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                                | apply hA
                                                                                                | apply hB
                                                                                                | apply ThreeSumApsp.Scale.SoftO.add
                                                                                                | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                                | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                                | apply ThreeSumApsp.Scale.SoftO.max
                                                                                                | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                                | apply ThreeSumApsp.Scale.SoftO.div);
                                                                                          (done))))));
                                                                          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                                                                          (all_goals
                                                                              try
                                                                                ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                                  (·
                                                                                      repeat'
                                                                                        with_reducible
                                                                                          first
                                                                                          | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                          | apply Light.PolyBounded.fst
                                                                                          | apply Light.PolyBounded.snd
                                                                                          | apply ThreeSumApsp.Scale.SoftO.log
                                                                                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                          | apply hA
                                                                                          | apply hB
                                                                                          | apply ThreeSumApsp.Scale.SoftO.add
                                                                                          | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                          | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                          | apply ThreeSumApsp.Scale.SoftO.max
                                                                                          | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                          | apply ThreeSumApsp.Scale.SoftO.div);
                                                                                  (· decide))))
                                                                      |
                                                                        ((apply ThreeSumApsp.Scale.SoftO.mono);
                                                                          (·
                                                                              repeat'
                                                                                with_reducible
                                                                                  first
                                                                                  | exact ThreeSumApsp.Scale.SoftO.const _
                                                                                  | apply Light.PolyBounded.fst
                                                                                  | apply Light.PolyBounded.snd
                                                                                  | apply ThreeSumApsp.Scale.SoftO.log
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                                                  | apply hA
                                                                                  | apply hB
                                                                                  | apply ThreeSumApsp.Scale.SoftO.add
                                                                                  | apply ThreeSumApsp.Scale.SoftO.mul
                                                                                  | apply ThreeSumApsp.Scale.SoftO.pow
                                                                                  | apply ThreeSumApsp.Scale.SoftO.max
                                                                                  | apply ThreeSumApsp.Scale.SoftO.sub
                                                                                  | apply ThreeSumApsp.Scale.SoftO.div)))
    fun n U => by simp [Light.polyBound]
theorem polyNeed {need : ℕ → ℕ → Need} (hw : PolyBounded fun n U => (need n U).word)
    (hc : PolyBounded fun n U => (need n U).cells) (hd : PolyBounded fun n U => (need n U).depth) :
    PolyNeed need := by
  obtain ⟨K, e, hK⟩ := exists_nat_le (F := fun n U => (need n U).word + (need n U).cells +
    (need n U).depth) (by first
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div);
                              (·
                                  first
                                  | decide
                                  | exact isEmptyElim))
                          |
                            ((fail_if_success
                                  (fail_if_success
                                      ((apply ThreeSumApsp.Scale.SoftO.mono);
                                        (on_goal 1 =>
                                            ((repeat'
                                                  with_reducible
                                                    first
                                                    | exact ThreeSumApsp.Scale.SoftO.const _
                                                    | apply Light.PolyBounded.fst
                                                    | apply Light.PolyBounded.snd
                                                    | apply ThreeSumApsp.Scale.SoftO.log
                                                    | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                    | apply hw
                                                    | apply hc
                                                    | apply hd
                                                    | apply ThreeSumApsp.Scale.SoftO.add
                                                    | apply ThreeSumApsp.Scale.SoftO.mul
                                                    | apply ThreeSumApsp.Scale.SoftO.pow
                                                    | apply ThreeSumApsp.Scale.SoftO.max
                                                    | apply ThreeSumApsp.Scale.SoftO.sub
                                                    | apply ThreeSumApsp.Scale.SoftO.div);
                                              (done))))));
                              (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                              (all_goals
                                  try
                                    ((apply ThreeSumApsp.Scale.SoftO.mono);
                                      (·
                                          repeat'
                                            with_reducible
                                              first
                                              | exact ThreeSumApsp.Scale.SoftO.const _
                                              | apply Light.PolyBounded.fst
                                              | apply Light.PolyBounded.snd
                                              | apply ThreeSumApsp.Scale.SoftO.log
                                              | apply ThreeSumApsp.Scale.SoftO.sqrt
                                              | apply hw
                                              | apply hc
                                              | apply hd
                                              | apply ThreeSumApsp.Scale.SoftO.add
                                              | apply ThreeSumApsp.Scale.SoftO.mul
                                              | apply ThreeSumApsp.Scale.SoftO.pow
                                              | apply ThreeSumApsp.Scale.SoftO.max
                                              | apply ThreeSumApsp.Scale.SoftO.sub
                                              | apply ThreeSumApsp.Scale.SoftO.div);
                                      (· decide))))
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div)))
  refine ⟨Nat.size K, e, fun n U => ?_⟩
  have hsum := hK n U
  have hpoly : K * ((n + 1) * (U + 1)) ^ e ≤ Light.polyBound (Nat.size K) e [n, U] := by
    simp only [Light.polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.lt_size_self K).le
  exact ⟨by omega, by omega, by omega⟩
end PolyBounded
namespace PolyNeed
variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}
private theorem part (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    ∃ R : ℕ → ℕ → ℕ, PolyBounded R ∧ ∀ n U, (need (A (n, U)) (B (n, U))).word ≤ R n U ∧
      (need (A (n, U)) (B (n, U))).cells ≤ R n U ∧ (need (A (n, U)) (B (n, U))).depth ≤ R n U :=
  let ⟨s, k, hle⟩ := h
  ⟨_, PolyBounded.polyBound (A := fun n U => A (n, U)) (B := fun n U => B (n, U))
    (hA.mono isEmptyElim) (hB.mono isEmptyElim) s k, fun _ _ => hle _ _⟩
theorem word (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).word) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).1
theorem cells (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).cells) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.1
theorem depth (h : PolyNeed need) (hA : polyScale.SoftO A a) (hB : polyScale.SoftO B b) :
    polyScale.SoftO (fun p => (need (A p) (B p)).depth) ![] :=
  let ⟨_, hR, hle⟩ := h.part hA hB
  Scale.SoftO.of_le hR fun p _ => (hle p.1 p.2).2.2
end PolyNeed
end Light
end
end
section
public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp
open Real
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
namespace Light.Sec3
end Light.Sec3
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3
open ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Scan
end Scan
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
namespace PowLt
end PowLt
namespace RootCeil
end RootCeil
end Light.Sec3
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3
open ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Brute
end Brute
section
variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}
end
end Light.Sec3
end
end
section
public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
namespace HostPoly
variable {D g : ℕ → ℕ}
section parts
variable (hD : PolyBounded fun n _ => D n)
include hD
end parts
end HostPoly
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
namespace CostParams.Hyp
variable {θ : CostParams} (h : θ.Hyp)
include h
end CostParams.Hyp
namespace Steps
variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}
end Steps
section within
variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}
end within
namespace Steps
variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}
end Steps
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
end Light.Sec3
end
end
section
public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
end Light.Sec3
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
end Light
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {d : ℕ}
namespace ChooseHost
end ChooseHost
open ChooseHost
end Light.Sec3
end
end
section
@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {d : ℕ}
namespace LopHosts
end LopHosts
open LopHosts
namespace LopArgs
end LopArgs
namespace LopHosts
end LopHosts
open LopHosts
end Light.Sec3
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace PowTable
end PowTable
open PowTable
end Light
end
end
section
@[expose] public section
namespace Light.Sec2
open ThreeSumApsp
namespace Par
end Par
namespace Par
end Par
namespace Par
variable (p : Par)
end Par
end Light.Sec2
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec
section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)
end
end ThreeSumApsp.Spec
end
end
section
public section
namespace Light.Sec2
open ThreeSumApsp
variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}
end Light.Sec2
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
namespace Dir
end Dir
section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}
end
end Light.Sec4
end
end
section
@[expose] public section
open Finset
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
namespace Query31
end Query31
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}
namespace Pre31
end Pre31
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec Finset
namespace IpAt
end IpAt
section
variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)
variable {X Y}
end
end Light.Sec4
end
end
section
@[expose] public section
namespace ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
section known
variable {m : ℤ → BitVec W} {i j k a b : ℤ}
end known
section framing
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}
end framing
end ThreeSumApsp.WordRam
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}
end
namespace WantedCore
end WantedCore
section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}
end
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}
namespace Offline32
end Offline32
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.WordRam
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.WordRam
end Light.Sec4
end
end
section
@[expose] public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
section need
variable {lim : Limits} {N D₀ w U fr d : ℕ}
end need
section summands
variable {N D U Q : ℕ}
end summands
end Light.Sec4
end
end
section
public section
namespace Light.Sec4
open ThreeSumApsp ThreeSumApsp.Spec
end Light.Sec4
end
end
section
public section
namespace ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
end ThreeSumApsp.FromClaims
end
end
section
@[expose] public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light.Sec3
end Light.Sec3
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace Theorem19
namespace Choice
variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P
end Choice
end Theorem19
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light.Sec3
end Light.Sec3
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3
open ThreeSumApsp.WordRam ThreeSumApsp.Spec
end Light.Sec3
end
end
section
@[expose] public section
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
open ThreeSumApsp ThreeSumApsp.WordRam
namespace Light.Sec3
end Light.Sec3
namespace ThreeSumApsp
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam
end
end
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace APSPFocusedSource
open ThreeSumApsp.WordRam
end APSPFocusedSource
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩
end
section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}
end
end Light
end
end
section
@[expose] public section
namespace Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)
end Light
end
end
section
@[expose] public section
namespace Light
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)
variable {dst j : ℕ} {f : ℕ → ℤ}
end Light
end
end
section
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
theorem Stmt.Runs.mono {s : Stmt} {σ : State} {R R' : State → Prop} (h : s.Runs lim σ R)
    (hR : ∀ σ', R σ' → R' σ') : s.Runs lim σ R' :=
  ⟨h.1, hR _ h.2⟩
theorem Ends.pieceThen {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by (((first
                            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                first
                                | omega
                                | (ring_nf; omega))
                            | omega
                            |
                              (simp [] <;>
                                  first
                                  | omega
                                  | (ring_nf; omega))))
                                )) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.next T₁ (h.mono le_rfl rest) hT
theorem Ends.pieceLast {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop}
    (h : Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by (((first
                                                                                   | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                                         _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                       first
                                                                                       | omega
                                                                                       | (ring_nf; omega))
                                                                                   | omega
                                                                                   |
                                                                                     (simp [] <;>
                                                                                         first
                                                                                         | omega
                                                                                         | (ring_nf; omega))))
                                                                                       )) :
    Ends lim P d s σ T Q :=
  h.mono hT rest
theorem Ends.setLast {loc μ : ℕ → ℤ} {T x : ℕ} {e : Expr} {Q : State → Prop}
    (h : Q ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩)
    (hs : e.Safe lim ⟨loc, μ⟩ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                           (try have := _root_.Light.Std.const_le (by assumption))
                                           simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                             )) (hT : e.cost + 1 ≤ T := by (((first
                                                                                | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                                      _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                    first
                                                                                    | omega
                                                                                    | (ring_nf; omega))
                                                                                | omega
                                                                                |
                                                                                  (simp [] <;>
                                                                                      first
                                                                                      | omega
                                                                                      | (ring_nf; omega))))
                                                                                    )) :
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set hs hT h
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d (s₁ ;; s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d (s₂ ;; s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      )) (hT : c.cost + 1 ≤ T := by (((first
                                                                         | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                               _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                             first
                                                                             | omega
                                                                             | (ring_nf; omega))
                                                                         | omega
                                                                         |
                                                                           (simp [] <;>
                                                                               first
                                                                               | omega
                                                                               | (ring_nf; omega))))
                                                                             )) :
    Ends lim P d (.ite c s₁ s₂ ;; s) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩
end Light
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace ChanHe
open Finset
def HasSol (S₁ S₂ S₃ : Finset ℤ) : Prop := ∃ a ∈ S₁, ∃ b ∈ S₂, ∃ c ∈ S₃, a + b + c = 0
def ConvSol (N : ℕ) (X Y Z : ℕ → ℤ) : Prop := ∃ i j : ℕ, i + j < N ∧ X i + Y j = Z (i + j)
def ConvOne (N : ℕ) (y : ℕ → ℤ) : Prop := ConvSol N y y y
def Node.Conv (ν : Node) (U N : ℕ) : Prop :=
  ConvSol N (arrXY ν.S₁ ν.M U) (arrXY ν.S₂ ν.M U) (arrZ ν.S₃ ν.M U)
end ChanHe
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
def treeCalls (Q : Finset ℕ) (Λ : ℕ) : ℕ → Finset ℤ → Finset ℤ → Finset ℤ → ℕ
  | 0, _, _, _ => 1
  | f + 1, S₁, S₂, S₃ =>
    if S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅ then 1 else
      1 + (treeCalls Q Λ f (heavy S₁ (modulus Q Λ S₁ S₂ S₃)) S₂ S₃ +
        treeCalls Q Λ f S₁ (heavy S₂ (modulus Q Λ S₁ S₂ S₃)) S₃ +
        treeCalls Q Λ f S₁ S₂ (heavy S₃ (modulus Q Λ S₁ S₂ S₃)))
def tNode (T : ℕ → ℕ → ℕ) (n V m np : ℕ) : ℕ :=
  tModulus np n n n V + tNodeArray m n n n V + T (8 * m ^ 2) (60 * V + 40) + 3 * tHeavy n V + 300
def tNodes (T : ℕ → ℕ → ℕ) (n V m np calls : ℕ) : ℕ := calls * (tNode T n V m np + 60)
abbrev NodeArgs.calls (a : NodeArgs) (Λ f : ℕ) : ℕ :=
  treeCalls (Nat.primesLE a.m) Λ f a.X₁.set a.X₂.set a.X₃.set
def TreeYes (m Λ f V : ℕ) (S₁ S₂ S₃ : Finset ℤ) : Prop :=
  ∃ ν ∈ nodes (Nat.primesLE m) Λ f S₁ S₂ S₃, ConvOne (8 * m ^ 2) (ν.oneArray V)
abbrev NodeArgs.Yes (a : NodeArgs) (Λ f : ℕ) : Prop :=
  TreeYes a.m Λ f a.V a.X₁.set a.X₂.set a.X₃.set
def NodesSpecAt (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) (f : ℕ) :
    Prop :=
  ∀ (a : NodeArgs) (Λ cx : ℕ) (μ : ℕ → ℤ) (d : ℕ), NodesPre lim r μ a Λ cx f d →
    Meets lim P p d ((f : ℤ) :: a.sets ++ [(cx : ℤ), a.fr]) μ
      (tNodes T a.n a.V a.m a.np (a.calls Λ f)) fun res μ' =>
        res = ThreeSumApsp.flag (a.Yes Λ f) ∧ Kept μ μ' a.fr
def NodesSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ f, NodesSpecAt lim P p T r f
def tTwice (n : ℕ) : ℕ := 60 * n + 40
def tZeroThree (n : ℕ) : ℕ := 40 * n + 40
def tPick (len : ℕ) : ℕ := 90 * len + 40
def twiceList (D C : List ℤ) : List ℤ :=
  ((D.zip C).filter fun q => decide (q.1 ≠ 0 ∧ 2 ≤ q.2)).map fun q => 2 * q.1
structure Twice.Ctx (lim : Limits) (μ : ℕ → ℤ) (val mul out V : ℕ) (D C : List ℤ) : Prop where
  len : C.length = D.length
  bounded : AbsLe D V
  segVal : Seg μ val D
  segMul : Seg μ mul C
  apartVal : Apart val D.length out D.length
  apartMul : Apart mul D.length out D.length
  spaceVal : val + D.length ≤ lim.space
  spaceMul : mul + D.length ≤ lim.space
  spaceOut : out + D.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (2 * V + 2 * D.length + 8 : ℤ) ≤ lim.word
def TwiceSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d val mul out V : ℕ) (D C : List ℤ) (μ : ℕ → ℤ), Twice.Ctx lim μ val mul out V D C →
    Meets lim P p d [D.length, val, mul, out] μ (tTwice D.length) fun r μ' =>
      r = ((twiceList D C).length : ℤ) ∧ Seg μ' out (twiceList D C) ∧ SameOutside μ μ' out D.length
def ZeroThreeSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d val mul : ℕ) (D C : List ℤ) (μ : ℕ → ℤ), C.length = D.length → Seg μ val D → Seg μ mul C →
    val + D.length ≤ lim.space → mul + D.length ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    (2 * D.length + 8 : ℤ) ≤ lim.word →
    Meets lim P p d [D.length, val, mul] μ (tZeroThree D.length) fun r μ' =>
      r = ThreeSumApsp.flag (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) ∧ μ' = μ
def pickList (Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) : List ℤ :=
  ((List.range L.length).filter fun i =>
    decide (BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x'))).map
    fun i => L.getD i 0
structure Pick.Ctx (lim : Limits) (μ : ℕ → ℤ) (s bt out Λ β β' : ℕ) (L BT : List ℤ) : Prop where
  lenTable : BT.length = L.length * Λ
  posA : β < Λ
  posB : β' < Λ
  segSrc : Seg μ s L
  segTable : Seg μ bt BT
  apartSrc : Apart s L.length out L.length
  apartTable : Apart bt (L.length * Λ) out L.length
  spaceSrc : s + L.length ≤ lim.space
  spaceTable : bt + L.length * Λ ≤ lim.space
  spaceOut : out + L.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (8 : ℤ) ≤ lim.word
def PickSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d s bt out Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) (μ : ℕ → ℤ),
    Pick.Ctx lim μ s bt out Λ β β' L BT →
    Meets lim P p d [L.length, s, bt, Λ, β, x, β', x', two, out] μ (tPick L.length) fun r μ' =>
      r = ((pickList Λ β β' x x' two L BT).length : ℤ) ∧
        Seg μ' out (pickList Λ β β' x x' two L BT) ∧ SameOutside μ μ' out L.length
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace ThreeSumApsp.Spec
section Filter
variable {α β : Type}
def passList (p : α → Bool) (f : α → β) (Z : List α) (i : ℕ) : List β := ((Z.take i).filter p).map f
@[simp] theorem passList_zero (p : α → Bool) (f : α → β) (Z : List α) : passList p f Z 0 = [] := by
  simp [passList]
theorem passList_length (p : α → Bool) (f : α → β) (Z : List α) :
    passList p f Z Z.length = (Z.filter p).map f := by
  simp [passList]
theorem passList_succ_of {p : α → Bool} (f : α → β) {Z : List α} {i : ℕ} (hi : i < Z.length)
    (h : p Z[i] = true) : passList p f Z (i + 1) = passList p f Z i ++ [f Z[i]] := by
  unfold passList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append, List.map_append]
  simp [h]
theorem passList_succ_of_not {p : α → Bool} (f : α → β) {Z : List α} {i : ℕ} (hi : i < Z.length)
    (h : p Z[i] = false) : passList p f Z (i + 1) = passList p f Z i := by
  unfold passList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append, List.map_append]
  simp [h]
theorem length_passList_le (p : α → Bool) (f : α → β) (Z : List α) (i : ℕ) :
    (passList p f Z i).length ≤ i := by
  rw [passList, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_take_le i Z)
end Filter
end ThreeSumApsp.Spec
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.Spec ThreeSumApsp.ChanHe
variable {lim : Limits} {P : Program} {d : ℕ}
def pickPart (Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) (i : ℕ) : List ℤ :=
  passList
    (fun i => decide (BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x')))
    (fun i => L.getD i 0) (List.range L.length) i
theorem pickPart_succ (Λ β β' : ℕ) (x x' two : ℤ) {L : List ℤ} (BT : List ℤ) {i : ℕ}
    (hi : i < L.length) :
    pickPart Λ β β' x x' two L BT (i + 1) =
      if BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x') then
        pickPart Λ β β' x x' two L BT i ++ [L.getD i 0]
      else pickPart Λ β β' x x' two L BT i := by
  have hi' : i < (List.range L.length).length := by simpa using hi
  split_ifs with h
  · exact (passList_succ_of _ hi' (by simpa using h)).trans (by simp [pickPart])
  · exact passList_succ_of_not _ hi' (by simpa using h)
theorem pickPart_length (Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) :
    pickPart Λ β β' x x' two L BT L.length = pickList Λ β β' x x' two L BT := by
  have h := passList_length
    (fun i => decide (BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x')))
    (fun i => L.getD i 0) (List.range L.length)
  rwa [List.length_range] at h
namespace Pick
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Table : ℕ := 2
@[inherit_doc Len] abbrev Width : ℕ := 3
@[inherit_doc Len] abbrev PosA : ℕ := 4
@[inherit_doc Len] abbrev DigitA : ℕ := 5
@[inherit_doc Len] abbrev PosB : ℕ := 6
@[inherit_doc Len] abbrev DigitB : ℕ := 7
@[inherit_doc Len] abbrev Two : ℕ := 8
@[inherit_doc Len] abbrev Out : ℕ := 9
@[inherit_doc Len] abbrev Idx : ℕ := 10
@[inherit_doc Len] abbrev Written : ℕ := 11
@[inherit_doc Len] abbrev Row : ℕ := 12
end Pick
open Pick in
def pickTake : Stmt :=
  .store (v Out +' v Written) (M (v Src +' v Idx)) ;;
  .set Written (v Written +' k 1)
open Pick in
def pickNext : Stmt :=
  .set Row (v Row +' v Width) ;;
  .set Idx (v Idx +' k 1)
open Pick in
def pickRound : Stmt :=
  .ite (M (v Row +' v PosA) =' v DigitA)
    (.ite (v Two =' k 0) pickTake (.ite (M (v Row +' v PosB) =' v DigitB) pickTake .skip))
    .skip ;;
  pickNext
open Pick in
def pickBody : Stmt :=
  .set Idx (k 0) ;;
  .set Written (k 0) ;;
  .set Row (v Table) ;;
  .while (v Idx <' v Len) pickRound ;;
  .set Len (v Written)
theorem Pick.Ctx.step {μ μ' : ℕ → ℤ} {s bt out Λ β β' i : ℕ} {L BT : List ℤ}
    (C : Pick.Ctx lim μ s bt out Λ β β' L BT) (hsame : SameOutside μ μ' out L.length)
    (hi : i < L.length) (x x' two : ℤ) :
    pickPart Λ β β' x x' two L BT (i + 1) =
      if μ' (bt + i * Λ + β) = x ∧ (two = 0 ∨ μ' (bt + i * Λ + β') = x') then
        pickPart Λ β β' x x' two L BT i ++ [μ' (s + i)]
      else pickPart Λ β β' x x' two L BT i := by
  (((obtain ⟨⟩ := _root_.id C))
              )
  have hrows : i * Λ + Λ ≤ L.length * Λ := Nat.mul_add_le_mul hi le_rfl
  have hread : ∀ γ < Λ, μ' (bt + i * Λ + γ) = BT.getD (i * Λ + γ) 0 := fun γ hγ => by
    rw [hsame _ (by omega), Nat.add_assoc]
    exact C.segTable.getD (by have := C.lenTable; omega) 0
  rw [hread β C.posA, hread β' C.posB, hsame (s + i) (by omega), C.segSrc.getD hi 0]
  exact pickPart_succ Λ β β' x x' two BT hi
def PickInv (μ : ℕ → ℤ) (s bt out Λ β β' : ℕ) (x x' two : ℤ) (L BT : List ℤ) (i : ℕ)
    (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (row : ℕ), row = bt + i * Λ ∧
    σ = ⟨frame [L.length, s, bt, Λ, β, x, β', x', two, out, i,
      (pickPart Λ β β' x x' two L BT i).length, row], μ'⟩ ∧
    Seg μ' out (pickPart Λ β β' x x' two L BT i) ∧ SameOutside μ μ' out L.length
theorem pickRound_runs {μ : ℕ → ℤ} {s bt out Λ β β' i : ℕ} {x x' two : ℤ} {L BT : List ℤ}
    (C : Pick.Ctx lim μ s bt out Λ β β' L BT) (hi : i < L.length) {σ : State}
    (hI : PickInv μ s bt out Λ β β' x x' two L BT i σ) :
    pickRound.Runs lim σ (PickInv μ s bt out Λ β β' x x' two L BT (i + 1)) := by
  obtain ⟨μ', row, hrow, rfl, hseg, hsame⟩ := hI
  have hstep := C.step hsame hi x x' two
  rw [← hrow] at hstep
  have hnext : row + Λ = bt + (i + 1) * Λ := by rw [hrow, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  (((obtain ⟨⟩ := _root_.id C))
              )
  have hle : (pickPart Λ β β' x x' two L BT i).length ≤ i := length_passList_le _ _ _ _
  have hrows : i * Λ + Λ ≤ L.length * Λ := Nat.mul_add_le_mul hi le_rfl
  by_cases hA : μ' (row + β) ≠ x
  ·
    rw [if_neg (by simp [hA])] at hstep
    exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                   (try have := _root_.Light.Std.const_le (by assumption))
                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pickRound, pickNext, hA] <;>
                     omega))
                                                 ), μ', row + Λ, hnext,
      by simp [pickRound, pickNext, update_frame_setLocal, hA, hstep], hstep ▸ hseg, hsame⟩
  rw [not_not] at hA
  by_cases hsel : two = 0 ∨ μ' (row + β') = x'
  ·
    rw [if_pos ⟨hA, hsel⟩] at hstep
    refine ⟨?safe, Function.update μ' (out + (pickPart Λ β β' x x' two L BT i).length) (μ' (s + i)),
      row + Λ, hnext, ?state, hstep ▸ hseg.snoc _, hsame.write (by omega) _⟩
    case safe =>
      by_cases h2 : two = 0
      · simp [pickRound, pickTake, pickNext, hA, eq_true h2, Limits.Addr, abs_le]; omega
      · simp [pickRound, pickTake, pickNext, hA, h2, hsel.resolve_left h2, Limits.Addr, abs_le]
        omega
    case state =>
      by_cases h2 : two = 0
      · simp [pickRound, pickTake, pickNext, update_frame_setLocal, hA, eq_true h2, hstep]
      · simp [pickRound, pickTake, pickNext, update_frame_setLocal, hA, h2,
          hsel.resolve_left h2, hstep]
  ·
    rw [if_neg (by simp [hsel])] at hstep
    rw [not_or] at hsel
    exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                   (try have := _root_.Light.Std.const_le (by assumption))
                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pickRound, pickNext, hA, hsel.1,
                       hsel.2] <;>
                     omega))
                                                                 ), μ',
      row + Λ, hnext,
      by simp [pickRound, pickNext, update_frame_setLocal, hA, hsel.1, hsel.2, hstep],
      hstep ▸ hseg, hsame⟩
theorem pick_spec {p : ℕ} (hP : P[p]? = some pickBody) : PickSpec lim P p := by
  intro d s bt out Λ β β' x x' two L BT μ C
  (((obtain ⟨⟩ := _root_.id C))
              )
  refine Meets.of_body hP ?_
  unfold tPick pickBody
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen bt ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
             )
  refine Ends.next _ (Ends.whileBlock (PickInv μ s bt out Λ β β' x x' two L BT) L.length
    ?start ?round ?done (hT := le_rfl)) (by simp [pickRound, pickTake, pickNext]; omega)
  case start => exact ⟨μ, bt, by simp, by simp [pickPart], by simp [pickPart], .refl⟩
  case round =>
    intro i σ hi hI
    obtain ⟨μ', row, -, rfl, -⟩ := id hI
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), pickRound_runs C hi hI⟩
  case done =>
    rintro _ ⟨μ', row, -, rfl, hseg, hsame⟩
    rw [pickPart_length] at hseg
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), Ends.setTo ((pickList Λ β β' x x' two L BT).length : ℕ)
      ⟨rfl, hseg, hsame⟩ (by simp [pickPart_length])
      (by simp [pickRound, pickTake, pickNext]; omega)⟩
namespace Bits
end Bits
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace List
variable {α β : Type*}
section
variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
end
section Sorted
variable [LinearOrder α]
end Sorted
end List
namespace ThreeSumApsp
variable {α β : Type*}
theorem AbsLe.getElem {l : List ℤ} {U : ℤ} (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U :=
  h _ (List.getElem_mem hi)
end ThreeSumApsp
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
noncomputable def tripleZeroUpTo (D C : List ℤ) (i : ℕ) : ℤ :=
  flag (∃ j < i, D.getD j 0 = 0 ∧ 3 ≤ C.getD j 0)
theorem tripleZeroUpTo_zero (D C : List ℤ) : tripleZeroUpTo D C 0 = 0 := flag_of_not (by simp)
theorem tripleZeroUpTo_succ (D C : List ℤ) (i : ℕ) :
    tripleZeroUpTo D C (i + 1) =
      if D.getD i 0 = 0 ∧ 2 < C.getD i 0 then 1 else tripleZeroUpTo D C i := by
  split_ifs with h
  · exact flag_of ⟨i, Nat.lt_succ_self i, h⟩
  · exact flag_congr (Nat.exists_lt_succ_right.trans (or_iff_left h))
theorem tripleZeroUpTo_length {D C : List ℤ} (hlen : C.length = D.length) :
    tripleZeroUpTo D C D.length = flag (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) := by
  refine flag_congr ⟨?_, ?_⟩
  · rintro ⟨j, hj, hp⟩
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (hlen ▸ hj)] at hp
    exact ⟨(D[j], C[j]), List.mem_iff_getElem.2 ⟨j, by simp [hlen, hj], by simp⟩, hp⟩
  · rintro ⟨q, hq, hp⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
    have hj' : j < D.length := by simp at hj; omega
    refine ⟨j, hj', ?_⟩
    rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ (hlen ▸ hj')]
    simpa using hp
namespace ZeroThree
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Val : ℕ := 1
@[inherit_doc Len] abbrev Mul : ℕ := 2
@[inherit_doc Len] abbrev Idx : ℕ := 3
@[inherit_doc Len] abbrev Found : ℕ := 4
end ZeroThree
open ZeroThree in
def zeroThreeBody : Stmt :=
  .set Idx (k 0) ;;
  .set Found (k 0) ;;
  .while (v Idx <' v Len) (
    .ite (M (v Val +' v Idx) =' k 0)
      (.ite (k 2 <' M (v Mul +' v Idx)) (.set Found (k 1)) .skip)
      .skip ;;
    .set Idx (v Idx +' k 1)) ;;
  .set Len (v Found)
def ZeroThreeInv (μ : ℕ → ℤ) (val mul : ℕ) (D C : List ℤ) (i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [D.length, val, mul, i, tripleZeroUpTo D C i], μ⟩
theorem zeroThree_spec {p : ℕ} (hP : P[p]? = some zeroThreeBody) : ZeroThreeSpec lim P p := by
  intro d val mul D C μ hlen hD hC hval hmul hw hword
  refine Meets.of_body hP ?_
  unfold tZeroThree zeroThreeBody
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             0
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
            )
  refine Ends.next _ (Ends.whileBlock (ZeroThreeInv μ val mul D C) D.length ?start ?round ?done
    (hT := le_rfl)) (by simp; omega)
  case start => simp [ZeroThreeInv, tripleZeroUpTo_zero]
  case round =>
    rintro i _ hi rfl
    have hstep := tripleZeroUpTo_succ D C i
    rw [← hD.getD hi 0, ← hC.getD (hlen ▸ hi) 0] at hstep
    refine ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                      (try have := _root_.Light.Std.const_le (by assumption))
                      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                        ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                     (try have := _root_.Light.Std.const_le (by assumption))
                                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                       ), ?_⟩
    by_cases h0 : μ (val + i) = 0 <;> by_cases h2 : 2 < μ (mul + i) <;>
      simp [Stmt.Runs, ZeroThreeInv, update_frame_setLocal, hstep, h0, h2, Limits.Addr, abs_le] <;>
      omega
  case done =>
    rintro _ rfl
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), Ends.setTo (tripleZeroUpTo D C D.length)
      ⟨tripleZeroUpTo_length hlen, rfl⟩ (hT := by simp; omega)⟩
def twicePart (D C : List ℤ) (i : ℕ) : List ℤ :=
  passList (fun q : ℤ × ℤ => decide (q.1 ≠ 0 ∧ 2 ≤ q.2)) (fun q => 2 * q.1) (D.zip C) i
theorem twicePart_succ {D C : List ℤ} (hlen : C.length = D.length) {i : ℕ} (hi : i < D.length) :
    twicePart D C (i + 1) =
      if D.getD i 0 ≠ 0 ∧ 1 < C.getD i 0 then twicePart D C i ++ [2 * D.getD i 0]
      else twicePart D C i := by
  have hi' : i < (D.zip C).length := by simp [hlen, hi]
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (hlen ▸ hi)]
  split_ifs with h
  · exact (passList_succ_of _ hi' (by simpa using ⟨h.1, h.2⟩)).trans (by simp [twicePart])
  · exact passList_succ_of_not _ hi' (by simpa [Int.add_one_le_iff] using h)
theorem twicePart_length {D C : List ℤ} (hlen : C.length = D.length) :
    twicePart D C D.length = twiceList D C := by
  have hzip : (D.zip C).length = D.length := by simp [hlen]
  rw [twicePart, ← hzip, passList_length]
  rfl
namespace Twice
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Val : ℕ := 1
@[inherit_doc Len] abbrev Mul : ℕ := 2
@[inherit_doc Len] abbrev Out : ℕ := 3
@[inherit_doc Len] abbrev Idx : ℕ := 4
@[inherit_doc Len] abbrev Written : ℕ := 5
end Twice
open Twice in
def twiceRound : Stmt :=
  .iteNe (M (v Val +' v Idx)) (k 0)
    (.ite (k 1 <' M (v Mul +' v Idx))
      (.store (v Out +' v Written) (k 2 *' M (v Val +' v Idx)) ;;
        .set Written (v Written +' k 1))
      .skip)
    .skip ;;
  .set Idx (v Idx +' k 1)
open Twice in
def twiceBody : Stmt :=
  .set Idx (k 0) ;;
  .set Written (k 0) ;;
  .while (v Idx <' v Len) twiceRound ;;
  .set Len (v Written)
def TwiceInv (μ : ℕ → ℤ) (val mul out : ℕ) (D C : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [D.length, val, mul, out, i, (twicePart D C i).length], μ'⟩ ∧
    Seg μ' out (twicePart D C i) ∧ SameOutside μ μ' out D.length
theorem twiceRound_runs {μ : ℕ → ℤ} {val mul out V i : ℕ} {D C : List ℤ}
    (K : Twice.Ctx lim μ val mul out V D C) (hi : i < D.length) {σ : State}
    (hI : TwiceInv μ val mul out D C i σ) :
    twiceRound.Runs lim σ (TwiceInv μ val mul out D C (i + 1)) := by
  obtain ⟨μ', rfl, hseg, hsame⟩ := hI
  (((obtain ⟨⟩ := _root_.id K))
              )
  have hle : (twicePart D C i).length ≤ i := length_passList_le _ _ _ _
  have hreadVal : μ' (val + i) = D.getD i 0 := (hsame _ (by omega)).trans (K.segVal.getD hi 0)
  have hreadMul : μ' (mul + i) = C.getD i 0 :=
    (hsame _ (by omega)).trans (K.segMul.getD (K.len ▸ hi) 0)
  have hfits := abs_le.1 (K.bounded.getElem hi)
  rw [← List.getD_eq_getElem _ 0 hi, ← hreadVal] at hfits
  have hstep := twicePart_succ K.len hi
  rw [← hreadVal, ← hreadMul] at hstep
  by_cases h0 : μ' (val + i) = 0
  ·
    rw [if_neg (by simp [h0])] at hstep
    exact ⟨by simp [twiceRound, h0, Limits.Addr, abs_le]; omega, μ',
      by simp [twiceRound, update_frame_setLocal, h0, hstep], hstep ▸ hseg, hsame⟩
  by_cases h1 : 1 < μ' (mul + i)
  ·
    rw [if_pos ⟨h0, h1⟩] at hstep
    exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                   (try have := _root_.Light.Std.const_le (by assumption))
                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, twiceRound, h0, h1] <;> omega))
                                            ),
      Function.update μ' (out + (twicePart D C i).length) (2 * μ' (val + i)),
      by simp [twiceRound, update_frame_setLocal, h0, h1, hstep], hstep ▸ hseg.snoc _,
      hsame.write (by omega) _⟩
  ·
    rw [if_neg (by simp [h1])] at hstep
    exact ⟨by simp [twiceRound, h0, h1, Limits.Addr, abs_le]; omega, μ',
      by simp [twiceRound, update_frame_setLocal, h0, h1, hstep], hstep ▸ hseg, hsame⟩
theorem twice_spec {p : ℕ} (hP : P[p]? = some twiceBody) : TwiceSpec lim P p := by
  intro d val mul out V D C μ K
  (((obtain ⟨⟩ := _root_.id K))
              )
  refine Meets.of_body hP ?_
  unfold tTwice twiceBody
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (0 : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                  )
  refine Ends.next _ (Ends.whileBlock (TwiceInv μ val mul out D C) D.length ?start ?round ?done
    (hT := le_rfl)) (by simp [twiceRound]; omega)
  case start => exact ⟨μ, by simp [twicePart], by simp [twicePart], .refl⟩
  case round =>
    intro i σ hi hI
    obtain ⟨μ', rfl, -⟩ := id hI
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), twiceRound_runs K hi hI⟩
  case done =>
    rintro _ ⟨μ', rfl, hseg, hsame⟩
    rw [twicePart_length K.len] at hseg
    exact ⟨by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                     (try have := _root_.Light.Std.const_le (by assumption))
                     simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                       ), by ((((   (try have := _root_.Light.Std.space_le (by assumption))
                                    (try have := _root_.Light.Std.const_le (by assumption))
                                    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
                                      ), Ends.setTo ((twiceList D C).length : ℕ)
      ⟨rfl, hseg, hsame⟩ (by simp [twicePart_length K.len]) (by simp [twiceRound]; omega)⟩
namespace DistinctMem
variable {μ μ' : ℕ → ℤ} {val mul i : ℕ} {L D : List ℤ}
end DistinctMem
namespace Distinct
end Distinct
end Light.Sec3.ChanHe
end
end
section
public section
namespace Finset
theorem mul_card_above_average_lt {ι : Type*} {Q : Finset ι} (hQ : Q.Nonempty) (k : ℕ)
    (f : ι → ℕ) : k * #{p ∈ Q | k * ∑ p' ∈ Q, f p' < f p * #Q} < #Q := by
  set B := {p ∈ Q | k * ∑ p' ∈ Q, f p' < f p * #Q}
  rcases B.eq_empty_or_nonempty with he | hne
  · rw [he, card_empty, mul_zero]
    exact hQ.card_pos
  refine lt_of_mul_lt_mul_right (a := ∑ p ∈ Q, f p) ?_ (Nat.zero_le _)
  calc k * #B * ∑ p ∈ Q, f p = ∑ _p ∈ B, k * ∑ p' ∈ Q, f p' := by
        rw [sum_const, smul_eq_mul]; ring
    _ < ∑ p ∈ B, f p * #Q := sum_lt_sum_of_nonempty hne fun p hp => (mem_filter.mp hp).2
    _ ≤ ∑ p ∈ Q, f p * #Q := sum_le_sum_of_subset (filter_subset _ _)
    _ = #Q * ∑ p ∈ Q, f p := by rw [← sum_mul, mul_comm]
theorem exists_forall_mul_card_le_mul_sum {ι : Type*} {Q : Finset ι} (hQ : Q.Nonempty) (k : ℕ)
    (f : Fin k → ι → ℕ) : ∃ p ∈ Q, ∀ i, f i p * #Q ≤ k * ∑ p' ∈ Q, f i p' := by
  classical
  by_contra hcon
  push Not at hcon
  set B : Fin k → Finset ι := fun i => {p ∈ Q | k * ∑ p' ∈ Q, f i p' < f i p * #Q}
  have hcover : Q ⊆ univ.biUnion B := fun p hp =>
    let ⟨i, hi⟩ := hcon p hp
    mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨hp, hi⟩⟩
  obtain ⟨i₀, -⟩ := hcon _ hQ.choose_spec
  refine lt_irrefl (k * #Q) ?_
  calc k * #Q ≤ k * ∑ i, #(B i) :=
        Nat.mul_le_mul_left _ ((card_le_card hcover).trans card_biUnion_le)
    _ = ∑ i, k * #(B i) := mul_sum ..
    _ < ∑ _i : Fin k, #Q :=
        sum_lt_sum_of_nonempty ⟨i₀, mem_univ i₀⟩ fun i _ => mul_card_above_average_lt hQ k (f i)
    _ = k * #Q := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
end Finset
end
end
section
public section
namespace Nat
open Finset
theorem card_primesLE_le (m : ℕ) : #(Nat.primesLE m) ≤ m := by
  rw [Nat.primesLE_eq_filter_Icc_one]
  exact (card_filter_le _ _).trans_eq (by simp)
theorem le_log_mul_card_primesLE (m : ℕ) : m ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set l := Nat.log 2 m
  have hlt : m < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
  calc 2 ^ m ≤ (m + 1) * Nat.lcmUpto m := Chebyshev.two_pow_le_mul_lcmUpto m
    _ = (m + 1) * ∏ p ∈ Nat.primesLE m, p ^ p.log m := by rw [Nat.lcmUpto_eq_prod_pow_log]
    _ ≤ 2 ^ (l + 1) * (2 ^ (l + 1)) ^ #(Nat.primesLE m) := Nat.mul_le_mul hlt
        (prod_le_pow_card _ _ _ fun p _ => (Nat.pow_log_le_self p hm.ne').trans hlt.le)
    _ = 2 ^ ((l + 1) * (#(Nat.primesLE m) + 1)) := by rw [← pow_succ', ← pow_mul]
theorem le_card_primesLE_mul_log (w : ℕ) :
    w ≤ #(Nat.primesLE ((w + 1) * (2 * Nat.log 2 (w + 1) + 4))) := by
  set a := Nat.log 2 (w + 1)
  set m := (w + 1) * (2 * a + 4) with hm
  have hw : w + 1 < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have ha : 2 * a + 4 ≤ 2 ^ (a + 2) := by
    have := Nat.lt_two_pow_self (n := a + 1)
    rw [pow_succ]
    omega
  have hlog : Nat.log 2 m < 2 * a + 3 := Nat.log_lt_of_lt_pow (by positivity) <|
    calc m < 2 ^ (a + 1) * 2 ^ (a + 2) := Nat.mul_lt_mul_of_lt_of_le hw ha (by positivity)
      _ = 2 ^ (2 * a + 3) := by rw [← pow_add]; congr 1; omega
  have hlt : (2 * a + 3) * (w + 1) < (2 * a + 3) * (#(Nat.primesLE m) + 1) :=
    calc (2 * a + 3) * (w + 1) < (2 * a + 4) * (w + 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = m := mul_comm _ _
      _ ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := le_log_mul_card_primesLE m
      _ ≤ (2 * a + 3) * (#(Nat.primesLE m) + 1) := Nat.mul_le_mul_right _ hlog
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega
end Nat
end
end
section
public section
namespace ThreeSumApsp
namespace ChanHe
open Finset
theorem natCast_dvd_sub_iff_emod_eq (M : ℕ) (x y : ℤ) :
    (M : ℤ) ∣ x - y ↔ x % (M : ℤ) = y % (M : ℤ) :=
  Int.modEq_iff_dvd.symm.trans eq_comm
theorem card_heavy_le_coll (S : Finset ℤ) (M : ℕ) : #(heavy S M) ≤ coll S M := by
  refine (card_le_card fun x hx => ?_).trans (card_image_le (f := Prod.fst))
  obtain ⟨hxS, y, hyS, hne, hd⟩ := mem_filter.mp hx
  exact mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_offDiag.mpr ⟨hxS, hyS, hne.symm⟩, hd⟩, rfl⟩
theorem coll_le_sq (S : Finset ℤ) (M : ℕ) : coll S M ≤ #S ^ 2 :=
  calc coll S M ≤ #S.offDiag := card_filter_le _ _
    _ = #S * #S - #S := offDiag_card S
    _ ≤ #S ^ 2 := by rw [sq]; omega
private theorem Lam_pos (U : ℕ) : 1 ≤ Lam U := Nat.succ_pos _
private theorem card_prime_divisors_le {Q : Finset ℕ} (hP : ∀ p ∈ Q, p.Prime) {U : ℕ} {d : ℤ}
    (hd : d ≠ 0) (hb : |d| ≤ 2 * (U : ℤ)) : #{p ∈ Q | ((p : ℕ) : ℤ) ∣ d} ≤ Lam U := by
  set T := {p ∈ Q | ((p : ℕ) : ℤ) ∣ d}
  have hprime : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_filter.mp hp).1
  have hsub : T ⊆ d.natAbs.primeFactors := fun p hp => Nat.mem_primeFactors.mpr
    ⟨hprime p hp, Int.natCast_dvd.mp (mem_filter.mp hp).2, Int.natAbs_ne_zero.mpr hd⟩
  have hpow : 2 ^ #T ≤ 2 * U :=
    calc 2 ^ #T ≤ ∏ p ∈ T, p := pow_card_le_prod _ _ _ fun p hp => (hprime p hp).two_le
      _ ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hd)
          ((prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd _))
      _ ≤ 2 * U := by have := abs_le.mp hb; omega
  exact (Nat.le_log_of_pow_le (by norm_num) hpow).trans (Nat.le_succ _)
theorem sum_coll_mul_le {Q : Finset ℕ} (hP : ∀ p ∈ Q, p.Prime) {U : ℕ} {S : Finset ℤ}
    (hS : Bdd U S) (M₀ : ℕ) : ∑ q ∈ Q, coll S (M₀ * q) ≤ Lam U * coll S M₀ := by
  set C := {xy ∈ S.offDiag | (M₀ : ℤ) ∣ xy.1 - xy.2}
  calc ∑ q ∈ Q, coll S (M₀ * q)
      ≤ ∑ q ∈ Q, #{xy ∈ C | (q : ℤ) ∣ xy.1 - xy.2} := by
        refine sum_le_sum fun q _ => card_le_card fun xy h => ?_
        obtain ⟨hxy, hd⟩ := mem_filter.mp h
        rw [Nat.cast_mul] at hd
        exact mem_filter.mpr
          ⟨mem_filter.mpr ⟨hxy, dvd_of_mul_right_dvd hd⟩, dvd_of_mul_left_dvd hd⟩
    _ = ∑ xy ∈ C, #{q ∈ Q | ((q : ℕ) : ℤ) ∣ xy.1 - xy.2} :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ ≤ ∑ _xy ∈ C, Lam U := by
        refine sum_le_sum fun xy h => ?_
        obtain ⟨hx, hy, hne⟩ := mem_offDiag.mp (mem_filter.mp h).1
        exact card_prime_divisors_le hP (sub_ne_zero.mpr hne)
          ((abs_sub _ _).trans (by linarith [hS _ hx, hS _ hy]))
    _ = Lam U * coll S M₀ := by rw [sum_const, smul_eq_mul, mul_comm, coll]
section searches
variable {Q : Finset ℕ} {U : ℕ} {S₁ S₂ S₃ : Finset ℤ}
private theorem pick_mem {T : Finset ℕ} (h : T.Nonempty) : pick T ∈ T := by
  rw [pick, dif_pos h]
  exact T.min'_mem h
private theorem exists_prime_coll_le (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁)
    (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) (M₀ : ℕ) :
    ∃ q ∈ Q, coll S₁ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₁ M₀ ∧
      coll S₂ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₂ M₀ ∧
      coll S₃ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₃ M₀ := by
  obtain ⟨q, hq, hgood⟩ :=
    Finset.exists_forall_mul_card_le_mul_sum hQ 3 fun i q => coll (![S₁, S₂, S₃] i) (M₀ * q)
  have havg : ∀ {S : Finset ℤ}, Bdd U S →
      3 * ∑ q' ∈ Q, coll S (M₀ * q') ≤ 3 * Lam U * coll S M₀ := fun hS => by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (sum_coll_mul_le hP hS M₀)
  exact ⟨q, hq, (hgood 0).trans (havg h₁), (hgood 1).trans (havg h₂), (hgood 2).trans (havg h₃)⟩
theorem firstP_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    firstP Q (Lam U) S₁ S₂ S₃ ∈ {p ∈ Q | coll S₁ p * #Q ≤ 3 * Lam U * #S₁ ^ 2 ∧
      coll S₂ p * #Q ≤ 3 * Lam U * #S₂ ^ 2 ∧ coll S₃ p * #Q ≤ 3 * Lam U * #S₃ ^ 2} := by
  obtain ⟨p, hp, c₁, c₂, c₃⟩ := exists_prime_coll_le hQ hP h₁ h₂ h₃ 1
  rw [one_mul] at c₁ c₂ c₃
  have hall : ∀ S : Finset ℤ, 3 * Lam U * coll S 1 ≤ 3 * Lam U * #S ^ 2 :=
    fun S => Nat.mul_le_mul_left _ (coll_le_sq S 1)
  exact pick_mem
    ⟨p, mem_filter.mpr ⟨hp, c₁.trans (hall S₁), c₂.trans (hall S₂), c₃.trans (hall S₃)⟩⟩
theorem secondP_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) (p : ℕ) :
    secondP Q (Lam U) S₁ S₂ S₃ p ∈ {q ∈ Q | coll S₁ (p * q) * #Q ≤ 3 * Lam U * coll S₁ p ∧
      coll S₂ (p * q) * #Q ≤ 3 * Lam U * coll S₂ p ∧
      coll S₃ (p * q) * #Q ≤ 3 * Lam U * coll S₃ p} := by
  obtain ⟨q, hq, hc⟩ := exists_prime_coll_le hQ hP h₁ h₂ h₃ p
  exact pick_mem ⟨q, mem_filter.mpr ⟨hq, hc⟩⟩
theorem modulus_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    firstP Q (Lam U) S₁ S₂ S₃ ∈ Q ∧ secondP Q (Lam U) S₁ S₂ S₃ (firstP Q (Lam U) S₁ S₂ S₃) ∈ Q ∧
    ∀ S ∈ [S₁, S₂, S₃], coll S (modulus Q (Lam U) S₁ S₂ S₃) * #Q ^ 2 ≤ 9 * Lam U ^ 2 * #S ^ 2 := by
  obtain ⟨hp, p₁, p₂, p₃⟩ := mem_filter.mp (firstP_spec hQ hP h₁ h₂ h₃)
  obtain ⟨hq, q₁, q₂, q₃⟩ :=
    mem_filter.mp (secondP_spec hQ hP h₁ h₂ h₃ (firstP Q (Lam U) S₁ S₂ S₃))
  have hmul : ∀ {c c' s : ℕ}, c' * #Q ≤ 3 * Lam U * s ^ 2 → c * #Q ≤ 3 * Lam U * c' →
      c * #Q ^ 2 ≤ 9 * Lam U ^ 2 * s ^ 2 := fun {c c' s} hfirst hsecond =>
    calc c * #Q ^ 2 = c * #Q * #Q := by ring
      _ ≤ 3 * Lam U * c' * #Q := Nat.mul_le_mul_right _ hsecond
      _ = 3 * Lam U * (c' * #Q) := by ring
      _ ≤ 3 * Lam U * (3 * Lam U * s ^ 2) := Nat.mul_le_mul_left _ hfirst
      _ = 9 * Lam U ^ 2 * s ^ 2 := by ring
  refine ⟨hp, hq, fun S hS => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl
  · exact hmul p₁ q₁
  · exact hmul p₂ q₂
  · exact hmul p₃ q₃
theorem modulus_bounds (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) {m : ℕ} (hm : ∀ p ∈ Q, p ≤ m)
    (h₁ : Bdd U S₁) (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) :
    1 ≤ modulus Q (Lam U) S₁ S₂ S₃ ∧ modulus Q (Lam U) S₁ S₂ S₃ ≤ m ^ 2 := by
  obtain ⟨hp, hq, -⟩ := modulus_spec hQ hP h₁ h₂ h₃
  exact ⟨Nat.mul_pos (hP _ hp).pos (hP _ hq).pos, sq m ▸ Nat.mul_le_mul (hm _ hp) (hm _ hq)⟩
theorem nonempty_of_le_card_sq {n : ℕ} (hbig : 18 * Lam U ^ 2 * n ≤ #Q ^ 2) (hn : 1 ≤ n) :
    Q.Nonempty := by
  have hpos : 0 < 18 * Lam U ^ 2 * n := by have := Lam_pos U; positivity
  exact card_pos.mp ((pow_pos_iff two_ne_zero).mp (hpos.trans_le hbig))
theorem card_heavy_modulus_le (hP : ∀ p ∈ Q, p.Prime) {n : ℕ}
    (hbig : 18 * Lam U ^ 2 * n ≤ #Q ^ 2) (hn : 1 ≤ n) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    ∀ S ∈ [S₁, S₂, S₃], 2 * n * #(heavy S (modulus Q (Lam U) S₁ S₂ S₃)) ≤ #S ^ 2 := by
  intro S hS
  obtain ⟨-, -, hcoll⟩ := modulus_spec (nonempty_of_le_card_sq hbig hn) hP h₁ h₂ h₃
  set M := modulus Q (Lam U) S₁ S₂ S₃
  have hΛ : 0 < 9 * Lam U ^ 2 := by have := Lam_pos U; positivity
  refine Nat.le_of_mul_le_mul_left ?_ hΛ
  calc 9 * Lam U ^ 2 * (2 * n * #(heavy S M))
      ≤ 9 * Lam U ^ 2 * (2 * n * coll S M) := by gcongr; exact card_heavy_le_coll S M
    _ = coll S M * (18 * Lam U ^ 2 * n) := by ring
    _ ≤ coll S M * #Q ^ 2 := Nat.mul_le_mul_left _ hbig
    _ ≤ 9 * Lam U ^ 2 * #S ^ 2 := hcoll S hS
end searches
theorem wPar_le_card_primesLE (n U : ℕ) : wPar n U ≤ #(Nat.primesLE (mPar n U)) :=
  Nat.le_card_primesLE_mul_log _
theorem le_card_primesLE_mPar_sq (n U : ℕ) : 18 * Lam U ^ 2 * n ≤ #(Nat.primesLE (mPar n U)) ^ 2 :=
  calc 18 * Lam U ^ 2 * n ≤ 25 * Lam U ^ 2 * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) (Nat.lt_succ_sqrt n).le
    _ = wPar n U ^ 2 := by unfold wPar; ring
    _ ≤ #(Nat.primesLE (mPar n U)) ^ 2 := Nat.pow_le_pow_left (wPar_le_card_primesLE n U) 2
end ChanHe
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace ChanHe
open Finset
section cells
variable {S : Finset ℤ} {M U : ℕ}
def light (S : Finset ℤ) (M : ℕ) : Finset ℤ := S \ heavy S M
private theorem mem_light {x : ℤ} : x ∈ light S M ↔ x ∈ S ∧ ∀ y ∈ S, y ≠ x → ¬ (M : ℤ) ∣ x - y := by
  simp only [light, heavy, mem_sdiff, mem_filter, not_and, not_exists]
  exact and_congr_right fun h => ⟨fun g => g h, fun g _ => g⟩
theorem light_subset (S : Finset ℤ) (M : ℕ) : light S M ⊆ S := sdiff_subset
theorem heavy_subset (S : Finset ℤ) (M : ℕ) : heavy S M ⊆ S := filter_subset _ _
theorem Bdd.mono {S T : Finset ℤ} (h : Bdd U S) (hT : T ⊆ S) : Bdd U T := fun x hx => h x (hT hx)
private theorem bucket_of_light {x : ℤ} (hx : x ∈ light S M) : bucket S M (x % (M : ℤ)) = {x} := by
  obtain ⟨hxS, halone⟩ := mem_light.mp hx
  refine eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨hxS, rfl⟩, fun y hy => ?_⟩
  obtain ⟨hyS, hmod⟩ := mem_filter.mp hy
  by_contra hne
  exact halone y hyS hne ((natCast_dvd_sub_iff_emod_eq M x y).mpr hmod.symm)
private theorem arr_of_light {x : ℤ} (hx : x ∈ light S M) (pd : ℤ) {i : ℕ}
    (hi : (i : ℤ) = x % (M : ℤ)) : arr S M pd i = x := by
  rw [arr, hi, bucket_of_light hx, card_singleton, if_pos rfl, sum_singleton]
private theorem arr_mem_light_or_eq (S : Finset ℤ) (M : ℕ) (pd : ℤ) (i : ℕ) :
    arr S M pd i ∈ light S M ∨ arr S M pd i = pd := by
  unfold arr
  split_ifs with h
  · left
    obtain ⟨x, hx⟩ := card_eq_one.mp h
    have hmem : ∀ y, y ∈ bucket S M i ↔ y = x := fun y => by rw [hx, mem_singleton]
    obtain ⟨hxS, hxi⟩ := mem_filter.mp ((hmem x).mpr rfl)
    rw [hx, sum_singleton]
    refine mem_light.mpr ⟨hxS, fun y hy hne hd => hne ((hmem y).mp (mem_filter.mpr ⟨hy, ?_⟩))⟩
    rw [← hxi]
    exact ((natCast_dvd_sub_iff_emod_eq M x y).mp hd).symm
  · exact .inr rfl
private theorem neg_mem_light_neg (S : Finset ℤ) (M : ℕ) (c : ℤ) :
    -c ∈ light (S.image fun c => -c) M ↔ c ∈ light S M := by
  simp only [mem_light, mem_image, neg_inj, exists_eq_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, ne_eq, ← neg_sub', dvd_neg]
private theorem arrXY_cases (M : ℕ) (h : Bdd U S) (i : ℕ) :
    (arrXY S M U i ∈ light S M ∧ |arrXY S M U i| ≤ U) ∨ arrXY S M U i = pad U :=
  (arr_mem_light_or_eq S M (pad U) i).imp_left fun hx => ⟨hx, h _ (light_subset S M hx)⟩
private theorem arrZ_cases (M : ℕ) (h : Bdd U S) (k : ℕ) :
    (∃ c ∈ light S M, |c| ≤ U ∧ arrZ S M U k = -c) ∨ arrZ S M U k = -pad U := by
  unfold arrZ
  split_ifs with hk
  · refine (arr_mem_light_or_eq (S.image fun c => -c) M (-pad U) (k % M)).imp_left fun hx => ?_
    rw [← neg_neg (arr _ _ _ _), neg_mem_light_neg] at hx
    exact ⟨_, hx, h _ (light_subset S M hx), (neg_neg _).symm⟩
  · exact .inr rfl
private theorem arrZ_of_light {c : ℤ} (hc : c ∈ light S M) (U : ℕ) {k : ℕ} (hk : k < 2 * M)
    (hkc : ((k % M : ℕ) : ℤ) = -c % (M : ℤ)) : arrZ S M U k = -c := by
  rw [arrZ, if_pos hk]
  exact arr_of_light ((neg_mem_light_neg S M c).mpr hc) _ hkc
private theorem abs_pad (U : ℕ) : |pad U| = 2 * (U : ℤ) + 1 :=
  abs_of_nonneg (by unfold pad; positivity)
theorem abs_arrXY_le (M : ℕ) (h : Bdd U S) (i : ℕ) : |arrXY S M U i| ≤ 2 * (U : ℤ) + 1 := by
  rcases arrXY_cases M h i with ⟨-, hb⟩ | he
  · exact hb.trans (by omega)
  · rw [he, abs_pad]
theorem abs_arrZ_le (M : ℕ) (h : Bdd U S) (k : ℕ) : |arrZ S M U k| ≤ 2 * (U : ℤ) + 1 := by
  rcases arrZ_cases M h k with ⟨c, -, hb, he⟩ | he
  · rw [he, abs_neg]
    exact hb.trans (by omega)
  · rw [he, abs_neg, abs_pad]
end cells
theorem node_correct {U M N : ℕ} (hM : 1 ≤ M) (hN : 2 * M ≤ N) {S₁ S₂ S₃ : Finset ℤ}
    (h₁ : Bdd U S₁) (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) :
    ConvSol N (arrXY S₁ M U) (arrXY S₂ M U) (arrZ S₃ M U) ↔
      HasSol (light S₁ M) (light S₂ M) (light S₃ M) := by
  constructor
  · rintro ⟨i, j, -, heq⟩
    rcases arrXY_cases M h₁ i with ⟨ha, ha'⟩ | ha <;>
      rcases arrXY_cases M h₂ j with ⟨hb, hb'⟩ | hb <;>
      rcases arrZ_cases M h₃ (i + j) with ⟨c, hc, hc', hz⟩ | hz
    · exact ⟨_, ha, _, hb, c, hc, by rw [heq, hz]; ring⟩
    all_goals
      simp only [pad, abs_le] at *
      omega
  · rintro ⟨a, ha, b, hb, c, hc, hsum⟩
    have hM0 : (M : ℤ) ≠ 0 := by omega
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg a hM0)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg b hM0)
    have hiM := Int.emod_lt_of_pos a (by omega : (0 : ℤ) < M)
    have hjM := Int.emod_lt_of_pos b (by omega : (0 : ℤ) < M)
    have hij : (((i + j) % M : ℕ) : ℤ) = -c % (M : ℤ) := by
      push_cast
      rw [← hi, ← hj, ← Int.add_emod]
      congr 1
      omega
    refine ⟨i, j, by omega, ?_⟩
    rw [arrXY, arr_of_light ha _ hi.symm, arrXY, arr_of_light hb _ hj.symm,
      arrZ_of_light hc U (by omega) hij]
    omega
def dSeq (j : ℕ) : ℕ := 2 ^ (2 ^ j - 1)
private theorem dSeq_succ (j : ℕ) : dSeq (j + 1) = 2 * dSeq j ^ 2 := by
  have hexp : 2 ^ (j + 1) - 1 = 1 + (2 ^ j - 1) * 2 := by
    have := Nat.one_le_two_pow (n := j)
    rw [pow_succ]
    omega
  rw [dSeq, dSeq, hexp, pow_add, pow_mul, pow_one]
private theorem dSeq_mono {i j : ℕ} (h : i ≤ j) : dSeq i ≤ dSeq j :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h) 1)
private theorem lt_dSeq_height (n : ℕ) : n < dSeq (height n) := by
  have hclog : Nat.log 2 n + 2 ≤ 2 ^ height n := Nat.le_pow_clog (by norm_num) _
  calc n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    _ ≤ dSeq (height n) := Nat.pow_le_pow_right (by norm_num) (by omega)
theorem height_pos (n : ℕ) : 1 ≤ height n :=
  Nat.clog_pos (b := 2) (n := Nat.log 2 n + 2) (by norm_num) (by omega)
private theorem two_pow_height_le (n : ℕ) : 2 ^ height n ≤ 2 * Nat.log 2 n + 2 := by
  have hlt : 2 ^ (height n - 1) < Nat.log 2 n + 2 :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := Nat.log 2 n + 2) (by norm_num) (by omega)
  rw [← Nat.sub_add_cancel (height_pos n), pow_succ]
  omega
structure Replaced (n U j : ℕ) (T : Finset ℤ) : Prop where
  bdd : Bdd U T
  card : #T * dSeq j ≤ n
namespace Replaced
variable {n U j : ℕ} {T : Finset ℤ}
theorem zero (hb : Bdd U T) (hc : #T ≤ n) : Replaced n U 0 T :=
  ⟨hb, by rwa [dSeq, pow_zero, Nat.sub_self, pow_zero, mul_one]⟩
theorem heavy (h : Replaced n U j T) (hn : 1 ≤ n) {M : ℕ}
    (hM : 2 * n * #(ChanHe.heavy T M) ≤ #T ^ 2) : Replaced n U (j + 1) (ChanHe.heavy T M) := by
  refine ⟨h.bdd.mono (heavy_subset T M), Nat.le_of_mul_le_mul_left ?_ hn⟩
  calc n * (#(ChanHe.heavy T M) * dSeq (j + 1))
      = 2 * n * #(ChanHe.heavy T M) * dSeq j ^ 2 := by rw [dSeq_succ]; ring
    _ ≤ #T ^ 2 * dSeq j ^ 2 := Nat.mul_le_mul_right _ hM
    _ = #T * dSeq j * (#T * dSeq j) := by ring
    _ ≤ n * n := Nat.mul_le_mul h.card h.card
theorem eq_empty (h : Replaced n U j T) (hj : height n ≤ j) : T = ∅ := by
  by_contra hne
  have hcard : 1 ≤ #T := card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
  have := lt_dSeq_height n
  have := dSeq_mono hj
  have := Nat.mul_le_mul_right (dSeq j) hcard
  have := h.card
  omega
end Replaced
private theorem exists_eq_empty {n U j₁ j₂ j₃ : ℕ} {T₁ T₂ T₃ : Finset ℤ} (r₁ : Replaced n U j₁ T₁)
    (r₂ : Replaced n U j₂ T₂) (r₃ : Replaced n U j₃ T₃) (hj : 3 * height n - 2 ≤ j₁ + j₂ + j₃) :
    T₁ = ∅ ∨ T₂ = ∅ ∨ T₃ = ∅ := by
  have := height_pos n
  rcases (by omega : height n ≤ j₁ ∨ height n ≤ j₂ ∨ height n ≤ j₃) with h | h | h
  · exact .inl (r₁.eq_empty h)
  · exact .inr (.inl (r₂.eq_empty h))
  · exact .inr (.inr (r₃.eq_empty h))
theorem HasSol.mono {S₁ S₂ S₃ T₁ T₂ T₃ : Finset ℤ} (h : HasSol S₁ S₂ S₃) (h₁ : S₁ ⊆ T₁)
    (h₂ : S₂ ⊆ T₂) (h₃ : S₃ ⊆ T₃) : HasSol T₁ T₂ T₃ :=
  let ⟨a, ha, b, hb, c, hc, hs⟩ := h
  ⟨a, h₁ ha, b, h₂ hb, c, h₃ hc, hs⟩
private theorem not_hasSol_of_empty {S₁ S₂ S₃ : Finset ℤ} (h : S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅) :
    ¬ HasSol S₁ S₂ S₃ := by
  rintro ⟨a, ha, b, hb, c, hc, -⟩
  rcases h with rfl | rfl | rfl <;> simp_all
theorem hasSol_split (S₁ S₂ S₃ : Finset ℤ) (M : ℕ) :
    HasSol S₁ S₂ S₃ ↔ HasSol (light S₁ M) (light S₂ M) (light S₃ M) ∨
      (HasSol (heavy S₁ M) S₂ S₃ ∨ HasSol S₁ (heavy S₂ M) S₃) ∨ HasSol S₁ S₂ (heavy S₃ M) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hs⟩
    by_contra hno
    simp only [not_or] at hno
    obtain ⟨hlight, ⟨hheavy₁, hheavy₂⟩, hheavy₃⟩ := hno
    exact hlight ⟨a, mem_sdiff.mpr ⟨ha, fun h => hheavy₁ ⟨a, h, b, hb, c, hc, hs⟩⟩,
      b, mem_sdiff.mpr ⟨hb, fun h => hheavy₂ ⟨a, ha, b, h, c, hc, hs⟩⟩,
      c, mem_sdiff.mpr ⟨hc, fun h => hheavy₃ ⟨a, ha, b, hb, c, h, hs⟩⟩, hs⟩
  · rintro (h | (h | h) | h)
    · exact h.mono (light_subset _ _) (light_subset _ _) (light_subset _ _)
    · exact h.mono (heavy_subset _ _) Subset.rfl Subset.rfl
    · exact h.mono Subset.rfl (heavy_subset _ _) Subset.rfl
    · exact h.mono Subset.rfl Subset.rfl (heavy_subset _ _)
theorem length_nodes_le (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    2 * (nodes Q Λ f S₁ S₂ S₃).length + 1 ≤ 3 ^ f := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => simp [nodes]
  | succ f ih =>
    unfold nodes
    split_ifs with h
    · exact Nat.one_le_pow _ _ (by norm_num)
    · simp only [List.length_cons, List.length_append]
      have := ih (heavy S₁ (modulus Q Λ S₁ S₂ S₃)) S₂ S₃
      have := ih S₁ (heavy S₂ (modulus Q Λ S₁ S₂ S₃)) S₃
      have := ih S₁ S₂ (heavy S₃ (modulus Q Λ S₁ S₂ S₃))
      rw [pow_succ]
      omega
theorem nodes_subset (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    ∀ ν ∈ nodes Q Λ f S₁ S₂ S₃, ν.S₁ ⊆ S₁ ∧ ν.S₂ ⊆ S₂ ∧ ν.S₃ ⊆ S₃ := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => simp [nodes]
  | succ f ih =>
    intro ν hν
    unfold nodes at hν
    split_ifs at hν with he
    · simp at hν
    · simp only [List.mem_cons, List.mem_append] at hν
      rcases hν with rfl | (hν | hν) | hν
      · exact ⟨Subset.rfl, Subset.rfl, Subset.rfl⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁.trans (heavy_subset _ _), s₂, s₃⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁, s₂.trans (heavy_subset _ _), s₃⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁, s₂, s₃.trans (heavy_subset _ _)⟩
structure Candidates (n U m : ℕ) (Q : Finset ℕ) : Prop where
  prime : ∀ p ∈ Q, p.Prime
  le : ∀ p ∈ Q, p ≤ m
  card : 18 * Lam U ^ 2 * n ≤ #Q ^ 2
private theorem candidates_primesLE (n U : ℕ) :
    Candidates n U (mPar n U) (Nat.primesLE (mPar n U)) :=
  ⟨fun _ => Nat.prime_of_mem_primesLE, fun _ => Nat.le_of_mem_primesLE,
    le_card_primesLE_mPar_sq n U⟩
theorem nodes_correct {n U N m : ℕ} (hn : 1 ≤ n) {Q : Finset ℕ} (hQ : Candidates n U m Q)
    (hN : 2 * m ^ 2 ≤ N) (f : ℕ) {T₁ T₂ T₃ : Finset ℤ} {j₁ j₂ j₃ : ℕ} (r₁ : Replaced n U j₁ T₁)
    (r₂ : Replaced n U j₂ T₂) (r₃ : Replaced n U j₃ T₃)
    (hf : 3 * height n - 2 ≤ f + j₁ + j₂ + j₃) :
    HasSol T₁ T₂ T₃ ↔ ∃ ν ∈ nodes Q (Lam U) f T₁ T₂ T₃, ν.Conv U N := by
  induction f generalizing T₁ T₂ T₃ j₁ j₂ j₃ with
  | zero => simp [nodes, not_hasSol_of_empty (exists_eq_empty r₁ r₂ r₃ (by omega))]
  | succ f ih =>
    unfold nodes
    split_ifs with he
    · simp [not_hasSol_of_empty he]
    obtain ⟨hM1, hMm⟩ := modulus_bounds (nonempty_of_le_card_sq hQ.card hn) hQ.prime hQ.le
      r₁.bdd r₂.bdd r₃.bdd
    have hheavy := card_heavy_modulus_le hQ.prime hQ.card hn r₁.bdd r₂.bdd r₃.bdd
    generalize modulus Q (Lam U) T₁ T₂ T₃ = M at hM1 hMm hheavy ⊢
    have hnode := node_correct (N := N) hM1 (by omega) r₁.bdd r₂.bdd r₃.bdd
    have hchild₁ := ih (r₁.heavy hn (hheavy T₁ (by simp))) r₂ r₃ (by omega)
    have hchild₂ := ih r₁ (r₂.heavy hn (hheavy T₂ (by simp))) r₃ (by omega)
    have hchild₃ := ih r₁ r₂ (r₃.heavy hn (hheavy T₃ (by simp))) (by omega)
    rw [hasSol_split T₁ T₂ T₃ M, ← hnode, hchild₁, hchild₂, hchild₃]
    simp only [List.mem_cons, List.mem_append, or_and_right, exists_or, exists_eq_left]
    rfl
structure Admissible (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) : Prop where
  card₁ : #S₁ ≤ n
  card₂ : #S₂ ≤ n
  card₃ : #S₃ ≤ n
  bdd₁ : Bdd U S₁
  bdd₂ : Bdd U S₂
  bdd₃ : Bdd U S₃
theorem Admissible.of_mem {n U : ℕ} {S₁ S₂ S₃ : Finset ℤ} (h : Admissible n U S₁ S₂ S₃) {ν : Node}
    (hν : ν ∈ reduction n U S₁ S₂ S₃) : Admissible n U ν.S₁ ν.S₂ ν.S₃ :=
  let ⟨s₁, s₂, s₃⟩ := nodes_subset _ _ _ _ _ _ ν hν
  ⟨(card_le_card s₁).trans h.card₁, (card_le_card s₂).trans h.card₂,
    (card_le_card s₃).trans h.card₃, h.bdd₁.mono s₁, h.bdd₂.mono s₂, h.bdd₃.mono s₃⟩
theorem reduction_correct {n U N : ℕ} (hn : 1 ≤ n) (hN : 2 * mPar n U ^ 2 ≤ N)
    {S₁ S₂ S₃ : Finset ℤ} (h : Admissible n U S₁ S₂ S₃) :
    HasSol S₁ S₂ S₃ ↔ ∃ ν ∈ reduction n U S₁ S₂ S₃, ν.Conv U N :=
  nodes_correct hn (candidates_primesLE n U) hN (fuel n) (.zero h.bdd₁ h.card₁)
    (.zero h.bdd₂ h.card₂) (.zero h.bdd₃ h.card₃) le_rfl
theorem three_pow_fuel_le (n : ℕ) : 3 ^ fuel n ≤ (2 * Nat.log 2 n + 2) ^ 5 :=
  calc 3 ^ fuel n ≤ 3 ^ (3 * height n) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    _ = 27 ^ height n := by rw [pow_mul]; norm_num
    _ ≤ 32 ^ height n := Nat.pow_le_pow_left (by norm_num) _
    _ = (2 ^ height n) ^ 5 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ (2 * Nat.log 2 n + 2) ^ 5 := Nat.pow_le_pow_left (two_pow_height_le n) 5
end ChanHe
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace ChanHe
open Finset
section distinct
variable {U : ℕ} {S : Finset ℤ}
private theorem lab_cast {x : ℤ} (hx : |x| ≤ (U : ℤ)) : ((lab U x : ℕ) : ℤ) = x + U :=
  Int.toNat_of_nonneg (by have := (abs_le.mp hx).1; omega)
private theorem lab_lt {x : ℤ} (hx : |x| ≤ (U : ℤ)) : lab U x < 2 ^ Lam U := by
  have := lab_cast hx
  have := (abs_le.mp hx).2
  exact (by omega : lab U x ≤ 2 * U).trans_lt (Nat.lt_pow_succ_log_self (by norm_num) _)
private theorem exists_testBit_lab_ne {x y : ℤ} (hx : |x| ≤ (U : ℤ)) (hy : |y| ≤ (U : ℤ))
    (hne : x ≠ y) : ∃ β < Lam U, (lab U x).testBit β ≠ (lab U y).testBit β := by
  have hlab : lab U x ≠ lab U y := fun h => hne (by have := lab_cast hx; have := lab_cast hy; omega)
  obtain ⟨β, hβ⟩ := Nat.exists_testBit_ne_of_ne hlab
  refine ⟨β, lt_of_not_ge fun hΛ => hβ ?_, hβ⟩
  have hpow := Nat.pow_le_pow_right (n := 2) (by norm_num) hΛ
  rw [Nat.testBit_eq_false_of_lt ((lab_lt hx).trans_le hpow),
    Nat.testBit_eq_false_of_lt ((lab_lt hy).trans_le hpow)]
private theorem exists_split_of_testBit (h : Bdd U S) {x y z : ℤ} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) {β : ℕ} (hβ : β < Lam U) (hxy : (lab U y).testBit β = !(lab U x).testBit β)
    (hxz : (lab U z).testBit β = !(lab U x).testBit β) (hyz : y ≠ z) (hs : x + y + z = 0) :
    ∃ β < Lam U, ∃ β' < Lam U, ∃ v : Bool,
      HasSol (splitA U β v S) (splitB U β β' v false S) (splitB U β β' v true S) := by
  obtain ⟨β', hβ', hne⟩ := exists_testBit_lab_ne (h y hy) (h z hz) hyz
  refine ⟨β, hβ, β', hβ', (lab U x).testBit β, x, mem_filter.mpr ⟨hx, rfl⟩, ?_⟩
  cases hyβ' : (lab U y).testBit β'
  · exact ⟨y, mem_filter.mpr ⟨hy, hxy, hyβ'⟩,
      z, mem_filter.mpr ⟨hz, hxz, by simpa [hyβ'] using hne.symm⟩, hs⟩
  · exact ⟨z, mem_filter.mpr ⟨hz, hxz, by simpa [hyβ'] using hne.symm⟩,
      y, mem_filter.mpr ⟨hy, hxy, hyβ'⟩, by omega⟩
theorem distinct_iff_split (h : Bdd U S) :
    (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a + b + c = 0) ↔
      ∃ β < Lam U, ∃ β' < Lam U, ∃ v : Bool,
        HasSol (splitA U β v S) (splitB U β β' v false S) (splitB U β β' v true S) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hab, hbc, hac, hs⟩
    obtain ⟨β, hβ, hbit⟩ := exists_testBit_lab_ne (h a ha) (h b hb) hab
    by_cases hcb : (lab U c).testBit β = (lab U b).testBit β
    · exact exists_split_of_testBit h ha hb hc hβ (Bool.eq_not_of_ne hbit.symm)
        (hcb.trans (Bool.eq_not_of_ne hbit.symm)) hbc hs
    · exact exists_split_of_testBit h hb ha hc hβ (Bool.eq_not_of_ne hbit)
        (Bool.eq_not_of_ne hcb) hac (by omega)
  · rintro ⟨β, -, β', -, v, a, ha, b, hb, c, hc, hs⟩
    obtain ⟨haS, haβ⟩ := mem_filter.mp ha
    obtain ⟨hbS, hbβ, hbβ'⟩ := mem_filter.mp hb
    obtain ⟨hcS, hcβ, hcβ'⟩ := mem_filter.mp hc
    refine ⟨a, haS, b, hbS, c, hcS, ?_, ?_, ?_, hs⟩
    · rintro rfl
      simp [haβ] at hbβ
    · rintro rfl
      simp [hbβ'] at hcβ'
    · rintro rfl
      simp [haβ] at hcβ
end distinct
section positions
variable {n : ℕ} {x : Fin n → ℤ}
def Degenerate (x : Fin n → ℤ) : Prop :=
  (∃ a : ℤ, a ≠ 0 ∧ 2 ≤ #{i : Fin n | x i = a} ∧ ∃ k, x k = -2 * a) ∨ 3 ≤ #{i : Fin n | x i = 0}
private theorem degenerate_of_eq {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (he : x i = x j) (hs : x i + x j + x k = 0) : Degenerate x := by
  by_cases h0 : x i = 0
  · exact .inr (two_lt_card.mpr ⟨i, by simpa using h0, j, by simpa using he ▸ h0,
      k, by simp only [mem_filter, mem_univ, true_and]; omega, hij, hik, hjk⟩)
  · exact .inl ⟨x i, h0, one_lt_card.mpr ⟨i, by simp, j, by simp [he], hij⟩, k, by omega⟩
theorem threeSum_iff_distinct_or_degenerate (x : Fin n → ℤ) :
    ThreeSum x ↔
      (∃ a ∈ univ.image x, ∃ b ∈ univ.image x, ∃ c ∈ univ.image x,
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a + b + c = 0) ∨ Degenerate x := by
  constructor
  · rintro ⟨i, j, k, hij, hjk, hik, hs⟩
    by_cases hxij : x i = x j
    · exact .inr (degenerate_of_eq hij hik hjk hxij hs)
    by_cases hxjk : x j = x k
    · exact .inr (degenerate_of_eq hjk hij.symm hik.symm hxjk (by omega))
    by_cases hxik : x i = x k
    · exact .inr (degenerate_of_eq hik hij hjk.symm hxik (by omega))
    · exact .inl ⟨x i, by simp, x j, by simp, x k, by simp, hxij, hxjk, hxik, hs⟩
  · rintro (⟨a, ha, b, hb, c, hc, hab, hbc, hac, hs⟩ | ⟨a, ha0, h2, k, hk⟩ | h3)
    · obtain ⟨i, -, rfl⟩ := mem_image.mp ha
      obtain ⟨j, -, rfl⟩ := mem_image.mp hb
      obtain ⟨k, -, rfl⟩ := mem_image.mp hc
      exact ⟨i, j, k, fun e => hab (e ▸ rfl), fun e => hbc (e ▸ rfl), fun e => hac (e ▸ rfl), hs⟩
    · obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp h2
      simp only [mem_filter, mem_univ, true_and] at hi hj
      have hne : ∀ t : Fin n, x t = a → t ≠ k := by
        rintro t ht rfl
        omega
      exact ⟨i, j, k, hij, hne j hj, hne i hi, by omega⟩
    · obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := two_lt_card.mp h3
      simp only [mem_filter, mem_univ, true_and] at hi hj hk
      exact ⟨i, j, k, hij, hjk, hik, by omega⟩
theorem degenerate_iff (x : Fin n → ℤ) :
    Degenerate x ↔ HasSol (twiceSet x) {0} (univ.image x) ∨ HasSol (zeroSet x) {0} {0} := by
  refine or_congr ⟨?_, ?_⟩ ⟨fun h3 => ?_, ?_⟩
  · rintro ⟨a, ha0, h2, k, hk⟩
    obtain ⟨i, hi, -⟩ := one_lt_card.mp h2
    have ha : a ∈ univ.image x := mem_image.mpr ⟨i, mem_univ i, (mem_filter.mp hi).2⟩
    exact ⟨2 * a, mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, ha0, h2⟩, rfl⟩, 0, mem_singleton_self 0,
      x k, mem_image_of_mem x (mem_univ k), by omega⟩
  · rintro ⟨_, ha', b, hb, _, hc, hs⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
    obtain ⟨-, ha0, h2⟩ := mem_filter.mp ha
    obtain ⟨k, -, rfl⟩ := mem_image.mp hc
    rw [mem_singleton.mp hb] at hs
    exact ⟨a, ha0, h2, k, by omega⟩
  · rw [zeroSet, if_pos h3]
    exact ⟨0, mem_singleton_self 0, 0, mem_singleton_self 0, 0, mem_singleton_self 0, rfl⟩
  · rintro ⟨a, ha, -⟩
    by_contra h3
    rw [zeroSet, if_neg h3] at ha
    exact notMem_empty a ha
end positions
section oneArray
variable {N W : ℕ} {X Y Z : ℕ → ℤ}
private theorem oneArray_val (W : ℕ) (X Y Z : ℕ → ℤ) (u : ℕ) :
    oneArray W X Y Z u = if u % 4 = 1 then X (u / 4) + (3 * W + 1)
      else if u % 4 = 2 then Y (u / 4) + 3 * (3 * W + 1)
      else if u % 4 = 3 then Z (u / 4) + 4 * (3 * W + 1) else 10 * (3 * W + 1) := rfl
private theorem oneArray_sol (W : ℕ) {i j : ℕ} (h : X i + Y j = Z (i + j)) :
    oneArray W X Y Z (4 * i + 1) + oneArray W X Y Z (4 * j + 2) =
      oneArray W X Y Z (4 * i + 1 + (4 * j + 2)) := by
  simp only [oneArray_val, show (4 * i + 1) % 4 = 1 by omega, show (4 * j + 2) % 4 = 2 by omega,
    show (4 * i + 1 + (4 * j + 2)) % 4 = 3 by omega, ↓reduceIte, Nat.reduceEqDiff]
  rw [show (4 * i + 1) / 4 = i by omega, show (4 * j + 2) / 4 = j by omega,
    show (4 * i + 1 + (4 * j + 2)) / 4 = i + j by omega]
  omega
private theorem convSol_of_oneArray (hX : ∀ i < N, |X i| ≤ (W : ℤ)) (hY : ∀ i < N, |Y i| ≤ (W : ℤ))
    (hZ : ∀ i < N, |Z i| ≤ (W : ℤ)) {u v : ℕ} (huv : u + v < 4 * N)
    (h : oneArray W X Y Z u + oneArray W X Y Z v = oneArray W X Y Z (u + v)) :
    ConvSol N X Y Z := by
  have hW : ∀ i < N, (-(W : ℤ) ≤ X i ∧ X i ≤ W) ∧ (-(W : ℤ) ≤ Y i ∧ Y i ≤ W) ∧
      (-(W : ℤ) ≤ Z i ∧ Z i ≤ W) :=
    fun i hi => ⟨abs_le.mp (hX i hi), abs_le.mp (hY i hi), abs_le.mp (hZ i hi)⟩
  have hWu := hW (u / 4) (by omega)
  have hWv := hW (v / 4) (by omega)
  have hWuv := hW ((u + v) / 4) (by omega)
  simp only [oneArray_val] at h
  by_cases h12 : u % 4 = 1 ∧ v % 4 = 2
  · refine ⟨u / 4, v / 4, by omega, ?_⟩
    rw [show u / 4 + v / 4 = (u + v) / 4 by omega]
    simp only [h12.1, h12.2, show (u + v) % 4 = 3 by omega, ↓reduceIte, Nat.reduceEqDiff] at h
    omega
  by_cases h21 : u % 4 = 2 ∧ v % 4 = 1
  · refine ⟨v / 4, u / 4, by omega, ?_⟩
    rw [show v / 4 + u / 4 = (u + v) / 4 by omega]
    simp only [h21.1, h21.2, show (u + v) % 4 = 3 by omega, ↓reduceIte, Nat.reduceEqDiff] at h
    omega
  · split_ifs at h <;> omega
theorem oneArray_correct (hX : ∀ i < N, |X i| ≤ (W : ℤ)) (hY : ∀ i < N, |Y i| ≤ (W : ℤ))
    (hZ : ∀ i < N, |Z i| ≤ (W : ℤ)) : ConvSol N X Y Z ↔ ConvOne (4 * N) (oneArray W X Y Z) :=
  ⟨fun ⟨i, j, _, h⟩ => ⟨4 * i + 1, 4 * j + 2, by omega, oneArray_sol W h⟩,
    fun ⟨_, _, huv, h⟩ => convSol_of_oneArray hX hY hZ huv h⟩
theorem abs_oneArray_le (hX : ∀ i < N, |X i| ≤ (W : ℤ)) (hY : ∀ i < N, |Y i| ≤ (W : ℤ))
    (hZ : ∀ i < N, |Z i| ≤ (W : ℤ)) {u : ℕ} (hu : u < 4 * N) :
    |oneArray W X Y Z u| ≤ 30 * (W : ℤ) + 10 := by
  have := abs_le.mp (hX (u / 4) (by omega))
  have := abs_le.mp (hY (u / 4) (by omega))
  have := abs_le.mp (hZ (u / 4) (by omega))
  rw [oneArray_val, abs_le]
  split_ifs <;> constructor <;> omega
end oneArray
section node
variable {n U : ℕ} {ν : Node}
private theorem Node.abs_arr_le (b₁ : Bdd U ν.S₁) (b₂ : Bdd U ν.S₂) (b₃ : Bdd U ν.S₃) :
    (∀ i, |arrXY ν.S₁ ν.M U i| ≤ ((2 * U + 1 : ℕ) : ℤ)) ∧
      (∀ i, |arrXY ν.S₂ ν.M U i| ≤ ((2 * U + 1 : ℕ) : ℤ)) ∧
      ∀ i, |arrZ ν.S₃ ν.M U i| ≤ ((2 * U + 1 : ℕ) : ℤ) := by
  push_cast
  exact ⟨abs_arrXY_le ν.M b₁, abs_arrXY_le ν.M b₂, abs_arrZ_le ν.M b₃⟩
theorem Node.conv_iff_convOne (b₁ : Bdd U ν.S₁) (b₂ : Bdd U ν.S₂) (b₃ : Bdd U ν.S₃) (N : ℕ) :
    ν.Conv U N ↔ ConvOne (4 * N) (ν.oneArray U) :=
  let ⟨hX, hY, hZ⟩ := Node.abs_arr_le b₁ b₂ b₃
  oneArray_correct (fun i _ => hX i) (fun i _ => hY i) (fun i _ => hZ i)
theorem Node.abs_oneArray_le (b₁ : Bdd U ν.S₁) (b₂ : Bdd U ν.S₂) (b₃ : Bdd U ν.S₃) (u : ℕ) :
    |ν.oneArray U u| ≤ 60 * (U : ℤ) + 40 := by
  obtain ⟨hX, hY, hZ⟩ := Node.abs_arr_le b₁ b₂ b₃
  refine (ChanHe.abs_oneArray_le (N := u + 1) (fun i _ => hX i) (fun i _ => hY i)
    (fun i _ => hZ i) (by omega)).trans_eq ?_
  push_cast
  ring
theorem reduction_correct_oneArray (hn : 1 ≤ n) {T₁ T₂ T₃ : Finset ℤ}
    (h : Admissible n U T₁ T₂ T₃) :
    HasSol T₁ T₂ T₃ ↔
      ∃ ν ∈ reduction n U T₁ T₂ T₃, ConvOne (8 * mPar n U ^ 2) (ν.oneArray U) := by
  rw [reduction_correct hn le_rfl h, show 8 * mPar n U ^ 2 = 4 * (2 * mPar n U ^ 2) by ring]
  refine exists_congr fun ν => and_congr_right fun hν => ?_
  have hν' := h.of_mem hν
  exact Node.conv_iff_convOne hν'.bdd₁ hν'.bdd₂ hν'.bdd₃ _
end node
section inputs
variable {n U : ℕ} {x : Fin n → ℤ}
private theorem bdd_image (hx : ∀ i, |x i| ≤ (U : ℤ)) : Bdd (2 * U) (univ.image x) := by
  intro a ha
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  exact (hx i).trans (by omega)
theorem bdd_twiceSet (hx : ∀ i, |x i| ≤ (U : ℤ)) : Bdd (2 * U) (twiceSet x) := by
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
  obtain ⟨i, -, rfl⟩ := mem_image.mp (mem_filter.mp ha).1
  rw [abs_mul, abs_two, Nat.cast_mul, Nat.cast_two]
  exact mul_le_mul_of_nonneg_left (hx i) (by norm_num)
theorem bdd_zero (U : ℕ) : Bdd U {0} := by
  intro a ha
  rw [mem_singleton.mp ha, abs_zero]
  exact Nat.cast_nonneg U
theorem bdd_zeroSet (U : ℕ) (x : Fin n → ℤ) : Bdd U (zeroSet x) := by
  unfold zeroSet
  split_ifs
  · exact bdd_zero U
  · exact fun a ha => absurd ha (notMem_empty a)
theorem card_image_univ_le (x : Fin n → ℤ) : #(univ.image x) ≤ n :=
  card_image_le.trans_eq (card_fin n)
private theorem card_twiceSet_le (x : Fin n → ℤ) : #(twiceSet x) ≤ n :=
  card_image_le.trans ((card_filter_le _ _).trans (card_image_univ_le x))
private theorem card_zeroSet_le (x : Fin n → ℤ) : #(zeroSet x) ≤ 1 := by
  unfold zeroSet
  split_ifs <;> simp
inductive IsInput (U : ℕ) (x : Fin n → ℤ) : Finset ℤ → Finset ℤ → Finset ℤ → Prop
  | split {β β' : ℕ} (hβ : β < Lam (2 * U)) (hβ' : β' < Lam (2 * U)) (v : Bool) :
    IsInput U x (splitA (2 * U) β v (univ.image x)) (splitB (2 * U) β β' v false (univ.image x))
      (splitB (2 * U) β β' v true (univ.image x))
  | twice : IsInput U x (twiceSet x) {0} (univ.image x)
  | zero : IsInput U x (zeroSet x) {0} {0}
private theorem exists_isInput_iff (P : Finset ℤ → Finset ℤ → Finset ℤ → Prop) :
    (∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ P T₁ T₂ T₃) ↔
      (∃ β < Lam (2 * U), ∃ β' < Lam (2 * U), ∃ v : Bool,
        P (splitA (2 * U) β v (univ.image x)) (splitB (2 * U) β β' v false (univ.image x))
          (splitB (2 * U) β β' v true (univ.image x))) ∨
      P (twiceSet x) {0} (univ.image x) ∨ P (zeroSet x) {0} {0} := by
  constructor
  · rintro ⟨_, _, _, ⟨hβ, hβ', v⟩ | _ | _, h⟩
    · exact .inl ⟨_, hβ, _, hβ', v, h⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rintro (⟨β, hβ, β', hβ', v, h⟩ | h | h)
    · exact ⟨_, _, _, .split hβ hβ' v, h⟩
    · exact ⟨_, _, _, .twice, h⟩
    · exact ⟨_, _, _, .zero, h⟩
theorem threeSum_iff_exists_input (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ThreeSum x ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ HasSol T₁ T₂ T₃ := by
  rw [threeSum_iff_distinct_or_degenerate, distinct_iff_split (bdd_image hx), degenerate_iff,
    exists_isInput_iff]
theorem mem_allNodes_iff {ν : Node} :
    ν ∈ allNodes n U x ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ ν ∈ reduction n (2 * U) T₁ T₂ T₃ := by
  rw [exists_isInput_iff fun T₁ T₂ T₃ => ν ∈ reduction n (2 * U) T₁ T₂ T₃]
  simp [allNodes]
theorem IsInput.admissible (hn : 1 ≤ n) (hx : ∀ i, |x i| ≤ (U : ℤ)) {T₁ T₂ T₃ : Finset ℤ}
    (h : IsInput U x T₁ T₂ T₃) : Admissible n (2 * U) T₁ T₂ T₃ := by
  have hb := bdd_image hx
  have hc := card_image_univ_le x
  have hc0 : #({0} : Finset ℤ) ≤ n := hn
  cases h with
  | split hβ hβ' v =>
    exact ⟨(card_filter_le _ _).trans hc, (card_filter_le _ _).trans hc,
      (card_filter_le _ _).trans hc, hb.mono (filter_subset _ _), hb.mono (filter_subset _ _),
      hb.mono (filter_subset _ _)⟩
  | twice => exact ⟨card_twiceSet_le x, hc0, hc, bdd_twiceSet hx, bdd_zero _, hb⟩
  | zero => exact ⟨(card_zeroSet_le x).trans hn, hc0, hc0, bdd_zeroSet _ x, bdd_zero _, bdd_zero _⟩
end inputs
theorem instances_correct (n U : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ThreeSum x ↔ ∃ y ∈ instances n U x, ConvOne (8 * mPar n (2 * U) ^ 2) y :=
  calc ThreeSum x
      ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ HasSol T₁ T₂ T₃ := threeSum_iff_exists_input hx
    _ ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ ∃ ν ∈ reduction n (2 * U) T₁ T₂ T₃,
          ConvOne (8 * mPar n (2 * U) ^ 2) (ν.oneArray (2 * U)) :=
        exists₃_congr fun _ _ _ => and_congr_right fun hT =>
          reduction_correct_oneArray hn (hT.admissible hn hx)
    _ ↔ ∃ ν ∈ allNodes n U x, ConvOne (8 * mPar n (2 * U) ^ 2) (ν.oneArray (2 * U)) :=
        ⟨fun ⟨T₁, T₂, T₃, hT, ν, hν, h⟩ => ⟨ν, mem_allNodes_iff.mpr ⟨T₁, T₂, T₃, hT, hν⟩, h⟩,
          fun ⟨ν, hν, h⟩ =>
            let ⟨T₁, T₂, T₃, hT, hν'⟩ := mem_allNodes_iff.mp hν
            ⟨T₁, T₂, T₃, hT, ν, hν', h⟩⟩
    _ ↔ ∃ y ∈ instances n U x, ConvOne (8 * mPar n (2 * U) ^ 2) y := by
        simp only [instances, List.mem_map, exists_exists_and_eq_and]
end ChanHe
end ThreeSumApsp
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
def bitOf (V β : ℕ) (x : ℤ) : ℤ := if (lab V x).testBit β then 1 else 0
def bitRow (Λ z : ℕ) : List ℤ := (List.range Λ).map fun β => if z.testBit β then 1 else 0
@[simp] theorem length_bitRow (Λ z : ℕ) : (bitRow Λ z).length = Λ := by simp [bitRow]
theorem bitTable_cons (V Λ : ℕ) (x : ℤ) (L : List ℤ) :
    bitTable V Λ (x :: L) = bitRow Λ (lab V x) ++ bitTable V Λ L := by
  simp [bitTable, bitRow]
theorem length_bitTable (V Λ : ℕ) (L : List ℤ) : (bitTable V Λ L).length = L.length * Λ := by
  induction L with
  | nil => simp [bitTable]
  | cons x L ih =>
    rw [bitTable_cons, List.length_append, ih, length_bitRow, List.length_cons, Nat.succ_mul,
      Nat.add_comm]
theorem getD_bitTable (V Λ : ℕ) (L : List ℤ) {i β : ℕ} (hi : i < L.length) (hβ : β < Λ) :
    (bitTable V Λ L).getD (i * Λ + β) 0 = bitOf V β (L.getD i 0) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    rw [bitTable_cons]
    cases i with
    | zero =>
      rw [List.getD_append _ _ _ _ (by simpa using hβ)]
      simp [bitRow, List.getD_eq_getElem?_getD, hβ, bitOf]
    | succ i =>
      rw [List.getD_append_right _ _ _ _ (by rw [length_bitRow, Nat.succ_mul]; omega),
        length_bitRow, show (i + 1) * Λ + β - Λ = i * Λ + β by rw [Nat.succ_mul]; omega,
        ih (by simpa using hi), List.getD_cons_succ]
theorem filter_by_position (L : List ℤ) (q : ℤ → Bool) :
    ((List.range L.length).filter fun i => q (L.getD i 0)).map (fun i => L.getD i 0) =
      L.filter q := by
  have hL : L = (List.range L.length).map fun i => L.getD i 0 := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  conv_rhs => rw [hL, List.filter_map]
  rfl
theorem pickList_eq (V Λ : ℕ) {β β' : ℕ} (hβ : β < Λ) (hβ' : β' < Λ) (b b' two : ℤ) (L : List ℤ) :
    pickList Λ β β' b b' two L (bitTable V Λ L) =
      L.filter fun x => decide (bitOf V β x = b ∧ (two = 0 ∨ bitOf V β' x = b')) := by
  rw [← filter_by_position L]
  unfold pickList
  congr 1
  refine List.filter_congr fun i hi => ?_
  have hi' : i < L.length := List.mem_range.1 hi
  rw [getD_bitTable V Λ L hi' hβ, getD_bitTable V Λ L hi' hβ']
theorem bitOf_eq_iff (V β : ℕ) (x : ℤ) (v : Bool) :
    bitOf V β x = (if v then 1 else 0) ↔ (lab V x).testBit β = v := by
  unfold bitOf
  cases v <;> cases (lab V x).testBit β <;> simp
theorem pick_splitA (V Λ : ℕ) {β β' : ℕ} (hβ : β < Λ) (hβ' : β' < Λ) (v : Bool) (b' : ℤ)
    {L : List ℤ} (hL : L.Nodup) :
    (pickList Λ β β' (if v then 1 else 0) b' 0 L (bitTable V Λ L)).Nodup ∧
      (pickList Λ β β' (if v then 1 else 0) b' 0 L (bitTable V Λ L)).toFinset =
        splitA V β v L.toFinset := by
  rw [pickList_eq V Λ hβ hβ']
  refine ⟨hL.filter _, ?_⟩
  ext x
  simp [splitA, bitOf_eq_iff]
theorem pick_splitB (V Λ : ℕ) {β β' : ℕ} (hβ : β < Λ) (hβ' : β' < Λ) (v w : Bool) {L : List ℤ}
    (hL : L.Nodup) :
    (pickList Λ β β' (if !v then 1 else 0) (if w then 1 else 0) 1 L (bitTable V Λ L)).Nodup ∧
      (pickList Λ β β' (if !v then 1 else 0) (if w then 1 else 0) 1 L (bitTable V Λ L)).toFinset =
        splitB V β β' v w L.toFinset := by
  rw [pickList_eq V Λ hβ hβ']
  refine ⟨hL.filter _, ?_⟩
  ext x
  simp only [List.toFinset_filter, Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq,
    bitOf_eq_iff, splitB]
  simp
theorem length_pickList_le (Λ β β' : ℕ) (b b' two : ℤ) (L BT : List ℤ) :
    (pickList Λ β β' b b' two L BT).length ≤ L.length := by
  unfold pickList
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)
theorem Values.length_le {n : ℕ} {X D C : List ℤ} (h : Values n X D C) : D.length ≤ n := by
  rw [← List.toFinset_card_of_nodup h.nodup, h.values]
  exact card_image_univ_le _
theorem Values.zip {n : ℕ} {X D C : List ℤ} (h : Values n X D C) :
    D.zip C = D.map fun a => (a, ((#{i : Fin n | vecOf n X i = a} : ℕ) : ℤ)) := by
  rw [h.counts]
  exact List.map_prod_left_eq_zip.symm
theorem Values.twice {n : ℕ} {X D C : List ℤ} (h : Values n X D C) :
    (twiceList D C).Nodup ∧ (twiceList D C).toFinset = twiceSet (vecOf n X) := by
  have hfilter : twiceList D C =
      (D.filter fun a => decide (a ≠ 0 ∧ 2 ≤ #{i : Fin n | vecOf n X i = a})).map
        fun a => 2 * a := by
    unfold twiceList
    rw [h.zip, List.filter_map, List.map_map]
    congr 1
    refine List.filter_congr fun a _ => ?_
    simp only [Function.comp, decide_eq_decide]
    exact and_congr_right fun _ => by norm_cast
  rw [hfilter]
  refine ⟨(h.nodup.filter _).map fun a b hab => by simpa using hab, ?_⟩
  have hmem : ∀ a : ℤ, a ∈ D ↔ a ∈ univ.image (vecOf n X) := fun a => by
    rw [← h.values, List.mem_toFinset]
  ext y
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq, twiceSet,
    Finset.mem_image, Finset.mem_filter, hmem]
theorem length_twiceList_le (D C : List ℤ) : (twiceList D C).length ≤ D.length := by
  unfold twiceList
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [List.length_zip])
theorem Values.zeroThree {n : ℕ} {X D C : List ℤ} (h : Values n X D C) :
    (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) ↔ 3 ≤ #{i : Fin n | vecOf n X i = 0} := by
  rw [h.zip]
  constructor
  · rintro ⟨q, hq, h0, h3⟩
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hq
    simp only at h0 h3
    subst h0
    exact_mod_cast h3
  · intro h3
    have hne : (#{i : Fin n | vecOf n X i = 0}) ≠ 0 := by omega
    obtain ⟨i, hi⟩ := Finset.card_ne_zero.1 hne
    have hi' : vecOf n X i = 0 := (Finset.mem_filter.1 hi).2
    have h0 : (0 : ℤ) ∈ D := by
      rw [← List.mem_toFinset, h.values]
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi'⟩
    exact ⟨_, List.mem_map.2 ⟨0, h0, rfl⟩, rfl, Int.ofNat_le.2 h3⟩
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.ChanHe Finset
@[simp] abbrev FrontArgs.vals (a : FrontArgs) (f : ℕ) : List ℤ :=
  [a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr]
def SplitYes (m Λ f V : ℕ) (S : Finset ℤ) (β β' : ℕ) (v : Bool) : Prop :=
  TreeYes m Λ f V (splitA V β v S) (splitB V β β' v false S) (splitB V β β' v true S)
abbrev FrontArgs.Yes (a : FrontArgs) (f β β' : ℕ) (v : Bool) : Prop :=
  SplitYes a.m a.Λ f a.V a.D.toFinset β β' v
def tTree (T : ℕ → ℕ → ℕ) (n V m np f : ℕ) : ℕ := tNodes T n V m np (2 * 3 ^ f)
def tRound (T : ℕ → ℕ → ℕ) (n V m np f : ℕ) : ℕ := 3 * tPick n + tTree T n V m np f + 120
def tRow (T : ℕ → ℕ → ℕ) (n V m np f Λ : ℕ) : ℕ := Λ * (2 * tRound T n V m np f + 80) + 40
def tGrid (T : ℕ → ℕ → ℕ) (n V m np f Λ : ℕ) : ℕ := Λ * (tRow T n V m np f Λ + 40) + 40
def RoundSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f β β' : ℕ) (v : Bool) (μ : ℕ → ℤ), FrontMem μ a → β < a.Λ → β' < a.Λ →
    ∀ d, GridPre lim r a f 0 d →
    Meets lim P p d ((β : ℤ) :: β' :: (if v then 1 else 0) :: a.vals f) μ
      (tRound T a.n a.V a.m a.np f) fun res μ' =>
      res = flag (a.Yes f β β' v) ∧ KeptBut μ μ' a.fr a.A (3 * a.n)
def RowSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f β : ℕ) (μ : ℕ → ℤ), FrontMem μ a → β < a.Λ →
    ∀ d, GridPre lim r a f 1 d →
    Meets lim P p d ((β : ℤ) :: a.vals f) μ (tRow T a.n a.V a.m a.np f a.Λ) fun res μ' =>
      0 ≤ res ∧ res ≤ 2 * (a.Λ : ℤ) ∧ (0 < res ↔ ∃ β' < a.Λ, ∃ v, a.Yes f β β' v) ∧
        KeptBut μ μ' a.fr a.A (3 * a.n)
def GridSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (a : FrontArgs) (f : ℕ) (μ : ℕ → ℤ), FrontMem μ a → ∀ d, GridPre lim r a f 2 d →
    Meets lim P p d (a.vals f) μ (tGrid T a.n a.V a.m a.np f a.Λ) fun res μ' =>
      res = flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, a.Yes f β β' v) ∧
        KeptBut μ μ' a.fr a.A (3 * a.n)
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
section memory
variable {μ μ' : ℕ → ℤ} {fr V m np pr cnt s len : ℕ} {S : Finset ℤ} {e : Env} {X : Slot}
  {a : NodeArgs}
theorem SetAt.kept (h : SetAt μ s len S) (hb : s + len ≤ fr) (hk : Kept μ μ' fr) :
    SetAt μ' s len S := by
  obtain ⟨L, hL, hs, hn, ht⟩ := h
  exact ⟨L, hL, hs.congr fun i hi => hk _ (by omega), hn, ht⟩
theorem SetAt.card (h : SetAt μ s len S) : #S = len := by
  obtain ⟨L, hL, -, hn, ht⟩ := h
  rw [← ht, List.toFinset_card_of_nodup hn, hL]
theorem SetAt.eq_empty (h : SetAt μ s len S) (h0 : len = 0) : S = ∅ :=
  Finset.card_eq_zero.1 (h.card.trans h0)
theorem card_heavy_le (h : SetAt μ s len S) (M : ℕ) : #(ChanHe.heavy S M) ≤ len :=
  h.card ▸ Finset.card_le_card (heavy_subset S M)
theorem Env.Ok.kept (h : e.Ok μ) (hk : Kept μ μ' e.fr) : e.Ok μ' :=
  { h with
    primes := ⟨h.primes.1, h.primes.2.congr fun i hi => hk _ (by
      have hbelow := h.belowPr
      have hnp := h.primes.1
      simp only [List.length_map, Finset.length_sort] at hi
      omega)⟩
    zero := fun r hr => (hk _ (by have := h.belowCnt; omega)).trans (h.zero r hr) }
theorem Slot.Ok.kept (h : X.Ok μ e) (hk : Kept μ μ' e.fr) : X.Ok μ' e :=
  { h with set := h.set.kept h.below hk }
theorem NodeMem.kept (h : NodeMem μ a) (hk : Kept μ μ' a.fr) : NodeMem μ' a :=
  ⟨h.envOk.kept hk, h.set₁.kept hk, h.set₂.kept hk, h.set₃.kept hk⟩
theorem Slot.Ok.bucket (h : X.Ok μ e) (he : e.Ok μ) {M : ℕ} (hM : 1 ≤ M) (hMm : M ≤ e.m * e.m) :
    BucketMem μ e.fr e.V M X.addr X.len e.cnt (e.m * e.m) X.set :=
  ⟨hM, hMm, h.bdd, h.set, he.zero, h.below, he.belowCnt, h.apart⟩
@[simp] def Env.push (e : Env) (len : ℕ) : Env := { e with fr := e.fr + len }
@[simp] def Slot.heavy (X : Slot) (fr M : ℕ) : Slot :=
  ⟨fr, #(ChanHe.heavy X.set M), ChanHe.heavy X.set M⟩
@[simp] def NodeArgs.push (a : NodeArgs) (len : ℕ) : NodeArgs :=
  { a with toEnv := a.toEnv.push len }
@[simp] def NodeArgs.child₁ (a : NodeArgs) (M : ℕ) : NodeArgs :=
  { a with toEnv := a.toEnv.push a.X₁.len, X₁ := a.X₁.heavy a.fr M }
@[inherit_doc NodeArgs.child₁, simp] def NodeArgs.child₂ (a : NodeArgs) (M : ℕ) : NodeArgs :=
  { a with toEnv := a.toEnv.push a.X₂.len, X₂ := a.X₂.heavy a.fr M }
@[inherit_doc NodeArgs.child₁, simp] def NodeArgs.child₃ (a : NodeArgs) (M : ℕ) : NodeArgs :=
  { a with toEnv := a.toEnv.push a.X₃.len, X₃ := a.X₃.heavy a.fr M }
theorem Env.Ok.push (h : e.Ok μ) (hk : KeptBut μ μ' (e.fr + len) e.fr len) : (e.push len).Ok μ' :=
  { h.kept (hk.mono fun b hb => by omega) with
    belowPr := h.belowPr.trans (Nat.le_add_right _ _)
    belowCnt := h.belowCnt.trans (Nat.le_add_right _ _) }
theorem Slot.Ok.push (h : X.Ok μ e) (hk : KeptBut μ μ' (e.fr + len) e.fr len) :
    X.Ok μ' (e.push len) :=
  { h.kept (hk.mono fun b hb => by omega) with below := h.below.trans (Nat.le_add_right _ _) }
theorem NodeMem.push (h : NodeMem μ a) (hk : KeptBut μ μ' (a.fr + len) a.fr len) :
    NodeMem μ' (a.push len) :=
  ⟨h.envOk.push hk, h.set₁.push hk, h.set₂.push hk, h.set₃.push hk⟩
theorem Slot.Ok.heavy (h : X.Ok μ e) (he : e.Ok μ) {M : ℕ}
    (hs : SetAt μ' e.fr #(ChanHe.heavy X.set M) (ChanHe.heavy X.set M)) :
    (X.heavy e.fr M).Ok μ' (e.push X.len) where
  set := hs
  le := (card_heavy_le h.set M).trans h.le
  bdd := h.bdd.mono (heavy_subset _ _)
  below := Nat.add_le_add_left (card_heavy_le h.set M) _
  apart := Or.inr he.belowCnt
theorem NodeMem.child₁ (h : NodeMem μ a) {M : ℕ} (hk : KeptBut μ μ' (a.fr + a.X₁.len) a.fr a.X₁.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₁.set M) (ChanHe.heavy a.X₁.set M)) :
    NodeMem μ' (a.child₁ M) :=
  ⟨h.envOk.push hk, h.set₁.heavy h.envOk hs, h.set₂.push hk, h.set₃.push hk⟩
theorem NodeMem.child₂ (h : NodeMem μ a) {M : ℕ} (hk : KeptBut μ μ' (a.fr + a.X₂.len) a.fr a.X₂.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₂.set M) (ChanHe.heavy a.X₂.set M)) :
    NodeMem μ' (a.child₂ M) :=
  ⟨h.envOk.push hk, h.set₁.push hk, h.set₂.heavy h.envOk hs, h.set₃.push hk⟩
theorem NodeMem.child₃ (h : NodeMem μ a) {M : ℕ} (hk : KeptBut μ μ' (a.fr + a.X₃.len) a.fr a.X₃.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₃.set M) (ChanHe.heavy a.X₃.set M)) :
    NodeMem μ' (a.child₃ M) :=
  ⟨h.envOk.push hk, h.set₁.push hk, h.set₂.push hk, h.set₃.heavy h.envOk hs⟩
theorem CtxAt.kept {cx Λ : ℕ} (h : CtxAt μ cx V m Λ np pr cnt) (hb : cx + 6 ≤ fr)
    (hk : Kept μ μ' fr) : CtxAt μ' cx V m Λ np pr cnt :=
  Seg.congr h fun i hi => hk _ (by simp only [List.length_cons, List.length_nil] at hi; omega)
end memory
theorem mul_le_wordNeed {x y z n V M : ℕ} (hx : x ≤ (n + 1) ^ 2) (hy : y ≤ M + 1)
    (hz : z ≤ 64 * (V + 1)) : x * y * z ≤ wordNeed n V M :=
  calc x * y * z ≤ (n + 1) ^ 2 * (M + 1) * (64 * (V + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
    _ = wordNeed n V M := by unfold wordNeed; ring
theorem mul_le_word {lim : Limits} {x y z n V M : ℕ} (h : ((wordNeed n V M : ℕ) : ℤ) ≤ lim.word)
    (hx : x ≤ (n + 1) ^ 2) (hy : y ≤ M + 1) (hz : z ≤ 64 * (V + 1)) :
    (x : ℤ) * y * z ≤ lim.word :=
  le_trans (by exact_mod_cast mul_le_wordNeed hx hy hz) h
theorem wordNeed_mono {n n' V M M' : ℕ} (hn : n ≤ n') (hM : M ≤ M') :
    wordNeed n V M ≤ wordNeed n' V M' := by
  unfold wordNeed
  gcongr
end Light.Sec3.ChanHe
end
end
section
public section
open Filter Asymptotics
namespace ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace IsBigOPow
end IsBigOPow
namespace IsPowPolylog
theorem of_abs_le (C : ℝ) (e n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → |f n| ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) : IsPowPolylog f a :=
  ⟨e, isBigO_of_abs_le C n₀ h⟩
end IsPowPolylog
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
namespace Scale
variable {α ι : Type*} [Fintype ι] (s : Scale α ι)
variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}
namespace SoftO
variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}
theorem log2 (hs : ∀ i x, s.dom x → s.base i x ≤ 2 ^ s.hidden x) (h : s.SoftO t e) :
    s.SoftO (fun x => Nat.log 2 (t x)) 0 := by
  obtain ⟨C, c, hC, hle⟩ := h.exists_le
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt C (one_lt_two (α := ℝ))
  refine ⟨1, K + c + ∑ i, e i, by positivity, fun x hx => ?_⟩
  have hf : 1 ≤ s.hidden x := s.one_le_hidden x hx
  have hhidden : s.hidden x ≤ 2 ^ s.hidden x := by
    have := one_add_mul_self_le_rpow_one_add (s := 1) (by norm_num) hf
    norm_num at this
    linarith
  have hbase := fun i => zero_le_one.trans (s.one_le_base i x hx)
  have hpow : (t x : ℝ) ≤ 2 ^ ((K + c + ∑ i, e i : ℕ) * s.hidden x) :=
    calc (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) := hle x hx
      _ ≤ 2 ^ K * ((2 ^ s.hidden x) ^ c * ∏ i, (2 ^ s.hidden x) ^ e i) := by
          have hmon := zero_le_one.trans (one_le_mon e hx)
          gcongr
          exact Finset.prod_le_prod (fun i _ => pow_nonneg (hbase i) _)
            fun i _ => pow_le_pow_left₀ (hbase i) (hs i x hx) _
      _ ≤ (2 ^ s.hidden x) ^ K * ((2 ^ s.hidden x) ^ c * ∏ i, (2 ^ s.hidden x) ^ e i) := by
          gcongr
          exact (Real.rpow_one 2).ge.trans (Real.rpow_le_rpow_of_exponent_le one_le_two hf)
      _ = 2 ^ ((K + c + ∑ i, e i : ℕ) * s.hidden x) := by
          rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← pow_add, ← add_assoc, ← Real.rpow_natCast,
            ← Real.rpow_mul zero_le_two, mul_comm]
  simp only [pow_one, mon_zero, mul_one]
  rcases Nat.eq_zero_or_pos (t x) with h0 | hpos
  · rw [h0, Nat.log_zero_right, Nat.cast_zero]
    positivity
  · have hlog : (2 : ℝ) ^ (Nat.log 2 (t x) : ℝ) ≤ t x := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
    exact_mod_cast (Real.rpow_le_rpow_left_iff one_lt_two).1 (hlog.trans hpow)
end SoftO
end Scale
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
theorem natLog_succ_le {n : ℕ} (hn : 2 ≤ n) : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 4 * Real.log n := by
  have hhalf : 1 / 2 ≤ Real.log 2 := Real.one_half_lt_log_two.le
  have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hfloor : Nat.log 2 n * Real.log 2 ≤ Real.log n :=
    calc Nat.log 2 n * Real.log 2 = Real.log ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow, Nat.cast_two]
      _ ≤ Real.log n := Real.log_le_log (by positivity)
          (by exact_mod_cast Nat.pow_log_le_self 2 (by omega))
  have hmul := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))
  push_cast
  linarith [hmul, hfloor, hhalf, hlog2]
theorem natSqrt_succ_le {n : ℕ} (hn : 1 ≤ n) : ((Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 2 * √(n : ℝ) := by
  have hone : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  push_cast
  linarith [Real.nat_sqrt_le_real_sqrt (a := n), hone]
noncomputable def sqrtScale : Scale ℕ (Fin 1) where
  dom n := 2 ≤ n
  hidden n := (Nat.log 2 n + 1 : ℕ)
  base _ n := (Nat.sqrt n + 1 : ℕ)
  one_le_hidden _ _ := Nat.one_le_cast.2 (Nat.le_add_left 1 _)
  one_le_base _ _ _ := Nat.one_le_cast.2 (Nat.le_add_left 1 _)
abbrev SoftOSqrtPow (F : ℕ → ℕ) (i : ℕ) : Prop := sqrtScale.SoftO F ![i]
namespace SoftOSqrtPow
variable {F : ℕ → ℕ} {i : ℕ}
theorem natLog : SoftOSqrtPow (fun n => Nat.log 2 n) 0 :=
  (Scale.SoftO.of_le_hidden fun _ _ => Nat.cast_le.2 (Nat.le_succ _)).mono (by decide)
theorem natSqrt : SoftOSqrtPow (fun n => Nat.sqrt n) 1 :=
  (Scale.SoftO.of_le_base 0 fun _ _ => Nat.cast_le.2 (Nat.le_succ _)).mono (by decide)
theorem self : SoftOSqrtPow (fun n => n) 2 :=
  (by ((first
         | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
             ·
               (repeat'
                   with_reducible
                     first
                     | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                     | apply natSqrt
                     | apply _root_.ThreeSumApsp.Scale.SoftO.add
                     | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                     | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                     | apply _root_.ThreeSumApsp.Scale.SoftO.max
                     | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                     | apply _root_.ThreeSumApsp.Scale.SoftO.div)
             ·
               first
               | decide
               | exact _root_.isEmptyElim)
         | ( fail_if_success
               (fail_if_success
                   ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                     on_goal 1 =>
                       ((repeat'
                             with_reducible
                               first
                               | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                               | apply natSqrt
                               | apply _root_.ThreeSumApsp.Scale.SoftO.add
                               | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                               | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                               | apply _root_.ThreeSumApsp.Scale.SoftO.max
                               | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                               | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                         done)))
             repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
             all_goals
               try (
                   apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   ·
                     (repeat'
                         with_reducible
                           first
                           | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                           | apply natSqrt
                           | apply _root_.ThreeSumApsp.Scale.SoftO.add
                           | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                           | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                           | apply _root_.ThreeSumApsp.Scale.SoftO.max
                           | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                           | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                   · decide))
         | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
             ·
               (repeat'
                   with_reducible
                     first
                     | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                     | apply natSqrt
                     | apply _root_.ThreeSumApsp.Scale.SoftO.add
                     | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                     | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                     | apply _root_.ThreeSumApsp.Scale.SoftO.max
                     | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                     | apply _root_.ThreeSumApsp.Scale.SoftO.div)))
                     ) : SoftOSqrtPow (fun n => (Nat.sqrt n + 1) ^ 2) 2).of_le fun n _ =>
    (Nat.lt_succ_sqrt n).le.trans (sq _).ge
theorem natLog_comp {e : Fin 1 → ℕ} (hF : sqrtScale.SoftO F e) :
    SoftOSqrtPow (fun n => Nat.log 2 (F n)) 0 := by
  refine (Scale.SoftO.log2 (fun _ n _ => ?_) hF).mono (by decide)
  have hsqrt : Nat.sqrt n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have := Nat.sqrt_le_self n
    omega
  simp only [sqrtScale, Real.rpow_natCast]
  exact_mod_cast hsqrt
theorem isPowPolylog (hF : SoftOSqrtPow F i) {a : ℝ} (ha : a = i / 2) :
    IsPowPolylog (fun n => (F n : ℝ)) a := by
  obtain ⟨K, e, hK0, hK⟩ := hF.exists_le
  refine .of_abs_le (K * 4 ^ e * 2 ^ i) e 2 fun n hn => ?_
  have hsqrt : √(n : ℝ) ^ i = (n : ℝ) ^ a := by
    rw [ha, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  calc (F n : ℝ)
      ≤ K * (((Nat.log 2 n + 1 : ℕ) : ℝ) ^ e * ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ i) := by
        simpa [sqrtScale, Scale.mon] using hK n hn
    _ ≤ K * ((4 * Real.log n) ^ e * (2 * √(n : ℝ)) ^ i) := by
        gcongr
        exacts [natLog_succ_le hn, natSqrt_succ_le (by omega)]
    _ = K * 4 ^ e * 2 ^ i * ((n : ℝ) ^ a * Real.log n ^ e) := by
        rw [mul_pow, mul_pow, hsqrt]
        ring
end SoftOSqrtPow
end ThreeSumApsp
end
end
section
public section
namespace ThreeSumApsp
namespace ChanHe
open Finset
theorem softO_Lam (κ : ℕ) : SoftOSqrtPow (fun n => Lam (2 * n ^ κ)) 0 := by
  unfold Lam
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
               )
theorem softO_wPar (κ : ℕ) : SoftOSqrtPow (fun n => wPar n (2 * n ^ κ) + 1) 1 := by
  unfold wPar
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_Lam κ
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_Lam κ
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_Lam κ
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_Lam κ
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                          )
theorem softO_mPar (κ : ℕ) : SoftOSqrtPow (fun n => mPar n (2 * n ^ κ)) 1 := by
  unfold mPar
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_wPar κ
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_wPar κ
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_wPar κ
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_wPar κ
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                           )
theorem one_le_lenOf (κ n : ℕ) : 1 ≤ lenOf κ n :=
  Nat.succ_le_of_lt (by unfold lenOf mPar; positivity)
section input
variable {κ n : ℕ} {x : Fin n → ℤ}
theorem convolution3SUM_iff_convOne (N : ℕ) (y : ℕ → ℤ) :
    Convolution3SUM (fun i : Fin N => y i) ↔ ConvOne N y :=
  ⟨fun ⟨i, j, h, e⟩ => ⟨i, j, h, e⟩, fun ⟨u, v, h, e⟩ => ⟨⟨u, by omega⟩, ⟨v, by omega⟩, h, e⟩⟩
end input
theorem isPowPolylog_lenOf (κ : ℕ) : IsPowPolylog (fun n => (lenOf κ n : ℝ)) 1 :=
  SoftOSqrtPow.isPowPolylog (i := 2) (by unfold lenOf; (((first
                                                            | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                                                                ·
                                                                  (repeat'
                                                                      with_reducible
                                                                        first
                                                                        | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                                                                        | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                                                                        | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                                                                        | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                                                                        | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                                                                        | apply softO_mPar κ
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.add
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.max
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                                                                ·
                                                                  first
                                                                  | decide
                                                                  | exact _root_.isEmptyElim)
                                                            | ( fail_if_success
                                                                  (fail_if_success
                                                                      ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                                                                        on_goal 1 =>
                                                                          ((repeat'
                                                                                with_reducible
                                                                                  first
                                                                                  | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                                                                                  | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                                                                                  | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                                                                                  | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                                                                                  | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                                                                                  | apply softO_mPar κ
                                                                                  | apply _root_.ThreeSumApsp.Scale.SoftO.add
                                                                                  | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                                                                                  | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                                                                                  | apply _root_.ThreeSumApsp.Scale.SoftO.max
                                                                                  | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                                                                                  | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                                                                            done)))
                                                                repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
                                                                all_goals
                                                                  try (
                                                                      apply _root_.ThreeSumApsp.Scale.SoftO.mono
                                                                      ·
                                                                        (repeat'
                                                                            with_reducible
                                                                              first
                                                                              | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                                                                              | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                                                                              | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                                                                              | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                                                                              | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                                                                              | apply softO_mPar κ
                                                                              | apply _root_.ThreeSumApsp.Scale.SoftO.add
                                                                              | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                                                                              | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                                                                              | apply _root_.ThreeSumApsp.Scale.SoftO.max
                                                                              | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                                                                              | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                                                                      · decide))
                                                            | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                                                                ·
                                                                  (repeat'
                                                                      with_reducible
                                                                        first
                                                                        | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                                                                        | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                                                                        | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                                                                        | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                                                                        | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                                                                        | apply softO_mPar κ
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.add
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.max
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                                                                        | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                                                                )) (by norm_num)
end ChanHe
end ThreeSumApsp
end
end
section
@[expose] public section
namespace ThreeSumApsp
theorem flag_mem (p : Prop) : 0 ≤ flag p ∧ flag p < 2 := by
  by_cases h : p
  · simp [flag_of h]
  · simp [flag_of_not h]
end ThreeSumApsp
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
variable {lim : Limits} {P : Program} {d : ℕ}
theorem conv_range_iff (N : ℕ) (y : ℕ → ℤ) :
    Convolution3SUM (vecOf N ((List.range N).map y)) ↔ ConvOne N y := by
  have : vecOf N ((List.range N).map y) = fun i : Fin N => y i := by
    funext i
    unfold vecOf
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  rw [this]
  exact convolution3SUM_iff_convOne N y
theorem flag_sum_pos (a b c e : Prop) : 0 < flag a + flag b + flag c + flag e ↔ a ∨ b ∨ c ∨ e := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases he : e <;>
    simp [flag_of, flag_of_not, ha, hb, hc, he]
theorem lam_le (V : ℕ) : Lam V ≤ V + 2 := by
  unfold Lam
  rcases Nat.eq_zero_or_pos V with rfl | h
  · simp
  · have : Nat.log 2 (2 * V) = Nat.log 2 V + 1 := by
      rw [Nat.mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
    have h2 : Nat.log 2 V < V := Nat.log_lt_self 2 (by omega)
    omega
namespace NodesLocals
abbrev LEVELS : ℕ := 0
@[inherit_doc LEVELS] abbrev SET1 : ℕ := 1
@[inherit_doc LEVELS] abbrev LEN1 : ℕ := 2
@[inherit_doc LEVELS] abbrev SET2 : ℕ := 3
@[inherit_doc LEVELS] abbrev LEN2 : ℕ := 4
@[inherit_doc LEVELS] abbrev SET3 : ℕ := 5
@[inherit_doc LEVELS] abbrev LEN3 : ℕ := 6
@[inherit_doc LEVELS] abbrev CTX : ℕ := 7
@[inherit_doc LEVELS] abbrev FREE : ℕ := 8
@[inherit_doc LEVELS] abbrev VMAX : ℕ := 9
@[inherit_doc LEVELS] abbrev MMAX : ℕ := 10
@[inherit_doc LEVELS] abbrev LAM : ℕ := 11
@[inherit_doc LEVELS] abbrev NPRIMES : ℕ := 12
@[inherit_doc LEVELS] abbrev PRIMES : ℕ := 13
@[inherit_doc LEVELS] abbrev CNT : ℕ := 14
@[inherit_doc LEVELS] abbrev MOD : ℕ := 15
@[inherit_doc LEVELS] abbrev LEN : ℕ := 16
@[inherit_doc LEVELS] abbrev FR2 : ℕ := 17
@[inherit_doc LEVELS] abbrev RES : ℕ := 18
@[inherit_doc LEVELS] abbrev ANS0 : ℕ := 19
@[inherit_doc LEVELS] abbrev HEAVY1 : ℕ := 20
@[inherit_doc LEVELS] abbrev ANS1 : ℕ := 21
@[inherit_doc LEVELS] abbrev HEAVY2 : ℕ := 22
@[inherit_doc LEVELS] abbrev ANS2 : ℕ := 23
@[inherit_doc LEVELS] abbrev HEAVY3 : ℕ := 24
@[inherit_doc LEVELS] abbrev ANS3 : ℕ := 25
end NodesLocals
open NodesLocals in
def nodesParams : Stmt :=
  .set VMAX (M (v CTX)) ;;
  .set MMAX (M (v CTX +' k 1)) ;;
  .set LAM (M (v CTX +' k 2)) ;;
  .set NPRIMES (M (v CTX +' k 3)) ;;
  .set PRIMES (M (v CTX +' k 4)) ;;
  .set CNT (M (v CTX +' k 5))
open NodesLocals in
def nodesOwn (pMod pArr pC3 : ℕ) : Stmt :=
  .call pMod
      [v SET1, v LEN1, v SET2, v LEN2, v SET3, v LEN3, v LAM, v NPRIMES, v PRIMES, v CNT, v FREE]
      MOD ;;
  .set LEN (k 8 *' (v MMAX *' v MMAX)) ;;
  .set FR2 (v FREE +' v LEN) ;;
  .call pArr
      [v MOD, v SET1, v LEN1, v SET2, v LEN2, v SET3, v LEN3, v VMAX, v MMAX, v FREE, v CNT, v FR2]
      RES ;;
  .call pC3 [v LEN, k 60 *' v VMAX +' k 40, v FREE, v FR2] ANS0
open NodesLocals in
def nodesChild₁ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN1, v SET1, v MOD, v FREE, v CNT, v FREE +' v LEN1] HEAVY1 ;;
  .call pSelf
      [v LEVELS -' k 1, v FREE, v HEAVY1, v SET2, v LEN2, v SET3, v LEN3, v CTX, v FREE +' v LEN1]
      ANS1
open NodesLocals in
def nodesChild₂ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN2, v SET2, v MOD, v FREE, v CNT, v FREE +' v LEN2] HEAVY2 ;;
  .call pSelf
      [v LEVELS -' k 1, v SET1, v LEN1, v FREE, v HEAVY2, v SET3, v LEN3, v CTX, v FREE +' v LEN2]
      ANS2
open NodesLocals in
def nodesChild₃ (pSelf pHeavy : ℕ) : Stmt :=
  .call pHeavy [v LEN3, v SET3, v MOD, v FREE, v CNT, v FREE +' v LEN3] HEAVY3 ;;
  .call pSelf
      [v LEVELS -' k 1, v SET1, v LEN1, v SET2, v LEN2, v FREE, v HEAVY3, v CTX, v FREE +' v LEN3]
      ANS3
open NodesLocals in
def nodesAnswer : Stmt :=
  .ite (k 0 <' v ANS0 +' v ANS1 +' v ANS2 +' v ANS3) (.set 0 (k 1)) (.set 0 (k 0))
def nodesMain (pSelf pMod pArr pC3 pHeavy : ℕ) : Stmt :=
  nodesParams ;; nodesOwn pMod pArr pC3 ;; nodesChild₁ pSelf pHeavy ;; nodesChild₂ pSelf pHeavy ;;
  nodesChild₃ pSelf pHeavy ;; nodesAnswer
open NodesLocals in
def nodesBody (pSelf pMod pArr pC3 pHeavy : ℕ) : Stmt :=
  .ite (v LEVELS =' k 0) (.set 0 (k 0)) (
  .ite (v LEN1 =' k 0) (.set 0 (k 0)) (
  .ite (v LEN2 =' k 0) (.set 0 (k 0)) (
  .ite (v LEN3 =' k 0) (.set 0 (k 0)) (nodesMain pSelf pMod pArr pC3 pHeavy))))
structure NodesCtx (lim : Limits) (P₀ R : Program) (p pMod pArr pC3 pHeavy : ℕ) (T : ℕ → ℕ → ℕ)
    (r : ℕ → ℕ → Need) : Prop where
  solver : Solves c3Task P₀ pC3 T r
  self : (P₀ ++ R)[p]? = some (nodesBody p pMod pArr pC3 pHeavy)
  modulus : ModulusSpec lim (P₀ ++ R) pMod
  array : NodeArraySpec lim (P₀ ++ R) pArr
  heavy : HeavySpec lim (P₀ ++ R) pHeavy
theorem treeCalls_le (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    treeCalls Q Λ f S₁ S₂ S₃ ≤ 3 * (nodes Q Λ f S₁ S₂ S₃).length + 1 := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => simp [treeCalls]
  | succ f ih =>
    unfold treeCalls nodes
    split_ifs with h
    · simp
    · simp only [List.length_cons, List.length_append]
      have a := ih (ChanHe.heavy S₁ (ChanHe.modulus Q Λ S₁ S₂ S₃)) S₂ S₃
      have b := ih S₁ (ChanHe.heavy S₂ (ChanHe.modulus Q Λ S₁ S₂ S₃)) S₃
      have c := ih S₁ S₂ (ChanHe.heavy S₃ (ChanHe.modulus Q Λ S₁ S₂ S₃))
      omega
theorem one_le_treeCalls (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    1 ≤ treeCalls Q Λ f S₁ S₂ S₃ := by
  cases f with
  | zero => simp [treeCalls]
  | succ f =>
    unfold treeCalls
    split_ifs <;> omega
section needs
variable {r : ℕ → ℕ → Need} {fr n V m f l M : ℕ}
theorem modulusNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (modulusNeed n V m).Ok lim fr (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega
theorem nodeArrayNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (nodeArrayNeed n V m).Ok lim (fr + 8 * m ^ 2) (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed, nodeArrayNeed, modulusNeed] <;> omega
theorem solverNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) :
    (r (8 * m ^ 2) (60 * V + 40)).Ok lim (fr + 8 * m ^ 2) (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega
theorem collNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) (hl : l ≤ n) (hM : M ≤ m * m) :
    (collNeed l V M).Ok lim (fr + l) (d + 1) := by
  have hsucc : (f + 1) * n = f * n + n := by ring
  have hword := wordNeed_mono (V := V) hl hM
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed, collNeed, modulusNeed] <;> omega
theorem childNeed_ok (h : (nodesNeed r n V m (f + 1)).Ok lim fr d) (hl : l ≤ n) :
    (nodesNeed r n V m f).Ok lim (fr + l) (d + 1) := by
  have hsucc : (f + 1) * n = f * n + n := by ring
  refine h.mono ?_ ?_ ?_ <;> simp only [nodesNeed] <;> omega
theorem tResid_mono {l n : ℕ} (h : l ≤ n) (V : ℕ) : tResid l V ≤ tResid n V := by
  unfold tResid
  gcongr
theorem tTally_mono {l n : ℕ} (h : l ≤ n) : tTally l ≤ tTally n := by
  unfold tTally
  omega
theorem tColl_mono {l n : ℕ} (h : l ≤ n) (V : ℕ) : tColl l V ≤ tColl n V := by
  have hresid := tResid_mono h V
  have htally := tTally_mono h
  unfold tColl
  omega
theorem tHeavy_mono {l n : ℕ} (h : l ≤ n) (V : ℕ) : tHeavy l V ≤ tHeavy n V := by
  have hresid := tResid_mono h V
  have htally := tTally_mono h
  unfold tHeavy
  omega
theorem tModulus_mono {l₁ l₂ l₃ n : ℕ} (h₁ : l₁ ≤ n) (h₂ : l₂ ≤ n) (h₃ : l₃ ≤ n) (np V : ℕ) :
    tModulus np l₁ l₂ l₃ V ≤ tModulus np n n n V := by
  have hcoll₁ := tColl_mono h₁ V
  have hcoll₂ := tColl_mono h₂ V
  have hcoll₃ := tColl_mono h₃ V
  have hsearch : tSearch np l₁ l₂ l₃ V ≤ tSearch np n n n V :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
  unfold tModulus
  omega
theorem tNodeArray_mono {l₁ l₂ l₃ n : ℕ} (h₁ : l₁ ≤ n) (h₂ : l₂ ≤ n) (h₃ : l₃ ≤ n) (m V : ℕ) :
    tNodeArray m l₁ l₂ l₃ V ≤ tNodeArray m n n n V := by
  have hresid₁ := tResid_mono h₁ V
  have hresid₂ := tResid_mono h₂ V
  have hresid₃ := tResid_mono h₃ V
  have htally₁ := tTally_mono h₁
  have htally₂ := tTally_mono h₂
  have htally₃ := tTally_mono h₃
  unfold tNodeArray
  omega
end needs
section parts
variable {P₀ R : Program} {p pMod pArr pC3 pHeavy : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {a : NodeArgs} {Λ cx f Mo : ℕ} {μ μ₀ μ' : ℕ → ℤ}
structure NodesFits (lim : Limits) (d fr n V m f : ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  room : fr + n + 8 * (m * m) ≤ lim.space
  levels : f ≤ lim.space
  wordV : 64 * ((V : ℤ) + 1) ≤ lim.word
  wordM : 64 * ((m : ℤ) * m + 1) ≤ lim.word
  depth : d < lim.depth
theorem NodesPre.fits (H : NodesPre lim r μ a Λ cx (f + 1) d) (hn : 1 ≤ a.n) :
    NodesFits lim d a.fr a.n a.V a.m f := by
  have hcells := H.ok.cells
  have hdepth := H.ok.depth
  have hword : ((wordNeed a.n a.V (a.m * a.m) : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast le_max_left _ _) H.ok.word
  simp only [nodesNeed] at hcells hdepth
  have hlevels : f ≤ f * a.n := Nat.le_mul_of_pos_right f hn
  have hsucc : (f + 1) * a.n = f * a.n + a.n := by ring
  have hsq : a.m ^ 2 = a.m * a.m := pow_two a.m
  have hone : 1 ≤ (a.n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨H.ok.space, by omega, by omega, ?_, ?_, by omega⟩
  · simpa using mul_le_word (x := 1) (y := 1) (z := 64 * (a.V + 1)) hword hone (by omega) le_rfl
  · have h := mul_le_word (x := 1) (y := a.m * a.m + 1) (z := 64) hword hone le_rfl (by omega)
    push_cast at h
    linarith
theorem NodesPre.child₁ (H : NodesPre lim r μ₀ a Λ cx (f + 1) d) (kept : Kept μ₀ μ a.fr)
    (hk : KeptBut μ μ' (a.fr + a.X₁.len) a.fr a.X₁.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₁.set Mo) (ChanHe.heavy a.X₁.set Mo)) :
    NodesPre lim r μ' (a.child₁ Mo) Λ cx f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₁ hk hs
    ctx := H.ctx.kept H.belowCtx (kept.then hk fun b hb => by omega)
    belowCtx := H.belowCtx.trans (Nat.le_add_right _ _)
    ok := childNeed_ok H.ok H.mem.set₁.le }
theorem NodesPre.child₂ (H : NodesPre lim r μ₀ a Λ cx (f + 1) d) (kept : Kept μ₀ μ a.fr)
    (hk : KeptBut μ μ' (a.fr + a.X₂.len) a.fr a.X₂.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₂.set Mo) (ChanHe.heavy a.X₂.set Mo)) :
    NodesPre lim r μ' (a.child₂ Mo) Λ cx f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₂ hk hs
    ctx := H.ctx.kept H.belowCtx (kept.then hk fun b hb => by omega)
    belowCtx := H.belowCtx.trans (Nat.le_add_right _ _)
    ok := childNeed_ok H.ok H.mem.set₂.le }
theorem NodesPre.child₃ (H : NodesPre lim r μ₀ a Λ cx (f + 1) d) (kept : Kept μ₀ μ a.fr)
    (hk : KeptBut μ μ' (a.fr + a.X₃.len) a.fr a.X₃.len)
    (hs : SetAt μ' a.fr #(ChanHe.heavy a.X₃.set Mo) (ChanHe.heavy a.X₃.set Mo)) :
    NodesPre lim r μ' (a.child₃ Mo) Λ cx f (d + 1) :=
  { H with
    mem := (H.mem.kept kept).child₃ hk hs
    ctx := H.ctx.kept H.belowCtx (kept.then hk fun b hb => by omega)
    belowCtx := H.belowCtx.trans (Nat.le_add_right _ _)
    ok := childNeed_ok H.ok H.mem.set₃.le }
abbrev NodeArgs.node (a : NodeArgs) (Mo : ℕ) : Node := ⟨a.X₁.set, a.X₂.set, a.X₃.set, Mo⟩
@[simp] abbrev nodesLocals (x : ℤ) (a : NodeArgs) (Λ cx : ℕ) (t : List ℤ) : List ℤ :=
  x :: a.sets ++ [(cx : ℤ), a.fr, a.V, a.m, Λ, a.np, a.pr, a.cnt] ++ t
theorem nodesParams_ends (hctx : CtxAt μ cx a.V a.m Λ a.np a.pr a.cnt) (hcx : cx + 6 ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) {x : ℤ} :
    Ends lim P d nodesParams ⟨frame (x :: a.sets ++ [(cx : ℤ), a.fr]), μ⟩ 28 fun σ' =>
      σ' = ⟨frame (nodesLocals x a Λ cx []), μ⟩ := by
  have hV : μ cx = a.V := by simpa using hctx 0 (by simp)
  have hm : μ (cx + 1) = a.m := by simpa using hctx 1 (by simp)
  have hΛ : μ (cx + 2) = Λ := by simpa using hctx 2 (by simp)
  have hnp : μ (cx + 3) = a.np := by simpa using hctx 3 (by simp)
  have hpr : μ (cx + 4) = a.pr := by simpa using hctx 4 (by simp)
  have hcnt : μ (cx + 5) = a.cnt := by simpa using hctx 5 (by simp)
  have haddr : ∀ j : ℤ, 0 ≤ j → ((cx : ℤ) + j).toNat = cx + j.toNat := fun j hj => by omega
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen a.V ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hV]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hV] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hV] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                       )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen a.m ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hm]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hm] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hm] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                       )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen Λ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 haddr, hΛ]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [haddr, hΛ] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hΛ] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                            )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen a.np ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 haddr, hnp]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [haddr, hnp] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hnp] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen a.pr ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 haddr, hpr]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [haddr, hpr] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hpr] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen a.cnt ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 haddr, hcnt]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [haddr, hcnt] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hcnt] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                  )
  rfl
theorem c3_meets (hsol : Solves c3Task P₀ pC3 T r) (hV : 1 ≤ a.V) (hm : 1 ≤ a.m)
    (hN : NodeMem μ₀ a) (harr : ∀ u < 8 * a.m ^ 2, μ (a.fr + u) = (a.node Mo).oneArray a.V u)
    (hok : (r (8 * a.m ^ 2) (60 * a.V + 40)).Ok lim (a.fr + 8 * a.m ^ 2) d) :
    Meets lim (P₀ ++ R) pC3 d
      [(8 * a.m ^ 2 : ℕ), (60 * a.V + 40 : ℕ), a.fr, (a.fr + 8 * a.m ^ 2 : ℕ)] μ
      (T (8 * a.m ^ 2) (60 * a.V + 40)) fun res μ' =>
        res = flag (ConvOne (8 * a.m ^ 2) ((a.node Mo).oneArray a.V)) ∧
          Kept μ μ' (a.fr + 8 * a.m ^ 2) := by
  have hpos : 1 ≤ a.m ^ 2 := Nat.one_le_pow _ _ hm
  refine (hsol.meets R (⟨8 * a.m ^ 2, 60 * a.V + 40, a.fr,
    (List.range (8 * a.m ^ 2)).map fun u => (a.node Mo).oneArray a.V u⟩ : VecInst)
    (a.fr + 8 * a.m ^ 2) ⟨?_, ?_, by simp, ?_, ?_, le_rfl⟩ hok).mono le_rfl ?_
  ·
    change 1 ≤ 8 * a.m ^ 2
    omega
  ·
    change 1 ≤ 60 * a.V + 40
    omega
  ·
    intro u hu
    simp [harr u (by simpa using hu)]
  ·
    intro e he
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 he
    have := Node.abs_oneArray_le (ν := a.node Mo) hN.set₁.bdd hN.set₂.bdd hN.set₃.bdd u
    push_cast
    exact this
  · rintro _ μ' ⟨rfl, kept⟩
    exact ⟨flag_congr (conv_range_iff _ _), kept⟩
theorem nodesOwn_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (H : NodesPre lim r μ a Λ cx (f + 1) d) (hn : 1 ≤ a.n)
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set) (hM1 : 1 ≤ Mo)
    (hM : Mo ≤ a.m * a.m) {x : ℤ} :
    Ends lim (P₀ ++ R) d (nodesOwn pMod pArr pC3) ⟨frame (nodesLocals x a Λ cx []), μ⟩
      (47 + tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V +
        tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V + T (8 * a.m ^ 2) (60 * a.V + 40))
      fun σ' => ∃ (y : ℤ) (μ' : ℕ → ℤ), Kept μ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals x a Λ cx [Mo, (8 * a.m ^ 2 : ℕ), (a.fr + 8 * a.m ^ 2 : ℕ), y,
          flag (ConvOne (8 * a.m ^ 2) ((a.node Mo).oneArray a.V))]), μ'⟩ := by
  have hfits := H.fits hn
  have hroom := hfits.room
  (((obtain ⟨⟩ := _root_.id hfits))
                  )
  have hsq : a.m ^ 2 = a.m * a.m := pow_two a.m
  have hnonneg : (0 : ℤ) ≤ (a.m : ℤ) * a.m := by positivity
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((C.modulus a Λ μ H.mem (H.lam ▸ lam_le a.V) (d + 1) (modulusNeed_ok H.ok)) _
                 (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (C.modulus a Λ μ H.mem (H.lam ▸ lam_le a.V) (d + 1) (modulusNeed_ok H.ok)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁ ⟨rfl, kept₁⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                         )
  rw [← hMo]
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (8 * a.m ^ 2 : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hsq]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hsq] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsq] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                      )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen (a.fr + 8 * a.m ^ 2 : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hsq]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hsq] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsq] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                             )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((C.array (a.push (8 * a.m ^ 2)) Mo a.fr μ₁ ((H.mem.kept kept₁).push .refl) hM1 hM
                   ⟨le_rfl, Or.inr H.mem.set₁.below, Or.inr H.mem.set₂.below, Or.inr H.mem.set₃.below,
                     Or.inr H.mem.envOk.belowCnt⟩
                   (d + 1) (nodeArrayNeed_ok H.ok))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (C.array (a.push (8 * a.m ^ 2)) Mo a.fr μ₁ ((H.mem.kept kept₁).push .refl) hM1 hM
                 ⟨le_rfl, Or.inr H.mem.set₁.below, Or.inr H.mem.set₂.below, Or.inr H.mem.set₃.below,
                   Or.inr H.mem.envOk.belowCnt⟩
                 (d + 1) (nodeArrayNeed_ok H.ok))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro y μ₂
               ⟨harr, (kept₂ : KeptBut μ₁ μ₂ (a.fr + 8 * a.m ^ 2) a.fr (8 * a.m ^ 2))⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                    )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((c3_meets C.solver H.V_pos H.m_pos H.mem harr (solverNeed_ok H.ok)) _ (by omega)) ?_ ?_
               ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (c3_meets C.solver H.V_pos H.m_pos H.mem harr (solverNeed_ok H.ok)) ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₃ ⟨rfl, kept₃⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                         )
  exact ⟨y, μ₃, (kept₁.then kept₂ fun b hb => by omega).then kept₃ fun b hb => by omega, rfl⟩
theorem nodesChild₁_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ₀ a Λ cx (f + 1) d)
    (hn : 1 ≤ a.n) (kept : Kept μ₀ μ a.fr) (hM1 : 1 ≤ Mo) (hM : Mo ≤ a.m * a.m)
    {x y z a₀ : ℤ} :
    Ends lim (P₀ ++ R) d (nodesChild₁ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀]), μ⟩
      (25 + tHeavy a.X₁.len a.V + tNodes T a.n a.V a.m a.np ((a.child₁ Mo).calls Λ f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀,
          #(ChanHe.heavy a.X₁.set Mo), flag ((a.child₁ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have hroom := hfits.room
  have hX := (H.mem.kept kept).set₁
  have hle := hX.le
  (((obtain ⟨⟩ := _root_.id hfits))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((C.heavy (d + 1) (a.fr + a.X₁.len) _ _ _ _ a.fr _ _ _ μ
                   ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
                   ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (C.heavy (d + 1) (a.fr + a.X₁.len) _ _ _ _ a.fr _ _ _ μ
                 ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
                 ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁
               ⟨rfl, hset, kept₁⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                               )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((ih (a.child₁ Mo) Λ cx μ₁ (d + 1) (H.child₁ kept kept₁ hset)) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (ih (a.child₁ Mo) Λ cx μ₁ (d + 1) (H.child₁ kept kept₁ hset))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₁.len))⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                          )
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩
theorem nodesChild₂_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ₀ a Λ cx (f + 1) d)
    (hn : 1 ≤ a.n) (kept : Kept μ₀ μ a.fr) (hM1 : 1 ≤ Mo) (hM : Mo ≤ a.m * a.m)
    {x y z a₀ h₁ a₁ : ℤ} :
    Ends lim (P₀ ++ R) d (nodesChild₂ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀, h₁, a₁]), μ⟩
      (25 + tHeavy a.X₂.len a.V + tNodes T a.n a.V a.m a.np ((a.child₂ Mo).calls Λ f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀, h₁, a₁,
          #(ChanHe.heavy a.X₂.set Mo), flag ((a.child₂ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have hroom := hfits.room
  have hX := (H.mem.kept kept).set₂
  have hle := hX.le
  (((obtain ⟨⟩ := _root_.id hfits))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((C.heavy (d + 1) (a.fr + a.X₂.len) _ _ _ _ a.fr _ _ _ μ
                   ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
                   ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (C.heavy (d + 1) (a.fr + a.X₂.len) _ _ _ _ a.fr _ _ _ μ
                 ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
                 ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁
               ⟨rfl, hset, kept₁⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                               )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((ih (a.child₂ Mo) Λ cx μ₁ (d + 1) (H.child₂ kept kept₁ hset)) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (ih (a.child₂ Mo) Λ cx μ₁ (d + 1) (H.child₂ kept kept₁ hset))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₂.len))⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                          )
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩
theorem nodesChild₃_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ₀ a Λ cx (f + 1) d)
    (hn : 1 ≤ a.n) (kept : Kept μ₀ μ a.fr) (hM1 : 1 ≤ Mo) (hM : Mo ≤ a.m * a.m)
    {x y z a₀ h₁ a₁ h₂ a₂ : ℤ} :
    Ends lim (P₀ ++ R) d (nodesChild₃ p pHeavy)
      ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀, h₁, a₁, h₂, a₂]), μ⟩
      (25 + tHeavy a.X₃.len a.V + tNodes T a.n a.V a.m a.np ((a.child₃ Mo).calls Λ f))
      fun σ' => ∃ μ' : ℕ → ℤ, Kept μ₀ μ' a.fr ∧
        σ' = ⟨frame (nodesLocals (f + 1 : ℕ) a Λ cx [Mo, x, y, z, a₀, h₁, a₁, h₂, a₂,
          #(ChanHe.heavy a.X₃.set Mo), flag ((a.child₃ Mo).Yes Λ f)]), μ'⟩ := by
  have hfits := H.fits hn
  have hroom := hfits.room
  have hX := (H.mem.kept kept).set₃
  have hle := hX.le
  (((obtain ⟨⟩ := _root_.id hfits))
                  )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((C.heavy (d + 1) (a.fr + a.X₃.len) _ _ _ _ a.fr _ _ _ μ
                   ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
                   ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (C.heavy (d + 1) (a.fr + a.X₃.len) _ _ _ _ a.fr _ _ _ μ
                 ((hX.push .refl).bucket ((H.mem.kept kept).envOk.push .refl) hM1 hM)
                 ⟨le_rfl, Or.inl hX.below, Or.inr H.mem.envOk.belowCnt⟩ (collNeed_ok H.ok hle hM))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁
               ⟨rfl, hset, kept₁⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                               )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((ih (a.child₃ Mo) Λ cx μ₁ (d + 1) (H.child₃ kept kept₁ hset)) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (ih (a.child₃ Mo) Λ cx μ₁ (d + 1) (H.child₃ kept kept₁ hset))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂ ⟨rfl, (kept₂ : Kept μ₁ μ₂ (a.fr + a.X₃.len))⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                          )
  exact ⟨μ₂, (kept.then kept₁ fun b hb => by omega).then kept₂ fun b hb => by omega, rfl⟩
theorem nodesAnswer_ends {loc : ℕ → ℤ} {R₀ R₁ R₂ R₃ : Prop} (hword : (4 : ℤ) ≤ lim.word)
    (hloc : loc NodesLocals.ANS0 = flag R₀ ∧ loc NodesLocals.ANS1 = flag R₁ ∧
      loc NodesLocals.ANS2 = flag R₂ ∧ loc NodesLocals.ANS3 = flag R₃ := by
      exact ⟨rfl, rfl, rfl, rfl⟩) :
    Ends lim P d nodesAnswer ⟨loc, μ⟩ 12 fun σ' =>
      σ'.loc 0 = flag (R₀ ∨ R₁ ∨ R₂ ∨ R₃) ∧ σ'.mem = μ := by
  obtain ⟨e₀, e₁, e₂, e₃⟩ := hloc
  have f₀ := flag_mem R₀
  have f₁ := flag_mem R₁
  have f₂ := flag_mem R₂
  have f₃ := flag_mem R₃
  unfold nodesAnswer
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_) (by (((  (try have := _root_.Light.Std.space_le (by assumption))
                                                                (try have := _root_.Light.Std.const_le (by assumption))
                                                                simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, e₀, e₁, e₂, e₃] <;> omega))
                                                                                     ))
  · have hpos : 0 < flag R₀ + flag R₁ + flag R₂ + flag R₃ := by simpa [e₀, e₁, e₂, e₃] using hyes
    exact Ends.setLast ⟨by simp [flag_of ((flag_sum_pos _ _ _ _).1 hpos)], rfl⟩ (by simp; omega)
  · have hzero : ¬ 0 < flag R₀ + flag R₁ + flag R₂ + flag R₃ := by
      simpa [e₀, e₁, e₂, e₃] using hno
    exact Ends.setLast ⟨by simp [flag_of_not fun h => hzero ((flag_sum_pos _ _ _ _).2 h)], rfl⟩
      (by simp; omega)
theorem tNodes_succ_le (hN : NodeMem μ a) (hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅))
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set) :
    178 + tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V +
      tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V + T (8 * a.m ^ 2) (60 * a.V + 40) +
      tHeavy a.X₁.len a.V + tHeavy a.X₂.len a.V + tHeavy a.X₃.len a.V +
      tNodes T a.n a.V a.m a.np ((a.child₁ Mo).calls Λ f) +
      tNodes T a.n a.V a.m a.np ((a.child₂ Mo).calls Λ f) +
      tNodes T a.n a.V a.m a.np ((a.child₃ Mo).calls Λ f)
    ≤ tNodes T a.n a.V a.m a.np (a.calls Λ (f + 1)) := by
  have hmod := tModulus_mono hN.set₁.le hN.set₂.le hN.set₃.le a.np a.V
  have harr := tNodeArray_mono hN.set₁.le hN.set₂.le hN.set₃.le a.m a.V
  have hheavy₁ := tHeavy_mono hN.set₁.le a.V
  have hheavy₂ := tHeavy_mono hN.set₂.le a.V
  have hheavy₃ := tHeavy_mono hN.set₃.le a.V
  have hcalls : a.calls Λ (f + 1) =
      1 + ((a.child₁ Mo).calls Λ f + (a.child₂ Mo).calls Λ f + (a.child₃ Mo).calls Λ f) := by
    simp [NodeArgs.calls, treeCalls, if_neg hS, ← hMo]
  rw [hcalls]
  generalize (a.child₁ Mo).calls Λ f = c₁
  generalize (a.child₂ Mo).calls Λ f = c₂
  generalize (a.child₃ Mo).calls Λ f = c₃
  simp only [tNodes]
  have hnode : tNode T a.n a.V a.m a.np = tModulus a.np a.n a.n a.n a.V +
      tNodeArray a.m a.n a.n a.n a.V + T (8 * a.m ^ 2) (60 * a.V + 40) + 3 * tHeavy a.n a.V +
      300 := rfl
  rw [show (1 + (c₁ + c₂ + c₃)) * (tNode T a.n a.V a.m a.np + 60) =
    (tNode T a.n a.V a.m a.np + 60) + c₁ * (tNode T a.n a.V a.m a.np + 60) +
    c₂ * (tNode T a.n a.V a.m a.np + 60) + c₃ * (tNode T a.n a.V a.m a.np + 60) by ring]
  omega
theorem NodeArgs.yes_succ (hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅))
    (hMo : Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set) :
    a.Yes Λ (f + 1) ↔ ConvOne (8 * a.m ^ 2) ((a.node Mo).oneArray a.V) ∨
      (a.child₁ Mo).Yes Λ f ∨ (a.child₂ Mo).Yes Λ f ∨ (a.child₃ Mo).Yes Λ f := by
  simp only [NodeArgs.Yes, TreeYes, NodeArgs.child₁, NodeArgs.child₂, NodeArgs.child₃, Slot.heavy,
    Env.push, nodes, if_neg hS, ← hMo, List.mem_cons, List.mem_append, or_and_right, exists_or,
    exists_eq_left, or_assoc]
theorem nodesMain_ends (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r)
    (ih : NodesSpecAt lim (P₀ ++ R) p T r f) (H : NodesPre lim r μ a Λ cx (f + 1) d)
    (hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅)) (hn : 1 ≤ a.n) :
    Ends lim (P₀ ++ R) d (nodesMain p pMod pArr pC3 pHeavy)
      ⟨frame (((f + 1 : ℕ) : ℤ) :: a.sets ++ [(cx : ℤ), a.fr]), μ⟩
      (tNodes T a.n a.V a.m a.np (a.calls Λ (f + 1)) - 16) fun σ' =>
      σ'.loc 0 = flag (a.Yes Λ (f + 1)) ∧ Kept μ σ'.mem a.fr := by
  obtain ⟨Mo, hMo⟩ :
      ∃ Mo, Mo = ChanHe.modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set := ⟨_, rfl⟩
  obtain ⟨hM1, hM⟩ : 1 ≤ Mo ∧ Mo ≤ a.m * a.m := by
    have := modulus_bounds H.primes (fun q hq => Nat.prime_of_mem_primesLE hq)
      (fun q hq => Nat.le_of_mem_primesLE hq) H.mem.set₁.bdd H.mem.set₂.bdd H.mem.set₃.bdd
    rwa [← H.lam, ← hMo, pow_two] at this
  have htime := tNodes_succ_le (T := T) (f := f) H.mem hS hMo
  have hfits := H.fits hn
  have hroom := hfits.room
  (((obtain ⟨⟩ := _root_.id H; obtain ⟨⟩ := _root_.id hfits))
                    )
  rw [flag_congr (NodeArgs.yes_succ hS hMo)]
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (nodesParams_ends H.ctx (by omega) hfits.space_le) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (nodesParams_ends H.ctx (by omega) hfits.space_le) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ rfl))
                                                                          )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (nodesOwn_ends C H hn hMo hM1 hM) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (nodesOwn_ends C H hn hMo hM1 hM) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨x, μ₁, kept₁, rfl⟩
                 ))
                                                                         )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (nodesChild₁_ends C ih H hn kept₁ hM1 hM) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (nodesChild₁_ends C ih H hn kept₁ hM1 hM) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨μ₂, kept₂, rfl⟩))
                                                                              )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (nodesChild₂_ends C ih H hn kept₂ hM1 hM) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (nodesChild₂_ends C ih H hn kept₂ hM1 hM) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨μ₃, kept₃, rfl⟩))
                                                                              )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (nodesChild₃_ends C ih H hn kept₃ hM1 hM) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (nodesChild₃_ends C ih H hn kept₃ hM1 hM) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨μ₄, kept₄, rfl⟩
                 ))
                                                                              )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (nodesAnswer_ends (by omega)) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (nodesAnswer_ends (by omega)) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨hres, hmem⟩))
                                                              )
  exact ⟨hres, hmem ▸ kept₄⟩
end parts
theorem nodes_spec {P₀ R : Program} {p pMod pArr pC3 pHeavy : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (C : NodesCtx lim P₀ R p pMod pArr pC3 pHeavy T r) :
    NodesSpec lim (P₀ ++ R) p T r := by
  intro f
  induction f with
  | zero =>
    intro a Λ cx μ d H
    have hzero : (0 : ℤ) ≤ lim.word := le_trans (by positivity) H.ok.space
    refine .of_body C.self (Ends.iteLast (fun _ => ?_) (fun h => absurd h (by simp))
      (hT := by simp [tNodes, treeCalls]))
    exact Ends.setTo 0 ⟨by simp [flag_of_not, TreeYes, nodes], .refl⟩
      (hT := by simp [tNodes, treeCalls])
  | succ f ih =>
    intro a Λ cx μ d H
    have hzero : (0 : ℤ) ≤ lim.word := le_trans (by positivity) H.ok.space
    have htime : 60 ≤ tNodes T a.n a.V a.m a.np (a.calls Λ (f + 1)) :=
      le_trans (by omega) (Nat.le_mul_of_pos_left _ (one_le_treeCalls _ _ _ _ _ _))
    have hempty : (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅) → ∀ T', 2 ≤ T' →
        Ends lim (P₀ ++ R) d (.set 0 (k 0))
          ⟨frame (((f + 1 : ℕ) : ℤ) :: a.sets ++ [(cx : ℤ), a.fr]), μ⟩ T' fun σ' =>
          σ'.loc 0 = flag (a.Yes Λ (f + 1)) ∧ Kept μ σ'.mem a.fr := fun h T' hT' =>
      Ends.setTo 0 ⟨by simp [flag_of_not, TreeYes, nodes, h], .refl⟩
    refine .of_body C.self (Ends.iteLast (fun h => absurd h (by simp; omega)) fun _ => ?_)
    refine Ends.iteLast (fun h => ?_) fun h₁ => ?_
    · exact hempty (Or.inl (H.mem.set₁.set.eq_empty (by simpa using h))) _ (by (((first
                                                                                    | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                                          _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                        first
                                                                                        | omega
                                                                                        | (ring_nf; omega))
                                                                                    | omega
                                                                                    |
                                                                                      (simp [] <;>
                                                                                          first
                                                                                          | omega
                                                                                          | (ring_nf; omega))))
                                                                                        ))
    refine Ends.iteLast (fun h => ?_) fun h₂ => ?_
    · exact hempty (Or.inr (Or.inl (H.mem.set₂.set.eq_empty (by simpa using h)))) _
        (by (((first
                 | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                       _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                     first
                     | omega
                     | (ring_nf; omega))
                 | omega
                 |
                   (simp [] <;>
                       first
                       | omega
                       | (ring_nf; omega))))
                     ))
    refine Ends.iteLast (fun h => ?_) fun h₃ => ?_
    · exact hempty (Or.inr (Or.inr (H.mem.set₃.set.eq_empty (by simpa using h)))) _
        (by (((first
                 | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                       _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                     first
                     | omega
                     | (ring_nf; omega))
                 | omega
                 |
                   (simp [] <;>
                       first
                       | omega
                       | (ring_nf; omega))))
                     ))
    have hl₁ : a.X₁.len ≠ 0 := by simpa using h₁
    have hS : ¬ (a.X₁.set = ∅ ∨ a.X₂.set = ∅ ∨ a.X₃.set = ∅) := by
      rintro (h | h | h)
      · exact hl₁ (by rw [← H.mem.set₁.set.card, h, Finset.card_empty])
      · exact h₂ (by simp [← H.mem.set₂.set.card, h])
      · exact h₃ (by simp [← H.mem.set₃.set.card, h])
    ((focus
         (refine
             _root_.Light.Ends.pieceLast (nodesMain_ends C ih H hS (by have := H.mem.set₁.le; omega))
               (fun _ macro_local_1 => macro_local_1) ?_;
           on_goal -1 =>
             ((first
                 | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                       _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                       _root_.List.sum_cons, _root_.List.sum_nil, ]
                     first
                     | omega
                     | (ring_nf; omega))
                 | omega
                 |
                   (simp [] <;>
                       first
                       | omega
                       | (ring_nf; omega))))))
                                                                           )
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
variable {lim : Limits} {P : Program} {d : ℕ}
namespace RoundLocals
abbrev BETA : ℕ := 0
@[inherit_doc BETA] abbrev BETA' : ℕ := 1
@[inherit_doc BETA] abbrev BIT : ℕ := 2
@[inherit_doc BETA] abbrev NVALUES : ℕ := 3
@[inherit_doc BETA] abbrev VAL : ℕ := 4
@[inherit_doc BETA] abbrev BITS : ℕ := 5
@[inherit_doc BETA] abbrev LAM : ℕ := 6
@[inherit_doc BETA] abbrev OUT0 : ℕ := 7
@[inherit_doc BETA] abbrev NMAX : ℕ := 8
@[inherit_doc BETA] abbrev LEVELS : ℕ := 9
@[inherit_doc BETA] abbrev CTX : ℕ := 10
@[inherit_doc BETA] abbrev FREE : ℕ := 11
@[inherit_doc BETA] abbrev NBIT : ℕ := 12
@[inherit_doc BETA] abbrev OUT1 : ℕ := 13
@[inherit_doc BETA] abbrev OUT2 : ℕ := 14
@[inherit_doc BETA] abbrev SIZE0 : ℕ := 15
@[inherit_doc BETA] abbrev SIZE1 : ℕ := 16
@[inherit_doc BETA] abbrev SIZE2 : ℕ := 17
end RoundLocals
open RoundLocals in
def roundSets (pPick : ℕ) : Stmt :=
  .set NBIT (k 1 -' v BIT) ;;
  .set OUT1 (v OUT0 +' v NMAX) ;;
  .set OUT2 (v OUT1 +' v NMAX) ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v BIT, v BETA', k 0, k 0, v OUT0] SIZE0 ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v NBIT, v BETA', k 0, k 1, v OUT1] SIZE1 ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v NBIT, v BETA', k 1, k 1, v OUT2] SIZE2
open RoundLocals in
def roundBody (pPick pNodes : ℕ) : Stmt :=
  roundSets pPick ;;
  .call pNodes [v LEVELS, v OUT0, v SIZE0, v OUT1, v SIZE1, v OUT2, v SIZE2, v CTX, v FREE] 0
theorem ChRound.treeCalls_le_pow (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    treeCalls Q Λ f S₁ S₂ S₃ ≤ 2 * 3 ^ f := by
  have hcalls := treeCalls_le Q Λ f S₁ S₂ S₃
  have hnodes := length_nodes_le Q Λ f S₁ S₂ S₃
  omega
section front
variable {μ μ' : ℕ → ℤ} {a : FrontArgs}
theorem FrontMem.keptBut (h : FrontMem μ a)
    (hk : KeptBut μ μ' a.fr a.A (3 * a.n)) : FrontMem μ' a := by
  have keep : ∀ s len : ℕ, s + len ≤ a.fr → Apart a.A (3 * a.n) s len →
      ∀ i < len, μ' (s + i) = μ (s + i) := fun s len hb hap i hi =>
    hk _ ⟨by omega, by omega⟩
  exact { h with
    segVal := h.segVal.congr fun i hi => keep a.val a.nd h.belowVal h.apartVal i (h.lenD ▸ hi)
    segBt := h.segBt.congr fun i hi => keep a.bt (a.nd * a.Λ) h.belowBt h.apartBt i
      (by rw [← h.lenD, ← length_bitTable a.V]; exact hi)
    ctx := Seg.congr h.ctx fun i hi => keep a.cx 6 h.belowCx h.apartCx i (by simpa using hi)
    primes := ⟨h.primes.1, h.primes.2.congr fun i hi =>
      keep a.pr a.np h.belowPr h.apartPr i (by rw [h.primes.1]; simpa using hi)⟩
    zero := fun i hi => (keep a.cnt (a.m * a.m) h.belowCnt h.apartCnt i hi).trans (h.zero i hi) }
theorem FrontMem.of_sameOutside (h : FrontMem μ a)
    (hs : SameOutside μ μ' a.A (3 * a.n)) : FrontMem μ' a :=
  h.keptBut (SameOn.mono hs fun _ hb => hb.2)
theorem FrontMem.pick_meets (h : FrontMem μ a) {pPick : ℕ}
    (hPick : PickSpec lim P pPick) {β β' o : ℕ} (hβ : β < a.Λ) (hβ' : β' < a.Λ) (x x' two : ℤ)
    (ho : o + a.n ≤ 3 * a.n) (hfr : a.fr ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word)
    (hword : (8 : ℤ) ≤ lim.word) :
    Meets lim P pPick d [a.nd, a.val, a.bt, a.Λ, β, x, β', x', two, (a.A + o : ℕ)] μ (tPick a.nd)
      fun r μ' =>
      r = ((pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).length : ℤ) ∧
        Seg μ' (a.A + o) (pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)) ∧
        SameOutside μ μ' (a.A + o) a.nd := by
  (((obtain ⟨⟩ := _root_.id h))
              )
  have hrows : a.D.length * a.Λ = a.nd * a.Λ := by rw [h.lenD]
  rw [← h.lenD]
  exact hPick d a.val a.bt (a.A + o) a.Λ β β' x x' two a.D _ μ {
    lenTable := length_bitTable a.V a.Λ a.D
    posA := hβ
    posB := hβ'
    segSrc := h.segVal
    segTable := h.segBt
    apartSrc := by omega
    apartTable := by omega
    spaceSrc := by omega
    spaceTable := by omega
    spaceOut := by omega
    space_le := hw
    word := hword }
theorem FrontMem.nodeMem (h : FrontMem μ a)
    {k₁ k₂ k₃ : ℕ} {S₁ S₂ S₃ : Finset ℤ} (h₁ : SetAt μ a.A k₁ S₁) (h₂ : SetAt μ (a.A + a.n) k₂ S₂)
    (h₃ : SetAt μ (a.A + a.n + a.n) k₃ S₃) (hk₁ : k₁ ≤ a.n) (hk₂ : k₂ ≤ a.n) (hk₃ : k₃ ≤ a.n)
    (hS₁ : S₁ ⊆ a.D.toFinset) (hS₂ : S₂ ⊆ a.D.toFinset) (hS₃ : S₃ ⊆ a.D.toFinset) :
    NodeMem μ ⟨a.toEnv, ⟨a.A, k₁, S₁⟩, ⟨a.A + a.n, k₂, S₂⟩, ⟨a.A + a.n + a.n, k₃, S₃⟩⟩ := by
  (((obtain ⟨⟩ := _root_.id h))
              )
  exact
    { envOk := ⟨h.primes, h.zero, h.belowPr, h.belowCnt, h.cntPr⟩
      set₁ := ⟨h₁, hk₁, h.bdd.mono hS₁, by dsimp only; omega, by dsimp only; omega⟩
      set₂ := ⟨h₂, hk₂, h.bdd.mono hS₂, by dsimp only; omega, by dsimp only; omega⟩
      set₃ := ⟨h₃, hk₃, h.bdd.mono hS₃, by dsimp only; omega, by dsimp only; omega⟩ }
theorem roundSets_ends (hF : FrontMem μ a) {pPick : ℕ}
    (hPick : PickSpec lim P pPick) {β β' f : ℕ} (hβ : β < a.Λ) (hβ' : β' < a.Λ) (v : Bool)
    (hfr : a.fr ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word) (hword : (8 : ℤ) ≤ lim.word)
    (hd : d < lim.depth) :
    Ends lim P d (roundSets pPick)
      ⟨frame [β, β', if v then 1 else 0, a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr], μ⟩
        (48 + 3 * tPick a.nd)
      fun σ' => ∃ (k₁ k₂ k₃ : ℕ) (μ' : ℕ → ℤ), SameOutside μ μ' a.A (3 * a.n) ∧
        NodeMem μ' ⟨a.toEnv, ⟨a.A, k₁, splitA a.V β v a.D.toFinset⟩,
          ⟨a.A + a.n, k₂, splitB a.V β β' v false a.D.toFinset⟩,
          ⟨a.A + a.n + a.n, k₃, splitB a.V β β' v true a.D.toFinset⟩⟩ ∧
        σ' = ⟨frame [β, β', if v then 1 else 0, a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr,
          if !v then 1 else 0, (a.A + a.n : ℕ), (a.A + a.n + a.n : ℕ), k₁, k₂, k₃], μ'⟩ := by
  have hA := hF.belowA
  have hndn := hF.nd_le
  have hlen : ∀ x x' two, (pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).length ≤ a.n :=
    fun x x' two => (length_pickList_le a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).trans
      (hF.lenD ▸ hndn)
  refine Ends.setToThen (if !v then 1 else 0) ?_ (by cases v <;> simp <;> omega)
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (a.A + a.n : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                          )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (a.A + a.n + a.n : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hF.pick_meets (o := 0) hPick hβ hβ' (if v then 1 else 0) 0 0 (by omega) hfr hw hword)
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hF.pick_meets (o := 0) hPick hβ hβ' (if v then 1 else 0) 0 0 (by omega) hfr hw hword)
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁ ⟨rfl, seg₁, same₁⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                        )
  have out₁ : SameOutside μ μ₁ a.A (3 * a.n) := same₁.mono (by omega) (by omega)
  have hF₁ := hF.of_sameOutside out₁
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hF₁.pick_meets (o := a.n) hPick hβ hβ' (if !v then 1 else 0) 0 1 (by omega) hfr hw
                   hword)
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hF₁.pick_meets (o := a.n) hPick hβ hβ' (if !v then 1 else 0) 0 1 (by omega) hfr hw
                 hword)
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂ ⟨rfl, seg₂, same₂⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                        )
  have out₂ : SameOutside μ₁ μ₂ a.A (3 * a.n) := same₂.mono (by omega) (by omega)
  have hF₂ := hF₁.of_sameOutside out₂
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hF₂.pick_meets (o := a.n + a.n) hPick hβ hβ' (if !v then 1 else 0) 1 1 (by omega) hfr
                   hw hword)
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hF₂.pick_meets (o := a.n + a.n) hPick hβ hβ' (if !v then 1 else 0) 1 1 (by omega) hfr
                 hw hword)
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₃ ⟨rfl, seg₃, same₃⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                        )
  have out₃ : SameOutside μ₂ μ₃ a.A (3 * a.n) := same₃.mono (by omega) (by omega)
  obtain ⟨nodup₁, set₁⟩ := pick_splitA a.V a.Λ hβ hβ' v 0 hF.nodup
  obtain ⟨nodup₂, set₂⟩ := pick_splitB a.V a.Λ hβ hβ' v false hF.nodup
  obtain ⟨nodup₃, set₃⟩ := pick_splitB a.V a.Λ hβ hβ' v true hF.nodup
  have hlen₁ := hlen (if v then 1 else 0) 0 0
  have hlen₂ := hlen (if !v then 1 else 0) 0 1
  exact ⟨_, _, _, μ₃, out₁.trans (out₂.trans out₃),
    (hF₂.of_sameOutside out₃).nodeMem
      ⟨_, rfl, (seg₁.of_sameOutside same₂ (by omega)).of_sameOutside same₃ (by omega), nodup₁, set₁⟩
      ⟨_, rfl, seg₂.of_sameOutside same₃ (by omega), nodup₂, set₂⟩
      ⟨_, rfl, Nat.add_assoc a.A a.n a.n ▸ seg₃, nodup₃, set₃⟩ hlen₁ hlen₂ (hlen _ _ _)
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _), rfl⟩
end front
theorem le_tRound (T : ℕ → ℕ → ℕ) {n nd : ℕ} (hnd : nd ≤ n) (V m np Λ f : ℕ)
    (S₁ S₂ S₃ : Finset ℤ) :
    59 + 3 * tPick nd + tNodes T n V m np (treeCalls (Nat.primesLE m) Λ f S₁ S₂ S₃)
      ≤ tRound T n V m np f := by
  have hpick : tPick nd ≤ tPick n := by simp only [tPick]; omega
  have htree := Nat.mul_le_mul_right (tNode T n V m np + 60)
    (ChRound.treeCalls_le_pow (Nat.primesLE m) Λ f S₁ S₂ S₃)
  simp only [tRound, tTree, tNodes] at htree ⊢
  omega
theorem round_spec {p pPick pNodes : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hP : P[p]? = some (roundBody pPick pNodes)) (hPick : PickSpec lim P pPick)
    (hN : NodesSpec lim P pNodes T r) : RoundSpec lim P p T r := by
  intro a f β β' v μ hF hβ hβ' d H
  refine .of_body hP ?_
  have hw := H.ok.space
  have hcells := H.ok.cells
  have hword := H.ok.word
  have hdepth := H.ok.depth
  simp only [gridNeed] at hcells hword hdepth
  push_cast at hword
  have htime := le_tRound T hF.nd_le a.V a.m a.np a.Λ f (splitA a.V β v a.D.toFinset)
    (splitB a.V β β' v false a.D.toFinset) (splitB a.V β β' v true a.D.toFinset)
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (roundSets_ends hF hPick hβ hβ' v (by omega) hw (by omega) (by omega)) ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (roundSets_ends hF hPick hβ hβ' v (by omega) hw (by omega) (by omega)) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨k₁, k₂, k₃, μ₁, out, hmem, rfl⟩
                 ))
                                                      )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       first
       |
         refine
           _root_.Light.Ends.callToThen
             ((hN f _ a.Λ a.cx μ₁ (d + 1)
                 { mem := hmem
                   ctx := (hF.of_sameOutside out).ctx
                   belowCtx := hF.belowCx
                   apartCtx := hF.cntCx
                   V_pos := H.V_pos
                   m_pos := H.m_pos
                   lam := H.lam
                   primes := H.primes
                   ok :=
                     { word := by dsimp only; omega, cells := hcells, space := hw,
                       depth := by dsimp only; omega } })
               _ (by omega))
             ?_ ?_ ?_ ?_
       |
         refine
           _root_.Light.Ends.callToThen
             (hN f _ a.Λ a.cx μ₁ (d + 1)
               { mem := hmem
                 ctx := (hF.of_sameOutside out).ctx
                 belowCtx := hF.belowCx
                 apartCtx := hF.cntCx
                 V_pos := H.V_pos
                 m_pos := H.m_pos
                 lam := H.lam
                 primes := H.primes
                 ok :=
                   { word := by dsimp only; omega, cells := hcells, space := hw,
                     depth := by dsimp only; omega } })
             ?_ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 NodeArgs.calls]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [NodeArgs.calls] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 => omega
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, NodeArgs.calls] <;>
               omega))
       on_goal -1 =>
         (rintro _ μ₂ ⟨rfl, kept⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                             )
  exact ⟨by simp [SplitYes, TreeYes], out.then kept fun b hb => ⟨hb.2, hb.1⟩⟩
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
variable {lim : Limits} {P : Program}
namespace Row
abbrev Beta : ℕ := 0
@[inherit_doc Beta] abbrev Result : ℕ := 0
@[inherit_doc Beta] abbrev NumValues : ℕ := 1
@[inherit_doc Beta] abbrev Val : ℕ := 2
@[inherit_doc Beta] abbrev Table : ℕ := 3
@[inherit_doc Beta] abbrev Digits : ℕ := 4
@[inherit_doc Beta] abbrev Out0 : ℕ := 5
@[inherit_doc Beta] abbrev MaxLen : ℕ := 6
@[inherit_doc Beta] abbrev Levels : ℕ := 7
@[inherit_doc Beta] abbrev Params : ℕ := 8
@[inherit_doc Beta] abbrev Free : ℕ := 9
@[inherit_doc Beta] abbrev Total : ℕ := 10
@[inherit_doc Beta] abbrev Beta' : ℕ := 11
@[inherit_doc Beta] abbrev Ans : ℕ := 12
end Row
open Row in
def rowRound (pRound : ℕ) : Stmt :=
  .call pRound
    [v Beta, v Beta', k 0,
      v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free] Ans ;;
  .set Total (v Total +' v Ans) ;;
  .call pRound
    [v Beta, v Beta', k 1,
      v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free] Ans ;;
  .set Total (v Total +' v Ans)
open Row in
def rowBody (pRound : ℕ) : Stmt :=
  .set Total (k 0) ;;
  .for Beta' (v Digits) (rowRound pRound) ;;
  .set Result (v Total)
namespace Grid
abbrev NumValues : ℕ := 0
@[inherit_doc NumValues] abbrev Result : ℕ := 0
@[inherit_doc NumValues] abbrev Val : ℕ := 1
@[inherit_doc NumValues] abbrev Table : ℕ := 2
@[inherit_doc NumValues] abbrev Digits : ℕ := 3
@[inherit_doc NumValues] abbrev Out0 : ℕ := 4
@[inherit_doc NumValues] abbrev MaxLen : ℕ := 5
@[inherit_doc NumValues] abbrev Levels : ℕ := 6
@[inherit_doc NumValues] abbrev Params : ℕ := 7
@[inherit_doc NumValues] abbrev Free : ℕ := 8
@[inherit_doc NumValues] abbrev Ans : ℕ := 9
@[inherit_doc NumValues] abbrev Beta : ℕ := 10
@[inherit_doc NumValues] abbrev Total : ℕ := 11
end Grid
open Grid in
def gridRound (pRow : ℕ) : Stmt :=
  .call pRow
    [v Beta, v NumValues, v Val, v Table, v Digits, v Out0, v MaxLen, v Levels, v Params, v Free]
    Total ;;
  .ite (k 0 <' v Total) (.set Ans (k 1)) .skip
open Grid in
def gridBody (pRow : ℕ) : Stmt :=
  .set Ans (k 0) ;;
  .for Beta (v Digits) (gridRound pRow) ;;
  .set Result (v Ans)
theorem GridPre.down {r : ℕ → ℕ → Need} {a : FrontArgs} {d f e : ℕ}
    (H : GridPre lim r a f (e + 1) d) :
    2 * (a.Λ : ℤ) + 16 ≤ lim.word ∧ d < lim.depth ∧ GridPre lim r a f e (d + 1) := by
  have hV := H.V_pos
  have hword := H.ok.word
  have hdepth := H.ok.depth
  have hlog := Nat.log_lt_self 2 (x := 2 * a.V) (by omega)
  simp only [gridNeed] at hword hdepth
  push_cast at hword
  have hlam : a.Λ ≤ 2 * a.V := by rw [H.lam, Lam]; omega
  exact ⟨by omega, by omega, H.V_pos, H.m_pos, H.lam, H.primes,
    H.ok.mono (by simp [gridNeed]) (by simp [gridNeed]) (by simp only [gridNeed]; omega)⟩
structure RowSum (S : ℕ → Bool → Prop) (i : ℕ) (acc : ℤ) : Prop where
  nonneg : 0 ≤ acc
  le : acc ≤ 2 * (i : ℤ)
  pos_iff : 0 < acc ↔ ∃ β' < i, ∃ v, S β' v
theorem RowSum.succ {S : ℕ → Bool → Prop} {i : ℕ} {acc : ℤ} (h : RowSum S i acc) :
    RowSum S (i + 1) (acc + flag (S i false) + flag (S i true)) := by
  have hlow := h.nonneg
  have hhigh := h.le
  have hfalse := flag_mem (S i false)
  have htrue := flag_mem (S i true)
  have hsplit : (∃ β' < i + 1, ∃ v, S β' v) ↔ (∃ β' < i, ∃ v, S β' v) ∨ S i false ∨ S i true := by
    rw [Nat.exists_lt_succ_right, Bool.exists_bool]
  refine ⟨by omega, by push_cast; omega, ?_⟩
  rw [hsplit, ← h.pos_iff]
  by_cases hf : S i false <;> by_cases ht : S i true <;>
    simp [flag_of, flag_of_not, hf, ht] <;> omega
section row
variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : FrontArgs} {d f β pRound : ℕ} {μ : ℕ → ℤ}
def RowInv (μ : ℕ → ℤ) (a : FrontArgs) (f β i : ℕ) (σ : State) : Prop :=
  ∃ (acc x : ℤ) (μ' : ℕ → ℤ), RowSum (a.Yes f β) i acc ∧ KeptBut μ μ' a.fr a.A (3 * a.n) ∧
    σ = ⟨frame ((β : ℤ) :: a.vals f ++ [acc, (i : ℤ), x]), μ'⟩
theorem rowRound_ends (hRound : RoundSpec lim P pRound T r) (hmem : FrontMem μ a) (hβ : β < a.Λ)
    (H : GridPre lim r a f 1 d) {i : ℕ} (hi : i < a.Λ) {σ : State} (hσ : RowInv μ a f β i σ) :
    Ends lim P d (rowRound pRound) σ (2 * tRound T a.n a.V a.m a.np f + 36) fun σ' =>
      σ'.loc Row.Beta' = i ∧ RowInv μ a f β (i + 1)
        { σ' with loc := Function.update σ'.loc Row.Beta' ((i : ℤ) + 1) } := by
  obtain ⟨acc, x, μ', hsum, kept, rfl⟩ := hσ
  obtain ⟨hword, hd, H'⟩ := H.down
  have hfalse := flag_mem (a.Yes f β i false)
  have htrue := flag_mem (a.Yes f β i true)
  have hlow := hsum.nonneg
  have hhigh := hsum.le
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hRound a f β i false μ' (hmem.keptBut kept) hβ hi (d + 1) H') _ (by omega)) ?_ ?_ ?_
               ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hRound a f β i false μ' (hmem.keptBut kept) hβ hi (d + 1) H') ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₁
               ⟨rfl, kept₁⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                         )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (acc + flag (a.Yes f β i false))
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                           )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hRound a f β i true μ₁ (hmem.keptBut (kept.trans kept₁)) hβ hi (d + 1) H') _
                 (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hRound a f β i true μ₁ (hmem.keptBut (kept.trans kept₁)) hβ hi (d + 1) H') ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂
               ⟨rfl, kept₂⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                         )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen (acc + flag (a.Yes f β i false) + flag (a.Yes f β i true)) ?_ ?_
             ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                                                                     )
  exact ⟨by simp, _, _, μ₂, hsum.succ, kept.trans (kept₁.trans kept₂),
      by rw [update_frame_setLocal]; rfl⟩
theorem row_spec {p : ℕ} (hP : P[p]? = some (rowBody pRound))
    (hRound : RoundSpec lim P pRound T r) : RowSpec lim P p T r := by
  intro a f β μ hmem hβ d H
  refine .of_body hP ?_
  have hword := H.down.1
  refine Ends.setToThen 0 ?_ (hT := by simp [tRow])
  refine Ends.next _ (Ends.for (RowInv μ a f β) a.Λ (2 * tRound T a.n a.V a.m a.np f + 36)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp [tRow]; ring_nf; omega)
  case start =>
    exact ⟨0, 0, μ, ⟨le_rfl, by simp, by simp⟩, .refl,
      by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl⟩
  case round => exact fun i σ hi _ hσ => rowRound_ends hRound hmem hβ H hi hσ
  case done =>
    rintro _ - ⟨acc, x, μ', hsum, kept, rfl⟩
    exact Ends.setTo acc
      ⟨by simpa using hsum.nonneg, by simpa using hsum.le, by simpa using hsum.pos_iff, kept⟩
      (hT := by simp [tRow]; ring_nf; omega)
  case bound =>
    rintro i _ - - ⟨acc, x, μ', -, -, rfl⟩
    simp
end row
section grid
variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : FrontArgs} {d f pRow : ℕ} {μ : ℕ → ℤ}
abbrev FrontArgs.RowYes (a : FrontArgs) (f β : ℕ) : Prop := ∃ β' < a.Λ, ∃ v, a.Yes f β β' v
def GridInv (μ : ℕ → ℤ) (a : FrontArgs) (f i : ℕ) (σ : State) : Prop :=
  ∃ (x : ℤ) (μ' : ℕ → ℤ), KeptBut μ μ' a.fr a.A (3 * a.n) ∧
    σ = ⟨frame (a.vals f ++ [flag (∃ β < i, a.RowYes f β), (i : ℤ), x]), μ'⟩
theorem gridRound_ends (hRow : RowSpec lim P pRow T r) (hmem : FrontMem μ a)
    (H : GridPre lim r a f 2 d) {i : ℕ} (hi : i < a.Λ) {σ : State} (hσ : GridInv μ a f i σ) :
    Ends lim P d (gridRound pRow) σ (tRow T a.n a.V a.m a.np f a.Λ + 18) fun σ' =>
      σ'.loc Grid.Beta = i ∧ GridInv μ a f (i + 1)
        { σ' with loc := Function.update σ'.loc Grid.Beta ((i : ℤ) + 1) } := by
  obtain ⟨x, μ', kept, rfl⟩ := hσ
  obtain ⟨hword, hd, H'⟩ := H.down
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hRow a f i μ' (hmem.keptBut kept) hi (d + 1) H') _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (hRow a f i μ' (hmem.keptBut kept) hi (d + 1) H') ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro sum μ₁
               ⟨-, -, hpos, kept₁⟩
                   ;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                             )
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_)
  · have hrow := hpos.1 (by simpa using hyes)
    exact Ends.setTo 1 ⟨by simp, sum, μ₁, kept.trans kept₁, by
      rw [update_frame_setLocal, flag_of (Nat.exists_lt_succ_right.2 (Or.inr hrow))]; rfl⟩
  · have hrow : ¬ a.RowYes f i := fun h => hno (by simpa using hpos.2 h)
    refine Ends.skip ⟨by simp, sum, μ₁, kept.trans kept₁, ?_⟩
    rw [update_frame_setLocal, flag_congr (Nat.exists_lt_succ_right.trans (or_iff_left hrow))]
    rfl
theorem grid_spec {p : ℕ} (hP : P[p]? = some (gridBody pRow)) (hRow : RowSpec lim P pRow T r) :
    GridSpec lim P p T r := by
  intro a f μ hmem d H
  refine .of_body hP ?_
  have hword := H.down.1
  refine Ends.setToThen 0 ?_ (hT := by simp [tGrid])
  refine Ends.next _ (Ends.for (GridInv μ a f) a.Λ (tRow T a.n a.V a.m a.np f a.Λ + 18)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp [tGrid]; ring_nf; omega)
  case start =>
    exact ⟨0, μ, .refl, by
      rw [update_frame_setLocal, ← frame_append_zeros _ 1, flag_of_not (by simp)]; rfl⟩
  case round => exact fun i σ hi _ hσ => gridRound_ends hRow hmem H hi hσ
  case done =>
    rintro _ - ⟨x, μ', kept, rfl⟩
    exact Ends.setTo (flag (∃ β < a.Λ, a.RowYes f β)) ⟨rfl, kept⟩
      (hT := by simp [tGrid]; ring_nf; omega)
  case bound =>
    rintro i _ - - ⟨x, μ', -, rfl⟩
    simp
end grid
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
def callsB (n : ℕ) : ℕ := 2 * 3 ^ fuel n
def nodeOwn (n V m np : ℕ) : ℕ := tModulus np n n n V + tNodeArray m n n n V + 3 * tHeavy n V + 360
theorem tNodes_eq (T : ℕ → ℕ → ℕ) (n V m np calls : ℕ) :
    tNodes T n V m np calls = calls * (nodeOwn n V m np + T (8 * m ^ 2) (60 * V + 40)) := by
  unfold tNodes tNode nodeOwn
  ring
def tSetup (n V : ℕ) : ℕ := tParams n V + tPrep n (Lam V) (mPar n V)
def inputsB (V : ℕ) : ℕ := 2 * Lam V ^ 2 + 2
def coreCalls (n V : ℕ) : ℕ := inputsB V * callsB n
def coreOwn (n V : ℕ) : ℕ :=
  tSetup n V + inputsB V * (callsB n * nodeOwn n V (mPar n V) #(Nat.primesLE (mPar n V)) + 3 *
    tPick n + 300) + tTwice n + tZeroThree n + 400
def coreTime (T : ℕ → ℕ → ℕ) (n V : ℕ) : ℕ :=
  coreOwn n V + coreCalls n V * T (8 * mPar n V ^ 2) (60 * V + 40)
def chTime (κ : ℕ) (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := 20 * κ + 40 + coreTime T n (2 * max U (n ^ κ))
def coreCells (n V : ℕ) : ℕ := 6 + mPar n V + mPar n V * mPar n V + 7 * n + n * Lam V + 1
def coreNeed (r : ℕ → ℕ → Need) (n V : ℕ) : Need :=
  ⟨(nodesNeed r n V (mPar n V) (fuel n)).word + 8 * (mPar n V + 1) ^ 2 + 8 * V + 4 * n + 64,
    coreCells n V + (nodesNeed r n V (mPar n V) (fuel n)).cells + mPar n V + n + Lam V + 8,
    (nodesNeed r n V (mPar n V) (fuel n)).depth + Nat.log 2 n + 6⟩
def chNeed (κ : ℕ) (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨(coreNeed r n (2 * max U (n ^ κ))).word + 2 * n ^ κ + 2 * U,
    (coreNeed r n (2 * max U (n ^ κ))).cells,
    (coreNeed r n (2 * max U (n ^ κ))).depth + 1⟩
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
namespace Map
variable (a : Map)
theorem layout : a.cx = a.b ∧ a.pr = a.cx + 6 ∧ a.cnt = a.pr + a.m ∧ a.srt = a.cnt + a.m * a.m ∧
    a.val = a.srt + a.n ∧ a.mul = a.val + a.n ∧ a.bt = a.mul + a.n ∧ a.A = a.bt + a.n * a.Λ ∧
    a.tw = a.A + 3 * a.n ∧ a.one = a.tw + a.n ∧ a.top = a.one + 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end Map
def CoreSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (d n U x b : ℕ) (X : List ℤ) (μ : ℕ → ℤ), X.length = n → AbsLe X U → Seg μ x X → x + n ≤ b →
    1 ≤ n → 1 ≤ U → (coreNeed r n (2 * U)).Ok lim b d →
    Meets lim P p d [n, ((2 * U : ℕ) : ℤ), x, b] μ (coreTime T n (2 * U)) fun res μ' =>
      res = flag (ThreeSum (vecOf n X)) ∧ Kept μ μ' b
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Host
abbrev Num : ℕ := 0
abbrev Bound : ℕ := 1
abbrev Addr : ℕ := 2
abbrev Free : ℕ := 3
abbrev Power : ℕ := 4
end Host
open Host
def hostPow : ℕ → Stmt
  | 0 => .skip
  | κ + 1 => .set Power (v Power *' v Num) ;; hostPow κ
def hostBody (κ pCore : ℕ) : Stmt :=
  .set Power (k 1) ;;
  hostPow κ ;;
  .ite (v Power <' v Bound) (.set Power (v Bound)) .skip ;;
  .call pCore [v Num, v Power +' v Power, v Addr, v Free] Num
theorem hostPow_ends {n B : ℕ} {U a fr : ℤ} {μ : ℕ → ℤ} (hB : (B : ℤ) ≤ lim.word) (κ : ℕ) :
    ∀ j : ℕ, (∀ i ≤ j + κ, n ^ i ≤ B) →
      Ends lim P d (hostPow κ) ⟨frame [n, U, a, fr, (n ^ j : ℕ)], μ⟩ (4 * κ) fun σ' =>
        σ' = ⟨frame [n, U, a, fr, (n ^ (j + κ) : ℕ)], μ⟩ := by
  induction κ with
  | zero => exact fun j _ => Ends.skip rfl
  | succ κ ih =>
    intro j hb
    have hfits : (n : ℤ) ^ j * n ≤ lim.word :=
      le_trans (by exact_mod_cast hb (j + 1) (by omega)) hB
    have hpos : 0 ≤ (n : ℤ) ^ j * n := by positivity
    unfold hostPow
    ((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine _root_.Light.Ends.setToThen (n ^ (j + 1) : ℕ) ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                   _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                   pow_succ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [pow_succ] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, pow_succ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                             )
    rw [show j + (κ + 1) = j + 1 + κ by omega]
    exact (ih (j + 1) fun i hi => hb i (by omega)).mono (by simp; omega) fun _ h => h
theorem hostCall_ends {κ pCore : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hC : CoreSpec lim P pCore T r) {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (chNeed κ r x.N x.U).Ok lim fr d) :
    Ends lim P d (.call pCore [v Num, v Power +' v Power, v Addr, v Free] Num)
      ⟨frame [(x.N : ℤ), x.U, x.a, fr, (max x.U (x.N ^ κ) : ℕ)], μ⟩
      (8 + coreTime T x.N (2 * max x.U (x.N ^ κ))) fun σ' =>
        σ'.loc 0 = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have hword := hok.word
  have hdepth := hok.depth
  simp only [chNeed] at hword hdepth
  have hU := hpre.U_pos
  have hUle : x.U ≤ max x.U (x.N ^ κ) := le_max_left _ _
  have hle : max x.U (x.N ^ κ) ≤ x.N ^ κ + x.U := max_le (by omega) (by omega)
  have hcells : fr + (coreNeed r x.N (2 * max x.U (x.N ^ κ))).cells ≤ lim.space := hok.cells
  generalize max x.U (x.N ^ κ) = U' at *
  have hentries : AbsLe x.X U' := fun y hy => (hpre.le y hy).trans (by exact_mod_cast hUle)
  have hneed : (coreNeed r x.N (2 * U')).Ok lim fr (d + 1) :=
    { word := le_trans (by exact_mod_cast (by omega)) hword
      cells := hcells
      space := hok.space
      depth := by omega }
  exact Ends.callTo (hC (d + 1) x.N U' x.a fr x.X μ hpre.len hentries hpre.seg hpre.below
    hpre.N_pos (hU.trans hUle) hneed) (fun res μ' h => h)
theorem host_spec {κ pCore : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hC : CoreSpec lim P pCore T r) {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (chNeed κ r x.N x.U).Ok lim fr d) :
    Ends lim P d (hostBody κ pCore) ⟨frame [(x.N : ℤ), x.U, x.a, fr], μ⟩ (chTime κ T x.N x.U)
      fun σ' => σ'.loc 0 = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have hword := hok.word
  simp only [chNeed] at hword
  have hpow : 1 ≤ x.N ^ κ := Nat.one_le_pow _ _ hpre.N_pos
  have hB : ((x.N ^ κ : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  have hcall := hostCall_ends hC hpre hok
  unfold hostBody chTime
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         refine
           _root_.Light.Ends.setToThen
             (x.N ^ 0 : ℕ)
             ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                        )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen
               (hostPow_ends hB κ 0 fun i hi => Nat.pow_le_pow_right hpre.N_pos (by omega)) ?_ ?_
         |
           refine
             _root_.Light.Ends.pieceLast
               (hostPow_ends hB κ 0 fun i hi => Nat.pow_le_pow_right hpre.N_pos (by omega)) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ rfl))
                                                         )
  rw [Nat.zero_add]
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · have hc' : x.N ^ κ < x.U := by exact_mod_cast (show ((x.N ^ κ : ℕ) : ℤ) < x.U from hc)
    rw [max_eq_left hc'.le] at hcall ⊢
    (((focus
           (((first
                 | refine _root_.Light.Ends.seqSelf ?_
                 | refine _root_.Light.Ends.skipLast ?_);
               (repeat
                   with_unfolding_none
                     first
                     | refine _root_.Light.Ends.seqAssoc ?_
                     | refine _root_.Light.Ends.skipThen ?_)))
           refine _root_.Light.Ends.setToThen x.U ?_ ?_ ?_
           on_goal -1 =>
             (first
               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                     _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                     _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega)))
           on_goal -1 =>
             ((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
           try (with_unfolding_none refine _root_.Light.Ends.skip ?_)))
                )
    exact hcall.mono (by (((first
                              | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                    _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                  first
                                  | omega
                                  | (ring_nf; omega))
                              | omega
                              |
                                (simp [] <;>
                                    first
                                    | omega
                                    | (ring_nf; omega))))
                                  )) fun _ h => h
  · have hc' : ¬ x.N ^ κ < x.U := fun h => hc (show ((x.N ^ κ : ℕ) : ℤ) < x.U by exact_mod_cast h)
    rw [max_eq_right (not_lt.1 hc')] at hcall ⊢
    exact Ends.next _ (Ends.skip (T := 0) (hcall.mono (by (((first
                                                               | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                                                                     _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                   first
                                                                   | omega
                                                                   | (ring_nf; omega))
                                                               | omega
                                                               |
                                                                 (simp [] <;>
                                                                     first
                                                                     | omega
                                                                     | (ring_nf; omega))))
                                                                   )) fun _ h => h))
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
open ThreeSumApsp
namespace Light.Sec3.ChanHe
open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset
theorem threeSum_iff_trees {n U : ℕ} (hn : 1 ≤ n) (x : Fin n → ℤ) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ThreeSum x ↔
      (∃ β < Lam (2 * U), ∃ β' < Lam (2 * U), ∃ v,
        SplitYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (univ.image x) β β' v) ∨
      TreeYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (twiceSet x) {0} (univ.image x) ∨
      TreeYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (zeroSet x) {0} {0} := by
  rw [instances_correct n U hn x hx]
  unfold instances allNodes SplitYes TreeYes reduction
  simp only [List.mem_map, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨y, ⟨ν, (⟨β, hβ, β', hβ', v, -, hν⟩ | hν | hν), rfl⟩, hc⟩
    · exact Or.inl ⟨β, hβ, β', hβ', v, ν, hν, hc⟩
    · exact Or.inr (Or.inl ⟨ν, hν, hc⟩)
    · exact Or.inr (Or.inr ⟨ν, hν, hc⟩)
  · rintro (⟨β, hβ, β', hβ', v, ν, hν, hc⟩ | ⟨ν, hν, hc⟩ | ⟨ν, hν, hc⟩)
    · exact ⟨_, ⟨ν, Or.inl ⟨β, hβ, β', hβ', v, by cases v <;> simp, hν⟩, rfl⟩, hc⟩
    · exact ⟨_, ⟨ν, Or.inr (Or.inl hν), rfl⟩, hc⟩
    · exact ⟨_, ⟨ν, Or.inr (Or.inr hν), rfl⟩, hc⟩
theorem ChCore.flag_sum_pos (a b c : Prop) : 0 < flag a + flag b + flag c ↔ a ∨ b ∨ c := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;>
    simp [flag_of, flag_of_not, ha, hb, hc]
theorem ChCore.time_le (T : ℕ → ℕ → ℕ) (n V : ℕ) :
    tParams n V + tPrep n (Lam V) (mPar n V)
        + tGrid T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) (Lam V) + tTwice n
        + tTree T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) + tZeroThree n
        + tTree T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) + 126 ≤ coreTime T n V := by
  set m := mPar n V
  set np := #(Nat.primesLE m)
  set Λ := Lam V
  set tt := tTree T n V m np (fuel n) with htt
  have htree : tt = callsB n * nodeOwn n V m np + callsB n * T (8 * m ^ 2) (60 * V + 40) := by
    rw [htt, tTree, tNodes_eq, callsB]
    ring
  have hgrid : tGrid T n V m np (fuel n) Λ
      = Λ ^ 2 * (6 * tPick n + 2 * tt + 320) + 80 * Λ + 40 := by
    simp only [tGrid, tRow, tRound, ← htt]
    ring
  have hcore : coreTime T n V = tParams n V + tPrep n Λ m
      + (Λ ^ 2 * (6 * tPick n + 2 * tt + 320) + 280 * Λ ^ 2 + 2 * tt + 6 * tPick n + 600)
      + tTwice n + tZeroThree n + 400 := by
    simp only [coreTime, coreOwn, coreCalls, inputsB, tSetup]
    rw [htree]
    ring
  have hsq : Λ ≤ Λ ^ 2 := Nat.le_self_pow two_ne_zero Λ
  rw [hgrid, hcore]
  omega
namespace Core
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Src : ℕ := 2
@[inherit_doc Len] abbrev Free : ℕ := 3
@[inherit_doc Len] abbrev Unread : ℕ := 4
@[inherit_doc Len] abbrev Digits : ℕ := 5
@[inherit_doc Len] abbrev PrimeBound : ℕ := 6
@[inherit_doc Len] abbrev Levels : ℕ := 7
@[inherit_doc Len] abbrev Base : ℕ := 8
@[inherit_doc Len] abbrev NumValues : ℕ := 9
@[inherit_doc Len] abbrev Sorted : ℕ := 10
@[inherit_doc Len] abbrev Val : ℕ := 11
@[inherit_doc Len] abbrev Mul : ℕ := 12
@[inherit_doc Len] abbrev Table : ℕ := 13
@[inherit_doc Len] abbrev Sets : ℕ := 14
@[inherit_doc Len] abbrev Doubles : ℕ := 15
@[inherit_doc Len] abbrev Zero : ℕ := 16
@[inherit_doc Len] abbrev Top : ℕ := 17
@[inherit_doc Len] abbrev AnsSplit : ℕ := 18
@[inherit_doc Len] abbrev NumDoubles : ℕ := 19
@[inherit_doc Len] abbrev AnsDoubles : ℕ := 20
@[inherit_doc Len] abbrev NumZero : ℕ := 21
@[inherit_doc Len] abbrev AnsZero : ℕ := 22
end Core
open Core in
def coreSetup (pParams pPrep : ℕ) : Stmt :=
  .call pParams [v Len, v Bound, v Free] Unread ;;
  .set Digits (M (v Free)) ;;
  .set PrimeBound (M (v Free +' k 1)) ;;
  .set Levels (M (v Free +' k 2)) ;;
  .set Base (v Free +' k 3) ;;
  .call pPrep [v Len, v Bound, v Digits, v PrimeBound, v Src, v Base] NumValues
open Core in
def coreAddr : Stmt :=
  .set Sorted (v Base +' k 6 +' v PrimeBound +' v PrimeBound *' v PrimeBound) ;;
  .set Val (v Sorted +' v Len) ;;
  .set Mul (v Val +' v Len) ;;
  .set Table (v Mul +' v Len) ;;
  .set Sets (v Table +' v Len *' v Digits) ;;
  .set Doubles (v Sets +' k 3 *' v Len) ;;
  .set Zero (v Doubles +' v Len) ;;
  .set Top (v Zero +' k 1)
open Core in
def coreSplit (pGrid : ℕ) : Stmt :=
  .call pGrid [v NumValues, v Val, v Table, v Digits, v Sets, v Len, v Levels, v Base, v Top]
    AnsSplit
open Core in
def coreDoubles (pTwice pNodes : ℕ) : Stmt :=
  .call pTwice [v NumValues, v Val, v Mul, v Doubles] NumDoubles ;;
  .call pNodes [v Levels, v Doubles, v NumDoubles, v Zero, k 1, v Val, v NumValues, v Base, v Top]
    AnsDoubles
open Core in
def coreZero (pZero pNodes : ℕ) : Stmt :=
  .call pZero [v NumValues, v Val, v Mul] NumZero ;;
  .call pNodes [v Levels, v Zero, v NumZero, v Zero, k 1, v Zero, k 1, v Base, v Top] AnsZero
open Core in
def coreAnswer : Stmt :=
  .ite (k 0 <' v AnsSplit +' v AnsDoubles +' v AnsZero) (.set Len (k 1)) (.set Len (k 0))
def coreBody (pParams pPrep pGrid pTwice pZero pNodes : ℕ) : Stmt :=
  coreSetup pParams pPrep ;;
  coreAddr ;;
  coreSplit pGrid ;;
  coreDoubles pTwice pNodes ;;
  coreZero pZero pNodes ;;
  coreAnswer
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Core
abbrev setupFrame (a : Map) (V f nd : ℕ) (x b unread : ℤ) : List ℤ :=
  [a.n, V, x, b, unread, a.Λ, a.m, f, a.b, nd]
abbrev addrFrame (a : Map) (V f nd : ℕ) (x b unread : ℤ) : List ℤ :=
  setupFrame a V f nd x b unread ++ [(a.srt : ℤ), a.val, a.mul, a.bt, a.A, a.tw, a.one, a.top]
end Core
open Core
theorem coreAddr_cost : coreAddr.blockCost = 42 := rfl
theorem coreAddr_runs (a : Map) (V f nd : ℕ) (x b unread : ℤ) (μ : ℕ → ℤ)
    (htop : (a.top : ℤ) ≤ lim.word) (hword : (6 : ℤ) ≤ lim.word) :
    coreAddr.Runs lim ⟨frame (setupFrame a V f nd x b unread), μ⟩
      (· = ⟨frame (addrFrame a V f nd x b unread), μ⟩) := by
  have hmap := a.layout
  have : (0 : ℤ) ≤ (a.m : ℤ) * a.m := by positivity
  have : (0 : ℤ) ≤ (a.n : ℤ) * a.Λ := by positivity
  exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                 (try have := _root_.Light.Std.const_le (by assumption))
                 simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, coreAddr] <;> omega))
                                ),
    by simp [coreAddr, update_frame_setLocal, Map.top, Map.one, Map.tw, Map.A, Map.bt, Map.mul,
      Map.val, Map.srt, Map.cnt, Map.pr, add_assoc]⟩
namespace Core
theorem Par.primes_nonempty {a : Map} {V f : ℕ} (h : Par a V f) : (Nat.primesLE a.m).Nonempty := by
  have hcard := wPar_le_card_primesLE a.n V
  rw [← h.primeBound] at hcard
  have hpos : 1 ≤ wPar a.n V :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.succ_pos _)) (Nat.succ_pos _)
  exact Finset.card_pos.1 (by omega)
theorem Par.primeBound_pos {a : Map} {V f : ℕ} (h : Par a V f) : 1 ≤ a.m :=
  (Finset.card_pos.2 h.primes_nonempty).trans_le (Nat.card_primesLE_le a.m)
abbrev Fixed (a : Map) (q : ℕ) : Prop := q < a.A ∨ q = a.one
section
variable {a : Map} {V : ℕ} {D C : List ℤ} {μ ν : ℕ → ℤ}
theorem Arrays.of_sameOn (h : Arrays a V D C μ) (hs : SameOn (Fixed a) μ ν) :
    Arrays a V D C ν := by
  have hmap := a.layout
  have hval := h.val_le
  have hmul := h.mul_le
  have hcard := Nat.card_primesLE_le a.m
  exact
    { val := h.val.of_sameOn hs fun i hi => Or.inl (by omega)
      mul := h.mul.of_sameOn hs fun i hi => Or.inl (by omega)
      ctx := Seg.of_sameOn h.ctx hs fun i hi => Or.inl (by simp at hi; omega)
      primes := ⟨rfl, h.primes.2.of_sameOn hs fun i hi => Or.inl (by
        rw [List.length_map, Finset.length_sort] at hi
        omega)⟩
      zero := fun q hq => (hs _ (Or.inl (by omega))).trans (h.zero q hq)
      one := (hs _ (Or.inr rfl)).trans h.one
      val_le := hval, mul_le := hmul }
theorem Arrays.placed_val (h : Arrays a V D C ν) (hD : D.Nodup) (hb : Bdd V D.toFinset) :
    Placed a V ν a.val D.length D.toFinset := by
  have hmap := a.layout
  have hval := h.val_le
  exact ⟨⟨D, rfl, h.val, hD, rfl⟩, hval, hb, le_rfl, by omega⟩
theorem Arrays.placed_zero (h : Arrays a V D C ν) (hn : 1 ≤ a.n) : Placed a V ν a.one 1 {0} := by
  have hmap := a.layout
  exact ⟨⟨[0], rfl, by simpa [seg_cons] using h.one, by simp, by simp⟩, hn, bdd_zero V, by omega,
    by omega⟩
theorem Arrays.nodesPre {r : ℕ → ℕ → Need} {f s₁ l₁ s₂ l₂ s₃ l₃ : ℕ} {S₁ S₂ S₃ : Finset ℤ}
    (h : Arrays a V D C ν) (hpar : Par a V f) (p₁ : Placed a V ν s₁ l₁ S₁)
    (p₂ : Placed a V ν s₂ l₂ S₂) (p₃ : Placed a V ν s₃ l₃ S₃)
    (hok : (nodesNeed r a.n V a.m f).Ok lim a.top d) :
    NodesPre lim r ν ⟨⟨a.top, a.n, V, a.m, #(Nat.primesLE a.m), a.pr, a.cnt⟩, ⟨s₁, l₁, S₁⟩,
      ⟨s₂, l₂, S₂⟩, ⟨s₃, l₃, S₃⟩⟩ a.Λ a.cx f d := by
  have hmap := a.layout
  have hcard := Nat.card_primesLE_le a.m
  (((obtain ⟨⟩ := _root_.id p₁; obtain ⟨⟩ := _root_.id p₂; obtain ⟨⟩ := _root_.id p₃))
                     )
  exact
    { mem :=
        { envOk := ⟨h.primes, h.zero, by dsimp only; omega, by dsimp only; omega,
            by dsimp only; omega⟩
          set₁ := ⟨p₁.set, p₁.le, p₁.bdd, p₁.below, by dsimp only; omega⟩
          set₂ := ⟨p₂.set, p₂.le, p₂.bdd, p₂.below, by dsimp only; omega⟩
          set₃ := ⟨p₃.set, p₃.le, p₃.bdd, p₃.below, by dsimp only; omega⟩ }
      ctx := h.ctx, belowCtx := by dsimp only; omega, apartCtx := by dsimp only; omega
      V_pos := hpar.bound_pos, m_pos := hpar.primeBound_pos, lam := hpar.digits
      primes := hpar.primes_nonempty, ok := hok }
theorem Arrays.nodes_meets {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {pNodes f s₁ l₁ s₂ l₂ s₃ l₃ : ℕ}
    {S₁ S₂ S₃ : Finset ℤ} (hNodes : NodesSpec lim P pNodes T r) (h : Arrays a V D C ν)
    (hpar : Par a V f) (p₁ : Placed a V ν s₁ l₁ S₁) (p₂ : Placed a V ν s₂ l₂ S₂)
    (p₃ : Placed a V ν s₃ l₃ S₃) (hok : (nodesNeed r a.n V a.m f).Ok lim a.top d) :
    Meets lim P pNodes d [(f : ℤ), s₁, l₁, s₂, l₂, s₃, l₃, a.cx, a.top] ν
      (tNodes T a.n V a.m #(Nat.primesLE a.m) (treeCalls (Nat.primesLE a.m) a.Λ f S₁ S₂ S₃))
      fun res μ' => res = flag (TreeYes a.m a.Λ f V S₁ S₂ S₃) ∧ Kept ν μ' a.top :=
  hNodes f _ a.Λ a.cx ν d (h.nodesPre hpar p₁ p₂ p₃ hok)
end
end Core
namespace Core
section
variable {r : ℕ → ℕ → Need} {a : Map} {V f : ℕ} {X D C : List ℤ} {μ ν : ℕ → ℤ}
theorem Ctx.okNodes (K : Ctx lim r d a V f X D C μ) :
    (nodesNeed r a.n V a.m f).Ok lim a.top (d + 1) :=
  ⟨by have := K.word; omega, K.cells, K.space, by have := K.depth; omega⟩
theorem Ctx.okGrid (K : Ctx lim r d a V f X D C μ) :
    (gridNeed r a.n V a.m f 2).Ok lim a.top (d + 1) :=
  ⟨by have := K.word; simp only [gridNeed]; push_cast; omega, K.cells, K.space,
    by have := K.depth; simp only [gridNeed]; omega⟩
theorem tNodes_le_tTree (T : ℕ → ℕ → ℕ) (n V m np Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    tNodes T n V m np (treeCalls (Nat.primesLE m) Λ f S₁ S₂ S₃) ≤ tTree T n V m np f :=
  Nat.mul_le_mul_right _ (ChRound.treeCalls_le_pow _ _ _ _ _ _)
theorem Ctx.placed_zeroSet (K : Ctx lim r d a V f X D C μ) (h : Arrays a V D C ν) :
    ∃ l : ℕ, flag (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) = (l : ℤ) ∧
      Placed a V ν a.one l (zeroSet (vecOf a.n X)) := by
  have hmap := a.layout
  have hzero := h.placed_zero K.par.len_pos
  by_cases h3 : 3 ≤ #{i | vecOf a.n X i = 0}
  · refine ⟨1, by rw [flag_of (K.values.zeroThree.2 h3)]; rfl, ?_⟩
    rwa [zeroSet, if_pos h3]
  · refine ⟨0, by rw [flag_of_not (mt K.values.zeroThree.1 h3)]; rfl, ?_⟩
    rw [zeroSet, if_neg h3]
    exact ⟨⟨[], rfl, Seg.nil, by simp, by simp⟩, Nat.zero_le _, fun _ hx => absurd hx (by simp),
      by omega, by omega⟩
end
end Core
section parts
variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : Map} {V f : ℕ} {X D C : List ℤ} {μ ν : ℕ → ℤ}
  {x b unread : ℤ}
theorem grid_meets_of_map {pGrid : ℕ} (hGrid : GridSpec lim P pGrid T r)
    (hF : FrontMem μ (a.front V D)) (H : GridPre lim r (a.front V D) f 2 d) :
    Meets lim P pGrid d [(D.length : ℤ), a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.top] μ
      (tGrid T a.n V a.m #(Nat.primesLE a.m) f a.Λ) fun res μ' =>
      res = flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, SplitYes a.m a.Λ f V D.toFinset β β' v) ∧
        KeptBut μ μ' a.top a.A (3 * a.n) :=
  hGrid (a.front V D) f μ hF d H
theorem coreSplit_ends {pGrid : ℕ} (hGrid : GridSpec lim P pGrid T r)
    (K : Ctx lim r d a V f X D C μ)
    (hF : FrontMem μ (a.front V D)) :
    Ends lim P d (coreSplit pGrid) ⟨frame (addrFrame a V f D.length x b unread), μ⟩
      (tGrid T a.n V a.m #(Nat.primesLE a.m) f a.Λ + 11) fun σ' => ∃ μ' : ℕ → ℤ,
        σ' = ⟨frame (addrFrame a V f D.length x b unread ++
          [flag (∃ β < a.Λ, ∃ β' < a.Λ, ∃ v, SplitYes a.m a.Λ f V D.toFinset β β' v)]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have hmap := a.layout
  have hdepth := K.depth
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((grid_meets_of_map hGrid hF
                   ⟨K.par.bound_pos, K.par.primeBound_pos, K.par.digits, K.par.primes_nonempty,
                     K.okGrid⟩)
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (grid_meets_of_map hGrid hF
                 ⟨K.par.bound_pos, K.par.primeBound_pos, K.par.digits, K.par.primes_nonempty,
                   K.okGrid⟩)
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ' ⟨rfl, hkept⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                           )
  exact ⟨μ', rfl, hkept.mono fun q hq => by omega⟩
theorem coreDoubles_ends {pTwice pNodes : ℕ} (hTwice : TwiceSpec lim P pTwice)
    (hNodes : NodesSpec lim P pNodes T r) (K : Ctx lim r d a V f X D C μ)
    (hν : SameOn (Fixed a) μ ν) (ans : ℤ) :
    Ends lim P d (coreDoubles pTwice pNodes)
      ⟨frame (addrFrame a V f D.length x b unread ++ [ans]), ν⟩
      (tTwice a.n + tTree T a.n V a.m #(Nat.primesLE a.m) f + 17) fun σ' =>
        ∃ (len : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (addrFrame a V f D.length x b unread ++ [ans, len,
          flag (TreeYes a.m a.Λ f V (twiceSet (vecOf a.n X)) {0} D.toFinset)]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have hmap := a.layout
  have hspace := K.space
  have hcells := K.cells
  have hval := K.arrays.val_le
  (((obtain ⟨⟩ := _root_.id K))
              )
  have hlenC : C.length = D.length := by rw [K.values.counts, List.length_map]
  have harr := K.arrays.of_sameOn hν
  have htime : tTwice D.length ≤ tTwice a.n := by simp only [tTwice]; omega
  have htree := tNodes_le_tTree T a.n V a.m #(Nat.primesLE a.m) a.Λ f
    (twiceSet (vecOf a.n X)) {0} D.toFinset
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hTwice (d + 1) a.val a.mul a.tw V D C ν
                   { len := hlenC, bounded := fun y hy => K.bddVal y (List.mem_toFinset.2 hy)
                     segVal := harr.val, segMul := harr.mul, apartVal := by omega, apartMul := by omega
                     spaceVal := by omega, spaceMul := by omega, spaceOut := by omega,
                     space_le := hspace
                     word := by omega })
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hTwice (d + 1) a.val a.mul a.tw V D C ν
                 { len := hlenC, bounded := fun y hy => K.bddVal y (List.mem_toFinset.2 hy)
                   segVal := harr.val, segMul := harr.mul, apartVal := by omega, apartMul := by omega
                   spaceVal := by omega, spaceMul := by omega, spaceOut := by omega, space_le := hspace
                   word := by omega })
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ ν₁ ⟨rfl, hdoubles, hsame⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                         )
  have hν₁ : SameOn (Fixed a) μ ν₁ := hν.trans (SameOn.mono hsame fun q hq => by omega)
  have harr₁ := K.arrays.of_sameOn hν₁
  have hplaced : Placed a V ν₁ a.tw (twiceList D C).length (twiceSet (vecOf a.n X)) :=
    ⟨⟨_, rfl, hdoubles, K.values.twice.1, K.values.twice.2⟩,
      (length_twiceList_le D C).trans hval, K.bddDoubles, by omega,
      by have := length_twiceList_le D C; omega⟩
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((harr₁.nodes_meets hNodes K.par hplaced (harr₁.placed_zero K.par.len_pos)
                   (harr₁.placed_val K.values.nodup K.bddVal) K.okNodes)
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (harr₁.nodes_meets hNodes K.par hplaced (harr₁.placed_zero K.par.len_pos)
                 (harr₁.placed_val K.values.nodup K.bddVal) K.okNodes)
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ' ⟨rfl, hkept⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                               )
  exact ⟨_, μ', rfl, hν₁.trans (hkept.mono fun q hq => by omega)⟩
theorem coreZero_ends {pZero pNodes : ℕ} (hZero : ZeroThreeSpec lim P pZero)
    (hNodes : NodesSpec lim P pNodes T r) (K : Ctx lim r d a V f X D C μ)
    (hν : SameOn (Fixed a) μ ν) (ans₁ len ans₂ : ℤ) :
    Ends lim P d (coreZero pZero pNodes)
      ⟨frame (addrFrame a V f D.length x b unread ++ [ans₁, len, ans₂]), ν⟩
      (tZeroThree a.n + tTree T a.n V a.m #(Nat.primesLE a.m) f + 16) fun σ' =>
        ∃ (len' : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (addrFrame a V f D.length x b unread ++ [ans₁, len,
          ans₂, len', flag (TreeYes a.m a.Λ f V (zeroSet (vecOf a.n X)) {0} {0})]), μ'⟩ ∧
          SameOn (Fixed a) μ μ' := by
  have hmap := a.layout
  have hspace := K.space
  have hcells := K.cells
  (((obtain ⟨⟩ := _root_.id K; obtain ⟨⟩ := _root_.id K.arrays))
                       )
  have hlenC : C.length = D.length := by rw [K.values.counts, List.length_map]
  have harr := K.arrays.of_sameOn hν
  have htime : tZeroThree D.length ≤ tZeroThree a.n := by simp only [tZeroThree]; omega
  have htree := tNodes_le_tTree T a.n V a.m #(Nat.primesLE a.m) a.Λ f
    (zeroSet (vecOf a.n X)) {0} {0}
  obtain ⟨l, hflag, hplaced⟩ := K.placed_zeroSet harr
  have hzero := harr.placed_zero (V := V) K.par.len_pos
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hZero (d + 1) a.val a.mul D C ν hlenC harr.val harr.mul (by omega) (by omega) hspace
                   (by omega))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hZero (d + 1) a.val a.mul D C ν hlenC harr.val harr.mul (by omega) (by omega) hspace
                 (by omega))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ ν₁ ⟨rfl, hν₁⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                     )
  rw [hν₁, hflag]
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((harr.nodes_meets hNodes K.par hplaced hzero hzero K.okNodes) _ (by omega)) ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen (harr.nodes_meets hNodes K.par hplaced hzero hzero K.okNodes)
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ' ⟨rfl, hkept⟩; try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                         )
  exact ⟨_, μ', rfl, hν.trans (hkept.mono fun q hq => by omega)⟩
theorem coreAnswer_cost : coreAnswer.blockCost = 10 := rfl
theorem coreAnswer_runs (G₁ G₂ G₃ : Prop) (nd : ℕ) (len₂ len₃ : ℤ) (hword : (6 : ℤ) ≤ lim.word) :
    coreAnswer.Runs lim
      ⟨frame (addrFrame a V f nd x b unread ++ [flag G₁, len₂, flag G₂, len₃, flag G₃]), μ⟩
      fun σ' => σ'.loc 0 = flag (G₁ ∨ G₂ ∨ G₃) ∧ σ'.mem = μ := by
  have h₁ := flag_mem G₁
  have h₂ := flag_mem G₂
  have h₃ := flag_mem G₃
  have hpos := ChCore.flag_sum_pos G₁ G₂ G₃
  by_cases h : G₁ ∨ G₂ ∨ G₃
  · have hsum := hpos.2 h
    exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                   (try have := _root_.Light.Std.const_le (by assumption))
                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, coreAnswer] <;> omega))
                                    ), by simp [coreAnswer, hsum, flag_of h]⟩
  · have hsum := mt hpos.1 h
    exact ⟨by (((  (try have := _root_.Light.Std.space_le (by assumption))
                   (try have := _root_.Light.Std.const_le (by assumption))
                   simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, coreAnswer] <;> omega))
                                    ), by simp [coreAnswer, hsum, flag_of_not h]⟩
end parts
namespace Core
end Core
theorem coreSetup_ends {pParams pPrep : ℕ} (hParams : ParamsSpec lim P pParams)
    (hPrep : PrepSpec lim P pPrep) {r : ℕ → ℕ → Need} {a : Map} {V f x b : ℕ} {X : List ℤ}
    {μ : ℕ → ℤ} (hpar : Par a V f) (hb : a.b = b + 3) (hlen : X.length = a.n) (hX : AbsLe X V)
    (hseg : Seg μ x X) (hxb : x + a.n ≤ b) (hok : (coreNeed r a.n V).Ok lim b d) :
    Ends lim P d (coreSetup pParams pPrep) ⟨frame [a.n, V, x, b], μ⟩
      (tParams a.n V + tPrep a.n a.Λ a.m + 30) fun σ' =>
        ∃ (unread : ℤ) (D C : List ℤ) (μ' : ℕ → ℤ),
          σ' = ⟨frame (setupFrame a V f D.length x b unread), μ'⟩ ∧ Setup a V b X D C μ μ' := by
  have hmap := a.layout
  have hspace := hok.space
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp only [coreNeed, coreCells, ← hpar.primeBound, ← hpar.digits, ← hpar.levels]
    at hcells hword hdepth
  push_cast at hword
  have hsq : (0 : ℤ) ≤ 8 * ((a.m : ℤ) + 1) ^ 2 := by positivity
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hParams (d + 1) a.n V b μ (by omega) hspace
                   (by rw [← hpar.primeBound]; push_cast; omega) (by omega))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hParams (d + 1) a.n V b μ (by omega) hspace
                 (by rw [← hpar.primeBound]; push_cast; omega) (by omega))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro unread μ₁ ⟨hcellsP, hsame₁⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                                                             )
  rw [← hpar.primeBound, ← hpar.digits, ← hpar.levels] at hcellsP
  have hdigits : μ₁ b = a.Λ := by simpa using hcellsP 0 (by simp)
  have hprime : μ₁ (b + 1) = a.m := by simpa using hcellsP 1 (by simp)
  have hlevels : μ₁ (b + 2) = f := by simpa using hcellsP 2 (by simp)
  have haddr₁ : ((b : ℤ) + 1).toNat = b + 1 := by omega
  have haddr₂ : ((b : ℤ) + 2).toNat = b + 2 := by omega
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen a.Λ ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hdigits]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hdigits] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdigits] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                            )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen a.m ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 haddr₁, hprime]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [haddr₁, hprime] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr₁, hprime] <;>
               omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                   )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen f ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 haddr₂, hlevels]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [haddr₂, hlevels] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr₂, hlevels] <;>
               omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                                  )
  ((focus
       (((first
             | refine _root_.Light.Ends.seqSelf ?_
             | refine _root_.Light.Ends.skipLast ?_);
           (repeat
               with_unfolding_none
                 first
                 | refine _root_.Light.Ends.seqAssoc ?_
                 | refine _root_.Light.Ends.skipThen ?_)))
       refine _root_.Light.Ends.setToThen a.b ?_ ?_ ?_
       on_goal -1 =>
         (first
           | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                 _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
                 hb]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [hb] <;>
                 first
                 | omega
                 | (ring_nf; omega)))
       on_goal -1 =>
         ((  (try have := _root_.Light.Std.space_le (by assumption))
             (try have := _root_.Light.Std.const_le (by assumption))
             simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hb] <;> omega))
       try (with_unfolding_none refine _root_.Light.Ends.skip ?_))
                       )
  (((focus
         (((first
               | refine _root_.Light.Ends.seqSelf ?_
               | refine _root_.Light.Ends.skipLast ?_);
             (repeat
                 with_unfolding_none
                   first
                   | refine _root_.Light.Ends.seqAssoc ?_
                   | refine _root_.Light.Ends.skipThen ?_)))
         first
         |
           refine
             _root_.Light.Ends.callToThen
               ((hPrep (d + 1) a V x X μ₁
                   { len := hlen, bounded := hX, below := by omega, bound_pos := hpar.bound_pos
                     digits := hpar.digits
                     ok :=
                       ⟨by simp only [prepNeed]; push_cast; omega, by simp only [prepNeed]; omega,
                         hspace, by simp only [prepNeed]; omega⟩ }
                   (hseg.of_sameOutside hsame₁ (by omega)))
                 _ (by omega))
               ?_ ?_ ?_ ?_
         |
           refine
             _root_.Light.Ends.callToThen
               (hPrep (d + 1) a V x X μ₁
                 { len := hlen, bounded := hX, below := by omega, bound_pos := hpar.bound_pos
                   digits := hpar.digits
                   ok :=
                     ⟨by simp only [prepNeed]; push_cast; omega, by simp only [prepNeed]; omega,
                       hspace, by simp only [prepNeed]; omega⟩ }
                 (hseg.of_sameOutside hsame₁ (by omega)))
               ?_ ?_ ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => omega
         on_goal -1 =>
           ((  (try have := _root_.Light.Std.space_le (by assumption))
               (try have := _root_.Light.Std.const_le (by assumption))
               simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
         on_goal -1 =>
           (rintro _ μ₂ ⟨⟨D, C, rfl, hvalues, hmul, hone, hfront⟩, hkept₂⟩;
             try (with_unfolding_none refine _root_.Light.Ends.skip ?_))))
                                                               )
  exact ⟨unread, D, C, μ₂, rfl, hvalues, hmul, hone, hfront,
    fun q hq => (hkept₂ q (by omega)).trans (hsame₁ q (Or.inl hq))⟩
theorem Core.Setup.ctx {r : ℕ → ℕ → Need} {a : Map} {U b : ℕ} {X D C : List ℤ} {μ μ' : ℕ → ℤ}
    (S : Setup a (2 * U) b X D C μ μ') (hpar : Par a (2 * U) (fuel a.n)) (hb : a.b = b + 3)
    (hx : ∀ i, |vecOf a.n X i| ≤ (U : ℤ)) (hok : (coreNeed r a.n (2 * U)).Ok lim b d) :
    Ctx lim r d a (2 * U) (fuel a.n) X D C μ' := by
  have hmap := a.layout
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp only [coreNeed, coreCells, ← hpar.primeBound, ← hpar.digits] at hcells hword hdepth
  push_cast at hword
  have hsq : (0 : ℤ) ≤ 8 * ((a.m : ℤ) + 1) ^ 2 := by positivity
  exact
    { par := hpar, values := S.values
      arrays :=
        { val := S.front.segVal, mul := S.mul, ctx := S.front.ctx, primes := S.front.primes
          zero := S.front.zero, one := S.one, val_le := S.values.length_le
          mul_le := by rw [S.values.counts, List.length_map]; exact S.values.length_le }
      bddVal := S.front.bdd, bddDoubles := bdd_twiceSet hx, space := hok.space
      cells := by omega, word := by push_cast; omega, depth := by omega }
theorem coreBody_ends {pParams pPrep pGrid pTwice pZero pNodes : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (hParams : ParamsSpec lim P pParams) (hPrep : PrepSpec lim P pPrep)
    (hGrid : GridSpec lim P pGrid T r) (hTwice : TwiceSpec lim P pTwice)
    (hZero : ZeroThreeSpec lim P pZero) (hNodes : NodesSpec lim P pNodes T r) {a : Map}
    {U x b : ℕ} {X : List ℤ} {μ : ℕ → ℤ} (hpar : Par a (2 * U) (fuel a.n)) (hb : a.b = b + 3)
    (hlen : X.length = a.n) (hx : ∀ i, |vecOf a.n X i| ≤ (U : ℤ)) (hX : AbsLe X (2 * U : ℕ))
    (hseg : Seg μ x X) (hxb : x + a.n ≤ b) (hok : (coreNeed r a.n (2 * U)).Ok lim b d) :
    Ends lim P d (coreBody pParams pPrep pGrid pTwice pZero pNodes)
      ⟨frame [a.n, ((2 * U : ℕ) : ℤ), x, b], μ⟩ (coreTime T a.n (2 * U)) fun σ' =>
        σ'.loc 0 = flag (ThreeSum (vecOf a.n X)) ∧ Kept μ σ'.mem b := by
  have hmap := a.layout
  have hfinal := threeSum_iff_trees hpar.len_pos (vecOf a.n X) hx
  have htime := ChCore.time_le T a.n (2 * U)
  rw [← hpar.primeBound, ← hpar.digits] at hfinal htime
  have hcostAddr := coreAddr_cost
  have hcostAnswer := coreAnswer_cost
  refine Ends.mono ?_ htime fun _ h => h
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         |
           refine
             _root_.Light.Ends.pieceThen (coreSetup_ends hParams hPrep hpar hb hlen hX hseg hxb hok) ?_
               ?_
         |
           refine
             _root_.Light.Ends.pieceLast (coreSetup_ends hParams hPrep hpar hb hlen hX hseg hxb hok) ?_
               ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 => rintro _ ⟨unread, D, C, μ₁, rfl, S⟩))
                                    )
  rw [← S.values.values] at hfinal
  have K := S.ctx hpar hb hx hok
  have hcells := K.cells
  (((obtain ⟨⟩ := _root_.id K))
              )
  refine Ends.next _ (Ends.block ((coreAddr_runs a (2 * U) (fuel a.n) D.length x b unread μ₁
    (by omega) (by omega)).mono ?_) le_rfl)
  rintro _ rfl
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (coreSplit_ends hGrid K S.front) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (coreSplit_ends hGrid K S.front) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨μ₂, rfl, hμ₂⟩
                 ))
                                                                   )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (coreDoubles_ends hTwice hNodes K hμ₂ _) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (coreDoubles_ends hTwice hNodes K hμ₂ _) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨len₂, μ₃, rfl, hμ₃⟩
                 ))
                                                                                 )
  (((focus
         (repeat
             with_unfolding_none
               first
               | refine _root_.Light.Ends.seqAssoc ?_
               | refine _root_.Light.Ends.skipThen ?_)
         first
         | refine _root_.Light.Ends.pieceThen (coreZero_ends hZero hNodes K hμ₃ _ _ _) ?_ ?_
         | refine _root_.Light.Ends.pieceLast (coreZero_ends hZero hNodes K hμ₃ _ _ _) ?_ ?_
         on_goal -1 =>
           (first
             | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost,
                   _root_.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil,
                   _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega)))
         on_goal -1 =>
           rintro _
             ⟨len₃, μ₄, rfl, hμ₄⟩
                 ))
                                                                                 )
  refine Ends.block ((coreAnswer_runs _ _ _ _ _ _ (by omega)).mono ?_)
  rintro σ' ⟨hres, hmem⟩
  exact ⟨by rw [hres, propext hfinal], fun q hq => by
    rw [hmem, hμ₄ q (Or.inl (by omega)), S.kept q hq]⟩
theorem core_spec {p pParams pPrep pGrid pTwice pZero pNodes : ℕ} {T : ℕ → ℕ → ℕ}
    {r : ℕ → ℕ → Need} (hP : P[p]? = some (coreBody pParams pPrep pGrid pTwice pZero pNodes))
    (hParams : ParamsSpec lim P pParams) (hPrep : PrepSpec lim P pPrep)
    (hGrid : GridSpec lim P pGrid T r) (hTwice : TwiceSpec lim P pTwice)
    (hZero : ZeroThreeSpec lim P pZero) (hNodes : NodesSpec lim P pNodes T r) :
    CoreSpec lim P p T r := by
  intro d n U x b X μ hlen hXU hseg hxb hn hU hok
  have hx : ∀ i, |vecOf n X i| ≤ (U : ℤ) := fun i => by
    have hi : i.val < X.length := by rw [hlen]; exact i.isLt
    simp only [vecOf, List.getD_eq_getElem _ _ hi]
    exact hXU.getElem hi
  exact ⟨_, hP, coreBody_ends hParams hPrep hGrid hTwice hZero hNodes
    (a := ⟨b + 3, n, Lam (2 * U), mPar n (2 * U)⟩) ⟨hn, by omega, rfl, rfl, rfl⟩ rfl hlen hx
    (fun y hy => (hXU y hy).trans (by push_cast; omega)) hseg hxb hok⟩
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
abbrev boundAt (k n : ℕ) : ℕ := 2 * n ^ k
def ownAt (k n : ℕ) : ℕ := 20 * k + 40 + coreOwn n (boundAt k n)
def callsAt (k n : ℕ) : ℕ := coreCalls n (boundAt k n)
def magAt (k n : ℕ) : ℕ := 60 * boundAt k n + 40
theorem chTime_eq {k n U : ℕ} (hU : U ≤ n ^ k) (Tn : ℕ → ℕ → ℕ) :
    chTime k Tn n U = ownAt k n + callsAt k n * Tn (lenOf k n) (magAt k n) := by
  simp only [chTime, coreTime, lenOf, ownAt, callsAt, magAt, boundAt, max_eq_right hU]
  omega
namespace ClaimF
section own
variable (k : ℕ)
abbrev numPrimes (n : ℕ) : ℕ := #(Nat.primesLE (mPar n (boundAt k n)))
theorem softO_numPrimes : SoftOSqrtPow (numPrimes k) 1 :=
  (softO_mPar k).of_le fun _ _ => Nat.card_primesLE_le _
theorem softO_tEmod : SoftOSqrtPow (fun n => tEmod (boundAt k n)) 0 := by
  unfold tEmod
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
               )
theorem softO_tResid : SoftOSqrtPow (fun n => tResid n (boundAt k n)) 2 := by
  unfold tResid
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tEmod k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_tEmod k
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_tEmod k
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tEmod k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                            )
theorem softO_tTally : SoftOSqrtPow (fun n => tTally n) 2 := by
  unfold tTally
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
               )
theorem softO_tColl : SoftOSqrtPow (fun n => tColl n (boundAt k n)) 2 := by
  unfold tColl
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tResid k
                   | apply softO_tTally
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_tResid k
                             | apply softO_tTally
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_tResid k
                         | apply softO_tTally
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tResid k
                   | apply softO_tTally
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                           )
theorem softO_tHeavy : SoftOSqrtPow (fun n => tHeavy n (boundAt k n)) 2 := by
  unfold tHeavy
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tResid k
                   | apply softO_tTally
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_tResid k
                             | apply softO_tTally
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_tResid k
                         | apply softO_tTally
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tResid k
                   | apply softO_tTally
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                           )
theorem softO_tSearch : SoftOSqrtPow (fun n => tSearch (numPrimes k n) n n n (boundAt k n)) 3 := by
  unfold tSearch
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_numPrimes k
                   | apply softO_tColl k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_numPrimes k
                             | apply softO_tColl k
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_numPrimes k
                         | apply softO_tColl k
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_numPrimes k
                   | apply softO_tColl k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                               )
theorem softO_tModulus :
    SoftOSqrtPow (fun n => tModulus (numPrimes k n) n n n (boundAt k n)) 3 := by
  unfold tModulus
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tSearch k
                   | apply softO_tColl k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_tSearch k
                             | apply softO_tColl k
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_tSearch k
                         | apply softO_tColl k
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tSearch k
                   | apply softO_tColl k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                             )
theorem softO_tNodeArray :
    SoftOSqrtPow (fun n => tNodeArray (mPar n (boundAt k n)) n n n (boundAt k n)) 2 := by
  unfold tNodeArray
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_mPar k
                   | apply softO_tResid k
                   | apply softO_tTally
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_mPar k
                             | apply softO_tResid k
                             | apply softO_tTally
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_mPar k
                         | apply softO_tResid k
                         | apply softO_tTally
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_mPar k
                   | apply softO_tResid k
                   | apply softO_tTally
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                                         )
theorem softO_nodeOwn :
    SoftOSqrtPow (fun n => nodeOwn n (boundAt k n) (mPar n (boundAt k n)) (numPrimes k n)) 3 := by
  unfold nodeOwn
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tModulus k
                   | apply softO_tNodeArray k
                   | apply softO_tHeavy k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_tModulus k
                             | apply softO_tNodeArray k
                             | apply softO_tHeavy k
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_tModulus k
                         | apply softO_tNodeArray k
                         | apply softO_tHeavy k
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tModulus k
                   | apply softO_tNodeArray k
                   | apply softO_tHeavy k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                                                   )
theorem softO_callsB : SoftOSqrtPow (fun n => callsB n) 0 := by
  unfold callsB
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply Scale.SoftO.of_forall_le three_pow_fuel_le
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply Scale.SoftO.of_forall_le three_pow_fuel_le
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply Scale.SoftO.of_forall_le three_pow_fuel_le
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply Scale.SoftO.of_forall_le three_pow_fuel_le
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                                         )
theorem softO_tSetup : SoftOSqrtPow (fun n => tSetup n (boundAt k n)) 2 := by
  unfold tSetup tParams tPrep tLog2 tPrimes tSort tDistinct tBits
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_wPar k
                   | apply softO_mPar k
                   | apply softO_Lam k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_wPar k
                             | apply softO_mPar k
                             | apply softO_Lam k
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_wPar k
                         | apply softO_mPar k
                         | apply softO_Lam k
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_wPar k
                   | apply softO_mPar k
                   | apply softO_Lam k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                                      )
theorem softO_ownAt : SoftOSqrtPow (ownAt k) 3 := by
  unfold ownAt coreOwn inputsB tPick tTwice tZeroThree
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tSetup k
                   | apply softO_nodeOwn k
                   | apply softO_callsB
                   | apply softO_Lam k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_tSetup k
                             | apply softO_nodeOwn k
                             | apply softO_callsB
                             | apply softO_Lam k
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_tSetup k
                         | apply softO_nodeOwn k
                         | apply softO_callsB
                         | apply softO_Lam k
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_tSetup k
                   | apply softO_nodeOwn k
                   | apply softO_callsB
                   | apply softO_Lam k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                                                         )
theorem softO_callsAt : SoftOSqrtPow (callsAt k) 0 := by
  unfold callsAt coreCalls inputsB
  (((first
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_callsB
                   | apply softO_Lam k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div)
           ·
             first
             | decide
             | exact _root_.isEmptyElim)
       | ( fail_if_success
             (fail_if_success
                 ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                             | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                             | apply softO_callsB
                             | apply softO_Lam k
                             | apply _root_.ThreeSumApsp.Scale.SoftO.add
                             | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                             | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                             | apply _root_.ThreeSumApsp.Scale.SoftO.max
                             | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                             | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                       done)))
           repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
           all_goals
             try (
                 apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                         | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                         | apply softO_callsB
                         | apply softO_Lam k
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 · decide))
       | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
           ·
             (repeat'
                 with_reducible
                   first
                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.self
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natSqrt
                   | apply _root_.ThreeSumApsp.SoftOSqrtPow.natLog_comp
                   | apply softO_callsB
                   | apply softO_Lam k
                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                   | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                                        )
end own
end ClaimF
theorem polyNeed_chNeed (κ : ℕ) (r : ℕ → ℕ → Need) (hr : PolyNeed r) : PolyNeed (chNeed κ r) := by
  have hfuel : ∀ n, fuel n ≤ 3 * (n + 2) := fun n => by
    have h1 : height n ≤ Nat.log 2 n + 2 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    have h2 : Nat.log 2 n ≤ n := Nat.log_le_self _ _
    unfold fuel
    omega
  have hm : PolyBounded fun n U => mPar n (2 * max U (n ^ κ)) := by
    unfold mPar wPar Lam
    (((first
         | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
             ·
               (repeat'
                   with_reducible
                     first
                     | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                     | apply _root_.Light.PolyBounded.fst
                     | apply _root_.Light.PolyBounded.snd
                     | apply _root_.ThreeSumApsp.Scale.SoftO.log
                     | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                     | apply _root_.ThreeSumApsp.Scale.SoftO.add
                     | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                     | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                     | apply _root_.ThreeSumApsp.Scale.SoftO.max
                     | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                     | apply _root_.ThreeSumApsp.Scale.SoftO.div)
             ·
               first
               | decide
               | exact _root_.isEmptyElim)
         | ( fail_if_success
               (fail_if_success
                   ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                     on_goal 1 =>
                       ((repeat'
                             with_reducible
                               first
                               | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                               | apply _root_.Light.PolyBounded.fst
                               | apply _root_.Light.PolyBounded.snd
                               | apply _root_.ThreeSumApsp.Scale.SoftO.log
                               | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                               | apply _root_.ThreeSumApsp.Scale.SoftO.add
                               | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                               | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                               | apply _root_.ThreeSumApsp.Scale.SoftO.max
                               | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                               | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                         done)))
             repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
             all_goals
               try (
                   apply _root_.ThreeSumApsp.Scale.SoftO.mono
                   ·
                     (repeat'
                         with_reducible
                           first
                           | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                           | apply _root_.Light.PolyBounded.fst
                           | apply _root_.Light.PolyBounded.snd
                           | apply _root_.ThreeSumApsp.Scale.SoftO.log
                           | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                           | apply _root_.ThreeSumApsp.Scale.SoftO.add
                           | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                           | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                           | apply _root_.ThreeSumApsp.Scale.SoftO.max
                           | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                           | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                   · decide))
         | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
             ·
               (repeat'
                   with_reducible
                     first
                     | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                     | apply _root_.Light.PolyBounded.fst
                     | apply _root_.Light.PolyBounded.snd
                     | apply _root_.ThreeSumApsp.Scale.SoftO.log
                     | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                     | apply _root_.ThreeSumApsp.Scale.SoftO.add
                     | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                     | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                     | apply _root_.ThreeSumApsp.Scale.SoftO.max
                     | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                     | apply _root_.ThreeSumApsp.Scale.SoftO.div))))
                 )
  unfold chNeed coreNeed coreCells nodesNeed modulusNeed wordNeed Lam
  (((refine _root_.Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
         ((first
             | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.Light.PolyBounded.fst
                         | apply _root_.Light.PolyBounded.snd
                         | apply _root_.ThreeSumApsp.Scale.SoftO.log
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                         | apply hr.word
                         | apply hr.cells
                         | apply hr.depth
                         | apply hm
                         | apply Scale.SoftO.of_forall_le hfuel
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                 ·
                   first
                   | decide
                   | exact _root_.isEmptyElim)
             | ( fail_if_success
                   (fail_if_success
                       ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                         on_goal 1 =>
                           ((repeat'
                                 with_reducible
                                   first
                                   | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                                   | apply _root_.Light.PolyBounded.fst
                                   | apply _root_.Light.PolyBounded.snd
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.log
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                                   | apply hr.word
                                   | apply hr.cells
                                   | apply hr.depth
                                   | apply hm
                                   | apply Scale.SoftO.of_forall_le hfuel
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.add
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.max
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                                   | apply _root_.ThreeSumApsp.Scale.SoftO.div);
                             done)))
                 repeat' with_reducible apply _root_.ThreeSumApsp.Scale.SoftO.add_le
                 all_goals
                   try (
                       apply _root_.ThreeSumApsp.Scale.SoftO.mono
                       ·
                         (repeat'
                             with_reducible
                               first
                               | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                               | apply _root_.Light.PolyBounded.fst
                               | apply _root_.Light.PolyBounded.snd
                               | apply _root_.ThreeSumApsp.Scale.SoftO.log
                               | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                               | apply hr.word
                               | apply hr.cells
                               | apply hr.depth
                               | apply hm
                               | apply Scale.SoftO.of_forall_le hfuel
                               | apply _root_.ThreeSumApsp.Scale.SoftO.add
                               | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                               | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                               | apply _root_.ThreeSumApsp.Scale.SoftO.max
                               | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                               | apply _root_.ThreeSumApsp.Scale.SoftO.div)
                       · decide))
             | ( apply _root_.ThreeSumApsp.Scale.SoftO.mono
                 ·
                   (repeat'
                       with_reducible
                         first
                         | exact _root_.ThreeSumApsp.Scale.SoftO.const _
                         | apply _root_.Light.PolyBounded.fst
                         | apply _root_.Light.PolyBounded.snd
                         | apply _root_.ThreeSumApsp.Scale.SoftO.log
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sqrt
                         | apply hr.word
                         | apply hr.cells
                         | apply hr.depth
                         | apply hm
                         | apply Scale.SoftO.of_forall_le hfuel
                         | apply _root_.ThreeSumApsp.Scale.SoftO.add
                         | apply _root_.ThreeSumApsp.Scale.SoftO.mul
                         | apply _root_.ThreeSumApsp.Scale.SoftO.pow
                         | apply _root_.ThreeSumApsp.Scale.SoftO.max
                         | apply _root_.ThreeSumApsp.Scale.SoftO.sub
                         | apply _root_.ThreeSumApsp.Scale.SoftO.div))))))
                                                                            )
theorem claim_CH20_Theorem_5_1_of_host (h : ∀ κ : ℕ, IsHost c3Task s3Task (chTime κ) (chNeed κ)) :
    Claim.CH20_Theorem_5_1 lightModel := by
  intro κ _
  have hκ : κ ≤ ⌈κ⌉₊ := Nat.le_ceil κ
  generalize ⌈κ⌉₊ = k at hκ
  refine ⟨fun n => ownAt k n, fun n => callsAt k n, fun n => magAt k n, lenOf k, 160, k,
    (ClaimF.softO_ownAt k).isPowPolylog (by norm_num),
    (ClaimF.softO_callsAt k).isPowPolylog (by norm_num), isPowPolylog_lenOf k,
    fun n hn => ⟨one_le_lenOf k n, ?_, ?_⟩, ?_⟩
  · exact Nat.one_le_cast.2 (by unfold magAt boundAt; omega)
  · have hpow : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
    have hmag : magAt k n ≤ 160 * n ^ k := by unfold magAt boundAt; omega
    rw [Real.rpow_natCast]
    change (magAt k n : ℝ) ≤ _
    exact_mod_cast hmag
  rintro T ⟨P, p, Tn, r, hr, hsol, hT⟩
  obtain ⟨R, p', hsol'⟩ := (h k).1 P p Tn r hsol
  refine ⟨timeUpTo (chTime k Tn), hsol'.solvedIn ((h k).2 r hr), fun n hn =>
    timeUpTo_le fun U hU => ?_⟩
  have hUk : U ≤ n ^ k := by
    have hle : (U : ℝ) ≤ (n : ℝ) ^ (k : ℝ) := (hU.trans_eq (max_eq_left (by positivity))).trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hκ)
    rw [Real.rpow_natCast] at hle
    exact_mod_cast hle
  rw [chTime_eq hUk]
  push_cast
  gcongr
  exact hT _ _ _ (one_le_lenOf k n) (by unfold magAt boundAt; omega) le_rfl
end Light.Sec3.ChanHe
end
end
section
@[expose] public section
namespace Light.Sec3.ChanHe
open ThreeSumApsp
namespace Proc
abbrev emod : ℕ := 0
@[inherit_doc emod] abbrev log2 : ℕ := 1
@[inherit_doc emod] abbrev clog2 : ℕ := 2
@[inherit_doc emod] abbrev sqrt : ℕ := 3
@[inherit_doc emod] abbrev sieve : ℕ := 4
@[inherit_doc emod] abbrev half : ℕ := 5
@[inherit_doc emod] abbrev merge : ℕ := 6
@[inherit_doc emod] abbrev copy : ℕ := 7
@[inherit_doc emod] abbrev fill : ℕ := 8
@[inherit_doc emod] abbrev sort : ℕ := 9
@[inherit_doc emod] abbrev resid : ℕ := 10
@[inherit_doc emod] abbrev tally : ℕ := 11
@[inherit_doc emod] abbrev coll : ℕ := 12
@[inherit_doc emod] abbrev heavy : ℕ := 13
@[inherit_doc emod] abbrev search : ℕ := 14
@[inherit_doc emod] abbrev modulus : ℕ := 15
@[inherit_doc emod] abbrev nodeArray : ℕ := 16
@[inherit_doc emod] abbrev nodes : ℕ := 17
@[inherit_doc emod] abbrev distinct : ℕ := 18
@[inherit_doc emod] abbrev twice : ℕ := 19
@[inherit_doc emod] abbrev zeroThree : ℕ := 20
@[inherit_doc emod] abbrev bits : ℕ := 21
@[inherit_doc emod] abbrev pick : ℕ := 22
@[inherit_doc emod] abbrev round : ℕ := 23
@[inherit_doc emod] abbrev row : ℕ := 24
@[inherit_doc emod] abbrev grid : ℕ := 25
@[inherit_doc emod] abbrev params : ℕ := 26
@[inherit_doc emod] abbrev prep : ℕ := 27
@[inherit_doc emod] abbrev core : ℕ := 28
@[inherit_doc emod] abbrev host : ℕ := 29
end Proc
def chBodies (κ pC3 o : ℕ) : Program :=
  [emodBody,
    log2Body,
    clog2Body,
    sqrtBody,
    sieveBody,
    halfBody,
    mergeBody,
    copyBody,
    fillBody,
    sortBody (o + Proc.sort) (o + Proc.half) (o + Proc.merge) (o + Proc.copy),
    residBody (o + Proc.emod),
    tallyBody,
    collBody (o + Proc.resid) (o + Proc.tally),
    heavyBody (o + Proc.resid) (o + Proc.tally),
    searchBody (o + Proc.coll),
    modulusBody (o + Proc.search) (o + Proc.coll),
    nodeArrayBody (o + Proc.resid) (o + Proc.tally),
    nodesBody (o + Proc.nodes) (o + Proc.modulus) (o + Proc.nodeArray) pC3 (o + Proc.heavy),
    distinctBody,
    twiceBody,
    zeroThreeBody,
    bitsBody,
    pickBody,
    roundBody (o + Proc.pick) (o + Proc.nodes),
    rowBody (o + Proc.round),
    gridBody (o + Proc.row),
    paramsBody (o + Proc.log2) (o + Proc.clog2) (o + Proc.sqrt),
    prepBody (o + Proc.sieve) (o + Proc.fill) (o + Proc.copy) (o + Proc.sort) (o + Proc.distinct)
      (o + Proc.bits),
    coreBody (o + Proc.params) (o + Proc.prep) (o + Proc.grid) (o + Proc.twice) (o + Proc.zeroThree)
      (o + Proc.nodes),
    hostBody κ (o + Proc.core)]
theorem isHost_s3 (κ : ℕ) : IsHost c3Task s3Task (chTime κ) (chNeed κ) := by
  refine ⟨fun P₀ pC3 T r hsol => ⟨chBodies κ pC3 P₀.length, P₀.length + Proc.host,
    hostBody κ (P₀.length + Proc.core), ?_,
    fun R lim d x μ fr hpre hok => ?_⟩, fun r hr => polyNeed_chNeed κ r hr⟩
  · have := getElem?_append_append (P₀ := P₀) (B := chBodies κ pC3 P₀.length) [] (i := Proc.host)
      rfl
    rwa [List.append_nil] at this
  rw [List.append_assoc]
  have L : ∀ {i : ℕ} {body : Stmt}, (chBodies κ pC3 P₀.length)[i]? = some body →
      (P₀ ++ (chBodies κ pC3 P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  have hEmod : EmodSpec lim (P₀ ++ (chBodies κ pC3 P₀.length ++ R)) P₀.length :=
    emodSpec_of (L (i := Proc.emod) rfl)
  have hLog2 := log2Spec_of (lim := lim) (L (i := Proc.log2) rfl)
  have hClog2 := clog2Spec_of (lim := lim) (L (i := Proc.clog2) rfl)
  have hPrimes := primesSpec_of (lim := lim) (L (i := Proc.sieve) rfl)
  have hSort :=
    sortSpec_of (lim := lim) ⟨L (i := Proc.sort) rfl, L (i := Proc.half) rfl,
      L (i := Proc.merge) rfl, L (i := Proc.copy) rfl⟩
  have hResid := resid_spec (L (i := Proc.resid) rfl) hEmod
  have hTally := tally_spec (lim := lim) (L (i := Proc.tally) rfl)
  have hColl := coll_spec (L (i := Proc.coll) rfl) hResid hTally
  have hHeavy := heavy_spec (L (i := Proc.heavy) rfl) hResid hTally
  have hModulus := modulusSpec_of (L (i := Proc.modulus) rfl) (L (i := Proc.search) rfl) hColl
  have hArray := nodeArray_spec (L (i := Proc.nodeArray) rfl) hResid hTally
  have hNodes := nodes_spec ⟨hsol, L (i := Proc.nodes) rfl, hModulus, hArray, hHeavy⟩
  have hDistinct := distinct_spec (lim := lim) (L (i := Proc.distinct) rfl)
  have hTwice := twice_spec (lim := lim) (L (i := Proc.twice) rfl)
  have hZero := zeroThree_spec (lim := lim) (L (i := Proc.zeroThree) rfl)
  have hBits := bits_spec (lim := lim) (L (i := Proc.bits) rfl)
  have hPick := pick_spec (lim := lim) (L (i := Proc.pick) rfl)
  have hRound := round_spec (L (i := Proc.round) rfl) hPick hNodes
  have hRow := row_spec (L (i := Proc.row) rfl) hRound
  have hGrid := grid_spec (L (i := Proc.grid) rfl) hRow
  have hParams := params_spec (L (i := Proc.params) rfl) hLog2 hClog2 (L (i := Proc.sqrt) rfl)
  have hPrep :=
    prep_spec (L (i := Proc.prep) rfl) hPrimes (L (i := Proc.fill) rfl) (L (i := Proc.copy) rfl)
      hSort hDistinct hBits
  have hCore := core_spec (L (i := Proc.core) rfl) hParams hPrep hGrid hTwice hZero hNodes
  exact host_spec hCore hpre hok
theorem claim_CH20_Theorem_5_1 : Claim.CH20_Theorem_5_1 lightModel :=
  claim_CH20_Theorem_5_1_of_host isHost_s3
end Light.Sec3.ChanHe
end
end
theorem solution : ThreeSumApsp.Claim.CH20_Theorem_5_1 Light.lightModel :=
  Light.Sec3.ChanHe.claim_CH20_Theorem_5_1
#print axioms solution
