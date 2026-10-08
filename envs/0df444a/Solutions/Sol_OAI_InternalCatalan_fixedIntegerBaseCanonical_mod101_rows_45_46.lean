-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_45_46
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T22:12:24.073984+00:00
-- url     : https://prove2.me/submissions/6945b8c4-2e68-4811-b3a3-df71008b9f2a

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAICatalanIrrationality
import Definitions.Def_OAICatalanChebyshevData
import Theorems.Thm_OAI_InternalCatalan_fixed_chebyshevT_typed_23
import Theorems.Thm_OAI_InternalCatalan_fixed_chebyshevT_typed_24
import Theorems.Thm_OAI_InternalCatalan_fixed_chebyshevU_typed_22
import Theorems.Thm_OAI_InternalCatalan_fixed_chebyshevU_typed_23

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevTData
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan


























def fixedChebyshevTData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (25 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-2600 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (80080 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-1144000 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (9152000 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-45260800 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (146227200 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-317521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (466944000 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-458752000 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (288358400 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-104857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (16777216 : ℤ)

def fixedChebyshevTData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (338 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-18928 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (416416 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-4759040 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (32361472 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-141213696 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (412778496 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-825556992 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (1133117440 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-1049624576 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (627048448 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-218103808 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (33554432 : ℤ)

def fixedChebyshevTData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-27 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (3276 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-117936 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (1976832 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-18670080 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (109983744 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-428654592 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (1143078912 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-2118057984 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (2724986880 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-2387607552 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (1358954496 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-452984832 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (67108864 : ℤ)

def fixedChebyshevTData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-392 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (25480 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-652288 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (8712704 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-69701632 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (361181184 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-1270087680 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (3111714816 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-5369233408 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (6499598336 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-5402263552 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (2936012800 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-939524096 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (134217728 : ℤ)

def fixedChebyshevTData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (29 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-4060 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (168896 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-3281408 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (36095488 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-249387008 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (1151016960 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-3683254272 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (8341487616 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-13463453696 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (15386804224 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-12163481600 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (6325010432 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-1946157056 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (268435456 : ℤ)

def fixedChebyshevTData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (450 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-33600 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (990080 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-15275520 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (141892608 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-859955200 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (3572121600 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-10478223360 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (22052208640 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-33426505728 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (36175872000 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-27262976000 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (13589544960 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-4026531840 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (536870912 : ℤ)

def fixedChebyshevTData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-31 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (4960 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-236096 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (5261568 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-66646528 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (533172224 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-2870927360 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (10827497472 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-29297934336 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (57567870976 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-82239815680 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (84515225600 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-60850962432 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (29125246976 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-8321499136 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (1073741824 : ℤ)

def fixedChebyshevTData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (43520 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-1462272 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (25798656 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-275185664 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (1926299648 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-9313976320 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-80648077312 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (148562247680 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-200655503360 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (196293427200 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-135291469824 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (62277025792 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (2147483648 : ℤ)

def fixedChebyshevTData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (33 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-5984 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (323136 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-8186112 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (118243840 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-1083543552 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (6723526656 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-29455450112 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (93564370944 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-218864025600 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (379364311040 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-485826232320 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (453437816832 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-299708186624 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (132875550720 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-35433480192 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (4294967296 : ℤ)

def fixedChebyshevTData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (578 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-55488 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (2108544 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-42170880 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (511673344 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-4093386752 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (22761029632 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-91044118528 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (267776819200 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-586290298880 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (959384125440 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-1167945891840 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (1042167103488 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-661693399040 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (282930970624 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-73014444032 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (8589934592 : ℤ)

def fixedChebyshevTData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-35 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (7140 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-434112 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (12403200 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-202585600 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (2106890240 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-14910300160 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (74977509376 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-275652608000 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (754417664000 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-1551944908800 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (2404594483200 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-2789329600512 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (2384042393600 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-1456262348800 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (601295421440 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-150323855360 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (17179869184 : ℤ)

def fixedChebyshevTData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-648 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (69768 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-2976768 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (66977280 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-916844544 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (8307167232 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-52581629952 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (240999137280 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-819082035200 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (2095125626880 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-4063273943040 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (5977134858240 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-6620826304512 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (5429778186240 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-3195455668224 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (1275605286912 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-309237645312 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (34359738368 : ℤ)

def fixedChebyshevTData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (37 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-8436 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (573648 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-18356736 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (336540160 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-3940579328 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (31524634624 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-180140769280 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (757650882560 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-2392581734400 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (5742196162560 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-10531142369280 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (14743599316992 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-15625695002624 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (12315818721280 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-6992206757888 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (2701534429184 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-635655159808 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (68719476736 : ℤ)

def fixedChebyshevTData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (722 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-86640 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (4124064 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-103690752 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (1589924864 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-16188325888 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (115630899200 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-601280675840 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (2334383800320 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-6880289095680 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (15547666268160 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-27039419596800 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (36108024938496 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-36681168191488 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (27827093110784 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-15260018802688 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (5712306503680 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1305670057984 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (137438953472 : ℤ)

def fixedChebyshevTData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-39 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (9880 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-746928 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (26604864 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-543921664 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (7120429056 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-63901286400 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (411402567680 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-1960212234240 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (7061349335040 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-19502774353920 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (41626474905600 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-68822438510592 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (87841744879616 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-85678155104256 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (62646392979456 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-33221572034560 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (12060268167168 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2680059592704 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (274877906944 : ℤ)

def fixedChebyshevTData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-800 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (106400 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-5617920 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (156900480 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-2677768192 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (30429184000 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-243433472000 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (1424085811200 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-6254808268800 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (21002987765760 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-54553214976000 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (110292369408000 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-173752901959680 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (212364657950720 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-199183403319296 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (140552804761600 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-72155450572800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (25426206392320 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-5497558138880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (549755813888 : ℤ)

def fixedChebyshevTData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (41 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-11480 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (959728 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-37840704 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (857722624 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-12475965440 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (124759654400 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-898269511680 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (4808383856640 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-19570965872640 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (61508749885440 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-150732904857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (289407177326592 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-435347548798976 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (510407471005696 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-461013199618048 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (314327181557760 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-156371169312768 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (53532472377344 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-11269994184704 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (1099511627776 : ℤ)

def fixedChebyshevTData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (882 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-129360 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (7537376 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-232581888 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (4393213440 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-55381114880 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (492952780800 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-3220624834560 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (15871575982080 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-60144919511040 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (177570714746880 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-411758179123200 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (752567256612864 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-1083059755548672 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (1219998345330688 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-1062579203997696 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (700809813688320 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-338168545017856 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (112562502893568 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-23089744183296 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (2199023255552 : ℤ)



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.CentralCoefficients
namespace OAI

namespace InternalCatalan

section

open scoped BigOperators



@[simp] theorem centralCoeff_zero : centralCoeff 0 = 1 := by
  norm_num [centralCoeff]

@[simp] theorem centralCoeffKernel_zero : centralCoeffKernel 0 = 1 := by
  norm_num [centralCoeffKernel]





@[simp] theorem momentScalar_zero : momentScalar 0 = 2 := by
  norm_num [momentScalar]





@[simp] theorem boundaryMinus_zero : boundaryMinus 0 = 0 := rfl
@[simp] theorem boundaryMinus_one : boundaryMinus 1 = 2 := rfl
@[simp] theorem boundaryPlus_zero : boundaryPlus 0 = 0 := rfl
@[simp] theorem boundaryPlus_one : boundaryPlus 1 = 0 := rfl








@[simp] theorem momentRat_zero_right (i : ℕ) : momentRat i 0 = boundaryMinus i := by
  simp [momentRat]

@[simp] theorem momentRat_zero_left (j : ℕ) : momentRat 0 j = boundaryPlus j := by
  cases j with
  | zero => simp [momentRat]
  | succ j => simp [momentRat]






@[simp] theorem harmonicRat_zero (d : ℕ) : harmonicRat d 0 = 0 := by
  simp [harmonicRat]



@[simp] theorem zetaRat_diagonal (i : ℕ) : zetaRat i i = -harmonicRat 2 i := by
  simp [zetaRat]




end













end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealColumnDeterminant
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial




@[simp] theorem reversedRow_zero (C : ℕ) : reversedRow C 0 = 0 := by
  simp [reversedRow]

theorem reversedRow_coeff (C : ℕ) (F : ℤ[X]) (i : ℕ) :
    (reversedRow C F).coeff i = if i < C then F.coeff (C - 1 - i) else 0 := by
  classical
  unfold reversedRow
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hi : i < C
  · rw [if_pos hi, Finset.sum_eq_single (C - 1 - i)]
    · rw [if_pos (by omega : i = C - 1 - (C - 1 - i))]
    · intro u hu hne
      have hu' := Finset.mem_range.mp hu
      rw [if_neg (by omega : i ≠ C - 1 - u)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := Finset.mem_range.mp hu
    rw [if_neg (by omega : i ≠ C - 1 - u)]


























theorem fixedTyped_reversedRow_add (F G : ℤ[X]) :
    reversedRow 63 (F + G) = reversedRow 63 F + reversedRow 63 G := by
  ext i
  simp only [reversedRow_coeff, coeff_add]
  split_ifs <;> simp

theorem fixedTyped_reversedRow_monomial (c : ℤ) (k : ℕ) (hk : k < 63) :
    reversedRow 63 (Polynomial.monomial (R := ℤ) k c) =
      Polynomial.monomial (R := ℤ) (62 - k) c := by
  ext i
  simp only [reversedRow_coeff, coeff_monomial]
  split_ifs <;> omega

theorem fixedTyped_rowFactor (p : ℤ[X]) :
    (1 - X) ^ 2 * p = p - 2 * (X * p) + X * (X * p) := by
  ring

theorem fixedTyped_rowP_of_parameters (N r exponent cutoff : ℕ) (index : ℤ)
    (F : ℤ[X]) (hh : h N = exponent) (hC : Cdegree N = cutoff)
    (hi : (rowDistance N r : ℤ) = index) (hF : Chebyshev.T ℤ index = F) :
    rowP N r = (1 - X) ^ exponent * reversedRow cutoff F := by
  unfold rowP
  rw [hh, hC, hi, hF]

theorem fixedTyped_rowD_of_parameters (N r exponent cutoff : ℕ) (index sign : ℤ)
    (F : ℤ[X]) (hh : h N = exponent) (hC : Cdegree N = cutoff)
    (hs : Int.sign (rowOffset N r) = sign)
    (hi : (rowDistance N r : ℤ) - 1 = index) (hF : Chebyshev.U ℤ index = F) :
    rowD N r = Polynomial.C sign * (1 - X) ^ exponent * reversedRow cutoff F := by
  unfold rowD
  rw [hh, hC, hs, hi, hF]




end

section

open scoped BigOperators









end

section

open Polynomial







variable {K : Type*} [Field K]




end

open Polynomial



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevUData
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

























def fixedChebyshevUData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-312 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (16016 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-320320 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (3294720 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-19914752 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (76038144 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (317521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-348651520 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (242221056 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-96468992 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (16777216 : ℤ)

def fixedChebyshevUData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (26 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-2912 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (96096 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-1464320 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (12446720 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-65175552 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (222265344 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-508035072 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (784465920 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-807403520 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (530579456 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-201326592 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (33554432 : ℤ)

def fixedChebyshevUData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (364 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-21840 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (512512 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-6223360 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (44808192 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-206389248 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-1333592064 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (1917583360 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-1857028096 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (1157627904 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-419430400 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (67108864 : ℤ)

def fixedChebyshevUData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-28 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (3640 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-139776 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (2489344 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-24893440 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (154791936 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (1778122752 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-3451650048 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (4642570240 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-4244635648 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (2516582400 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-872415232 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (134217728 : ℤ)

def fixedChebyshevUData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-420 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (29120 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-792064 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (11202048 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-94595072 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (515973120 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-1905131520 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (4889837568 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-8820883456 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (11142168576 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-9646899200 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (5452595200 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-1811939328 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (268435456 : ℤ)

def fixedChebyshevUData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (30 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-4480 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (198016 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-4073472 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (47297536 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-343982080 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (1666990080 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-5588385792 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (13231325184 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-22284337152 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (26528972800 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-21810380800 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (11777605632 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-3758096384 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (536870912 : ℤ)

def fixedChebyshevUData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (480 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-38080 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (1188096 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-19348992 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (189190144 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-1203937280 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (5239111680 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-16066609152 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (35283533824 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-55710842880 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (62704844800 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-49073356800 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (25367150592 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-7784628224 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (1073741824 : ℤ)

def fixedChebyshevUData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (5440 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-274176 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (6449664 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-85995520 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (722362368 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-4074864640 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (16066609152 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-45364543488 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (92851404800 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-137950658560 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (147220070400 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-109924319232 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (54492397568 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-16106127360 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (2147483648 : ℤ)

def fixedChebyshevUData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-544 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (48960 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-1736448 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (32248320 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-361181184 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (2648662016 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-13388840960 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (48199827456 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-126012620800 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (241413652480 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-338606161920 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (343513497600 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-245215789056 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (116769423360 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-33285996544 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (4294967296 : ℤ)

def fixedChebyshevUData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (34 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-6528 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (372096 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-9922560 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (150492160 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-1444724736 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (9372188672 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-42844291072 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (141764198400 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-344876646400 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (620777963520 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-824432394240 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (796951314432 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-544923975680 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (249644974080 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (8589934592 : ℤ)

def fixedChebyshevUData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (612 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-62016 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (2480640 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-52093440 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (662165504 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-5538111488 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-133888409600 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (409541017600 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-931166945280 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (1580162088960 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-1992378286080 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (1839118417920 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-1206617374720 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (532575944704 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-141733920768 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (17179869184 : ℤ)

def fixedChebyshevUData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-36 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (7752 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-496128 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (14883840 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-254679040 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (2769055744 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-20448411648 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (107110727680 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-409541017600 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (1163958681600 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-2483111854080 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (3984756572160 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-4781707886592 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (4223160811520 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-2662879723520 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (1133871366144 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-292057776128 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (34359738368 : ℤ)

def fixedChebyshevUData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-684 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (77520 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-3472896 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (81861120 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-1171523584 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (11076222976 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-73030041600 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (348109864960 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-1228623052800 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (3259084308480 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-6546385797120 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (9961891430400 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-11402534191104 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (9652938997760 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-5858335391744 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (2409476653056 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-601295421440 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (68719476736 : ℤ)

def fixedChebyshevUData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (38 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-9120 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (651168 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-21829632 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (418401280 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-5112102912 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (42600857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-253170810880 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (1105760747520 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-3621204787200 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (9001280471040 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-17077528166400 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (24705490747392 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-27028229193728 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (21968757719040 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-12850542149632 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (5111011082240 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-1236950581248 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (137438953472 : ℤ)

def fixedChebyshevUData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (760 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-95760 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (4775232 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-125520384 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (2008326144 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-21300428800 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (158231756800 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-854451486720 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (3440144547840 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-10501493882880 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (24548946739200 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-44116947763200 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (60813515685888 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-63709397385216 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (49795850829824 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-28110560952320 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (10823317585920 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-2542620639232 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (274877906944 : ℤ)

def fixedChebyshevUData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-40 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (10640 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-842688 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (31380096 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-669442048 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (9128755200 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-85201715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (569634324480 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-2814663720960 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (10501493882880 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-30004268236800 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (66175421644800 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-112939386273792 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (148655260565504 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-149387552489472 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (112442243809280 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-61332132986880 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (22883585753088 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-5222680231936 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (549755813888 : ℤ)

def fixedChebyshevUData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-840 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (117040 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-6460608 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (188280576 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-3347210240 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (39557939200 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-328635187200 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (1993720135680 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-9069471989760 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (31504481648640 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-84557483212800 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (176467791052800 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-286692288233472 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (361019918516224 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-348570955808768 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (252995048570880 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-133487583559680 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (48309792145408 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-10720238370816 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1099511627776 : ℤ)

def fixedChebyshevUData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (42 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-12320 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (1076768 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-44301312 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (1046003200 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-15823175680 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (164317593600 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-1226904698880 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (6802103992320 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-28640437862400 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (93013231534080 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-235290388070400 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (465874968379392 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-722039837032448 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (871427389521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-809584155426816 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (567322230128640 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-289858752872448 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (101842264522752 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-21990232555520 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (2199023255552 : ℤ)



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevT39To41
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixedTyped_chebyshevT_link (a b c : ℤ) (P Q : ℤ[X])
    (hba : b = a + 1) (hca : c = a + 2)
    (hP : Chebyshev.T ℤ a = P) (hQ : Chebyshev.T ℤ b = Q) :
    Chebyshev.T ℤ c = (2 : ℤ[X]) * X * Q - P := by
  rw [hca, Chebyshev.T_add_two, ← hba, hP, hQ]

theorem fixedTyped_chebyshevU_link (a b c : ℤ) (P Q : ℤ[X])
    (hba : b = a + 1) (hca : c = a + 2)
    (hP : Chebyshev.U ℤ a = P) (hQ : Chebyshev.U ℤ b = Q) :
    Chebyshev.U ℤ c = (2 : ℤ[X]) * X * Q - P := by
  rw [hca, Chebyshev.U_add_two, ← hba, hP, hQ]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan












end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan








end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan







end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan


theorem fixed_chebyshevT_typed_25 :
    Chebyshev.T ℤ 25 = fixedChebyshevTData_25 := by
  calc
    Chebyshev.T ℤ 25 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_24 - fixedChebyshevTData_23 :=
      fixedTyped_chebyshevT_link 23 24 25 fixedChebyshevTData_23 fixedChebyshevTData_24
        (by decide) (by decide) fixed_chebyshevT_typed_23 fixed_chebyshevT_typed_24
    _ = fixedChebyshevTData_25 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_24, fixedChebyshevTData_23, fixedChebyshevTData_25, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_24, fixedChebyshevTData_23, fixedChebyshevTData_25, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 25
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 25, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 25 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_26 :
    Chebyshev.T ℤ 26 = fixedChebyshevTData_26 := by
  calc
    Chebyshev.T ℤ 26 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_25 - fixedChebyshevTData_24 :=
      fixedTyped_chebyshevT_link 24 25 26 fixedChebyshevTData_24 fixedChebyshevTData_25
        (by decide) (by decide) fixed_chebyshevT_typed_24 fixed_chebyshevT_typed_25
    _ = fixedChebyshevTData_26 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_25, fixedChebyshevTData_24, fixedChebyshevTData_26, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_25, fixedChebyshevTData_24, fixedChebyshevTData_26, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 26
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 26, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 26 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_27 :
    Chebyshev.T ℤ 27 = fixedChebyshevTData_27 := by
  calc
    Chebyshev.T ℤ 27 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_26 - fixedChebyshevTData_25 :=
      fixedTyped_chebyshevT_link 25 26 27 fixedChebyshevTData_25 fixedChebyshevTData_26
        (by decide) (by decide) fixed_chebyshevT_typed_25 fixed_chebyshevT_typed_26
    _ = fixedChebyshevTData_27 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_26, fixedChebyshevTData_25, fixedChebyshevTData_27, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_26, fixedChebyshevTData_25, fixedChebyshevTData_27, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 27
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 27, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 27 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_28 :
    Chebyshev.T ℤ 28 = fixedChebyshevTData_28 := by
  calc
    Chebyshev.T ℤ 28 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_27 - fixedChebyshevTData_26 :=
      fixedTyped_chebyshevT_link 26 27 28 fixedChebyshevTData_26 fixedChebyshevTData_27
        (by decide) (by decide) fixed_chebyshevT_typed_26 fixed_chebyshevT_typed_27
    _ = fixedChebyshevTData_28 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_27, fixedChebyshevTData_26, fixedChebyshevTData_28, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_27, fixedChebyshevTData_26, fixedChebyshevTData_28, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 28
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 28, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 28 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_24 :
    Chebyshev.U ℤ 24 = fixedChebyshevUData_24 := by
  calc
    Chebyshev.U ℤ 24 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_23 - fixedChebyshevUData_22 :=
      fixedTyped_chebyshevU_link 22 23 24 fixedChebyshevUData_22 fixedChebyshevUData_23
        (by decide) (by decide) fixed_chebyshevU_typed_22 fixed_chebyshevU_typed_23
    _ = fixedChebyshevUData_24 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_23, fixedChebyshevUData_22, fixedChebyshevUData_24, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_23, fixedChebyshevUData_22, fixedChebyshevUData_24, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 24
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 24, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 24 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_25 :
    Chebyshev.U ℤ 25 = fixedChebyshevUData_25 := by
  calc
    Chebyshev.U ℤ 25 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_24 - fixedChebyshevUData_23 :=
      fixedTyped_chebyshevU_link 23 24 25 fixedChebyshevUData_23 fixedChebyshevUData_24
        (by decide) (by decide) fixed_chebyshevU_typed_23 fixed_chebyshevU_typed_24
    _ = fixedChebyshevUData_25 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_24, fixedChebyshevUData_23, fixedChebyshevUData_25, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_24, fixedChebyshevUData_23, fixedChebyshevUData_25, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 25
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 25, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 25 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_26 :
    Chebyshev.U ℤ 26 = fixedChebyshevUData_26 := by
  calc
    Chebyshev.U ℤ 26 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_25 - fixedChebyshevUData_24 :=
      fixedTyped_chebyshevU_link 24 25 26 fixedChebyshevUData_24 fixedChebyshevUData_25
        (by decide) (by decide) fixed_chebyshevU_typed_24 fixed_chebyshevU_typed_25
    _ = fixedChebyshevUData_26 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_25, fixedChebyshevUData_24, fixedChebyshevUData_26, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_25, fixedChebyshevUData_24, fixedChebyshevUData_26, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 26
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 26, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 26 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_27 :
    Chebyshev.U ℤ 27 = fixedChebyshevUData_27 := by
  calc
    Chebyshev.U ℤ 27 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_26 - fixedChebyshevUData_25 :=
      fixedTyped_chebyshevU_link 25 26 27 fixedChebyshevUData_25 fixedChebyshevUData_26
        (by decide) (by decide) fixed_chebyshevU_typed_25 fixed_chebyshevU_typed_26
    _ = fixedChebyshevUData_27 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_26, fixedChebyshevUData_25, fixedChebyshevUData_27, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_26, fixedChebyshevUData_25, fixedChebyshevUData_27, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 27
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 27, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 27 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_28 :
    Chebyshev.U ℤ 28 = fixedChebyshevUData_28 := by
  calc
    Chebyshev.U ℤ 28 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_27 - fixedChebyshevUData_26 :=
      fixedTyped_chebyshevU_link 26 27 28 fixedChebyshevUData_26 fixedChebyshevUData_27
        (by decide) (by decide) fixed_chebyshevU_typed_26 fixed_chebyshevU_typed_27
    _ = fixedChebyshevUData_28 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_27, fixedChebyshevUData_26, fixedChebyshevUData_28, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_27, fixedChebyshevUData_26, fixedChebyshevUData_28, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 28
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 28, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 28 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_29 :
    Chebyshev.T ℤ 29 = fixedChebyshevTData_29 := by
  calc
    Chebyshev.T ℤ 29 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_28 - fixedChebyshevTData_27 :=
      fixedTyped_chebyshevT_link 27 28 29 fixedChebyshevTData_27 fixedChebyshevTData_28
        (by decide) (by decide) fixed_chebyshevT_typed_27 fixed_chebyshevT_typed_28
    _ = fixedChebyshevTData_29 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_28, fixedChebyshevTData_27, fixedChebyshevTData_29, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_28, fixedChebyshevTData_27, fixedChebyshevTData_29, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 29
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 29, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 29 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_30 :
    Chebyshev.T ℤ 30 = fixedChebyshevTData_30 := by
  calc
    Chebyshev.T ℤ 30 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_29 - fixedChebyshevTData_28 :=
      fixedTyped_chebyshevT_link 28 29 30 fixedChebyshevTData_28 fixedChebyshevTData_29
        (by decide) (by decide) fixed_chebyshevT_typed_28 fixed_chebyshevT_typed_29
    _ = fixedChebyshevTData_30 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_29, fixedChebyshevTData_28, fixedChebyshevTData_30, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_29, fixedChebyshevTData_28, fixedChebyshevTData_30, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 30
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 30, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 30 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_31 :
    Chebyshev.T ℤ 31 = fixedChebyshevTData_31 := by
  calc
    Chebyshev.T ℤ 31 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_30 - fixedChebyshevTData_29 :=
      fixedTyped_chebyshevT_link 29 30 31 fixedChebyshevTData_29 fixedChebyshevTData_30
        (by decide) (by decide) fixed_chebyshevT_typed_29 fixed_chebyshevT_typed_30
    _ = fixedChebyshevTData_31 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_30, fixedChebyshevTData_29, fixedChebyshevTData_31, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_30, fixedChebyshevTData_29, fixedChebyshevTData_31, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 31
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 31, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 31 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_32 :
    Chebyshev.T ℤ 32 = fixedChebyshevTData_32 := by
  calc
    Chebyshev.T ℤ 32 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_31 - fixedChebyshevTData_30 :=
      fixedTyped_chebyshevT_link 30 31 32 fixedChebyshevTData_30 fixedChebyshevTData_31
        (by decide) (by decide) fixed_chebyshevT_typed_30 fixed_chebyshevT_typed_31
    _ = fixedChebyshevTData_32 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_31, fixedChebyshevTData_30, fixedChebyshevTData_32, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_31, fixedChebyshevTData_30, fixedChebyshevTData_32, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 32
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 32, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 32 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_33 :
    Chebyshev.T ℤ 33 = fixedChebyshevTData_33 := by
  calc
    Chebyshev.T ℤ 33 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_32 - fixedChebyshevTData_31 :=
      fixedTyped_chebyshevT_link 31 32 33 fixedChebyshevTData_31 fixedChebyshevTData_32
        (by decide) (by decide) fixed_chebyshevT_typed_31 fixed_chebyshevT_typed_32
    _ = fixedChebyshevTData_33 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_32, fixedChebyshevTData_31, fixedChebyshevTData_33, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_32, fixedChebyshevTData_31, fixedChebyshevTData_33, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 33
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 33, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 33 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_34 :
    Chebyshev.T ℤ 34 = fixedChebyshevTData_34 := by
  calc
    Chebyshev.T ℤ 34 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_33 - fixedChebyshevTData_32 :=
      fixedTyped_chebyshevT_link 32 33 34 fixedChebyshevTData_32 fixedChebyshevTData_33
        (by decide) (by decide) fixed_chebyshevT_typed_32 fixed_chebyshevT_typed_33
    _ = fixedChebyshevTData_34 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_33, fixedChebyshevTData_32, fixedChebyshevTData_34, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_33, fixedChebyshevTData_32, fixedChebyshevTData_34, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 34
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 34, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 34 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_35 :
    Chebyshev.T ℤ 35 = fixedChebyshevTData_35 := by
  calc
    Chebyshev.T ℤ 35 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_34 - fixedChebyshevTData_33 :=
      fixedTyped_chebyshevT_link 33 34 35 fixedChebyshevTData_33 fixedChebyshevTData_34
        (by decide) (by decide) fixed_chebyshevT_typed_33 fixed_chebyshevT_typed_34
    _ = fixedChebyshevTData_35 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_34, fixedChebyshevTData_33, fixedChebyshevTData_35, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_34, fixedChebyshevTData_33, fixedChebyshevTData_35, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 35
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 35, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 35 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_36 :
    Chebyshev.T ℤ 36 = fixedChebyshevTData_36 := by
  calc
    Chebyshev.T ℤ 36 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_35 - fixedChebyshevTData_34 :=
      fixedTyped_chebyshevT_link 34 35 36 fixedChebyshevTData_34 fixedChebyshevTData_35
        (by decide) (by decide) fixed_chebyshevT_typed_34 fixed_chebyshevT_typed_35
    _ = fixedChebyshevTData_36 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_35, fixedChebyshevTData_34, fixedChebyshevTData_36, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_35, fixedChebyshevTData_34, fixedChebyshevTData_36, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 36
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 36, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 36 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_37 :
    Chebyshev.T ℤ 37 = fixedChebyshevTData_37 := by
  calc
    Chebyshev.T ℤ 37 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_36 - fixedChebyshevTData_35 :=
      fixedTyped_chebyshevT_link 35 36 37 fixedChebyshevTData_35 fixedChebyshevTData_36
        (by decide) (by decide) fixed_chebyshevT_typed_35 fixed_chebyshevT_typed_36
    _ = fixedChebyshevTData_37 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_36, fixedChebyshevTData_35, fixedChebyshevTData_37, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_36, fixedChebyshevTData_35, fixedChebyshevTData_37, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 37
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 37, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 37 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_38 :
    Chebyshev.T ℤ 38 = fixedChebyshevTData_38 := by
  calc
    Chebyshev.T ℤ 38 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_37 - fixedChebyshevTData_36 :=
      fixedTyped_chebyshevT_link 36 37 38 fixedChebyshevTData_36 fixedChebyshevTData_37
        (by decide) (by decide) fixed_chebyshevT_typed_36 fixed_chebyshevT_typed_37
    _ = fixedChebyshevTData_38 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_37, fixedChebyshevTData_36, fixedChebyshevTData_38, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_37, fixedChebyshevTData_36, fixedChebyshevTData_38, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 38
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 38, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 38 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_39 :
    Chebyshev.T ℤ 39 = fixedChebyshevTData_39 := by
  calc
    Chebyshev.T ℤ 39 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_38 - fixedChebyshevTData_37 :=
      fixedTyped_chebyshevT_link 37 38 39 fixedChebyshevTData_37 fixedChebyshevTData_38
        (by decide) (by decide) fixed_chebyshevT_typed_37 fixed_chebyshevT_typed_38
    _ = fixedChebyshevTData_39 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_38, fixedChebyshevTData_37, fixedChebyshevTData_39, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_38, fixedChebyshevTData_37, fixedChebyshevTData_39, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 39
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 39, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 39 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_40 :
    Chebyshev.T ℤ 40 = fixedChebyshevTData_40 := by
  calc
    Chebyshev.T ℤ 40 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_39 - fixedChebyshevTData_38 :=
      fixedTyped_chebyshevT_link 38 39 40 fixedChebyshevTData_38 fixedChebyshevTData_39
        (by decide) (by decide) fixed_chebyshevT_typed_38 fixed_chebyshevT_typed_39
    _ = fixedChebyshevTData_40 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_39, fixedChebyshevTData_38, fixedChebyshevTData_40, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_39, fixedChebyshevTData_38, fixedChebyshevTData_40, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 40
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 40, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 40 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_41 :
    Chebyshev.T ℤ 41 = fixedChebyshevTData_41 := by
  calc
    Chebyshev.T ℤ 41 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_40 - fixedChebyshevTData_39 :=
      fixedTyped_chebyshevT_link 39 40 41 fixedChebyshevTData_39 fixedChebyshevTData_40
        (by decide) (by decide) fixed_chebyshevT_typed_39 fixed_chebyshevT_typed_40
    _ = fixedChebyshevTData_41 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_40, fixedChebyshevTData_39, fixedChebyshevTData_41, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_40, fixedChebyshevTData_39, fixedChebyshevTData_41, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 41
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 41, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 41 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT0To7
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_29 :
    Chebyshev.U ℤ 29 = fixedChebyshevUData_29 := by
  calc
    Chebyshev.U ℤ 29 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_28 - fixedChebyshevUData_27 :=
      fixedTyped_chebyshevU_link 27 28 29 fixedChebyshevUData_27 fixedChebyshevUData_28
        (by decide) (by decide) fixed_chebyshevU_typed_27 fixed_chebyshevU_typed_28
    _ = fixedChebyshevUData_29 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_28, fixedChebyshevUData_27, fixedChebyshevUData_29, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_28, fixedChebyshevUData_27, fixedChebyshevUData_29, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 29
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 29, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 29 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_30 :
    Chebyshev.U ℤ 30 = fixedChebyshevUData_30 := by
  calc
    Chebyshev.U ℤ 30 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_29 - fixedChebyshevUData_28 :=
      fixedTyped_chebyshevU_link 28 29 30 fixedChebyshevUData_28 fixedChebyshevUData_29
        (by decide) (by decide) fixed_chebyshevU_typed_28 fixed_chebyshevU_typed_29
    _ = fixedChebyshevUData_30 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_29, fixedChebyshevUData_28, fixedChebyshevUData_30, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_29, fixedChebyshevUData_28, fixedChebyshevUData_30, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 30
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 30, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 30 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_31 :
    Chebyshev.U ℤ 31 = fixedChebyshevUData_31 := by
  calc
    Chebyshev.U ℤ 31 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_30 - fixedChebyshevUData_29 :=
      fixedTyped_chebyshevU_link 29 30 31 fixedChebyshevUData_29 fixedChebyshevUData_30
        (by decide) (by decide) fixed_chebyshevU_typed_29 fixed_chebyshevU_typed_30
    _ = fixedChebyshevUData_31 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_30, fixedChebyshevUData_29, fixedChebyshevUData_31, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_30, fixedChebyshevUData_29, fixedChebyshevUData_31, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 31
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 31, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 31 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_32 :
    Chebyshev.U ℤ 32 = fixedChebyshevUData_32 := by
  calc
    Chebyshev.U ℤ 32 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_31 - fixedChebyshevUData_30 :=
      fixedTyped_chebyshevU_link 30 31 32 fixedChebyshevUData_30 fixedChebyshevUData_31
        (by decide) (by decide) fixed_chebyshevU_typed_30 fixed_chebyshevU_typed_31
    _ = fixedChebyshevUData_32 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_31, fixedChebyshevUData_30, fixedChebyshevUData_32, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_31, fixedChebyshevUData_30, fixedChebyshevUData_32, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 32
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 32, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 32 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_33 :
    Chebyshev.U ℤ 33 = fixedChebyshevUData_33 := by
  calc
    Chebyshev.U ℤ 33 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_32 - fixedChebyshevUData_31 :=
      fixedTyped_chebyshevU_link 31 32 33 fixedChebyshevUData_31 fixedChebyshevUData_32
        (by decide) (by decide) fixed_chebyshevU_typed_31 fixed_chebyshevU_typed_32
    _ = fixedChebyshevUData_33 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_32, fixedChebyshevUData_31, fixedChebyshevUData_33, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_32, fixedChebyshevUData_31, fixedChebyshevUData_33, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 33
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 33, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 33 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_34 :
    Chebyshev.U ℤ 34 = fixedChebyshevUData_34 := by
  calc
    Chebyshev.U ℤ 34 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_33 - fixedChebyshevUData_32 :=
      fixedTyped_chebyshevU_link 32 33 34 fixedChebyshevUData_32 fixedChebyshevUData_33
        (by decide) (by decide) fixed_chebyshevU_typed_32 fixed_chebyshevU_typed_33
    _ = fixedChebyshevUData_34 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_33, fixedChebyshevUData_32, fixedChebyshevUData_34, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_33, fixedChebyshevUData_32, fixedChebyshevUData_34, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 34
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 34, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 34 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_35 :
    Chebyshev.U ℤ 35 = fixedChebyshevUData_35 := by
  calc
    Chebyshev.U ℤ 35 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_34 - fixedChebyshevUData_33 :=
      fixedTyped_chebyshevU_link 33 34 35 fixedChebyshevUData_33 fixedChebyshevUData_34
        (by decide) (by decide) fixed_chebyshevU_typed_33 fixed_chebyshevU_typed_34
    _ = fixedChebyshevUData_35 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_34, fixedChebyshevUData_33, fixedChebyshevUData_35, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_34, fixedChebyshevUData_33, fixedChebyshevUData_35, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 35
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 35, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 35 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_36 :
    Chebyshev.U ℤ 36 = fixedChebyshevUData_36 := by
  calc
    Chebyshev.U ℤ 36 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_35 - fixedChebyshevUData_34 :=
      fixedTyped_chebyshevU_link 34 35 36 fixedChebyshevUData_34 fixedChebyshevUData_35
        (by decide) (by decide) fixed_chebyshevU_typed_34 fixed_chebyshevU_typed_35
    _ = fixedChebyshevUData_36 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_35, fixedChebyshevUData_34, fixedChebyshevUData_36, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_35, fixedChebyshevUData_34, fixedChebyshevUData_36, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 36
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 36, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 36 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_37 :
    Chebyshev.U ℤ 37 = fixedChebyshevUData_37 := by
  calc
    Chebyshev.U ℤ 37 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_36 - fixedChebyshevUData_35 :=
      fixedTyped_chebyshevU_link 35 36 37 fixedChebyshevUData_35 fixedChebyshevUData_36
        (by decide) (by decide) fixed_chebyshevU_typed_35 fixed_chebyshevU_typed_36
    _ = fixedChebyshevUData_37 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_36, fixedChebyshevUData_35, fixedChebyshevUData_37, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_36, fixedChebyshevUData_35, fixedChebyshevUData_37, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 37
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 37, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 37 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_38 :
    Chebyshev.U ℤ 38 = fixedChebyshevUData_38 := by
  calc
    Chebyshev.U ℤ 38 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_37 - fixedChebyshevUData_36 :=
      fixedTyped_chebyshevU_link 36 37 38 fixedChebyshevUData_36 fixedChebyshevUData_37
        (by decide) (by decide) fixed_chebyshevU_typed_36 fixed_chebyshevU_typed_37
    _ = fixedChebyshevUData_38 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_37, fixedChebyshevUData_36, fixedChebyshevUData_38, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_37, fixedChebyshevUData_36, fixedChebyshevUData_38, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 38
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 38, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 38 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_39 :
    Chebyshev.U ℤ 39 = fixedChebyshevUData_39 := by
  calc
    Chebyshev.U ℤ 39 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_38 - fixedChebyshevUData_37 :=
      fixedTyped_chebyshevU_link 37 38 39 fixedChebyshevUData_37 fixedChebyshevUData_38
        (by decide) (by decide) fixed_chebyshevU_typed_37 fixed_chebyshevU_typed_38
    _ = fixedChebyshevUData_39 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_38, fixedChebyshevUData_37, fixedChebyshevUData_39, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_38, fixedChebyshevUData_37, fixedChebyshevUData_39, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 39
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 39, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 39 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_40 :
    Chebyshev.U ℤ 40 = fixedChebyshevUData_40 := by
  calc
    Chebyshev.U ℤ 40 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_39 - fixedChebyshevUData_38 :=
      fixedTyped_chebyshevU_link 38 39 40 fixedChebyshevUData_38 fixedChebyshevUData_39
        (by decide) (by decide) fixed_chebyshevU_typed_38 fixed_chebyshevU_typed_39
    _ = fixedChebyshevUData_40 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_39, fixedChebyshevUData_38, fixedChebyshevUData_40, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_39, fixedChebyshevUData_38, fixedChebyshevUData_40, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 40
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 40, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 40 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_41 :
    Chebyshev.U ℤ 41 = fixedChebyshevUData_41 := by
  calc
    Chebyshev.U ℤ 41 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_40 - fixedChebyshevUData_39 :=
      fixedTyped_chebyshevU_link 39 40 41 fixedChebyshevUData_39 fixedChebyshevUData_40
        (by decide) (by decide) fixed_chebyshevU_typed_39 fixed_chebyshevU_typed_40
    _ = fixedChebyshevUData_41 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_40, fixedChebyshevUData_39, fixedChebyshevUData_41, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_40, fixedChebyshevUData_39, fixedChebyshevUData_41, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 41
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 41, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 41 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_42 :
    Chebyshev.T ℤ 42 = fixedChebyshevTData_42 := by
  calc
    Chebyshev.T ℤ 42 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_41 - fixedChebyshevTData_40 :=
      fixedTyped_chebyshevT_link 40 41 42 fixedChebyshevTData_40 fixedChebyshevTData_41
        (by decide) (by decide) fixed_chebyshevT_typed_40 fixed_chebyshevT_typed_41
    _ = fixedChebyshevTData_42 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_41, fixedChebyshevTData_40, fixedChebyshevTData_42, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_41, fixedChebyshevTData_40, fixedChebyshevTData_42, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 42
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 42, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 42 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]



end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan



end InternalCatalan

end




noncomputable section
open Polynomial
namespace InternalCatalan









































end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT40To44
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan






def fixedReversedTData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (41 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-11480 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (959728 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-37840704 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (857722624 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-12475965440 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (124759654400 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-898269511680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (4808383856640 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-19570965872640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (61508749885440 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-150732904857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (289407177326592 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-435347548798976 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (510407471005696 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-461013199618048 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (314327181557760 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-156371169312768 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (53532472377344 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-11269994184704 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (1099511627776 : ℤ)

def fixedReversedTCoeff_41 (n : ℕ) : ℤ :=
    (if 61 = n then (41 : ℤ) else 0) +
    (if 59 = n then (-11480 : ℤ) else 0) +
    (if 57 = n then (959728 : ℤ) else 0) +
    (if 55 = n then (-37840704 : ℤ) else 0) +
    (if 53 = n then (857722624 : ℤ) else 0) +
    (if 51 = n then (-12475965440 : ℤ) else 0) +
    (if 49 = n then (124759654400 : ℤ) else 0) +
    (if 47 = n then (-898269511680 : ℤ) else 0) +
    (if 45 = n then (4808383856640 : ℤ) else 0) +
    (if 43 = n then (-19570965872640 : ℤ) else 0) +
    (if 41 = n then (61508749885440 : ℤ) else 0) +
    (if 39 = n then (-150732904857600 : ℤ) else 0) +
    (if 37 = n then (289407177326592 : ℤ) else 0) +
    (if 35 = n then (-435347548798976 : ℤ) else 0) +
    (if 33 = n then (510407471005696 : ℤ) else 0) +
    (if 31 = n then (-461013199618048 : ℤ) else 0) +
    (if 29 = n then (314327181557760 : ℤ) else 0) +
    (if 27 = n then (-156371169312768 : ℤ) else 0) +
    (if 25 = n then (53532472377344 : ℤ) else 0) +
    (if 23 = n then (-11269994184704 : ℤ) else 0) +
    (if 21 = n then (1099511627776 : ℤ) else 0)

theorem fixed_reversedT_typed_data_41 : reversedRow 63 fixedChebyshevTData_41 = fixedReversedTData_41 := by
  simp only [fixedChebyshevTData_41, fixedReversedTData_41, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (41 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-11480 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (959728 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-37840704 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (857722624 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-12475965440 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (124759654400 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-898269511680 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (4808383856640 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-19570965872640 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (61508749885440 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-150732904857600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (289407177326592 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-435347548798976 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (510407471005696 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-461013199618048 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (314327181557760 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (-156371169312768 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (53532472377344 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (-11269994184704 : ℤ) 39 (by decide),
    fixedTyped_reversedRow_monomial (1099511627776 : ℤ) 41 (by decide)]

theorem fixed_reversedT_typed_coeff_41 (n : ℕ) :
    fixedReversedTData_41.coeff n = fixedReversedTCoeff_41 n := by
  simp only [fixedReversedTData_41, fixedReversedTCoeff_41, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_41 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_41 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_41, if_neg, add_zero]

def fixedReversedTData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (882 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-129360 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (7537376 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-232581888 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (4393213440 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-55381114880 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (492952780800 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-3220624834560 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (15871575982080 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-60144919511040 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (177570714746880 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-411758179123200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (752567256612864 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1083059755548672 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (1219998345330688 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-1062579203997696 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (700809813688320 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-338168545017856 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (112562502893568 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-23089744183296 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (2199023255552 : ℤ)

def fixedReversedTCoeff_42 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (882 : ℤ) else 0) +
    (if 58 = n then (-129360 : ℤ) else 0) +
    (if 56 = n then (7537376 : ℤ) else 0) +
    (if 54 = n then (-232581888 : ℤ) else 0) +
    (if 52 = n then (4393213440 : ℤ) else 0) +
    (if 50 = n then (-55381114880 : ℤ) else 0) +
    (if 48 = n then (492952780800 : ℤ) else 0) +
    (if 46 = n then (-3220624834560 : ℤ) else 0) +
    (if 44 = n then (15871575982080 : ℤ) else 0) +
    (if 42 = n then (-60144919511040 : ℤ) else 0) +
    (if 40 = n then (177570714746880 : ℤ) else 0) +
    (if 38 = n then (-411758179123200 : ℤ) else 0) +
    (if 36 = n then (752567256612864 : ℤ) else 0) +
    (if 34 = n then (-1083059755548672 : ℤ) else 0) +
    (if 32 = n then (1219998345330688 : ℤ) else 0) +
    (if 30 = n then (-1062579203997696 : ℤ) else 0) +
    (if 28 = n then (700809813688320 : ℤ) else 0) +
    (if 26 = n then (-338168545017856 : ℤ) else 0) +
    (if 24 = n then (112562502893568 : ℤ) else 0) +
    (if 22 = n then (-23089744183296 : ℤ) else 0) +
    (if 20 = n then (2199023255552 : ℤ) else 0)

theorem fixed_reversedT_typed_data_42 : reversedRow 63 fixedChebyshevTData_42 = fixedReversedTData_42 := by
  simp only [fixedChebyshevTData_42, fixedReversedTData_42, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (882 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-129360 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (7537376 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-232581888 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (4393213440 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-55381114880 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (492952780800 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-3220624834560 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (15871575982080 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-60144919511040 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (177570714746880 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-411758179123200 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (752567256612864 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-1083059755548672 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (1219998345330688 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-1062579203997696 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (700809813688320 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (-338168545017856 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (112562502893568 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (-23089744183296 : ℤ) 40 (by decide),
    fixedTyped_reversedRow_monomial (2199023255552 : ℤ) 42 (by decide)]

theorem fixed_reversedT_typed_coeff_42 (n : ℕ) :
    fixedReversedTData_42.coeff n = fixedReversedTCoeff_42 n := by
  simp only [fixedReversedTData_42, fixedReversedTCoeff_42, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_42 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_42 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_42, if_neg, add_zero]











end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedU40To43
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-840 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (117040 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-6460608 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (188280576 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-3347210240 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (39557939200 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-328635187200 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (1993720135680 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-9069471989760 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (31504481648640 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-84557483212800 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (176467791052800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-286692288233472 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (361019918516224 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-348570955808768 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (252995048570880 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-133487583559680 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (48309792145408 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-10720238370816 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (1099511627776 : ℤ)

def fixedReversedUCoeff_40 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-840 : ℤ) else 0) +
    (if 58 = n then (117040 : ℤ) else 0) +
    (if 56 = n then (-6460608 : ℤ) else 0) +
    (if 54 = n then (188280576 : ℤ) else 0) +
    (if 52 = n then (-3347210240 : ℤ) else 0) +
    (if 50 = n then (39557939200 : ℤ) else 0) +
    (if 48 = n then (-328635187200 : ℤ) else 0) +
    (if 46 = n then (1993720135680 : ℤ) else 0) +
    (if 44 = n then (-9069471989760 : ℤ) else 0) +
    (if 42 = n then (31504481648640 : ℤ) else 0) +
    (if 40 = n then (-84557483212800 : ℤ) else 0) +
    (if 38 = n then (176467791052800 : ℤ) else 0) +
    (if 36 = n then (-286692288233472 : ℤ) else 0) +
    (if 34 = n then (361019918516224 : ℤ) else 0) +
    (if 32 = n then (-348570955808768 : ℤ) else 0) +
    (if 30 = n then (252995048570880 : ℤ) else 0) +
    (if 28 = n then (-133487583559680 : ℤ) else 0) +
    (if 26 = n then (48309792145408 : ℤ) else 0) +
    (if 24 = n then (-10720238370816 : ℤ) else 0) +
    (if 22 = n then (1099511627776 : ℤ) else 0)

theorem fixed_reversedU_typed_data_40 : reversedRow 63 fixedChebyshevUData_40 = fixedReversedUData_40 := by
  simp only [fixedChebyshevUData_40, fixedReversedUData_40, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-840 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (117040 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-6460608 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (188280576 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-3347210240 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (39557939200 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-328635187200 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (1993720135680 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-9069471989760 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (31504481648640 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-84557483212800 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (176467791052800 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-286692288233472 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (361019918516224 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-348570955808768 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (252995048570880 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-133487583559680 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (48309792145408 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (-10720238370816 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (1099511627776 : ℤ) 40 (by decide)]

theorem fixed_reversedU_typed_coeff_40 (n : ℕ) :
    fixedReversedUData_40.coeff n = fixedReversedUCoeff_40 n := by
  simp only [fixedReversedUData_40, fixedReversedUCoeff_40, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_40 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_40 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_40, if_neg, add_zero]

def fixedReversedUData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (42 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-12320 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1076768 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-44301312 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1046003200 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-15823175680 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (164317593600 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-1226904698880 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (6802103992320 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-28640437862400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (93013231534080 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-235290388070400 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (465874968379392 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-722039837032448 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (871427389521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-809584155426816 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (567322230128640 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-289858752872448 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (101842264522752 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-21990232555520 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (2199023255552 : ℤ)

def fixedReversedUCoeff_41 (n : ℕ) : ℤ :=
    (if 61 = n then (42 : ℤ) else 0) +
    (if 59 = n then (-12320 : ℤ) else 0) +
    (if 57 = n then (1076768 : ℤ) else 0) +
    (if 55 = n then (-44301312 : ℤ) else 0) +
    (if 53 = n then (1046003200 : ℤ) else 0) +
    (if 51 = n then (-15823175680 : ℤ) else 0) +
    (if 49 = n then (164317593600 : ℤ) else 0) +
    (if 47 = n then (-1226904698880 : ℤ) else 0) +
    (if 45 = n then (6802103992320 : ℤ) else 0) +
    (if 43 = n then (-28640437862400 : ℤ) else 0) +
    (if 41 = n then (93013231534080 : ℤ) else 0) +
    (if 39 = n then (-235290388070400 : ℤ) else 0) +
    (if 37 = n then (465874968379392 : ℤ) else 0) +
    (if 35 = n then (-722039837032448 : ℤ) else 0) +
    (if 33 = n then (871427389521920 : ℤ) else 0) +
    (if 31 = n then (-809584155426816 : ℤ) else 0) +
    (if 29 = n then (567322230128640 : ℤ) else 0) +
    (if 27 = n then (-289858752872448 : ℤ) else 0) +
    (if 25 = n then (101842264522752 : ℤ) else 0) +
    (if 23 = n then (-21990232555520 : ℤ) else 0) +
    (if 21 = n then (2199023255552 : ℤ) else 0)

theorem fixed_reversedU_typed_data_41 : reversedRow 63 fixedChebyshevUData_41 = fixedReversedUData_41 := by
  simp only [fixedChebyshevUData_41, fixedReversedUData_41, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (42 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-12320 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (1076768 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-44301312 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (1046003200 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-15823175680 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (164317593600 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-1226904698880 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (6802103992320 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-28640437862400 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (93013231534080 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-235290388070400 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (465874968379392 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-722039837032448 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (871427389521920 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-809584155426816 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (567322230128640 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (-289858752872448 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (101842264522752 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (-21990232555520 : ℤ) 39 (by decide),
    fixedTyped_reversedRow_monomial (2199023255552 : ℤ) 41 (by decide)]

theorem fixed_reversedU_typed_coeff_41 (n : ℕ) :
    fixedReversedUData_41.coeff n = fixedReversedUCoeff_41 n := by
  simp only [fixedReversedUData_41, fixedReversedUCoeff_41, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_41 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_41 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_41, if_neg, add_zero]











end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow45
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_45 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 21 (1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-2199023255552 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-10170482556928 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (22539988369408 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (42262478192640 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-107064944754688 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-102838696935424 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (312742338625536 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (157956012244992 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-628654363115520 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-146686018060288 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (922026399236096 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (49394271387648 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1020814942011392 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (75059922206720 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (870695097597952 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-145940371472384 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-578814354653184 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (138674272468992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (301465809715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-89224154972160 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-123017499770880 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (41937784012800 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (39141931745280 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-14762582016000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-9616767713280 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (3910114344960 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1796539023360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-773509857280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-249519308800 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (112283688960 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (24951930880 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-11618242816 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1715445248 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (819881920 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (75681408 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-36880976 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1919456 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (948248 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (22960 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-11439 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-82 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (41 : ℤ)

def fixedRowPCoeff_45 (n : ℕ) : ℤ :=
    (if 21 = n then (1099511627776 : ℤ) else 0) +
    (if 22 = n then (-2199023255552 : ℤ) else 0) +
    (if 23 = n then (-10170482556928 : ℤ) else 0) +
    (if 24 = n then (22539988369408 : ℤ) else 0) +
    (if 25 = n then (42262478192640 : ℤ) else 0) +
    (if 26 = n then (-107064944754688 : ℤ) else 0) +
    (if 27 = n then (-102838696935424 : ℤ) else 0) +
    (if 28 = n then (312742338625536 : ℤ) else 0) +
    (if 29 = n then (157956012244992 : ℤ) else 0) +
    (if 30 = n then (-628654363115520 : ℤ) else 0) +
    (if 31 = n then (-146686018060288 : ℤ) else 0) +
    (if 32 = n then (922026399236096 : ℤ) else 0) +
    (if 33 = n then (49394271387648 : ℤ) else 0) +
    (if 34 = n then (-1020814942011392 : ℤ) else 0) +
    (if 35 = n then (75059922206720 : ℤ) else 0) +
    (if 36 = n then (870695097597952 : ℤ) else 0) +
    (if 37 = n then (-145940371472384 : ℤ) else 0) +
    (if 38 = n then (-578814354653184 : ℤ) else 0) +
    (if 39 = n then (138674272468992 : ℤ) else 0) +
    (if 40 = n then (301465809715200 : ℤ) else 0) +
    (if 41 = n then (-89224154972160 : ℤ) else 0) +
    (if 42 = n then (-123017499770880 : ℤ) else 0) +
    (if 43 = n then (41937784012800 : ℤ) else 0) +
    (if 44 = n then (39141931745280 : ℤ) else 0) +
    (if 45 = n then (-14762582016000 : ℤ) else 0) +
    (if 46 = n then (-9616767713280 : ℤ) else 0) +
    (if 47 = n then (3910114344960 : ℤ) else 0) +
    (if 48 = n then (1796539023360 : ℤ) else 0) +
    (if 49 = n then (-773509857280 : ℤ) else 0) +
    (if 50 = n then (-249519308800 : ℤ) else 0) +
    (if 51 = n then (112283688960 : ℤ) else 0) +
    (if 52 = n then (24951930880 : ℤ) else 0) +
    (if 53 = n then (-11618242816 : ℤ) else 0) +
    (if 54 = n then (-1715445248 : ℤ) else 0) +
    (if 55 = n then (819881920 : ℤ) else 0) +
    (if 56 = n then (75681408 : ℤ) else 0) +
    (if 57 = n then (-36880976 : ℤ) else 0) +
    (if 58 = n then (-1919456 : ℤ) else 0) +
    (if 59 = n then (948248 : ℤ) else 0) +
    (if 60 = n then (22960 : ℤ) else 0) +
    (if 61 = n then (-11439 : ℤ) else 0) +
    (if 62 = n then (-82 : ℤ) else 0) +
    (if 63 = n then (41 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_45 (n : ℕ) :
    fixedRowPData_45.coeff n = fixedRowPCoeff_45 n := by
  simp only [fixedRowPData_45, fixedRowPCoeff_45, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_45 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_45 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_45, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_45 : ∀ k : Fin 63,
    fixedReversedTCoeff_41 (k.val + 2) - 2 * fixedReversedTCoeff_41 (k.val + 1) + fixedReversedTCoeff_41 k.val = fixedRowPCoeff_45 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_45 :
    (1 - X) ^ 2 * fixedReversedTData_41 = fixedRowPData_45 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_41, fixed_rowP_typed_coeff_45]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_41, fixed_rowP_typed_coeff_45]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_41, fixed_rowP_typed_coeff_45]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_45 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_41 _ (by omega),
              fixed_reversedT_typed_tail_41 _ (by omega), fixed_reversedT_typed_tail_41 _ hn',
              fixed_rowP_typed_tail_45 _ (by omega)]
            decide

theorem fixed_rowP_typed_45 : rowP 1 45 = fixedRowPData_45 := by
  calc
    rowP 1 45 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_41 :=
      fixedTyped_rowP_of_parameters 1 45 2 63 41 fixedChebyshevTData_41
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_41
    _ = fixedRowPData_45 := by
      rw [fixed_reversedT_typed_data_41, fixed_rowP_typed_factor_45]

def fixedRowDData_45 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 22 (1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-2199023255552 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-9620726743040 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (21440476741632 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (37589553774592 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-96619584290816 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-85177791414272 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (266975167119360 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (119507465011200 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-505990097141760 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-95575907237888 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (697141911617536 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (12448962707456 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-722039837032448 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (74327630282752 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (573384576466944 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-110224497180672 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-352935582105600 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (91910307840000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (169114966425600 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-53053001564160 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-63008963297280 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (22435009658880 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (18138943979520 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-7075751854080 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-3987440271360 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1665084948480 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (657270374400 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-289077248000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-79115878400 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (36210728960 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (6694420480 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-3158929664 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-376561152 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (181819968 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (12921216 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-6343568 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-234080 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (116200 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1680 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-839 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_45 (n : ℕ) : ℤ :=
    (if 22 = n then (1099511627776 : ℤ) else 0) +
    (if 23 = n then (-2199023255552 : ℤ) else 0) +
    (if 24 = n then (-9620726743040 : ℤ) else 0) +
    (if 25 = n then (21440476741632 : ℤ) else 0) +
    (if 26 = n then (37589553774592 : ℤ) else 0) +
    (if 27 = n then (-96619584290816 : ℤ) else 0) +
    (if 28 = n then (-85177791414272 : ℤ) else 0) +
    (if 29 = n then (266975167119360 : ℤ) else 0) +
    (if 30 = n then (119507465011200 : ℤ) else 0) +
    (if 31 = n then (-505990097141760 : ℤ) else 0) +
    (if 32 = n then (-95575907237888 : ℤ) else 0) +
    (if 33 = n then (697141911617536 : ℤ) else 0) +
    (if 34 = n then (12448962707456 : ℤ) else 0) +
    (if 35 = n then (-722039837032448 : ℤ) else 0) +
    (if 36 = n then (74327630282752 : ℤ) else 0) +
    (if 37 = n then (573384576466944 : ℤ) else 0) +
    (if 38 = n then (-110224497180672 : ℤ) else 0) +
    (if 39 = n then (-352935582105600 : ℤ) else 0) +
    (if 40 = n then (91910307840000 : ℤ) else 0) +
    (if 41 = n then (169114966425600 : ℤ) else 0) +
    (if 42 = n then (-53053001564160 : ℤ) else 0) +
    (if 43 = n then (-63008963297280 : ℤ) else 0) +
    (if 44 = n then (22435009658880 : ℤ) else 0) +
    (if 45 = n then (18138943979520 : ℤ) else 0) +
    (if 46 = n then (-7075751854080 : ℤ) else 0) +
    (if 47 = n then (-3987440271360 : ℤ) else 0) +
    (if 48 = n then (1665084948480 : ℤ) else 0) +
    (if 49 = n then (657270374400 : ℤ) else 0) +
    (if 50 = n then (-289077248000 : ℤ) else 0) +
    (if 51 = n then (-79115878400 : ℤ) else 0) +
    (if 52 = n then (36210728960 : ℤ) else 0) +
    (if 53 = n then (6694420480 : ℤ) else 0) +
    (if 54 = n then (-3158929664 : ℤ) else 0) +
    (if 55 = n then (-376561152 : ℤ) else 0) +
    (if 56 = n then (181819968 : ℤ) else 0) +
    (if 57 = n then (12921216 : ℤ) else 0) +
    (if 58 = n then (-6343568 : ℤ) else 0) +
    (if 59 = n then (-234080 : ℤ) else 0) +
    (if 60 = n then (116200 : ℤ) else 0) +
    (if 61 = n then (1680 : ℤ) else 0) +
    (if 62 = n then (-839 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_45 (n : ℕ) :
    fixedRowDData_45.coeff n = fixedRowDCoeff_45 n := by
  simp only [fixedRowDData_45, fixedRowDCoeff_45, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_45 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_45 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_45, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_45 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_40 (k.val + 2) - 2 * fixedReversedUCoeff_40 (k.val + 1) + fixedReversedUCoeff_40 k.val) = fixedRowDCoeff_45 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_45 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_40 = fixedRowDData_45 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_40, fixed_rowD_typed_coeff_45]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_40, fixed_rowD_typed_coeff_45]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_40, fixed_rowD_typed_coeff_45]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_45 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_40 _ (by omega),
              fixed_reversedU_typed_tail_40 _ (by omega), fixed_reversedU_typed_tail_40 _ hn',
              fixed_rowD_typed_tail_45 _ (by omega)]
            decide

theorem fixed_rowD_typed_45 : rowD 1 45 = fixedRowDData_45 := by
  calc
    rowD 1 45 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_40 :=
      fixedTyped_rowD_of_parameters 1 45 2 63 40 (1)
        fixedChebyshevUData_40 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_40
    _ = fixedRowDData_45 := by
      rw [fixed_reversedU_typed_data_40, fixed_rowD_typed_factor_45]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow46
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_46 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 20 (2199023255552 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-4398046511104 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-20890720927744 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (46179488366592 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (89472758710272 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-225125005787136 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-225606042124288 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (676337090035712 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (362641268670464 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-1401619627376640 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-361769390309376 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (2125158407995392 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (157419141332992 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2439996690661376 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (136938589782016 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2166119511097344 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-330492498935808 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-1505134513225728 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (340809077489664 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (823516358246400 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-234187464376320 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-355141429493760 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (117425795235840 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (120289839022080 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-44273343528960 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-31743151964160 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (12650951147520 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (6441249669120 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-2727672053760 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-985905561600 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (437571665920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (110762229760 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-50987901440 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-8786426880 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (4160631552 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (465163776 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-225044512 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-15074752 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (7408016 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (258720 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-128478 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1764 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (881 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_46 (n : ℕ) : ℤ :=
    (if 20 = n then (2199023255552 : ℤ) else 0) +
    (if 21 = n then (-4398046511104 : ℤ) else 0) +
    (if 22 = n then (-20890720927744 : ℤ) else 0) +
    (if 23 = n then (46179488366592 : ℤ) else 0) +
    (if 24 = n then (89472758710272 : ℤ) else 0) +
    (if 25 = n then (-225125005787136 : ℤ) else 0) +
    (if 26 = n then (-225606042124288 : ℤ) else 0) +
    (if 27 = n then (676337090035712 : ℤ) else 0) +
    (if 28 = n then (362641268670464 : ℤ) else 0) +
    (if 29 = n then (-1401619627376640 : ℤ) else 0) +
    (if 30 = n then (-361769390309376 : ℤ) else 0) +
    (if 31 = n then (2125158407995392 : ℤ) else 0) +
    (if 32 = n then (157419141332992 : ℤ) else 0) +
    (if 33 = n then (-2439996690661376 : ℤ) else 0) +
    (if 34 = n then (136938589782016 : ℤ) else 0) +
    (if 35 = n then (2166119511097344 : ℤ) else 0) +
    (if 36 = n then (-330492498935808 : ℤ) else 0) +
    (if 37 = n then (-1505134513225728 : ℤ) else 0) +
    (if 38 = n then (340809077489664 : ℤ) else 0) +
    (if 39 = n then (823516358246400 : ℤ) else 0) +
    (if 40 = n then (-234187464376320 : ℤ) else 0) +
    (if 41 = n then (-355141429493760 : ℤ) else 0) +
    (if 42 = n then (117425795235840 : ℤ) else 0) +
    (if 43 = n then (120289839022080 : ℤ) else 0) +
    (if 44 = n then (-44273343528960 : ℤ) else 0) +
    (if 45 = n then (-31743151964160 : ℤ) else 0) +
    (if 46 = n then (12650951147520 : ℤ) else 0) +
    (if 47 = n then (6441249669120 : ℤ) else 0) +
    (if 48 = n then (-2727672053760 : ℤ) else 0) +
    (if 49 = n then (-985905561600 : ℤ) else 0) +
    (if 50 = n then (437571665920 : ℤ) else 0) +
    (if 51 = n then (110762229760 : ℤ) else 0) +
    (if 52 = n then (-50987901440 : ℤ) else 0) +
    (if 53 = n then (-8786426880 : ℤ) else 0) +
    (if 54 = n then (4160631552 : ℤ) else 0) +
    (if 55 = n then (465163776 : ℤ) else 0) +
    (if 56 = n then (-225044512 : ℤ) else 0) +
    (if 57 = n then (-15074752 : ℤ) else 0) +
    (if 58 = n then (7408016 : ℤ) else 0) +
    (if 59 = n then (258720 : ℤ) else 0) +
    (if 60 = n then (-128478 : ℤ) else 0) +
    (if 61 = n then (-1764 : ℤ) else 0) +
    (if 62 = n then (881 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_46 (n : ℕ) :
    fixedRowPData_46.coeff n = fixedRowPCoeff_46 n := by
  simp only [fixedRowPData_46, fixedRowPCoeff_46, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_46 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_46 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_46, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_46 : ∀ k : Fin 63,
    fixedReversedTCoeff_42 (k.val + 2) - 2 * fixedReversedTCoeff_42 (k.val + 1) + fixedReversedTCoeff_42 k.val = fixedRowPCoeff_46 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_46 :
    (1 - X) ^ 2 * fixedReversedTData_42 = fixedRowPData_46 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_42, fixed_rowP_typed_coeff_46]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_42, fixed_rowP_typed_coeff_46]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_42, fixed_rowP_typed_coeff_46]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_46 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_42 _ (by omega),
              fixed_reversedT_typed_tail_42 _ (by omega), fixed_reversedT_typed_tail_42 _ hn',
              fixed_rowP_typed_tail_46 _ (by omega)]
            decide

theorem fixed_rowP_typed_46 : rowP 1 46 = fixedRowPData_46 := by
  calc
    rowP 1 46 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_42 :=
      fixedTyped_rowP_of_parameters 1 46 2 63 42 fixedChebyshevTData_42
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_42
    _ = fixedRowPData_46 := by
      rw [fixed_reversedT_typed_data_42, fixed_rowP_typed_factor_46]

def fixedRowDData_46 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 21 (2199023255552 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-4398046511104 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-19791209299968 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (43980465111040 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (79852031967232 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-203684529045504 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-188016488349696 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (579717505744896 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (277463477256192 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-1134644460257280 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-242261925298176 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (1619168310853632 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (61843234095104 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1742854779043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (149387552489472 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1444079674064896 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-256164868653056 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-931749936758784 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (230584580308992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (470580776140800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-142277156536320 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-186026463068160 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (64372793671680 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (57280875724800 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-21838333870080 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-13604207984640 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (5575199293440 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (2453809397760 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-1062587105280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-328635187200 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (148494417920 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (31646351360 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-14777172480 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-2092006400 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (1001701888 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (88602624 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-43224544 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-2153536 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (1064448 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (24640 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-12278 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-84 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (42 : ℤ)

def fixedRowDCoeff_46 (n : ℕ) : ℤ :=
    (if 21 = n then (2199023255552 : ℤ) else 0) +
    (if 22 = n then (-4398046511104 : ℤ) else 0) +
    (if 23 = n then (-19791209299968 : ℤ) else 0) +
    (if 24 = n then (43980465111040 : ℤ) else 0) +
    (if 25 = n then (79852031967232 : ℤ) else 0) +
    (if 26 = n then (-203684529045504 : ℤ) else 0) +
    (if 27 = n then (-188016488349696 : ℤ) else 0) +
    (if 28 = n then (579717505744896 : ℤ) else 0) +
    (if 29 = n then (277463477256192 : ℤ) else 0) +
    (if 30 = n then (-1134644460257280 : ℤ) else 0) +
    (if 31 = n then (-242261925298176 : ℤ) else 0) +
    (if 32 = n then (1619168310853632 : ℤ) else 0) +
    (if 33 = n then (61843234095104 : ℤ) else 0) +
    (if 34 = n then (-1742854779043840 : ℤ) else 0) +
    (if 35 = n then (149387552489472 : ℤ) else 0) +
    (if 36 = n then (1444079674064896 : ℤ) else 0) +
    (if 37 = n then (-256164868653056 : ℤ) else 0) +
    (if 38 = n then (-931749936758784 : ℤ) else 0) +
    (if 39 = n then (230584580308992 : ℤ) else 0) +
    (if 40 = n then (470580776140800 : ℤ) else 0) +
    (if 41 = n then (-142277156536320 : ℤ) else 0) +
    (if 42 = n then (-186026463068160 : ℤ) else 0) +
    (if 43 = n then (64372793671680 : ℤ) else 0) +
    (if 44 = n then (57280875724800 : ℤ) else 0) +
    (if 45 = n then (-21838333870080 : ℤ) else 0) +
    (if 46 = n then (-13604207984640 : ℤ) else 0) +
    (if 47 = n then (5575199293440 : ℤ) else 0) +
    (if 48 = n then (2453809397760 : ℤ) else 0) +
    (if 49 = n then (-1062587105280 : ℤ) else 0) +
    (if 50 = n then (-328635187200 : ℤ) else 0) +
    (if 51 = n then (148494417920 : ℤ) else 0) +
    (if 52 = n then (31646351360 : ℤ) else 0) +
    (if 53 = n then (-14777172480 : ℤ) else 0) +
    (if 54 = n then (-2092006400 : ℤ) else 0) +
    (if 55 = n then (1001701888 : ℤ) else 0) +
    (if 56 = n then (88602624 : ℤ) else 0) +
    (if 57 = n then (-43224544 : ℤ) else 0) +
    (if 58 = n then (-2153536 : ℤ) else 0) +
    (if 59 = n then (1064448 : ℤ) else 0) +
    (if 60 = n then (24640 : ℤ) else 0) +
    (if 61 = n then (-12278 : ℤ) else 0) +
    (if 62 = n then (-84 : ℤ) else 0) +
    (if 63 = n then (42 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_46 (n : ℕ) :
    fixedRowDData_46.coeff n = fixedRowDCoeff_46 n := by
  simp only [fixedRowDData_46, fixedRowDCoeff_46, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_46 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_46 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_46, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_46 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_41 (k.val + 2) - 2 * fixedReversedUCoeff_41 (k.val + 1) + fixedReversedUCoeff_41 k.val) = fixedRowDCoeff_46 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_46 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_41 = fixedRowDData_46 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_41, fixed_rowD_typed_coeff_46]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_41, fixed_rowD_typed_coeff_46]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_41, fixed_rowD_typed_coeff_46]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_46 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_41 _ (by omega),
              fixed_reversedU_typed_tail_41 _ (by omega), fixed_reversedU_typed_tail_41 _ hn',
              fixed_rowD_typed_tail_46 _ (by omega)]
            decide

theorem fixed_rowD_typed_46 : rowD 1 46 = fixedRowDData_46 := by
  calc
    rowD 1 46 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_41 :=
      fixedTyped_rowD_of_parameters 1 46 2 63 41 (1)
        fixedChebyshevUData_41 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_41
    _ = fixedRowDData_46 := by
      rw [fixed_reversedU_typed_data_41, fixed_rowD_typed_factor_46]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.PalindromicBlockInverse
namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan





@[simp] theorem fixedMatrix_zero : fixedMatrix 0 = fixedB0 := by simp [fixedMatrix]
@[simp] theorem fixedMatrix_one : fixedMatrix 1 = fixedB0 + fixedB1 := by
  simp [fixedMatrix]
@[simp] theorem fixedMatrix_neg_one : fixedMatrix (-1) = fixedB0 - fixedB1 := by
  simp [fixedMatrix, sub_eq_add_neg]




end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan




end InternalCatalan

end



noncomputable section

namespace InternalCatalan



















open scoped BigOperators


























end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker













end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker








end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Split.IntBaseRows43
namespace OAI

namespace InternalCatalan



theorem splitBaseMod_row_45 (k : Fin 48) :
    (fixedIntegerBaseCanonical (45 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (45 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (45 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_45 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_45 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 45).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 45).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_45, fixed_rowD_typed_45]
    simp only [fixed_rowP_typed_coeff_45, fixed_rowD_typed_coeff_45,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_46 (k : Fin 48) :
    (fixedIntegerBaseCanonical (46 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (46 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (46 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_46 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_46 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 46).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 46).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_46, fixed_rowD_typed_46]
    simp only [fixed_rowP_typed_coeff_46, fixed_rowD_typed_coeff_46,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel




end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Split.Fine
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): finer groups, and the
coarser published statements recovered from them. -/

namespace OAI

namespace InternalCatalan

















theorem fixedIntegerBaseCanonical_mod101_rows_45_46 (r : Fin 49) (hr : 45 ≤ r.val ∧ r.val < 47)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  obtain ⟨r, hr'⟩ := r
  obtain ⟨hra, hrb⟩ := hr
  simp only at hra hrb
  interval_cases r
  · exact splitBaseMod_row_45 k
  · exact splitBaseMod_row_46 k
























end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (hr : 45 ≤ r.val ∧ r.val < 47)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_45_46
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_45_46 <;> assumption)

end
