-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_47_48
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T22:12:59.393317+00:00
-- url     : https://prove2.me/submissions/e0ac7808-782d-4175-9b99-04504c28837a

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

def fixedChebyshevTData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-43 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (13244 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-1218448 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (52915456 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-1322886400 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (21262392320 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-235521884160 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (1884175073280 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-11249633525760 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (51314117836800 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-181798588907520 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (505874334351360 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-1112923535572992 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (1940482062024704 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-2676526982103040 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (2901009890279424 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2439485589553152 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (1557990796689408 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-729869562413056 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (236394999971840 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-47278999994368 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (4398046511104 : ℤ)

def fixedChebyshevTData_44 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-968 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (155848 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-9974272 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (338412800 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-7038986240 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (97905899520 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-963996549120 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (6988974981120 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-38370843033600 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (162773155184640 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-541167892561920 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (1423506847825920 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-2978414327758848 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (4964023879598080 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-6573052309536768 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (6864598984556544 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-5579780992794624 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (3454150138396672 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1572301627719680 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (495879744126976 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-96757023244288 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (8796093022208 : ℤ)

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

def fixedChebyshevUData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (924 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-141680 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (8614144 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-276883200 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (5439216640 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-71204290560 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (657270374400 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-4447529533440 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (22673679974400 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-88785357373440 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (270583946280960 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-647048567193600 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (1218442224992256 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-1805099592581120 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (2091425734852608 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-1872163359424512 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (1268132043816960 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-628027297890304 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (214404767416320 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-45079976738816 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (4398046511104 : ℤ)

def fixedChebyshevUData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-44 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (14168 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-1360128 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (61529600 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-1599769600 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (26701608960 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-306726174720 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (2541445447680 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-15697163059200 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (73987797811200 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-270583946280960 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (776458280632320 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-1759972102766592 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (3158924287016960 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-4481626574684160 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (4992435625132032 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-4311648948977664 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2826122840506368 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-1357896860303360 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (450799767388160 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-92358976733184 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (8796093022208 : ℤ)

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

theorem fixed_chebyshevT_typed_43 :
    Chebyshev.T ℤ 43 = fixedChebyshevTData_43 := by
  calc
    Chebyshev.T ℤ 43 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_42 - fixedChebyshevTData_41 :=
      fixedTyped_chebyshevT_link 41 42 43 fixedChebyshevTData_41 fixedChebyshevTData_42
        (by decide) (by decide) fixed_chebyshevT_typed_41 fixed_chebyshevT_typed_42
    _ = fixedChebyshevTData_43 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_42, fixedChebyshevTData_41, fixedChebyshevTData_43, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_42, fixedChebyshevTData_41, fixedChebyshevTData_43, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 43
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 43, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 43 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_44 :
    Chebyshev.T ℤ 44 = fixedChebyshevTData_44 := by
  calc
    Chebyshev.T ℤ 44 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_43 - fixedChebyshevTData_42 :=
      fixedTyped_chebyshevT_link 42 43 44 fixedChebyshevTData_42 fixedChebyshevTData_43
        (by decide) (by decide) fixed_chebyshevT_typed_42 fixed_chebyshevT_typed_43
    _ = fixedChebyshevTData_44 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_43, fixedChebyshevTData_42, fixedChebyshevTData_44, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_43, fixedChebyshevTData_42, fixedChebyshevTData_44, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 44
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 44, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 44 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_42 :
    Chebyshev.U ℤ 42 = fixedChebyshevUData_42 := by
  calc
    Chebyshev.U ℤ 42 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_41 - fixedChebyshevUData_40 :=
      fixedTyped_chebyshevU_link 40 41 42 fixedChebyshevUData_40 fixedChebyshevUData_41
        (by decide) (by decide) fixed_chebyshevU_typed_40 fixed_chebyshevU_typed_41
    _ = fixedChebyshevUData_42 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_41, fixedChebyshevUData_40, fixedChebyshevUData_42, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_41, fixedChebyshevUData_40, fixedChebyshevUData_42, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 42
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 42, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 42 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_43 :
    Chebyshev.U ℤ 43 = fixedChebyshevUData_43 := by
  calc
    Chebyshev.U ℤ 43 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_42 - fixedChebyshevUData_41 :=
      fixedTyped_chebyshevU_link 41 42 43 fixedChebyshevUData_41 fixedChebyshevUData_42
        (by decide) (by decide) fixed_chebyshevU_typed_41 fixed_chebyshevU_typed_42
    _ = fixedChebyshevUData_43 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_42, fixedChebyshevUData_41, fixedChebyshevUData_43, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_42, fixedChebyshevUData_41, fixedChebyshevUData_43, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 43
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 43, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 43 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

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
















def fixedReversedTData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-43 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (13244 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1218448 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (52915456 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1322886400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (21262392320 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-235521884160 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1884175073280 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-11249633525760 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (51314117836800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-181798588907520 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (505874334351360 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-1112923535572992 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (1940482062024704 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2676526982103040 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (2901009890279424 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-2439485589553152 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (1557990796689408 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-729869562413056 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (236394999971840 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-47278999994368 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (4398046511104 : ℤ)

def fixedReversedTCoeff_43 (n : ℕ) : ℤ :=
    (if 61 = n then (-43 : ℤ) else 0) +
    (if 59 = n then (13244 : ℤ) else 0) +
    (if 57 = n then (-1218448 : ℤ) else 0) +
    (if 55 = n then (52915456 : ℤ) else 0) +
    (if 53 = n then (-1322886400 : ℤ) else 0) +
    (if 51 = n then (21262392320 : ℤ) else 0) +
    (if 49 = n then (-235521884160 : ℤ) else 0) +
    (if 47 = n then (1884175073280 : ℤ) else 0) +
    (if 45 = n then (-11249633525760 : ℤ) else 0) +
    (if 43 = n then (51314117836800 : ℤ) else 0) +
    (if 41 = n then (-181798588907520 : ℤ) else 0) +
    (if 39 = n then (505874334351360 : ℤ) else 0) +
    (if 37 = n then (-1112923535572992 : ℤ) else 0) +
    (if 35 = n then (1940482062024704 : ℤ) else 0) +
    (if 33 = n then (-2676526982103040 : ℤ) else 0) +
    (if 31 = n then (2901009890279424 : ℤ) else 0) +
    (if 29 = n then (-2439485589553152 : ℤ) else 0) +
    (if 27 = n then (1557990796689408 : ℤ) else 0) +
    (if 25 = n then (-729869562413056 : ℤ) else 0) +
    (if 23 = n then (236394999971840 : ℤ) else 0) +
    (if 21 = n then (-47278999994368 : ℤ) else 0) +
    (if 19 = n then (4398046511104 : ℤ) else 0)

theorem fixed_reversedT_typed_data_43 : reversedRow 63 fixedChebyshevTData_43 = fixedReversedTData_43 := by
  simp only [fixedChebyshevTData_43, fixedReversedTData_43, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-43 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (13244 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-1218448 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (52915456 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-1322886400 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (21262392320 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-235521884160 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (1884175073280 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-11249633525760 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (51314117836800 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-181798588907520 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (505874334351360 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-1112923535572992 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (1940482062024704 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-2676526982103040 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (2901009890279424 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-2439485589553152 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (1557990796689408 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (-729869562413056 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (236394999971840 : ℤ) 39 (by decide),
    fixedTyped_reversedRow_monomial (-47278999994368 : ℤ) 41 (by decide),
    fixedTyped_reversedRow_monomial (4398046511104 : ℤ) 43 (by decide)]

theorem fixed_reversedT_typed_coeff_43 (n : ℕ) :
    fixedReversedTData_43.coeff n = fixedReversedTCoeff_43 n := by
  simp only [fixedReversedTData_43, fixedReversedTCoeff_43, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_43 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_43 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_43, if_neg, add_zero]

def fixedReversedTData_44 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-968 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (155848 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-9974272 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (338412800 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-7038986240 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (97905899520 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-963996549120 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (6988974981120 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-38370843033600 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (162773155184640 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-541167892561920 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (1423506847825920 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-2978414327758848 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (4964023879598080 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-6573052309536768 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (6864598984556544 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-5579780992794624 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (3454150138396672 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-1572301627719680 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (495879744126976 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-96757023244288 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (8796093022208 : ℤ)

def fixedReversedTCoeff_44 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-968 : ℤ) else 0) +
    (if 58 = n then (155848 : ℤ) else 0) +
    (if 56 = n then (-9974272 : ℤ) else 0) +
    (if 54 = n then (338412800 : ℤ) else 0) +
    (if 52 = n then (-7038986240 : ℤ) else 0) +
    (if 50 = n then (97905899520 : ℤ) else 0) +
    (if 48 = n then (-963996549120 : ℤ) else 0) +
    (if 46 = n then (6988974981120 : ℤ) else 0) +
    (if 44 = n then (-38370843033600 : ℤ) else 0) +
    (if 42 = n then (162773155184640 : ℤ) else 0) +
    (if 40 = n then (-541167892561920 : ℤ) else 0) +
    (if 38 = n then (1423506847825920 : ℤ) else 0) +
    (if 36 = n then (-2978414327758848 : ℤ) else 0) +
    (if 34 = n then (4964023879598080 : ℤ) else 0) +
    (if 32 = n then (-6573052309536768 : ℤ) else 0) +
    (if 30 = n then (6864598984556544 : ℤ) else 0) +
    (if 28 = n then (-5579780992794624 : ℤ) else 0) +
    (if 26 = n then (3454150138396672 : ℤ) else 0) +
    (if 24 = n then (-1572301627719680 : ℤ) else 0) +
    (if 22 = n then (495879744126976 : ℤ) else 0) +
    (if 20 = n then (-96757023244288 : ℤ) else 0) +
    (if 18 = n then (8796093022208 : ℤ) else 0)

theorem fixed_reversedT_typed_data_44 : reversedRow 63 fixedChebyshevTData_44 = fixedReversedTData_44 := by
  simp only [fixedChebyshevTData_44, fixedReversedTData_44, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-968 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (155848 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-9974272 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (338412800 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-7038986240 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (97905899520 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-963996549120 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (6988974981120 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-38370843033600 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (162773155184640 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-541167892561920 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (1423506847825920 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-2978414327758848 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (4964023879598080 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-6573052309536768 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (6864598984556544 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-5579780992794624 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (3454150138396672 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (-1572301627719680 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (495879744126976 : ℤ) 40 (by decide),
    fixedTyped_reversedRow_monomial (-96757023244288 : ℤ) 42 (by decide),
    fixedTyped_reversedRow_monomial (8796093022208 : ℤ) 44 (by decide)]

theorem fixed_reversedT_typed_coeff_44 (n : ℕ) :
    fixedReversedTData_44.coeff n = fixedReversedTCoeff_44 n := by
  simp only [fixedReversedTData_44, fixedReversedTCoeff_44, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_44 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_44 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_44, if_neg, add_zero]

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











def fixedReversedUData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (924 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-141680 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (8614144 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-276883200 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (5439216640 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-71204290560 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (657270374400 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-4447529533440 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (22673679974400 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-88785357373440 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (270583946280960 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-647048567193600 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1218442224992256 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1805099592581120 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (2091425734852608 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-1872163359424512 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (1268132043816960 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-628027297890304 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (214404767416320 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-45079976738816 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (4398046511104 : ℤ)

def fixedReversedUCoeff_42 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (924 : ℤ) else 0) +
    (if 58 = n then (-141680 : ℤ) else 0) +
    (if 56 = n then (8614144 : ℤ) else 0) +
    (if 54 = n then (-276883200 : ℤ) else 0) +
    (if 52 = n then (5439216640 : ℤ) else 0) +
    (if 50 = n then (-71204290560 : ℤ) else 0) +
    (if 48 = n then (657270374400 : ℤ) else 0) +
    (if 46 = n then (-4447529533440 : ℤ) else 0) +
    (if 44 = n then (22673679974400 : ℤ) else 0) +
    (if 42 = n then (-88785357373440 : ℤ) else 0) +
    (if 40 = n then (270583946280960 : ℤ) else 0) +
    (if 38 = n then (-647048567193600 : ℤ) else 0) +
    (if 36 = n then (1218442224992256 : ℤ) else 0) +
    (if 34 = n then (-1805099592581120 : ℤ) else 0) +
    (if 32 = n then (2091425734852608 : ℤ) else 0) +
    (if 30 = n then (-1872163359424512 : ℤ) else 0) +
    (if 28 = n then (1268132043816960 : ℤ) else 0) +
    (if 26 = n then (-628027297890304 : ℤ) else 0) +
    (if 24 = n then (214404767416320 : ℤ) else 0) +
    (if 22 = n then (-45079976738816 : ℤ) else 0) +
    (if 20 = n then (4398046511104 : ℤ) else 0)

theorem fixed_reversedU_typed_data_42 : reversedRow 63 fixedChebyshevUData_42 = fixedReversedUData_42 := by
  simp only [fixedChebyshevUData_42, fixedReversedUData_42, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (924 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-141680 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (8614144 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-276883200 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (5439216640 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-71204290560 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (657270374400 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-4447529533440 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (22673679974400 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-88785357373440 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (270583946280960 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-647048567193600 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (1218442224992256 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-1805099592581120 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (2091425734852608 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-1872163359424512 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (1268132043816960 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (-628027297890304 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (214404767416320 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (-45079976738816 : ℤ) 40 (by decide),
    fixedTyped_reversedRow_monomial (4398046511104 : ℤ) 42 (by decide)]

theorem fixed_reversedU_typed_coeff_42 (n : ℕ) :
    fixedReversedUData_42.coeff n = fixedReversedUCoeff_42 n := by
  simp only [fixedReversedUData_42, fixedReversedUCoeff_42, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_42 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_42 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_42, if_neg, add_zero]

def fixedReversedUData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-44 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (14168 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1360128 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (61529600 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1599769600 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (26701608960 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-306726174720 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2541445447680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-15697163059200 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (73987797811200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-270583946280960 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (776458280632320 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-1759972102766592 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (3158924287016960 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-4481626574684160 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (4992435625132032 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-4311648948977664 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (2826122840506368 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-1357896860303360 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (450799767388160 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-92358976733184 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (8796093022208 : ℤ)

def fixedReversedUCoeff_43 (n : ℕ) : ℤ :=
    (if 61 = n then (-44 : ℤ) else 0) +
    (if 59 = n then (14168 : ℤ) else 0) +
    (if 57 = n then (-1360128 : ℤ) else 0) +
    (if 55 = n then (61529600 : ℤ) else 0) +
    (if 53 = n then (-1599769600 : ℤ) else 0) +
    (if 51 = n then (26701608960 : ℤ) else 0) +
    (if 49 = n then (-306726174720 : ℤ) else 0) +
    (if 47 = n then (2541445447680 : ℤ) else 0) +
    (if 45 = n then (-15697163059200 : ℤ) else 0) +
    (if 43 = n then (73987797811200 : ℤ) else 0) +
    (if 41 = n then (-270583946280960 : ℤ) else 0) +
    (if 39 = n then (776458280632320 : ℤ) else 0) +
    (if 37 = n then (-1759972102766592 : ℤ) else 0) +
    (if 35 = n then (3158924287016960 : ℤ) else 0) +
    (if 33 = n then (-4481626574684160 : ℤ) else 0) +
    (if 31 = n then (4992435625132032 : ℤ) else 0) +
    (if 29 = n then (-4311648948977664 : ℤ) else 0) +
    (if 27 = n then (2826122840506368 : ℤ) else 0) +
    (if 25 = n then (-1357896860303360 : ℤ) else 0) +
    (if 23 = n then (450799767388160 : ℤ) else 0) +
    (if 21 = n then (-92358976733184 : ℤ) else 0) +
    (if 19 = n then (8796093022208 : ℤ) else 0)

theorem fixed_reversedU_typed_data_43 : reversedRow 63 fixedChebyshevUData_43 = fixedReversedUData_43 := by
  simp only [fixedChebyshevUData_43, fixedReversedUData_43, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-44 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (14168 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-1360128 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (61529600 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-1599769600 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (26701608960 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-306726174720 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (2541445447680 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-15697163059200 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (73987797811200 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-270583946280960 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (776458280632320 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-1759972102766592 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (3158924287016960 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-4481626574684160 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (4992435625132032 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-4311648948977664 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (2826122840506368 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (-1357896860303360 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (450799767388160 : ℤ) 39 (by decide),
    fixedTyped_reversedRow_monomial (-92358976733184 : ℤ) 41 (by decide),
    fixedTyped_reversedRow_monomial (8796093022208 : ℤ) 43 (by decide)]

theorem fixed_reversedU_typed_coeff_43 (n : ℕ) :
    fixedReversedUData_43.coeff n = fixedReversedUCoeff_43 n := by
  simp only [fixedReversedUData_43, fixedReversedUCoeff_43, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_43 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_43 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_43, if_neg, add_zero]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow47
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_47 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 19 (4398046511104 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-8796093022208 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-42880953483264 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (94557999988736 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (189115999977472 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-472789999943680 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-493474562441216 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (1459739124826112 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (828121234276352 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-3115981593378816 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-881494792863744 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (4878971179106304 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (461524300726272 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-5802019780558848 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (224482908176384 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (5353053964206080 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-736044920078336 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-3880964124049408 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (827558526451712 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (2225847071145984 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-607049201221632 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-1011748668702720 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (324075745443840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (363597177815040 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-130484471070720 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-102628235673600 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (40064484311040 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (22499267051520 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-9365458452480 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-3768350146560 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1648653189120 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (471043768320 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-214259491840 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-42524784640 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (19939505920 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (2645772800 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1269970944 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-105830912 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (51697008 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2436896 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1205204 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-26488 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (13201 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (86 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-43 : ℤ)

def fixedRowPCoeff_47 (n : ℕ) : ℤ :=
    (if 19 = n then (4398046511104 : ℤ) else 0) +
    (if 20 = n then (-8796093022208 : ℤ) else 0) +
    (if 21 = n then (-42880953483264 : ℤ) else 0) +
    (if 22 = n then (94557999988736 : ℤ) else 0) +
    (if 23 = n then (189115999977472 : ℤ) else 0) +
    (if 24 = n then (-472789999943680 : ℤ) else 0) +
    (if 25 = n then (-493474562441216 : ℤ) else 0) +
    (if 26 = n then (1459739124826112 : ℤ) else 0) +
    (if 27 = n then (828121234276352 : ℤ) else 0) +
    (if 28 = n then (-3115981593378816 : ℤ) else 0) +
    (if 29 = n then (-881494792863744 : ℤ) else 0) +
    (if 30 = n then (4878971179106304 : ℤ) else 0) +
    (if 31 = n then (461524300726272 : ℤ) else 0) +
    (if 32 = n then (-5802019780558848 : ℤ) else 0) +
    (if 33 = n then (224482908176384 : ℤ) else 0) +
    (if 34 = n then (5353053964206080 : ℤ) else 0) +
    (if 35 = n then (-736044920078336 : ℤ) else 0) +
    (if 36 = n then (-3880964124049408 : ℤ) else 0) +
    (if 37 = n then (827558526451712 : ℤ) else 0) +
    (if 38 = n then (2225847071145984 : ℤ) else 0) +
    (if 39 = n then (-607049201221632 : ℤ) else 0) +
    (if 40 = n then (-1011748668702720 : ℤ) else 0) +
    (if 41 = n then (324075745443840 : ℤ) else 0) +
    (if 42 = n then (363597177815040 : ℤ) else 0) +
    (if 43 = n then (-130484471070720 : ℤ) else 0) +
    (if 44 = n then (-102628235673600 : ℤ) else 0) +
    (if 45 = n then (40064484311040 : ℤ) else 0) +
    (if 46 = n then (22499267051520 : ℤ) else 0) +
    (if 47 = n then (-9365458452480 : ℤ) else 0) +
    (if 48 = n then (-3768350146560 : ℤ) else 0) +
    (if 49 = n then (1648653189120 : ℤ) else 0) +
    (if 50 = n then (471043768320 : ℤ) else 0) +
    (if 51 = n then (-214259491840 : ℤ) else 0) +
    (if 52 = n then (-42524784640 : ℤ) else 0) +
    (if 53 = n then (19939505920 : ℤ) else 0) +
    (if 54 = n then (2645772800 : ℤ) else 0) +
    (if 55 = n then (-1269970944 : ℤ) else 0) +
    (if 56 = n then (-105830912 : ℤ) else 0) +
    (if 57 = n then (51697008 : ℤ) else 0) +
    (if 58 = n then (2436896 : ℤ) else 0) +
    (if 59 = n then (-1205204 : ℤ) else 0) +
    (if 60 = n then (-26488 : ℤ) else 0) +
    (if 61 = n then (13201 : ℤ) else 0) +
    (if 62 = n then (86 : ℤ) else 0) +
    (if 63 = n then (-43 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_47 (n : ℕ) :
    fixedRowPData_47.coeff n = fixedRowPCoeff_47 n := by
  simp only [fixedRowPData_47, fixedRowPCoeff_47, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_47 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_47 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_47, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_47 : ∀ k : Fin 63,
    fixedReversedTCoeff_43 (k.val + 2) - 2 * fixedReversedTCoeff_43 (k.val + 1) + fixedReversedTCoeff_43 k.val = fixedRowPCoeff_47 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_47 :
    (1 - X) ^ 2 * fixedReversedTData_43 = fixedRowPData_47 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_43, fixed_rowP_typed_coeff_47]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_43, fixed_rowP_typed_coeff_47]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_43, fixed_rowP_typed_coeff_47]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_47 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_43 _ (by omega),
              fixed_reversedT_typed_tail_43 _ (by omega), fixed_reversedT_typed_tail_43 _ hn',
              fixed_rowP_typed_tail_47 _ (by omega)]
            decide

theorem fixed_rowP_typed_47 : rowP 1 47 = fixedRowPData_47 := by
  calc
    rowP 1 47 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_43 :=
      fixedTyped_rowP_of_parameters 1 47 2 63 43 fixedChebyshevTData_43
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_43
    _ = fixedRowPData_47 := by
      rw [fixed_reversedT_typed_data_43, fixed_rowP_typed_factor_47]

def fixedRowDData_47 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 20 (4398046511104 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-8796093022208 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-40681930227712 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (90159953477632 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (169324790677504 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-428809534832640 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-413622530473984 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (1256054595780608 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (640104745926656 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-2536264087633920 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-604031315607552 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (3744326718849024 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (219262375428096 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-4182851469705216 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (286326142271488 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (3610199185162240 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-586657367588864 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2436884449984512 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (571393657798656 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (1294097134387200 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-376464620912640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-541167892561920 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (181798588907520 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (177570714746880 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-66111677399040 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-45347359948800 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (18226150440960 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (8895059066880 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-3790259159040 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-1314540748800 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (586066083840 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (142408581120 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-65765073920 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-10878433280 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (5162333440 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (553766400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-268269056 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-17228288 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (8472464 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (283360 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-140756 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1848 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (923 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_47 (n : ℕ) : ℤ :=
    (if 20 = n then (4398046511104 : ℤ) else 0) +
    (if 21 = n then (-8796093022208 : ℤ) else 0) +
    (if 22 = n then (-40681930227712 : ℤ) else 0) +
    (if 23 = n then (90159953477632 : ℤ) else 0) +
    (if 24 = n then (169324790677504 : ℤ) else 0) +
    (if 25 = n then (-428809534832640 : ℤ) else 0) +
    (if 26 = n then (-413622530473984 : ℤ) else 0) +
    (if 27 = n then (1256054595780608 : ℤ) else 0) +
    (if 28 = n then (640104745926656 : ℤ) else 0) +
    (if 29 = n then (-2536264087633920 : ℤ) else 0) +
    (if 30 = n then (-604031315607552 : ℤ) else 0) +
    (if 31 = n then (3744326718849024 : ℤ) else 0) +
    (if 32 = n then (219262375428096 : ℤ) else 0) +
    (if 33 = n then (-4182851469705216 : ℤ) else 0) +
    (if 34 = n then (286326142271488 : ℤ) else 0) +
    (if 35 = n then (3610199185162240 : ℤ) else 0) +
    (if 36 = n then (-586657367588864 : ℤ) else 0) +
    (if 37 = n then (-2436884449984512 : ℤ) else 0) +
    (if 38 = n then (571393657798656 : ℤ) else 0) +
    (if 39 = n then (1294097134387200 : ℤ) else 0) +
    (if 40 = n then (-376464620912640 : ℤ) else 0) +
    (if 41 = n then (-541167892561920 : ℤ) else 0) +
    (if 42 = n then (181798588907520 : ℤ) else 0) +
    (if 43 = n then (177570714746880 : ℤ) else 0) +
    (if 44 = n then (-66111677399040 : ℤ) else 0) +
    (if 45 = n then (-45347359948800 : ℤ) else 0) +
    (if 46 = n then (18226150440960 : ℤ) else 0) +
    (if 47 = n then (8895059066880 : ℤ) else 0) +
    (if 48 = n then (-3790259159040 : ℤ) else 0) +
    (if 49 = n then (-1314540748800 : ℤ) else 0) +
    (if 50 = n then (586066083840 : ℤ) else 0) +
    (if 51 = n then (142408581120 : ℤ) else 0) +
    (if 52 = n then (-65765073920 : ℤ) else 0) +
    (if 53 = n then (-10878433280 : ℤ) else 0) +
    (if 54 = n then (5162333440 : ℤ) else 0) +
    (if 55 = n then (553766400 : ℤ) else 0) +
    (if 56 = n then (-268269056 : ℤ) else 0) +
    (if 57 = n then (-17228288 : ℤ) else 0) +
    (if 58 = n then (8472464 : ℤ) else 0) +
    (if 59 = n then (283360 : ℤ) else 0) +
    (if 60 = n then (-140756 : ℤ) else 0) +
    (if 61 = n then (-1848 : ℤ) else 0) +
    (if 62 = n then (923 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_47 (n : ℕ) :
    fixedRowDData_47.coeff n = fixedRowDCoeff_47 n := by
  simp only [fixedRowDData_47, fixedRowDCoeff_47, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_47 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_47 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_47, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_47 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_42 (k.val + 2) - 2 * fixedReversedUCoeff_42 (k.val + 1) + fixedReversedUCoeff_42 k.val) = fixedRowDCoeff_47 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_47 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_42 = fixedRowDData_47 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_42, fixed_rowD_typed_coeff_47]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_42, fixed_rowD_typed_coeff_47]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_42, fixed_rowD_typed_coeff_47]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_47 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_42 _ (by omega),
              fixed_reversedU_typed_tail_42 _ (by omega), fixed_reversedU_typed_tail_42 _ hn',
              fixed_rowD_typed_tail_47 _ (by omega)]
            decide

theorem fixed_rowD_typed_47 : rowD 1 47 = fixedRowDData_47 := by
  calc
    rowD 1 47 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_42 :=
      fixedTyped_rowD_of_parameters 1 47 2 63 42 (1)
        fixedChebyshevUData_42 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_42
    _ = fixedRowDData_47 := by
      rw [fixed_reversedU_typed_data_42, fixed_rowD_typed_factor_47]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow48
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_48 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 18 (8796093022208 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-17592186044416 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-87960930222080 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (193514046488576 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (399122720882688 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-991759488253952 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-1076421883592704 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (3144603255439360 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (1881848510676992 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-6908300276793344 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-2125630854397952 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (11159561985589248 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (1284817991761920 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-13729197969113088 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (291546675019776 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (13146104619073536 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1609028429938688 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-9928047759196160 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1985609551839232 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (5956828655517696 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1554907479932928 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-2847013695651840 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (882338955264000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (1082335785123840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-378394737377280 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-325546310369280 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (124402312151040 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (76741686067200 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-31381868052480 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-13977949962240 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (6024978432000 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1927993098240 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-866090649600 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-195811799040 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (90866913280 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (14077972480 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-6700573440 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-676825600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (328438528 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (19948544 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-9818424 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-311696 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (154880 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1936 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-967 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_48 (n : ℕ) : ℤ :=
    (if 18 = n then (8796093022208 : ℤ) else 0) +
    (if 19 = n then (-17592186044416 : ℤ) else 0) +
    (if 20 = n then (-87960930222080 : ℤ) else 0) +
    (if 21 = n then (193514046488576 : ℤ) else 0) +
    (if 22 = n then (399122720882688 : ℤ) else 0) +
    (if 23 = n then (-991759488253952 : ℤ) else 0) +
    (if 24 = n then (-1076421883592704 : ℤ) else 0) +
    (if 25 = n then (3144603255439360 : ℤ) else 0) +
    (if 26 = n then (1881848510676992 : ℤ) else 0) +
    (if 27 = n then (-6908300276793344 : ℤ) else 0) +
    (if 28 = n then (-2125630854397952 : ℤ) else 0) +
    (if 29 = n then (11159561985589248 : ℤ) else 0) +
    (if 30 = n then (1284817991761920 : ℤ) else 0) +
    (if 31 = n then (-13729197969113088 : ℤ) else 0) +
    (if 32 = n then (291546675019776 : ℤ) else 0) +
    (if 33 = n then (13146104619073536 : ℤ) else 0) +
    (if 34 = n then (-1609028429938688 : ℤ) else 0) +
    (if 35 = n then (-9928047759196160 : ℤ) else 0) +
    (if 36 = n then (1985609551839232 : ℤ) else 0) +
    (if 37 = n then (5956828655517696 : ℤ) else 0) +
    (if 38 = n then (-1554907479932928 : ℤ) else 0) +
    (if 39 = n then (-2847013695651840 : ℤ) else 0) +
    (if 40 = n then (882338955264000 : ℤ) else 0) +
    (if 41 = n then (1082335785123840 : ℤ) else 0) +
    (if 42 = n then (-378394737377280 : ℤ) else 0) +
    (if 43 = n then (-325546310369280 : ℤ) else 0) +
    (if 44 = n then (124402312151040 : ℤ) else 0) +
    (if 45 = n then (76741686067200 : ℤ) else 0) +
    (if 46 = n then (-31381868052480 : ℤ) else 0) +
    (if 47 = n then (-13977949962240 : ℤ) else 0) +
    (if 48 = n then (6024978432000 : ℤ) else 0) +
    (if 49 = n then (1927993098240 : ℤ) else 0) +
    (if 50 = n then (-866090649600 : ℤ) else 0) +
    (if 51 = n then (-195811799040 : ℤ) else 0) +
    (if 52 = n then (90866913280 : ℤ) else 0) +
    (if 53 = n then (14077972480 : ℤ) else 0) +
    (if 54 = n then (-6700573440 : ℤ) else 0) +
    (if 55 = n then (-676825600 : ℤ) else 0) +
    (if 56 = n then (328438528 : ℤ) else 0) +
    (if 57 = n then (19948544 : ℤ) else 0) +
    (if 58 = n then (-9818424 : ℤ) else 0) +
    (if 59 = n then (-311696 : ℤ) else 0) +
    (if 60 = n then (154880 : ℤ) else 0) +
    (if 61 = n then (1936 : ℤ) else 0) +
    (if 62 = n then (-967 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_48 (n : ℕ) :
    fixedRowPData_48.coeff n = fixedRowPCoeff_48 n := by
  simp only [fixedRowPData_48, fixedRowPCoeff_48, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_48 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_48 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_48, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_48 : ∀ k : Fin 63,
    fixedReversedTCoeff_44 (k.val + 2) - 2 * fixedReversedTCoeff_44 (k.val + 1) + fixedReversedTCoeff_44 k.val = fixedRowPCoeff_48 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_48 :
    (1 - X) ^ 2 * fixedReversedTData_44 = fixedRowPData_48 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_44, fixed_rowP_typed_coeff_48]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_44, fixed_rowP_typed_coeff_48]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_44, fixed_rowP_typed_coeff_48]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_48 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_44 _ (by omega),
              fixed_reversedT_typed_tail_44 _ (by omega), fixed_reversedT_typed_tail_44 _ hn',
              fixed_rowP_typed_tail_48 _ (by omega)]
            decide

theorem fixed_rowP_typed_48 : rowP 1 48 = fixedRowPData_48 := by
  calc
    rowP 1 48 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_44 :=
      fixedTyped_rowP_of_parameters 1 48 2 63 44 fixedChebyshevTData_44
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_44
    _ = fixedRowPData_48 := by
      rw [fixed_reversedT_typed_data_44, fixed_rowP_typed_factor_48]

def fixedRowDData_48 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 19 (8796093022208 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-17592186044416 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-83562883710976 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (184717953466368 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (358440790654976 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-901599534776320 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-907097092915200 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (2715793720606720 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (1468225980203008 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-5652245681012736 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-1485526108471296 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (8623297897955328 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (680786676154368 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-9984871250264064 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (510809050447872 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (8963253149368320 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-1322702287667200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-6317848574033920 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (1398952184250368 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (3519944205533184 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-983513822134272 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-1552916561264640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (505874334351360 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (541167892561920 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-196596148469760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-147975595622400 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (58290634752000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (31394326118400 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-13155717611520 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-5082890895360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (2234719272960 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (613452349440 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-280024565760 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-53403217920 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (25101839360 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (3199539200 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1538240000 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-123059200 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (60169472 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2720256 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1345960 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-28336 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (14124 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (88 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-44 : ℤ)

def fixedRowDCoeff_48 (n : ℕ) : ℤ :=
    (if 19 = n then (8796093022208 : ℤ) else 0) +
    (if 20 = n then (-17592186044416 : ℤ) else 0) +
    (if 21 = n then (-83562883710976 : ℤ) else 0) +
    (if 22 = n then (184717953466368 : ℤ) else 0) +
    (if 23 = n then (358440790654976 : ℤ) else 0) +
    (if 24 = n then (-901599534776320 : ℤ) else 0) +
    (if 25 = n then (-907097092915200 : ℤ) else 0) +
    (if 26 = n then (2715793720606720 : ℤ) else 0) +
    (if 27 = n then (1468225980203008 : ℤ) else 0) +
    (if 28 = n then (-5652245681012736 : ℤ) else 0) +
    (if 29 = n then (-1485526108471296 : ℤ) else 0) +
    (if 30 = n then (8623297897955328 : ℤ) else 0) +
    (if 31 = n then (680786676154368 : ℤ) else 0) +
    (if 32 = n then (-9984871250264064 : ℤ) else 0) +
    (if 33 = n then (510809050447872 : ℤ) else 0) +
    (if 34 = n then (8963253149368320 : ℤ) else 0) +
    (if 35 = n then (-1322702287667200 : ℤ) else 0) +
    (if 36 = n then (-6317848574033920 : ℤ) else 0) +
    (if 37 = n then (1398952184250368 : ℤ) else 0) +
    (if 38 = n then (3519944205533184 : ℤ) else 0) +
    (if 39 = n then (-983513822134272 : ℤ) else 0) +
    (if 40 = n then (-1552916561264640 : ℤ) else 0) +
    (if 41 = n then (505874334351360 : ℤ) else 0) +
    (if 42 = n then (541167892561920 : ℤ) else 0) +
    (if 43 = n then (-196596148469760 : ℤ) else 0) +
    (if 44 = n then (-147975595622400 : ℤ) else 0) +
    (if 45 = n then (58290634752000 : ℤ) else 0) +
    (if 46 = n then (31394326118400 : ℤ) else 0) +
    (if 47 = n then (-13155717611520 : ℤ) else 0) +
    (if 48 = n then (-5082890895360 : ℤ) else 0) +
    (if 49 = n then (2234719272960 : ℤ) else 0) +
    (if 50 = n then (613452349440 : ℤ) else 0) +
    (if 51 = n then (-280024565760 : ℤ) else 0) +
    (if 52 = n then (-53403217920 : ℤ) else 0) +
    (if 53 = n then (25101839360 : ℤ) else 0) +
    (if 54 = n then (3199539200 : ℤ) else 0) +
    (if 55 = n then (-1538240000 : ℤ) else 0) +
    (if 56 = n then (-123059200 : ℤ) else 0) +
    (if 57 = n then (60169472 : ℤ) else 0) +
    (if 58 = n then (2720256 : ℤ) else 0) +
    (if 59 = n then (-1345960 : ℤ) else 0) +
    (if 60 = n then (-28336 : ℤ) else 0) +
    (if 61 = n then (14124 : ℤ) else 0) +
    (if 62 = n then (88 : ℤ) else 0) +
    (if 63 = n then (-44 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_48 (n : ℕ) :
    fixedRowDData_48.coeff n = fixedRowDCoeff_48 n := by
  simp only [fixedRowDData_48, fixedRowDCoeff_48, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_48 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_48 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_48, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_48 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_43 (k.val + 2) - 2 * fixedReversedUCoeff_43 (k.val + 1) + fixedReversedUCoeff_43 k.val) = fixedRowDCoeff_48 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_48 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_43 = fixedRowDData_48 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_43, fixed_rowD_typed_coeff_48]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_43, fixed_rowD_typed_coeff_48]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_43, fixed_rowD_typed_coeff_48]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_48 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_43 _ (by omega),
              fixed_reversedU_typed_tail_43 _ (by omega), fixed_reversedU_typed_tail_43 _ hn',
              fixed_rowD_typed_tail_48 _ (by omega)]
            decide

theorem fixed_rowD_typed_48 : rowD 1 48 = fixedRowDData_48 := by
  calc
    rowD 1 48 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_43 :=
      fixedTyped_rowD_of_parameters 1 48 2 63 43 (1)
        fixedChebyshevUData_43 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_43
    _ = fixedRowDData_48 := by
      rw [fixed_reversedU_typed_data_43, fixed_rowD_typed_factor_48]

end InternalCatalan

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





theorem splitBaseMod_row_47 (k : Fin 48) :
    (fixedIntegerBaseCanonical (47 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (47 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (47 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_47 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_47 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 47).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 47).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_47, fixed_rowD_typed_47]
    simp only [fixed_rowP_typed_coeff_47, fixed_rowD_typed_coeff_47,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_48 (k : Fin 48) :
    (fixedIntegerBaseCanonical (48 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (48 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (48 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_48 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_48 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 48).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 48).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_48, fixed_rowD_typed_48]
    simp only [fixed_rowP_typed_coeff_48, fixed_rowD_typed_coeff_48,
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


















theorem fixedIntegerBaseCanonical_mod101_rows_47_48 (r : Fin 49) (hr : 47 ≤ r.val ∧ r.val < 49)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  obtain ⟨r, hr'⟩ := r
  obtain ⟨hra, hrb⟩ := hr
  simp only at hra hrb
  interval_cases r
  · exact splitBaseMod_row_47 k
  · exact splitBaseMod_row_48 k























end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (hr : 47 ≤ r.val ∧ r.val < 49)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_47_48
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_47_48 <;> assumption)

end
