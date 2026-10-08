-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_43_44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T22:07:48.09104+00:00
-- url     : https://prove2.me/submissions/31ae5dae-3b2b-4a30-afdb-4ff1795d3d97

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

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT32To39
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan




































def fixedReversedTData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-39 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (9880 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-746928 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (26604864 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-543921664 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (7120429056 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-63901286400 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (411402567680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-1960212234240 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (7061349335040 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-19502774353920 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (41626474905600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-68822438510592 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (87841744879616 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-85678155104256 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (62646392979456 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-33221572034560 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (12060268167168 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-2680059592704 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (274877906944 : ℤ)

def fixedReversedTCoeff_39 (n : ℕ) : ℤ :=
    (if 61 = n then (-39 : ℤ) else 0) +
    (if 59 = n then (9880 : ℤ) else 0) +
    (if 57 = n then (-746928 : ℤ) else 0) +
    (if 55 = n then (26604864 : ℤ) else 0) +
    (if 53 = n then (-543921664 : ℤ) else 0) +
    (if 51 = n then (7120429056 : ℤ) else 0) +
    (if 49 = n then (-63901286400 : ℤ) else 0) +
    (if 47 = n then (411402567680 : ℤ) else 0) +
    (if 45 = n then (-1960212234240 : ℤ) else 0) +
    (if 43 = n then (7061349335040 : ℤ) else 0) +
    (if 41 = n then (-19502774353920 : ℤ) else 0) +
    (if 39 = n then (41626474905600 : ℤ) else 0) +
    (if 37 = n then (-68822438510592 : ℤ) else 0) +
    (if 35 = n then (87841744879616 : ℤ) else 0) +
    (if 33 = n then (-85678155104256 : ℤ) else 0) +
    (if 31 = n then (62646392979456 : ℤ) else 0) +
    (if 29 = n then (-33221572034560 : ℤ) else 0) +
    (if 27 = n then (12060268167168 : ℤ) else 0) +
    (if 25 = n then (-2680059592704 : ℤ) else 0) +
    (if 23 = n then (274877906944 : ℤ) else 0)

theorem fixed_reversedT_typed_data_39 : reversedRow 63 fixedChebyshevTData_39 = fixedReversedTData_39 := by
  simp only [fixedChebyshevTData_39, fixedReversedTData_39, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-39 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (9880 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-746928 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (26604864 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-543921664 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (7120429056 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-63901286400 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (411402567680 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-1960212234240 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (7061349335040 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-19502774353920 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (41626474905600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-68822438510592 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (87841744879616 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-85678155104256 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (62646392979456 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-33221572034560 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (12060268167168 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (-2680059592704 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (274877906944 : ℤ) 39 (by decide)]

theorem fixed_reversedT_typed_coeff_39 (n : ℕ) :
    fixedReversedTData_39.coeff n = fixedReversedTCoeff_39 n := by
  simp only [fixedReversedTData_39, fixedReversedTCoeff_39, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_39 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_39 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_39, if_neg, add_zero]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedU32To39
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan































def fixedReversedUData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (760 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-95760 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (4775232 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-125520384 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2008326144 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-21300428800 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (158231756800 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-854451486720 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (3440144547840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-10501493882880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (24548946739200 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-44116947763200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (60813515685888 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-63709397385216 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (49795850829824 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-28110560952320 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (10823317585920 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-2542620639232 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (274877906944 : ℤ)

def fixedReversedUCoeff_38 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (760 : ℤ) else 0) +
    (if 58 = n then (-95760 : ℤ) else 0) +
    (if 56 = n then (4775232 : ℤ) else 0) +
    (if 54 = n then (-125520384 : ℤ) else 0) +
    (if 52 = n then (2008326144 : ℤ) else 0) +
    (if 50 = n then (-21300428800 : ℤ) else 0) +
    (if 48 = n then (158231756800 : ℤ) else 0) +
    (if 46 = n then (-854451486720 : ℤ) else 0) +
    (if 44 = n then (3440144547840 : ℤ) else 0) +
    (if 42 = n then (-10501493882880 : ℤ) else 0) +
    (if 40 = n then (24548946739200 : ℤ) else 0) +
    (if 38 = n then (-44116947763200 : ℤ) else 0) +
    (if 36 = n then (60813515685888 : ℤ) else 0) +
    (if 34 = n then (-63709397385216 : ℤ) else 0) +
    (if 32 = n then (49795850829824 : ℤ) else 0) +
    (if 30 = n then (-28110560952320 : ℤ) else 0) +
    (if 28 = n then (10823317585920 : ℤ) else 0) +
    (if 26 = n then (-2542620639232 : ℤ) else 0) +
    (if 24 = n then (274877906944 : ℤ) else 0)

theorem fixed_reversedU_typed_data_38 : reversedRow 63 fixedChebyshevUData_38 = fixedReversedUData_38 := by
  simp only [fixedChebyshevUData_38, fixedReversedUData_38, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (760 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-95760 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (4775232 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-125520384 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (2008326144 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-21300428800 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (158231756800 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-854451486720 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (3440144547840 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-10501493882880 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (24548946739200 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-44116947763200 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (60813515685888 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-63709397385216 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (49795850829824 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-28110560952320 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (10823317585920 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (-2542620639232 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (274877906944 : ℤ) 38 (by decide)]

theorem fixed_reversedU_typed_coeff_38 (n : ℕ) :
    fixedReversedUData_38.coeff n = fixedReversedUCoeff_38 n := by
  simp only [fixedReversedUData_38, fixedReversedUCoeff_38, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_38 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_38 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_38, if_neg, add_zero]

def fixedReversedUData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-40 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (10640 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-842688 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (31380096 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-669442048 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (9128755200 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-85201715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (569634324480 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2814663720960 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (10501493882880 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-30004268236800 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (66175421644800 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-112939386273792 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (148655260565504 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-149387552489472 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (112442243809280 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-61332132986880 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (22883585753088 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-5222680231936 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (549755813888 : ℤ)

def fixedReversedUCoeff_39 (n : ℕ) : ℤ :=
    (if 61 = n then (-40 : ℤ) else 0) +
    (if 59 = n then (10640 : ℤ) else 0) +
    (if 57 = n then (-842688 : ℤ) else 0) +
    (if 55 = n then (31380096 : ℤ) else 0) +
    (if 53 = n then (-669442048 : ℤ) else 0) +
    (if 51 = n then (9128755200 : ℤ) else 0) +
    (if 49 = n then (-85201715200 : ℤ) else 0) +
    (if 47 = n then (569634324480 : ℤ) else 0) +
    (if 45 = n then (-2814663720960 : ℤ) else 0) +
    (if 43 = n then (10501493882880 : ℤ) else 0) +
    (if 41 = n then (-30004268236800 : ℤ) else 0) +
    (if 39 = n then (66175421644800 : ℤ) else 0) +
    (if 37 = n then (-112939386273792 : ℤ) else 0) +
    (if 35 = n then (148655260565504 : ℤ) else 0) +
    (if 33 = n then (-149387552489472 : ℤ) else 0) +
    (if 31 = n then (112442243809280 : ℤ) else 0) +
    (if 29 = n then (-61332132986880 : ℤ) else 0) +
    (if 27 = n then (22883585753088 : ℤ) else 0) +
    (if 25 = n then (-5222680231936 : ℤ) else 0) +
    (if 23 = n then (549755813888 : ℤ) else 0)

theorem fixed_reversedU_typed_data_39 : reversedRow 63 fixedChebyshevUData_39 = fixedReversedUData_39 := by
  simp only [fixedChebyshevUData_39, fixedReversedUData_39, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-40 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (10640 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-842688 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (31380096 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-669442048 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (9128755200 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-85201715200 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (569634324480 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-2814663720960 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (10501493882880 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-30004268236800 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (66175421644800 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-112939386273792 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (148655260565504 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-149387552489472 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (112442243809280 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-61332132986880 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (22883585753088 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (-5222680231936 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (549755813888 : ℤ) 39 (by decide)]

theorem fixed_reversedU_typed_coeff_39 (n : ℕ) :
    fixedReversedUData_39.coeff n = fixedReversedUCoeff_39 n := by
  simp only [fixedReversedUData_39, fixedReversedUCoeff_39, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_39 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_39 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_39, if_neg, add_zero]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow43
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 23 (274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-549755813888 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-2405181685760 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (5360119185408 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (9380208574464 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-24120536334336 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-21161303867392 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (66443144069120 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (29424820944896 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-125292785958912 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-23031762124800 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (171356310208512 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2163589775360 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-175683489759232 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (19019306369024 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (137644877021184 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-27195963604992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-83252949811200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (22123700551680 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (39005548707840 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-12441425018880 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-14122698670080 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (5101137100800 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (3920424468480 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-1548809666560 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-822805135360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (347501281280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (127802572800 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-56780857344 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-14240858112 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (6576507392 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1087843328 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-517316800 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-53209728 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (25857936 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1493856 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-737048 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-19760 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (9841 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (78 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-39 : ℤ)

def fixedRowPCoeff_43 (n : ℕ) : ℤ :=
    (if 23 = n then (274877906944 : ℤ) else 0) +
    (if 24 = n then (-549755813888 : ℤ) else 0) +
    (if 25 = n then (-2405181685760 : ℤ) else 0) +
    (if 26 = n then (5360119185408 : ℤ) else 0) +
    (if 27 = n then (9380208574464 : ℤ) else 0) +
    (if 28 = n then (-24120536334336 : ℤ) else 0) +
    (if 29 = n then (-21161303867392 : ℤ) else 0) +
    (if 30 = n then (66443144069120 : ℤ) else 0) +
    (if 31 = n then (29424820944896 : ℤ) else 0) +
    (if 32 = n then (-125292785958912 : ℤ) else 0) +
    (if 33 = n then (-23031762124800 : ℤ) else 0) +
    (if 34 = n then (171356310208512 : ℤ) else 0) +
    (if 35 = n then (2163589775360 : ℤ) else 0) +
    (if 36 = n then (-175683489759232 : ℤ) else 0) +
    (if 37 = n then (19019306369024 : ℤ) else 0) +
    (if 38 = n then (137644877021184 : ℤ) else 0) +
    (if 39 = n then (-27195963604992 : ℤ) else 0) +
    (if 40 = n then (-83252949811200 : ℤ) else 0) +
    (if 41 = n then (22123700551680 : ℤ) else 0) +
    (if 42 = n then (39005548707840 : ℤ) else 0) +
    (if 43 = n then (-12441425018880 : ℤ) else 0) +
    (if 44 = n then (-14122698670080 : ℤ) else 0) +
    (if 45 = n then (5101137100800 : ℤ) else 0) +
    (if 46 = n then (3920424468480 : ℤ) else 0) +
    (if 47 = n then (-1548809666560 : ℤ) else 0) +
    (if 48 = n then (-822805135360 : ℤ) else 0) +
    (if 49 = n then (347501281280 : ℤ) else 0) +
    (if 50 = n then (127802572800 : ℤ) else 0) +
    (if 51 = n then (-56780857344 : ℤ) else 0) +
    (if 52 = n then (-14240858112 : ℤ) else 0) +
    (if 53 = n then (6576507392 : ℤ) else 0) +
    (if 54 = n then (1087843328 : ℤ) else 0) +
    (if 55 = n then (-517316800 : ℤ) else 0) +
    (if 56 = n then (-53209728 : ℤ) else 0) +
    (if 57 = n then (25857936 : ℤ) else 0) +
    (if 58 = n then (1493856 : ℤ) else 0) +
    (if 59 = n then (-737048 : ℤ) else 0) +
    (if 60 = n then (-19760 : ℤ) else 0) +
    (if 61 = n then (9841 : ℤ) else 0) +
    (if 62 = n then (78 : ℤ) else 0) +
    (if 63 = n then (-39 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_43 (n : ℕ) :
    fixedRowPData_43.coeff n = fixedRowPCoeff_43 n := by
  simp only [fixedRowPData_43, fixedRowPCoeff_43, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_43 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_43 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_43, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_43 : ∀ k : Fin 63,
    fixedReversedTCoeff_39 (k.val + 2) - 2 * fixedReversedTCoeff_39 (k.val + 1) + fixedReversedTCoeff_39 k.val = fixedRowPCoeff_43 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_43 :
    (1 - X) ^ 2 * fixedReversedTData_39 = fixedRowPData_43 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_39, fixed_rowP_typed_coeff_43]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_39, fixed_rowP_typed_coeff_43]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_39, fixed_rowP_typed_coeff_43]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_43 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_39 _ (by omega),
              fixed_reversedT_typed_tail_39 _ (by omega), fixed_reversedT_typed_tail_39 _ hn',
              fixed_rowP_typed_tail_43 _ (by omega)]
            decide

theorem fixed_rowP_typed_43 : rowP 1 43 = fixedRowPData_43 := by
  calc
    rowP 1 43 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_39 :=
      fixedTyped_rowP_of_parameters 1 43 2 63 39 fixedChebyshevTData_39
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_39
    _ = fixedRowPData_43 := by
      rw [fixed_reversedT_typed_data_39, fixed_rowP_typed_factor_43]

def fixedRowDData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 24 (274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-549755813888 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-2267742732288 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (5085241278464 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (8280696946688 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-21646635171840 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-17287243366400 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (56221121904640 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (21685289877504 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-99591701659648 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-13913546555392 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (127418794770432 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-2895881699328 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-121627031371776 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (16696567922688 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (88233895526400 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-19568001024000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-49097893478400 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (14047452856320 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (21002987765760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-7061349335040 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-6880289095680 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (2585693061120 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1708902973440 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-696219729920 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-316463513600 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (136931328000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (42600857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-19292102656 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-4016652288 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1882805760 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (251040768 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-120745152 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-9550464 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (4679472 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (191520 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-95000 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1520 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (759 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_43 (n : ℕ) : ℤ :=
    (if 24 = n then (274877906944 : ℤ) else 0) +
    (if 25 = n then (-549755813888 : ℤ) else 0) +
    (if 26 = n then (-2267742732288 : ℤ) else 0) +
    (if 27 = n then (5085241278464 : ℤ) else 0) +
    (if 28 = n then (8280696946688 : ℤ) else 0) +
    (if 29 = n then (-21646635171840 : ℤ) else 0) +
    (if 30 = n then (-17287243366400 : ℤ) else 0) +
    (if 31 = n then (56221121904640 : ℤ) else 0) +
    (if 32 = n then (21685289877504 : ℤ) else 0) +
    (if 33 = n then (-99591701659648 : ℤ) else 0) +
    (if 34 = n then (-13913546555392 : ℤ) else 0) +
    (if 35 = n then (127418794770432 : ℤ) else 0) +
    (if 36 = n then (-2895881699328 : ℤ) else 0) +
    (if 37 = n then (-121627031371776 : ℤ) else 0) +
    (if 38 = n then (16696567922688 : ℤ) else 0) +
    (if 39 = n then (88233895526400 : ℤ) else 0) +
    (if 40 = n then (-19568001024000 : ℤ) else 0) +
    (if 41 = n then (-49097893478400 : ℤ) else 0) +
    (if 42 = n then (14047452856320 : ℤ) else 0) +
    (if 43 = n then (21002987765760 : ℤ) else 0) +
    (if 44 = n then (-7061349335040 : ℤ) else 0) +
    (if 45 = n then (-6880289095680 : ℤ) else 0) +
    (if 46 = n then (2585693061120 : ℤ) else 0) +
    (if 47 = n then (1708902973440 : ℤ) else 0) +
    (if 48 = n then (-696219729920 : ℤ) else 0) +
    (if 49 = n then (-316463513600 : ℤ) else 0) +
    (if 50 = n then (136931328000 : ℤ) else 0) +
    (if 51 = n then (42600857600 : ℤ) else 0) +
    (if 52 = n then (-19292102656 : ℤ) else 0) +
    (if 53 = n then (-4016652288 : ℤ) else 0) +
    (if 54 = n then (1882805760 : ℤ) else 0) +
    (if 55 = n then (251040768 : ℤ) else 0) +
    (if 56 = n then (-120745152 : ℤ) else 0) +
    (if 57 = n then (-9550464 : ℤ) else 0) +
    (if 58 = n then (4679472 : ℤ) else 0) +
    (if 59 = n then (191520 : ℤ) else 0) +
    (if 60 = n then (-95000 : ℤ) else 0) +
    (if 61 = n then (-1520 : ℤ) else 0) +
    (if 62 = n then (759 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_43 (n : ℕ) :
    fixedRowDData_43.coeff n = fixedRowDCoeff_43 n := by
  simp only [fixedRowDData_43, fixedRowDCoeff_43, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_43 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_43 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_43, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_43 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_38 (k.val + 2) - 2 * fixedReversedUCoeff_38 (k.val + 1) + fixedReversedUCoeff_38 k.val) = fixedRowDCoeff_43 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_43 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_38 = fixedRowDData_43 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_38, fixed_rowD_typed_coeff_43]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_38, fixed_rowD_typed_coeff_43]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_38, fixed_rowD_typed_coeff_43]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_43 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_38 _ (by omega),
              fixed_reversedU_typed_tail_38 _ (by omega), fixed_reversedU_typed_tail_38 _ hn',
              fixed_rowD_typed_tail_43 _ (by omega)]
            decide

theorem fixed_rowD_typed_43 : rowD 1 43 = fixedRowDData_43 := by
  calc
    rowD 1 43 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_38 :=
      fixedTyped_rowD_of_parameters 1 43 2 63 38 (1)
        fixedChebyshevUData_38 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_38
    _ = fixedRowDData_43 := by
      rw [fixed_reversedU_typed_data_38, fixed_rowD_typed_factor_43]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT40To44
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-800 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (106400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-5617920 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (156900480 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-2677768192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (30429184000 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-243433472000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (1424085811200 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-6254808268800 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (21002987765760 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-54553214976000 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (110292369408000 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-173752901959680 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (212364657950720 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-199183403319296 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (140552804761600 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-72155450572800 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (25426206392320 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-5497558138880 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (549755813888 : ℤ)

def fixedReversedTCoeff_40 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-800 : ℤ) else 0) +
    (if 58 = n then (106400 : ℤ) else 0) +
    (if 56 = n then (-5617920 : ℤ) else 0) +
    (if 54 = n then (156900480 : ℤ) else 0) +
    (if 52 = n then (-2677768192 : ℤ) else 0) +
    (if 50 = n then (30429184000 : ℤ) else 0) +
    (if 48 = n then (-243433472000 : ℤ) else 0) +
    (if 46 = n then (1424085811200 : ℤ) else 0) +
    (if 44 = n then (-6254808268800 : ℤ) else 0) +
    (if 42 = n then (21002987765760 : ℤ) else 0) +
    (if 40 = n then (-54553214976000 : ℤ) else 0) +
    (if 38 = n then (110292369408000 : ℤ) else 0) +
    (if 36 = n then (-173752901959680 : ℤ) else 0) +
    (if 34 = n then (212364657950720 : ℤ) else 0) +
    (if 32 = n then (-199183403319296 : ℤ) else 0) +
    (if 30 = n then (140552804761600 : ℤ) else 0) +
    (if 28 = n then (-72155450572800 : ℤ) else 0) +
    (if 26 = n then (25426206392320 : ℤ) else 0) +
    (if 24 = n then (-5497558138880 : ℤ) else 0) +
    (if 22 = n then (549755813888 : ℤ) else 0)

theorem fixed_reversedT_typed_data_40 : reversedRow 63 fixedChebyshevTData_40 = fixedReversedTData_40 := by
  simp only [fixedChebyshevTData_40, fixedReversedTData_40, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-800 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (106400 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-5617920 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (156900480 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-2677768192 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (30429184000 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-243433472000 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (1424085811200 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-6254808268800 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (21002987765760 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-54553214976000 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (110292369408000 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-173752901959680 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (212364657950720 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-199183403319296 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (140552804761600 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-72155450572800 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (25426206392320 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (-5497558138880 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (549755813888 : ℤ) 40 (by decide)]

theorem fixed_reversedT_typed_coeff_40 (n : ℕ) :
    fixedReversedTData_40.coeff n = fixedReversedTCoeff_40 n := by
  simp only [fixedReversedTData_40, fixedReversedTCoeff_40, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_40 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_40 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_40, if_neg, add_zero]





















end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow44
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_44 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 22 (549755813888 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-4947802324992 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (10995116277760 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (19928648253440 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-50852412784640 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-46729244180480 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (144310901145600 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (68397354188800 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-281105609523200 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-58630598557696 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (398366806638592 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (13181254631424 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-424729315901440 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (38611755991040 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (347505803919360 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-63460532551680 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-220584738816000 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (55739154432000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (109106429952000 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-33550227210240 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-42005975531520 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (14748179496960 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (12509616537600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-4830722457600 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-2848171622400 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1180652339200 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (486866944000 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-213004288000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-60858368000 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (27751415808 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (5355536384 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-2520867712 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-313800960 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (151282560 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (11235840 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-5511520 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-212800 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (105600 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1600 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-799 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_44 (n : ℕ) : ℤ :=
    (if 22 = n then (549755813888 : ℤ) else 0) +
    (if 23 = n then (-1099511627776 : ℤ) else 0) +
    (if 24 = n then (-4947802324992 : ℤ) else 0) +
    (if 25 = n then (10995116277760 : ℤ) else 0) +
    (if 26 = n then (19928648253440 : ℤ) else 0) +
    (if 27 = n then (-50852412784640 : ℤ) else 0) +
    (if 28 = n then (-46729244180480 : ℤ) else 0) +
    (if 29 = n then (144310901145600 : ℤ) else 0) +
    (if 30 = n then (68397354188800 : ℤ) else 0) +
    (if 31 = n then (-281105609523200 : ℤ) else 0) +
    (if 32 = n then (-58630598557696 : ℤ) else 0) +
    (if 33 = n then (398366806638592 : ℤ) else 0) +
    (if 34 = n then (13181254631424 : ℤ) else 0) +
    (if 35 = n then (-424729315901440 : ℤ) else 0) +
    (if 36 = n then (38611755991040 : ℤ) else 0) +
    (if 37 = n then (347505803919360 : ℤ) else 0) +
    (if 38 = n then (-63460532551680 : ℤ) else 0) +
    (if 39 = n then (-220584738816000 : ℤ) else 0) +
    (if 40 = n then (55739154432000 : ℤ) else 0) +
    (if 41 = n then (109106429952000 : ℤ) else 0) +
    (if 42 = n then (-33550227210240 : ℤ) else 0) +
    (if 43 = n then (-42005975531520 : ℤ) else 0) +
    (if 44 = n then (14748179496960 : ℤ) else 0) +
    (if 45 = n then (12509616537600 : ℤ) else 0) +
    (if 46 = n then (-4830722457600 : ℤ) else 0) +
    (if 47 = n then (-2848171622400 : ℤ) else 0) +
    (if 48 = n then (1180652339200 : ℤ) else 0) +
    (if 49 = n then (486866944000 : ℤ) else 0) +
    (if 50 = n then (-213004288000 : ℤ) else 0) +
    (if 51 = n then (-60858368000 : ℤ) else 0) +
    (if 52 = n then (27751415808 : ℤ) else 0) +
    (if 53 = n then (5355536384 : ℤ) else 0) +
    (if 54 = n then (-2520867712 : ℤ) else 0) +
    (if 55 = n then (-313800960 : ℤ) else 0) +
    (if 56 = n then (151282560 : ℤ) else 0) +
    (if 57 = n then (11235840 : ℤ) else 0) +
    (if 58 = n then (-5511520 : ℤ) else 0) +
    (if 59 = n then (-212800 : ℤ) else 0) +
    (if 60 = n then (105600 : ℤ) else 0) +
    (if 61 = n then (1600 : ℤ) else 0) +
    (if 62 = n then (-799 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_44 (n : ℕ) :
    fixedRowPData_44.coeff n = fixedRowPCoeff_44 n := by
  simp only [fixedRowPData_44, fixedRowPCoeff_44, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_44 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_44 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_44, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_44 : ∀ k : Fin 63,
    fixedReversedTCoeff_40 (k.val + 2) - 2 * fixedReversedTCoeff_40 (k.val + 1) + fixedReversedTCoeff_40 k.val = fixedRowPCoeff_44 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_44 :
    (1 - X) ^ 2 * fixedReversedTData_40 = fixedRowPData_44 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_40, fixed_rowP_typed_coeff_44]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_40, fixed_rowP_typed_coeff_44]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_40, fixed_rowP_typed_coeff_44]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_44 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_40 _ (by omega),
              fixed_reversedT_typed_tail_40 _ (by omega), fixed_reversedT_typed_tail_40 _ hn',
              fixed_rowP_typed_tail_44 _ (by omega)]
            decide

theorem fixed_rowP_typed_44 : rowP 1 44 = fixedRowPData_44 := by
  calc
    rowP 1 44 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_40 :=
      fixedTyped_rowP_of_parameters 1 44 2 63 40 fixedChebyshevTData_40
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_40
    _ = fixedRowPData_44 := by
      rw [fixed_reversedT_typed_data_40, fixed_rowP_typed_factor_44]

def fixedRowDData_44 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 23 (549755813888 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-4672924418048 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (10445360463872 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (17660905521152 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-45767171506176 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-38448547233792 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (122664265973760 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (51110110822400 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-224884487618560 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-36945308680192 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (298775104978944 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-732291923968 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-297310521131008 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (35715874291712 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (225878772547584 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-46763964628992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-132350843289600 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (36171153408000 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (60008536473600 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-19502774353920 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-21002987765760 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (7686830161920 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (5629327441920 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-2245029396480 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-1139268648960 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (484432609280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (170403430400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-76072960000 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-18257510400 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (8459313152 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1338884096 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-638061952 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-62760192 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (30537408 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1685376 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-832048 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-21280 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (10600 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (80 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-40 : ℤ)

def fixedRowDCoeff_44 (n : ℕ) : ℤ :=
    (if 23 = n then (549755813888 : ℤ) else 0) +
    (if 24 = n then (-1099511627776 : ℤ) else 0) +
    (if 25 = n then (-4672924418048 : ℤ) else 0) +
    (if 26 = n then (10445360463872 : ℤ) else 0) +
    (if 27 = n then (17660905521152 : ℤ) else 0) +
    (if 28 = n then (-45767171506176 : ℤ) else 0) +
    (if 29 = n then (-38448547233792 : ℤ) else 0) +
    (if 30 = n then (122664265973760 : ℤ) else 0) +
    (if 31 = n then (51110110822400 : ℤ) else 0) +
    (if 32 = n then (-224884487618560 : ℤ) else 0) +
    (if 33 = n then (-36945308680192 : ℤ) else 0) +
    (if 34 = n then (298775104978944 : ℤ) else 0) +
    (if 35 = n then (-732291923968 : ℤ) else 0) +
    (if 36 = n then (-297310521131008 : ℤ) else 0) +
    (if 37 = n then (35715874291712 : ℤ) else 0) +
    (if 38 = n then (225878772547584 : ℤ) else 0) +
    (if 39 = n then (-46763964628992 : ℤ) else 0) +
    (if 40 = n then (-132350843289600 : ℤ) else 0) +
    (if 41 = n then (36171153408000 : ℤ) else 0) +
    (if 42 = n then (60008536473600 : ℤ) else 0) +
    (if 43 = n then (-19502774353920 : ℤ) else 0) +
    (if 44 = n then (-21002987765760 : ℤ) else 0) +
    (if 45 = n then (7686830161920 : ℤ) else 0) +
    (if 46 = n then (5629327441920 : ℤ) else 0) +
    (if 47 = n then (-2245029396480 : ℤ) else 0) +
    (if 48 = n then (-1139268648960 : ℤ) else 0) +
    (if 49 = n then (484432609280 : ℤ) else 0) +
    (if 50 = n then (170403430400 : ℤ) else 0) +
    (if 51 = n then (-76072960000 : ℤ) else 0) +
    (if 52 = n then (-18257510400 : ℤ) else 0) +
    (if 53 = n then (8459313152 : ℤ) else 0) +
    (if 54 = n then (1338884096 : ℤ) else 0) +
    (if 55 = n then (-638061952 : ℤ) else 0) +
    (if 56 = n then (-62760192 : ℤ) else 0) +
    (if 57 = n then (30537408 : ℤ) else 0) +
    (if 58 = n then (1685376 : ℤ) else 0) +
    (if 59 = n then (-832048 : ℤ) else 0) +
    (if 60 = n then (-21280 : ℤ) else 0) +
    (if 61 = n then (10600 : ℤ) else 0) +
    (if 62 = n then (80 : ℤ) else 0) +
    (if 63 = n then (-40 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_44 (n : ℕ) :
    fixedRowDData_44.coeff n = fixedRowDCoeff_44 n := by
  simp only [fixedRowDData_44, fixedRowDCoeff_44, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_44 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_44 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_44, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_44 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_39 (k.val + 2) - 2 * fixedReversedUCoeff_39 (k.val + 1) + fixedReversedUCoeff_39 k.val) = fixedRowDCoeff_44 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_44 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_39 = fixedRowDData_44 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_39, fixed_rowD_typed_coeff_44]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_39, fixed_rowD_typed_coeff_44]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_39, fixed_rowD_typed_coeff_44]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_44 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_39 _ (by omega),
              fixed_reversedU_typed_tail_39 _ (by omega), fixed_reversedU_typed_tail_39 _ hn',
              fixed_rowD_typed_tail_44 _ (by omega)]
            decide

theorem fixed_rowD_typed_44 : rowD 1 44 = fixedRowDData_44 := by
  calc
    rowD 1 44 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_39 :=
      fixedTyped_rowD_of_parameters 1 44 2 63 39 (1)
        fixedChebyshevUData_39 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_39
    _ = fixedRowDData_44 := by
      rw [fixed_reversedU_typed_data_39, fixed_rowD_typed_factor_44]

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

theorem splitBaseMod_row_43 (k : Fin 48) :
    (fixedIntegerBaseCanonical (43 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (43 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (43 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_43 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_43 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 43).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 43).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_43, fixed_rowD_typed_43]
    simp only [fixed_rowP_typed_coeff_43, fixed_rowD_typed_coeff_43,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_44 (k : Fin 48) :
    (fixedIntegerBaseCanonical (44 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (44 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (44 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_44 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_44 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 44).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 44).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_44, fixed_rowD_typed_44]
    simp only [fixed_rowP_typed_coeff_44, fixed_rowD_typed_coeff_44,
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
















theorem fixedIntegerBaseCanonical_mod101_rows_43_44 (r : Fin 49) (hr : 43 ≤ r.val ∧ r.val < 45)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  obtain ⟨r, hr'⟩ := r
  obtain ⟨hra, hrb⟩ := hr
  simp only at hra hrb
  interval_cases r
  · exact splitBaseMod_row_43 k
  · exact splitBaseMod_row_44 k

























end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (hr : 43 ≤ r.val ∧ r.val < 45)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_43_44
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_43_44 <;> assumption)

end
