-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_36_42
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T20:21:22.683657+00:00
-- url     : https://prove2.me/submissions/60b39d30-c6fc-4431-96b2-9c0853688ed1

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Prime.Basic
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAICatalanIrrationality

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevTData
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedChebyshevTData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ)

def fixedChebyshevTData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (1 : ℤ)

def fixedChebyshevTData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (2 : ℤ)

def fixedChebyshevTData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-3 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (4 : ℤ)

def fixedChebyshevTData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (8 : ℤ)

def fixedChebyshevTData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (5 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (16 : ℤ)

def fixedChebyshevTData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (18 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-48 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (32 : ℤ)

def fixedChebyshevTData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-7 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (56 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-112 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (64 : ℤ)

def fixedChebyshevTData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (160 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-256 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (128 : ℤ)

def fixedChebyshevTData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (9 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-120 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (432 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-576 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (256 : ℤ)

def fixedChebyshevTData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (50 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-400 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-1280 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (512 : ℤ)

def fixedChebyshevTData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-11 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (220 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-1232 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (1024 : ℤ)

def fixedChebyshevTData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-72 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (840 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (6912 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-6144 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (2048 : ℤ)

def fixedChebyshevTData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (13 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-364 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (2912 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-9984 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (16640 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-13312 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (4096 : ℤ)

def fixedChebyshevTData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (98 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-1568 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (9408 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-26880 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (39424 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-28672 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (8192 : ℤ)

def fixedChebyshevTData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-15 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (560 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-6048 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (28800 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-70400 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (92160 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-61440 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (16384 : ℤ)

def fixedChebyshevTData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (2688 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-21504 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-180224 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (212992 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (32768 : ℤ)

def fixedChebyshevTData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (17 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-816 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (11424 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-71808 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (239360 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-452608 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (487424 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-278528 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (65536 : ℤ)

def fixedChebyshevTData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (162 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-4320 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (44352 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-228096 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-1118208 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (1105920 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-589824 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (131072 : ℤ)

def fixedChebyshevTData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-19 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (1140 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-20064 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (160512 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-695552 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (1770496 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-2723840 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (2490368 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-1245184 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (262144 : ℤ)

def fixedChebyshevTData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-200 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (6600 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (549120 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-2050048 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (4659200 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-6553600 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (5570560 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-2621440 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (524288 : ℤ)

def fixedChebyshevTData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (21 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-1540 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (33264 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-329472 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (1793792 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-5870592 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (12042240 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-15597568 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (12386304 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-5505024 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (1048576 : ℤ)

def fixedChebyshevTData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (242 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-9680 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (151008 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-1208064 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (5637632 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-16400384 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (30638080 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-36765696 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (27394048 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-11534336 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (2097152 : ℤ)

def fixedChebyshevTData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-23 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (2024 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-52624 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (631488 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-4209920 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (17145856 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-44843008 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (76873728 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-85917696 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (60293120 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-24117248 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (4194304 : ℤ)

def fixedChebyshevTData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-288 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (13728 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-256256 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (2471040 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-14057472 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-120324096 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-199229440 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (132120576 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-50331648 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (8388608 : ℤ)

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

def fixedChebyshevUData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ)

def fixedChebyshevUData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (2 : ℤ)

def fixedChebyshevUData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (4 : ℤ)

def fixedChebyshevUData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (8 : ℤ)

def fixedChebyshevUData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (16 : ℤ)

def fixedChebyshevUData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (6 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (32 : ℤ)

def fixedChebyshevUData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (24 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-80 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (64 : ℤ)

def fixedChebyshevUData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (80 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-192 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (128 : ℤ)

def fixedChebyshevUData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-40 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (240 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-448 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (256 : ℤ)

def fixedChebyshevUData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (10 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-160 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (672 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (512 : ℤ)

def fixedChebyshevUData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (60 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-560 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-2304 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (1024 : ℤ)

def fixedChebyshevUData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (280 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (4608 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-5120 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (2048 : ℤ)

def fixedChebyshevUData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-84 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-5376 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (11520 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-11264 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (4096 : ℤ)

def fixedChebyshevUData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (14 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-448 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (4032 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-15360 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (28160 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-24576 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (8192 : ℤ)

def fixedChebyshevUData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (112 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-2016 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (13440 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-42240 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (67584 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-53248 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (16384 : ℤ)

def fixedChebyshevUData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (672 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-8064 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (42240 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-112640 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (159744 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-114688 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (32768 : ℤ)

def fixedChebyshevUData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-144 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (3360 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-29568 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (126720 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-292864 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (372736 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-245760 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (65536 : ℤ)

def fixedChebyshevUData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (18 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-960 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (14784 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-101376 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (366080 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-745472 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (860160 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (131072 : ℤ)

def fixedChebyshevUData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (180 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-5280 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (59136 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-329472 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-1863680 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (1966080 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-1114112 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (262144 : ℤ)

def fixedChebyshevUData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (1320 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-25344 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (219648 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (2795520 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-4587520 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (4456448 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-2359296 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (524288 : ℤ)

def fixedChebyshevUData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-220 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (7920 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-109824 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (768768 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-3075072 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (7454720 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-11141120 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (10027008 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-4980736 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (1048576 : ℤ)

def fixedChebyshevUData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (22 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-1760 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (41184 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-439296 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (2562560 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-8945664 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (19496960 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-26738688 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (22413312 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-10485760 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (2097152 : ℤ)

def fixedChebyshevUData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (264 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-11440 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (192192 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-1647360 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (8200192 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (50135040 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-63504384 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (49807360 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-22020096 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (4194304 : ℤ)

def fixedChebyshevUData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-24 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (2288 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-64064 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (823680 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-5857280 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-70189056 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-149422080 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (110100480 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-46137344 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (8388608 : ℤ)

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







end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevU18To23
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_0 :
    Chebyshev.U ℤ 0 = fixedChebyshevUData_0 := by
  norm_num [fixedChebyshevUData_0, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem fixed_chebyshevU_typed_1 :
    Chebyshev.U ℤ 1 = fixedChebyshevUData_1 := by
  norm_num [fixedChebyshevUData_1, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem fixed_chebyshevU_typed_2 :
    Chebyshev.U ℤ 2 = fixedChebyshevUData_2 := by
  calc
    Chebyshev.U ℤ 2 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 1 - Chebyshev.U ℤ 0 :=
      Chebyshev.U_add_two ℤ 0
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_1 - fixedChebyshevUData_0 := by
      rw [fixed_chebyshevU_typed_1, fixed_chebyshevU_typed_0]
    _ = fixedChebyshevUData_2 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_1, fixedChebyshevUData_0, fixedChebyshevUData_2, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_1, fixedChebyshevUData_0, fixedChebyshevUData_2, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 2
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 2, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 2 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_3 :
    Chebyshev.U ℤ 3 = fixedChebyshevUData_3 := by
  calc
    Chebyshev.U ℤ 3 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 2 - Chebyshev.U ℤ 1 :=
      Chebyshev.U_add_two ℤ 1
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_2 - fixedChebyshevUData_1 := by
      rw [fixed_chebyshevU_typed_2, fixed_chebyshevU_typed_1]
    _ = fixedChebyshevUData_3 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_2, fixedChebyshevUData_1, fixedChebyshevUData_3, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_2, fixedChebyshevUData_1, fixedChebyshevUData_3, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 3
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 3, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 3 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_4 :
    Chebyshev.U ℤ 4 = fixedChebyshevUData_4 := by
  calc
    Chebyshev.U ℤ 4 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 3 - Chebyshev.U ℤ 2 :=
      Chebyshev.U_add_two ℤ 2
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_3 - fixedChebyshevUData_2 := by
      rw [fixed_chebyshevU_typed_3, fixed_chebyshevU_typed_2]
    _ = fixedChebyshevUData_4 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_3, fixedChebyshevUData_2, fixedChebyshevUData_4, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_3, fixedChebyshevUData_2, fixedChebyshevUData_4, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 4
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 4, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 4 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_5 :
    Chebyshev.U ℤ 5 = fixedChebyshevUData_5 := by
  calc
    Chebyshev.U ℤ 5 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 4 - Chebyshev.U ℤ 3 :=
      Chebyshev.U_add_two ℤ 3
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_4 - fixedChebyshevUData_3 := by
      rw [fixed_chebyshevU_typed_4, fixed_chebyshevU_typed_3]
    _ = fixedChebyshevUData_5 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_4, fixedChebyshevUData_3, fixedChebyshevUData_5, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_4, fixedChebyshevUData_3, fixedChebyshevUData_5, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 5
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 5, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 5 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_6 :
    Chebyshev.U ℤ 6 = fixedChebyshevUData_6 := by
  calc
    Chebyshev.U ℤ 6 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 5 - Chebyshev.U ℤ 4 :=
      Chebyshev.U_add_two ℤ 4
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_5 - fixedChebyshevUData_4 := by
      rw [fixed_chebyshevU_typed_5, fixed_chebyshevU_typed_4]
    _ = fixedChebyshevUData_6 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_5, fixedChebyshevUData_4, fixedChebyshevUData_6, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_5, fixedChebyshevUData_4, fixedChebyshevUData_6, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 6
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 6, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 6 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_7 :
    Chebyshev.U ℤ 7 = fixedChebyshevUData_7 := by
  calc
    Chebyshev.U ℤ 7 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 6 - Chebyshev.U ℤ 5 :=
      Chebyshev.U_add_two ℤ 5
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_6 - fixedChebyshevUData_5 := by
      rw [fixed_chebyshevU_typed_6, fixed_chebyshevU_typed_5]
    _ = fixedChebyshevUData_7 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_6, fixedChebyshevUData_5, fixedChebyshevUData_7, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_6, fixedChebyshevUData_5, fixedChebyshevUData_7, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 7
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 7, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 7 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_8 :
    Chebyshev.U ℤ 8 = fixedChebyshevUData_8 := by
  calc
    Chebyshev.U ℤ 8 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 7 - Chebyshev.U ℤ 6 :=
      Chebyshev.U_add_two ℤ 6
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_7 - fixedChebyshevUData_6 := by
      rw [fixed_chebyshevU_typed_7, fixed_chebyshevU_typed_6]
    _ = fixedChebyshevUData_8 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_7, fixedChebyshevUData_6, fixedChebyshevUData_8, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_7, fixedChebyshevUData_6, fixedChebyshevUData_8, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 8
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 8, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 8 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_9 :
    Chebyshev.U ℤ 9 = fixedChebyshevUData_9 := by
  calc
    Chebyshev.U ℤ 9 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 8 - Chebyshev.U ℤ 7 :=
      Chebyshev.U_add_two ℤ 7
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_8 - fixedChebyshevUData_7 := by
      rw [fixed_chebyshevU_typed_8, fixed_chebyshevU_typed_7]
    _ = fixedChebyshevUData_9 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_8, fixedChebyshevUData_7, fixedChebyshevUData_9, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_8, fixedChebyshevUData_7, fixedChebyshevUData_9, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 9
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 9, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 9 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_10 :
    Chebyshev.U ℤ 10 = fixedChebyshevUData_10 := by
  calc
    Chebyshev.U ℤ 10 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 9 - Chebyshev.U ℤ 8 :=
      Chebyshev.U_add_two ℤ 8
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_9 - fixedChebyshevUData_8 := by
      rw [fixed_chebyshevU_typed_9, fixed_chebyshevU_typed_8]
    _ = fixedChebyshevUData_10 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_9, fixedChebyshevUData_8, fixedChebyshevUData_10, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_9, fixedChebyshevUData_8, fixedChebyshevUData_10, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 10
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 10, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 10 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_11 :
    Chebyshev.U ℤ 11 = fixedChebyshevUData_11 := by
  calc
    Chebyshev.U ℤ 11 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 10 - Chebyshev.U ℤ 9 :=
      Chebyshev.U_add_two ℤ 9
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_10 - fixedChebyshevUData_9 := by
      rw [fixed_chebyshevU_typed_10, fixed_chebyshevU_typed_9]
    _ = fixedChebyshevUData_11 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_10, fixedChebyshevUData_9, fixedChebyshevUData_11, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_10, fixedChebyshevUData_9, fixedChebyshevUData_11, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 11
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 11, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 11 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_12 :
    Chebyshev.U ℤ 12 = fixedChebyshevUData_12 := by
  calc
    Chebyshev.U ℤ 12 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 11 - Chebyshev.U ℤ 10 :=
      Chebyshev.U_add_two ℤ 10
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_11 - fixedChebyshevUData_10 := by
      rw [fixed_chebyshevU_typed_11, fixed_chebyshevU_typed_10]
    _ = fixedChebyshevUData_12 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_11, fixedChebyshevUData_10, fixedChebyshevUData_12, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_11, fixedChebyshevUData_10, fixedChebyshevUData_12, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 12
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 12, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 12 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_13 :
    Chebyshev.U ℤ 13 = fixedChebyshevUData_13 := by
  calc
    Chebyshev.U ℤ 13 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 12 - Chebyshev.U ℤ 11 :=
      Chebyshev.U_add_two ℤ 11
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_12 - fixedChebyshevUData_11 := by
      rw [fixed_chebyshevU_typed_12, fixed_chebyshevU_typed_11]
    _ = fixedChebyshevUData_13 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_12, fixedChebyshevUData_11, fixedChebyshevUData_13, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_12, fixedChebyshevUData_11, fixedChebyshevUData_13, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 13
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 13, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 13 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_14 :
    Chebyshev.U ℤ 14 = fixedChebyshevUData_14 := by
  calc
    Chebyshev.U ℤ 14 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 13 - Chebyshev.U ℤ 12 :=
      Chebyshev.U_add_two ℤ 12
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_13 - fixedChebyshevUData_12 := by
      rw [fixed_chebyshevU_typed_13, fixed_chebyshevU_typed_12]
    _ = fixedChebyshevUData_14 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_13, fixedChebyshevUData_12, fixedChebyshevUData_14, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_13, fixedChebyshevUData_12, fixedChebyshevUData_14, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 14
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 14, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 14 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_15 :
    Chebyshev.U ℤ 15 = fixedChebyshevUData_15 := by
  calc
    Chebyshev.U ℤ 15 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 14 - Chebyshev.U ℤ 13 :=
      Chebyshev.U_add_two ℤ 13
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_14 - fixedChebyshevUData_13 := by
      rw [fixed_chebyshevU_typed_14, fixed_chebyshevU_typed_13]
    _ = fixedChebyshevUData_15 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_14, fixedChebyshevUData_13, fixedChebyshevUData_15, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_14, fixedChebyshevUData_13, fixedChebyshevUData_15, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 15
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 15, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 15 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_16 :
    Chebyshev.U ℤ 16 = fixedChebyshevUData_16 := by
  calc
    Chebyshev.U ℤ 16 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 15 - Chebyshev.U ℤ 14 :=
      Chebyshev.U_add_two ℤ 14
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_15 - fixedChebyshevUData_14 := by
      rw [fixed_chebyshevU_typed_15, fixed_chebyshevU_typed_14]
    _ = fixedChebyshevUData_16 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_15, fixedChebyshevUData_14, fixedChebyshevUData_16, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_15, fixedChebyshevUData_14, fixedChebyshevUData_16, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 16
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 16, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 16 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_17 :
    Chebyshev.U ℤ 17 = fixedChebyshevUData_17 := by
  calc
    Chebyshev.U ℤ 17 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 16 - Chebyshev.U ℤ 15 :=
      Chebyshev.U_add_two ℤ 15
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_16 - fixedChebyshevUData_15 := by
      rw [fixed_chebyshevU_typed_16, fixed_chebyshevU_typed_15]
    _ = fixedChebyshevUData_17 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_16, fixedChebyshevUData_15, fixedChebyshevUData_17, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_16, fixedChebyshevUData_15, fixedChebyshevUData_17, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 17
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 17, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 17 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_18 :
    Chebyshev.U ℤ 18 = fixedChebyshevUData_18 := by
  calc
    Chebyshev.U ℤ 18 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 17 - Chebyshev.U ℤ 16 :=
      Chebyshev.U_add_two ℤ 16
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_17 - fixedChebyshevUData_16 := by
      rw [fixed_chebyshevU_typed_17, fixed_chebyshevU_typed_16]
    _ = fixedChebyshevUData_18 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_17, fixedChebyshevUData_16, fixedChebyshevUData_18, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_17, fixedChebyshevUData_16, fixedChebyshevUData_18, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 18
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 18, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 18 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_19 :
    Chebyshev.U ℤ 19 = fixedChebyshevUData_19 := by
  calc
    Chebyshev.U ℤ 19 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 18 - Chebyshev.U ℤ 17 :=
      Chebyshev.U_add_two ℤ 17
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_18 - fixedChebyshevUData_17 := by
      rw [fixed_chebyshevU_typed_18, fixed_chebyshevU_typed_17]
    _ = fixedChebyshevUData_19 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_18, fixedChebyshevUData_17, fixedChebyshevUData_19, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_18, fixedChebyshevUData_17, fixedChebyshevUData_19, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 19
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 19, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 19 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_20 :
    Chebyshev.U ℤ 20 = fixedChebyshevUData_20 := by
  calc
    Chebyshev.U ℤ 20 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 19 - Chebyshev.U ℤ 18 :=
      Chebyshev.U_add_two ℤ 18
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_19 - fixedChebyshevUData_18 := by
      rw [fixed_chebyshevU_typed_19, fixed_chebyshevU_typed_18]
    _ = fixedChebyshevUData_20 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_19, fixedChebyshevUData_18, fixedChebyshevUData_20, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_19, fixedChebyshevUData_18, fixedChebyshevUData_20, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 20
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 20, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 20 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_21 :
    Chebyshev.U ℤ 21 = fixedChebyshevUData_21 := by
  calc
    Chebyshev.U ℤ 21 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 20 - Chebyshev.U ℤ 19 :=
      Chebyshev.U_add_two ℤ 19
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_20 - fixedChebyshevUData_19 := by
      rw [fixed_chebyshevU_typed_20, fixed_chebyshevU_typed_19]
    _ = fixedChebyshevUData_21 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_20, fixedChebyshevUData_19, fixedChebyshevUData_21, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_20, fixedChebyshevUData_19, fixedChebyshevUData_21, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 21
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 21, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 21 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_22 :
    Chebyshev.U ℤ 22 = fixedChebyshevUData_22 := by
  calc
    Chebyshev.U ℤ 22 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 21 - Chebyshev.U ℤ 20 :=
      Chebyshev.U_add_two ℤ 20
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_21 - fixedChebyshevUData_20 := by
      rw [fixed_chebyshevU_typed_21, fixed_chebyshevU_typed_20]
    _ = fixedChebyshevUData_22 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_21, fixedChebyshevUData_20, fixedChebyshevUData_22, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_21, fixedChebyshevUData_20, fixedChebyshevUData_22, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 22
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 22, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 22 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_23 :
    Chebyshev.U ℤ 23 = fixedChebyshevUData_23 := by
  calc
    Chebyshev.U ℤ 23 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 22 - Chebyshev.U ℤ 21 :=
      Chebyshev.U_add_two ℤ 21
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_22 - fixedChebyshevUData_21 := by
      rw [fixed_chebyshevU_typed_22, fixed_chebyshevU_typed_21]
    _ = fixedChebyshevUData_23 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_22, fixedChebyshevUData_21, fixedChebyshevUData_23, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_22, fixedChebyshevUData_21, fixedChebyshevUData_23, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 23
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 23, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 23 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

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

theorem fixed_chebyshevT_typed_0 :
    Chebyshev.T ℤ 0 = fixedChebyshevTData_0 := by
  norm_num [fixedChebyshevTData_0, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem fixed_chebyshevT_typed_1 :
    Chebyshev.T ℤ 1 = fixedChebyshevTData_1 := by
  norm_num [fixedChebyshevTData_1, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem fixed_chebyshevT_typed_2 :
    Chebyshev.T ℤ 2 = fixedChebyshevTData_2 := by
  calc
    Chebyshev.T ℤ 2 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 1 - Chebyshev.T ℤ 0 :=
      Chebyshev.T_add_two ℤ 0
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_1 - fixedChebyshevTData_0 := by
      rw [fixed_chebyshevT_typed_1, fixed_chebyshevT_typed_0]
    _ = fixedChebyshevTData_2 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_1, fixedChebyshevTData_0, fixedChebyshevTData_2, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_1, fixedChebyshevTData_0, fixedChebyshevTData_2, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 2
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 2, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 2 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_3 :
    Chebyshev.T ℤ 3 = fixedChebyshevTData_3 := by
  calc
    Chebyshev.T ℤ 3 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 2 - Chebyshev.T ℤ 1 :=
      Chebyshev.T_add_two ℤ 1
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_2 - fixedChebyshevTData_1 := by
      rw [fixed_chebyshevT_typed_2, fixed_chebyshevT_typed_1]
    _ = fixedChebyshevTData_3 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_2, fixedChebyshevTData_1, fixedChebyshevTData_3, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_2, fixedChebyshevTData_1, fixedChebyshevTData_3, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 3
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 3, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 3 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_4 :
    Chebyshev.T ℤ 4 = fixedChebyshevTData_4 := by
  calc
    Chebyshev.T ℤ 4 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 3 - Chebyshev.T ℤ 2 :=
      Chebyshev.T_add_two ℤ 2
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_3 - fixedChebyshevTData_2 := by
      rw [fixed_chebyshevT_typed_3, fixed_chebyshevT_typed_2]
    _ = fixedChebyshevTData_4 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_3, fixedChebyshevTData_2, fixedChebyshevTData_4, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_3, fixedChebyshevTData_2, fixedChebyshevTData_4, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 4
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 4, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 4 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_5 :
    Chebyshev.T ℤ 5 = fixedChebyshevTData_5 := by
  calc
    Chebyshev.T ℤ 5 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 4 - Chebyshev.T ℤ 3 :=
      Chebyshev.T_add_two ℤ 3
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_4 - fixedChebyshevTData_3 := by
      rw [fixed_chebyshevT_typed_4, fixed_chebyshevT_typed_3]
    _ = fixedChebyshevTData_5 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_4, fixedChebyshevTData_3, fixedChebyshevTData_5, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_4, fixedChebyshevTData_3, fixedChebyshevTData_5, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 5
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 5, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 5 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_6 :
    Chebyshev.T ℤ 6 = fixedChebyshevTData_6 := by
  calc
    Chebyshev.T ℤ 6 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 5 - Chebyshev.T ℤ 4 :=
      Chebyshev.T_add_two ℤ 4
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_5 - fixedChebyshevTData_4 := by
      rw [fixed_chebyshevT_typed_5, fixed_chebyshevT_typed_4]
    _ = fixedChebyshevTData_6 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_5, fixedChebyshevTData_4, fixedChebyshevTData_6, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_5, fixedChebyshevTData_4, fixedChebyshevTData_6, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 6
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 6, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 6 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_7 :
    Chebyshev.T ℤ 7 = fixedChebyshevTData_7 := by
  calc
    Chebyshev.T ℤ 7 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 6 - Chebyshev.T ℤ 5 :=
      Chebyshev.T_add_two ℤ 5
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_6 - fixedChebyshevTData_5 := by
      rw [fixed_chebyshevT_typed_6, fixed_chebyshevT_typed_5]
    _ = fixedChebyshevTData_7 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_6, fixedChebyshevTData_5, fixedChebyshevTData_7, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_6, fixedChebyshevTData_5, fixedChebyshevTData_7, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 7
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 7, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 7 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_8 :
    Chebyshev.T ℤ 8 = fixedChebyshevTData_8 := by
  calc
    Chebyshev.T ℤ 8 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 7 - Chebyshev.T ℤ 6 :=
      Chebyshev.T_add_two ℤ 6
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_7 - fixedChebyshevTData_6 := by
      rw [fixed_chebyshevT_typed_7, fixed_chebyshevT_typed_6]
    _ = fixedChebyshevTData_8 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_7, fixedChebyshevTData_6, fixedChebyshevTData_8, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_7, fixedChebyshevTData_6, fixedChebyshevTData_8, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 8
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 8, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 8 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_9 :
    Chebyshev.T ℤ 9 = fixedChebyshevTData_9 := by
  calc
    Chebyshev.T ℤ 9 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 8 - Chebyshev.T ℤ 7 :=
      Chebyshev.T_add_two ℤ 7
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_8 - fixedChebyshevTData_7 := by
      rw [fixed_chebyshevT_typed_8, fixed_chebyshevT_typed_7]
    _ = fixedChebyshevTData_9 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_8, fixedChebyshevTData_7, fixedChebyshevTData_9, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_8, fixedChebyshevTData_7, fixedChebyshevTData_9, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 9
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 9, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 9 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_10 :
    Chebyshev.T ℤ 10 = fixedChebyshevTData_10 := by
  calc
    Chebyshev.T ℤ 10 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 9 - Chebyshev.T ℤ 8 :=
      Chebyshev.T_add_two ℤ 8
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_9 - fixedChebyshevTData_8 := by
      rw [fixed_chebyshevT_typed_9, fixed_chebyshevT_typed_8]
    _ = fixedChebyshevTData_10 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_9, fixedChebyshevTData_8, fixedChebyshevTData_10, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_9, fixedChebyshevTData_8, fixedChebyshevTData_10, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 10
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 10, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 10 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_11 :
    Chebyshev.T ℤ 11 = fixedChebyshevTData_11 := by
  calc
    Chebyshev.T ℤ 11 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 10 - Chebyshev.T ℤ 9 :=
      Chebyshev.T_add_two ℤ 9
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_10 - fixedChebyshevTData_9 := by
      rw [fixed_chebyshevT_typed_10, fixed_chebyshevT_typed_9]
    _ = fixedChebyshevTData_11 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_10, fixedChebyshevTData_9, fixedChebyshevTData_11, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_10, fixedChebyshevTData_9, fixedChebyshevTData_11, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 11
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 11, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 11 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_12 :
    Chebyshev.T ℤ 12 = fixedChebyshevTData_12 := by
  calc
    Chebyshev.T ℤ 12 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 11 - Chebyshev.T ℤ 10 :=
      Chebyshev.T_add_two ℤ 10
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_11 - fixedChebyshevTData_10 := by
      rw [fixed_chebyshevT_typed_11, fixed_chebyshevT_typed_10]
    _ = fixedChebyshevTData_12 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_11, fixedChebyshevTData_10, fixedChebyshevTData_12, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_11, fixedChebyshevTData_10, fixedChebyshevTData_12, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 12
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 12, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 12 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_13 :
    Chebyshev.T ℤ 13 = fixedChebyshevTData_13 := by
  calc
    Chebyshev.T ℤ 13 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 12 - Chebyshev.T ℤ 11 :=
      Chebyshev.T_add_two ℤ 11
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_12 - fixedChebyshevTData_11 := by
      rw [fixed_chebyshevT_typed_12, fixed_chebyshevT_typed_11]
    _ = fixedChebyshevTData_13 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_12, fixedChebyshevTData_11, fixedChebyshevTData_13, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_12, fixedChebyshevTData_11, fixedChebyshevTData_13, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 13
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 13, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 13 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_14 :
    Chebyshev.T ℤ 14 = fixedChebyshevTData_14 := by
  calc
    Chebyshev.T ℤ 14 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 13 - Chebyshev.T ℤ 12 :=
      Chebyshev.T_add_two ℤ 12
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_13 - fixedChebyshevTData_12 := by
      rw [fixed_chebyshevT_typed_13, fixed_chebyshevT_typed_12]
    _ = fixedChebyshevTData_14 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_13, fixedChebyshevTData_12, fixedChebyshevTData_14, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_13, fixedChebyshevTData_12, fixedChebyshevTData_14, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 14
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 14, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 14 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_15 :
    Chebyshev.T ℤ 15 = fixedChebyshevTData_15 := by
  calc
    Chebyshev.T ℤ 15 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 14 - Chebyshev.T ℤ 13 :=
      Chebyshev.T_add_two ℤ 13
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_14 - fixedChebyshevTData_13 := by
      rw [fixed_chebyshevT_typed_14, fixed_chebyshevT_typed_13]
    _ = fixedChebyshevTData_15 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_14, fixedChebyshevTData_13, fixedChebyshevTData_15, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_14, fixedChebyshevTData_13, fixedChebyshevTData_15, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 15
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 15, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 15 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_16 :
    Chebyshev.T ℤ 16 = fixedChebyshevTData_16 := by
  calc
    Chebyshev.T ℤ 16 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 15 - Chebyshev.T ℤ 14 :=
      Chebyshev.T_add_two ℤ 14
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_15 - fixedChebyshevTData_14 := by
      rw [fixed_chebyshevT_typed_15, fixed_chebyshevT_typed_14]
    _ = fixedChebyshevTData_16 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_15, fixedChebyshevTData_14, fixedChebyshevTData_16, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_15, fixedChebyshevTData_14, fixedChebyshevTData_16, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 16
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 16, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 16 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_17 :
    Chebyshev.T ℤ 17 = fixedChebyshevTData_17 := by
  calc
    Chebyshev.T ℤ 17 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 16 - Chebyshev.T ℤ 15 :=
      Chebyshev.T_add_two ℤ 15
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_16 - fixedChebyshevTData_15 := by
      rw [fixed_chebyshevT_typed_16, fixed_chebyshevT_typed_15]
    _ = fixedChebyshevTData_17 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_16, fixedChebyshevTData_15, fixedChebyshevTData_17, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_16, fixedChebyshevTData_15, fixedChebyshevTData_17, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 17
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 17, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 17 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_18 :
    Chebyshev.T ℤ 18 = fixedChebyshevTData_18 := by
  calc
    Chebyshev.T ℤ 18 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 17 - Chebyshev.T ℤ 16 :=
      Chebyshev.T_add_two ℤ 16
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_17 - fixedChebyshevTData_16 := by
      rw [fixed_chebyshevT_typed_17, fixed_chebyshevT_typed_16]
    _ = fixedChebyshevTData_18 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_17, fixedChebyshevTData_16, fixedChebyshevTData_18, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_17, fixedChebyshevTData_16, fixedChebyshevTData_18, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 18
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 18, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 18 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_19 :
    Chebyshev.T ℤ 19 = fixedChebyshevTData_19 := by
  calc
    Chebyshev.T ℤ 19 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 18 - Chebyshev.T ℤ 17 :=
      Chebyshev.T_add_two ℤ 17
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_18 - fixedChebyshevTData_17 := by
      rw [fixed_chebyshevT_typed_18, fixed_chebyshevT_typed_17]
    _ = fixedChebyshevTData_19 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_18, fixedChebyshevTData_17, fixedChebyshevTData_19, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_18, fixedChebyshevTData_17, fixedChebyshevTData_19, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 19
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 19, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 19 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_20 :
    Chebyshev.T ℤ 20 = fixedChebyshevTData_20 := by
  calc
    Chebyshev.T ℤ 20 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 19 - Chebyshev.T ℤ 18 :=
      Chebyshev.T_add_two ℤ 18
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_19 - fixedChebyshevTData_18 := by
      rw [fixed_chebyshevT_typed_19, fixed_chebyshevT_typed_18]
    _ = fixedChebyshevTData_20 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_19, fixedChebyshevTData_18, fixedChebyshevTData_20, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_19, fixedChebyshevTData_18, fixedChebyshevTData_20, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 20
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 20, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 20 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_21 :
    Chebyshev.T ℤ 21 = fixedChebyshevTData_21 := by
  calc
    Chebyshev.T ℤ 21 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 20 - Chebyshev.T ℤ 19 :=
      Chebyshev.T_add_two ℤ 19
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_20 - fixedChebyshevTData_19 := by
      rw [fixed_chebyshevT_typed_20, fixed_chebyshevT_typed_19]
    _ = fixedChebyshevTData_21 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_20, fixedChebyshevTData_19, fixedChebyshevTData_21, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_20, fixedChebyshevTData_19, fixedChebyshevTData_21, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 21
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 21, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 21 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_22 :
    Chebyshev.T ℤ 22 = fixedChebyshevTData_22 := by
  calc
    Chebyshev.T ℤ 22 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 21 - Chebyshev.T ℤ 20 :=
      Chebyshev.T_add_two ℤ 20
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_21 - fixedChebyshevTData_20 := by
      rw [fixed_chebyshevT_typed_21, fixed_chebyshevT_typed_20]
    _ = fixedChebyshevTData_22 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_21, fixedChebyshevTData_20, fixedChebyshevTData_22, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_21, fixedChebyshevTData_20, fixedChebyshevTData_22, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 22
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 22, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 22 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_23 :
    Chebyshev.T ℤ 23 = fixedChebyshevTData_23 := by
  calc
    Chebyshev.T ℤ 23 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 22 - Chebyshev.T ℤ 21 :=
      Chebyshev.T_add_two ℤ 21
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_22 - fixedChebyshevTData_21 := by
      rw [fixed_chebyshevT_typed_22, fixed_chebyshevT_typed_21]
    _ = fixedChebyshevTData_23 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_22, fixedChebyshevTData_21, fixedChebyshevTData_23, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_22, fixedChebyshevTData_21, fixedChebyshevTData_23, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 23
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 23, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 23 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_24 :
    Chebyshev.T ℤ 24 = fixedChebyshevTData_24 := by
  calc
    Chebyshev.T ℤ 24 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_23 - fixedChebyshevTData_22 :=
      fixedTyped_chebyshevT_link 22 23 24 fixedChebyshevTData_22 fixedChebyshevTData_23
        (by decide) (by decide) fixed_chebyshevT_typed_22 fixed_chebyshevT_typed_23
    _ = fixedChebyshevTData_24 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_23, fixedChebyshevTData_22, fixedChebyshevTData_24, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_23, fixedChebyshevTData_22, fixedChebyshevTData_24, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 24
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 24, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 24 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

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

def fixedReversedTData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (43520 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1462272 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (25798656 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-275185664 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (1926299648 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-9313976320 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-80648077312 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (148562247680 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-200655503360 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (196293427200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-135291469824 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (62277025792 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (2147483648 : ℤ)

def fixedReversedTCoeff_32 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-512 : ℤ) else 0) +
    (if 58 = n then (43520 : ℤ) else 0) +
    (if 56 = n then (-1462272 : ℤ) else 0) +
    (if 54 = n then (25798656 : ℤ) else 0) +
    (if 52 = n then (-275185664 : ℤ) else 0) +
    (if 50 = n then (1926299648 : ℤ) else 0) +
    (if 48 = n then (-9313976320 : ℤ) else 0) +
    (if 46 = n then (32133218304 : ℤ) else 0) +
    (if 44 = n then (-80648077312 : ℤ) else 0) +
    (if 42 = n then (148562247680 : ℤ) else 0) +
    (if 40 = n then (-200655503360 : ℤ) else 0) +
    (if 38 = n then (196293427200 : ℤ) else 0) +
    (if 36 = n then (-135291469824 : ℤ) else 0) +
    (if 34 = n then (62277025792 : ℤ) else 0) +
    (if 32 = n then (-17179869184 : ℤ) else 0) +
    (if 30 = n then (2147483648 : ℤ) else 0)

theorem fixed_reversedT_typed_data_32 : reversedRow 63 fixedChebyshevTData_32 = fixedReversedTData_32 := by
  simp only [fixedChebyshevTData_32, fixedReversedTData_32, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-512 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (43520 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-1462272 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (25798656 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-275185664 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (1926299648 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-9313976320 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (32133218304 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-80648077312 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (148562247680 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-200655503360 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (196293427200 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-135291469824 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (62277025792 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-17179869184 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (2147483648 : ℤ) 32 (by decide)]

theorem fixed_reversedT_typed_coeff_32 (n : ℕ) :
    fixedReversedTData_32.coeff n = fixedReversedTCoeff_32 n := by
  simp only [fixedReversedTData_32, fixedReversedTCoeff_32, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_32 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_32 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_32, if_neg, add_zero]

def fixedReversedTData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (33 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-5984 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (323136 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-8186112 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (118243840 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-1083543552 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (6723526656 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-29455450112 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (93564370944 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-218864025600 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (379364311040 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-485826232320 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (453437816832 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-299708186624 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (132875550720 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-35433480192 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (4294967296 : ℤ)

def fixedReversedTCoeff_33 (n : ℕ) : ℤ :=
    (if 61 = n then (33 : ℤ) else 0) +
    (if 59 = n then (-5984 : ℤ) else 0) +
    (if 57 = n then (323136 : ℤ) else 0) +
    (if 55 = n then (-8186112 : ℤ) else 0) +
    (if 53 = n then (118243840 : ℤ) else 0) +
    (if 51 = n then (-1083543552 : ℤ) else 0) +
    (if 49 = n then (6723526656 : ℤ) else 0) +
    (if 47 = n then (-29455450112 : ℤ) else 0) +
    (if 45 = n then (93564370944 : ℤ) else 0) +
    (if 43 = n then (-218864025600 : ℤ) else 0) +
    (if 41 = n then (379364311040 : ℤ) else 0) +
    (if 39 = n then (-485826232320 : ℤ) else 0) +
    (if 37 = n then (453437816832 : ℤ) else 0) +
    (if 35 = n then (-299708186624 : ℤ) else 0) +
    (if 33 = n then (132875550720 : ℤ) else 0) +
    (if 31 = n then (-35433480192 : ℤ) else 0) +
    (if 29 = n then (4294967296 : ℤ) else 0)

theorem fixed_reversedT_typed_data_33 : reversedRow 63 fixedChebyshevTData_33 = fixedReversedTData_33 := by
  simp only [fixedChebyshevTData_33, fixedReversedTData_33, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (33 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-5984 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (323136 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-8186112 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (118243840 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-1083543552 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (6723526656 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-29455450112 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (93564370944 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-218864025600 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (379364311040 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-485826232320 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (453437816832 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-299708186624 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (132875550720 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-35433480192 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (4294967296 : ℤ) 33 (by decide)]

theorem fixed_reversedT_typed_coeff_33 (n : ℕ) :
    fixedReversedTData_33.coeff n = fixedReversedTCoeff_33 n := by
  simp only [fixedReversedTData_33, fixedReversedTCoeff_33, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_33 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_33 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_33, if_neg, add_zero]

def fixedReversedTData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (578 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-55488 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2108544 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-42170880 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (511673344 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-4093386752 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (22761029632 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-91044118528 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (267776819200 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-586290298880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (959384125440 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1167945891840 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1042167103488 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-661693399040 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (282930970624 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-73014444032 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (8589934592 : ℤ)

def fixedReversedTCoeff_34 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (578 : ℤ) else 0) +
    (if 58 = n then (-55488 : ℤ) else 0) +
    (if 56 = n then (2108544 : ℤ) else 0) +
    (if 54 = n then (-42170880 : ℤ) else 0) +
    (if 52 = n then (511673344 : ℤ) else 0) +
    (if 50 = n then (-4093386752 : ℤ) else 0) +
    (if 48 = n then (22761029632 : ℤ) else 0) +
    (if 46 = n then (-91044118528 : ℤ) else 0) +
    (if 44 = n then (267776819200 : ℤ) else 0) +
    (if 42 = n then (-586290298880 : ℤ) else 0) +
    (if 40 = n then (959384125440 : ℤ) else 0) +
    (if 38 = n then (-1167945891840 : ℤ) else 0) +
    (if 36 = n then (1042167103488 : ℤ) else 0) +
    (if 34 = n then (-661693399040 : ℤ) else 0) +
    (if 32 = n then (282930970624 : ℤ) else 0) +
    (if 30 = n then (-73014444032 : ℤ) else 0) +
    (if 28 = n then (8589934592 : ℤ) else 0)

theorem fixed_reversedT_typed_data_34 : reversedRow 63 fixedChebyshevTData_34 = fixedReversedTData_34 := by
  simp only [fixedChebyshevTData_34, fixedReversedTData_34, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (578 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-55488 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (2108544 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-42170880 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (511673344 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-4093386752 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (22761029632 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-91044118528 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (267776819200 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-586290298880 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (959384125440 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-1167945891840 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (1042167103488 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-661693399040 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (282930970624 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-73014444032 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (8589934592 : ℤ) 34 (by decide)]

theorem fixed_reversedT_typed_coeff_34 (n : ℕ) :
    fixedReversedTData_34.coeff n = fixedReversedTCoeff_34 n := by
  simp only [fixedReversedTData_34, fixedReversedTCoeff_34, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_34 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_34 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_34, if_neg, add_zero]

def fixedReversedTData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-35 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (7140 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-434112 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (12403200 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-202585600 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2106890240 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-14910300160 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (74977509376 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-275652608000 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (754417664000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1551944908800 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (2404594483200 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2789329600512 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2384042393600 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-1456262348800 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (601295421440 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-150323855360 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (17179869184 : ℤ)

def fixedReversedTCoeff_35 (n : ℕ) : ℤ :=
    (if 61 = n then (-35 : ℤ) else 0) +
    (if 59 = n then (7140 : ℤ) else 0) +
    (if 57 = n then (-434112 : ℤ) else 0) +
    (if 55 = n then (12403200 : ℤ) else 0) +
    (if 53 = n then (-202585600 : ℤ) else 0) +
    (if 51 = n then (2106890240 : ℤ) else 0) +
    (if 49 = n then (-14910300160 : ℤ) else 0) +
    (if 47 = n then (74977509376 : ℤ) else 0) +
    (if 45 = n then (-275652608000 : ℤ) else 0) +
    (if 43 = n then (754417664000 : ℤ) else 0) +
    (if 41 = n then (-1551944908800 : ℤ) else 0) +
    (if 39 = n then (2404594483200 : ℤ) else 0) +
    (if 37 = n then (-2789329600512 : ℤ) else 0) +
    (if 35 = n then (2384042393600 : ℤ) else 0) +
    (if 33 = n then (-1456262348800 : ℤ) else 0) +
    (if 31 = n then (601295421440 : ℤ) else 0) +
    (if 29 = n then (-150323855360 : ℤ) else 0) +
    (if 27 = n then (17179869184 : ℤ) else 0)

theorem fixed_reversedT_typed_data_35 : reversedRow 63 fixedChebyshevTData_35 = fixedReversedTData_35 := by
  simp only [fixedChebyshevTData_35, fixedReversedTData_35, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-35 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (7140 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-434112 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (12403200 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-202585600 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (2106890240 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-14910300160 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (74977509376 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-275652608000 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (754417664000 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-1551944908800 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (2404594483200 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-2789329600512 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (2384042393600 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-1456262348800 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (601295421440 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-150323855360 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (17179869184 : ℤ) 35 (by decide)]

theorem fixed_reversedT_typed_coeff_35 (n : ℕ) :
    fixedReversedTData_35.coeff n = fixedReversedTCoeff_35 n := by
  simp only [fixedReversedTData_35, fixedReversedTCoeff_35, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_35 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_35 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_35, if_neg, add_zero]

def fixedReversedTData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-648 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (69768 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-2976768 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (66977280 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-916844544 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (8307167232 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-52581629952 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (240999137280 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-819082035200 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (2095125626880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-4063273943040 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (5977134858240 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-6620826304512 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (5429778186240 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-3195455668224 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (1275605286912 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-309237645312 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (34359738368 : ℤ)

def fixedReversedTCoeff_36 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-648 : ℤ) else 0) +
    (if 58 = n then (69768 : ℤ) else 0) +
    (if 56 = n then (-2976768 : ℤ) else 0) +
    (if 54 = n then (66977280 : ℤ) else 0) +
    (if 52 = n then (-916844544 : ℤ) else 0) +
    (if 50 = n then (8307167232 : ℤ) else 0) +
    (if 48 = n then (-52581629952 : ℤ) else 0) +
    (if 46 = n then (240999137280 : ℤ) else 0) +
    (if 44 = n then (-819082035200 : ℤ) else 0) +
    (if 42 = n then (2095125626880 : ℤ) else 0) +
    (if 40 = n then (-4063273943040 : ℤ) else 0) +
    (if 38 = n then (5977134858240 : ℤ) else 0) +
    (if 36 = n then (-6620826304512 : ℤ) else 0) +
    (if 34 = n then (5429778186240 : ℤ) else 0) +
    (if 32 = n then (-3195455668224 : ℤ) else 0) +
    (if 30 = n then (1275605286912 : ℤ) else 0) +
    (if 28 = n then (-309237645312 : ℤ) else 0) +
    (if 26 = n then (34359738368 : ℤ) else 0)

theorem fixed_reversedT_typed_data_36 : reversedRow 63 fixedChebyshevTData_36 = fixedReversedTData_36 := by
  simp only [fixedChebyshevTData_36, fixedReversedTData_36, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-648 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (69768 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-2976768 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (66977280 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-916844544 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (8307167232 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-52581629952 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (240999137280 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-819082035200 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (2095125626880 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-4063273943040 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (5977134858240 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-6620826304512 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (5429778186240 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-3195455668224 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (1275605286912 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-309237645312 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (34359738368 : ℤ) 36 (by decide)]

theorem fixed_reversedT_typed_coeff_36 (n : ℕ) :
    fixedReversedTData_36.coeff n = fixedReversedTCoeff_36 n := by
  simp only [fixedReversedTData_36, fixedReversedTCoeff_36, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_36 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_36 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_36, if_neg, add_zero]

def fixedReversedTData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (37 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-8436 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (573648 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-18356736 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (336540160 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-3940579328 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (31524634624 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-180140769280 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (757650882560 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-2392581734400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (5742196162560 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-10531142369280 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (14743599316992 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-15625695002624 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (12315818721280 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-6992206757888 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (2701534429184 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-635655159808 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (68719476736 : ℤ)

def fixedReversedTCoeff_37 (n : ℕ) : ℤ :=
    (if 61 = n then (37 : ℤ) else 0) +
    (if 59 = n then (-8436 : ℤ) else 0) +
    (if 57 = n then (573648 : ℤ) else 0) +
    (if 55 = n then (-18356736 : ℤ) else 0) +
    (if 53 = n then (336540160 : ℤ) else 0) +
    (if 51 = n then (-3940579328 : ℤ) else 0) +
    (if 49 = n then (31524634624 : ℤ) else 0) +
    (if 47 = n then (-180140769280 : ℤ) else 0) +
    (if 45 = n then (757650882560 : ℤ) else 0) +
    (if 43 = n then (-2392581734400 : ℤ) else 0) +
    (if 41 = n then (5742196162560 : ℤ) else 0) +
    (if 39 = n then (-10531142369280 : ℤ) else 0) +
    (if 37 = n then (14743599316992 : ℤ) else 0) +
    (if 35 = n then (-15625695002624 : ℤ) else 0) +
    (if 33 = n then (12315818721280 : ℤ) else 0) +
    (if 31 = n then (-6992206757888 : ℤ) else 0) +
    (if 29 = n then (2701534429184 : ℤ) else 0) +
    (if 27 = n then (-635655159808 : ℤ) else 0) +
    (if 25 = n then (68719476736 : ℤ) else 0)

theorem fixed_reversedT_typed_data_37 : reversedRow 63 fixedChebyshevTData_37 = fixedReversedTData_37 := by
  simp only [fixedChebyshevTData_37, fixedReversedTData_37, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (37 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-8436 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (573648 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-18356736 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (336540160 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-3940579328 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (31524634624 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-180140769280 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (757650882560 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-2392581734400 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (5742196162560 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-10531142369280 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (14743599316992 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-15625695002624 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (12315818721280 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-6992206757888 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (2701534429184 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (-635655159808 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (68719476736 : ℤ) 37 (by decide)]

theorem fixed_reversedT_typed_coeff_37 (n : ℕ) :
    fixedReversedTData_37.coeff n = fixedReversedTCoeff_37 n := by
  simp only [fixedReversedTData_37, fixedReversedTCoeff_37, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_37 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_37 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_37, if_neg, add_zero]

def fixedReversedTData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (722 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-86640 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (4124064 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-103690752 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1589924864 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-16188325888 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (115630899200 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-601280675840 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (2334383800320 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-6880289095680 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (15547666268160 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-27039419596800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (36108024938496 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-36681168191488 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (27827093110784 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-15260018802688 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (5712306503680 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-1305670057984 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (137438953472 : ℤ)

def fixedReversedTCoeff_38 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (722 : ℤ) else 0) +
    (if 58 = n then (-86640 : ℤ) else 0) +
    (if 56 = n then (4124064 : ℤ) else 0) +
    (if 54 = n then (-103690752 : ℤ) else 0) +
    (if 52 = n then (1589924864 : ℤ) else 0) +
    (if 50 = n then (-16188325888 : ℤ) else 0) +
    (if 48 = n then (115630899200 : ℤ) else 0) +
    (if 46 = n then (-601280675840 : ℤ) else 0) +
    (if 44 = n then (2334383800320 : ℤ) else 0) +
    (if 42 = n then (-6880289095680 : ℤ) else 0) +
    (if 40 = n then (15547666268160 : ℤ) else 0) +
    (if 38 = n then (-27039419596800 : ℤ) else 0) +
    (if 36 = n then (36108024938496 : ℤ) else 0) +
    (if 34 = n then (-36681168191488 : ℤ) else 0) +
    (if 32 = n then (27827093110784 : ℤ) else 0) +
    (if 30 = n then (-15260018802688 : ℤ) else 0) +
    (if 28 = n then (5712306503680 : ℤ) else 0) +
    (if 26 = n then (-1305670057984 : ℤ) else 0) +
    (if 24 = n then (137438953472 : ℤ) else 0)

theorem fixed_reversedT_typed_data_38 : reversedRow 63 fixedChebyshevTData_38 = fixedReversedTData_38 := by
  simp only [fixedChebyshevTData_38, fixedReversedTData_38, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (722 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-86640 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (4124064 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-103690752 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (1589924864 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-16188325888 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (115630899200 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-601280675840 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (2334383800320 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-6880289095680 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (15547666268160 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-27039419596800 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (36108024938496 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-36681168191488 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (27827093110784 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-15260018802688 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (5712306503680 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (-1305670057984 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (137438953472 : ℤ) 38 (by decide)]

theorem fixed_reversedT_typed_coeff_38 (n : ℕ) :
    fixedReversedTData_38.coeff n = fixedReversedTCoeff_38 n := by
  simp only [fixedReversedTData_38, fixedReversedTCoeff_38, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_38 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_38 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_38, if_neg, add_zero]






end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedU24To31
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan




































def fixedReversedUData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (5440 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-274176 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (6449664 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-85995520 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (722362368 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-4074864640 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (16066609152 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-45364543488 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (92851404800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-137950658560 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (147220070400 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-109924319232 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (54492397568 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-16106127360 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (2147483648 : ℤ)

def fixedReversedUCoeff_31 (n : ℕ) : ℤ :=
    (if 61 = n then (-32 : ℤ) else 0) +
    (if 59 = n then (5440 : ℤ) else 0) +
    (if 57 = n then (-274176 : ℤ) else 0) +
    (if 55 = n then (6449664 : ℤ) else 0) +
    (if 53 = n then (-85995520 : ℤ) else 0) +
    (if 51 = n then (722362368 : ℤ) else 0) +
    (if 49 = n then (-4074864640 : ℤ) else 0) +
    (if 47 = n then (16066609152 : ℤ) else 0) +
    (if 45 = n then (-45364543488 : ℤ) else 0) +
    (if 43 = n then (92851404800 : ℤ) else 0) +
    (if 41 = n then (-137950658560 : ℤ) else 0) +
    (if 39 = n then (147220070400 : ℤ) else 0) +
    (if 37 = n then (-109924319232 : ℤ) else 0) +
    (if 35 = n then (54492397568 : ℤ) else 0) +
    (if 33 = n then (-16106127360 : ℤ) else 0) +
    (if 31 = n then (2147483648 : ℤ) else 0)

theorem fixed_reversedU_typed_data_31 : reversedRow 63 fixedChebyshevUData_31 = fixedReversedUData_31 := by
  simp only [fixedChebyshevUData_31, fixedReversedUData_31, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-32 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (5440 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-274176 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (6449664 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-85995520 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (722362368 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-4074864640 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (16066609152 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-45364543488 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (92851404800 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-137950658560 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (147220070400 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-109924319232 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (54492397568 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-16106127360 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (2147483648 : ℤ) 31 (by decide)]

theorem fixed_reversedU_typed_coeff_31 (n : ℕ) :
    fixedReversedUData_31.coeff n = fixedReversedUCoeff_31 n := by
  simp only [fixedReversedUData_31, fixedReversedUCoeff_31, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_31 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_31 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_31, if_neg, add_zero]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow36
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 30 (2147483648 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-4294967296 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-15032385536 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (45097156608 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-124554051584 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-73014444032 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (270582939648 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (61001957376 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-392586854400 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-4362076160 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (401311006720 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-52093255680 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-297124495360 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (67914170368 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (161296154624 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-48514859008 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-64266436608 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (22819241984 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (18627952640 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-7387676672 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-3852599296 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1651113984 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (550371328 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-249387008 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-51597312 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (24336384 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (2924544 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1418752 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-87040 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (43008 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-511 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_36 (n : ℕ) : ℤ :=
    (if 30 = n then (2147483648 : ℤ) else 0) +
    (if 31 = n then (-4294967296 : ℤ) else 0) +
    (if 32 = n then (-15032385536 : ℤ) else 0) +
    (if 33 = n then (34359738368 : ℤ) else 0) +
    (if 34 = n then (45097156608 : ℤ) else 0) +
    (if 35 = n then (-124554051584 : ℤ) else 0) +
    (if 36 = n then (-73014444032 : ℤ) else 0) +
    (if 37 = n then (270582939648 : ℤ) else 0) +
    (if 38 = n then (61001957376 : ℤ) else 0) +
    (if 39 = n then (-392586854400 : ℤ) else 0) +
    (if 40 = n then (-4362076160 : ℤ) else 0) +
    (if 41 = n then (401311006720 : ℤ) else 0) +
    (if 42 = n then (-52093255680 : ℤ) else 0) +
    (if 43 = n then (-297124495360 : ℤ) else 0) +
    (if 44 = n then (67914170368 : ℤ) else 0) +
    (if 45 = n then (161296154624 : ℤ) else 0) +
    (if 46 = n then (-48514859008 : ℤ) else 0) +
    (if 47 = n then (-64266436608 : ℤ) else 0) +
    (if 48 = n then (22819241984 : ℤ) else 0) +
    (if 49 = n then (18627952640 : ℤ) else 0) +
    (if 50 = n then (-7387676672 : ℤ) else 0) +
    (if 51 = n then (-3852599296 : ℤ) else 0) +
    (if 52 = n then (1651113984 : ℤ) else 0) +
    (if 53 = n then (550371328 : ℤ) else 0) +
    (if 54 = n then (-249387008 : ℤ) else 0) +
    (if 55 = n then (-51597312 : ℤ) else 0) +
    (if 56 = n then (24336384 : ℤ) else 0) +
    (if 57 = n then (2924544 : ℤ) else 0) +
    (if 58 = n then (-1418752 : ℤ) else 0) +
    (if 59 = n then (-87040 : ℤ) else 0) +
    (if 60 = n then (43008 : ℤ) else 0) +
    (if 61 = n then (1024 : ℤ) else 0) +
    (if 62 = n then (-511 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_36 (n : ℕ) :
    fixedRowPData_36.coeff n = fixedRowPCoeff_36 n := by
  simp only [fixedRowPData_36, fixedRowPCoeff_36, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_36 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_36 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_36, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_36 : ∀ k : Fin 63,
    fixedReversedTCoeff_32 (k.val + 2) - 2 * fixedReversedTCoeff_32 (k.val + 1) + fixedReversedTCoeff_32 k.val = fixedRowPCoeff_36 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_36 :
    (1 - X) ^ 2 * fixedReversedTData_32 = fixedRowPData_36 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_32, fixed_rowP_typed_coeff_36]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_32, fixed_rowP_typed_coeff_36]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_32, fixed_rowP_typed_coeff_36]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_36 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_32 _ (by omega),
              fixed_reversedT_typed_tail_32 _ (by omega), fixed_reversedT_typed_tail_32 _ hn',
              fixed_rowP_typed_tail_36 _ (by omega)]
            decide

theorem fixed_rowP_typed_36 : rowP 1 36 = fixedRowPData_36 := by
  calc
    rowP 1 36 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_32 :=
      fixedTyped_rowP_of_parameters 1 36 2 63 32 fixedChebyshevTData_32
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_32
    _ = fixedRowPData_36 := by
      rw [fixed_reversedT_typed_data_32, fixed_rowP_typed_factor_36]

def fixedRowDData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 31 (2147483648 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-4294967296 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-13958643712 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (32212254720 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (38386270208 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-108984795136 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-55431921664 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (219848638464 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (37295751168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-294440140800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (9269411840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (275901317120 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-45099253760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-185702809600 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (47486861312 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (90729086976 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-29297934336 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (11991744512 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (8149729280 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-3352502272 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-1444724736 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (636366848 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (171991040 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-79545856 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-12899328 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (6175488 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (548352 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-268736 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-10880 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (5408 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-32 : ℤ)

def fixedRowDCoeff_36 (n : ℕ) : ℤ :=
    (if 31 = n then (2147483648 : ℤ) else 0) +
    (if 32 = n then (-4294967296 : ℤ) else 0) +
    (if 33 = n then (-13958643712 : ℤ) else 0) +
    (if 34 = n then (32212254720 : ℤ) else 0) +
    (if 35 = n then (38386270208 : ℤ) else 0) +
    (if 36 = n then (-108984795136 : ℤ) else 0) +
    (if 37 = n then (-55431921664 : ℤ) else 0) +
    (if 38 = n then (219848638464 : ℤ) else 0) +
    (if 39 = n then (37295751168 : ℤ) else 0) +
    (if 40 = n then (-294440140800 : ℤ) else 0) +
    (if 41 = n then (9269411840 : ℤ) else 0) +
    (if 42 = n then (275901317120 : ℤ) else 0) +
    (if 43 = n then (-45099253760 : ℤ) else 0) +
    (if 44 = n then (-185702809600 : ℤ) else 0) +
    (if 45 = n then (47486861312 : ℤ) else 0) +
    (if 46 = n then (90729086976 : ℤ) else 0) +
    (if 47 = n then (-29297934336 : ℤ) else 0) +
    (if 48 = n then (-32133218304 : ℤ) else 0) +
    (if 49 = n then (11991744512 : ℤ) else 0) +
    (if 50 = n then (8149729280 : ℤ) else 0) +
    (if 51 = n then (-3352502272 : ℤ) else 0) +
    (if 52 = n then (-1444724736 : ℤ) else 0) +
    (if 53 = n then (636366848 : ℤ) else 0) +
    (if 54 = n then (171991040 : ℤ) else 0) +
    (if 55 = n then (-79545856 : ℤ) else 0) +
    (if 56 = n then (-12899328 : ℤ) else 0) +
    (if 57 = n then (6175488 : ℤ) else 0) +
    (if 58 = n then (548352 : ℤ) else 0) +
    (if 59 = n then (-268736 : ℤ) else 0) +
    (if 60 = n then (-10880 : ℤ) else 0) +
    (if 61 = n then (5408 : ℤ) else 0) +
    (if 62 = n then (64 : ℤ) else 0) +
    (if 63 = n then (-32 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_36 (n : ℕ) :
    fixedRowDData_36.coeff n = fixedRowDCoeff_36 n := by
  simp only [fixedRowDData_36, fixedRowDCoeff_36, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_36 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_36 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_36, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_36 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_31 (k.val + 2) - 2 * fixedReversedUCoeff_31 (k.val + 1) + fixedReversedUCoeff_31 k.val) = fixedRowDCoeff_36 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_36 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_31 = fixedRowDData_36 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_31, fixed_rowD_typed_coeff_36]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_31, fixed_rowD_typed_coeff_36]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_31, fixed_rowD_typed_coeff_36]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_36 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_31 _ (by omega),
              fixed_reversedU_typed_tail_31 _ (by omega), fixed_reversedU_typed_tail_31 _ hn',
              fixed_rowD_typed_tail_36 _ (by omega)]
            decide

theorem fixed_rowD_typed_36 : rowD 1 36 = fixedRowDData_36 := by
  calc
    rowD 1 36 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_31 :=
      fixedTyped_rowD_of_parameters 1 36 2 63 31 (1)
        fixedChebyshevUData_31 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_31
    _ = fixedRowDData_36 := by
      rw [fixed_reversedU_typed_data_31, fixed_rowD_typed_factor_36]

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

def fixedReversedUData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-544 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (48960 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1736448 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (32248320 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-361181184 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (2648662016 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-13388840960 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (48199827456 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-126012620800 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (241413652480 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-338606161920 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (343513497600 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-245215789056 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (116769423360 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-33285996544 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (4294967296 : ℤ)

def fixedReversedUCoeff_32 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-544 : ℤ) else 0) +
    (if 58 = n then (48960 : ℤ) else 0) +
    (if 56 = n then (-1736448 : ℤ) else 0) +
    (if 54 = n then (32248320 : ℤ) else 0) +
    (if 52 = n then (-361181184 : ℤ) else 0) +
    (if 50 = n then (2648662016 : ℤ) else 0) +
    (if 48 = n then (-13388840960 : ℤ) else 0) +
    (if 46 = n then (48199827456 : ℤ) else 0) +
    (if 44 = n then (-126012620800 : ℤ) else 0) +
    (if 42 = n then (241413652480 : ℤ) else 0) +
    (if 40 = n then (-338606161920 : ℤ) else 0) +
    (if 38 = n then (343513497600 : ℤ) else 0) +
    (if 36 = n then (-245215789056 : ℤ) else 0) +
    (if 34 = n then (116769423360 : ℤ) else 0) +
    (if 32 = n then (-33285996544 : ℤ) else 0) +
    (if 30 = n then (4294967296 : ℤ) else 0)

theorem fixed_reversedU_typed_data_32 : reversedRow 63 fixedChebyshevUData_32 = fixedReversedUData_32 := by
  simp only [fixedChebyshevUData_32, fixedReversedUData_32, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-544 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (48960 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-1736448 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (32248320 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-361181184 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (2648662016 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-13388840960 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (48199827456 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-126012620800 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (241413652480 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-338606161920 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (343513497600 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-245215789056 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (116769423360 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-33285996544 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (4294967296 : ℤ) 32 (by decide)]

theorem fixed_reversedU_typed_coeff_32 (n : ℕ) :
    fixedReversedUData_32.coeff n = fixedReversedUCoeff_32 n := by
  simp only [fixedReversedUData_32, fixedReversedUCoeff_32, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_32 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_32 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_32, if_neg, add_zero]

def fixedReversedUData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (34 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-6528 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (372096 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-9922560 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (150492160 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-1444724736 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (9372188672 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-42844291072 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (141764198400 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-344876646400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (620777963520 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-824432394240 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (796951314432 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-544923975680 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (249644974080 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (8589934592 : ℤ)

def fixedReversedUCoeff_33 (n : ℕ) : ℤ :=
    (if 61 = n then (34 : ℤ) else 0) +
    (if 59 = n then (-6528 : ℤ) else 0) +
    (if 57 = n then (372096 : ℤ) else 0) +
    (if 55 = n then (-9922560 : ℤ) else 0) +
    (if 53 = n then (150492160 : ℤ) else 0) +
    (if 51 = n then (-1444724736 : ℤ) else 0) +
    (if 49 = n then (9372188672 : ℤ) else 0) +
    (if 47 = n then (-42844291072 : ℤ) else 0) +
    (if 45 = n then (141764198400 : ℤ) else 0) +
    (if 43 = n then (-344876646400 : ℤ) else 0) +
    (if 41 = n then (620777963520 : ℤ) else 0) +
    (if 39 = n then (-824432394240 : ℤ) else 0) +
    (if 37 = n then (796951314432 : ℤ) else 0) +
    (if 35 = n then (-544923975680 : ℤ) else 0) +
    (if 33 = n then (249644974080 : ℤ) else 0) +
    (if 31 = n then (-68719476736 : ℤ) else 0) +
    (if 29 = n then (8589934592 : ℤ) else 0)

theorem fixed_reversedU_typed_data_33 : reversedRow 63 fixedChebyshevUData_33 = fixedReversedUData_33 := by
  simp only [fixedChebyshevUData_33, fixedReversedUData_33, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (34 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-6528 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (372096 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-9922560 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (150492160 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-1444724736 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (9372188672 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-42844291072 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (141764198400 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-344876646400 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (620777963520 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-824432394240 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (796951314432 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-544923975680 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (249644974080 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-68719476736 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (8589934592 : ℤ) 33 (by decide)]

theorem fixed_reversedU_typed_coeff_33 (n : ℕ) :
    fixedReversedUData_33.coeff n = fixedReversedUCoeff_33 n := by
  simp only [fixedReversedUData_33, fixedReversedUCoeff_33, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_33 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_33 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_33, if_neg, add_zero]

def fixedReversedUData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (612 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-62016 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2480640 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-52093440 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (662165504 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-5538111488 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-133888409600 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (409541017600 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-931166945280 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1580162088960 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1992378286080 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1839118417920 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1206617374720 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (532575944704 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-141733920768 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (17179869184 : ℤ)

def fixedReversedUCoeff_34 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (612 : ℤ) else 0) +
    (if 58 = n then (-62016 : ℤ) else 0) +
    (if 56 = n then (2480640 : ℤ) else 0) +
    (if 54 = n then (-52093440 : ℤ) else 0) +
    (if 52 = n then (662165504 : ℤ) else 0) +
    (if 50 = n then (-5538111488 : ℤ) else 0) +
    (if 48 = n then (32133218304 : ℤ) else 0) +
    (if 46 = n then (-133888409600 : ℤ) else 0) +
    (if 44 = n then (409541017600 : ℤ) else 0) +
    (if 42 = n then (-931166945280 : ℤ) else 0) +
    (if 40 = n then (1580162088960 : ℤ) else 0) +
    (if 38 = n then (-1992378286080 : ℤ) else 0) +
    (if 36 = n then (1839118417920 : ℤ) else 0) +
    (if 34 = n then (-1206617374720 : ℤ) else 0) +
    (if 32 = n then (532575944704 : ℤ) else 0) +
    (if 30 = n then (-141733920768 : ℤ) else 0) +
    (if 28 = n then (17179869184 : ℤ) else 0)

theorem fixed_reversedU_typed_data_34 : reversedRow 63 fixedChebyshevUData_34 = fixedReversedUData_34 := by
  simp only [fixedChebyshevUData_34, fixedReversedUData_34, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (612 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-62016 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (2480640 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-52093440 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (662165504 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-5538111488 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (32133218304 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-133888409600 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (409541017600 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-931166945280 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (1580162088960 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-1992378286080 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (1839118417920 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-1206617374720 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (532575944704 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-141733920768 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (17179869184 : ℤ) 34 (by decide)]

theorem fixed_reversedU_typed_coeff_34 (n : ℕ) :
    fixedReversedUData_34.coeff n = fixedReversedUCoeff_34 n := by
  simp only [fixedReversedUData_34, fixedReversedUCoeff_34, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_34 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_34 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_34, if_neg, add_zero]

def fixedReversedUData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-36 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (7752 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-496128 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (14883840 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-254679040 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2769055744 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-20448411648 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (107110727680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-409541017600 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (1163958681600 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-2483111854080 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (3984756572160 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-4781707886592 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (4223160811520 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2662879723520 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (1133871366144 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-292057776128 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (34359738368 : ℤ)

def fixedReversedUCoeff_35 (n : ℕ) : ℤ :=
    (if 61 = n then (-36 : ℤ) else 0) +
    (if 59 = n then (7752 : ℤ) else 0) +
    (if 57 = n then (-496128 : ℤ) else 0) +
    (if 55 = n then (14883840 : ℤ) else 0) +
    (if 53 = n then (-254679040 : ℤ) else 0) +
    (if 51 = n then (2769055744 : ℤ) else 0) +
    (if 49 = n then (-20448411648 : ℤ) else 0) +
    (if 47 = n then (107110727680 : ℤ) else 0) +
    (if 45 = n then (-409541017600 : ℤ) else 0) +
    (if 43 = n then (1163958681600 : ℤ) else 0) +
    (if 41 = n then (-2483111854080 : ℤ) else 0) +
    (if 39 = n then (3984756572160 : ℤ) else 0) +
    (if 37 = n then (-4781707886592 : ℤ) else 0) +
    (if 35 = n then (4223160811520 : ℤ) else 0) +
    (if 33 = n then (-2662879723520 : ℤ) else 0) +
    (if 31 = n then (1133871366144 : ℤ) else 0) +
    (if 29 = n then (-292057776128 : ℤ) else 0) +
    (if 27 = n then (34359738368 : ℤ) else 0)

theorem fixed_reversedU_typed_data_35 : reversedRow 63 fixedChebyshevUData_35 = fixedReversedUData_35 := by
  simp only [fixedChebyshevUData_35, fixedReversedUData_35, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-36 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (7752 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-496128 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (14883840 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-254679040 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (2769055744 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-20448411648 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (107110727680 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-409541017600 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (1163958681600 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-2483111854080 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (3984756572160 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-4781707886592 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (4223160811520 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-2662879723520 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (1133871366144 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-292057776128 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (34359738368 : ℤ) 35 (by decide)]

theorem fixed_reversedU_typed_coeff_35 (n : ℕ) :
    fixedReversedUData_35.coeff n = fixedReversedUCoeff_35 n := by
  simp only [fixedReversedUData_35, fixedReversedUCoeff_35, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_35 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_35 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_35, if_neg, add_zero]

def fixedReversedUData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-684 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (77520 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-3472896 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (81861120 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-1171523584 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (11076222976 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-73030041600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (348109864960 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-1228623052800 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (3259084308480 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-6546385797120 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (9961891430400 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-11402534191104 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (9652938997760 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-5858335391744 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (2409476653056 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-601295421440 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (68719476736 : ℤ)

def fixedReversedUCoeff_36 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-684 : ℤ) else 0) +
    (if 58 = n then (77520 : ℤ) else 0) +
    (if 56 = n then (-3472896 : ℤ) else 0) +
    (if 54 = n then (81861120 : ℤ) else 0) +
    (if 52 = n then (-1171523584 : ℤ) else 0) +
    (if 50 = n then (11076222976 : ℤ) else 0) +
    (if 48 = n then (-73030041600 : ℤ) else 0) +
    (if 46 = n then (348109864960 : ℤ) else 0) +
    (if 44 = n then (-1228623052800 : ℤ) else 0) +
    (if 42 = n then (3259084308480 : ℤ) else 0) +
    (if 40 = n then (-6546385797120 : ℤ) else 0) +
    (if 38 = n then (9961891430400 : ℤ) else 0) +
    (if 36 = n then (-11402534191104 : ℤ) else 0) +
    (if 34 = n then (9652938997760 : ℤ) else 0) +
    (if 32 = n then (-5858335391744 : ℤ) else 0) +
    (if 30 = n then (2409476653056 : ℤ) else 0) +
    (if 28 = n then (-601295421440 : ℤ) else 0) +
    (if 26 = n then (68719476736 : ℤ) else 0)

theorem fixed_reversedU_typed_data_36 : reversedRow 63 fixedChebyshevUData_36 = fixedReversedUData_36 := by
  simp only [fixedChebyshevUData_36, fixedReversedUData_36, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-684 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (77520 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-3472896 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (81861120 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-1171523584 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (11076222976 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-73030041600 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (348109864960 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-1228623052800 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (3259084308480 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-6546385797120 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (9961891430400 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-11402534191104 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (9652938997760 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-5858335391744 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (2409476653056 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-601295421440 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (68719476736 : ℤ) 36 (by decide)]

theorem fixed_reversedU_typed_coeff_36 (n : ℕ) :
    fixedReversedUData_36.coeff n = fixedReversedUCoeff_36 n := by
  simp only [fixedReversedUData_36, fixedReversedUCoeff_36, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_36 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_36 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_36, if_neg, add_zero]

def fixedReversedUData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (38 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-9120 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (651168 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-21829632 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (418401280 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-5112102912 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (42600857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-253170810880 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (1105760747520 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-3621204787200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (9001280471040 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-17077528166400 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (24705490747392 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-27028229193728 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (21968757719040 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-12850542149632 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (5111011082240 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-1236950581248 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (137438953472 : ℤ)

def fixedReversedUCoeff_37 (n : ℕ) : ℤ :=
    (if 61 = n then (38 : ℤ) else 0) +
    (if 59 = n then (-9120 : ℤ) else 0) +
    (if 57 = n then (651168 : ℤ) else 0) +
    (if 55 = n then (-21829632 : ℤ) else 0) +
    (if 53 = n then (418401280 : ℤ) else 0) +
    (if 51 = n then (-5112102912 : ℤ) else 0) +
    (if 49 = n then (42600857600 : ℤ) else 0) +
    (if 47 = n then (-253170810880 : ℤ) else 0) +
    (if 45 = n then (1105760747520 : ℤ) else 0) +
    (if 43 = n then (-3621204787200 : ℤ) else 0) +
    (if 41 = n then (9001280471040 : ℤ) else 0) +
    (if 39 = n then (-17077528166400 : ℤ) else 0) +
    (if 37 = n then (24705490747392 : ℤ) else 0) +
    (if 35 = n then (-27028229193728 : ℤ) else 0) +
    (if 33 = n then (21968757719040 : ℤ) else 0) +
    (if 31 = n then (-12850542149632 : ℤ) else 0) +
    (if 29 = n then (5111011082240 : ℤ) else 0) +
    (if 27 = n then (-1236950581248 : ℤ) else 0) +
    (if 25 = n then (137438953472 : ℤ) else 0)

theorem fixed_reversedU_typed_data_37 : reversedRow 63 fixedChebyshevUData_37 = fixedReversedUData_37 := by
  simp only [fixedChebyshevUData_37, fixedReversedUData_37, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (38 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-9120 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (651168 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-21829632 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (418401280 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-5112102912 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (42600857600 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-253170810880 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (1105760747520 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-3621204787200 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (9001280471040 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-17077528166400 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (24705490747392 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-27028229193728 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (21968757719040 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-12850542149632 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (5111011082240 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (-1236950581248 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (137438953472 : ℤ) 37 (by decide)]

theorem fixed_reversedU_typed_coeff_37 (n : ℕ) :
    fixedReversedUData_37.coeff n = fixedReversedUCoeff_37 n := by
  simp only [fixedReversedUData_37, fixedReversedUCoeff_37, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_37 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_37 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_37, if_neg, add_zero]











end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow37
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 29 (4294967296 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-8589934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-31138512896 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (70866960384 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (97442070528 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-265751101440 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-166832635904 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (599416373248 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (153729630208 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-906875633664 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-32388415488 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (971652464640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-106461921280 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-758728622080 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (160500285440 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (437728051200 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-125299654656 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-187128741888 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (64108920832 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (58910900224 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-22731923456 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-13447053312 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (5639983104 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2167087104 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-965299712 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-236487680 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (110057728 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (16372224 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-7862976 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-646272 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (317152 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (11968 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-5951 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-66 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (33 : ℤ)

def fixedRowPCoeff_37 (n : ℕ) : ℤ :=
    (if 29 = n then (4294967296 : ℤ) else 0) +
    (if 30 = n then (-8589934592 : ℤ) else 0) +
    (if 31 = n then (-31138512896 : ℤ) else 0) +
    (if 32 = n then (70866960384 : ℤ) else 0) +
    (if 33 = n then (97442070528 : ℤ) else 0) +
    (if 34 = n then (-265751101440 : ℤ) else 0) +
    (if 35 = n then (-166832635904 : ℤ) else 0) +
    (if 36 = n then (599416373248 : ℤ) else 0) +
    (if 37 = n then (153729630208 : ℤ) else 0) +
    (if 38 = n then (-906875633664 : ℤ) else 0) +
    (if 39 = n then (-32388415488 : ℤ) else 0) +
    (if 40 = n then (971652464640 : ℤ) else 0) +
    (if 41 = n then (-106461921280 : ℤ) else 0) +
    (if 42 = n then (-758728622080 : ℤ) else 0) +
    (if 43 = n then (160500285440 : ℤ) else 0) +
    (if 44 = n then (437728051200 : ℤ) else 0) +
    (if 45 = n then (-125299654656 : ℤ) else 0) +
    (if 46 = n then (-187128741888 : ℤ) else 0) +
    (if 47 = n then (64108920832 : ℤ) else 0) +
    (if 48 = n then (58910900224 : ℤ) else 0) +
    (if 49 = n then (-22731923456 : ℤ) else 0) +
    (if 50 = n then (-13447053312 : ℤ) else 0) +
    (if 51 = n then (5639983104 : ℤ) else 0) +
    (if 52 = n then (2167087104 : ℤ) else 0) +
    (if 53 = n then (-965299712 : ℤ) else 0) +
    (if 54 = n then (-236487680 : ℤ) else 0) +
    (if 55 = n then (110057728 : ℤ) else 0) +
    (if 56 = n then (16372224 : ℤ) else 0) +
    (if 57 = n then (-7862976 : ℤ) else 0) +
    (if 58 = n then (-646272 : ℤ) else 0) +
    (if 59 = n then (317152 : ℤ) else 0) +
    (if 60 = n then (11968 : ℤ) else 0) +
    (if 61 = n then (-5951 : ℤ) else 0) +
    (if 62 = n then (-66 : ℤ) else 0) +
    (if 63 = n then (33 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_37 (n : ℕ) :
    fixedRowPData_37.coeff n = fixedRowPCoeff_37 n := by
  simp only [fixedRowPData_37, fixedRowPCoeff_37, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_37 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_37 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_37, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_37 : ∀ k : Fin 63,
    fixedReversedTCoeff_33 (k.val + 2) - 2 * fixedReversedTCoeff_33 (k.val + 1) + fixedReversedTCoeff_33 k.val = fixedRowPCoeff_37 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_37 :
    (1 - X) ^ 2 * fixedReversedTData_33 = fixedRowPData_37 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_33, fixed_rowP_typed_coeff_37]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_33, fixed_rowP_typed_coeff_37]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_33, fixed_rowP_typed_coeff_37]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_37 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_33 _ (by omega),
              fixed_reversedT_typed_tail_33 _ (by omega), fixed_reversedT_typed_tail_33 _ hn',
              fixed_rowP_typed_tail_37 _ (by omega)]
            decide

theorem fixed_rowP_typed_37 : rowP 1 37 = fixedRowPData_37 := by
  calc
    rowP 1 37 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_33 :=
      fixedTyped_rowP_of_parameters 1 37 2 63 33 fixedChebyshevTData_33
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_33
    _ = fixedRowPData_37 := by
      rw [fixed_reversedT_typed_data_33, fixed_rowP_typed_factor_37]

def fixedRowDData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 30 (4294967296 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-8589934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-28991029248 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (66571993088 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (83483426816 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-233538846720 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-128446365696 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (490431578112 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (98297708544 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-687026995200 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (4907335680 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (677212323840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-97192509440 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-482827304960 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (115401031680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (252025241600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-77812793344 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-96399654912 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (34810986496 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (26777681920 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-10740178944 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-5297324032 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2287480832 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (722362368 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-328932864 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-64496640 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (30511872 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (3472896 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1687488 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-97920 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (48416 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1088 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-543 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_37 (n : ℕ) : ℤ :=
    (if 30 = n then (4294967296 : ℤ) else 0) +
    (if 31 = n then (-8589934592 : ℤ) else 0) +
    (if 32 = n then (-28991029248 : ℤ) else 0) +
    (if 33 = n then (66571993088 : ℤ) else 0) +
    (if 34 = n then (83483426816 : ℤ) else 0) +
    (if 35 = n then (-233538846720 : ℤ) else 0) +
    (if 36 = n then (-128446365696 : ℤ) else 0) +
    (if 37 = n then (490431578112 : ℤ) else 0) +
    (if 38 = n then (98297708544 : ℤ) else 0) +
    (if 39 = n then (-687026995200 : ℤ) else 0) +
    (if 40 = n then (4907335680 : ℤ) else 0) +
    (if 41 = n then (677212323840 : ℤ) else 0) +
    (if 42 = n then (-97192509440 : ℤ) else 0) +
    (if 43 = n then (-482827304960 : ℤ) else 0) +
    (if 44 = n then (115401031680 : ℤ) else 0) +
    (if 45 = n then (252025241600 : ℤ) else 0) +
    (if 46 = n then (-77812793344 : ℤ) else 0) +
    (if 47 = n then (-96399654912 : ℤ) else 0) +
    (if 48 = n then (34810986496 : ℤ) else 0) +
    (if 49 = n then (26777681920 : ℤ) else 0) +
    (if 50 = n then (-10740178944 : ℤ) else 0) +
    (if 51 = n then (-5297324032 : ℤ) else 0) +
    (if 52 = n then (2287480832 : ℤ) else 0) +
    (if 53 = n then (722362368 : ℤ) else 0) +
    (if 54 = n then (-328932864 : ℤ) else 0) +
    (if 55 = n then (-64496640 : ℤ) else 0) +
    (if 56 = n then (30511872 : ℤ) else 0) +
    (if 57 = n then (3472896 : ℤ) else 0) +
    (if 58 = n then (-1687488 : ℤ) else 0) +
    (if 59 = n then (-97920 : ℤ) else 0) +
    (if 60 = n then (48416 : ℤ) else 0) +
    (if 61 = n then (1088 : ℤ) else 0) +
    (if 62 = n then (-543 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_37 (n : ℕ) :
    fixedRowDData_37.coeff n = fixedRowDCoeff_37 n := by
  simp only [fixedRowDData_37, fixedRowDCoeff_37, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_37 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_37 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_37, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_37 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_32 (k.val + 2) - 2 * fixedReversedUCoeff_32 (k.val + 1) + fixedReversedUCoeff_32 k.val) = fixedRowDCoeff_37 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_37 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_32 = fixedRowDData_37 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_32, fixed_rowD_typed_coeff_37]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_32, fixed_rowD_typed_coeff_37]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_32, fixed_rowD_typed_coeff_37]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_37 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_32 _ (by omega),
              fixed_reversedU_typed_tail_32 _ (by omega), fixed_reversedU_typed_tail_32 _ hn',
              fixed_rowD_typed_tail_37 _ (by omega)]
            decide

theorem fixed_rowD_typed_37 : rowD 1 37 = fixedRowDData_37 := by
  calc
    rowD 1 37 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_32 :=
      fixedTyped_rowD_of_parameters 1 37 2 63 32 (1)
        fixedChebyshevUData_32 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_32
    _ = fixedRowDData_37 := by
      rw [fixed_reversedU_typed_data_32, fixed_rowD_typed_factor_37]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow38
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 28 (8589934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-64424509440 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (146028888064 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (209916526592 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-565861941248 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-378762428416 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (1323386798080 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (380473704448 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2084334206976 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-125778788352 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (2335891783680 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-208561766400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1918768250880 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (373093826560 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (1172580597760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-318513479680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-535553638400 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (176732700672 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (182088237056 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-68283088896 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-45522059264 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (18667642880 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (8186773504 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-3581713408 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1023346688 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (469502464 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (84341760 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-40062336 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-4217088 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2053056 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (110976 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-54910 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1156 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (577 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_38 (n : ℕ) : ℤ :=
    (if 28 = n then (8589934592 : ℤ) else 0) +
    (if 29 = n then (-17179869184 : ℤ) else 0) +
    (if 30 = n then (-64424509440 : ℤ) else 0) +
    (if 31 = n then (146028888064 : ℤ) else 0) +
    (if 32 = n then (209916526592 : ℤ) else 0) +
    (if 33 = n then (-565861941248 : ℤ) else 0) +
    (if 34 = n then (-378762428416 : ℤ) else 0) +
    (if 35 = n then (1323386798080 : ℤ) else 0) +
    (if 36 = n then (380473704448 : ℤ) else 0) +
    (if 37 = n then (-2084334206976 : ℤ) else 0) +
    (if 38 = n then (-125778788352 : ℤ) else 0) +
    (if 39 = n then (2335891783680 : ℤ) else 0) +
    (if 40 = n then (-208561766400 : ℤ) else 0) +
    (if 41 = n then (-1918768250880 : ℤ) else 0) +
    (if 42 = n then (373093826560 : ℤ) else 0) +
    (if 43 = n then (1172580597760 : ℤ) else 0) +
    (if 44 = n then (-318513479680 : ℤ) else 0) +
    (if 45 = n then (-535553638400 : ℤ) else 0) +
    (if 46 = n then (176732700672 : ℤ) else 0) +
    (if 47 = n then (182088237056 : ℤ) else 0) +
    (if 48 = n then (-68283088896 : ℤ) else 0) +
    (if 49 = n then (-45522059264 : ℤ) else 0) +
    (if 50 = n then (18667642880 : ℤ) else 0) +
    (if 51 = n then (8186773504 : ℤ) else 0) +
    (if 52 = n then (-3581713408 : ℤ) else 0) +
    (if 53 = n then (-1023346688 : ℤ) else 0) +
    (if 54 = n then (469502464 : ℤ) else 0) +
    (if 55 = n then (84341760 : ℤ) else 0) +
    (if 56 = n then (-40062336 : ℤ) else 0) +
    (if 57 = n then (-4217088 : ℤ) else 0) +
    (if 58 = n then (2053056 : ℤ) else 0) +
    (if 59 = n then (110976 : ℤ) else 0) +
    (if 60 = n then (-54910 : ℤ) else 0) +
    (if 61 = n then (-1156 : ℤ) else 0) +
    (if 62 = n then (577 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_38 (n : ℕ) :
    fixedRowPData_38.coeff n = fixedRowPCoeff_38 n := by
  simp only [fixedRowPData_38, fixedRowPCoeff_38, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_38 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_38 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_38, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_38 : ∀ k : Fin 63,
    fixedReversedTCoeff_34 (k.val + 2) - 2 * fixedReversedTCoeff_34 (k.val + 1) + fixedReversedTCoeff_34 k.val = fixedRowPCoeff_38 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_38 :
    (1 - X) ^ 2 * fixedReversedTData_34 = fixedRowPData_38 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_34, fixed_rowP_typed_coeff_38]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_34, fixed_rowP_typed_coeff_38]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_34, fixed_rowP_typed_coeff_38]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_38 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_34 _ (by omega),
              fixed_reversedT_typed_tail_34 _ (by omega), fixed_reversedT_typed_tail_34 _ hn',
              fixed_rowP_typed_tail_38 _ (by omega)]
            decide

theorem fixed_rowP_typed_38 : rowP 1 38 = fixedRowPData_38 := by
  calc
    rowP 1 38 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_34 :=
      fixedTyped_rowP_of_parameters 1 38 2 63 34 fixedChebyshevTData_34
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_34
    _ = fixedRowPData_38 := by
      rw [fixed_reversedT_typed_data_34, fixed_rowP_typed_factor_38]

def fixedRowDData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 29 (8589934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-60129542144 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (180925497344 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-499289948160 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-295279001600 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1089847951360 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (252027338752 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1593902628864 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-27481079808 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1648864788480 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-203654430720 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1241555927040 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (275901317120 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (689753292800 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-203112448000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-283528396800 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (98919907328 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (85688582144 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-33472102400 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-18744377344 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (7927463936 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2889449472 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1294232576 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-300984320 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (140569600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (19845120 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-9550464 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-744192 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (365568 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (13056 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-6494 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-68 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (34 : ℤ)

def fixedRowDCoeff_38 (n : ℕ) : ℤ :=
    (if 29 = n then (8589934592 : ℤ) else 0) +
    (if 30 = n then (-17179869184 : ℤ) else 0) +
    (if 31 = n then (-60129542144 : ℤ) else 0) +
    (if 32 = n then (137438953472 : ℤ) else 0) +
    (if 33 = n then (180925497344 : ℤ) else 0) +
    (if 34 = n then (-499289948160 : ℤ) else 0) +
    (if 35 = n then (-295279001600 : ℤ) else 0) +
    (if 36 = n then (1089847951360 : ℤ) else 0) +
    (if 37 = n then (252027338752 : ℤ) else 0) +
    (if 38 = n then (-1593902628864 : ℤ) else 0) +
    (if 39 = n then (-27481079808 : ℤ) else 0) +
    (if 40 = n then (1648864788480 : ℤ) else 0) +
    (if 41 = n then (-203654430720 : ℤ) else 0) +
    (if 42 = n then (-1241555927040 : ℤ) else 0) +
    (if 43 = n then (275901317120 : ℤ) else 0) +
    (if 44 = n then (689753292800 : ℤ) else 0) +
    (if 45 = n then (-203112448000 : ℤ) else 0) +
    (if 46 = n then (-283528396800 : ℤ) else 0) +
    (if 47 = n then (98919907328 : ℤ) else 0) +
    (if 48 = n then (85688582144 : ℤ) else 0) +
    (if 49 = n then (-33472102400 : ℤ) else 0) +
    (if 50 = n then (-18744377344 : ℤ) else 0) +
    (if 51 = n then (7927463936 : ℤ) else 0) +
    (if 52 = n then (2889449472 : ℤ) else 0) +
    (if 53 = n then (-1294232576 : ℤ) else 0) +
    (if 54 = n then (-300984320 : ℤ) else 0) +
    (if 55 = n then (140569600 : ℤ) else 0) +
    (if 56 = n then (19845120 : ℤ) else 0) +
    (if 57 = n then (-9550464 : ℤ) else 0) +
    (if 58 = n then (-744192 : ℤ) else 0) +
    (if 59 = n then (365568 : ℤ) else 0) +
    (if 60 = n then (13056 : ℤ) else 0) +
    (if 61 = n then (-6494 : ℤ) else 0) +
    (if 62 = n then (-68 : ℤ) else 0) +
    (if 63 = n then (34 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_38 (n : ℕ) :
    fixedRowDData_38.coeff n = fixedRowDCoeff_38 n := by
  simp only [fixedRowDData_38, fixedRowDCoeff_38, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_38 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_38 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_38, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_38 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_33 (k.val + 2) - 2 * fixedReversedUCoeff_33 (k.val + 1) + fixedReversedUCoeff_33 k.val) = fixedRowDCoeff_38 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_38 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_33 = fixedRowDData_38 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_33, fixed_rowD_typed_coeff_38]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_33, fixed_rowD_typed_coeff_38]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_33, fixed_rowD_typed_coeff_38]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_38 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_33 _ (by omega),
              fixed_reversedU_typed_tail_33 _ (by omega), fixed_reversedU_typed_tail_33 _ hn',
              fixed_rowD_typed_tail_38 _ (by omega)]
            decide

theorem fixed_rowD_typed_38 : rowD 1 38 = fixedRowDData_38 := by
  calc
    rowD 1 38 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_33 :=
      fixedTyped_rowD_of_parameters 1 38 2 63 33 (1)
        fixedChebyshevUData_33 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_33
    _ = fixedRowDData_38 := by
      rw [fixed_reversedU_typed_data_33, fixed_rowD_typed_factor_38]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow39
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 27 (17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-133143986176 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (300647710720 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (450971566080 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-1202590842880 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-854966927360 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (2912524697600 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (927780044800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-4768084787200 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-405287206912 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (5578659201024 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-384735117312 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-4809188966400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (852649574400 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (3103889817600 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-797527244800 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-1508835328000 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (478765056000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (551305216000 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-200675098624 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-149955018752 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (60067209216 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (29820600320 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-12803409920 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-4213780480 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1904304640 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (405171200 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-190182400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-24806400 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (11969088 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (868224 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-426972 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-14280 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (7105 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (70 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-35 : ℤ)

def fixedRowPCoeff_39 (n : ℕ) : ℤ :=
    (if 27 = n then (17179869184 : ℤ) else 0) +
    (if 28 = n then (-34359738368 : ℤ) else 0) +
    (if 29 = n then (-133143986176 : ℤ) else 0) +
    (if 30 = n then (300647710720 : ℤ) else 0) +
    (if 31 = n then (450971566080 : ℤ) else 0) +
    (if 32 = n then (-1202590842880 : ℤ) else 0) +
    (if 33 = n then (-854966927360 : ℤ) else 0) +
    (if 34 = n then (2912524697600 : ℤ) else 0) +
    (if 35 = n then (927780044800 : ℤ) else 0) +
    (if 36 = n then (-4768084787200 : ℤ) else 0) +
    (if 37 = n then (-405287206912 : ℤ) else 0) +
    (if 38 = n then (5578659201024 : ℤ) else 0) +
    (if 39 = n then (-384735117312 : ℤ) else 0) +
    (if 40 = n then (-4809188966400 : ℤ) else 0) +
    (if 41 = n then (852649574400 : ℤ) else 0) +
    (if 42 = n then (3103889817600 : ℤ) else 0) +
    (if 43 = n then (-797527244800 : ℤ) else 0) +
    (if 44 = n then (-1508835328000 : ℤ) else 0) +
    (if 45 = n then (478765056000 : ℤ) else 0) +
    (if 46 = n then (551305216000 : ℤ) else 0) +
    (if 47 = n then (-200675098624 : ℤ) else 0) +
    (if 48 = n then (-149955018752 : ℤ) else 0) +
    (if 49 = n then (60067209216 : ℤ) else 0) +
    (if 50 = n then (29820600320 : ℤ) else 0) +
    (if 51 = n then (-12803409920 : ℤ) else 0) +
    (if 52 = n then (-4213780480 : ℤ) else 0) +
    (if 53 = n then (1904304640 : ℤ) else 0) +
    (if 54 = n then (405171200 : ℤ) else 0) +
    (if 55 = n then (-190182400 : ℤ) else 0) +
    (if 56 = n then (-24806400 : ℤ) else 0) +
    (if 57 = n then (11969088 : ℤ) else 0) +
    (if 58 = n then (868224 : ℤ) else 0) +
    (if 59 = n then (-426972 : ℤ) else 0) +
    (if 60 = n then (-14280 : ℤ) else 0) +
    (if 61 = n then (7105 : ℤ) else 0) +
    (if 62 = n then (70 : ℤ) else 0) +
    (if 63 = n then (-35 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_39 (n : ℕ) :
    fixedRowPData_39.coeff n = fixedRowPCoeff_39 n := by
  simp only [fixedRowPData_39, fixedRowPCoeff_39, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_39 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_39 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_39, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_39 : ∀ k : Fin 63,
    fixedReversedTCoeff_35 (k.val + 2) - 2 * fixedReversedTCoeff_35 (k.val + 1) + fixedReversedTCoeff_35 k.val = fixedRowPCoeff_39 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_39 :
    (1 - X) ^ 2 * fixedReversedTData_35 = fixedRowPData_39 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_35, fixed_rowP_typed_coeff_39]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_35, fixed_rowP_typed_coeff_39]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_35, fixed_rowP_typed_coeff_39]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_39 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_35 _ (by omega),
              fixed_reversedT_typed_tail_35 _ (by omega), fixed_reversedT_typed_tail_35 _ hn',
              fixed_rowP_typed_tail_39 _ (by omega)]
            decide

theorem fixed_rowP_typed_39 : rowP 1 39 = fixedRowPData_39 := by
  calc
    rowP 1 39 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_35 :=
      fixedTyped_rowP_of_parameters 1 39 2 63 35 fixedChebyshevTData_35
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_35
    _ = fixedRowPData_39 := by
      rw [fixed_reversedT_typed_data_35, fixed_rowP_typed_factor_39]

def fixedRowDData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 28 (17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-124554051584 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (283467841536 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (390842023936 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-1065151889408 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-674041430016 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2413234749440 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (632501043200 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-3678236835840 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-153259868160 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (3984756572160 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-412216197120 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-3160324177920 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (648995143680 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (1862333890560 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-521625927680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-819082035200 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (275652608000 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (267776819200 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-101755191296 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-64266436608 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (26595106816 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (11076222976 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-4875945984 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1324331008 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (610072064 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (104186880 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-49612800 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-4961280 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2418624 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (124032 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-61404 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1224 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (611 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_39 (n : ℕ) : ℤ :=
    (if 28 = n then (17179869184 : ℤ) else 0) +
    (if 29 = n then (-34359738368 : ℤ) else 0) +
    (if 30 = n then (-124554051584 : ℤ) else 0) +
    (if 31 = n then (283467841536 : ℤ) else 0) +
    (if 32 = n then (390842023936 : ℤ) else 0) +
    (if 33 = n then (-1065151889408 : ℤ) else 0) +
    (if 34 = n then (-674041430016 : ℤ) else 0) +
    (if 35 = n then (2413234749440 : ℤ) else 0) +
    (if 36 = n then (632501043200 : ℤ) else 0) +
    (if 37 = n then (-3678236835840 : ℤ) else 0) +
    (if 38 = n then (-153259868160 : ℤ) else 0) +
    (if 39 = n then (3984756572160 : ℤ) else 0) +
    (if 40 = n then (-412216197120 : ℤ) else 0) +
    (if 41 = n then (-3160324177920 : ℤ) else 0) +
    (if 42 = n then (648995143680 : ℤ) else 0) +
    (if 43 = n then (1862333890560 : ℤ) else 0) +
    (if 44 = n then (-521625927680 : ℤ) else 0) +
    (if 45 = n then (-819082035200 : ℤ) else 0) +
    (if 46 = n then (275652608000 : ℤ) else 0) +
    (if 47 = n then (267776819200 : ℤ) else 0) +
    (if 48 = n then (-101755191296 : ℤ) else 0) +
    (if 49 = n then (-64266436608 : ℤ) else 0) +
    (if 50 = n then (26595106816 : ℤ) else 0) +
    (if 51 = n then (11076222976 : ℤ) else 0) +
    (if 52 = n then (-4875945984 : ℤ) else 0) +
    (if 53 = n then (-1324331008 : ℤ) else 0) +
    (if 54 = n then (610072064 : ℤ) else 0) +
    (if 55 = n then (104186880 : ℤ) else 0) +
    (if 56 = n then (-49612800 : ℤ) else 0) +
    (if 57 = n then (-4961280 : ℤ) else 0) +
    (if 58 = n then (2418624 : ℤ) else 0) +
    (if 59 = n then (124032 : ℤ) else 0) +
    (if 60 = n then (-61404 : ℤ) else 0) +
    (if 61 = n then (-1224 : ℤ) else 0) +
    (if 62 = n then (611 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_39 (n : ℕ) :
    fixedRowDData_39.coeff n = fixedRowDCoeff_39 n := by
  simp only [fixedRowDData_39, fixedRowDCoeff_39, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_39 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_39 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_39, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_39 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_34 (k.val + 2) - 2 * fixedReversedUCoeff_34 (k.val + 1) + fixedReversedUCoeff_34 k.val) = fixedRowDCoeff_39 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_39 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_34 = fixedRowDData_39 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_34, fixed_rowD_typed_coeff_39]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_34, fixed_rowD_typed_coeff_39]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_34, fixed_rowD_typed_coeff_39]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_39 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_34 _ (by omega),
              fixed_reversedU_typed_tail_34 _ (by omega), fixed_reversedU_typed_tail_34 _ hn',
              fixed_rowD_typed_tail_39 _ (by omega)]
            decide

theorem fixed_rowD_typed_39 : rowD 1 39 = fixedRowDData_39 := by
  calc
    rowD 1 39 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_34 :=
      fixedTyped_rowD_of_parameters 1 39 2 63 34 (1)
        fixedChebyshevUData_34 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_34
    _ = fixedRowDData_39 := by
      rw [fixed_reversedU_typed_data_34, fixed_rowD_typed_factor_39]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow40
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 26 (34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (618475290624 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (966367641600 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-2551210573824 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-1919850381312 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (6390911336448 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (2234322518016 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-10859556372480 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1191048118272 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (13241652609024 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-643691446272 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-11954269716480 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1913860915200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (8126547886080 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1968148316160 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-4190251253760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1276043591680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (1638164070400 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-578082897920 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-481998274560 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (188417507328 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (105163259904 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-44274462720 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-16614334464 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (7390322688 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1833689088 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-849867264 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-133954560 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (64000512 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (5953536 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-2907000 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-139536 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (69120 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1296 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-647 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_40 (n : ℕ) : ℤ :=
    (if 26 = n then (34359738368 : ℤ) else 0) +
    (if 27 = n then (-68719476736 : ℤ) else 0) +
    (if 28 = n then (-274877906944 : ℤ) else 0) +
    (if 29 = n then (618475290624 : ℤ) else 0) +
    (if 30 = n then (966367641600 : ℤ) else 0) +
    (if 31 = n then (-2551210573824 : ℤ) else 0) +
    (if 32 = n then (-1919850381312 : ℤ) else 0) +
    (if 33 = n then (6390911336448 : ℤ) else 0) +
    (if 34 = n then (2234322518016 : ℤ) else 0) +
    (if 35 = n then (-10859556372480 : ℤ) else 0) +
    (if 36 = n then (-1191048118272 : ℤ) else 0) +
    (if 37 = n then (13241652609024 : ℤ) else 0) +
    (if 38 = n then (-643691446272 : ℤ) else 0) +
    (if 39 = n then (-11954269716480 : ℤ) else 0) +
    (if 40 = n then (1913860915200 : ℤ) else 0) +
    (if 41 = n then (8126547886080 : ℤ) else 0) +
    (if 42 = n then (-1968148316160 : ℤ) else 0) +
    (if 43 = n then (-4190251253760 : ℤ) else 0) +
    (if 44 = n then (1276043591680 : ℤ) else 0) +
    (if 45 = n then (1638164070400 : ℤ) else 0) +
    (if 46 = n then (-578082897920 : ℤ) else 0) +
    (if 47 = n then (-481998274560 : ℤ) else 0) +
    (if 48 = n then (188417507328 : ℤ) else 0) +
    (if 49 = n then (105163259904 : ℤ) else 0) +
    (if 50 = n then (-44274462720 : ℤ) else 0) +
    (if 51 = n then (-16614334464 : ℤ) else 0) +
    (if 52 = n then (7390322688 : ℤ) else 0) +
    (if 53 = n then (1833689088 : ℤ) else 0) +
    (if 54 = n then (-849867264 : ℤ) else 0) +
    (if 55 = n then (-133954560 : ℤ) else 0) +
    (if 56 = n then (64000512 : ℤ) else 0) +
    (if 57 = n then (5953536 : ℤ) else 0) +
    (if 58 = n then (-2907000 : ℤ) else 0) +
    (if 59 = n then (-139536 : ℤ) else 0) +
    (if 60 = n then (69120 : ℤ) else 0) +
    (if 61 = n then (1296 : ℤ) else 0) +
    (if 62 = n then (-647 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_40 (n : ℕ) :
    fixedRowPData_40.coeff n = fixedRowPCoeff_40 n := by
  simp only [fixedRowPData_40, fixedRowPCoeff_40, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_40 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_40 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_40, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_40 : ∀ k : Fin 63,
    fixedReversedTCoeff_36 (k.val + 2) - 2 * fixedReversedTCoeff_36 (k.val + 1) + fixedReversedTCoeff_36 k.val = fixedRowPCoeff_40 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_40 :
    (1 - X) ^ 2 * fixedReversedTData_36 = fixedRowPData_40 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_36, fixed_rowP_typed_coeff_40]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_36, fixed_rowP_typed_coeff_40]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_36, fixed_rowP_typed_coeff_40]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_40 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_36 _ (by omega),
              fixed_reversedT_typed_tail_36 _ (by omega), fixed_reversedT_typed_tail_36 _ hn',
              fixed_rowP_typed_tail_40 _ (by omega)]
            decide

theorem fixed_rowP_typed_40 : rowP 1 40 = fixedRowPData_40 := by
  calc
    rowP 1 40 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_36 :=
      fixedTyped_rowP_of_parameters 1 40 2 63 36 fixedChebyshevTData_36
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_36
    _ = fixedRowPData_40 := by
      rw [fixed_reversedT_typed_data_36, fixed_rowP_typed_factor_40]

def fixedRowDData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 27 (34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-257698037760 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (584115552256 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (841813590016 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-2267742732288 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-1529008357376 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (5325759447040 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (1560281088000 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-8446321623040 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-558547075072 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (9563415773184 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-796951314432 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-7969513144320 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (1501644718080 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (4966223708160 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-1319153172480 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-2327917363200 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (754417664000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (819082035200 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-302430289920 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-214221455360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (86662316032 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (40896823296 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-17679355904 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-5538111488 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (2514376704 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (509358080 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-239795200 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-29767680 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (14387712 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (992256 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-488376 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-15504 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (7716 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (72 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-36 : ℤ)

def fixedRowDCoeff_40 (n : ℕ) : ℤ :=
    (if 27 = n then (34359738368 : ℤ) else 0) +
    (if 28 = n then (-68719476736 : ℤ) else 0) +
    (if 29 = n then (-257698037760 : ℤ) else 0) +
    (if 30 = n then (584115552256 : ℤ) else 0) +
    (if 31 = n then (841813590016 : ℤ) else 0) +
    (if 32 = n then (-2267742732288 : ℤ) else 0) +
    (if 33 = n then (-1529008357376 : ℤ) else 0) +
    (if 34 = n then (5325759447040 : ℤ) else 0) +
    (if 35 = n then (1560281088000 : ℤ) else 0) +
    (if 36 = n then (-8446321623040 : ℤ) else 0) +
    (if 37 = n then (-558547075072 : ℤ) else 0) +
    (if 38 = n then (9563415773184 : ℤ) else 0) +
    (if 39 = n then (-796951314432 : ℤ) else 0) +
    (if 40 = n then (-7969513144320 : ℤ) else 0) +
    (if 41 = n then (1501644718080 : ℤ) else 0) +
    (if 42 = n then (4966223708160 : ℤ) else 0) +
    (if 43 = n then (-1319153172480 : ℤ) else 0) +
    (if 44 = n then (-2327917363200 : ℤ) else 0) +
    (if 45 = n then (754417664000 : ℤ) else 0) +
    (if 46 = n then (819082035200 : ℤ) else 0) +
    (if 47 = n then (-302430289920 : ℤ) else 0) +
    (if 48 = n then (-214221455360 : ℤ) else 0) +
    (if 49 = n then (86662316032 : ℤ) else 0) +
    (if 50 = n then (40896823296 : ℤ) else 0) +
    (if 51 = n then (-17679355904 : ℤ) else 0) +
    (if 52 = n then (-5538111488 : ℤ) else 0) +
    (if 53 = n then (2514376704 : ℤ) else 0) +
    (if 54 = n then (509358080 : ℤ) else 0) +
    (if 55 = n then (-239795200 : ℤ) else 0) +
    (if 56 = n then (-29767680 : ℤ) else 0) +
    (if 57 = n then (14387712 : ℤ) else 0) +
    (if 58 = n then (992256 : ℤ) else 0) +
    (if 59 = n then (-488376 : ℤ) else 0) +
    (if 60 = n then (-15504 : ℤ) else 0) +
    (if 61 = n then (7716 : ℤ) else 0) +
    (if 62 = n then (72 : ℤ) else 0) +
    (if 63 = n then (-36 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_40 (n : ℕ) :
    fixedRowDData_40.coeff n = fixedRowDCoeff_40 n := by
  simp only [fixedRowDData_40, fixedRowDCoeff_40, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_40 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_40 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_40, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_40 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_35 (k.val + 2) - 2 * fixedReversedUCoeff_35 (k.val + 1) + fixedReversedUCoeff_35 k.val) = fixedRowDCoeff_40 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_40 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_35 = fixedRowDData_40 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_35, fixed_rowD_typed_coeff_40]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_35, fixed_rowD_typed_coeff_40]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_35, fixed_rowD_typed_coeff_40]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_40 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_35 _ (by omega),
              fixed_reversedU_typed_tail_35 _ (by omega), fixed_reversedU_typed_tail_35 _ hn',
              fixed_rowD_typed_tail_40 _ (by omega)]
            decide

theorem fixed_rowD_typed_40 : rowD 1 40 = fixedRowDData_40 := by
  calc
    rowD 1 40 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_35 :=
      fixedTyped_rowD_of_parameters 1 40 2 63 35 (1)
        fixedChebyshevUData_35 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_35
    _ = fixedRowDData_40 := by
      rw [fixed_reversedU_typed_data_35, fixed_rowD_typed_factor_40]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow41
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 25 (68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-566935683072 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (1271310319616 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (2065879269376 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-5403068858368 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-4290672328704 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (13984413515776 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (5323611963392 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-24631637442560 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-3309876281344 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (31251390005248 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-882095685632 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-29487198633984 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (4212456947712 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (21062284738560 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-4788946206720 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-11484392325120 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (3349614428160 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (4785163468800 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-1634930851840 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-1515301765120 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (577510113280 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (360281538560 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-148616134656 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-63049269248 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (27584055296 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (7881158656 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-3604039168 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-673080320 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (318183424 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (36713472 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-17783088 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1147296 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (565212 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (16872 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-8399 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-74 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (37 : ℤ)

def fixedRowPCoeff_41 (n : ℕ) : ℤ :=
    (if 25 = n then (68719476736 : ℤ) else 0) +
    (if 26 = n then (-137438953472 : ℤ) else 0) +
    (if 27 = n then (-566935683072 : ℤ) else 0) +
    (if 28 = n then (1271310319616 : ℤ) else 0) +
    (if 29 = n then (2065879269376 : ℤ) else 0) +
    (if 30 = n then (-5403068858368 : ℤ) else 0) +
    (if 31 = n then (-4290672328704 : ℤ) else 0) +
    (if 32 = n then (13984413515776 : ℤ) else 0) +
    (if 33 = n then (5323611963392 : ℤ) else 0) +
    (if 34 = n then (-24631637442560 : ℤ) else 0) +
    (if 35 = n then (-3309876281344 : ℤ) else 0) +
    (if 36 = n then (31251390005248 : ℤ) else 0) +
    (if 37 = n then (-882095685632 : ℤ) else 0) +
    (if 38 = n then (-29487198633984 : ℤ) else 0) +
    (if 39 = n then (4212456947712 : ℤ) else 0) +
    (if 40 = n then (21062284738560 : ℤ) else 0) +
    (if 41 = n then (-4788946206720 : ℤ) else 0) +
    (if 42 = n then (-11484392325120 : ℤ) else 0) +
    (if 43 = n then (3349614428160 : ℤ) else 0) +
    (if 44 = n then (4785163468800 : ℤ) else 0) +
    (if 45 = n then (-1634930851840 : ℤ) else 0) +
    (if 46 = n then (-1515301765120 : ℤ) else 0) +
    (if 47 = n then (577510113280 : ℤ) else 0) +
    (if 48 = n then (360281538560 : ℤ) else 0) +
    (if 49 = n then (-148616134656 : ℤ) else 0) +
    (if 50 = n then (-63049269248 : ℤ) else 0) +
    (if 51 = n then (27584055296 : ℤ) else 0) +
    (if 52 = n then (7881158656 : ℤ) else 0) +
    (if 53 = n then (-3604039168 : ℤ) else 0) +
    (if 54 = n then (-673080320 : ℤ) else 0) +
    (if 55 = n then (318183424 : ℤ) else 0) +
    (if 56 = n then (36713472 : ℤ) else 0) +
    (if 57 = n then (-17783088 : ℤ) else 0) +
    (if 58 = n then (-1147296 : ℤ) else 0) +
    (if 59 = n then (565212 : ℤ) else 0) +
    (if 60 = n then (16872 : ℤ) else 0) +
    (if 61 = n then (-8399 : ℤ) else 0) +
    (if 62 = n then (-74 : ℤ) else 0) +
    (if 63 = n then (37 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_41 (n : ℕ) :
    fixedRowPData_41.coeff n = fixedRowPCoeff_41 n := by
  simp only [fixedRowPData_41, fixedRowPCoeff_41, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_41 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_41 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_41, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_41 : ∀ k : Fin 63,
    fixedReversedTCoeff_37 (k.val + 2) - 2 * fixedReversedTCoeff_37 (k.val + 1) + fixedReversedTCoeff_37 k.val = fixedRowPCoeff_41 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_41 :
    (1 - X) ^ 2 * fixedReversedTData_37 = fixedRowPData_41 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_37, fixed_rowP_typed_coeff_41]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_37, fixed_rowP_typed_coeff_41]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_37, fixed_rowP_typed_coeff_41]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_41 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_37 _ (by omega),
              fixed_reversedT_typed_tail_37 _ (by omega), fixed_reversedT_typed_tail_37 _ hn',
              fixed_rowP_typed_tail_41 _ (by omega)]
            decide

theorem fixed_rowP_typed_41 : rowP 1 41 = fixedRowPData_41 := by
  calc
    rowP 1 41 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_37 :=
      fixedTyped_rowP_of_parameters 1 41 2 63 37 fixedChebyshevTData_37
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_37
    _ = fixedRowPData_41 := by
      rw [fixed_reversedT_typed_data_37, fixed_rowP_typed_factor_41]

def fixedRowDData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 26 (68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-532575944704 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (1202590842880 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (1808181231616 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-4818953306112 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-3448858738688 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (11716670783488 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (3794603606016 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-19305877995520 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1749595193344 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (22805068382208 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1440642760704 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-19923782860800 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (3415505633280 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (13092771594240 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-3287301488640 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-6518168616960 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (2030461255680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (2457246105600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-880513187840 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-696219729920 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (275079823360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (146060083200 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-61953818624 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-22152445952 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (9904699392 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (2343047168 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1089662464 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-163722240 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (78388224 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (6945792 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-3395376 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-155040 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (76836 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1368 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-683 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_41 (n : ℕ) : ℤ :=
    (if 26 = n then (68719476736 : ℤ) else 0) +
    (if 27 = n then (-137438953472 : ℤ) else 0) +
    (if 28 = n then (-532575944704 : ℤ) else 0) +
    (if 29 = n then (1202590842880 : ℤ) else 0) +
    (if 30 = n then (1808181231616 : ℤ) else 0) +
    (if 31 = n then (-4818953306112 : ℤ) else 0) +
    (if 32 = n then (-3448858738688 : ℤ) else 0) +
    (if 33 = n then (11716670783488 : ℤ) else 0) +
    (if 34 = n then (3794603606016 : ℤ) else 0) +
    (if 35 = n then (-19305877995520 : ℤ) else 0) +
    (if 36 = n then (-1749595193344 : ℤ) else 0) +
    (if 37 = n then (22805068382208 : ℤ) else 0) +
    (if 38 = n then (-1440642760704 : ℤ) else 0) +
    (if 39 = n then (-19923782860800 : ℤ) else 0) +
    (if 40 = n then (3415505633280 : ℤ) else 0) +
    (if 41 = n then (13092771594240 : ℤ) else 0) +
    (if 42 = n then (-3287301488640 : ℤ) else 0) +
    (if 43 = n then (-6518168616960 : ℤ) else 0) +
    (if 44 = n then (2030461255680 : ℤ) else 0) +
    (if 45 = n then (2457246105600 : ℤ) else 0) +
    (if 46 = n then (-880513187840 : ℤ) else 0) +
    (if 47 = n then (-696219729920 : ℤ) else 0) +
    (if 48 = n then (275079823360 : ℤ) else 0) +
    (if 49 = n then (146060083200 : ℤ) else 0) +
    (if 50 = n then (-61953818624 : ℤ) else 0) +
    (if 51 = n then (-22152445952 : ℤ) else 0) +
    (if 52 = n then (9904699392 : ℤ) else 0) +
    (if 53 = n then (2343047168 : ℤ) else 0) +
    (if 54 = n then (-1089662464 : ℤ) else 0) +
    (if 55 = n then (-163722240 : ℤ) else 0) +
    (if 56 = n then (78388224 : ℤ) else 0) +
    (if 57 = n then (6945792 : ℤ) else 0) +
    (if 58 = n then (-3395376 : ℤ) else 0) +
    (if 59 = n then (-155040 : ℤ) else 0) +
    (if 60 = n then (76836 : ℤ) else 0) +
    (if 61 = n then (1368 : ℤ) else 0) +
    (if 62 = n then (-683 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_41 (n : ℕ) :
    fixedRowDData_41.coeff n = fixedRowDCoeff_41 n := by
  simp only [fixedRowDData_41, fixedRowDCoeff_41, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_41 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_41 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_41, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_41 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_36 (k.val + 2) - 2 * fixedReversedUCoeff_36 (k.val + 1) + fixedReversedUCoeff_36 k.val) = fixedRowDCoeff_41 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_41 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_36 = fixedRowDData_41 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_36, fixed_rowD_typed_coeff_41]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_36, fixed_rowD_typed_coeff_41]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_36, fixed_rowD_typed_coeff_41]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_41 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_36 _ (by omega),
              fixed_reversedU_typed_tail_36 _ (by omega), fixed_reversedU_typed_tail_36 _ hn',
              fixed_rowD_typed_tail_41 _ (by omega)]
            decide

theorem fixed_rowD_typed_41 : rowD 1 41 = fixedRowDData_41 := by
  calc
    rowD 1 41 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_36 :=
      fixedTyped_rowD_of_parameters 1 41 2 63 36 (1)
        fixedChebyshevUData_36 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_36
    _ = fixedRowDData_41 := by
      rw [fixed_reversedU_typed_data_36, fixed_rowD_typed_factor_41]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow42
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 24 (137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-1168231104512 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (2611340115968 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (4406636445696 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-11424613007360 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-9547712299008 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (30520037605376 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (12567074308096 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-55654186221568 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-8854075080704 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (73362336382976 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-573143252992 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-72216049876992 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (9068605341696 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (54078839193600 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-11491753328640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-31095332536320 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (8667377172480 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (13760578191360 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-4545905295360 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-4668767600640 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (1733103124480 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1202561351680 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-485649776640 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-231261798400 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (99442573312 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (32376651776 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-14598401024 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-3179849728 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1486234112 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (207381504 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-99566688 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-8248128 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (4037424 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (173280 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-85918 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1444 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (721 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_42 (n : ℕ) : ℤ :=
    (if 24 = n then (137438953472 : ℤ) else 0) +
    (if 25 = n then (-274877906944 : ℤ) else 0) +
    (if 26 = n then (-1168231104512 : ℤ) else 0) +
    (if 27 = n then (2611340115968 : ℤ) else 0) +
    (if 28 = n then (4406636445696 : ℤ) else 0) +
    (if 29 = n then (-11424613007360 : ℤ) else 0) +
    (if 30 = n then (-9547712299008 : ℤ) else 0) +
    (if 31 = n then (30520037605376 : ℤ) else 0) +
    (if 32 = n then (12567074308096 : ℤ) else 0) +
    (if 33 = n then (-55654186221568 : ℤ) else 0) +
    (if 34 = n then (-8854075080704 : ℤ) else 0) +
    (if 35 = n then (73362336382976 : ℤ) else 0) +
    (if 36 = n then (-573143252992 : ℤ) else 0) +
    (if 37 = n then (-72216049876992 : ℤ) else 0) +
    (if 38 = n then (9068605341696 : ℤ) else 0) +
    (if 39 = n then (54078839193600 : ℤ) else 0) +
    (if 40 = n then (-11491753328640 : ℤ) else 0) +
    (if 41 = n then (-31095332536320 : ℤ) else 0) +
    (if 42 = n then (8667377172480 : ℤ) else 0) +
    (if 43 = n then (13760578191360 : ℤ) else 0) +
    (if 44 = n then (-4545905295360 : ℤ) else 0) +
    (if 45 = n then (-4668767600640 : ℤ) else 0) +
    (if 46 = n then (1733103124480 : ℤ) else 0) +
    (if 47 = n then (1202561351680 : ℤ) else 0) +
    (if 48 = n then (-485649776640 : ℤ) else 0) +
    (if 49 = n then (-231261798400 : ℤ) else 0) +
    (if 50 = n then (99442573312 : ℤ) else 0) +
    (if 51 = n then (32376651776 : ℤ) else 0) +
    (if 52 = n then (-14598401024 : ℤ) else 0) +
    (if 53 = n then (-3179849728 : ℤ) else 0) +
    (if 54 = n then (1486234112 : ℤ) else 0) +
    (if 55 = n then (207381504 : ℤ) else 0) +
    (if 56 = n then (-99566688 : ℤ) else 0) +
    (if 57 = n then (-8248128 : ℤ) else 0) +
    (if 58 = n then (4037424 : ℤ) else 0) +
    (if 59 = n then (173280 : ℤ) else 0) +
    (if 60 = n then (-85918 : ℤ) else 0) +
    (if 61 = n then (-1444 : ℤ) else 0) +
    (if 62 = n then (721 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_42 (n : ℕ) :
    fixedRowPData_42.coeff n = fixedRowPCoeff_42 n := by
  simp only [fixedRowPData_42, fixedRowPCoeff_42, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_42 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_42 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_42, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_42 : ∀ k : Fin 63,
    fixedReversedTCoeff_38 (k.val + 2) - 2 * fixedReversedTCoeff_38 (k.val + 1) + fixedReversedTCoeff_38 k.val = fixedRowPCoeff_42 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_42 :
    (1 - X) ^ 2 * fixedReversedTData_38 = fixedRowPData_42 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_38, fixed_rowP_typed_coeff_42]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_38, fixed_rowP_typed_coeff_42]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_38, fixed_rowP_typed_coeff_42]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_42 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_38 _ (by omega),
              fixed_reversedT_typed_tail_38 _ (by omega), fixed_reversedT_typed_tail_38 _ hn',
              fixed_rowP_typed_tail_42 _ (by omega)]
            decide

theorem fixed_rowP_typed_42 : rowP 1 42 = fixedRowPData_42 := by
  calc
    rowP 1 42 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_38 :=
      fixedTyped_rowP_of_parameters 1 42 2 63 38 fixedChebyshevTData_38
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_38
    _ = fixedRowPData_42 := by
      rw [fixed_reversedT_typed_data_38, fixed_rowP_typed_factor_42]

def fixedRowDData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 25 (137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (2473901162496 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (3874060500992 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-10222022164480 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-7739531067392 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (25701084299264 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (9118215569408 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-43937515438080 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-5059471474688 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (54056458387456 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2322738446336 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-49410981494784 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (7627962580992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (34155056332800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-8076247695360 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-18002560942080 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (5380075683840 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (7242409574400 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2515444039680 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-2211521495040 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (852589936640 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (506341621760 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-210569953280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-85201715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (37488754688 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (10224205824 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-4693701632 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-836802560 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (396571648 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (43659264 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-21178464 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1302336 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (642048 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (18240 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-9082 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-76 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (38 : ℤ)

def fixedRowDCoeff_42 (n : ℕ) : ℤ :=
    (if 25 = n then (137438953472 : ℤ) else 0) +
    (if 26 = n then (-274877906944 : ℤ) else 0) +
    (if 27 = n then (-1099511627776 : ℤ) else 0) +
    (if 28 = n then (2473901162496 : ℤ) else 0) +
    (if 29 = n then (3874060500992 : ℤ) else 0) +
    (if 30 = n then (-10222022164480 : ℤ) else 0) +
    (if 31 = n then (-7739531067392 : ℤ) else 0) +
    (if 32 = n then (25701084299264 : ℤ) else 0) +
    (if 33 = n then (9118215569408 : ℤ) else 0) +
    (if 34 = n then (-43937515438080 : ℤ) else 0) +
    (if 35 = n then (-5059471474688 : ℤ) else 0) +
    (if 36 = n then (54056458387456 : ℤ) else 0) +
    (if 37 = n then (-2322738446336 : ℤ) else 0) +
    (if 38 = n then (-49410981494784 : ℤ) else 0) +
    (if 39 = n then (7627962580992 : ℤ) else 0) +
    (if 40 = n then (34155056332800 : ℤ) else 0) +
    (if 41 = n then (-8076247695360 : ℤ) else 0) +
    (if 42 = n then (-18002560942080 : ℤ) else 0) +
    (if 43 = n then (5380075683840 : ℤ) else 0) +
    (if 44 = n then (7242409574400 : ℤ) else 0) +
    (if 45 = n then (-2515444039680 : ℤ) else 0) +
    (if 46 = n then (-2211521495040 : ℤ) else 0) +
    (if 47 = n then (852589936640 : ℤ) else 0) +
    (if 48 = n then (506341621760 : ℤ) else 0) +
    (if 49 = n then (-210569953280 : ℤ) else 0) +
    (if 50 = n then (-85201715200 : ℤ) else 0) +
    (if 51 = n then (37488754688 : ℤ) else 0) +
    (if 52 = n then (10224205824 : ℤ) else 0) +
    (if 53 = n then (-4693701632 : ℤ) else 0) +
    (if 54 = n then (-836802560 : ℤ) else 0) +
    (if 55 = n then (396571648 : ℤ) else 0) +
    (if 56 = n then (43659264 : ℤ) else 0) +
    (if 57 = n then (-21178464 : ℤ) else 0) +
    (if 58 = n then (-1302336 : ℤ) else 0) +
    (if 59 = n then (642048 : ℤ) else 0) +
    (if 60 = n then (18240 : ℤ) else 0) +
    (if 61 = n then (-9082 : ℤ) else 0) +
    (if 62 = n then (-76 : ℤ) else 0) +
    (if 63 = n then (38 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_42 (n : ℕ) :
    fixedRowDData_42.coeff n = fixedRowDCoeff_42 n := by
  simp only [fixedRowDData_42, fixedRowDCoeff_42, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_42 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_42 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_42, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_42 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_37 (k.val + 2) - 2 * fixedReversedUCoeff_37 (k.val + 1) + fixedReversedUCoeff_37 k.val) = fixedRowDCoeff_42 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_42 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_37 = fixedRowDData_42 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_37, fixed_rowD_typed_coeff_42]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_37, fixed_rowD_typed_coeff_42]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_37, fixed_rowD_typed_coeff_42]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_42 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_37 _ (by omega),
              fixed_reversedU_typed_tail_37 _ (by omega), fixed_reversedU_typed_tail_37 _ hn',
              fixed_rowD_typed_tail_42 _ (by omega)]
            decide

theorem fixed_rowD_typed_42 : rowD 1 42 = fixedRowDData_42 := by
  calc
    rowD 1 42 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_37 :=
      fixedTyped_rowD_of_parameters 1 42 2 63 37 (1)
        fixedChebyshevUData_37 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_37
    _ = fixedRowDData_42 := by
      rw [fixed_reversedU_typed_data_37, fixed_rowD_typed_factor_42]

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
-- module Solutions.OAICatalan.Split.IntBaseRows36
namespace OAI

namespace InternalCatalan

theorem splitBaseMod_row_36 (k : Fin 48) :
    (fixedIntegerBaseCanonical (36 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (36 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (36 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_36 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_36 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 36).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 36).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_36, fixed_rowD_typed_36]
    simp only [fixed_rowP_typed_coeff_36, fixed_rowD_typed_coeff_36,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_37 (k : Fin 48) :
    (fixedIntegerBaseCanonical (37 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (37 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (37 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_37 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_37 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 37).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 37).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_37, fixed_rowD_typed_37]
    simp only [fixed_rowP_typed_coeff_37, fixed_rowD_typed_coeff_37,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_38 (k : Fin 48) :
    (fixedIntegerBaseCanonical (38 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (38 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (38 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_38 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_38 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 38).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 38).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_38, fixed_rowD_typed_38]
    simp only [fixed_rowP_typed_coeff_38, fixed_rowD_typed_coeff_38,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_39 (k : Fin 48) :
    (fixedIntegerBaseCanonical (39 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (39 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (39 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_39 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_39 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 39).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 39).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_39, fixed_rowD_typed_39]
    simp only [fixed_rowP_typed_coeff_39, fixed_rowD_typed_coeff_39,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_40 (k : Fin 48) :
    (fixedIntegerBaseCanonical (40 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (40 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (40 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_40 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_40 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 40).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 40).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_40, fixed_rowD_typed_40]
    simp only [fixed_rowP_typed_coeff_40, fixed_rowD_typed_coeff_40,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_41 (k : Fin 48) :
    (fixedIntegerBaseCanonical (41 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (41 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (41 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_41 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_41 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 41).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 41).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_41, fixed_rowD_typed_41]
    simp only [fixed_rowP_typed_coeff_41, fixed_rowD_typed_coeff_41,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_42 (k : Fin 48) :
    (fixedIntegerBaseCanonical (42 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (42 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (42 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_42 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_42 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 42).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 42).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_42, fixed_rowD_typed_42]
    simp only [fixed_rowP_typed_coeff_42, fixed_rowD_typed_coeff_42,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem fixedIntegerBaseCanonical_mod101_rows_36_42 (r : Fin 49) (hr : 36 ≤ r.val ∧ r.val < 43)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  obtain ⟨r, hr'⟩ := r
  obtain ⟨hra, hrb⟩ := hr
  simp only at hra hrb
  interval_cases r
  · exact splitBaseMod_row_36 k
  · exact splitBaseMod_row_37 k
  · exact splitBaseMod_row_38 k
  · exact splitBaseMod_row_39 k
  · exact splitBaseMod_row_40 k
  · exact splitBaseMod_row_41 k
  · exact splitBaseMod_row_42 k

end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (hr : 36 ≤ r.val ∧ r.val < 43)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_36_42
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_36_42 <;> assumption)

end
