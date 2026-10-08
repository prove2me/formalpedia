-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_30_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T20:47:59.822826+00:00
-- url     : https://prove2.me/submissions/3d595224-f64a-4c86-a5ea-706236f2da3c

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
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT24To31
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan











def fixedReversedTData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (338 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-18928 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (416416 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-4759040 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (32361472 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-141213696 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (412778496 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-825556992 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1133117440 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1049624576 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (627048448 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-218103808 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (33554432 : ℤ)

def fixedReversedTCoeff_26 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (338 : ℤ) else 0) +
    (if 58 = n then (-18928 : ℤ) else 0) +
    (if 56 = n then (416416 : ℤ) else 0) +
    (if 54 = n then (-4759040 : ℤ) else 0) +
    (if 52 = n then (32361472 : ℤ) else 0) +
    (if 50 = n then (-141213696 : ℤ) else 0) +
    (if 48 = n then (412778496 : ℤ) else 0) +
    (if 46 = n then (-825556992 : ℤ) else 0) +
    (if 44 = n then (1133117440 : ℤ) else 0) +
    (if 42 = n then (-1049624576 : ℤ) else 0) +
    (if 40 = n then (627048448 : ℤ) else 0) +
    (if 38 = n then (-218103808 : ℤ) else 0) +
    (if 36 = n then (33554432 : ℤ) else 0)

theorem fixed_reversedT_typed_data_26 : reversedRow 63 fixedChebyshevTData_26 = fixedReversedTData_26 := by
  simp only [fixedChebyshevTData_26, fixedReversedTData_26, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (338 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-18928 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (416416 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-4759040 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (32361472 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-141213696 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (412778496 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-825556992 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (1133117440 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-1049624576 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (627048448 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-218103808 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (33554432 : ℤ) 26 (by decide)]

theorem fixed_reversedT_typed_coeff_26 (n : ℕ) :
    fixedReversedTData_26.coeff n = fixedReversedTCoeff_26 n := by
  simp only [fixedReversedTData_26, fixedReversedTCoeff_26, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_26 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_26 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_26, if_neg, add_zero]

def fixedReversedTData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-27 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (3276 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-117936 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (1976832 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-18670080 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (109983744 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-428654592 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1143078912 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2118057984 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (2724986880 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-2387607552 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (1358954496 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-452984832 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (67108864 : ℤ)

def fixedReversedTCoeff_27 (n : ℕ) : ℤ :=
    (if 61 = n then (-27 : ℤ) else 0) +
    (if 59 = n then (3276 : ℤ) else 0) +
    (if 57 = n then (-117936 : ℤ) else 0) +
    (if 55 = n then (1976832 : ℤ) else 0) +
    (if 53 = n then (-18670080 : ℤ) else 0) +
    (if 51 = n then (109983744 : ℤ) else 0) +
    (if 49 = n then (-428654592 : ℤ) else 0) +
    (if 47 = n then (1143078912 : ℤ) else 0) +
    (if 45 = n then (-2118057984 : ℤ) else 0) +
    (if 43 = n then (2724986880 : ℤ) else 0) +
    (if 41 = n then (-2387607552 : ℤ) else 0) +
    (if 39 = n then (1358954496 : ℤ) else 0) +
    (if 37 = n then (-452984832 : ℤ) else 0) +
    (if 35 = n then (67108864 : ℤ) else 0)

theorem fixed_reversedT_typed_data_27 : reversedRow 63 fixedChebyshevTData_27 = fixedReversedTData_27 := by
  simp only [fixedChebyshevTData_27, fixedReversedTData_27, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-27 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (3276 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-117936 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (1976832 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-18670080 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (109983744 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-428654592 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (1143078912 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-2118057984 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (2724986880 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-2387607552 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (1358954496 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-452984832 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (67108864 : ℤ) 27 (by decide)]

theorem fixed_reversedT_typed_coeff_27 (n : ℕ) :
    fixedReversedTData_27.coeff n = fixedReversedTCoeff_27 n := by
  simp only [fixedReversedTData_27, fixedReversedTCoeff_27, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_27 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_27 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_27, if_neg, add_zero]

def fixedReversedTData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-392 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (25480 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-652288 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (8712704 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-69701632 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (361181184 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-1270087680 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (3111714816 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-5369233408 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (6499598336 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-5402263552 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (2936012800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-939524096 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (134217728 : ℤ)

def fixedReversedTCoeff_28 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-392 : ℤ) else 0) +
    (if 58 = n then (25480 : ℤ) else 0) +
    (if 56 = n then (-652288 : ℤ) else 0) +
    (if 54 = n then (8712704 : ℤ) else 0) +
    (if 52 = n then (-69701632 : ℤ) else 0) +
    (if 50 = n then (361181184 : ℤ) else 0) +
    (if 48 = n then (-1270087680 : ℤ) else 0) +
    (if 46 = n then (3111714816 : ℤ) else 0) +
    (if 44 = n then (-5369233408 : ℤ) else 0) +
    (if 42 = n then (6499598336 : ℤ) else 0) +
    (if 40 = n then (-5402263552 : ℤ) else 0) +
    (if 38 = n then (2936012800 : ℤ) else 0) +
    (if 36 = n then (-939524096 : ℤ) else 0) +
    (if 34 = n then (134217728 : ℤ) else 0)

theorem fixed_reversedT_typed_data_28 : reversedRow 63 fixedChebyshevTData_28 = fixedReversedTData_28 := by
  simp only [fixedChebyshevTData_28, fixedReversedTData_28, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-392 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (25480 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-652288 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (8712704 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-69701632 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (361181184 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-1270087680 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (3111714816 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-5369233408 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (6499598336 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-5402263552 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (2936012800 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-939524096 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (134217728 : ℤ) 28 (by decide)]

theorem fixed_reversedT_typed_coeff_28 (n : ℕ) :
    fixedReversedTData_28.coeff n = fixedReversedTCoeff_28 n := by
  simp only [fixedReversedTData_28, fixedReversedTCoeff_28, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_28 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_28 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_28, if_neg, add_zero]

def fixedReversedTData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (29 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-4060 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (168896 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-3281408 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (36095488 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-249387008 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1151016960 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-3683254272 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (8341487616 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-13463453696 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (15386804224 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-12163481600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (6325010432 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-1946157056 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (268435456 : ℤ)

def fixedReversedTCoeff_29 (n : ℕ) : ℤ :=
    (if 61 = n then (29 : ℤ) else 0) +
    (if 59 = n then (-4060 : ℤ) else 0) +
    (if 57 = n then (168896 : ℤ) else 0) +
    (if 55 = n then (-3281408 : ℤ) else 0) +
    (if 53 = n then (36095488 : ℤ) else 0) +
    (if 51 = n then (-249387008 : ℤ) else 0) +
    (if 49 = n then (1151016960 : ℤ) else 0) +
    (if 47 = n then (-3683254272 : ℤ) else 0) +
    (if 45 = n then (8341487616 : ℤ) else 0) +
    (if 43 = n then (-13463453696 : ℤ) else 0) +
    (if 41 = n then (15386804224 : ℤ) else 0) +
    (if 39 = n then (-12163481600 : ℤ) else 0) +
    (if 37 = n then (6325010432 : ℤ) else 0) +
    (if 35 = n then (-1946157056 : ℤ) else 0) +
    (if 33 = n then (268435456 : ℤ) else 0)

theorem fixed_reversedT_typed_data_29 : reversedRow 63 fixedChebyshevTData_29 = fixedReversedTData_29 := by
  simp only [fixedChebyshevTData_29, fixedReversedTData_29, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (29 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-4060 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (168896 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-3281408 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (36095488 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-249387008 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (1151016960 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-3683254272 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (8341487616 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-13463453696 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (15386804224 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-12163481600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (6325010432 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-1946157056 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (268435456 : ℤ) 29 (by decide)]

theorem fixed_reversedT_typed_coeff_29 (n : ℕ) :
    fixedReversedTData_29.coeff n = fixedReversedTCoeff_29 n := by
  simp only [fixedReversedTData_29, fixedReversedTCoeff_29, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_29 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_29 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_29, if_neg, add_zero]

def fixedReversedTData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (450 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-33600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (990080 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-15275520 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (141892608 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-859955200 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (3572121600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-10478223360 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (22052208640 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-33426505728 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (36175872000 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-27262976000 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (13589544960 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-4026531840 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (536870912 : ℤ)

def fixedReversedTCoeff_30 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (450 : ℤ) else 0) +
    (if 58 = n then (-33600 : ℤ) else 0) +
    (if 56 = n then (990080 : ℤ) else 0) +
    (if 54 = n then (-15275520 : ℤ) else 0) +
    (if 52 = n then (141892608 : ℤ) else 0) +
    (if 50 = n then (-859955200 : ℤ) else 0) +
    (if 48 = n then (3572121600 : ℤ) else 0) +
    (if 46 = n then (-10478223360 : ℤ) else 0) +
    (if 44 = n then (22052208640 : ℤ) else 0) +
    (if 42 = n then (-33426505728 : ℤ) else 0) +
    (if 40 = n then (36175872000 : ℤ) else 0) +
    (if 38 = n then (-27262976000 : ℤ) else 0) +
    (if 36 = n then (13589544960 : ℤ) else 0) +
    (if 34 = n then (-4026531840 : ℤ) else 0) +
    (if 32 = n then (536870912 : ℤ) else 0)

theorem fixed_reversedT_typed_data_30 : reversedRow 63 fixedChebyshevTData_30 = fixedReversedTData_30 := by
  simp only [fixedChebyshevTData_30, fixedReversedTData_30, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (450 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-33600 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (990080 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-15275520 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (141892608 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-859955200 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (3572121600 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-10478223360 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (22052208640 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-33426505728 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (36175872000 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-27262976000 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (13589544960 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-4026531840 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (536870912 : ℤ) 30 (by decide)]

theorem fixed_reversedT_typed_coeff_30 (n : ℕ) :
    fixedReversedTData_30.coeff n = fixedReversedTCoeff_30 n := by
  simp only [fixedReversedTData_30, fixedReversedTCoeff_30, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_30 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_30 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_30, if_neg, add_zero]

def fixedReversedTData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-31 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (4960 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-236096 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (5261568 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-66646528 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (533172224 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-2870927360 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (10827497472 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-29297934336 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (57567870976 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-82239815680 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (84515225600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-60850962432 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (29125246976 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-8321499136 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (1073741824 : ℤ)

def fixedReversedTCoeff_31 (n : ℕ) : ℤ :=
    (if 61 = n then (-31 : ℤ) else 0) +
    (if 59 = n then (4960 : ℤ) else 0) +
    (if 57 = n then (-236096 : ℤ) else 0) +
    (if 55 = n then (5261568 : ℤ) else 0) +
    (if 53 = n then (-66646528 : ℤ) else 0) +
    (if 51 = n then (533172224 : ℤ) else 0) +
    (if 49 = n then (-2870927360 : ℤ) else 0) +
    (if 47 = n then (10827497472 : ℤ) else 0) +
    (if 45 = n then (-29297934336 : ℤ) else 0) +
    (if 43 = n then (57567870976 : ℤ) else 0) +
    (if 41 = n then (-82239815680 : ℤ) else 0) +
    (if 39 = n then (84515225600 : ℤ) else 0) +
    (if 37 = n then (-60850962432 : ℤ) else 0) +
    (if 35 = n then (29125246976 : ℤ) else 0) +
    (if 33 = n then (-8321499136 : ℤ) else 0) +
    (if 31 = n then (1073741824 : ℤ) else 0)

theorem fixed_reversedT_typed_data_31 : reversedRow 63 fixedChebyshevTData_31 = fixedReversedTData_31 := by
  simp only [fixedChebyshevTData_31, fixedReversedTData_31, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-31 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (4960 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-236096 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (5261568 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-66646528 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (533172224 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-2870927360 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (10827497472 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-29297934336 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (57567870976 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-82239815680 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (84515225600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-60850962432 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (29125246976 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-8321499136 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (1073741824 : ℤ) 31 (by decide)]

theorem fixed_reversedT_typed_coeff_31 (n : ℕ) :
    fixedReversedTData_31.coeff n = fixedReversedTCoeff_31 n := by
  simp only [fixedReversedTData_31, fixedReversedTCoeff_31, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_31 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_31 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_31, if_neg, add_zero]

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






def fixedReversedUData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (26 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-2912 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (96096 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1464320 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (12446720 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-65175552 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (222265344 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-508035072 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (784465920 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-807403520 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (530579456 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-201326592 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (33554432 : ℤ)

def fixedReversedUCoeff_25 (n : ℕ) : ℤ :=
    (if 61 = n then (26 : ℤ) else 0) +
    (if 59 = n then (-2912 : ℤ) else 0) +
    (if 57 = n then (96096 : ℤ) else 0) +
    (if 55 = n then (-1464320 : ℤ) else 0) +
    (if 53 = n then (12446720 : ℤ) else 0) +
    (if 51 = n then (-65175552 : ℤ) else 0) +
    (if 49 = n then (222265344 : ℤ) else 0) +
    (if 47 = n then (-508035072 : ℤ) else 0) +
    (if 45 = n then (784465920 : ℤ) else 0) +
    (if 43 = n then (-807403520 : ℤ) else 0) +
    (if 41 = n then (530579456 : ℤ) else 0) +
    (if 39 = n then (-201326592 : ℤ) else 0) +
    (if 37 = n then (33554432 : ℤ) else 0)

theorem fixed_reversedU_typed_data_25 : reversedRow 63 fixedChebyshevUData_25 = fixedReversedUData_25 := by
  simp only [fixedChebyshevUData_25, fixedReversedUData_25, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (26 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-2912 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (96096 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-1464320 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (12446720 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-65175552 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (222265344 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-508035072 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (784465920 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-807403520 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (530579456 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-201326592 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (33554432 : ℤ) 25 (by decide)]

theorem fixed_reversedU_typed_coeff_25 (n : ℕ) :
    fixedReversedUData_25.coeff n = fixedReversedUCoeff_25 n := by
  simp only [fixedReversedUData_25, fixedReversedUCoeff_25, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_25 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_25 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_25, if_neg, add_zero]

def fixedReversedUData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (364 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-21840 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (512512 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-6223360 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (44808192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-206389248 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-1333592064 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1917583360 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1857028096 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1157627904 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-419430400 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (67108864 : ℤ)

def fixedReversedUCoeff_26 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (364 : ℤ) else 0) +
    (if 58 = n then (-21840 : ℤ) else 0) +
    (if 56 = n then (512512 : ℤ) else 0) +
    (if 54 = n then (-6223360 : ℤ) else 0) +
    (if 52 = n then (44808192 : ℤ) else 0) +
    (if 50 = n then (-206389248 : ℤ) else 0) +
    (if 48 = n then (635043840 : ℤ) else 0) +
    (if 46 = n then (-1333592064 : ℤ) else 0) +
    (if 44 = n then (1917583360 : ℤ) else 0) +
    (if 42 = n then (-1857028096 : ℤ) else 0) +
    (if 40 = n then (1157627904 : ℤ) else 0) +
    (if 38 = n then (-419430400 : ℤ) else 0) +
    (if 36 = n then (67108864 : ℤ) else 0)

theorem fixed_reversedU_typed_data_26 : reversedRow 63 fixedChebyshevUData_26 = fixedReversedUData_26 := by
  simp only [fixedChebyshevUData_26, fixedReversedUData_26, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (364 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-21840 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (512512 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-6223360 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (44808192 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-206389248 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (635043840 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-1333592064 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (1917583360 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-1857028096 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (1157627904 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-419430400 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (67108864 : ℤ) 26 (by decide)]

theorem fixed_reversedU_typed_coeff_26 (n : ℕ) :
    fixedReversedUData_26.coeff n = fixedReversedUCoeff_26 n := by
  simp only [fixedReversedUData_26, fixedReversedUCoeff_26, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_26 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_26 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_26, if_neg, add_zero]

def fixedReversedUData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-28 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (3640 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-139776 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2489344 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-24893440 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (154791936 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1778122752 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-3451650048 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (4642570240 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-4244635648 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (2516582400 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-872415232 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (134217728 : ℤ)

def fixedReversedUCoeff_27 (n : ℕ) : ℤ :=
    (if 61 = n then (-28 : ℤ) else 0) +
    (if 59 = n then (3640 : ℤ) else 0) +
    (if 57 = n then (-139776 : ℤ) else 0) +
    (if 55 = n then (2489344 : ℤ) else 0) +
    (if 53 = n then (-24893440 : ℤ) else 0) +
    (if 51 = n then (154791936 : ℤ) else 0) +
    (if 49 = n then (-635043840 : ℤ) else 0) +
    (if 47 = n then (1778122752 : ℤ) else 0) +
    (if 45 = n then (-3451650048 : ℤ) else 0) +
    (if 43 = n then (4642570240 : ℤ) else 0) +
    (if 41 = n then (-4244635648 : ℤ) else 0) +
    (if 39 = n then (2516582400 : ℤ) else 0) +
    (if 37 = n then (-872415232 : ℤ) else 0) +
    (if 35 = n then (134217728 : ℤ) else 0)

theorem fixed_reversedU_typed_data_27 : reversedRow 63 fixedChebyshevUData_27 = fixedReversedUData_27 := by
  simp only [fixedChebyshevUData_27, fixedReversedUData_27, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-28 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (3640 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-139776 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (2489344 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-24893440 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (154791936 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-635043840 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (1778122752 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-3451650048 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (4642570240 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-4244635648 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (2516582400 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-872415232 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (134217728 : ℤ) 27 (by decide)]

theorem fixed_reversedU_typed_coeff_27 (n : ℕ) :
    fixedReversedUData_27.coeff n = fixedReversedUCoeff_27 n := by
  simp only [fixedReversedUData_27, fixedReversedUCoeff_27, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_27 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_27 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_27, if_neg, add_zero]

def fixedReversedUData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-420 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (29120 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-792064 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (11202048 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-94595072 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (515973120 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-1905131520 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (4889837568 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-8820883456 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (11142168576 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-9646899200 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (5452595200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1811939328 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (268435456 : ℤ)

def fixedReversedUCoeff_28 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-420 : ℤ) else 0) +
    (if 58 = n then (29120 : ℤ) else 0) +
    (if 56 = n then (-792064 : ℤ) else 0) +
    (if 54 = n then (11202048 : ℤ) else 0) +
    (if 52 = n then (-94595072 : ℤ) else 0) +
    (if 50 = n then (515973120 : ℤ) else 0) +
    (if 48 = n then (-1905131520 : ℤ) else 0) +
    (if 46 = n then (4889837568 : ℤ) else 0) +
    (if 44 = n then (-8820883456 : ℤ) else 0) +
    (if 42 = n then (11142168576 : ℤ) else 0) +
    (if 40 = n then (-9646899200 : ℤ) else 0) +
    (if 38 = n then (5452595200 : ℤ) else 0) +
    (if 36 = n then (-1811939328 : ℤ) else 0) +
    (if 34 = n then (268435456 : ℤ) else 0)

theorem fixed_reversedU_typed_data_28 : reversedRow 63 fixedChebyshevUData_28 = fixedReversedUData_28 := by
  simp only [fixedChebyshevUData_28, fixedReversedUData_28, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-420 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (29120 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-792064 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (11202048 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-94595072 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (515973120 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-1905131520 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (4889837568 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-8820883456 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (11142168576 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-9646899200 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (5452595200 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-1811939328 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (268435456 : ℤ) 28 (by decide)]

theorem fixed_reversedU_typed_coeff_28 (n : ℕ) :
    fixedReversedUData_28.coeff n = fixedReversedUCoeff_28 n := by
  simp only [fixedReversedUData_28, fixedReversedUCoeff_28, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_28 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_28 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_28, if_neg, add_zero]

def fixedReversedUData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (30 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-4480 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (198016 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-4073472 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (47297536 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-343982080 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1666990080 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-5588385792 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (13231325184 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-22284337152 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (26528972800 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-21810380800 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (11777605632 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-3758096384 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (536870912 : ℤ)

def fixedReversedUCoeff_29 (n : ℕ) : ℤ :=
    (if 61 = n then (30 : ℤ) else 0) +
    (if 59 = n then (-4480 : ℤ) else 0) +
    (if 57 = n then (198016 : ℤ) else 0) +
    (if 55 = n then (-4073472 : ℤ) else 0) +
    (if 53 = n then (47297536 : ℤ) else 0) +
    (if 51 = n then (-343982080 : ℤ) else 0) +
    (if 49 = n then (1666990080 : ℤ) else 0) +
    (if 47 = n then (-5588385792 : ℤ) else 0) +
    (if 45 = n then (13231325184 : ℤ) else 0) +
    (if 43 = n then (-22284337152 : ℤ) else 0) +
    (if 41 = n then (26528972800 : ℤ) else 0) +
    (if 39 = n then (-21810380800 : ℤ) else 0) +
    (if 37 = n then (11777605632 : ℤ) else 0) +
    (if 35 = n then (-3758096384 : ℤ) else 0) +
    (if 33 = n then (536870912 : ℤ) else 0)

theorem fixed_reversedU_typed_data_29 : reversedRow 63 fixedChebyshevUData_29 = fixedReversedUData_29 := by
  simp only [fixedChebyshevUData_29, fixedReversedUData_29, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (30 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-4480 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (198016 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-4073472 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (47297536 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-343982080 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (1666990080 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-5588385792 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (13231325184 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-22284337152 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (26528972800 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-21810380800 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (11777605632 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-3758096384 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (536870912 : ℤ) 29 (by decide)]

theorem fixed_reversedU_typed_coeff_29 (n : ℕ) :
    fixedReversedUData_29.coeff n = fixedReversedUCoeff_29 n := by
  simp only [fixedReversedUData_29, fixedReversedUCoeff_29, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_29 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_29 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_29, if_neg, add_zero]

def fixedReversedUData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (480 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-38080 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (1188096 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-19348992 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (189190144 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1203937280 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (5239111680 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-16066609152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (35283533824 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-55710842880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (62704844800 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-49073356800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (25367150592 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-7784628224 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (1073741824 : ℤ)

def fixedReversedUCoeff_30 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (480 : ℤ) else 0) +
    (if 58 = n then (-38080 : ℤ) else 0) +
    (if 56 = n then (1188096 : ℤ) else 0) +
    (if 54 = n then (-19348992 : ℤ) else 0) +
    (if 52 = n then (189190144 : ℤ) else 0) +
    (if 50 = n then (-1203937280 : ℤ) else 0) +
    (if 48 = n then (5239111680 : ℤ) else 0) +
    (if 46 = n then (-16066609152 : ℤ) else 0) +
    (if 44 = n then (35283533824 : ℤ) else 0) +
    (if 42 = n then (-55710842880 : ℤ) else 0) +
    (if 40 = n then (62704844800 : ℤ) else 0) +
    (if 38 = n then (-49073356800 : ℤ) else 0) +
    (if 36 = n then (25367150592 : ℤ) else 0) +
    (if 34 = n then (-7784628224 : ℤ) else 0) +
    (if 32 = n then (1073741824 : ℤ) else 0)

theorem fixed_reversedU_typed_data_30 : reversedRow 63 fixedChebyshevUData_30 = fixedReversedUData_30 := by
  simp only [fixedChebyshevUData_30, fixedReversedUData_30, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (480 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-38080 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (1188096 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-19348992 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (189190144 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-1203937280 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (5239111680 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-16066609152 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (35283533824 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-55710842880 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (62704844800 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-49073356800 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (25367150592 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-7784628224 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (1073741824 : ℤ) 30 (by decide)]

theorem fixed_reversedU_typed_coeff_30 (n : ℕ) :
    fixedReversedUData_30.coeff n = fixedReversedUCoeff_30 n := by
  simp only [fixedReversedUData_30, fixedReversedUCoeff_30, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_30 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_30 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_30, if_neg, add_zero]






end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow30
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 36 (33554432 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-184549376 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (436207616 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (408944640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1254096896 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-422576128 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (2099249152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (83492864 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2266234880 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (307560448 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1651113984 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-412778496 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-825556992 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (271564800 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (282427392 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-108852224 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-64722944 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (27602432 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (9518080 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-4342624 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-832832 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (397488 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (37856 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-18590 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-676 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (337 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_30 (n : ℕ) : ℤ :=
    (if 36 = n then (33554432 : ℤ) else 0) +
    (if 37 = n then (-67108864 : ℤ) else 0) +
    (if 38 = n then (-184549376 : ℤ) else 0) +
    (if 39 = n then (436207616 : ℤ) else 0) +
    (if 40 = n then (408944640 : ℤ) else 0) +
    (if 41 = n then (-1254096896 : ℤ) else 0) +
    (if 42 = n then (-422576128 : ℤ) else 0) +
    (if 43 = n then (2099249152 : ℤ) else 0) +
    (if 44 = n then (83492864 : ℤ) else 0) +
    (if 45 = n then (-2266234880 : ℤ) else 0) +
    (if 46 = n then (307560448 : ℤ) else 0) +
    (if 47 = n then (1651113984 : ℤ) else 0) +
    (if 48 = n then (-412778496 : ℤ) else 0) +
    (if 49 = n then (-825556992 : ℤ) else 0) +
    (if 50 = n then (271564800 : ℤ) else 0) +
    (if 51 = n then (282427392 : ℤ) else 0) +
    (if 52 = n then (-108852224 : ℤ) else 0) +
    (if 53 = n then (-64722944 : ℤ) else 0) +
    (if 54 = n then (27602432 : ℤ) else 0) +
    (if 55 = n then (9518080 : ℤ) else 0) +
    (if 56 = n then (-4342624 : ℤ) else 0) +
    (if 57 = n then (-832832 : ℤ) else 0) +
    (if 58 = n then (397488 : ℤ) else 0) +
    (if 59 = n then (37856 : ℤ) else 0) +
    (if 60 = n then (-18590 : ℤ) else 0) +
    (if 61 = n then (-676 : ℤ) else 0) +
    (if 62 = n then (337 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_30 (n : ℕ) :
    fixedRowPData_30.coeff n = fixedRowPCoeff_30 n := by
  simp only [fixedRowPData_30, fixedRowPCoeff_30, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_30 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_30 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_30, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_30 : ∀ k : Fin 63,
    fixedReversedTCoeff_26 (k.val + 2) - 2 * fixedReversedTCoeff_26 (k.val + 1) + fixedReversedTCoeff_26 k.val = fixedRowPCoeff_30 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_30 :
    (1 - X) ^ 2 * fixedReversedTData_26 = fixedRowPData_30 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_26, fixed_rowP_typed_coeff_30]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_26, fixed_rowP_typed_coeff_30]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_26, fixed_rowP_typed_coeff_30]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_30 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_26 _ (by omega),
              fixed_reversedT_typed_tail_26 _ (by omega), fixed_reversedT_typed_tail_26 _ hn',
              fixed_rowP_typed_tail_30 _ (by omega)]
            decide

theorem fixed_rowP_typed_30 : rowP 1 30 = fixedRowPData_30 := by
  calc
    rowP 1 30 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_26 :=
      fixedTyped_rowP_of_parameters 1 30 2 63 26 fixedChebyshevTData_26
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_26
    _ = fixedRowPData_30 := by
      rw [fixed_reversedT_typed_data_26, fixed_rowP_typed_factor_30]

def fixedRowDData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 37 (33554432 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-167772160 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (402653184 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (329252864 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1061158912 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-276824064 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1614807040 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-22937600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-1568931840 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (276430848 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1016070144 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-285769728 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-444530688 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (157089792 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (130351104 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-52728832 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-24893440 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (10982400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2928640 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1368224 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-192192 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (93184 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (5824 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-2886 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-52 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (26 : ℤ)

def fixedRowDCoeff_30 (n : ℕ) : ℤ :=
    (if 37 = n then (33554432 : ℤ) else 0) +
    (if 38 = n then (-67108864 : ℤ) else 0) +
    (if 39 = n then (-167772160 : ℤ) else 0) +
    (if 40 = n then (402653184 : ℤ) else 0) +
    (if 41 = n then (329252864 : ℤ) else 0) +
    (if 42 = n then (-1061158912 : ℤ) else 0) +
    (if 43 = n then (-276824064 : ℤ) else 0) +
    (if 44 = n then (1614807040 : ℤ) else 0) +
    (if 45 = n then (-22937600 : ℤ) else 0) +
    (if 46 = n then (-1568931840 : ℤ) else 0) +
    (if 47 = n then (276430848 : ℤ) else 0) +
    (if 48 = n then (1016070144 : ℤ) else 0) +
    (if 49 = n then (-285769728 : ℤ) else 0) +
    (if 50 = n then (-444530688 : ℤ) else 0) +
    (if 51 = n then (157089792 : ℤ) else 0) +
    (if 52 = n then (130351104 : ℤ) else 0) +
    (if 53 = n then (-52728832 : ℤ) else 0) +
    (if 54 = n then (-24893440 : ℤ) else 0) +
    (if 55 = n then (10982400 : ℤ) else 0) +
    (if 56 = n then (2928640 : ℤ) else 0) +
    (if 57 = n then (-1368224 : ℤ) else 0) +
    (if 58 = n then (-192192 : ℤ) else 0) +
    (if 59 = n then (93184 : ℤ) else 0) +
    (if 60 = n then (5824 : ℤ) else 0) +
    (if 61 = n then (-2886 : ℤ) else 0) +
    (if 62 = n then (-52 : ℤ) else 0) +
    (if 63 = n then (26 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_30 (n : ℕ) :
    fixedRowDData_30.coeff n = fixedRowDCoeff_30 n := by
  simp only [fixedRowDData_30, fixedRowDCoeff_30, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_30 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_30 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_30, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_30 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_25 (k.val + 2) - 2 * fixedReversedUCoeff_25 (k.val + 1) + fixedReversedUCoeff_25 k.val) = fixedRowDCoeff_30 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_30 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_25 = fixedRowDData_30 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_25, fixed_rowD_typed_coeff_30]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_25, fixed_rowD_typed_coeff_30]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_25, fixed_rowD_typed_coeff_30]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_30 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_25 _ (by omega),
              fixed_reversedU_typed_tail_25 _ (by omega), fixed_reversedU_typed_tail_25 _ hn',
              fixed_rowD_typed_tail_30 _ (by omega)]
            decide

theorem fixed_rowD_typed_30 : rowD 1 30 = fixedRowDData_30 := by
  calc
    rowD 1 30 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_25 :=
      fixedTyped_rowD_of_parameters 1 30 2 63 25 (1)
        fixedChebyshevUData_25 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_25
    _ = fixedRowDData_30 := by
      rw [fixed_reversedU_typed_data_25, fixed_rowD_typed_factor_30]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow31
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 35 (67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-134217728 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-385875968 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (905969664 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (905969664 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-2717908992 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1028653056 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (4775215104 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (337379328 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-5449973760 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (606928896 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (4236115968 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-974979072 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-2286157824 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (714424320 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (857309184 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-318670848 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-219967488 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (91313664 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (37340160 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-16693248 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-3953664 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1858896 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (235872 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-114660 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-6552 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (3249 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (54 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-27 : ℤ)

def fixedRowPCoeff_31 (n : ℕ) : ℤ :=
    (if 35 = n then (67108864 : ℤ) else 0) +
    (if 36 = n then (-134217728 : ℤ) else 0) +
    (if 37 = n then (-385875968 : ℤ) else 0) +
    (if 38 = n then (905969664 : ℤ) else 0) +
    (if 39 = n then (905969664 : ℤ) else 0) +
    (if 40 = n then (-2717908992 : ℤ) else 0) +
    (if 41 = n then (-1028653056 : ℤ) else 0) +
    (if 42 = n then (4775215104 : ℤ) else 0) +
    (if 43 = n then (337379328 : ℤ) else 0) +
    (if 44 = n then (-5449973760 : ℤ) else 0) +
    (if 45 = n then (606928896 : ℤ) else 0) +
    (if 46 = n then (4236115968 : ℤ) else 0) +
    (if 47 = n then (-974979072 : ℤ) else 0) +
    (if 48 = n then (-2286157824 : ℤ) else 0) +
    (if 49 = n then (714424320 : ℤ) else 0) +
    (if 50 = n then (857309184 : ℤ) else 0) +
    (if 51 = n then (-318670848 : ℤ) else 0) +
    (if 52 = n then (-219967488 : ℤ) else 0) +
    (if 53 = n then (91313664 : ℤ) else 0) +
    (if 54 = n then (37340160 : ℤ) else 0) +
    (if 55 = n then (-16693248 : ℤ) else 0) +
    (if 56 = n then (-3953664 : ℤ) else 0) +
    (if 57 = n then (1858896 : ℤ) else 0) +
    (if 58 = n then (235872 : ℤ) else 0) +
    (if 59 = n then (-114660 : ℤ) else 0) +
    (if 60 = n then (-6552 : ℤ) else 0) +
    (if 61 = n then (3249 : ℤ) else 0) +
    (if 62 = n then (54 : ℤ) else 0) +
    (if 63 = n then (-27 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_31 (n : ℕ) :
    fixedRowPData_31.coeff n = fixedRowPCoeff_31 n := by
  simp only [fixedRowPData_31, fixedRowPCoeff_31, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_31 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_31 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_31, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_31 : ∀ k : Fin 63,
    fixedReversedTCoeff_27 (k.val + 2) - 2 * fixedReversedTCoeff_27 (k.val + 1) + fixedReversedTCoeff_27 k.val = fixedRowPCoeff_31 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_31 :
    (1 - X) ^ 2 * fixedReversedTData_27 = fixedRowPData_31 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_27, fixed_rowP_typed_coeff_31]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_27, fixed_rowP_typed_coeff_31]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_27, fixed_rowP_typed_coeff_31]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_31 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_27 _ (by omega),
              fixed_reversedT_typed_tail_27 _ (by omega), fixed_reversedT_typed_tail_27 _ hn',
              fixed_rowP_typed_tail_31 _ (by omega)]
            decide

theorem fixed_rowP_typed_31 : rowP 1 31 = fixedRowPData_31 := by
  calc
    rowP 1 31 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_27 :=
      fixedTyped_rowP_of_parameters 1 31 2 63 27 fixedChebyshevTData_27
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_27
    _ = fixedRowPData_31 := by
      rw [fixed_reversedT_typed_data_27, fixed_rowP_typed_factor_31]

def fixedRowDData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 36 (67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-134217728 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-352321536 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (838860800 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (738197504 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-2315255808 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-699400192 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (3714056192 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (60555264 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-3835166720 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (583991296 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2667184128 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-698548224 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-1270087680 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (428654592 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (412778496 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-161581056 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-89616384 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (38584832 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (12446720 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-5710848 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (490672 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (43680 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-21476 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-728 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (363 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_31 (n : ℕ) : ℤ :=
    (if 36 = n then (67108864 : ℤ) else 0) +
    (if 37 = n then (-134217728 : ℤ) else 0) +
    (if 38 = n then (-352321536 : ℤ) else 0) +
    (if 39 = n then (838860800 : ℤ) else 0) +
    (if 40 = n then (738197504 : ℤ) else 0) +
    (if 41 = n then (-2315255808 : ℤ) else 0) +
    (if 42 = n then (-699400192 : ℤ) else 0) +
    (if 43 = n then (3714056192 : ℤ) else 0) +
    (if 44 = n then (60555264 : ℤ) else 0) +
    (if 45 = n then (-3835166720 : ℤ) else 0) +
    (if 46 = n then (583991296 : ℤ) else 0) +
    (if 47 = n then (2667184128 : ℤ) else 0) +
    (if 48 = n then (-698548224 : ℤ) else 0) +
    (if 49 = n then (-1270087680 : ℤ) else 0) +
    (if 50 = n then (428654592 : ℤ) else 0) +
    (if 51 = n then (412778496 : ℤ) else 0) +
    (if 52 = n then (-161581056 : ℤ) else 0) +
    (if 53 = n then (-89616384 : ℤ) else 0) +
    (if 54 = n then (38584832 : ℤ) else 0) +
    (if 55 = n then (12446720 : ℤ) else 0) +
    (if 56 = n then (-5710848 : ℤ) else 0) +
    (if 57 = n then (-1025024 : ℤ) else 0) +
    (if 58 = n then (490672 : ℤ) else 0) +
    (if 59 = n then (43680 : ℤ) else 0) +
    (if 60 = n then (-21476 : ℤ) else 0) +
    (if 61 = n then (-728 : ℤ) else 0) +
    (if 62 = n then (363 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_31 (n : ℕ) :
    fixedRowDData_31.coeff n = fixedRowDCoeff_31 n := by
  simp only [fixedRowDData_31, fixedRowDCoeff_31, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_31 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_31 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_31, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_31 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_26 (k.val + 2) - 2 * fixedReversedUCoeff_26 (k.val + 1) + fixedReversedUCoeff_26 k.val) = fixedRowDCoeff_31 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_31 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_26 = fixedRowDData_31 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_26, fixed_rowD_typed_coeff_31]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_26, fixed_rowD_typed_coeff_31]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_26, fixed_rowD_typed_coeff_31]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_31 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_26 _ (by omega),
              fixed_reversedU_typed_tail_26 _ (by omega), fixed_reversedU_typed_tail_26 _ hn',
              fixed_rowD_typed_tail_31 _ (by omega)]
            decide

theorem fixed_rowD_typed_31 : rowD 1 31 = fixedRowDData_31 := by
  calc
    rowD 1 31 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_26 :=
      fixedTyped_rowD_of_parameters 1 31 2 63 26 (1)
        fixedChebyshevUData_26 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_26
    _ = fixedRowDData_31 := by
      rw [fixed_reversedU_typed_data_26, fixed_rowD_typed_factor_31]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow32
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 34 (134217728 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-268435456 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-805306368 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (1879048192 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (1996488704 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-5872025600 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-2466250752 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (10804527104 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (1097334784 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-12999196672 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1130364928 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (10738466816 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-2257518592 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-6223429632 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1841627136 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (2540175360 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-908906496 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-722362368 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (291479552 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (139403264 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-60988928 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-17425408 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (8060416 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1304576 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-626808 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-50960 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (25088 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (784 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-391 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_32 (n : ℕ) : ℤ :=
    (if 34 = n then (134217728 : ℤ) else 0) +
    (if 35 = n then (-268435456 : ℤ) else 0) +
    (if 36 = n then (-805306368 : ℤ) else 0) +
    (if 37 = n then (1879048192 : ℤ) else 0) +
    (if 38 = n then (1996488704 : ℤ) else 0) +
    (if 39 = n then (-5872025600 : ℤ) else 0) +
    (if 40 = n then (-2466250752 : ℤ) else 0) +
    (if 41 = n then (10804527104 : ℤ) else 0) +
    (if 42 = n then (1097334784 : ℤ) else 0) +
    (if 43 = n then (-12999196672 : ℤ) else 0) +
    (if 44 = n then (1130364928 : ℤ) else 0) +
    (if 45 = n then (10738466816 : ℤ) else 0) +
    (if 46 = n then (-2257518592 : ℤ) else 0) +
    (if 47 = n then (-6223429632 : ℤ) else 0) +
    (if 48 = n then (1841627136 : ℤ) else 0) +
    (if 49 = n then (2540175360 : ℤ) else 0) +
    (if 50 = n then (-908906496 : ℤ) else 0) +
    (if 51 = n then (-722362368 : ℤ) else 0) +
    (if 52 = n then (291479552 : ℤ) else 0) +
    (if 53 = n then (139403264 : ℤ) else 0) +
    (if 54 = n then (-60988928 : ℤ) else 0) +
    (if 55 = n then (-17425408 : ℤ) else 0) +
    (if 56 = n then (8060416 : ℤ) else 0) +
    (if 57 = n then (1304576 : ℤ) else 0) +
    (if 58 = n then (-626808 : ℤ) else 0) +
    (if 59 = n then (-50960 : ℤ) else 0) +
    (if 60 = n then (25088 : ℤ) else 0) +
    (if 61 = n then (784 : ℤ) else 0) +
    (if 62 = n then (-391 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_32 (n : ℕ) :
    fixedRowPData_32.coeff n = fixedRowPCoeff_32 n := by
  simp only [fixedRowPData_32, fixedRowPCoeff_32, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_32 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_32 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_32, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_32 : ∀ k : Fin 63,
    fixedReversedTCoeff_28 (k.val + 2) - 2 * fixedReversedTCoeff_28 (k.val + 1) + fixedReversedTCoeff_28 k.val = fixedRowPCoeff_32 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_32 :
    (1 - X) ^ 2 * fixedReversedTData_28 = fixedRowPData_32 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_28, fixed_rowP_typed_coeff_32]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_28, fixed_rowP_typed_coeff_32]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_28, fixed_rowP_typed_coeff_32]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_32 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_28 _ (by omega),
              fixed_reversedT_typed_tail_28 _ (by omega), fixed_reversedT_typed_tail_28 _ hn',
              fixed_rowP_typed_tail_32 _ (by omega)]
            decide

theorem fixed_rowP_typed_32 : rowP 1 32 = fixedRowPData_32 := by
  calc
    rowP 1 32 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_28 :=
      fixedTyped_rowP_of_parameters 1 32 2 63 28 fixedChebyshevTData_28
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_28
    _ = fixedRowPData_32 := by
      rw [fixed_reversedT_typed_data_28, fixed_rowP_typed_factor_32]

def fixedRowDData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 35 (134217728 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-268435456 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-738197504 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (1744830464 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (1644167168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-5033164800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1728053248 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (8489271296 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (397934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-9285140480 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (1190920192 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (6903300096 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-1673527296 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-3556245504 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1143078912 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (1270087680 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-480251904 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-309583872 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (129898496 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (49786880 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-22404096 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-4978688 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (2349568 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (279552 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-136136 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-7280 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (3612 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (56 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-28 : ℤ)

def fixedRowDCoeff_32 (n : ℕ) : ℤ :=
    (if 35 = n then (134217728 : ℤ) else 0) +
    (if 36 = n then (-268435456 : ℤ) else 0) +
    (if 37 = n then (-738197504 : ℤ) else 0) +
    (if 38 = n then (1744830464 : ℤ) else 0) +
    (if 39 = n then (1644167168 : ℤ) else 0) +
    (if 40 = n then (-5033164800 : ℤ) else 0) +
    (if 41 = n then (-1728053248 : ℤ) else 0) +
    (if 42 = n then (8489271296 : ℤ) else 0) +
    (if 43 = n then (397934592 : ℤ) else 0) +
    (if 44 = n then (-9285140480 : ℤ) else 0) +
    (if 45 = n then (1190920192 : ℤ) else 0) +
    (if 46 = n then (6903300096 : ℤ) else 0) +
    (if 47 = n then (-1673527296 : ℤ) else 0) +
    (if 48 = n then (-3556245504 : ℤ) else 0) +
    (if 49 = n then (1143078912 : ℤ) else 0) +
    (if 50 = n then (1270087680 : ℤ) else 0) +
    (if 51 = n then (-480251904 : ℤ) else 0) +
    (if 52 = n then (-309583872 : ℤ) else 0) +
    (if 53 = n then (129898496 : ℤ) else 0) +
    (if 54 = n then (49786880 : ℤ) else 0) +
    (if 55 = n then (-22404096 : ℤ) else 0) +
    (if 56 = n then (-4978688 : ℤ) else 0) +
    (if 57 = n then (2349568 : ℤ) else 0) +
    (if 58 = n then (279552 : ℤ) else 0) +
    (if 59 = n then (-136136 : ℤ) else 0) +
    (if 60 = n then (-7280 : ℤ) else 0) +
    (if 61 = n then (3612 : ℤ) else 0) +
    (if 62 = n then (56 : ℤ) else 0) +
    (if 63 = n then (-28 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_32 (n : ℕ) :
    fixedRowDData_32.coeff n = fixedRowDCoeff_32 n := by
  simp only [fixedRowDData_32, fixedRowDCoeff_32, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_32 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_32 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_32, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_32 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_27 (k.val + 2) - 2 * fixedReversedUCoeff_27 (k.val + 1) + fixedReversedUCoeff_27 k.val) = fixedRowDCoeff_32 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_32 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_27 = fixedRowDData_32 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_27, fixed_rowD_typed_coeff_32]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_27, fixed_rowD_typed_coeff_32]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_27, fixed_rowD_typed_coeff_32]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_32 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_27 _ (by omega),
              fixed_reversedU_typed_tail_27 _ (by omega), fixed_reversedU_typed_tail_27 _ hn',
              fixed_rowD_typed_tail_32 _ (by omega)]
            decide

theorem fixed_rowD_typed_32 : rowD 1 32 = fixedRowDData_32 := by
  calc
    rowD 1 32 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_27 :=
      fixedTyped_rowD_of_parameters 1 32 2 63 27 (1)
        fixedChebyshevUData_27 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_27
    _ = fixedRowDData_32 := by
      rw [fixed_reversedU_typed_data_27, fixed_rowD_typed_factor_32]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow33
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 33 (268435456 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-536870912 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-1677721600 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (3892314112 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (4378853376 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-12650020864 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-5838471168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (24326963200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (3223322624 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-30773608448 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (1923350528 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (26926907392 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-5121966080 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-16682975232 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (4658233344 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (7366508544 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-2532237312 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-2302033920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (901629952 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (498774016 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-213291520 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-72190976 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (32814080 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (6562816 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-3112512 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-337792 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (164836 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (8120 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4031 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-58 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (29 : ℤ)

def fixedRowPCoeff_33 (n : ℕ) : ℤ :=
    (if 33 = n then (268435456 : ℤ) else 0) +
    (if 34 = n then (-536870912 : ℤ) else 0) +
    (if 35 = n then (-1677721600 : ℤ) else 0) +
    (if 36 = n then (3892314112 : ℤ) else 0) +
    (if 37 = n then (4378853376 : ℤ) else 0) +
    (if 38 = n then (-12650020864 : ℤ) else 0) +
    (if 39 = n then (-5838471168 : ℤ) else 0) +
    (if 40 = n then (24326963200 : ℤ) else 0) +
    (if 41 = n then (3223322624 : ℤ) else 0) +
    (if 42 = n then (-30773608448 : ℤ) else 0) +
    (if 43 = n then (1923350528 : ℤ) else 0) +
    (if 44 = n then (26926907392 : ℤ) else 0) +
    (if 45 = n then (-5121966080 : ℤ) else 0) +
    (if 46 = n then (-16682975232 : ℤ) else 0) +
    (if 47 = n then (4658233344 : ℤ) else 0) +
    (if 48 = n then (7366508544 : ℤ) else 0) +
    (if 49 = n then (-2532237312 : ℤ) else 0) +
    (if 50 = n then (-2302033920 : ℤ) else 0) +
    (if 51 = n then (901629952 : ℤ) else 0) +
    (if 52 = n then (498774016 : ℤ) else 0) +
    (if 53 = n then (-213291520 : ℤ) else 0) +
    (if 54 = n then (-72190976 : ℤ) else 0) +
    (if 55 = n then (32814080 : ℤ) else 0) +
    (if 56 = n then (6562816 : ℤ) else 0) +
    (if 57 = n then (-3112512 : ℤ) else 0) +
    (if 58 = n then (-337792 : ℤ) else 0) +
    (if 59 = n then (164836 : ℤ) else 0) +
    (if 60 = n then (8120 : ℤ) else 0) +
    (if 61 = n then (-4031 : ℤ) else 0) +
    (if 62 = n then (-58 : ℤ) else 0) +
    (if 63 = n then (29 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_33 (n : ℕ) :
    fixedRowPData_33.coeff n = fixedRowPCoeff_33 n := by
  simp only [fixedRowPData_33, fixedRowPCoeff_33, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_33 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_33 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_33, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_33 : ∀ k : Fin 63,
    fixedReversedTCoeff_29 (k.val + 2) - 2 * fixedReversedTCoeff_29 (k.val + 1) + fixedReversedTCoeff_29 k.val = fixedRowPCoeff_33 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_33 :
    (1 - X) ^ 2 * fixedReversedTData_29 = fixedRowPData_33 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_29, fixed_rowP_typed_coeff_33]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_29, fixed_rowP_typed_coeff_33]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_29, fixed_rowP_typed_coeff_33]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_33 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_29 _ (by omega),
              fixed_reversedT_typed_tail_29 _ (by omega), fixed_reversedT_typed_tail_29 _ hn',
              fixed_rowP_typed_tail_33 _ (by omega)]
            decide

theorem fixed_rowP_typed_33 : rowP 1 33 = fixedRowPData_33 := by
  calc
    rowP 1 33 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_29 :=
      fixedTyped_rowP_of_parameters 1 33 2 63 29 fixedChebyshevTData_29
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_29
    _ = fixedRowPData_33 := by
      rw [fixed_reversedT_typed_data_29, fixed_rowP_typed_factor_33]

def fixedRowDData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 34 (268435456 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-536870912 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1543503872 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (3623878656 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (3640655872 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-10905190400 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-4194304000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (19293798400 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (1495269376 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-22284337152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (2321285120 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (17641766912 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-3931045888 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-9779675136 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (2984706048 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (3810263040 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1389158400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-1031946240 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (421378048 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (189190144 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-83393024 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-22404096 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (10409984 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1584128 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-762944 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-58240 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (28700 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (840 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-419 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_33 (n : ℕ) : ℤ :=
    (if 34 = n then (268435456 : ℤ) else 0) +
    (if 35 = n then (-536870912 : ℤ) else 0) +
    (if 36 = n then (-1543503872 : ℤ) else 0) +
    (if 37 = n then (3623878656 : ℤ) else 0) +
    (if 38 = n then (3640655872 : ℤ) else 0) +
    (if 39 = n then (-10905190400 : ℤ) else 0) +
    (if 40 = n then (-4194304000 : ℤ) else 0) +
    (if 41 = n then (19293798400 : ℤ) else 0) +
    (if 42 = n then (1495269376 : ℤ) else 0) +
    (if 43 = n then (-22284337152 : ℤ) else 0) +
    (if 44 = n then (2321285120 : ℤ) else 0) +
    (if 45 = n then (17641766912 : ℤ) else 0) +
    (if 46 = n then (-3931045888 : ℤ) else 0) +
    (if 47 = n then (-9779675136 : ℤ) else 0) +
    (if 48 = n then (2984706048 : ℤ) else 0) +
    (if 49 = n then (3810263040 : ℤ) else 0) +
    (if 50 = n then (-1389158400 : ℤ) else 0) +
    (if 51 = n then (-1031946240 : ℤ) else 0) +
    (if 52 = n then (421378048 : ℤ) else 0) +
    (if 53 = n then (189190144 : ℤ) else 0) +
    (if 54 = n then (-83393024 : ℤ) else 0) +
    (if 55 = n then (-22404096 : ℤ) else 0) +
    (if 56 = n then (10409984 : ℤ) else 0) +
    (if 57 = n then (1584128 : ℤ) else 0) +
    (if 58 = n then (-762944 : ℤ) else 0) +
    (if 59 = n then (-58240 : ℤ) else 0) +
    (if 60 = n then (28700 : ℤ) else 0) +
    (if 61 = n then (840 : ℤ) else 0) +
    (if 62 = n then (-419 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_33 (n : ℕ) :
    fixedRowDData_33.coeff n = fixedRowDCoeff_33 n := by
  simp only [fixedRowDData_33, fixedRowDCoeff_33, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_33 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_33 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_33, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_33 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_28 (k.val + 2) - 2 * fixedReversedUCoeff_28 (k.val + 1) + fixedReversedUCoeff_28 k.val) = fixedRowDCoeff_33 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_33 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_28 = fixedRowDData_33 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_28, fixed_rowD_typed_coeff_33]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_28, fixed_rowD_typed_coeff_33]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_28, fixed_rowD_typed_coeff_33]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_33 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_28 _ (by omega),
              fixed_reversedU_typed_tail_28 _ (by omega), fixed_reversedU_typed_tail_28 _ hn',
              fixed_rowD_typed_tail_33 _ (by omega)]
            decide

theorem fixed_rowD_typed_33 : rowD 1 33 = fixedRowDData_33 := by
  calc
    rowD 1 33 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_28 :=
      fixedTyped_rowD_of_parameters 1 33 2 63 28 (1)
        fixedChebyshevUData_28 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_28
    _ = fixedRowDData_33 := by
      rw [fixed_reversedU_typed_data_28, fixed_rowD_typed_factor_33]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow34
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 32 (536870912 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-1073741824 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-3489660928 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (8053063680 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (9563013120 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-27179089920 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-13673431040 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (54525952000 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (8912896000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-72351744000 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (2749366272 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (66853011456 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-11374297088 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-44104417280 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (11573985280 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (20956446720 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-6906101760 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-7144243200 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (2712166400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (1719910400 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-718062592 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-283785216 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (126617088 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (30551040 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-14285440 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1980160 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (956480 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (67200 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-33150 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-900 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (449 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_34 (n : ℕ) : ℤ :=
    (if 32 = n then (536870912 : ℤ) else 0) +
    (if 33 = n then (-1073741824 : ℤ) else 0) +
    (if 34 = n then (-3489660928 : ℤ) else 0) +
    (if 35 = n then (8053063680 : ℤ) else 0) +
    (if 36 = n then (9563013120 : ℤ) else 0) +
    (if 37 = n then (-27179089920 : ℤ) else 0) +
    (if 38 = n then (-13673431040 : ℤ) else 0) +
    (if 39 = n then (54525952000 : ℤ) else 0) +
    (if 40 = n then (8912896000 : ℤ) else 0) +
    (if 41 = n then (-72351744000 : ℤ) else 0) +
    (if 42 = n then (2749366272 : ℤ) else 0) +
    (if 43 = n then (66853011456 : ℤ) else 0) +
    (if 44 = n then (-11374297088 : ℤ) else 0) +
    (if 45 = n then (-44104417280 : ℤ) else 0) +
    (if 46 = n then (11573985280 : ℤ) else 0) +
    (if 47 = n then (20956446720 : ℤ) else 0) +
    (if 48 = n then (-6906101760 : ℤ) else 0) +
    (if 49 = n then (-7144243200 : ℤ) else 0) +
    (if 50 = n then (2712166400 : ℤ) else 0) +
    (if 51 = n then (1719910400 : ℤ) else 0) +
    (if 52 = n then (-718062592 : ℤ) else 0) +
    (if 53 = n then (-283785216 : ℤ) else 0) +
    (if 54 = n then (126617088 : ℤ) else 0) +
    (if 55 = n then (30551040 : ℤ) else 0) +
    (if 56 = n then (-14285440 : ℤ) else 0) +
    (if 57 = n then (-1980160 : ℤ) else 0) +
    (if 58 = n then (956480 : ℤ) else 0) +
    (if 59 = n then (67200 : ℤ) else 0) +
    (if 60 = n then (-33150 : ℤ) else 0) +
    (if 61 = n then (-900 : ℤ) else 0) +
    (if 62 = n then (449 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_34 (n : ℕ) :
    fixedRowPData_34.coeff n = fixedRowPCoeff_34 n := by
  simp only [fixedRowPData_34, fixedRowPCoeff_34, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_34 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_34 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_34, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_34 : ∀ k : Fin 63,
    fixedReversedTCoeff_30 (k.val + 2) - 2 * fixedReversedTCoeff_30 (k.val + 1) + fixedReversedTCoeff_30 k.val = fixedRowPCoeff_34 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_34 :
    (1 - X) ^ 2 * fixedReversedTData_30 = fixedRowPData_34 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_30, fixed_rowP_typed_coeff_34]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_30, fixed_rowP_typed_coeff_34]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_30, fixed_rowP_typed_coeff_34]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_34 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_30 _ (by omega),
              fixed_reversedT_typed_tail_30 _ (by omega), fixed_reversedT_typed_tail_30 _ hn',
              fixed_rowP_typed_tail_34 _ (by omega)]
            decide

theorem fixed_rowP_typed_34 : rowP 1 34 = fixedRowPData_34 := by
  calc
    rowP 1 34 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_30 :=
      fixedTyped_rowP_of_parameters 1 34 2 63 30 fixedChebyshevTData_30
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_30
    _ = fixedRowPData_34 := by
      rw [fixed_reversedT_typed_data_30, fixed_rowP_typed_factor_34]

def fixedRowDData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 33 (536870912 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1073741824 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-3221225472 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (7516192768 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (8019509248 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-23555211264 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-10032775168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (43620761600 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (4718592000 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-53057945600 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (4244635648 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (44568674304 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-9053011968 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-26462650368 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (7642939392 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (11176771584 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-3921395712 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-3333980160 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (1323008000 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (687964160 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-296684544 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-94595072 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (43224064 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (8146944 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-3875456 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-396032 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (193536 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (8960 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4450 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-60 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (30 : ℤ)

def fixedRowDCoeff_34 (n : ℕ) : ℤ :=
    (if 33 = n then (536870912 : ℤ) else 0) +
    (if 34 = n then (-1073741824 : ℤ) else 0) +
    (if 35 = n then (-3221225472 : ℤ) else 0) +
    (if 36 = n then (7516192768 : ℤ) else 0) +
    (if 37 = n then (8019509248 : ℤ) else 0) +
    (if 38 = n then (-23555211264 : ℤ) else 0) +
    (if 39 = n then (-10032775168 : ℤ) else 0) +
    (if 40 = n then (43620761600 : ℤ) else 0) +
    (if 41 = n then (4718592000 : ℤ) else 0) +
    (if 42 = n then (-53057945600 : ℤ) else 0) +
    (if 43 = n then (4244635648 : ℤ) else 0) +
    (if 44 = n then (44568674304 : ℤ) else 0) +
    (if 45 = n then (-9053011968 : ℤ) else 0) +
    (if 46 = n then (-26462650368 : ℤ) else 0) +
    (if 47 = n then (7642939392 : ℤ) else 0) +
    (if 48 = n then (11176771584 : ℤ) else 0) +
    (if 49 = n then (-3921395712 : ℤ) else 0) +
    (if 50 = n then (-3333980160 : ℤ) else 0) +
    (if 51 = n then (1323008000 : ℤ) else 0) +
    (if 52 = n then (687964160 : ℤ) else 0) +
    (if 53 = n then (-296684544 : ℤ) else 0) +
    (if 54 = n then (-94595072 : ℤ) else 0) +
    (if 55 = n then (43224064 : ℤ) else 0) +
    (if 56 = n then (8146944 : ℤ) else 0) +
    (if 57 = n then (-3875456 : ℤ) else 0) +
    (if 58 = n then (-396032 : ℤ) else 0) +
    (if 59 = n then (193536 : ℤ) else 0) +
    (if 60 = n then (8960 : ℤ) else 0) +
    (if 61 = n then (-4450 : ℤ) else 0) +
    (if 62 = n then (-60 : ℤ) else 0) +
    (if 63 = n then (30 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_34 (n : ℕ) :
    fixedRowDData_34.coeff n = fixedRowDCoeff_34 n := by
  simp only [fixedRowDData_34, fixedRowDCoeff_34, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_34 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_34 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_34, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_34 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_29 (k.val + 2) - 2 * fixedReversedUCoeff_29 (k.val + 1) + fixedReversedUCoeff_29 k.val) = fixedRowDCoeff_34 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_34 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_29 = fixedRowDData_34 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_29, fixed_rowD_typed_coeff_34]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_29, fixed_rowD_typed_coeff_34]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_29, fixed_rowD_typed_coeff_34]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_34 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_29 _ (by omega),
              fixed_reversedU_typed_tail_29 _ (by omega), fixed_reversedU_typed_tail_29 _ hn',
              fixed_rowD_typed_tail_34 _ (by omega)]
            decide

theorem fixed_rowD_typed_34 : rowD 1 34 = fixedRowDData_34 := by
  calc
    rowD 1 34 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_29 :=
      fixedTyped_rowD_of_parameters 1 34 2 63 29 (1)
        fixedChebyshevUData_29 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_29
    _ = fixedRowDData_34 := by
      rw [fixed_reversedU_typed_data_29, fixed_rowD_typed_factor_34]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow35
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 31 (1073741824 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-2147483648 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-7247757312 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (16642998272 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (20803747840 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-58250493952 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-31725715456 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (121701924864 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (23664263168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-169030451200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (2275409920 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (164479631360 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-24671944704 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-115135741952 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (28269936640 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (58595868672 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-18470436864 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-21654994944 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (7956570112 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (5741854720 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-2337755136 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-1066344448 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (466525696 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (133293056 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-61384960 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-10523136 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (5025472 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (472192 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-231136 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-9920 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (4929 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (62 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-31 : ℤ)

def fixedRowPCoeff_35 (n : ℕ) : ℤ :=
    (if 31 = n then (1073741824 : ℤ) else 0) +
    (if 32 = n then (-2147483648 : ℤ) else 0) +
    (if 33 = n then (-7247757312 : ℤ) else 0) +
    (if 34 = n then (16642998272 : ℤ) else 0) +
    (if 35 = n then (20803747840 : ℤ) else 0) +
    (if 36 = n then (-58250493952 : ℤ) else 0) +
    (if 37 = n then (-31725715456 : ℤ) else 0) +
    (if 38 = n then (121701924864 : ℤ) else 0) +
    (if 39 = n then (23664263168 : ℤ) else 0) +
    (if 40 = n then (-169030451200 : ℤ) else 0) +
    (if 41 = n then (2275409920 : ℤ) else 0) +
    (if 42 = n then (164479631360 : ℤ) else 0) +
    (if 43 = n then (-24671944704 : ℤ) else 0) +
    (if 44 = n then (-115135741952 : ℤ) else 0) +
    (if 45 = n then (28269936640 : ℤ) else 0) +
    (if 46 = n then (58595868672 : ℤ) else 0) +
    (if 47 = n then (-18470436864 : ℤ) else 0) +
    (if 48 = n then (-21654994944 : ℤ) else 0) +
    (if 49 = n then (7956570112 : ℤ) else 0) +
    (if 50 = n then (5741854720 : ℤ) else 0) +
    (if 51 = n then (-2337755136 : ℤ) else 0) +
    (if 52 = n then (-1066344448 : ℤ) else 0) +
    (if 53 = n then (466525696 : ℤ) else 0) +
    (if 54 = n then (133293056 : ℤ) else 0) +
    (if 55 = n then (-61384960 : ℤ) else 0) +
    (if 56 = n then (-10523136 : ℤ) else 0) +
    (if 57 = n then (5025472 : ℤ) else 0) +
    (if 58 = n then (472192 : ℤ) else 0) +
    (if 59 = n then (-231136 : ℤ) else 0) +
    (if 60 = n then (-9920 : ℤ) else 0) +
    (if 61 = n then (4929 : ℤ) else 0) +
    (if 62 = n then (62 : ℤ) else 0) +
    (if 63 = n then (-31 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_35 (n : ℕ) :
    fixedRowPData_35.coeff n = fixedRowPCoeff_35 n := by
  simp only [fixedRowPData_35, fixedRowPCoeff_35, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_35 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_35 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_35, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_35 : ∀ k : Fin 63,
    fixedReversedTCoeff_31 (k.val + 2) - 2 * fixedReversedTCoeff_31 (k.val + 1) + fixedReversedTCoeff_31 k.val = fixedRowPCoeff_35 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_35 :
    (1 - X) ^ 2 * fixedReversedTData_31 = fixedRowPData_35 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_31, fixed_rowP_typed_coeff_35]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_31, fixed_rowP_typed_coeff_35]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_31, fixed_rowP_typed_coeff_35]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_35 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_31 _ (by omega),
              fixed_reversedT_typed_tail_31 _ (by omega), fixed_reversedT_typed_tail_31 _ hn',
              fixed_rowP_typed_tail_35 _ (by omega)]
            decide

theorem fixed_rowP_typed_35 : rowP 1 35 = fixedRowPData_35 := by
  calc
    rowP 1 35 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_31 :=
      fixedTyped_rowP_of_parameters 1 35 2 63 31 fixedChebyshevTData_31
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_31
    _ = fixedRowPData_35 := by
      rw [fixed_reversedT_typed_data_31, fixed_rowP_typed_factor_35]

def fixedRowDData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 32 (1073741824 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2147483648 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-6710886400 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (15569256448 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (17582522368 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-50734301184 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-23706206208 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (98146713600 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (13631488000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-125409689600 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (6994001920 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (111421685760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-20427309056 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-70567067648 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (19216924672 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-10827497472 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-10478223360 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (4035174400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2407874560 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-1014747136 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-378380288 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (169841152 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (38697984 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-18160896 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-2376192 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1150016 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (76160 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-37600 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-960 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (479 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_35 (n : ℕ) : ℤ :=
    (if 32 = n then (1073741824 : ℤ) else 0) +
    (if 33 = n then (-2147483648 : ℤ) else 0) +
    (if 34 = n then (-6710886400 : ℤ) else 0) +
    (if 35 = n then (15569256448 : ℤ) else 0) +
    (if 36 = n then (17582522368 : ℤ) else 0) +
    (if 37 = n then (-50734301184 : ℤ) else 0) +
    (if 38 = n then (-23706206208 : ℤ) else 0) +
    (if 39 = n then (98146713600 : ℤ) else 0) +
    (if 40 = n then (13631488000 : ℤ) else 0) +
    (if 41 = n then (-125409689600 : ℤ) else 0) +
    (if 42 = n then (6994001920 : ℤ) else 0) +
    (if 43 = n then (111421685760 : ℤ) else 0) +
    (if 44 = n then (-20427309056 : ℤ) else 0) +
    (if 45 = n then (-70567067648 : ℤ) else 0) +
    (if 46 = n then (19216924672 : ℤ) else 0) +
    (if 47 = n then (32133218304 : ℤ) else 0) +
    (if 48 = n then (-10827497472 : ℤ) else 0) +
    (if 49 = n then (-10478223360 : ℤ) else 0) +
    (if 50 = n then (4035174400 : ℤ) else 0) +
    (if 51 = n then (2407874560 : ℤ) else 0) +
    (if 52 = n then (-1014747136 : ℤ) else 0) +
    (if 53 = n then (-378380288 : ℤ) else 0) +
    (if 54 = n then (169841152 : ℤ) else 0) +
    (if 55 = n then (38697984 : ℤ) else 0) +
    (if 56 = n then (-18160896 : ℤ) else 0) +
    (if 57 = n then (-2376192 : ℤ) else 0) +
    (if 58 = n then (1150016 : ℤ) else 0) +
    (if 59 = n then (76160 : ℤ) else 0) +
    (if 60 = n then (-37600 : ℤ) else 0) +
    (if 61 = n then (-960 : ℤ) else 0) +
    (if 62 = n then (479 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_35 (n : ℕ) :
    fixedRowDData_35.coeff n = fixedRowDCoeff_35 n := by
  simp only [fixedRowDData_35, fixedRowDCoeff_35, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_35 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_35 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_35, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_35 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_30 (k.val + 2) - 2 * fixedReversedUCoeff_30 (k.val + 1) + fixedReversedUCoeff_30 k.val) = fixedRowDCoeff_35 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_35 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_30 = fixedRowDData_35 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_30, fixed_rowD_typed_coeff_35]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_30, fixed_rowD_typed_coeff_35]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_30, fixed_rowD_typed_coeff_35]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_35 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_30 _ (by omega),
              fixed_reversedU_typed_tail_30 _ (by omega), fixed_reversedU_typed_tail_30 _ hn',
              fixed_rowD_typed_tail_35 _ (by omega)]
            decide

theorem fixed_rowD_typed_35 : rowD 1 35 = fixedRowDData_35 := by
  calc
    rowD 1 35 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_30 :=
      fixedTyped_rowD_of_parameters 1 35 2 63 30 (1)
        fixedChebyshevUData_30 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_30
    _ = fixedRowDData_35 := by
      rw [fixed_reversedU_typed_data_30, fixed_rowD_typed_factor_35]

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
-- module Solutions.OAICatalan.Split.IntBaseRows30
namespace OAI

namespace InternalCatalan

theorem splitBaseMod_row_30 (k : Fin 48) :
    (fixedIntegerBaseCanonical (30 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (30 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (30 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_30 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_30 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 30).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 30).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_30, fixed_rowD_typed_30]
    simp only [fixed_rowP_typed_coeff_30, fixed_rowD_typed_coeff_30,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_31 (k : Fin 48) :
    (fixedIntegerBaseCanonical (31 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (31 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (31 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_31 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_31 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 31).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 31).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_31, fixed_rowD_typed_31]
    simp only [fixed_rowP_typed_coeff_31, fixed_rowD_typed_coeff_31,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_32 (k : Fin 48) :
    (fixedIntegerBaseCanonical (32 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (32 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (32 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_32 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_32 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 32).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 32).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_32, fixed_rowD_typed_32]
    simp only [fixed_rowP_typed_coeff_32, fixed_rowD_typed_coeff_32,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_33 (k : Fin 48) :
    (fixedIntegerBaseCanonical (33 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (33 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (33 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_33 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_33 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 33).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 33).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_33, fixed_rowD_typed_33]
    simp only [fixed_rowP_typed_coeff_33, fixed_rowD_typed_coeff_33,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_34 (k : Fin 48) :
    (fixedIntegerBaseCanonical (34 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (34 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (34 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_34 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_34 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 34).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 34).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_34, fixed_rowD_typed_34]
    simp only [fixed_rowP_typed_coeff_34, fixed_rowD_typed_coeff_34,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_35 (k : Fin 48) :
    (fixedIntegerBaseCanonical (35 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (35 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (35 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_35 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_35 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 35).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 35).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_35, fixed_rowD_typed_35]
    simp only [fixed_rowP_typed_coeff_35, fixed_rowD_typed_coeff_35,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem fixedIntegerBaseCanonical_mod101_rows_30_35 (r : Fin 49) (hr : 30 ≤ r.val ∧ r.val < 36)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  obtain ⟨r, hr'⟩ := r
  obtain ⟨hra, hrb⟩ := hr
  simp only at hra hrb
  interval_cases r
  · exact splitBaseMod_row_30 k
  · exact splitBaseMod_row_31 k
  · exact splitBaseMod_row_32 k
  · exact splitBaseMod_row_33 k
  · exact splitBaseMod_row_34 k
  · exact splitBaseMod_row_35 k

end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (hr : 30 ≤ r.val ∧ r.val < 36)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_30_35
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_30_35 <;> assumption)

end
