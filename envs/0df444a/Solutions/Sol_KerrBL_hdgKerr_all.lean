-- Prove2me | solution 1 for KerrBL.hdgKerr_all
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T10:00:06.20032+00:00
-- url     : https://prove2.me/submissions/6ff11cf4-f65f-402e-b7c1-7d4f38aedaed

import Definitions.Def_KerrBL_Kerr_ClosedForms
import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Theorems.Thm_KerrBL_hasDerivAt_Del_r
import Theorems.Thm_KerrBL_hasDerivAt_Sig_r
import Theorems.Thm_KerrBL_hasDerivAt_Sig_th
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Constructions
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open KerrBL Filter Topology

namespace KerrBL

theorem hdgKerr_000 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 0 (Function.update x 0 u)) (dgKerr M a 0 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_00, dgKerr_000, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_001 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 1 (Function.update x 0 u)) (dgKerr M a 0 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_01, dgKerr_001, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_002 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 2 (Function.update x 0 u)) (dgKerr M a 0 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_02, dgKerr_002, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_003 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 3 (Function.update x 0 u)) (dgKerr M a 0 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_03, dgKerr_003, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_010 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 0 (Function.update x 0 u)) (dgKerr M a 0 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_10, dgKerr_010, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_011 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 1 (Function.update x 0 u)) (dgKerr M a 0 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_11, dgKerr_011, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_012 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 2 (Function.update x 0 u)) (dgKerr M a 0 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_12, dgKerr_012, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_013 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 3 (Function.update x 0 u)) (dgKerr M a 0 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_13, dgKerr_013, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_020 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 0 (Function.update x 0 u)) (dgKerr M a 0 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_20, dgKerr_020, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_021 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 1 (Function.update x 0 u)) (dgKerr M a 0 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_21, dgKerr_021, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_022 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 2 (Function.update x 0 u)) (dgKerr M a 0 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_22, dgKerr_022, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_023 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 3 (Function.update x 0 u)) (dgKerr M a 0 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_23, dgKerr_023, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_030 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 0 (Function.update x 0 u)) (dgKerr M a 0 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_30, dgKerr_030, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_031 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 1 (Function.update x 0 u)) (dgKerr M a 0 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_31, dgKerr_031, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_032 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 2 (Function.update x 0 u)) (dgKerr M a 0 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_32, dgKerr_032, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_033 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 3 (Function.update x 0 u)) (dgKerr M a 0 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_33, dgKerr_033, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_100 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 0 (Function.update x 1 u)) (dgKerr M a 1 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_00, dgKerr_100, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_const (x 1) ((-1))).fun_add (((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs]))).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_101 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 1 (Function.update x 1 u)) (dgKerr M a 1 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_01, dgKerr_101, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_102 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 2 (Function.update x 1 u)) (dgKerr M a 1 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_02, dgKerr_102, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_103 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 3 (Function.update x 1 u)) (dgKerr M a 1 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_03, dgKerr_103, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((hasDerivAt_const (x 1) ((((-2))*M*a))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_110 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 0 (Function.update x 1 u)) (dgKerr M a 1 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_10, dgKerr_110, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_111 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 1 (Function.update x 1 u)) (dgKerr M a 1 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_11, dgKerr_111, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_div (hasDerivAt_Del_r M a (x 1)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_112 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 2 (Function.update x 1 u)) (dgKerr M a 1 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_12, dgKerr_112, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_113 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 3 (Function.update x 1 u)) (dgKerr M a 1 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_13, dgKerr_113, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_120 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 0 (Function.update x 1 u)) (dgKerr M a 1 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_20, dgKerr_120, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_121 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 1 (Function.update x 1 u)) (dgKerr M a 1 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_21, dgKerr_121, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_122 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 2 (Function.update x 1 u)) (dgKerr M a 1 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_22, dgKerr_122, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_123 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 3 (Function.update x 1 u)) (dgKerr M a 1 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_23, dgKerr_123, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_130 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 0 (Function.update x 1 u)) (dgKerr M a 1 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_30, dgKerr_130, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((hasDerivAt_const (x 1) ((((-2))*M*a))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_131 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 1 (Function.update x 1 u)) (dgKerr M a 1 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_31, dgKerr_131, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_132 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 2 (Function.update x 1 u)) (dgKerr M a 1 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_32, dgKerr_132, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_133 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 3 (Function.update x 1 u)) (dgKerr M a 1 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_33, dgKerr_133, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))).fun_mul (((hasDerivAt_const (x 1) (a^(2:ℕ))).fun_add ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_add (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])))).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_200 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 0 (Function.update x 2 u)) (dgKerr M a 2 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_00, dgKerr_200, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((hasDerivAt_const (x 2) ((-1))).fun_add ((hasDerivAt_const (x 2) (2*M*(x 1))).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs]))).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_201 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 1 (Function.update x 2 u)) (dgKerr M a 2 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_01, dgKerr_201, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_202 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 2 (Function.update x 2 u)) (dgKerr M a 2 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_02, dgKerr_202, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_203 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 3 (Function.update x 2 u)) (dgKerr M a 2 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_03, dgKerr_203, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((hasDerivAt_const (x 2) ((((-2))*M*a*(x 1)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_210 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 0 (Function.update x 2 u)) (dgKerr M a 2 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_10, dgKerr_210, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_211 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 1 (Function.update x 2 u)) (dgKerr M a 2 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_11, dgKerr_211, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_div (hasDerivAt_const (x 2) (Del M a (x 1))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_212 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 2 (Function.update x 2 u)) (dgKerr M a 2 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_12, dgKerr_212, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_213 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 3 (Function.update x 2 u)) (dgKerr M a 2 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_13, dgKerr_213, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_220 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 0 (Function.update x 2 u)) (dgKerr M a 2 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_20, dgKerr_220, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_221 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 1 (Function.update x 2 u)) (dgKerr M a 2 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_21, dgKerr_221, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_222 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 2 (Function.update x 2 u)) (dgKerr M a 2 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_22, dgKerr_222, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (hasDerivAt_Sig_th a (x 1) (x 2)).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_223 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 3 (Function.update x 2 u)) (dgKerr M a 2 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_23, dgKerr_223, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_230 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 0 (Function.update x 2 u)) (dgKerr M a 2 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_30, dgKerr_230, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((hasDerivAt_const (x 2) ((((-2))*M*a*(x 1)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_231 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 1 (Function.update x 2 u)) (dgKerr M a 2 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_31, dgKerr_231, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_232 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 2 (Function.update x 2 u)) (dgKerr M a 2 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_32, dgKerr_232, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_233 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 3 (Function.update x 2 u)) (dgKerr M a 2 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_33, dgKerr_233, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((Real.hasDerivAt_sin (x 2)).fun_pow 2).fun_mul (((hasDerivAt_const (x 2) (a^(2:ℕ))).fun_add (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_add (((hasDerivAt_const (x 2) ((2*M*(x 1)*a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])))).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdgKerr_300 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 0 (Function.update x 3 u)) (dgKerr M a 3 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_00, dgKerr_300, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_301 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 1 (Function.update x 3 u)) (dgKerr M a 3 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_01, dgKerr_301, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_302 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 2 (Function.update x 3 u)) (dgKerr M a 3 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_02, dgKerr_302, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_303 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 0 3 (Function.update x 3 u)) (dgKerr M a 3 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_03, dgKerr_303, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_310 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 0 (Function.update x 3 u)) (dgKerr M a 3 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_10, dgKerr_310, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_311 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 1 (Function.update x 3 u)) (dgKerr M a 3 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_11, dgKerr_311, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_312 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 2 (Function.update x 3 u)) (dgKerr M a 3 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_12, dgKerr_312, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_313 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 1 3 (Function.update x 3 u)) (dgKerr M a 3 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_13, dgKerr_313, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_320 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 0 (Function.update x 3 u)) (dgKerr M a 3 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_20, dgKerr_320, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_321 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 1 (Function.update x 3 u)) (dgKerr M a 3 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_21, dgKerr_321, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_322 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 2 (Function.update x 3 u)) (dgKerr M a 3 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_22, dgKerr_322, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_323 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 2 3 (Function.update x 3 u)) (dgKerr M a 3 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_23, dgKerr_323, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_330 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 0 (Function.update x 3 u)) (dgKerr M a 3 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_30, dgKerr_330, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_331 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 1 (Function.update x 3 u)) (dgKerr M a 3 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_31, dgKerr_331, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_332 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 2 (Function.update x 3 u)) (dgKerr M a 3 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_32, dgKerr_332, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdgKerr_333 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => gKerr M a 3 3 (Function.update x 3 u)) (dgKerr M a 3 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [gKerr_33, dgKerr_333, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

end KerrBL

/- Every coordinate slice of every metric component is differentiable on the regular domain,
with the closed-form derivative. -/
theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ l i j : Fin 4, HasDerivAt (fun u => gKerr M a i j (Function.update x l u)) (dgKerr M a l i j (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x l) := by
  intro l i j
  fin_cases l <;> fin_cases i <;> fin_cases j
  exacts [hdgKerr_000 M a x hx, hdgKerr_001 M a x hx, hdgKerr_002 M a x hx, hdgKerr_003 M a x hx, hdgKerr_010 M a x hx, hdgKerr_011 M a x hx, hdgKerr_012 M a x hx, hdgKerr_013 M a x hx, hdgKerr_020 M a x hx, hdgKerr_021 M a x hx, hdgKerr_022 M a x hx, hdgKerr_023 M a x hx, hdgKerr_030 M a x hx, hdgKerr_031 M a x hx, hdgKerr_032 M a x hx, hdgKerr_033 M a x hx, hdgKerr_100 M a x hx, hdgKerr_101 M a x hx, hdgKerr_102 M a x hx, hdgKerr_103 M a x hx, hdgKerr_110 M a x hx, hdgKerr_111 M a x hx, hdgKerr_112 M a x hx, hdgKerr_113 M a x hx, hdgKerr_120 M a x hx, hdgKerr_121 M a x hx, hdgKerr_122 M a x hx, hdgKerr_123 M a x hx, hdgKerr_130 M a x hx, hdgKerr_131 M a x hx, hdgKerr_132 M a x hx, hdgKerr_133 M a x hx, hdgKerr_200 M a x hx, hdgKerr_201 M a x hx, hdgKerr_202 M a x hx, hdgKerr_203 M a x hx, hdgKerr_210 M a x hx, hdgKerr_211 M a x hx, hdgKerr_212 M a x hx, hdgKerr_213 M a x hx, hdgKerr_220 M a x hx, hdgKerr_221 M a x hx, hdgKerr_222 M a x hx, hdgKerr_223 M a x hx, hdgKerr_230 M a x hx, hdgKerr_231 M a x hx, hdgKerr_232 M a x hx, hdgKerr_233 M a x hx, hdgKerr_300 M a x hx, hdgKerr_301 M a x hx, hdgKerr_302 M a x hx, hdgKerr_303 M a x hx, hdgKerr_310 M a x hx, hdgKerr_311 M a x hx, hdgKerr_312 M a x hx, hdgKerr_313 M a x hx, hdgKerr_320 M a x hx, hdgKerr_321 M a x hx, hdgKerr_322 M a x hx, hdgKerr_323 M a x hx, hdgKerr_330 M a x hx, hdgKerr_331 M a x hx, hdgKerr_332 M a x hx, hdgKerr_333 M a x hx]
