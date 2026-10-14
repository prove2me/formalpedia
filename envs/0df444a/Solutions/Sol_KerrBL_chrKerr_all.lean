-- Prove2me | solution 1 for KerrBL.chrKerr_all
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T10:02:16.686682+00:00
-- url     : https://prove2.me/submissions/2f5ccc08-2184-4d79-b5f7-17dabcaaf605

import Definitions.Def_KerrBL_Kerr_ClosedForms
import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Theorems.Thm_KerrBL_pdgKerr_all
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

theorem chrKerr_000 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 0 0 x = GammaKerrpt M a 0 0 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_000, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_001 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 0 1 x = GammaKerrpt M a 0 0 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_001, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_002 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 0 2 x = GammaKerrpt M a 0 0 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_002, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_003 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 0 3 x = GammaKerrpt M a 0 0 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_003, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_010 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 1 0 x = GammaKerrpt M a 0 1 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_010, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_011 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 1 1 x = GammaKerrpt M a 0 1 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_011, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_012 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 1 2 x = GammaKerrpt M a 0 1 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_012, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_013 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 1 3 x = GammaKerrpt M a 0 1 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_013, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_020 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 2 0 x = GammaKerrpt M a 0 2 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_020, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_021 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 2 1 x = GammaKerrpt M a 0 2 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_021, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_022 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 2 2 x = GammaKerrpt M a 0 2 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_022, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_023 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 2 3 x = GammaKerrpt M a 0 2 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_023, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_030 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 3 0 x = GammaKerrpt M a 0 3 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_030, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_031 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 3 1 x = GammaKerrpt M a 0 3 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_031, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_032 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 3 2 x = GammaKerrpt M a 0 3 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_032, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_033 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 0 3 3 x = GammaKerrpt M a 0 3 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_033, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_100 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 0 0 x = GammaKerrpt M a 1 0 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_100, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_101 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 0 1 x = GammaKerrpt M a 1 0 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_101, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_102 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 0 2 x = GammaKerrpt M a 1 0 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_102, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_103 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 0 3 x = GammaKerrpt M a 1 0 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_103, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_110 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 1 0 x = GammaKerrpt M a 1 1 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_110, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_111 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 1 1 x = GammaKerrpt M a 1 1 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_111, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_112 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 1 2 x = GammaKerrpt M a 1 1 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_112, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_113 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 1 3 x = GammaKerrpt M a 1 1 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_113, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_120 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 2 0 x = GammaKerrpt M a 1 2 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_120, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_121 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 2 1 x = GammaKerrpt M a 1 2 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_121, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_122 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 2 2 x = GammaKerrpt M a 1 2 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_122, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_123 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 2 3 x = GammaKerrpt M a 1 2 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_123, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_130 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 3 0 x = GammaKerrpt M a 1 3 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_130, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_131 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 3 1 x = GammaKerrpt M a 1 3 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_131, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_132 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 3 2 x = GammaKerrpt M a 1 3 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_132, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_133 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 1 3 3 x = GammaKerrpt M a 1 3 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_133, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_200 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 0 0 x = GammaKerrpt M a 2 0 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_200, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_201 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 0 1 x = GammaKerrpt M a 2 0 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_201, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_202 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 0 2 x = GammaKerrpt M a 2 0 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_202, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_203 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 0 3 x = GammaKerrpt M a 2 0 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_203, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_210 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 1 0 x = GammaKerrpt M a 2 1 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_210, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_211 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 1 1 x = GammaKerrpt M a 2 1 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_211, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_212 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 1 2 x = GammaKerrpt M a 2 1 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_212, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_213 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 1 3 x = GammaKerrpt M a 2 1 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_213, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_220 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 2 0 x = GammaKerrpt M a 2 2 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_220, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_221 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 2 1 x = GammaKerrpt M a 2 2 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_221, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_222 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 2 2 x = GammaKerrpt M a 2 2 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_222, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_223 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 2 3 x = GammaKerrpt M a 2 2 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_223, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_230 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 3 0 x = GammaKerrpt M a 2 3 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_230, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_231 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 3 1 x = GammaKerrpt M a 2 3 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_231, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_232 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 3 2 x = GammaKerrpt M a 2 3 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_232, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_233 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 2 3 3 x = GammaKerrpt M a 2 3 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_233, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_300 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 0 0 x = GammaKerrpt M a 3 0 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_300, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_301 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 0 1 x = GammaKerrpt M a 3 0 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_301, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_302 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 0 2 x = GammaKerrpt M a 3 0 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_302, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_303 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 0 3 x = GammaKerrpt M a 3 0 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_303, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_310 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 1 0 x = GammaKerrpt M a 3 1 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_310, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_311 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 1 1 x = GammaKerrpt M a 3 1 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_311, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_312 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 1 2 x = GammaKerrpt M a 3 1 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_312, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_313 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 1 3 x = GammaKerrpt M a 3 1 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_313, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_320 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 2 0 x = GammaKerrpt M a 3 2 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_320, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_321 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 2 1 x = GammaKerrpt M a 3 2 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_321, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_322 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 2 2 x = GammaKerrpt M a 3 2 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_322, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_323 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 2 3 x = GammaKerrpt M a 3 2 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_323, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_330 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 3 0 x = GammaKerrpt M a 3 3 0 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_330, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_331 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 3 1 x = GammaKerrpt M a 3 3 1 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_331, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_332 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 3 2 x = GammaKerrpt M a 3 3 2 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_332, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

theorem chrKerr_333 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    christoffel (gKerr M a) (giKerr M a) 3 3 3 x = GammaKerrpt M a 3 3 3 x := by
  have hd := pdgKerr_all M a x hx
  obtain ⟨hS, hD, hs⟩ := hx
  unfold christoffel GammaKerrpt
  simp only [Fin.sum_univ_four, hd, GammaKerr_333, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, dgKerr_000, dgKerr_001, dgKerr_002, dgKerr_003, dgKerr_010, dgKerr_011, dgKerr_012, dgKerr_013, dgKerr_020, dgKerr_021, dgKerr_022, dgKerr_023, dgKerr_030, dgKerr_031, dgKerr_032, dgKerr_033, dgKerr_100, dgKerr_101, dgKerr_102, dgKerr_103, dgKerr_110, dgKerr_111, dgKerr_112, dgKerr_113, dgKerr_120, dgKerr_121, dgKerr_122, dgKerr_123, dgKerr_130, dgKerr_131, dgKerr_132, dgKerr_133, dgKerr_200, dgKerr_201, dgKerr_202, dgKerr_203, dgKerr_210, dgKerr_211, dgKerr_212, dgKerr_213, dgKerr_220, dgKerr_221, dgKerr_222, dgKerr_223, dgKerr_230, dgKerr_231, dgKerr_232, dgKerr_233, dgKerr_300, dgKerr_301, dgKerr_302, dgKerr_303, dgKerr_310, dgKerr_311, dgKerr_312, dgKerr_313, dgKerr_320, dgKerr_321, dgKerr_322, dgKerr_323, dgKerr_330, dgKerr_331, dgKerr_332, dgKerr_333]
  first | ring1 | (field_simp; ring1) | field_simp

end KerrBL

theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ i j k : Fin 4, christoffel (gKerr M a) (giKerr M a) i j k x = GammaKerrpt M a i j k x := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  exacts [chrKerr_000 M a x hx, chrKerr_001 M a x hx, chrKerr_002 M a x hx, chrKerr_003 M a x hx, chrKerr_010 M a x hx, chrKerr_011 M a x hx, chrKerr_012 M a x hx, chrKerr_013 M a x hx, chrKerr_020 M a x hx, chrKerr_021 M a x hx, chrKerr_022 M a x hx, chrKerr_023 M a x hx, chrKerr_030 M a x hx, chrKerr_031 M a x hx, chrKerr_032 M a x hx, chrKerr_033 M a x hx, chrKerr_100 M a x hx, chrKerr_101 M a x hx, chrKerr_102 M a x hx, chrKerr_103 M a x hx, chrKerr_110 M a x hx, chrKerr_111 M a x hx, chrKerr_112 M a x hx, chrKerr_113 M a x hx, chrKerr_120 M a x hx, chrKerr_121 M a x hx, chrKerr_122 M a x hx, chrKerr_123 M a x hx, chrKerr_130 M a x hx, chrKerr_131 M a x hx, chrKerr_132 M a x hx, chrKerr_133 M a x hx, chrKerr_200 M a x hx, chrKerr_201 M a x hx, chrKerr_202 M a x hx, chrKerr_203 M a x hx, chrKerr_210 M a x hx, chrKerr_211 M a x hx, chrKerr_212 M a x hx, chrKerr_213 M a x hx, chrKerr_220 M a x hx, chrKerr_221 M a x hx, chrKerr_222 M a x hx, chrKerr_223 M a x hx, chrKerr_230 M a x hx, chrKerr_231 M a x hx, chrKerr_232 M a x hx, chrKerr_233 M a x hx, chrKerr_300 M a x hx, chrKerr_301 M a x hx, chrKerr_302 M a x hx, chrKerr_303 M a x hx, chrKerr_310 M a x hx, chrKerr_311 M a x hx, chrKerr_312 M a x hx, chrKerr_313 M a x hx, chrKerr_320 M a x hx, chrKerr_321 M a x hx, chrKerr_322 M a x hx, chrKerr_323 M a x hx, chrKerr_330 M a x hx, chrKerr_331 M a x hx, chrKerr_332 M a x hx, chrKerr_333 M a x hx]
