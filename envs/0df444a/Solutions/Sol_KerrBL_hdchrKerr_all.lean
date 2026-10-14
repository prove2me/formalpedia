-- Prove2me | solution 1 for KerrBL.hdchrKerr_all
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T10:04:36.042347+00:00
-- url     : https://prove2.me/submissions/4337055c-bdde-4e2d-b167-60ed8420a0f9

import Definitions.Def_KerrBL_Kerr_ClosedForms
import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Theorems.Thm_KerrBL_chrKerr_all
import Theorems.Thm_KerrBL_hasDerivAt_Del_r
import Theorems.Thm_KerrBL_hasDerivAt_Sig_r
import Theorems.Thm_KerrBL_hasDerivAt_Sig_th
import Theorems.Thm_KerrBL_reg_eventually_Kerr
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

/-- The coordinate slice `u ↦ update x i u` tends to `x` as `u → x i`. -/
theorem tendsto_update (x : Pt) (i : Fin 4) :
    Tendsto (fun u : ℝ => Function.update x i u) (𝓝 (x i)) (𝓝 x) := by
  have h : Continuous (fun u : ℝ => Function.update x i u) :=
    continuous_const.update i continuous_id
  simpa [Function.update_eq_self] using h.tendsto (x i)

theorem hdchrKerr_0000 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 0 (Function.update x 0 u)) (dGammaKerr M a 0 0 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 0 0 (Function.update x 0 u) = GammaKerrpt M a 0 0 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_000, dGammaKerr_0000, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0001 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 1 (Function.update x 0 u)) (dGammaKerr M a 0 0 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 0 1 (Function.update x 0 u) = GammaKerrpt M a 0 0 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_001, dGammaKerr_0001, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0002 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 2 (Function.update x 0 u)) (dGammaKerr M a 0 0 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 0 2 (Function.update x 0 u) = GammaKerrpt M a 0 0 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_002, dGammaKerr_0002, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0003 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 3 (Function.update x 0 u)) (dGammaKerr M a 0 0 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 0 3 (Function.update x 0 u) = GammaKerrpt M a 0 0 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_003, dGammaKerr_0003, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0010 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 0 (Function.update x 0 u)) (dGammaKerr M a 0 0 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 1 0 (Function.update x 0 u) = GammaKerrpt M a 0 1 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_010, dGammaKerr_0010, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0011 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 1 (Function.update x 0 u)) (dGammaKerr M a 0 0 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 1 1 (Function.update x 0 u) = GammaKerrpt M a 0 1 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_011, dGammaKerr_0011, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0012 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 2 (Function.update x 0 u)) (dGammaKerr M a 0 0 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 1 2 (Function.update x 0 u) = GammaKerrpt M a 0 1 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_012, dGammaKerr_0012, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0013 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 3 (Function.update x 0 u)) (dGammaKerr M a 0 0 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 1 3 (Function.update x 0 u) = GammaKerrpt M a 0 1 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_013, dGammaKerr_0013, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0020 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 0 (Function.update x 0 u)) (dGammaKerr M a 0 0 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 2 0 (Function.update x 0 u) = GammaKerrpt M a 0 2 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_020, dGammaKerr_0020, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0021 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 1 (Function.update x 0 u)) (dGammaKerr M a 0 0 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 2 1 (Function.update x 0 u) = GammaKerrpt M a 0 2 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_021, dGammaKerr_0021, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0022 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 2 (Function.update x 0 u)) (dGammaKerr M a 0 0 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 2 2 (Function.update x 0 u) = GammaKerrpt M a 0 2 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_022, dGammaKerr_0022, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0023 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 3 (Function.update x 0 u)) (dGammaKerr M a 0 0 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 2 3 (Function.update x 0 u) = GammaKerrpt M a 0 2 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_023, dGammaKerr_0023, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0030 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 0 (Function.update x 0 u)) (dGammaKerr M a 0 0 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 3 0 (Function.update x 0 u) = GammaKerrpt M a 0 3 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_030, dGammaKerr_0030, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0031 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 1 (Function.update x 0 u)) (dGammaKerr M a 0 0 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 3 1 (Function.update x 0 u) = GammaKerrpt M a 0 3 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_031, dGammaKerr_0031, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0032 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 2 (Function.update x 0 u)) (dGammaKerr M a 0 0 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 3 2 (Function.update x 0 u) = GammaKerrpt M a 0 3 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_032, dGammaKerr_0032, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0033 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 3 (Function.update x 0 u)) (dGammaKerr M a 0 0 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 0 3 3 (Function.update x 0 u) = GammaKerrpt M a 0 3 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_033, dGammaKerr_0033, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0100 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 0 (Function.update x 0 u)) (dGammaKerr M a 0 1 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 0 0 (Function.update x 0 u) = GammaKerrpt M a 1 0 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_100, dGammaKerr_0100, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0101 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 1 (Function.update x 0 u)) (dGammaKerr M a 0 1 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 0 1 (Function.update x 0 u) = GammaKerrpt M a 1 0 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_101, dGammaKerr_0101, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0102 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 2 (Function.update x 0 u)) (dGammaKerr M a 0 1 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 0 2 (Function.update x 0 u) = GammaKerrpt M a 1 0 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_102, dGammaKerr_0102, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0103 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 3 (Function.update x 0 u)) (dGammaKerr M a 0 1 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 0 3 (Function.update x 0 u) = GammaKerrpt M a 1 0 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_103, dGammaKerr_0103, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0110 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 0 (Function.update x 0 u)) (dGammaKerr M a 0 1 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 1 0 (Function.update x 0 u) = GammaKerrpt M a 1 1 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_110, dGammaKerr_0110, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0111 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 1 (Function.update x 0 u)) (dGammaKerr M a 0 1 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 1 1 (Function.update x 0 u) = GammaKerrpt M a 1 1 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_111, dGammaKerr_0111, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0112 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 2 (Function.update x 0 u)) (dGammaKerr M a 0 1 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 1 2 (Function.update x 0 u) = GammaKerrpt M a 1 1 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_112, dGammaKerr_0112, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0113 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 3 (Function.update x 0 u)) (dGammaKerr M a 0 1 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 1 3 (Function.update x 0 u) = GammaKerrpt M a 1 1 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_113, dGammaKerr_0113, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0120 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 0 (Function.update x 0 u)) (dGammaKerr M a 0 1 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 2 0 (Function.update x 0 u) = GammaKerrpt M a 1 2 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_120, dGammaKerr_0120, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0121 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 1 (Function.update x 0 u)) (dGammaKerr M a 0 1 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 2 1 (Function.update x 0 u) = GammaKerrpt M a 1 2 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_121, dGammaKerr_0121, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0122 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 2 (Function.update x 0 u)) (dGammaKerr M a 0 1 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 2 2 (Function.update x 0 u) = GammaKerrpt M a 1 2 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_122, dGammaKerr_0122, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0123 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 3 (Function.update x 0 u)) (dGammaKerr M a 0 1 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 2 3 (Function.update x 0 u) = GammaKerrpt M a 1 2 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_123, dGammaKerr_0123, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0130 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 0 (Function.update x 0 u)) (dGammaKerr M a 0 1 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 3 0 (Function.update x 0 u) = GammaKerrpt M a 1 3 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_130, dGammaKerr_0130, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0131 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 1 (Function.update x 0 u)) (dGammaKerr M a 0 1 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 3 1 (Function.update x 0 u) = GammaKerrpt M a 1 3 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_131, dGammaKerr_0131, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0132 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 2 (Function.update x 0 u)) (dGammaKerr M a 0 1 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 3 2 (Function.update x 0 u) = GammaKerrpt M a 1 3 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_132, dGammaKerr_0132, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0133 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 3 (Function.update x 0 u)) (dGammaKerr M a 0 1 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 1 3 3 (Function.update x 0 u) = GammaKerrpt M a 1 3 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_133, dGammaKerr_0133, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0200 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 0 (Function.update x 0 u)) (dGammaKerr M a 0 2 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 0 0 (Function.update x 0 u) = GammaKerrpt M a 2 0 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_200, dGammaKerr_0200, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0201 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 1 (Function.update x 0 u)) (dGammaKerr M a 0 2 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 0 1 (Function.update x 0 u) = GammaKerrpt M a 2 0 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_201, dGammaKerr_0201, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0202 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 2 (Function.update x 0 u)) (dGammaKerr M a 0 2 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 0 2 (Function.update x 0 u) = GammaKerrpt M a 2 0 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_202, dGammaKerr_0202, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0203 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 3 (Function.update x 0 u)) (dGammaKerr M a 0 2 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 0 3 (Function.update x 0 u) = GammaKerrpt M a 2 0 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_203, dGammaKerr_0203, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0210 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 0 (Function.update x 0 u)) (dGammaKerr M a 0 2 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 1 0 (Function.update x 0 u) = GammaKerrpt M a 2 1 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_210, dGammaKerr_0210, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0211 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 1 (Function.update x 0 u)) (dGammaKerr M a 0 2 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 1 1 (Function.update x 0 u) = GammaKerrpt M a 2 1 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_211, dGammaKerr_0211, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0212 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 2 (Function.update x 0 u)) (dGammaKerr M a 0 2 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 1 2 (Function.update x 0 u) = GammaKerrpt M a 2 1 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_212, dGammaKerr_0212, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0213 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 3 (Function.update x 0 u)) (dGammaKerr M a 0 2 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 1 3 (Function.update x 0 u) = GammaKerrpt M a 2 1 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_213, dGammaKerr_0213, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0220 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 0 (Function.update x 0 u)) (dGammaKerr M a 0 2 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 2 0 (Function.update x 0 u) = GammaKerrpt M a 2 2 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_220, dGammaKerr_0220, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0221 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 1 (Function.update x 0 u)) (dGammaKerr M a 0 2 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 2 1 (Function.update x 0 u) = GammaKerrpt M a 2 2 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_221, dGammaKerr_0221, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0222 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 2 (Function.update x 0 u)) (dGammaKerr M a 0 2 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 2 2 (Function.update x 0 u) = GammaKerrpt M a 2 2 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_222, dGammaKerr_0222, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0223 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 3 (Function.update x 0 u)) (dGammaKerr M a 0 2 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 2 3 (Function.update x 0 u) = GammaKerrpt M a 2 2 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_223, dGammaKerr_0223, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0230 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 0 (Function.update x 0 u)) (dGammaKerr M a 0 2 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 3 0 (Function.update x 0 u) = GammaKerrpt M a 2 3 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_230, dGammaKerr_0230, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0231 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 1 (Function.update x 0 u)) (dGammaKerr M a 0 2 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 3 1 (Function.update x 0 u) = GammaKerrpt M a 2 3 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_231, dGammaKerr_0231, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0232 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 2 (Function.update x 0 u)) (dGammaKerr M a 0 2 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 3 2 (Function.update x 0 u) = GammaKerrpt M a 2 3 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_232, dGammaKerr_0232, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0233 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 3 (Function.update x 0 u)) (dGammaKerr M a 0 2 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 2 3 3 (Function.update x 0 u) = GammaKerrpt M a 2 3 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_233, dGammaKerr_0233, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0300 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 0 (Function.update x 0 u)) (dGammaKerr M a 0 3 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 0 0 (Function.update x 0 u) = GammaKerrpt M a 3 0 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_300, dGammaKerr_0300, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0301 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 1 (Function.update x 0 u)) (dGammaKerr M a 0 3 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 0 1 (Function.update x 0 u) = GammaKerrpt M a 3 0 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_301, dGammaKerr_0301, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0302 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 2 (Function.update x 0 u)) (dGammaKerr M a 0 3 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 0 2 (Function.update x 0 u) = GammaKerrpt M a 3 0 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_302, dGammaKerr_0302, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0303 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 3 (Function.update x 0 u)) (dGammaKerr M a 0 3 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 0 3 (Function.update x 0 u) = GammaKerrpt M a 3 0 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_303, dGammaKerr_0303, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0310 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 0 (Function.update x 0 u)) (dGammaKerr M a 0 3 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 1 0 (Function.update x 0 u) = GammaKerrpt M a 3 1 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_310, dGammaKerr_0310, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0311 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 1 (Function.update x 0 u)) (dGammaKerr M a 0 3 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 1 1 (Function.update x 0 u) = GammaKerrpt M a 3 1 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_311, dGammaKerr_0311, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0312 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 2 (Function.update x 0 u)) (dGammaKerr M a 0 3 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 1 2 (Function.update x 0 u) = GammaKerrpt M a 3 1 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_312, dGammaKerr_0312, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0313 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 3 (Function.update x 0 u)) (dGammaKerr M a 0 3 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 1 3 (Function.update x 0 u) = GammaKerrpt M a 3 1 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_313, dGammaKerr_0313, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0320 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 0 (Function.update x 0 u)) (dGammaKerr M a 0 3 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 2 0 (Function.update x 0 u) = GammaKerrpt M a 3 2 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_320, dGammaKerr_0320, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0321 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 1 (Function.update x 0 u)) (dGammaKerr M a 0 3 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 2 1 (Function.update x 0 u) = GammaKerrpt M a 3 2 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_321, dGammaKerr_0321, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0322 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 2 (Function.update x 0 u)) (dGammaKerr M a 0 3 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 2 2 (Function.update x 0 u) = GammaKerrpt M a 3 2 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_322, dGammaKerr_0322, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0323 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 3 (Function.update x 0 u)) (dGammaKerr M a 0 3 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 2 3 (Function.update x 0 u) = GammaKerrpt M a 3 2 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_323, dGammaKerr_0323, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0330 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 0 (Function.update x 0 u)) (dGammaKerr M a 0 3 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 3 0 (Function.update x 0 u) = GammaKerrpt M a 3 3 0 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_330, dGammaKerr_0330, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0331 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 1 (Function.update x 0 u)) (dGammaKerr M a 0 3 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 3 1 (Function.update x 0 u) = GammaKerrpt M a 3 3 1 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_331, dGammaKerr_0331, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0332 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 2 (Function.update x 0 u)) (dGammaKerr M a 0 3 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 3 2 (Function.update x 0 u) = GammaKerrpt M a 3 3 2 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_332, dGammaKerr_0332, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_0333 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 3 (Function.update x 0 u)) (dGammaKerr M a 0 3 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 0) := by
  have hev : ∀ᶠ u in 𝓝 (x 0), christoffel (gKerr M a) (giKerr M a) 3 3 3 (Function.update x 0 u) = GammaKerrpt M a 3 3 3 (Function.update x 0 u) :=
    (tendsto_update x 0).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_333, dGammaKerr_0333, Function.update_self, Function.update_of_ne (show (1:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 0 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 0 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1000 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 0 (Function.update x 1 u)) (dGammaKerr M a 1 0 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 0 0 (Function.update x 1 u) = GammaKerrpt M a 0 0 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_000, dGammaKerr_1000, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1001 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 1 (Function.update x 1 u)) (dGammaKerr M a 1 0 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 0 1 (Function.update x 1 u) = GammaKerrpt M a 0 0 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_001, dGammaKerr_1001, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((((((hasDerivAt_const (x 1) ((2*M))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 6)).fun_sub (((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ))))).fun_sub (((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 4))).fun_add ((hasDerivAt_const (x 1) ((4*M*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 4))).fun_add ((hasDerivAt_const (x 1) ((2*M*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_sub ((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_sub (((hasDerivAt_const (x 1) ((4*M^(2:ℕ)*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add (((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) (2)).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1002 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 2 (Function.update x 1 u)) (dGammaKerr M a 1 0 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 0 2 (Function.update x 1 u) = GammaKerrpt M a 0 0 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_002, dGammaKerr_1002, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((hasDerivAt_const (x 1) ((((-2))*M*Real.sin (x 2)*Real.cos (x 2)*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 5)).fun_sub ((hasDerivAt_const (x 1) ((4*M*Real.sin (x 2)*Real.cos (x 2)*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(6:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((4*Real.cos (x 2)*M^(2:ℕ)*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((4*Real.sin (x 2)*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1003 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 3 (Function.update x 1 u)) (dGammaKerr M a 1 0 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 0 3 (Function.update x 1 u) = GammaKerrpt M a 0 0 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_003, dGammaKerr_1003, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1010 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 0 (Function.update x 1 u)) (dGammaKerr M a 1 0 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 1 0 (Function.update x 1 u) = GammaKerrpt M a 0 1 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_010, dGammaKerr_1010, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((((((hasDerivAt_const (x 1) ((2*M))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 6)).fun_sub (((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ))))).fun_sub (((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 4))).fun_add ((hasDerivAt_const (x 1) ((4*M*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 4))).fun_add ((hasDerivAt_const (x 1) ((2*M*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_sub ((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_sub (((hasDerivAt_const (x 1) ((4*M^(2:ℕ)*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add (((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) (2)).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1011 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 1 (Function.update x 1 u)) (dGammaKerr M a 1 0 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 1 1 (Function.update x 1 u) = GammaKerrpt M a 0 1 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_011, dGammaKerr_1011, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1012 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 2 (Function.update x 1 u)) (dGammaKerr M a 1 0 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 1 2 (Function.update x 1 u) = GammaKerrpt M a 0 1 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_012, dGammaKerr_1012, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1013 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 3 (Function.update x 1 u)) (dGammaKerr M a 1 0 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 1 3 (Function.update x 1 u) = GammaKerrpt M a 0 1 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_013, dGammaKerr_1013, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((((((((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_sub (((hasDerivAt_const (x 1) ((2*M*a))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 6)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((4*M*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 4)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((2*M*a^(5:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((4*M^(2:ℕ)*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_sub (((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add ((((hasDerivAt_const (x 1) ((M*a))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 4)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub ((((hasDerivAt_const (x 1) ((2*M*a))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub ((((((hasDerivAt_const (x 1) (2)).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1020 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 0 (Function.update x 1 u)) (dGammaKerr M a 1 0 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 2 0 (Function.update x 1 u) = GammaKerrpt M a 0 2 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_020, dGammaKerr_1020, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((hasDerivAt_const (x 1) ((((-2))*M*Real.sin (x 2)*Real.cos (x 2)*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 5)).fun_sub ((hasDerivAt_const (x 1) ((4*M*Real.sin (x 2)*Real.cos (x 2)*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(6:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((4*Real.cos (x 2)*M^(2:ℕ)*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((4*Real.sin (x 2)*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1021 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 1 (Function.update x 1 u)) (dGammaKerr M a 1 0 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 2 1 (Function.update x 1 u) = GammaKerrpt M a 0 2 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_021, dGammaKerr_1021, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1022 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 2 (Function.update x 1 u)) (dGammaKerr M a 1 0 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 2 2 (Function.update x 1 u) = GammaKerrpt M a 0 2 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_022, dGammaKerr_1022, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1023 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 3 (Function.update x 1 u)) (dGammaKerr M a 1 0 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 2 3 (Function.update x 1 u) = GammaKerrpt M a 0 2 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_023, dGammaKerr_1023, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((((((((((hasDerivAt_const (x 1) ((2*M*Real.cos (x 2)*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 5)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ)))).fun_add (((hasDerivAt_const (x 1) ((4*M*Real.cos (x 2)*a^(5:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(7:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((4*Real.cos (x 2)*M^(2:ℕ)*a^(5:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(5:ℕ))))).fun_sub ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(5:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((2*M*a*Real.sin (x 2)*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 5))).fun_add ((((hasDerivAt_const (x 1) ((4*M*Real.sin (x 2)*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3))).fun_add ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(5:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((2*M*a*Real.sin (x 2)*Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub ((((((hasDerivAt_const (x 1) ((8*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_sub (((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1030 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 0 (Function.update x 1 u)) (dGammaKerr M a 1 0 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 3 0 (Function.update x 1 u) = GammaKerrpt M a 0 3 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_030, dGammaKerr_1030, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1031 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 1 (Function.update x 1 u)) (dGammaKerr M a 1 0 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 3 1 (Function.update x 1 u) = GammaKerrpt M a 0 3 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_031, dGammaKerr_1031, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((((((((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_sub (((hasDerivAt_const (x 1) ((2*M*a))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 6)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((4*M*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 4)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((2*M*a^(5:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((4*M^(2:ℕ)*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_sub (((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add ((((hasDerivAt_const (x 1) ((M*a))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 4)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub ((((hasDerivAt_const (x 1) ((2*M*a))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub ((((((hasDerivAt_const (x 1) (2)).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1032 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 2 (Function.update x 1 u)) (dGammaKerr M a 1 0 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 3 2 (Function.update x 1 u) = GammaKerrpt M a 0 3 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_032, dGammaKerr_1032, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((((((((((hasDerivAt_const (x 1) ((2*M*Real.cos (x 2)*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 5)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ)))).fun_add (((hasDerivAt_const (x 1) ((4*M*Real.cos (x 2)*a^(5:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(7:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((4*Real.cos (x 2)*M^(2:ℕ)*a^(5:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(5:ℕ))))).fun_sub ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(5:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((2*M*a*Real.sin (x 2)*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 5))).fun_add ((((hasDerivAt_const (x 1) ((4*M*Real.sin (x 2)*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3))).fun_add ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(5:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((2*M*a*Real.sin (x 2)*Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub ((((((hasDerivAt_const (x 1) ((8*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_sub (((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1033 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 3 (Function.update x 1 u)) (dGammaKerr M a 1 0 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 0 3 3 (Function.update x 1 u) = GammaKerrpt M a 0 3 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_033, dGammaKerr_1033, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1100 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 0 (Function.update x 1 u)) (dGammaKerr M a 1 1 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 0 0 (Function.update x 1 u) = GammaKerrpt M a 1 0 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_100, dGammaKerr_1100, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_neg).fun_add (((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1101 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 1 (Function.update x 1 u)) (dGammaKerr M a 1 1 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 0 1 (Function.update x 1 u) = GammaKerrpt M a 1 0 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_101, dGammaKerr_1101, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1102 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 2 (Function.update x 1 u)) (dGammaKerr M a 1 1 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 0 2 (Function.update x 1 u) = GammaKerrpt M a 1 0 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_102, dGammaKerr_1102, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1103 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 3 (Function.update x 1 u)) (dGammaKerr M a 1 1 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 0 3 (Function.update x 1 u) = GammaKerrpt M a 1 0 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_103, dGammaKerr_1103, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((hasDerivAt_const (x 1) ((M*a))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_sub ((((hasDerivAt_const (x 1) ((2*M*a))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1110 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 0 (Function.update x 1 u)) (dGammaKerr M a 1 1 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 1 0 (Function.update x 1 u) = GammaKerrpt M a 1 1 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_110, dGammaKerr_1110, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1111 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 1 (Function.update x 1 u)) (dGammaKerr M a 1 1 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 1 1 (Function.update x 1 u) = GammaKerrpt M a 1 1 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_111, dGammaKerr_1111, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((hasDerivAt_id' (x 1)).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_add ((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))))).fun_sub ((hasDerivAt_id' (x 1)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1112 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 2 (Function.update x 1 u)) (dGammaKerr M a 1 1 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 1 2 (Function.update x 1 u) = GammaKerrpt M a 1 1 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_112, dGammaKerr_1112, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_const (x 1) (-(Real.sin (x 2)*Real.cos (x 2)*a^(2:ℕ)))).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1113 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 3 (Function.update x 1 u)) (dGammaKerr M a 1 1 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 1 3 (Function.update x 1 u) = GammaKerrpt M a 1 1 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_113, dGammaKerr_1113, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1120 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 0 (Function.update x 1 u)) (dGammaKerr M a 1 1 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 2 0 (Function.update x 1 u) = GammaKerrpt M a 1 2 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_120, dGammaKerr_1120, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1121 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 1 (Function.update x 1 u)) (dGammaKerr M a 1 1 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 2 1 (Function.update x 1 u) = GammaKerrpt M a 1 2 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_121, dGammaKerr_1121, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_const (x 1) (-(Real.sin (x 2)*Real.cos (x 2)*a^(2:ℕ)))).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1122 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 2 (Function.update x 1 u)) (dGammaKerr M a 1 1 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 2 2 (Function.update x 1 u) = GammaKerrpt M a 1 2 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_122, dGammaKerr_1122, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((hasDerivAt_id' (x 1)).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_neg).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1123 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 3 (Function.update x 1 u)) (dGammaKerr M a 1 1 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 2 3 (Function.update x 1 u) = GammaKerrpt M a 1 2 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_123, dGammaKerr_1123, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1130 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 0 (Function.update x 1 u)) (dGammaKerr M a 1 1 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 3 0 (Function.update x 1 u) = GammaKerrpt M a 1 3 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_130, dGammaKerr_1130, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((hasDerivAt_const (x 1) ((M*a))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_sub ((((hasDerivAt_const (x 1) ((2*M*a))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1131 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 1 (Function.update x 1 u)) (dGammaKerr M a 1 1 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 3 1 (Function.update x 1 u) = GammaKerrpt M a 1 3 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_131, dGammaKerr_1131, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1132 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 2 (Function.update x 1 u)) (dGammaKerr M a 1 1 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 3 2 (Function.update x 1 u) = GammaKerrpt M a 1 3 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_132, dGammaKerr_1132, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1133 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 3 (Function.update x 1 u)) (dGammaKerr M a 1 1 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 1 3 3 (Function.update x 1 u) = GammaKerrpt M a 1 3 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_133, dGammaKerr_1133, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((hasDerivAt_id' (x 1)).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2)).fun_neg).fun_sub (((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1200 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 0 (Function.update x 1 u)) (dGammaKerr M a 1 2 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 0 0 (Function.update x 1 u) = GammaKerrpt M a 2 0 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_200, dGammaKerr_1200, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((hasDerivAt_const (x 1) ((((-2))*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1201 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 1 (Function.update x 1 u)) (dGammaKerr M a 1 2 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 0 1 (Function.update x 1 u) = GammaKerrpt M a 2 0 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_201, dGammaKerr_1201, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1202 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 2 (Function.update x 1 u)) (dGammaKerr M a 1 2 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 0 2 (Function.update x 1 u) = GammaKerrpt M a 2 0 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_202, dGammaKerr_1202, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1203 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 3 (Function.update x 1 u)) (dGammaKerr M a 1 2 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 0 3 (Function.update x 1 u) = GammaKerrpt M a 2 0 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_203, dGammaKerr_1203, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ)))).fun_add (((((hasDerivAt_const (x 1) ((2*M*a))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1210 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 0 (Function.update x 1 u)) (dGammaKerr M a 1 2 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 1 0 (Function.update x 1 u) = GammaKerrpt M a 2 1 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_210, dGammaKerr_1210, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1211 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 1 (Function.update x 1 u)) (dGammaKerr M a 1 2 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 1 1 (Function.update x 1 u) = GammaKerrpt M a 2 1 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_211, dGammaKerr_1211, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_const (x 1) (Real.sin (x 2)*Real.cos (x 2)*a^(2:ℕ))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1212 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 2 (Function.update x 1 u)) (dGammaKerr M a 1 2 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 1 2 (Function.update x 1 u) = GammaKerrpt M a 2 1 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_212, dGammaKerr_1212, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_id' (x 1)).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1213 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 3 (Function.update x 1 u)) (dGammaKerr M a 1 2 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 1 3 (Function.update x 1 u) = GammaKerrpt M a 2 1 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_213, dGammaKerr_1213, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1220 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 0 (Function.update x 1 u)) (dGammaKerr M a 1 2 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 2 0 (Function.update x 1 u) = GammaKerrpt M a 2 2 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_220, dGammaKerr_1220, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1221 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 1 (Function.update x 1 u)) (dGammaKerr M a 1 2 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 2 1 (Function.update x 1 u) = GammaKerrpt M a 2 2 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_221, dGammaKerr_1221, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_id' (x 1)).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1222 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 2 (Function.update x 1 u)) (dGammaKerr M a 1 2 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 2 2 (Function.update x 1 u) = GammaKerrpt M a 2 2 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_222, dGammaKerr_1222, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((hasDerivAt_const (x 1) (-(Real.sin (x 2)*Real.cos (x 2)*a^(2:ℕ)))).fun_div (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1223 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 3 (Function.update x 1 u)) (dGammaKerr M a 1 2 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 2 3 (Function.update x 1 u) = GammaKerrpt M a 2 2 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_223, dGammaKerr_1223, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1230 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 0 (Function.update x 1 u)) (dGammaKerr M a 1 2 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 3 0 (Function.update x 1 u) = GammaKerrpt M a 2 3 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_230, dGammaKerr_1230, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ)))).fun_add (((((hasDerivAt_const (x 1) ((2*M*a))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1231 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 1 (Function.update x 1 u)) (dGammaKerr M a 1 2 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 3 1 (Function.update x 1 u) = GammaKerrpt M a 2 3 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_231, dGammaKerr_1231, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1232 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 2 (Function.update x 1 u)) (dGammaKerr M a 1 2 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 3 2 (Function.update x 1 u) = GammaKerrpt M a 2 3 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_232, dGammaKerr_1232, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1233 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 3 (Function.update x 1 u)) (dGammaKerr M a 1 2 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 2 3 3 (Function.update x 1 u) = GammaKerrpt M a 2 3 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_233, dGammaKerr_1233, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((hasDerivAt_const (x 1) ((Real.sin (x 2)*Real.cos (x 2)*a^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2)).fun_neg).fun_sub (((hasDerivAt_const (x 1) ((Real.sin (x 2)*Real.cos (x 2)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(5:ℕ))))).fun_sub ((((((hasDerivAt_const (x 1) ((4*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(3:ℕ))))).fun_div ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1300 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 0 (Function.update x 1 u)) (dGammaKerr M a 1 3 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 0 0 (Function.update x 1 u) = GammaKerrpt M a 3 0 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_300, dGammaKerr_1300, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1301 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 1 (Function.update x 1 u)) (dGammaKerr M a 1 3 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 0 1 (Function.update x 1 u) = GammaKerrpt M a 3 0 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_301, dGammaKerr_1301, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((hasDerivAt_const (x 1) ((4*a*M^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_sub (((hasDerivAt_const (x 1) ((M*a))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1)))).fun_add (((hasDerivAt_const (x 1) ((2*M*a))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_add ((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((2*M*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub ((((hasDerivAt_const (x 1) ((2*a))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1302 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 2 (Function.update x 1 u)) (dGammaKerr M a 1 3 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 0 2 (Function.update x 1 u) = GammaKerrpt M a 3 0 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_302, dGammaKerr_1302, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ)))).fun_sub (((hasDerivAt_const (x 1) ((4*Real.cos (x 2)*M^(2:ℕ)*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((((hasDerivAt_const (x 1) ((2*M*a))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1)))).fun_sub ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div (((hasDerivAt_const (x 1) (Real.sin (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1303 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 3 (Function.update x 1 u)) (dGammaKerr M a 1 3 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 0 3 (Function.update x 1 u) = GammaKerrpt M a 3 0 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_303, dGammaKerr_1303, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1310 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 0 (Function.update x 1 u)) (dGammaKerr M a 1 3 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 1 0 (Function.update x 1 u) = GammaKerrpt M a 3 1 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_310, dGammaKerr_1310, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((hasDerivAt_const (x 1) ((4*a*M^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_sub (((hasDerivAt_const (x 1) ((M*a))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1)))).fun_add (((hasDerivAt_const (x 1) ((2*M*a))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2))).fun_add ((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((2*M*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub ((((hasDerivAt_const (x 1) ((2*a))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1311 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 1 (Function.update x 1 u)) (dGammaKerr M a 1 3 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 1 1 (Function.update x 1 u) = GammaKerrpt M a 3 1 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_311, dGammaKerr_1311, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1312 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 2 (Function.update x 1 u)) (dGammaKerr M a 1 3 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 1 2 (Function.update x 1 u) = GammaKerrpt M a 3 1 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_312, dGammaKerr_1312, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1313 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 3 (Function.update x 1 u)) (dGammaKerr M a 1 3 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 1 3 (Function.update x 1 u) = GammaKerrpt M a 3 1 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_313, dGammaKerr_1313, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((((((hasDerivAt_id' (x 1)).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2)).fun_sub ((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((2*M*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((4*M^(2:ℕ)*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub ((((hasDerivAt_id' (x 1)).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_add (((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) (2)).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1320 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 0 (Function.update x 1 u)) (dGammaKerr M a 1 3 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 2 0 (Function.update x 1 u) = GammaKerrpt M a 3 2 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_320, dGammaKerr_1320, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ)))).fun_sub (((hasDerivAt_const (x 1) ((4*Real.cos (x 2)*M^(2:ℕ)*a^(3:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((((hasDerivAt_const (x 1) ((2*M*a))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1)))).fun_sub ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div (((hasDerivAt_const (x 1) (Real.sin (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1321 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 1 (Function.update x 1 u)) (dGammaKerr M a 1 3 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 2 1 (Function.update x 1 u) = GammaKerrpt M a 3 2 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_321, dGammaKerr_1321, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1322 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 2 (Function.update x 1 u)) (dGammaKerr M a 1 3 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 2 2 (Function.update x 1 u) = GammaKerrpt M a 3 2 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_322, dGammaKerr_1322, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1323 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 3 (Function.update x 1 u)) (dGammaKerr M a 1 3 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 2 3 (Function.update x 1 u) = GammaKerrpt M a 3 2 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_323, dGammaKerr_1323, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((((((((hasDerivAt_const (x 1) (Real.cos (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2)).fun_add ((((hasDerivAt_const (x 1) (Real.cos (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub ((hasDerivAt_const (x 1) ((Real.cos (x 2)*a^(4:ℕ)*Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(6:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(6:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((4*Real.cos (x 2)*M^(2:ℕ)*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_sub ((((hasDerivAt_const (x 1) ((Real.cos (x 2)*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_add ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_sub ((((((hasDerivAt_const (x 1) ((4*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) ((4*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add (((((((hasDerivAt_const (x 1) ((4*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div (((hasDerivAt_const (x 1) (Real.sin (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1330 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 0 (Function.update x 1 u)) (dGammaKerr M a 1 3 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 3 0 (Function.update x 1 u) = GammaKerrpt M a 3 3 0 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_330, dGammaKerr_1330, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_1331 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 1 (Function.update x 1 u)) (dGammaKerr M a 1 3 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 3 1 (Function.update x 1 u) = GammaKerrpt M a 3 3 1 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_331, dGammaKerr_1331, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine (((((((((((hasDerivAt_id' (x 1)).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2)).fun_sub ((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((2*M*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_sub (((hasDerivAt_const (x 1) ((4*M^(2:ℕ)*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 3)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub ((((hasDerivAt_id' (x 1)).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_add (((((hasDerivAt_const (x 1) (M)).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) (2)).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div ((hasDerivAt_Del_r M a (x 1)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1332 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 2 (Function.update x 1 u)) (dGammaKerr M a 1 3 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 3 2 (Function.update x 1 u) = GammaKerrpt M a 3 3 2 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_332, dGammaKerr_1332, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  refine ((((((((((((((hasDerivAt_const (x 1) (Real.cos (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2)).fun_add ((((hasDerivAt_const (x 1) (Real.cos (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub ((hasDerivAt_const (x 1) ((Real.cos (x 2)*a^(4:ℕ)*Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_sub (((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(6:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(6:ℕ))))).fun_add (((hasDerivAt_const (x 1) ((4*Real.cos (x 2)*M^(2:ℕ)*a^(4:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_sub ((((hasDerivAt_const (x 1) ((Real.cos (x 2)*a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 2))).fun_add ((((((hasDerivAt_const (x 1) ((2*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_sub ((((((hasDerivAt_const (x 1) ((4*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(4:ℕ))))).fun_add ((((((hasDerivAt_const (x 1) ((4*Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_const (x 1) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul ((hasDerivAt_id' (x 1)).fun_pow 2)).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_add (((((((hasDerivAt_const (x 1) ((4*M))).fun_mul (hasDerivAt_id' (x 1))).fun_mul (hasDerivAt_const (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Sig_r a (x 1) (Real.cos (x 2)))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul (hasDerivAt_const (x 1) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 1) (Real.sin (x 2)^(2:ℕ))))).fun_div (((hasDerivAt_const (x 1) (Real.sin (x 2))).fun_mul (hasDerivAt_Del_r M a (x 1))).fun_mul ((hasDerivAt_Sig_r a (x 1) (Real.cos (x 2))).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_1333 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 3 (Function.update x 1 u)) (dGammaKerr M a 1 3 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 1) := by
  have hev : ∀ᶠ u in 𝓝 (x 1), christoffel (gKerr M a) (giKerr M a) 3 3 3 (Function.update x 1 u) = GammaKerrpt M a 3 3 3 (Function.update x 1 u) :=
    (tendsto_update x 1).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_333, dGammaKerr_1333, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 1 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 1 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2000 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 0 (Function.update x 2 u)) (dGammaKerr M a 2 0 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 0 0 (Function.update x 2 u) = GammaKerrpt M a 0 0 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_000, dGammaKerr_2000, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2001 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 1 (Function.update x 2 u)) (dGammaKerr M a 2 0 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 0 1 (Function.update x 2 u) = GammaKerrpt M a 0 0 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_001, dGammaKerr_2001, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((((hasDerivAt_const (x 2) (2*M*(x 1)^(6:ℕ))).fun_sub (((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ))))).fun_sub (((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(4:ℕ))))).fun_add (hasDerivAt_const (x 2) (4*M*a^(2:ℕ)*(x 1)^(4:ℕ)))).fun_add (hasDerivAt_const (x 2) (2*M*a^(4:ℕ)*(x 1)^(2:ℕ)))).fun_sub ((((hasDerivAt_const (x 2) ((2*M))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ))))).fun_sub ((hasDerivAt_const (x 2) ((4*M^(2:ℕ)*a^(2:ℕ)*(x 1)^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((2*M*Del M a (x 1)*a^(2:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*(x 1)))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2002 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 2 (Function.update x 2 u)) (dGammaKerr M a 2 0 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 0 2 (Function.update x 2 u) = GammaKerrpt M a 0 0 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_002, dGammaKerr_2002, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((((hasDerivAt_const (x 2) ((((-2))*M))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(5:ℕ)))).fun_sub (((((hasDerivAt_const (x 2) ((4*M))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(3:ℕ))))).fun_sub ((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(6:ℕ))))).fun_add ((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_add (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_add (((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ))))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2003 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 3 (Function.update x 2 u)) (dGammaKerr M a 2 0 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 0 3 (Function.update x 2 u) = GammaKerrpt M a 0 0 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_003, dGammaKerr_2003, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2010 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 0 (Function.update x 2 u)) (dGammaKerr M a 2 0 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 1 0 (Function.update x 2 u) = GammaKerrpt M a 0 1 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_010, dGammaKerr_2010, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((((hasDerivAt_const (x 2) (2*M*(x 1)^(6:ℕ))).fun_sub (((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ))))).fun_sub (((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(4:ℕ))))).fun_add (hasDerivAt_const (x 2) (4*M*a^(2:ℕ)*(x 1)^(4:ℕ)))).fun_add (hasDerivAt_const (x 2) (2*M*a^(4:ℕ)*(x 1)^(2:ℕ)))).fun_sub ((((hasDerivAt_const (x 2) ((2*M))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ))))).fun_sub ((hasDerivAt_const (x 2) ((4*M^(2:ℕ)*a^(2:ℕ)*(x 1)^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((2*M*Del M a (x 1)*a^(2:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*(x 1)))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2011 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 1 (Function.update x 2 u)) (dGammaKerr M a 2 0 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 1 1 (Function.update x 2 u) = GammaKerrpt M a 0 1 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_011, dGammaKerr_2011, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2012 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 2 (Function.update x 2 u)) (dGammaKerr M a 2 0 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 1 2 (Function.update x 2 u) = GammaKerrpt M a 0 1 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_012, dGammaKerr_2012, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2013 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 3 (Function.update x 2 u)) (dGammaKerr M a 2 0 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 1 3 (Function.update x 2 u) = GammaKerrpt M a 0 1 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_013, dGammaKerr_2013, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((((((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_sub ((hasDerivAt_const (x 2) ((2*M*a*(x 1)^(6:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((4*M*a^(3:ℕ)*(x 1)^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((2*M*a^(5:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add ((hasDerivAt_const (x 2) ((4*M^(2:ℕ)*a^(3:ℕ)*(x 1)^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_sub (((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add ((hasDerivAt_const (x 2) ((2*M*Del M a (x 1)*a^(3:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add ((((hasDerivAt_const (x 2) ((M*a))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*M))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub (((hasDerivAt_const (x 2) ((2*M*a*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub (((((hasDerivAt_const (x 2) ((2*(x 1)))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2020 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 0 (Function.update x 2 u)) (dGammaKerr M a 2 0 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 2 0 (Function.update x 2 u) = GammaKerrpt M a 0 2 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_020, dGammaKerr_2020, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((((hasDerivAt_const (x 2) ((((-2))*M))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(5:ℕ)))).fun_sub (((((hasDerivAt_const (x 2) ((4*M))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(3:ℕ))))).fun_sub ((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(6:ℕ))))).fun_add ((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_add (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_add (((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ))))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2021 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 1 (Function.update x 2 u)) (dGammaKerr M a 2 0 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 2 1 (Function.update x 2 u) = GammaKerrpt M a 0 2 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_021, dGammaKerr_2021, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2022 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 2 (Function.update x 2 u)) (dGammaKerr M a 2 0 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 2 2 (Function.update x 2 u) = GammaKerrpt M a 0 2 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_022, dGammaKerr_2022, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2023 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 3 (Function.update x 2 u)) (dGammaKerr M a 2 0 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 2 3 (Function.update x 2 u) = GammaKerrpt M a 0 2 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_023, dGammaKerr_2023, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((((((((((hasDerivAt_const (x 2) ((2*M))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(5:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3)).fun_add (((((hasDerivAt_const (x 2) ((4*M))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_add ((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(7:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_sub ((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 5))).fun_sub (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 5))).fun_add (((((hasDerivAt_const (x 2) ((2*M*a))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(5:ℕ))))).fun_add ((((((hasDerivAt_const (x 2) ((4*M))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(3:ℕ))))).fun_add (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ))))).fun_sub (((((hasDerivAt_const (x 2) ((2*M*a))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(3:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub (((((((hasDerivAt_const (x 2) (8)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_sub ((((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2030 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 0 (Function.update x 2 u)) (dGammaKerr M a 2 0 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 3 0 (Function.update x 2 u) = GammaKerrpt M a 0 3 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_030, dGammaKerr_2030, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2031 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 1 (Function.update x 2 u)) (dGammaKerr M a 2 0 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 3 1 (Function.update x 2 u) = GammaKerrpt M a 0 3 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_031, dGammaKerr_2031, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((((((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_sub ((hasDerivAt_const (x 2) ((2*M*a*(x 1)^(6:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((4*M*a^(3:ℕ)*(x 1)^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((2*M*a^(5:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add ((hasDerivAt_const (x 2) ((4*M^(2:ℕ)*a^(3:ℕ)*(x 1)^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_sub (((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add ((hasDerivAt_const (x 2) ((2*M*Del M a (x 1)*a^(3:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add ((((hasDerivAt_const (x 2) ((M*a))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*M))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub (((hasDerivAt_const (x 2) ((2*M*a*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub (((((hasDerivAt_const (x 2) ((2*(x 1)))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2032 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 2 (Function.update x 2 u)) (dGammaKerr M a 2 0 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 3 2 (Function.update x 2 u) = GammaKerrpt M a 0 3 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_032, dGammaKerr_2032, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((((((((((hasDerivAt_const (x 2) ((2*M))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(5:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3)).fun_add (((((hasDerivAt_const (x 2) ((4*M))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_add ((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(7:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_sub ((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 5))).fun_sub (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 5))).fun_add (((((hasDerivAt_const (x 2) ((2*M*a))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(5:ℕ))))).fun_add ((((((hasDerivAt_const (x 2) ((4*M))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(3:ℕ))))).fun_add (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ))))).fun_sub (((((hasDerivAt_const (x 2) ((2*M*a))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(3:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub (((((((hasDerivAt_const (x 2) (8)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_sub ((((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2033 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 3 (Function.update x 2 u)) (dGammaKerr M a 2 0 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 0 3 3 (Function.update x 2 u) = GammaKerrpt M a 0 3 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_033, dGammaKerr_2033, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2100 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 0 (Function.update x 2 u)) (dGammaKerr M a 2 1 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 0 0 (Function.update x 2 u) = GammaKerrpt M a 1 0 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_100, dGammaKerr_2100, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_neg).fun_add (hasDerivAt_const (x 2) (2*M*Del M a (x 1)*(x 1)^(2:ℕ)))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2101 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 1 (Function.update x 2 u)) (dGammaKerr M a 2 1 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 0 1 (Function.update x 2 u) = GammaKerrpt M a 1 0 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_101, dGammaKerr_2101, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2102 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 2 (Function.update x 2 u)) (dGammaKerr M a 2 1 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 0 2 (Function.update x 2 u) = GammaKerrpt M a 1 0 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_102, dGammaKerr_2102, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2103 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 3 (Function.update x 2 u)) (dGammaKerr M a 2 1 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 0 3 (Function.update x 2 u) = GammaKerrpt M a 1 0 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_103, dGammaKerr_2103, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((hasDerivAt_const (x 2) ((M*a))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_sub ((hasDerivAt_const (x 2) ((2*M*a*Del M a (x 1)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2110 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 0 (Function.update x 2 u)) (dGammaKerr M a 2 1 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 1 0 (Function.update x 2 u) = GammaKerrpt M a 1 1 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_110, dGammaKerr_2110, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2111 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 1 (Function.update x 2 u)) (dGammaKerr M a 2 1 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 1 1 (Function.update x 2 u) = GammaKerrpt M a 1 1 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_111, dGammaKerr_2111, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((hasDerivAt_const (x 2) ((x 1)*Del M a (x 1))).fun_add ((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2)))).fun_sub ((hasDerivAt_const (x 2) ((x 1))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2)))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2112 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 2 (Function.update x 2 u)) (dGammaKerr M a 2 1 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 1 2 (Function.update x 2 u) = GammaKerrpt M a 1 1 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_112, dGammaKerr_2112, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((Real.hasDerivAt_sin (x 2)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_neg).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2113 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 3 (Function.update x 2 u)) (dGammaKerr M a 2 1 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 1 3 (Function.update x 2 u) = GammaKerrpt M a 1 1 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_113, dGammaKerr_2113, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2120 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 0 (Function.update x 2 u)) (dGammaKerr M a 2 1 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 2 0 (Function.update x 2 u) = GammaKerrpt M a 1 2 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_120, dGammaKerr_2120, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2121 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 1 (Function.update x 2 u)) (dGammaKerr M a 2 1 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 2 1 (Function.update x 2 u) = GammaKerrpt M a 1 2 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_121, dGammaKerr_2121, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((Real.hasDerivAt_sin (x 2)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_neg).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2122 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 2 (Function.update x 2 u)) (dGammaKerr M a 2 1 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 2 2 (Function.update x 2 u) = GammaKerrpt M a 1 2 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_122, dGammaKerr_2122, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((hasDerivAt_const (x 2) (-((x 1)*Del M a (x 1)))).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2123 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 3 (Function.update x 2 u)) (dGammaKerr M a 2 1 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 2 3 (Function.update x 2 u) = GammaKerrpt M a 1 2 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_123, dGammaKerr_2123, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2130 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 0 (Function.update x 2 u)) (dGammaKerr M a 2 1 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 3 0 (Function.update x 2 u) = GammaKerrpt M a 1 3 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_130, dGammaKerr_2130, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((hasDerivAt_const (x 2) ((M*a))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_sub ((hasDerivAt_const (x 2) ((2*M*a*Del M a (x 1)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2131 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 1 (Function.update x 2 u)) (dGammaKerr M a 2 1 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 3 1 (Function.update x 2 u) = GammaKerrpt M a 1 3 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_131, dGammaKerr_2131, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2132 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 2 (Function.update x 2 u)) (dGammaKerr M a 2 1 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 3 2 (Function.update x 2 u) = GammaKerrpt M a 1 3 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_132, dGammaKerr_2132, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2133 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 3 (Function.update x 2 u)) (dGammaKerr M a 2 1 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 1 3 3 (Function.update x 2 u) = GammaKerrpt M a 1 3 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_133, dGammaKerr_2133, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((hasDerivAt_const (x 2) (((x 1)*Del M a (x 1)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2)).fun_neg).fun_sub (((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add ((hasDerivAt_const (x 2) ((2*M*Del M a (x 1)*a^(2:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2200 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 0 (Function.update x 2 u)) (dGammaKerr M a 2 2 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 0 0 (Function.update x 2 u) = GammaKerrpt M a 2 0 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_200, dGammaKerr_2200, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((hasDerivAt_const (x 2) ((((-2))*M*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2201 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 1 (Function.update x 2 u)) (dGammaKerr M a 2 2 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 0 1 (Function.update x 2 u) = GammaKerrpt M a 2 0 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_201, dGammaKerr_2201, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2202 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 2 (Function.update x 2 u)) (dGammaKerr M a 2 2 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 0 2 (Function.update x 2 u) = GammaKerrpt M a 2 0 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_202, dGammaKerr_2202, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2203 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 3 (Function.update x 2 u)) (dGammaKerr M a 2 2 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 0 3 (Function.update x 2 u) = GammaKerrpt M a 2 0 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_203, dGammaKerr_2203, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3)).fun_add ((((hasDerivAt_const (x 2) ((2*M*a*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2)))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2210 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 0 (Function.update x 2 u)) (dGammaKerr M a 2 2 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 1 0 (Function.update x 2 u) = GammaKerrpt M a 2 1 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_210, dGammaKerr_2210, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2211 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 1 (Function.update x 2 u)) (dGammaKerr M a 2 2 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 1 1 (Function.update x 2 u) = GammaKerrpt M a 2 1 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_211, dGammaKerr_2211, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((Real.hasDerivAt_sin (x 2)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2212 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 2 (Function.update x 2 u)) (dGammaKerr M a 2 2 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 1 2 (Function.update x 2 u) = GammaKerrpt M a 2 1 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_212, dGammaKerr_2212, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((hasDerivAt_const (x 2) ((x 1))).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2213 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 3 (Function.update x 2 u)) (dGammaKerr M a 2 2 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 1 3 (Function.update x 2 u) = GammaKerrpt M a 2 1 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_213, dGammaKerr_2213, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2220 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 0 (Function.update x 2 u)) (dGammaKerr M a 2 2 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 2 0 (Function.update x 2 u) = GammaKerrpt M a 2 2 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_220, dGammaKerr_2220, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2221 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 1 (Function.update x 2 u)) (dGammaKerr M a 2 2 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 2 1 (Function.update x 2 u) = GammaKerrpt M a 2 2 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_221, dGammaKerr_2221, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((hasDerivAt_const (x 2) ((x 1))).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2222 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 2 (Function.update x 2 u)) (dGammaKerr M a 2 2 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 2 2 (Function.update x 2 u) = GammaKerrpt M a 2 2 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_222, dGammaKerr_2222, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((Real.hasDerivAt_sin (x 2)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_neg).fun_div (hasDerivAt_Sig_th a (x 1) (x 2)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2223 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 3 (Function.update x 2 u)) (dGammaKerr M a 2 2 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 2 3 (Function.update x 2 u) = GammaKerrpt M a 2 2 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_223, dGammaKerr_2223, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2230 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 0 (Function.update x 2 u)) (dGammaKerr M a 2 2 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 3 0 (Function.update x 2 u) = GammaKerrpt M a 2 3 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_230, dGammaKerr_2230, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3)).fun_add ((((hasDerivAt_const (x 2) ((2*M*a*(x 1)))).fun_mul (Real.hasDerivAt_sin (x 2))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2)))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2231 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 1 (Function.update x 2 u)) (dGammaKerr M a 2 2 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 3 1 (Function.update x 2 u) = GammaKerrpt M a 2 3 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_231, dGammaKerr_2231, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2232 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 2 (Function.update x 2 u)) (dGammaKerr M a 2 2 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 3 2 (Function.update x 2 u) = GammaKerrpt M a 2 3 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_232, dGammaKerr_2232, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2233 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 3 (Function.update x 2 u)) (dGammaKerr M a 2 2 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 2 3 3 (Function.update x 2 u) = GammaKerrpt M a 2 3 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_233, dGammaKerr_2233, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((Real.hasDerivAt_sin (x 2)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2)).fun_neg).fun_sub ((((Real.hasDerivAt_sin (x 2)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub ((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 5))).fun_sub (((((hasDerivAt_const (x 2) ((4*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 3))).fun_div ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2300 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 0 (Function.update x 2 u)) (dGammaKerr M a 2 3 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 0 0 (Function.update x 2 u) = GammaKerrpt M a 3 0 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_300, dGammaKerr_2300, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2301 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 1 (Function.update x 2 u)) (dGammaKerr M a 2 3 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 0 1 (Function.update x 2 u) = GammaKerrpt M a 3 0 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_301, dGammaKerr_2301, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((hasDerivAt_const (x 2) (4*a*M^(2:ℕ)*(x 1)^(3:ℕ))).fun_sub (((hasDerivAt_const (x 2) ((M*a))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1))))).fun_add (hasDerivAt_const (x 2) (2*M*a*Del M a (x 1)*(x 1)^(2:ℕ)))).fun_add ((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((2*M*a^(3:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub (((hasDerivAt_const (x 2) ((2*a*(x 1)))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ))))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2302 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 2 (Function.update x 2 u)) (dGammaKerr M a 2 3 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 0 2 (Function.update x 2 u) = GammaKerrpt M a 3 0 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_302, dGammaKerr_2302, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4)).fun_sub ((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((((hasDerivAt_const (x 2) ((2*M*a*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1))))).fun_sub (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div (((Real.hasDerivAt_sin (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2303 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 3 (Function.update x 2 u)) (dGammaKerr M a 2 3 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 0 3 (Function.update x 2 u) = GammaKerrpt M a 3 0 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_303, dGammaKerr_2303, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2310 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 0 (Function.update x 2 u)) (dGammaKerr M a 2 3 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 1 0 (Function.update x 2 u) = GammaKerrpt M a 3 1 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_310, dGammaKerr_2310, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((hasDerivAt_const (x 2) (4*a*M^(2:ℕ)*(x 1)^(3:ℕ))).fun_sub (((hasDerivAt_const (x 2) ((M*a))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1))))).fun_add (hasDerivAt_const (x 2) (2*M*a*Del M a (x 1)*(x 1)^(2:ℕ)))).fun_add ((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((2*M*a^(3:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub (((hasDerivAt_const (x 2) ((2*a*(x 1)))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ))))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2311 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 1 (Function.update x 2 u)) (dGammaKerr M a 2 3 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 1 1 (Function.update x 2 u) = GammaKerrpt M a 3 1 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_311, dGammaKerr_2311, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2312 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 2 (Function.update x 2 u)) (dGammaKerr M a 2 3 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 1 2 (Function.update x 2 u) = GammaKerrpt M a 3 1 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_312, dGammaKerr_2312, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2313 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 3 (Function.update x 2 u)) (dGammaKerr M a 2 3 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 1 3 (Function.update x 2 u) = GammaKerrpt M a 3 1 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_313, dGammaKerr_2313, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((((((hasDerivAt_const (x 2) (((x 1)*Del M a (x 1)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2)).fun_sub ((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add ((hasDerivAt_const (x 2) ((2*M*a^(4:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_sub ((hasDerivAt_const (x 2) ((4*M^(2:ℕ)*a^(2:ℕ)*(x 1)^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub (((hasDerivAt_const (x 2) (((x 1)*a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((2*M*Del M a (x 1)*a^(2:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*(x 1)))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2320 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 0 (Function.update x 2 u)) (dGammaKerr M a 2 3 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 2 0 (Function.update x 2 u) = GammaKerrpt M a 3 2 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_320, dGammaKerr_2320, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine (((((((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(5:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4)).fun_sub ((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((((hasDerivAt_const (x 2) ((2*M*a*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1))))).fun_sub (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div (((Real.hasDerivAt_sin (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2321 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 1 (Function.update x 2 u)) (dGammaKerr M a 2 3 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 2 1 (Function.update x 2 u) = GammaKerrpt M a 3 2 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_321, dGammaKerr_2321, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2322 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 2 (Function.update x 2 u)) (dGammaKerr M a 2 3 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 2 2 (Function.update x 2 u) = GammaKerrpt M a 3 2 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_322, dGammaKerr_2322, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2323 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 3 (Function.update x 2 u)) (dGammaKerr M a 2 3 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 2 3 (Function.update x 2 u) = GammaKerrpt M a 3 2 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_323, dGammaKerr_2323, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((((((((((Real.hasDerivAt_cos (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2)).fun_add ((((Real.hasDerivAt_cos (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub ((((Real.hasDerivAt_cos (x 2)).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub ((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(6:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 6))).fun_add ((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_sub (((((Real.hasDerivAt_cos (x 2)).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_sub (((((hasDerivAt_const (x 2) ((4*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add (((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add ((((((hasDerivAt_const (x 2) ((4*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div (((Real.hasDerivAt_sin (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2330 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 0 (Function.update x 2 u)) (dGammaKerr M a 2 3 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 3 0 (Function.update x 2 u) = GammaKerrpt M a 3 3 0 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_330, dGammaKerr_2330, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_2331 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 1 (Function.update x 2 u)) (dGammaKerr M a 2 3 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 3 1 (Function.update x 2 u) = GammaKerrpt M a 3 3 1 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_331, dGammaKerr_2331, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((((((hasDerivAt_const (x 2) (((x 1)*Del M a (x 1)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2)).fun_sub ((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add ((hasDerivAt_const (x 2) ((2*M*a^(4:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_sub ((hasDerivAt_const (x 2) ((4*M^(2:ℕ)*a^(2:ℕ)*(x 1)^(3:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub (((hasDerivAt_const (x 2) (((x 1)*a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) (M)).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_sub ((hasDerivAt_const (x 2) ((2*M*Del M a (x 1)*a^(2:ℕ)*(x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*(x 1)))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div ((hasDerivAt_const (x 2) (Del M a (x 1))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2332 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 2 (Function.update x 2 u)) (dGammaKerr M a 2 3 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 3 2 (Function.update x 2 u) = GammaKerrpt M a 3 3 2 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_332, dGammaKerr_2332, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  refine ((((((((((((((Real.hasDerivAt_cos (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2)).fun_add ((((Real.hasDerivAt_cos (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub ((((Real.hasDerivAt_cos (x 2)).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_sub ((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(6:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 6))).fun_add ((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_sub (((((Real.hasDerivAt_cos (x 2)).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2)).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 2))).fun_add (((((hasDerivAt_const (x 2) ((2*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_sub (((((hasDerivAt_const (x 2) ((4*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (a^(4:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 4))).fun_add (((((((hasDerivAt_const (x 2) (4)).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (M^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul (hasDerivAt_const (x 2) ((x 1)^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_add ((((((hasDerivAt_const (x 2) ((4*M*(x 1)))).fun_mul (Real.hasDerivAt_cos (x 2))).fun_mul (hasDerivAt_Sig_th a (x 1) (x 2))).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul (hasDerivAt_const (x 2) (a^(2:ℕ)))).fun_mul ((Real.hasDerivAt_sin (x 2)).fun_pow 2))).fun_div (((Real.hasDerivAt_sin (x 2)).fun_mul (hasDerivAt_const (x 2) (Del M a (x 1)))).fun_mul ((hasDerivAt_Sig_th a (x 1) (x 2)).fun_pow 3)) (by beta_reduce; first | positivity | simp [hS, hD, hs])).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp

theorem hdchrKerr_2333 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 3 (Function.update x 2 u)) (dGammaKerr M a 2 3 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 2) := by
  have hev : ∀ᶠ u in 𝓝 (x 2), christoffel (gKerr M a) (giKerr M a) 3 3 3 (Function.update x 2 u) = GammaKerrpt M a 3 3 3 (Function.update x 2 u) :=
    (tendsto_update x 2).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_333, dGammaKerr_2333, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 2 by decide), Function.update_of_ne (show (3:Fin 4) ≠ 2 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3000 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 0 (Function.update x 3 u)) (dGammaKerr M a 3 0 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 0 0 (Function.update x 3 u) = GammaKerrpt M a 0 0 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_000, dGammaKerr_3000, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3001 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 1 (Function.update x 3 u)) (dGammaKerr M a 3 0 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 0 1 (Function.update x 3 u) = GammaKerrpt M a 0 0 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_001, dGammaKerr_3001, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3002 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 2 (Function.update x 3 u)) (dGammaKerr M a 3 0 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 0 2 (Function.update x 3 u) = GammaKerrpt M a 0 0 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_002, dGammaKerr_3002, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3003 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 0 3 (Function.update x 3 u)) (dGammaKerr M a 3 0 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 0 3 (Function.update x 3 u) = GammaKerrpt M a 0 0 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_003, dGammaKerr_3003, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3010 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 0 (Function.update x 3 u)) (dGammaKerr M a 3 0 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 1 0 (Function.update x 3 u) = GammaKerrpt M a 0 1 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_010, dGammaKerr_3010, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3011 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 1 (Function.update x 3 u)) (dGammaKerr M a 3 0 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 1 1 (Function.update x 3 u) = GammaKerrpt M a 0 1 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_011, dGammaKerr_3011, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3012 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 2 (Function.update x 3 u)) (dGammaKerr M a 3 0 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 1 2 (Function.update x 3 u) = GammaKerrpt M a 0 1 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_012, dGammaKerr_3012, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3013 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 1 3 (Function.update x 3 u)) (dGammaKerr M a 3 0 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 1 3 (Function.update x 3 u) = GammaKerrpt M a 0 1 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_013, dGammaKerr_3013, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3020 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 0 (Function.update x 3 u)) (dGammaKerr M a 3 0 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 2 0 (Function.update x 3 u) = GammaKerrpt M a 0 2 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_020, dGammaKerr_3020, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3021 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 1 (Function.update x 3 u)) (dGammaKerr M a 3 0 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 2 1 (Function.update x 3 u) = GammaKerrpt M a 0 2 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_021, dGammaKerr_3021, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3022 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 2 (Function.update x 3 u)) (dGammaKerr M a 3 0 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 2 2 (Function.update x 3 u) = GammaKerrpt M a 0 2 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_022, dGammaKerr_3022, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3023 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 2 3 (Function.update x 3 u)) (dGammaKerr M a 3 0 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 2 3 (Function.update x 3 u) = GammaKerrpt M a 0 2 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_023, dGammaKerr_3023, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3030 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 0 (Function.update x 3 u)) (dGammaKerr M a 3 0 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 3 0 (Function.update x 3 u) = GammaKerrpt M a 0 3 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_030, dGammaKerr_3030, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3031 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 1 (Function.update x 3 u)) (dGammaKerr M a 3 0 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 3 1 (Function.update x 3 u) = GammaKerrpt M a 0 3 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_031, dGammaKerr_3031, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3032 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 2 (Function.update x 3 u)) (dGammaKerr M a 3 0 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 3 2 (Function.update x 3 u) = GammaKerrpt M a 0 3 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_032, dGammaKerr_3032, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3033 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 0 3 3 (Function.update x 3 u)) (dGammaKerr M a 3 0 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 0 3 3 (Function.update x 3 u) = GammaKerrpt M a 0 3 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 0 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_033, dGammaKerr_3033, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3100 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 0 (Function.update x 3 u)) (dGammaKerr M a 3 1 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 0 0 (Function.update x 3 u) = GammaKerrpt M a 1 0 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_100, dGammaKerr_3100, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3101 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 1 (Function.update x 3 u)) (dGammaKerr M a 3 1 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 0 1 (Function.update x 3 u) = GammaKerrpt M a 1 0 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_101, dGammaKerr_3101, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3102 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 2 (Function.update x 3 u)) (dGammaKerr M a 3 1 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 0 2 (Function.update x 3 u) = GammaKerrpt M a 1 0 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_102, dGammaKerr_3102, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3103 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 0 3 (Function.update x 3 u)) (dGammaKerr M a 3 1 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 0 3 (Function.update x 3 u) = GammaKerrpt M a 1 0 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_103, dGammaKerr_3103, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3110 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 0 (Function.update x 3 u)) (dGammaKerr M a 3 1 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 1 0 (Function.update x 3 u) = GammaKerrpt M a 1 1 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_110, dGammaKerr_3110, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3111 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 1 (Function.update x 3 u)) (dGammaKerr M a 3 1 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 1 1 (Function.update x 3 u) = GammaKerrpt M a 1 1 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_111, dGammaKerr_3111, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3112 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 2 (Function.update x 3 u)) (dGammaKerr M a 3 1 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 1 2 (Function.update x 3 u) = GammaKerrpt M a 1 1 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_112, dGammaKerr_3112, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3113 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 1 3 (Function.update x 3 u)) (dGammaKerr M a 3 1 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 1 3 (Function.update x 3 u) = GammaKerrpt M a 1 1 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_113, dGammaKerr_3113, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3120 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 0 (Function.update x 3 u)) (dGammaKerr M a 3 1 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 2 0 (Function.update x 3 u) = GammaKerrpt M a 1 2 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_120, dGammaKerr_3120, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3121 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 1 (Function.update x 3 u)) (dGammaKerr M a 3 1 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 2 1 (Function.update x 3 u) = GammaKerrpt M a 1 2 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_121, dGammaKerr_3121, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3122 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 2 (Function.update x 3 u)) (dGammaKerr M a 3 1 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 2 2 (Function.update x 3 u) = GammaKerrpt M a 1 2 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_122, dGammaKerr_3122, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3123 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 2 3 (Function.update x 3 u)) (dGammaKerr M a 3 1 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 2 3 (Function.update x 3 u) = GammaKerrpt M a 1 2 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_123, dGammaKerr_3123, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3130 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 0 (Function.update x 3 u)) (dGammaKerr M a 3 1 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 3 0 (Function.update x 3 u) = GammaKerrpt M a 1 3 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_130, dGammaKerr_3130, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3131 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 1 (Function.update x 3 u)) (dGammaKerr M a 3 1 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 3 1 (Function.update x 3 u) = GammaKerrpt M a 1 3 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_131, dGammaKerr_3131, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3132 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 2 (Function.update x 3 u)) (dGammaKerr M a 3 1 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 3 2 (Function.update x 3 u) = GammaKerrpt M a 1 3 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_132, dGammaKerr_3132, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3133 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 1 3 3 (Function.update x 3 u)) (dGammaKerr M a 3 1 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 1 3 3 (Function.update x 3 u) = GammaKerrpt M a 1 3 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 1 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_133, dGammaKerr_3133, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3200 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 0 (Function.update x 3 u)) (dGammaKerr M a 3 2 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 0 0 (Function.update x 3 u) = GammaKerrpt M a 2 0 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_200, dGammaKerr_3200, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3201 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 1 (Function.update x 3 u)) (dGammaKerr M a 3 2 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 0 1 (Function.update x 3 u) = GammaKerrpt M a 2 0 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_201, dGammaKerr_3201, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3202 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 2 (Function.update x 3 u)) (dGammaKerr M a 3 2 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 0 2 (Function.update x 3 u) = GammaKerrpt M a 2 0 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_202, dGammaKerr_3202, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3203 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 0 3 (Function.update x 3 u)) (dGammaKerr M a 3 2 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 0 3 (Function.update x 3 u) = GammaKerrpt M a 2 0 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_203, dGammaKerr_3203, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3210 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 0 (Function.update x 3 u)) (dGammaKerr M a 3 2 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 1 0 (Function.update x 3 u) = GammaKerrpt M a 2 1 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_210, dGammaKerr_3210, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3211 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 1 (Function.update x 3 u)) (dGammaKerr M a 3 2 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 1 1 (Function.update x 3 u) = GammaKerrpt M a 2 1 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_211, dGammaKerr_3211, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3212 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 2 (Function.update x 3 u)) (dGammaKerr M a 3 2 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 1 2 (Function.update x 3 u) = GammaKerrpt M a 2 1 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_212, dGammaKerr_3212, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3213 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 1 3 (Function.update x 3 u)) (dGammaKerr M a 3 2 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 1 3 (Function.update x 3 u) = GammaKerrpt M a 2 1 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_213, dGammaKerr_3213, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3220 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 0 (Function.update x 3 u)) (dGammaKerr M a 3 2 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 2 0 (Function.update x 3 u) = GammaKerrpt M a 2 2 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_220, dGammaKerr_3220, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3221 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 1 (Function.update x 3 u)) (dGammaKerr M a 3 2 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 2 1 (Function.update x 3 u) = GammaKerrpt M a 2 2 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_221, dGammaKerr_3221, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3222 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 2 (Function.update x 3 u)) (dGammaKerr M a 3 2 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 2 2 (Function.update x 3 u) = GammaKerrpt M a 2 2 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_222, dGammaKerr_3222, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3223 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 2 3 (Function.update x 3 u)) (dGammaKerr M a 3 2 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 2 3 (Function.update x 3 u) = GammaKerrpt M a 2 2 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_223, dGammaKerr_3223, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3230 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 0 (Function.update x 3 u)) (dGammaKerr M a 3 2 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 3 0 (Function.update x 3 u) = GammaKerrpt M a 2 3 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_230, dGammaKerr_3230, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3231 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 1 (Function.update x 3 u)) (dGammaKerr M a 3 2 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 3 1 (Function.update x 3 u) = GammaKerrpt M a 2 3 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_231, dGammaKerr_3231, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3232 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 2 (Function.update x 3 u)) (dGammaKerr M a 3 2 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 3 2 (Function.update x 3 u) = GammaKerrpt M a 2 3 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_232, dGammaKerr_3232, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3233 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 2 3 3 (Function.update x 3 u)) (dGammaKerr M a 3 2 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 2 3 3 (Function.update x 3 u) = GammaKerrpt M a 2 3 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 2 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_233, dGammaKerr_3233, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3300 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 0 (Function.update x 3 u)) (dGammaKerr M a 3 3 0 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 0 0 (Function.update x 3 u) = GammaKerrpt M a 3 0 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_300, dGammaKerr_3300, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3301 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 1 (Function.update x 3 u)) (dGammaKerr M a 3 3 0 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 0 1 (Function.update x 3 u) = GammaKerrpt M a 3 0 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_301, dGammaKerr_3301, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3302 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 2 (Function.update x 3 u)) (dGammaKerr M a 3 3 0 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 0 2 (Function.update x 3 u) = GammaKerrpt M a 3 0 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_302, dGammaKerr_3302, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3303 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 0 3 (Function.update x 3 u)) (dGammaKerr M a 3 3 0 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 0 3 (Function.update x 3 u) = GammaKerrpt M a 3 0 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 0 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_303, dGammaKerr_3303, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3310 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 0 (Function.update x 3 u)) (dGammaKerr M a 3 3 1 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 1 0 (Function.update x 3 u) = GammaKerrpt M a 3 1 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_310, dGammaKerr_3310, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3311 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 1 (Function.update x 3 u)) (dGammaKerr M a 3 3 1 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 1 1 (Function.update x 3 u) = GammaKerrpt M a 3 1 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_311, dGammaKerr_3311, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3312 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 2 (Function.update x 3 u)) (dGammaKerr M a 3 3 1 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 1 2 (Function.update x 3 u) = GammaKerrpt M a 3 1 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_312, dGammaKerr_3312, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3313 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 1 3 (Function.update x 3 u)) (dGammaKerr M a 3 3 1 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 1 3 (Function.update x 3 u) = GammaKerrpt M a 3 1 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 1 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_313, dGammaKerr_3313, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3320 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 0 (Function.update x 3 u)) (dGammaKerr M a 3 3 2 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 2 0 (Function.update x 3 u) = GammaKerrpt M a 3 2 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_320, dGammaKerr_3320, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3321 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 1 (Function.update x 3 u)) (dGammaKerr M a 3 3 2 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 2 1 (Function.update x 3 u) = GammaKerrpt M a 3 2 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_321, dGammaKerr_3321, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3322 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 2 (Function.update x 3 u)) (dGammaKerr M a 3 3 2 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 2 2 (Function.update x 3 u) = GammaKerrpt M a 3 2 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_322, dGammaKerr_3322, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3323 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 2 3 (Function.update x 3 u)) (dGammaKerr M a 3 3 2 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 2 3 (Function.update x 3 u) = GammaKerrpt M a 3 2 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 2 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_323, dGammaKerr_3323, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3330 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 0 (Function.update x 3 u)) (dGammaKerr M a 3 3 3 0 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 3 0 (Function.update x 3 u) = GammaKerrpt M a 3 3 0 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 0))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_330, dGammaKerr_3330, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3331 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 1 (Function.update x 3 u)) (dGammaKerr M a 3 3 3 1 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 3 1 (Function.update x 3 u) = GammaKerrpt M a 3 3 1 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 1))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_331, dGammaKerr_3331, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3332 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 2 (Function.update x 3 u)) (dGammaKerr M a 3 3 3 2 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 3 2 (Function.update x 3 u) = GammaKerrpt M a 3 3 2 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 2))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_332, dGammaKerr_3332, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

theorem hdchrKerr_3333 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) 3 3 3 (Function.update x 3 u)) (dGammaKerr M a 3 3 3 3 (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x 3) := by
  have hev : ∀ᶠ u in 𝓝 (x 3), christoffel (gKerr M a) (giKerr M a) 3 3 3 (Function.update x 3 u) = GammaKerrpt M a 3 3 3 (Function.update x 3 u) :=
    (tendsto_update x 3).eventually ((reg_eventually_Kerr M a x hx).mono (fun y hy => chrKerr_all M a y hy 3 3 3))
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [GammaKerrpt, GammaKerr_333, dGammaKerr_3333, Function.update_self, Function.update_of_ne (show (0:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (1:Fin 4) ≠ 3 by decide), Function.update_of_ne (show (2:Fin 4) ≠ 3 by decide)]
  exact hasDerivAt_const _ _

end KerrBL

/- Every coordinate slice of every generic Christoffel symbol is differentiable on the regular
domain, with the closed-form derivative. -/
theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ l i j k : Fin 4, HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) i j k (Function.update x l u)) (dGammaKerr M a l i j k (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x l) := by
  intro l i j k
  fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k
  exacts [hdchrKerr_0000 M a x hx, hdchrKerr_0001 M a x hx, hdchrKerr_0002 M a x hx, hdchrKerr_0003 M a x hx, hdchrKerr_0010 M a x hx, hdchrKerr_0011 M a x hx, hdchrKerr_0012 M a x hx, hdchrKerr_0013 M a x hx, hdchrKerr_0020 M a x hx, hdchrKerr_0021 M a x hx, hdchrKerr_0022 M a x hx, hdchrKerr_0023 M a x hx, hdchrKerr_0030 M a x hx, hdchrKerr_0031 M a x hx, hdchrKerr_0032 M a x hx, hdchrKerr_0033 M a x hx, hdchrKerr_0100 M a x hx, hdchrKerr_0101 M a x hx, hdchrKerr_0102 M a x hx, hdchrKerr_0103 M a x hx, hdchrKerr_0110 M a x hx, hdchrKerr_0111 M a x hx, hdchrKerr_0112 M a x hx, hdchrKerr_0113 M a x hx, hdchrKerr_0120 M a x hx, hdchrKerr_0121 M a x hx, hdchrKerr_0122 M a x hx, hdchrKerr_0123 M a x hx, hdchrKerr_0130 M a x hx, hdchrKerr_0131 M a x hx, hdchrKerr_0132 M a x hx, hdchrKerr_0133 M a x hx, hdchrKerr_0200 M a x hx, hdchrKerr_0201 M a x hx, hdchrKerr_0202 M a x hx, hdchrKerr_0203 M a x hx, hdchrKerr_0210 M a x hx, hdchrKerr_0211 M a x hx, hdchrKerr_0212 M a x hx, hdchrKerr_0213 M a x hx, hdchrKerr_0220 M a x hx, hdchrKerr_0221 M a x hx, hdchrKerr_0222 M a x hx, hdchrKerr_0223 M a x hx, hdchrKerr_0230 M a x hx, hdchrKerr_0231 M a x hx, hdchrKerr_0232 M a x hx, hdchrKerr_0233 M a x hx, hdchrKerr_0300 M a x hx, hdchrKerr_0301 M a x hx, hdchrKerr_0302 M a x hx, hdchrKerr_0303 M a x hx, hdchrKerr_0310 M a x hx, hdchrKerr_0311 M a x hx, hdchrKerr_0312 M a x hx, hdchrKerr_0313 M a x hx, hdchrKerr_0320 M a x hx, hdchrKerr_0321 M a x hx, hdchrKerr_0322 M a x hx, hdchrKerr_0323 M a x hx, hdchrKerr_0330 M a x hx, hdchrKerr_0331 M a x hx, hdchrKerr_0332 M a x hx, hdchrKerr_0333 M a x hx, hdchrKerr_1000 M a x hx, hdchrKerr_1001 M a x hx, hdchrKerr_1002 M a x hx, hdchrKerr_1003 M a x hx, hdchrKerr_1010 M a x hx, hdchrKerr_1011 M a x hx, hdchrKerr_1012 M a x hx, hdchrKerr_1013 M a x hx, hdchrKerr_1020 M a x hx, hdchrKerr_1021 M a x hx, hdchrKerr_1022 M a x hx, hdchrKerr_1023 M a x hx, hdchrKerr_1030 M a x hx, hdchrKerr_1031 M a x hx, hdchrKerr_1032 M a x hx, hdchrKerr_1033 M a x hx, hdchrKerr_1100 M a x hx, hdchrKerr_1101 M a x hx, hdchrKerr_1102 M a x hx, hdchrKerr_1103 M a x hx, hdchrKerr_1110 M a x hx, hdchrKerr_1111 M a x hx, hdchrKerr_1112 M a x hx, hdchrKerr_1113 M a x hx, hdchrKerr_1120 M a x hx, hdchrKerr_1121 M a x hx, hdchrKerr_1122 M a x hx, hdchrKerr_1123 M a x hx, hdchrKerr_1130 M a x hx, hdchrKerr_1131 M a x hx, hdchrKerr_1132 M a x hx, hdchrKerr_1133 M a x hx, hdchrKerr_1200 M a x hx, hdchrKerr_1201 M a x hx, hdchrKerr_1202 M a x hx, hdchrKerr_1203 M a x hx, hdchrKerr_1210 M a x hx, hdchrKerr_1211 M a x hx, hdchrKerr_1212 M a x hx, hdchrKerr_1213 M a x hx, hdchrKerr_1220 M a x hx, hdchrKerr_1221 M a x hx, hdchrKerr_1222 M a x hx, hdchrKerr_1223 M a x hx, hdchrKerr_1230 M a x hx, hdchrKerr_1231 M a x hx, hdchrKerr_1232 M a x hx, hdchrKerr_1233 M a x hx, hdchrKerr_1300 M a x hx, hdchrKerr_1301 M a x hx, hdchrKerr_1302 M a x hx, hdchrKerr_1303 M a x hx, hdchrKerr_1310 M a x hx, hdchrKerr_1311 M a x hx, hdchrKerr_1312 M a x hx, hdchrKerr_1313 M a x hx, hdchrKerr_1320 M a x hx, hdchrKerr_1321 M a x hx, hdchrKerr_1322 M a x hx, hdchrKerr_1323 M a x hx, hdchrKerr_1330 M a x hx, hdchrKerr_1331 M a x hx, hdchrKerr_1332 M a x hx, hdchrKerr_1333 M a x hx, hdchrKerr_2000 M a x hx, hdchrKerr_2001 M a x hx, hdchrKerr_2002 M a x hx, hdchrKerr_2003 M a x hx, hdchrKerr_2010 M a x hx, hdchrKerr_2011 M a x hx, hdchrKerr_2012 M a x hx, hdchrKerr_2013 M a x hx, hdchrKerr_2020 M a x hx, hdchrKerr_2021 M a x hx, hdchrKerr_2022 M a x hx, hdchrKerr_2023 M a x hx, hdchrKerr_2030 M a x hx, hdchrKerr_2031 M a x hx, hdchrKerr_2032 M a x hx, hdchrKerr_2033 M a x hx, hdchrKerr_2100 M a x hx, hdchrKerr_2101 M a x hx, hdchrKerr_2102 M a x hx, hdchrKerr_2103 M a x hx, hdchrKerr_2110 M a x hx, hdchrKerr_2111 M a x hx, hdchrKerr_2112 M a x hx, hdchrKerr_2113 M a x hx, hdchrKerr_2120 M a x hx, hdchrKerr_2121 M a x hx, hdchrKerr_2122 M a x hx, hdchrKerr_2123 M a x hx, hdchrKerr_2130 M a x hx, hdchrKerr_2131 M a x hx, hdchrKerr_2132 M a x hx, hdchrKerr_2133 M a x hx, hdchrKerr_2200 M a x hx, hdchrKerr_2201 M a x hx, hdchrKerr_2202 M a x hx, hdchrKerr_2203 M a x hx, hdchrKerr_2210 M a x hx, hdchrKerr_2211 M a x hx, hdchrKerr_2212 M a x hx, hdchrKerr_2213 M a x hx, hdchrKerr_2220 M a x hx, hdchrKerr_2221 M a x hx, hdchrKerr_2222 M a x hx, hdchrKerr_2223 M a x hx, hdchrKerr_2230 M a x hx, hdchrKerr_2231 M a x hx, hdchrKerr_2232 M a x hx, hdchrKerr_2233 M a x hx, hdchrKerr_2300 M a x hx, hdchrKerr_2301 M a x hx, hdchrKerr_2302 M a x hx, hdchrKerr_2303 M a x hx, hdchrKerr_2310 M a x hx, hdchrKerr_2311 M a x hx, hdchrKerr_2312 M a x hx, hdchrKerr_2313 M a x hx, hdchrKerr_2320 M a x hx, hdchrKerr_2321 M a x hx, hdchrKerr_2322 M a x hx, hdchrKerr_2323 M a x hx, hdchrKerr_2330 M a x hx, hdchrKerr_2331 M a x hx, hdchrKerr_2332 M a x hx, hdchrKerr_2333 M a x hx, hdchrKerr_3000 M a x hx, hdchrKerr_3001 M a x hx, hdchrKerr_3002 M a x hx, hdchrKerr_3003 M a x hx, hdchrKerr_3010 M a x hx, hdchrKerr_3011 M a x hx, hdchrKerr_3012 M a x hx, hdchrKerr_3013 M a x hx, hdchrKerr_3020 M a x hx, hdchrKerr_3021 M a x hx, hdchrKerr_3022 M a x hx, hdchrKerr_3023 M a x hx, hdchrKerr_3030 M a x hx, hdchrKerr_3031 M a x hx, hdchrKerr_3032 M a x hx, hdchrKerr_3033 M a x hx, hdchrKerr_3100 M a x hx, hdchrKerr_3101 M a x hx, hdchrKerr_3102 M a x hx, hdchrKerr_3103 M a x hx, hdchrKerr_3110 M a x hx, hdchrKerr_3111 M a x hx, hdchrKerr_3112 M a x hx, hdchrKerr_3113 M a x hx, hdchrKerr_3120 M a x hx, hdchrKerr_3121 M a x hx, hdchrKerr_3122 M a x hx, hdchrKerr_3123 M a x hx, hdchrKerr_3130 M a x hx, hdchrKerr_3131 M a x hx, hdchrKerr_3132 M a x hx, hdchrKerr_3133 M a x hx, hdchrKerr_3200 M a x hx, hdchrKerr_3201 M a x hx, hdchrKerr_3202 M a x hx, hdchrKerr_3203 M a x hx, hdchrKerr_3210 M a x hx, hdchrKerr_3211 M a x hx, hdchrKerr_3212 M a x hx, hdchrKerr_3213 M a x hx, hdchrKerr_3220 M a x hx, hdchrKerr_3221 M a x hx, hdchrKerr_3222 M a x hx, hdchrKerr_3223 M a x hx, hdchrKerr_3230 M a x hx, hdchrKerr_3231 M a x hx, hdchrKerr_3232 M a x hx, hdchrKerr_3233 M a x hx, hdchrKerr_3300 M a x hx, hdchrKerr_3301 M a x hx, hdchrKerr_3302 M a x hx, hdchrKerr_3303 M a x hx, hdchrKerr_3310 M a x hx, hdchrKerr_3311 M a x hx, hdchrKerr_3312 M a x hx, hdchrKerr_3313 M a x hx, hdchrKerr_3320 M a x hx, hdchrKerr_3321 M a x hx, hdchrKerr_3322 M a x hx, hdchrKerr_3323 M a x hx, hdchrKerr_3330 M a x hx, hdchrKerr_3331 M a x hx, hdchrKerr_3332 M a x hx, hdchrKerr_3333 M a x hx]
