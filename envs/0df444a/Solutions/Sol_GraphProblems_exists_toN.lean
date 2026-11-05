-- Prove2me | solution 1 for GraphProblems.exists_toN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:55:32.544906+00:00
-- url     : https://prove2.me/submissions/dbf5f8d4-8afd-49aa-8c78-b61631037dfd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_Engine

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat
namespace GraphProblems
theorem _root_.solution {N : ℕ} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < N) : ∃ φ : Sat3.CNF N, Decode.toN φ = ψ := by
  refine ⟨ψ.pmap (fun C hC => C.pmap (fun l hl => ((⟨l.1, hl⟩ : Fin N), l.2)) hC) h, ?_⟩
  unfold Decode.toN
  rw [List.map_pmap]
  conv_rhs => rw [← List.map_id ψ]
  rw [← List.pmap_eq_map (p := fun C => ∀ l ∈ C, l.1 < N) (H := h)]
  refine List.pmap_congr_left ψ fun C _ hC _ => ?_
  rw [List.map_pmap]
  conv_rhs => rw [id, ← List.map_id C]
  rw [← List.pmap_eq_map (p := fun l : ℕ × Bool => l.1 < N) (H := hC)]
  exact List.pmap_congr_left C fun l _ _ _ => rfl
end GraphProblems
