-- Prove2me | solution 1 for Given.stLevelPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:06.573847+00:00
-- url     : https://prove2.me/submissions/8ead693d-7620-468f-9573-afec3b1bbd59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
import Theorems.Thm_Given_networkOn_steps
import Theorems.Thm_Eight_Level_Cert_numPat8_polyT
import Theorems.Thm_Eight_Level_Cert_useRowP_polyT
import Theorems.Thm_Eight_ViaGrouping_stKeeps
import Theorems.Thm_Eight_stKeeps
import Theorems.Thm_Exits_stKeeps
import Theorems.Thm_Given_gridProcs_poly
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Printed_lamOf_unary
import Theorems.Thm_Printed_levelDiv_poly
import Theorems.Thm_Printed_stGroupingPoly
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
namespace Given
theorem _root_.solution : StLevelPoly := by
  intro K g M hM
  have hl := Printed.lamOf_unary
  have hN := stGroupingPoly K g M hM
  obtain ⟨i1⟩ := networkOn_steps g _ _ hN (gridProcs_poly g false)
  obtain ⟨i2⟩ := networkOn_steps g _ _ hN (gridProcs_poly g true)
  have i3 := IsPolyQ.ite (Eight.Level.Cert.useRowP_polyT (lam := fun c : List Unit × List Unit => c.1.length) Eight.stKeeps g hl) (networkOn g (groupingMachine K g M) (gridProcs g false)) (networkOn g (groupingMachine K g M) (gridProcs g true))
  have i4 := IsPolyQ.sumRange (QueryMachine.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOn g (groupingMachine K g M) (gridProcs g false)) (networkOn g (groupingMachine K g M) (gridProcs g true))) (Eight.Level.Cert.numPat8_polyT (lam := fun c : List Unit × List Unit => c.1.length) g hl)
  obtain ⟨i5⟩ := levelDiv_poly g
  exact ⟨IsPolyQ.bind _ _⟩
end Given
