-- Prove2me | solution 1 for GraphProblems.stCertForm
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:22:55.623439+00:00
-- url     : https://prove2.me/submissions/ead9d678-5db4-464f-9f6b-f34c6d924120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_CountKSat_Poly
import Definitions.Def_GraphProblems_Cert
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat
variable {α : Type} [Enc α]

attribute [local fun_prop] Groundwork.Decode.clauseDec_polyT
attribute [local fun_prop] Groundwork.Decode.slotDec_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.decide_mem
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.elem
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.product
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sprod
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] P2M_Groundwork_PolyT_chunks__bc5b8682856d
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45

namespace GraphProblems

@[fun_prop] theorem ones_polyT {x : α → List Bool} (hx : PolyT x) :
    PolyT fun a => ones (x a) := by
  unfold ones
  fun_prop

@[fun_prop] theorem rest_polyT {x : α → List Bool} (hx : PolyT x) :
    PolyT fun a => rest (x a) := by
  unfold rest
  fun_prop

@[fun_prop] theorem adjB_polyT {n u v : α → ℕ} {m : α → List Bool}
    (hn : PolyT n) (hm : PolyT m) (hu : PolyT u) (hv : PolyT v) :
    PolyT fun a => adjB (n a) (m a) (u a) (v a) := by
  unfold adjB
  fun_prop

theorem pairs_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun a => pairs (n a) := by
  have hr : PolyT fun a => List.range (n a) := PolyT.range hn
  unfold pairs
  fun_prop

end GraphProblems

theorem solution : StCertForm := by
  have hu : Unary fun a : List Unit × List Bool => a.1.length := Unary.of_length (by fun_prop)
  have hr : PolyT fun a : List Unit × List Bool => List.range a.1.length := PolyT.range hu
  have hp : PolyT fun a : List Unit × List Bool => pairs a.1.length := pairs_polyT hu
  refine ⟨?_, ?_, ?_, fun k => ?_⟩
  · unfold indepF
    fun_prop
  · unfold cliqueF
    fun_prop
  · unfold coverF
    fun_prop
  · unfold colorF
    fun_prop
