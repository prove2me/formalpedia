-- Prove2me | solution 1 for GraphProblems.stCertRead
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:21:21.319276+00:00
-- url     : https://prove2.me/submissions/d2e650d4-978e-41bd-b7a5-9908312591ef

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

attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.length

namespace GraphProblems

@[fun_prop] theorem ones_polyT_aux {x : α → List Bool} (hx : PolyT x) :
    PolyT fun a => ones (x a) := by
  unfold ones
  fun_prop

@[fun_prop] theorem rest_polyT_aux {x : α → List Bool} (hx : PolyT x) :
    PolyT fun a => rest (x a) := by
  unfold rest
  fun_prop

theorem ones_unary_aux {x : α → List Bool} (hx : PolyT x) :
    Unary fun a => ones (x a) := by
  unfold ones
  exact Unary.of_length (by fun_prop)

end GraphProblems

theorem solution : StCertRead := by
  have h1 : PolyT fun x : List Bool => List.replicate (ones x) () :=
    GraphProblems.ones_unary_aux PolyT.id'
  constructor
  · unfold GraphProblems.read1
    fun_prop
  · unfold GraphProblems.read2
    fun_prop
