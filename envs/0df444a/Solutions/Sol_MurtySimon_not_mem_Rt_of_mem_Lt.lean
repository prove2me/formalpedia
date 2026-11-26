-- Prove2me | solution 1 for MurtySimon.not_mem_Rt_of_mem_Lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:26.591475+00:00
-- url     : https://prove2.me/submissions/f362b195-3f21-48b6-8e89-64d079b8c936

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components
public import Theorems.Thm_MurtySimon_mem_Rt
public import Theorems.Thm_MurtySimon_mem_Lt
public import Theorems.Thm_MurtySimon_IsCrit_not_mem_edgeSet


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {M : Finset (Sym2 V)} {e : Sym2 V} (h : e ∈ Lt G M) : e ∉ Rt G :=
  fun h' => (mem_Rt.1 h').not_mem_edgeSet (mem_Lt.1 h).1
end MurtySimon
