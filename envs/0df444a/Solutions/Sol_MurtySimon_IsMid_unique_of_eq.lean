-- Prove2me | solution 1 for MurtySimon.IsMid.unique_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:43.958193+00:00
-- url     : https://prove2.me/submissions/1e384129-a02a-4fa2-acc3-11b15fd48da8

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_IsMid_unique

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace MurtySimon
namespace IsMid
theorem _root_.solution {x y x' y' u u' : V} (hf : s(x, y) = s(x', y')) (h : IsMid G x y u)
    (h' : IsMid G x' y' u') : u' = u := by
  rcases Sym2.eq_iff.1 hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.unique h'
  · exact h.symm.unique h'
end IsMid
end MurtySimon
