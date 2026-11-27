-- Prove2me | solution 1 for MatchingPolytope.Multi.gcut_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:55.919859+00:00
-- url     : https://prove2.me/submissions/9264b7af-4e81-46a0-8839-4d10f6af2e8e

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq E] (e : E) (T : Finset V) :
    gcut ends (F.erase e) T = (gcut ends F T).erase e := by
  classical
  ext e'
  simp only [gcut, Finset.mem_filter, Finset.mem_erase]
  tauto
end MatchingPolytope.Multi
