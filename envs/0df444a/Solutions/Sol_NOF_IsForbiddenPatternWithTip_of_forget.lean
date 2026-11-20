-- Prove2me | solution 1 for NOF.IsForbiddenPatternWithTip.of_forget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:13:36.389409+00:00
-- url     : https://prove2.me/submissions/b85f5d66-1e7b-40e0-964b-2db2ab703e46

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Definitions.Def_ChandraFurstLipton_MultidimCorners

set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {a : ι → ι → G} {v : ι → G}
namespace NOF
namespace IsForbiddenPatternWithTip
theorem _root_.solution (h : ∀ i, forget i v = forget i (a i)) :
    IsForbiddenPatternWithTip a v := isForbiddenPatternWithTip_iff_forget.mpr h
end IsForbiddenPatternWithTip
end NOF
