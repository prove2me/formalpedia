-- Prove2me | solution 1 for KernelRank.fin2Vec_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:49:17.093802+00:00
-- url     : https://prove2.me/submissions/11632cb1-ce13-4d96-8789-6b7c4c3f3314

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
namespace KernelRank
theorem _root_.solution (x y : α) : fin2Vec x y 1 = y := rfl
end KernelRank
