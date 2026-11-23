-- Prove2me | solution 1 for KernelRank.fin2Vec_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:49:16.353812+00:00
-- url     : https://prove2.me/submissions/be24b17d-ce9a-4cd6-ac35-8246d5ab32ab

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
namespace KernelRank
theorem _root_.solution (x y : α) : fin2Vec x y 0 = x := rfl
end KernelRank
