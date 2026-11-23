-- Prove2me | solution 1 for KernelRank.row_mem_rowSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:51:21.940236+00:00
-- url     : https://prove2.me/submissions/f1a7efce-bd65-42a8-8d98-97d08687a081

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]
namespace KernelRank
theorem _root_.solution (K : (Fin 2 → α) → 𝕜) (y : α) :
    (fun x => K (fin2Vec x y)) ∈ rowSpan K :=
  Submodule.subset_span ⟨y, rfl⟩
end KernelRank
