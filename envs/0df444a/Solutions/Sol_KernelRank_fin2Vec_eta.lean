-- Prove2me | solution 1 for KernelRank.fin2Vec_eta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:54:58.024015+00:00
-- url     : https://prove2.me/submissions/c3f65f29-d6db-4776-a787-008adba48b93

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
namespace KernelRank
theorem _root_.solution (z : Fin 2 → α) : fin2Vec (z 0) (z 1) = z := by
  ext i
  match i with
  | 0 => rfl
  | 1 => rfl
end KernelRank
