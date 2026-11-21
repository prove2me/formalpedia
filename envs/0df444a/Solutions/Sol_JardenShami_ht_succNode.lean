-- Prove2me | solution 1 for JardenShami.ht_succNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:38.521234+00:00
-- url     : https://prove2.me/submissions/dc86aa4e-1615-4c3a-8b6c-cbf1347d7fad

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Tree_ht_le_ht_of_le
import Theorems.Thm_JardenShami_Iio_succNode

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {t : T} (ht' : ¬ IsLeaf t) : ht (succNode ht') = Order.succ (ht t) := by
  have hm : t < succNode ht' := WellFounded.min_mem _ {x | t < x} _
  refine le_antisymm ?_ (Order.succ_le_of_lt (ht_lt_ht hm))
  by_contra hc
  obtain ⟨s, hs, hs'⟩ := exists_lt_ht_eq (lt_of_not_ge hc)
  have hst : s ∈ Set.Iio (succNode ht') := hs
  rw [Iio_succNode] at hst
  have := ht_le_ht_of_le hst
  rw [hs'] at this
  exact (Order.lt_succ_of_not_isMax (not_isMax _)).not_ge this
end JardenShami
