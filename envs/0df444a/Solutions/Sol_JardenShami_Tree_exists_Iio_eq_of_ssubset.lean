-- Prove2me | solution 1 for JardenShami.Tree.exists_Iio_eq_of_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:32.968021+00:00
-- url     : https://prove2.me/submissions/33343e25-be3a-4319-9a65-161664ea506c

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami.Tree
theorem _root_.solution {s t : T} (h : Set.Iio s ⊂ Set.Iio t) :
    ∃ u < t, Set.Iio s = Set.Iio u := by
  obtain ⟨u, hut, hu⟩ := exists_lt_ht_eq (ht_lt_ht_of_Iio_ssubset h)
  have hsub : Set.Iio s ⊆ Set.Iio u := by
    intro x hx
    rcases lt_trichotomy_of_lt (h.1 hx) hut with h' | rfl | h'
    · exact h'
    · exact absurd hu (ht_lt_ht hx).ne
    · exact absurd hu (ht_lt_ht (lt_trans h' hx)).ne
  refine ⟨u, hut, hsub.antisymm ?_⟩
  by_contra hc
  exact (ht_lt_ht_of_Iio_ssubset (hsub.ssubset_of_not_subset hc)).ne hu.symm
end JardenShami.Tree
