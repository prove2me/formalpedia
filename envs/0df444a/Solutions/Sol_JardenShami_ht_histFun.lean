-- Prove2me | solution 1 for JardenShami.ht_histFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:16.483766+00:00
-- url     : https://prove2.me/submissions/d2463ff1-da20-441b-b080-38869ebd6396

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Tree_exists_Iio_eq_of_ssubset
import Theorems.Thm_JardenShami_histFun_eq_iff
import Theorems.Thm_JardenShami_Iio_ssubset_Iio_of_lt

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (t : T) :
    ht (⟨histFun t, t, rfl⟩ : HistoryTree T) = Ordinal.lift.{w + 1} (ht t) := by
  let g : HistoryTree T := ⟨histFun t, t, rfl⟩
  have hsurj : ∀ y : Set.Iio g, ∃ u : Set.Iio t, (y : HistoryTree T).1 = histFun u.1 := by
    rintro ⟨⟨_, s, rfl⟩, hs⟩
    obtain ⟨u, hu, hsu⟩ := exists_Iio_eq_of_ssubset (histFun_ssubset_iff.1 hs)
    exact ⟨⟨u, hu⟩, histFun_eq_iff.2 hsu⟩
  let f : (fun x y : Set.Iio t => (x : T) < y) ↪r
      (fun x y : Set.Iio g => (x : HistoryTree T) < y) :=
    RelEmbedding.ofMonotone
      (fun u => ⟨⟨histFun u.1, u.1, rfl⟩, show histFun u.1 ⊂ histFun t from
        histFun_ssubset_iff.2 (Iio_ssubset_Iio_of_lt u.2)⟩)
      (fun a b h => show histFun a.1 ⊂ histFun b.1 from
        histFun_ssubset_iff.2 (Iio_ssubset_Iio_of_lt h))
  have e := RelIso.ofSurjective f (by
    intro y
    obtain ⟨u, hu⟩ := hsurj y
    exact ⟨u, Subtype.ext (Subtype.ext hu.symm)⟩)
  have := e.ordinal_lift_type_eq
  unfold ht
  rw [this, Ordinal.lift_id'.{w, w + 1}]
end JardenShami
