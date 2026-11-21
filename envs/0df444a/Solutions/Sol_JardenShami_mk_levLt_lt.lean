-- Prove2me | solution 1 for JardenShami.mk_levLt_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:38.651299+00:00
-- url     : https://prove2.me/submissions/2f7a65dc-0500-47bf-bb7e-c7f44dc7080f

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_eq
attribute [local simp] JardenShami.Kappa.coe_mk



set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {κ : Cardinal.{w}} (hκ : κ.IsRegular) (hT : IsKappaTree κ T)
    {α : Ordinal.{w}} (hα : α < κ.ord) : #{s : T | ht s < α} < κ := by
  let ι := {β : Kappa κ // (β : Ordinal.{w}) < α}
  have hsub : {s : T | ht s < α} ⊆ ⋃ β : ι, Lev T (β.1 : Ordinal.{w}) := by
    intro s hs
    refine Set.mem_iUnion.2 ⟨⟨Kappa.mk (ht s) (hs.trans hα), by rw [Kappa.coe_mk]; exact hs⟩, ?_⟩
    exact (Kappa.coe_mk _ _).symm
  refine (Cardinal.mk_le_mk_of_subset hsub).trans_lt
    (Cardinal.mk_iUnion_le_sum_mk.trans_lt (Cardinal.sum_lt_of_isRegular hκ ?_ fun β =>
      hT.2 _ (Kappa.coe_lt_ord β.1)))
  refine (Cardinal.mk_le_of_injective (f := fun β : ι =>
    (⟨β.1, Kappa.coe_lt_coe.1 (by rw [Kappa.coe_mk]; exact β.2)⟩ :
      Set.Iio (Kappa.mk α hα))) ?_).trans_lt ?_
  · intro a b h
    exact Subtype.ext (congrArg (fun z : Set.Iio (Kappa.mk α hα) => (z : Kappa κ)) h)
  · have := Cardinal.mk_Iio_lt (Kappa.mk α hα) (by rw [Kappa.mk_eq, Ordinal.type_toType])
    rwa [Kappa.mk_eq] at this
end JardenShami
