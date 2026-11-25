-- Prove2me | solution 1 for HatAffineOffsets.typeI_offsetCoverable_iff_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:16:41.899018+00:00
-- url     : https://prove2.me/submissions/0a36860d-ad52-4c43-abe7-a1e741af02d2

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI
import Theorems.Thm_HatAffineOffsets_typeIRoot_eq_iff
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (r : Fin m)
    (alpha b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (halpha : forall i, alpha i ≠ 0)
    (hrealizeI : forall y i, F y i = alpha i * y r + b i)
    (x : Fin (Fintype.card K - 1) -> K) :
    OffsetCoverable F x <-> Function.Injective (typeIRoot alpha b x) := by
  classical
  let roots : Fin (Fintype.card K - 1) -> K := typeIRoot alpha b x
  constructor
  · rintro ⟨g, hg⟩
    by_contra hnotinj
    have himage_lt :
        (Finset.univ.image roots).card <
          (Finset.univ : Finset (Fin (Fintype.card K - 1))).card := by
      have hle := Finset.card_image_le (s :=
        (Finset.univ : Finset (Fin (Fintype.card K - 1)))) (f := roots)
      have hne :
          (Finset.univ.image roots).card ≠
            (Finset.univ : Finset (Fin (Fintype.card K - 1))).card := by
        intro heq
        apply hnotinj
        intro i k hik
        exact (Finset.card_image_iff.mp heq)
          (Finset.mem_univ i) (Finset.mem_univ k) hik
      omega
    have hcomp_two :
        2 <= (Finset.univ \ Finset.univ.image roots).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ]
      apply Nat.le_sub_of_add_le
      have himage_lt' :
          (Finset.univ.image roots).card < Fintype.card K - 1 := by
        simpa using himage_lt
      omega
    obtain ⟨z, hzmem, hzgr⟩ :
        exists z, z ∈ (Finset.univ \ Finset.univ.image roots) ∧ z ≠ g r := by
      by_contra hnone
      push_neg at hnone
      have hsub :
          (Finset.univ \ Finset.univ.image roots) ⊆ ({g r} : Finset K) := by
        intro z hz
        simpa [hnone z hz]
      have hcard := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hcard
      omega
    let y : Fin m -> K := fun j => if j = r then z else g j + 1
    have hybad : y ∈ HatAffineGeneral.BadSet F x := by
      intro i hFi
      have hroot : roots i = y r := by
        apply (typeIRoot_eq_iff (halpha i)).mpr
        simpa only [roots, typeIRoot] using
          (hrealizeI y i).symm.trans hFi
      have hznot : z ∉ Finset.univ.image roots :=
        (Finset.mem_sdiff.mp hzmem).2
      apply hznot
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simpa [y] using hroot
    obtain ⟨j, hj⟩ := hg y hybad
    by_cases hjr : j = r
    · subst j
      exact hzgr (by simpa [y] using hj)
    · have hone : (1 : K) = 0 := by
        have hadd : g j + 1 = g j := by simpa [y, hjr] using hj
        linear_combination hadd
      exact one_ne_zero hone
  · intro hinj
    have himage_card :
        (Finset.univ.image roots).card = Fintype.card K - 1 := by
      rw [Finset.card_image_of_injective Finset.univ hinj]
      simp
    have hcomp_card :
        (Finset.univ \ Finset.univ.image roots).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, himage_card]
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcomp_card
    let g : Fin m -> K := fun j => if j = r then a else 0
    refine ⟨g, ?_⟩
    intro y hy
    refine ⟨r, ?_⟩
    have hyrange : y r ∉ Finset.univ.image roots := by
      intro hymem
      obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hymem
      have hFi : F y i = x i := by
        rw [hrealizeI y i]
        exact (typeIRoot_eq_iff (halpha i)).mp hiy
      exact hy i hFi
    have hycomp : y r ∈ Finset.univ \ Finset.univ.image roots :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyrange⟩
    rw [ha] at hycomp
    have hyr : y r = a := by simpa using hycomp
    simp [g, hyr]
end HatAffineOffsets
