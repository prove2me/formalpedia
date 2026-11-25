-- Prove2me | solution 1 for HatAffineOffsets.typeII_offsetCoverable_iff_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:17:58.144581+00:00
-- url     : https://prove2.me/submissions/2bf6d334-fbcb-4dcf-8181-549cd22b097d

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_typeIID_eq_iff
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (hm : 1 <= m) (hq : 4 <= Fintype.card K)
    (u v : Fin m)
    (alpha c b : Fin (Fintype.card K - 1) -> K)
    (F : (Fin m -> K) -> Fin (Fintype.card K - 1) -> K)
    (huv : u ≠ v)
    (halpha : forall i, alpha i ≠ 0)
    (hrealizeII : forall y i,
      F y i = alpha i * (y u - c i * y v) + b i)
    (x : Fin (Fintype.card K - 1) -> K) :
    OffsetCoverable F x ↔ TypeIICross c (typeIID alpha b x) := by
  classical
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g u, g v, ?_⟩
    intro U V hactive
    by_cases hU : U = g u
    · exact Or.inl hU
    by_cases hV : V = g v
    · exact Or.inr hV
    exfalso
    let y : Fin m -> K := fun j =>
      if j = u then U else if j = v then V else g j + 1
    have hybad : y ∈ HatAffineGeneral.BadSet F x := by
      intro i hFi
      have hd : typeIID alpha b x i = y u - c i * y v := by
        apply (typeIID_eq_iff (halpha i)).mpr
        exact (hrealizeII y i).symm.trans hFi
      apply hactive i
      simpa [y, huv, Ne.symm huv] using hd.symm
    obtain ⟨j, hj⟩ := hg y hybad
    by_cases hju : j = u
    · subst j
      exact hU (by simpa [y] using hj)
    by_cases hjv : j = v
    · subst j
      exact hV (by simpa [y, huv, Ne.symm huv] using hj)
    have hadd : g j + 1 = g j := by simpa [y, hju, hjv] using hj
    have hone : (1 : K) = 0 := by
      calc
        1 = (g j + 1) - g j := by ring
        _ = 0 := by rw [hadd]; exact sub_self _
    exact one_ne_zero hone
  · rintro ⟨a, beta, hcross⟩
    let g : Fin m -> K := fun j =>
      if j = u then a else if j = v then beta else 0
    refine ⟨g, ?_⟩
    intro y hybad
    have hactive : forall i, y u - c i * y v ≠ typeIID alpha b x i := by
      intro i hi
      apply hybad i
      rw [hrealizeII y i]
      exact (typeIID_eq_iff (halpha i)).mp hi.symm
    rcases hcross (y u) (y v) hactive with hu | hv
    · exact ⟨u, by simp [g, hu]⟩
    · exact ⟨v, by simp [g, hv, huv, Ne.symm huv]⟩
end HatAffineOffsets
