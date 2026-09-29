-- Prove2me | solution 1 for Homeomorph.exists_sheet_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/11609ce0-8552-5259-948a-53799abce0e2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Homeomorph_exists_sheet_decomposition

set_option autoImplicit false

namespace SheetDecomposition

open Topology

variable {E X I : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace I]
variable [DiscreteTopology I] {f : E → X} {U : Set X} {Ω : Set E}

open scoped Classical in

noncomputable def subtypeSheet (H : Ω ≃ₜ U × I)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) (i : I) [Nonempty Ω] :
    OpenPartialHomeomorph Ω X where
  toFun := fun e => ((H e).1 : X)
  invFun := fun z => if hz : z ∈ V then H.symm (⟨z, hVU hz⟩, i) else Classical.arbitrary _
  source := ⇑H ⁻¹' ((Subtype.val ⁻¹' V) ×ˢ ({i} : Set I))
  target := V
  map_source' := by
    rintro e ⟨h1, -⟩
    exact h1
  map_target' := by
    intro z hz
    simp only [Set.mem_preimage, dif_pos hz, Homeomorph.apply_symm_apply]
    exact Set.mem_prod.mpr ⟨hz, rfl⟩
  left_inv' := by
    rintro e ⟨h1, h2⟩
    have hz : ((H e).1 : X) ∈ V := h1
    rw [dif_pos hz]
    have hpair : (⟨((H e).1 : X), hVU hz⟩, i) = H e := by
      refine Prod.ext ?_ ?_
      · exact Subtype.ext rfl
      · exact (Set.mem_singleton_iff.mp h2).symm
    rw [hpair, Homeomorph.symm_apply_apply]
  right_inv' := by
    intro z hz
    rw [dif_pos hz, Homeomorph.apply_symm_apply]
  open_source := by
    refine H.continuous.isOpen_preimage _ ?_
    exact IsOpen.prod (hV.preimage continuous_subtype_val) (isOpen_discrete _)
  open_target := hV
  continuousOn_toFun :=
    ((continuous_subtype_val.comp (continuous_fst.comp H.continuous))).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : V.domRestrict (fun z => if hz : z ∈ V then H.symm (⟨z, hVU hz⟩, i)
        else Classical.arbitrary _) = fun zv : V => H.symm (⟨zv.1, hVU zv.2⟩, i) := by
      funext zv
      exact dif_pos zv.2
    rw [hres]
    exact H.symm.continuous.comp
      (Continuous.prodMk (Continuous.subtype_mk continuous_subtype_val _) continuous_const)

noncomputable def sheet (hpre : IsOpen Ω) (H : Ω ≃ₜ U × I)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) (i : I) [Nonempty Ω] :
    OpenPartialHomeomorph E X :=
  (hpre.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val).symm.trans
    (subtypeSheet H hV hVU i)

theorem sheet_decomposition (hpre : IsOpen Ω) (H : Ω ≃ₜ U × I)
    (hH : ∀ x, ((H x).1 : X) = f x)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) [Nonempty Ω] :
    ∃ ζ : I → OpenPartialHomeomorph E X,
      (∀ i, (ζ i).target = V) ∧
      (∀ i, ∀ e ∈ (ζ i).source, e ∈ Ω ∧ ζ i e = f e) ∧
      (∀ i, ∀ z ∈ V, (ζ i).symm z ∈ Ω ∧ f ((ζ i).symm z) = z) ∧
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
      (∀ e : E, e ∈ Ω → f e ∈ V → ∃ i, e ∈ (ζ i).source) := by
  classical
  have hval_inv : ∀ ê : Ω,
      (hpre.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val).symm (ê : E) = ê :=
    fun ê => hpre.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
  refine ⟨fun i => sheet hpre H hV hVU i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [sheet, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.preimage_univ,
      Set.inter_univ]
    rfl
  · intro i e he
    unfold sheet at he
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at he
    obtain ⟨he1, he2⟩ := he
    obtain ⟨ê, rfl⟩ := he1
    refine ⟨ê.2, ?_⟩
    show (sheet hpre H hV hVU i) (ê : E) = f (ê : E)
    unfold sheet
    rw [OpenPartialHomeomorph.trans_apply, hval_inv ê]
    exact hH ê
  · intro i z hz
    have hss : ((sheet hpre H hV hVU i).symm z : E)
        = ((H.symm (⟨z, hVU hz⟩, i) : Ω) : E) := by
      show ((if hz' : z ∈ V then H.symm (⟨z, hVU hz'⟩, i)
          else Classical.arbitrary _ : Ω) : E) = _
      rw [dif_pos hz]
    constructor
    · rw [hss]
      exact (H.symm (⟨z, hVU hz⟩, i)).2
    · rw [hss, ← hH (H.symm (⟨z, hVU hz⟩, i)), Homeomorph.apply_symm_apply]
  · intro i j hij
    rw [Set.disjoint_left]
    intro e hei hej
    unfold sheet at hei hej
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hei hej
    obtain ⟨he1, he2⟩ := hei
    obtain ⟨-, he2'⟩ := hej
    obtain ⟨ê, rfl⟩ := he1
    rw [Set.mem_preimage, hval_inv ê] at he2 he2'
    have hi : (H ê).2 = i := (Set.mem_prod.mp he2).2
    have hj : (H ê).2 = j := (Set.mem_prod.mp he2').2
    exact hij (hi ▸ hj)
  · intro e he hfe
    refine ⟨(H ⟨e, he⟩).2, ?_⟩
    unfold sheet
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    constructor
    · exact ⟨⟨e, he⟩, rfl⟩
    · rw [Set.mem_preimage, hval_inv ⟨e, he⟩]
      refine Set.mem_prod.mpr ⟨?_, rfl⟩
      show ((H ⟨e, he⟩).1 : X) ∈ V
      rw [hH]
      exact hfe

end SheetDecomposition

theorem solution {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] [DiscreteTopology I] {f : E → X} {U : Set X}
    {Ω : Set E} (hpre : IsOpen Ω) (H : Ω ≃ₜ U × I) (hH : ∀ x, ((H x).1 : X) = f x)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) [Nonempty Ω] :
    ∃ ζ : I → OpenPartialHomeomorph E X,
      (∀ i, (ζ i).target = V) ∧
      (∀ i, ∀ e ∈ (ζ i).source, e ∈ Ω ∧ ζ i e = f e) ∧
      (∀ i, ∀ z ∈ V, (ζ i).symm z ∈ Ω ∧ f ((ζ i).symm z) = z) ∧
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
      (∀ e : E, e ∈ Ω → f e ∈ V → ∃ i, e ∈ (ζ i).source) := by
  exact SheetDecomposition.sheet_decomposition (hpre := hpre) (H := H) (hH := hH) (hV := hV) (hVU := hVU)

end S_Homeomorph_exists_sheet_decomposition
end P2MW
export P2MW.S_Homeomorph_exists_sheet_decomposition (solution)
