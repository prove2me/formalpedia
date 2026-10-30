-- Prove2me | solution 1 for JuschenkoMonod.isAmenable_fullGroup_of_isMinimal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:54:31.496096+00:00
-- url     : https://prove2.me/submissions/3025bd39-3e76-444b-afe1-d62096c1ddbb

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_CantorSystems
import Definitions.Def_IntervalExchange
import Definitions.Def_Chou_Classes
import Definitions.Def_JuschenkoMonod
import Theorems.Thm_Garrido_isAmenable_of_directed
import Theorems.Thm_Garrido_isAmenable_of_finite
import Theorems.Thm_JuschenkoMonod_isAmenable_of_isAmenable_stabilizer_symmDiff_natSet
import Theorems.Thm_JuschenkoMonod_isLocallyFinite_stabilizer_of_hasUbiquitousPatternProperty
import Theorems.Thm_JuschenkoMonod_exists_orbitIndexing_and_injective_and_hasUbiquitousPatternProperty_range_of_isMinimal

open scoped Pointwise ENNReal

namespace JuschenkoMonod

lemma amenable_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Garrido.IsAmenable G) : Garrido.IsAmenable H := by
  obtain ⟨m, hm, h1, hinv⟩ := h
  refine ⟨fun s => m (e ⁻¹' s), ⟨by simpa using hm.1, fun s t hst => ?_⟩, by simpa using h1, ?_⟩
  · have := hm.2 (e ⁻¹' s) (e ⁻¹' t) (hst.preimage _)
    simpa [Set.preimage_union] using this
  · intro g s
    have := hinv (e.symm g) (e ⁻¹' s)
    convert this using 2
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem]

lemma amenable_of_isLocallyFinite {H : Type*} [Group H] (h : Chou.IsLocallyFinite H) :
    Garrido.IsAmenable H := by
  classical
  refine Garrido.isAmenable_of_directed (fun s : Finset H => Subgroup.closure (s : Set H)) ?_ ?_ ?_
  · intro s t
    refine ⟨s ∪ t, Subgroup.closure_mono ?_, Subgroup.closure_mono ?_⟩ <;> simp
  · refine top_unique fun x _ => ?_
    exact Subgroup.mem_iSup_of_mem ({x} : Finset H) (Subgroup.subset_closure (by simp))
  · intro s
    haveI := h (s : Set H) s.finite_toSet
    exact Garrido.isAmenable_of_finite _

theorem goal_aux (C : Type*) [TopologicalSpace C]
    (hC : CantorSystems.IsCantorSpace C) (T : C ≃ₜ C) (hT : IsMinimal T) :
    Garrido.IsAmenable (fullGroup T) := by
  obtain ⟨p⟩ := hC.1
  have key := exists_orbitIndexing_and_injective_and_hasUbiquitousPatternProperty_range_of_isMinimal
    C hC T hT p
  obtain ⟨φ, hφ⟩ := key.1
  obtain ⟨hinj, hU⟩ := key.2 φ hφ
  set G : Subgroup (Equiv.Perm ℤ) := φ.range.map (IntervalExchange.wobbling ℤ).subtype with hG
  have hGle : G ≤ IntervalExchange.wobbling ℤ := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hamen : Garrido.IsAmenable G := by
    refine isAmenable_of_isAmenable_stabilizer_symmDiff_natSet G hGle fun E => ?_
    exact amenable_of_isLocallyFinite
      (isLocallyFinite_stabilizer_of_hasUbiquitousPatternProperty G hGle hU E)
  have e1 : fullGroup T ≃* φ.range := MonoidHom.ofInjective hinj
  have e2 : φ.range ≃* G :=
    Subgroup.equivMapOfInjective _ _ (IntervalExchange.wobbling ℤ).subtype_injective
  exact amenable_of_mulEquiv (e1.trans e2).symm hamen

end JuschenkoMonod

theorem solution : type_of% @JuschenkoMonod.goal_aux := @JuschenkoMonod.goal_aux
