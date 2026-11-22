-- Prove2me | solution 1 for MasulloGRH.schwartzBruhatAverage_transfer
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T16:14:51.378765+00:00
-- url     : https://prove2.me/submissions/19836300-9332-4a4c-9340-7e1e00694089

import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging
import Theorems.Thm_MasulloGRH_schwartz_correspondence
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup

set_option autoImplicit false

open MeasureTheory Topology

namespace MasulloGRHTransferAux

open MasulloGRH

theorem integral_subgroupHaar_congr {G₁ G₂ : Type*} [CommGroup G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [CommGroup G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    (k₁ : Subgroup G₁) (k₂ : Subgroup G₂) (hk₁ : IsCompact (k₁ : Set G₁))
    (hk₂ : IsCompact (k₂ : Set G₂)) (e : k₁ ≃ₜ* k₂) (F : k₂ → ℂ) :
    (letI : MeasurableSpace k₁ := borel k₁; ∫ q : k₁, F (e q) ∂ subgroupHaar k₁) =
      (letI : MeasurableSpace k₂ := borel k₂; ∫ y : k₂, F y ∂ subgroupHaar k₂) := by
  letI : MeasurableSpace k₁ := borel k₁
  haveI : BorelSpace k₁ := ⟨rfl⟩
  letI : MeasurableSpace k₂ := borel k₂
  haveI : BorelSpace k₂ := ⟨rfl⟩
  haveI : CompactSpace k₁ := isCompact_iff_compactSpace.mp hk₁
  haveI : CompactSpace k₂ := isCompact_iff_compactSpace.mp hk₂
  have h1 : subgroupHaar k₁ = Measure.haarMeasure ⊤ := by
    simp only [subgroupHaar, dif_pos hk₁]
  have h2 : subgroupHaar k₂ = Measure.haarMeasure ⊤ := by
    simp only [subgroupHaar, dif_pos hk₂]
  show ∫ q : k₁, F (e q) ∂ subgroupHaar k₁ = ∫ y : k₂, F y ∂ subgroupHaar k₂
  rw [h1, h2]
  haveI hp1 : IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k₁)) :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts k₁))⟩
  haveI hp2 : IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k₂)) :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts k₂))⟩
  let eM : k₁ ≃ᵐ k₂ := e.toHomeomorph.toMeasurableEquiv
  haveI : IsProbabilityMeasure ((Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k₁)).map e) :=
    Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  have hmap : (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k₁)).map e =
      Measure.haarMeasure ⊤ :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  rw [← hmap]
  exact (integral_map_equiv eM F).symm

end MasulloGRHTransferAux

namespace MasulloGRHTransferAux

open MasulloGRH in
theorem transfer_main
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G]
    (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π)
    (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' k')
    (hπ' : IsElemPresentation Γ' k' π') :
    ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d', Continuous T ∧
      ∀ g : ElemSchwartz m n r s d,
        schwartzBruhatAverage Γ' k' (extendPullback Γ π g.toFun) =
          extendPullback Γ' π' (T g).toFun := by
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hs.2.2.1
  have hk'c : IsCompact (k' : Set G) := isCompact_of_isGoodSubgroup G k' hs'.2.2.1
  have hΓo : IsOpen (Γ : Set G) := hs.1
  have hΓ'o : IsOpen (Γ' : Set G) := hs'.1
  have hk'Γ' : k' ≤ Γ' := hs'.2.2.2
  have hΓ'c : IsClosed (Γ' : Set G) := Subgroup.isClosed_of_isOpen Γ' hΓ'o
  set P₀ : Subgroup Γ' := Γ.subgroupOf Γ' with hP₀def
  have hP₀ : IsOpen (P₀ : Set Γ') := hΓo.preimage continuous_subtype_val
  have hP₀c : IsClosed (P₀ : Set Γ') := Subgroup.isClosed_of_isOpen P₀ hP₀
  let ι : P₀ →* Γ :=
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hιc : Continuous ι :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hvv : IsOpenMap (fun x : P₀ => (x.1 : G)) :=
    hΓ'o.isOpenMap_subtype_val.comp hP₀.isOpenMap_subtype_val
  have hιo : IsOpenMap ι := by
    intro V hV
    have : (ι '' V) = Subtype.val ⁻¹' ((fun x : P₀ => (x.1 : G)) '' V) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
    rw [this]
    exact (hvv V hV).preimage continuous_subtype_val
  let α : P₀ →* Multiplicative (ElemGroup m n r s d) := π.comp ι
  have hemb : IsClosedEmbedding (fun x : P₀ => (x.1 : G)) :=
    hΓ'c.isClosedEmbedding_subtypeVal.comp hP₀c.isClosedEmbedding_subtypeVal
  have hαk : IsCompact {x : P₀ | α x = 1} := by
    have : {x : P₀ | α x = 1} = (fun x : P₀ => (x.1 : G)) ⁻¹' k := by
      ext x
      exact hπ.2.2.2.2 (ι x)
    rw [this]
    exact hemb.isCompact_preimage hkc
  have hβk : IsCompact {x : Γ' | π' x = 1} := by
    have : {x : Γ' | π' x = 1} = Subtype.val ⁻¹' (k' : Set G) := by
      ext x
      exact hπ'.2.2.2.2 x
    rw [this]
    exact hΓ'c.isClosedEmbedding_subtypeVal.isCompact_preimage hk'c
  haveI : LocallyCompactSpace Γ' := hΓ'o.locallyCompactSpace
  obtain ⟨T, hT, hTg⟩ := schwartz_correspondence Γ' P₀ hP₀ m n r s d hπ.1 α
    (hπ.2.1.comp hιc) (hπ.2.2.1.comp hιo) hαk m' n' r' s' d' π' hπ'.2.1 hπ'.2.2.1 hβk
  -- the identification `ker π' ≃ k'`
  let e : π'.ker ≃ₜ* k' :=
    { toFun := fun q => ⟨q.1.1, (hπ'.2.2.2.2 q.1).mp (MonoidHom.mem_ker.mp q.2)⟩
      invFun := fun y => ⟨⟨y.1, hk'Γ' y.2⟩, MonoidHom.mem_ker.mpr ((hπ'.2.2.2.2 _).mpr y.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      continuous_invFun :=
        ((continuous_subtype_val.subtype_mk _).subtype_mk _) }
  haveI : LocallyCompactSpace Γ' := hΓ'o.locallyCompactSpace
  have hkerc : IsCompact ((π'.ker : Subgroup Γ') : Set Γ') := hβk
  refine ⟨T, hT, fun g => ?_⟩
  funext x
  obtain ⟨h1, -⟩ := hTg g
  by_cases hx : x ∈ Γ'
  · rw [schwartzBruhatAverage, Set.indicator_of_mem (show x ∈ (Γ' : Set G) from hx),
      extendPullback, dif_pos hx, h1 ⟨x, hx⟩, schwartzBruhatAverage,
      Set.indicator_of_mem (show (⟨x, hx⟩ : Γ') ∈ ((⊤ : Subgroup Γ') : Set Γ') from trivial)]
    have key : ∀ q : π'.ker, extendPullback P₀ α g.toFun (⟨x, hx⟩ * q) =
        extendPullback Γ π g.toFun (x * ((q : Γ') : G)) := by
      intro q
      by_cases hm : x * ((q : Γ') : G) ∈ Γ
      · have hm' : (⟨x, hx⟩ * (q : Γ') : Γ') ∈ P₀ := Subgroup.mem_subgroupOf.mpr hm
        rw [extendPullback, extendPullback, dif_pos hm', dif_pos hm]
        rfl
      · have hm' : (⟨x, hx⟩ * (q : Γ') : Γ') ∉ P₀ := fun h => hm (Subgroup.mem_subgroupOf.mp h)
        rw [extendPullback, extendPullback, dif_neg hm', dif_neg hm]
    symm
    have := integral_subgroupHaar_congr π'.ker k' hkerc hk'c e
      (fun y => extendPullback Γ π g.toFun (x * (y : G)))
    refine Eq.trans ?_ this
    exact integral_congr_ae (Filter.Eventually.of_forall key)
  · have h2 : x ∉ (Γ' : Set G) := hx
    rw [schwartzBruhatAverage, Set.indicator_of_notMem h2, extendPullback, dif_neg hx]

end MasulloGRHTransferAux

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G]
    (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
    (π : ↥Γ →* Multiplicative (MasulloGRH.ElemGroup m n r s d)) (hs : MasulloGRH.IsStructuralPair Γ k)
    (hπ : MasulloGRH.IsElemPresentation Γ k π)
    (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (π' : ↥Γ' →* Multiplicative (MasulloGRH.ElemGroup m' n' r' s' d'))
    (hs' : MasulloGRH.IsStructuralPair Γ' k')
    (hπ' : MasulloGRH.IsElemPresentation Γ' k' π') :
    ∃ T : MasulloGRH.ElemSchwartz m n r s d →ₗ[ℂ] MasulloGRH.ElemSchwartz m' n' r' s' d',
      Continuous T ∧
      ∀ g : MasulloGRH.ElemSchwartz m n r s d,
        MasulloGRH.schwartzBruhatAverage Γ' k' (MasulloGRH.extendPullback Γ π g.toFun) =
          MasulloGRH.extendPullback Γ' π' (T g).toFun :=
  MasulloGRHTransferAux.transfer_main G Γ k m n r s d π hs hπ Γ' k' m' n' r' s' d' π' hs' hπ'
