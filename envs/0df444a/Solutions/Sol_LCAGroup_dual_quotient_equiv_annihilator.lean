-- Prove2me | solution 1 for LCAGroup.dual_quotient_equiv_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:29:48.731027+00:00
-- url     : https://prove2.me/submissions/803c99fe-572f-42b2-a2ac-2096c916514c

import Mathlib
import Definitions.Def_LCAGroup_Annihilator

open Topology

set_option autoImplicit false

namespace Sol_LCAGroup_dual_quotient_equiv_annihilator

open Set Filter

/-- The compact-open neighbourhoods of the trivial character: the sets of characters mapping a
compact set `K` into a neighbourhood `V` of `1` in the circle form a basis of `𝓝 1`. -/
theorem pontryaginDual_nhds_one_hasBasis (G : Type*) [CommGroup G] [TopologicalSpace G] :
    (𝓝 (1 : PontryaginDual G)).HasBasis
      (fun p : Set G × Set Circle => IsCompact p.1 ∧ p.2 ∈ 𝓝 (1 : Circle))
      (fun p => {χ : PontryaginDual G | MapsTo χ p.1 p.2}) := by
  let f : PontryaginDual G → C(G, Circle) := ContinuousMonoidHom.toContinuousMap
  have hf : IsInducing f := ContinuousMonoidHom.isInducing_toContinuousMap G Circle
  rw [hf.nhds_eq_comap]
  exact ((𝓝 (1 : Circle)).basis_sets.nhds_continuousMapConst (X := G)).comap f

/-- A compact subset of a quotient of a locally compact group is contained in the image of a
compact subset of the group. -/
theorem exists_isCompact_quotient_preimage {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] (H : Subgroup G) {K : Set (G ⧸ H)}
    (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ K ⊆ (QuotientGroup.mk : G → G ⧸ H) '' C := by
  obtain ⟨L, hLcomp, hL⟩ := exists_compact_mem_nhds (1 : G)
  have hU : (QuotientGroup.mk : G → G ⧸ H) '' L ∈ 𝓝 (1 : G ⧸ H) :=
    (QuotientGroup.isOpenMap_coe (N := H)).image_mem_nhds hL
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK
    ⟨(1 : G ⧸ H), mem_interior_iff_mem_nhds.mpr hU⟩
  refine ⟨⋃ g ∈ t, Homeomorph.mulLeft (g.out)⁻¹ '' L,
    t.isCompact_biUnion fun g _ =>
      hLcomp.image (Homeomorph.mulLeft (g.out)⁻¹).continuous, ?_⟩
  intro k hk
  obtain ⟨g, hg, hkU⟩ := mem_iUnion₂.mp (ht hk)
  rw [mem_preimage, mem_image] at hkU
  obtain ⟨y, hy, hgy⟩ := hkU
  refine ⟨(g.out)⁻¹ * y, mem_iUnion₂.mpr ⟨g, hg, mem_image_of_mem _ hy⟩, ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hgy,
    inv_mul_cancel_left]

end Sol_LCAGroup_dual_quotient_equiv_annihilator

open LCAGroup Sol_LCAGroup_dual_quotient_equiv_annihilator in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* annihilator H,
      ∀ (η : PontryaginDual (G ⧸ H)) (x : G),
        (e η : PontryaginDual G) x = η (x : G ⧸ H) := by
  -- the quotient map as a continuous homomorphism
  let q : G →ₜ* G ⧸ H :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := QuotientGroup.continuous_mk }
  have hq (x : G) : q x = (x : G ⧸ H) := rfl
  have hker (ψ : annihilator H) : H ≤ (ψ : PontryaginDual G).toMonoidHom.ker := by
    intro x hx
    exact (mem_annihilator_iff H ψ.val).1 ψ.property x hx
  -- pull-back along the quotient map
  let toAnn : PontryaginDual (G ⧸ H) →* annihilator H :=
    { toFun := fun χ => ⟨PontryaginDual.map q χ, by
        rw [mem_annihilator_iff]
        intro x hx
        rw [PontryaginDual.map_apply]
        have h1 : q x = 1 := (QuotientGroup.eq_one_iff x).2 hx
        rw [h1, map_one]⟩
      map_one' := Subtype.ext (map_one (PontryaginDual.map q))
      map_mul' := fun χ φ => Subtype.ext (map_mul (PontryaginDual.map q) χ φ) }
  -- descent of a character trivial on `H`
  let fromAnnFun (ψ : annihilator H) : PontryaginDual (G ⧸ H) :=
    { toMonoidHom := QuotientGroup.lift H (ψ : PontryaginDual G).toMonoidHom (hker ψ)
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ψ.val.continuous_toFun }
  have happly (ψ : annihilator H) (x : G) :
      fromAnnFun ψ (x : G ⧸ H) = (ψ : PontryaginDual G) x :=
    QuotientGroup.lift_mk' H (hker ψ) x
  let fromAnn : annihilator H →* PontryaginDual (G ⧸ H) :=
    { toFun := fromAnnFun
      map_one' := by
        apply PontryaginDual.ext
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        rw [happly 1 x]
        rfl
      map_mul' := fun ψ φ => by
        apply PontryaginDual.ext
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        rw [happly (ψ * φ) x]
        have hr :
            (fromAnnFun ψ * fromAnnFun φ) (x : G ⧸ H) =
              fromAnnFun ψ (x : G ⧸ H) * fromAnnFun φ (x : G ⧸ H) :=
          ContinuousMonoidHom.mul_apply _ _ _
        rw [hr, happly ψ x, happly φ x, Subgroup.coe_mul]
        rfl }
  have hinv_left (χ : PontryaginDual (G ⧸ H)) : fromAnn (toAnn χ) = χ := by
    apply PontryaginDual.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact happly (toAnn χ) x
  have hinv_right (ψ : annihilator H) : toAnn (fromAnn ψ) = ψ := by
    apply Subtype.ext
    apply PontryaginDual.ext
    intro x
    exact happly ψ x
  have hto_cont : Continuous toAnn := by
    rw [IsInducing.subtypeVal.continuous_iff (f := toAnn)]
    exact (PontryaginDual.map q).continuous
  have hfrom_cont : Continuous fromAnn := by
    refine continuous_of_continuousAt_one fromAnn ?_
    rw [ContinuousAt, map_one fromAnn]
    refine (pontryaginDual_nhds_one_hasBasis (G ⧸ H)).tendsto_right_iff.mpr ?_
    rintro ⟨K, V⟩ ⟨hK, hV⟩
    obtain ⟨C, hC, hKC⟩ := exists_isCompact_quotient_preimage H hK
    rw [IsInducing.subtypeVal.nhds_eq_comap (1 : annihilator H)]
    refine Filter.mem_comap.mpr ⟨{ψ : PontryaginDual G | Set.MapsTo ψ C V},
      (pontryaginDual_nhds_one_hasBasis G).mem_of_mem (i := (C, V)) ⟨hC, hV⟩, ?_⟩
    intro ψ hψ
    have hψ' : Set.MapsTo ((ψ : PontryaginDual G) : G → Circle) C V := hψ
    show Set.MapsTo (fromAnn ψ) K V
    intro k hk
    obtain ⟨x, hxC, rfl⟩ := hKC hk
    show fromAnnFun ψ (x : G ⧸ H) ∈ V
    rw [happly ψ x]
    exact hψ' hxC
  let e : PontryaginDual (G ⧸ H) ≃ₜ* annihilator H :=
    { toFun := toAnn
      invFun := fromAnn
      left_inv := hinv_left
      right_inv := hinv_right
      map_mul' := toAnn.map_mul
      continuous_toFun := hto_cont
      continuous_invFun := hfrom_cont }
  exact ⟨e, fun χ x => rfl⟩
