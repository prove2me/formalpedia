-- Prove2me | solution 1 for NeronModelInfra.exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2966a706-1f3e-5e78-ae67-9faff6fc92cd

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_pointwise_extension_dense
import Theorems.Thm_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra P2MW.S_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth.NeronModelInfra"

namespace NeronModelInfra
p2m_export "NeronModelInfra" "specGenericFibreInclusion SchemeHomOver genericFibreRestrict genericFibreRestrict_coe_comp_fst"
namespace NBHDEXT
p2m_open "NeronModelInfra"

namespace Aux

open TopologicalSpace Topology

theorem isLocallyNoetherian_of_locallyOfFiniteType {S : Type u} [CommRing S] [IsNoetherianRing S]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType t] : IsLocallyNoetherian T := by
  refine isLocallyNoetherian_of_affine_cover (S := fun V : T.affineOpens => V) (by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩) fun V => ?_
  have hft : RingHom.FiniteType (t.appLE ⊤ V (le_top.trans (le_of_eq (Scheme.Hom.preimage_top t).symm))).hom :=
    HasRingHomProperty.appLE @LocallyOfFiniteType t inferInstance ⟨⊤, isAffineOpen_top _⟩ V _
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of S), ⊤) :=
    isNoetherianRing_of_ringEquiv S (Scheme.ΓSpecIso (CommRingCat.of S)).symm.commRingCatIsoToRingEquiv
  letI := (t.appLE ⊤ V (le_top.trans (le_of_eq (Scheme.Hom.preimage_top t).symm))).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Spec (CommRingCat.of S), ⊤) Γ(T, V) := hft
  exact Algebra.FiniteType.isNoetherianRing Γ(Spec (CommRingCat.of S), ⊤) Γ(T, V)

theorem eq_irreducibleComponent_of_mem {X : Scheme.{u}} {x : X} (hx : IsDomain (X.presheaf.stalk x))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hxZ : x ∈ Z) : Z = irreducibleComponent x := by
  have hZ' := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  obtain ⟨ξ', hξ'⟩ := QuasiSober.sober hZ'.1 isClosed_irreducibleComponent
  have h1 : ξ ⤳ x := hξ.specializes hxZ
  have h2 : ξ' ⤳ x := hξ'.specializes mem_irreducibleComponent
  have hr : Set.range (X.fromSpecStalk x).base = {y | y ⤳ x} := Scheme.range_fromSpecStalk
  obtain ⟨p, hp⟩ : ξ ∈ Set.range (X.fromSpecStalk x).base := by rw [hr]; exact h1
  obtain ⟨p', hp'⟩ : ξ' ∈ Set.range (X.fromSpecStalk x).base := by rw [hr]; exact h2
  haveI : IsDomain (X.presheaf.stalk x) := hx
  set g : X := (X.fromSpecStalk x).base (genericPoint (Spec (X.presheaf.stalk x))) with hg
  have hc : Continuous (X.fromSpecStalk x).base := (X.fromSpecStalk x).continuous
  have hg1 : g ⤳ ξ := hp ▸ (genericPoint_specializes p).map hc
  have hg2 : g ⤳ ξ' := hp' ▸ (genericPoint_specializes p').map hc
  have hcl : IsIrreducible (closure ({g} : Set X)) := isIrreducible_singleton.closure
  have hsub : Z ⊆ closure {g} := by
    rw [← hξ.def]; exact specializes_iff_closure_subset.mp hg1
  have hsub' : irreducibleComponent x ⊆ closure {g} := by
    rw [← hξ'.def]; exact specializes_iff_closure_subset.mp hg2
  have e1 : closure {g} = Z := Set.Subset.antisymm (hZ.2 hcl hsub) hsub
  have e2 : closure {g} = irreducibleComponent x := Set.Subset.antisymm (hZ'.2 hcl hsub') hsub'
  exact e1.symm.trans e2

theorem exists_open_subset_irreducibleComponent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (z : X) (hz : IsDomain (X.presheaf.stalk z)) :
    ∃ O : Set X, IsOpen O ∧ z ∈ O ∧ O ⊆ irreducibleComponent z := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ : ↥(Spec Γ(X, U)) → (U : Set X) := fun q => ⟨hU.fromSpec.base q, by
    have : hU.fromSpec.base q ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rwa [hU.range_fromSpec] at this⟩
  have hφc : Continuous φ := hU.fromSpec.continuous.subtype_mk _
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have : y ∈ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hy
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, rfl⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_surjective φ hφc hφs
  set z' : (U : Set X) := ⟨z, hzU⟩
  set F : Set (U : Set X) := ⋃ C ∈ {C ∈ irreducibleComponents (U : Set X) | z' ∉ C}, C with hF
  have hFfin : {C ∈ irreducibleComponents (U : Set X) | z' ∉ C}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset (Set.sep_subset _ _)
  have hFcl : IsClosed F := hFfin.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hzF : z' ∉ F := by
    simp only [hF, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, and_imp]
    exact fun C _ hzC hzC' => hzC hzC'
  refine ⟨Subtype.val '' Fᶜ, U.isOpen.isOpenMap_subtype_val _ hFcl.isOpen_compl, ⟨z', hzF, rfl⟩, ?_⟩
  rintro _ ⟨y, hyF, rfl⟩
  have hC := irreducibleComponent_mem_irreducibleComponents y
  have hzC : z' ∈ irreducibleComponent y := by
    by_contra h
    exact hyF (Set.mem_biUnion (x := irreducibleComponent y) ⟨hC, h⟩ mem_irreducibleComponent)
  have hS : IsIrreducible (Subtype.val '' irreducibleComponent y : Set X) :=
    hC.1.image _ continuous_subtype_val.continuousOn
  obtain ⟨W, hWpre, hSW, hWmax⟩ := exists_preirreducible _ hS.2
  have hWirr : IsIrreducible W := ⟨⟨z, hSW ⟨z', hzC, rfl⟩⟩, hWpre⟩
  have hWcomp : W ∈ irreducibleComponents X :=
    ⟨hWirr, fun u hu hWu => (hWmax u hu.2 hWu).le⟩
  have hWeq : W = irreducibleComponent z := eq_irreducibleComponent_of_mem hz hWcomp (hSW ⟨z', hzC, rfl⟩)
  rw [← hWeq]
  exact hSW ⟨y, mem_irreducibleComponent, rfl⟩

end Aux

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

local notation "ιK" => specGenericFibreInclusion R K

theorem repack
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    (uK : SchemeHomOver (pullback.snd t ιK) (pullback.snd f ιK))
    (G : T.Opens) (η : T) (hηG : η ∈ G)
    (V : (G : Scheme.{u}).Opens) (v : (V : Scheme.{u}) ⟶ X) (hv : v ≫ f = V.ι ≫ G.ι ≫ t)
    (hηV : (⟨η, hηG⟩ : (G : Scheme.{u})) ∈ V)
    (hle : Set.range (pullback.fst (G.ι ≫ t) ιK).base ⊆ Set.range V.ι.base)
    (hcompat : IsOpenImmersion.lift V.ι (pullback.fst (G.ι ≫ t) ιK) hle ≫ v =
      (pullback.map (G.ι ≫ t) ιK t ιK G.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1) ≫ pullback.fst f ιK) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
      (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) ιK t ιK U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by

  let j : (V : Scheme.{u}) ⟶ T := V.ι ≫ G.ι
  let U : T.Opens := j.opensRange
  let e := Scheme.Hom.isoOpensRange j
  have he : e.inv ≫ j = U.ι := Scheme.Hom.isoOpensRange_inv_comp j
  have hUG : U ≤ G := by
    rintro _ ⟨y, rfl⟩
    exact (V.ι.base y).2
  have hηU : η ∈ U := ⟨⟨⟨η, hηG⟩, hηV⟩, rfl⟩
  let g : SchemeHomOver (U.ι ≫ t) f := ⟨e.inv ≫ v, by
    rw [Category.assoc, hv, ← Category.assoc e.inv V.ι, ← Category.assoc (e.inv ≫ V.ι) G.ι t, Category.assoc e.inv]
    change (e.inv ≫ j) ≫ t = U.ι ≫ t
    rw [he]⟩
  refine ⟨U, hηU, g, ?_⟩

  let mUG : pullback (U.ι ≫ t) ιK ⟶ pullback (G.ι ≫ t) ιK :=
    pullback.map (U.ι ≫ t) ιK (G.ι ≫ t) ιK (T.homOfLE hUG) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Category.assoc, Scheme.homOfLE_ι]) (by rw [Category.comp_id, Category.id_comp])
  have h1 : pullback.fst (U.ι ≫ t) ιK ≫ e.inv = mUG ≫ IsOpenImmersion.lift V.ι (pullback.fst (G.ι ≫ t) ιK) hle := by
    rw [← cancel_mono j]
    change (pullback.fst (U.ι ≫ t) ιK ≫ e.inv) ≫ j = (mUG ≫ IsOpenImmersion.lift V.ι (pullback.fst (G.ι ≫ t) ιK) hle) ≫ V.ι ≫ G.ι
    rw [Category.assoc, he, Category.assoc, IsOpenImmersion.lift_fac_assoc]
    simp only [mUG, pullback.map, pullback.lift_fst_assoc, Category.assoc, Scheme.homOfLE_ι]
  have h2 : mUG ≫ pullback.map (G.ι ≫ t) ιK t ιK G.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) =
      pullback.map (U.ι ≫ t) ιK t ιK U.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) := by
    apply pullback.hom_ext
    · simp only [mUG, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Scheme.homOfLE_ι]
    · simp only [mUG, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst]
    change pullback.fst (U.ι ≫ t) ιK ≫ e.inv ≫ v = _
    rw [← Category.assoc, h1, Category.assoc, hcompat, ← Category.assoc, ← Category.assoc, h2, Category.assoc]
  · rw [(genericFibreRestrict R K f (U.ι ≫ t) g).2, Category.assoc, uK.2]
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]

theorem exists_integral_opens
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (G : T.Opens) (_ : η ∈ G), IsIntegral (G : Scheme.{u}) ∧ IsCompact (G : Set T) ∧
      ∀ x : (G : Scheme.{u}), (G.ι ≫ t).base x = IsLocalRing.closedPoint R → (⟨η, ‹η ∈ G›⟩ : (G : Scheme.{u})) ⤳ x := by
  classical

  haveI : IsLocallyNoetherian T := Aux.isLocallyNoetherian_of_locallyOfFiniteType t
  haveI : CompactSpace T := by
    have := QuasiCompact.isCompact_preimage (f := t) Set.univ isOpen_univ isCompact_univ
    simpa using isCompact_univ_iff.mp (by simpa using this)
  haveI : IsNoetherian T := ⟨⟩
  haveI : IsReduced T := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian t
  obtain ⟨hdom, -⟩ := AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R t η hηs hgen

  obtain ⟨O, hO, hηO, hOsub⟩ := Aux.exists_open_subset_irreducibleComponent η hdom

  let Ts : Set T := {x : T | t.base x = IsLocalRing.closedPoint R}
  have hTs : IsClosed Ts :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (IsLocalRing.maximalIdeal.isMaximal R)).preimage
      t.base.hom.continuous
  haveI : QuasiSober Ts := hTs.isClosedEmbedding_subtypeVal.quasiSober
  haveI : TopologicalSpace.NoetherianSpace Ts := inferInstance
  let η' : Ts := ⟨η, hηs⟩
  let F : Set Ts := ⋃ C ∈ {C ∈ irreducibleComponents Ts | η' ∉ C}, C
  have hFfin : {C ∈ irreducibleComponents Ts | η' ∉ C}.Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (Set.sep_subset _ _)
  have hFcl : IsClosed F := hFfin.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hF' : IsClosed (Subtype.val '' F : Set T) := hTs.isClosedEmbedding_subtypeVal.isClosedMap _ hFcl
  have hηF : η ∉ (Subtype.val '' F : Set T) := by
    rintro ⟨y, hy, hyη⟩
    have : y = η' := Subtype.ext hyη
    subst this
    simp only [F, Set.mem_iUnion, Set.mem_setOf_eq] at hy
    obtain ⟨C, ⟨-, hC⟩, hC'⟩ := hy
    exact hC hC'

  obtain ⟨_, ⟨G, hG, rfl⟩, hηG, hGsub⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (show η ∈ O ∩ (Subtype.val '' F)ᶜ from ⟨hηO, hηF⟩) (hO.inter hF'.isOpen_compl)
  refine ⟨G, hηG, ?_, hG.isCompact, ?_⟩
  ·
    have hirr : IsIrreducible (G : Set T) := by
      refine ⟨⟨η, hηG⟩, (irreducibleComponent_mem_irreducibleComponents η).1.2.open_subset G.isOpen ?_⟩
      exact fun x hx => hOsub (hGsub hx).1
    haveI : IrreducibleSpace (G : Scheme.{u}) := (isIrreducible_iff_irreducibleSpace (s := (G : Set T))).mp hirr
    haveI : IsReduced (G : Scheme.{u}) := isReduced_of_isOpenImmersion (Scheme.Opens.ι G)
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  ·
    intro x hx
    have hxs : t.base x.1 = IsLocalRing.closedPoint R := hx
    let x' : Ts := ⟨x.1, hxs⟩

    have hC := irreducibleComponent_mem_irreducibleComponents x'
    have hηC : η' ∈ irreducibleComponent x' := by
      by_contra h
      have : x.1 ∈ (Subtype.val '' F : Set T) :=
        ⟨x', Set.mem_biUnion (x := irreducibleComponent x') ⟨hC, h⟩ mem_irreducibleComponent, rfl⟩
      exact (hGsub x.2).2 this

    obtain ⟨ζ, hζ⟩ := QuasiSober.sober hC.1 isClosed_irreducibleComponent
    have hζη : ζ ⤳ η' := hζ.specializes hηC
    have hζx : ζ ⤳ x' := hζ.specializes mem_irreducibleComponent
    have hζT : ζ.1 ⤳ η := hζη.map continuous_subtype_val
    have hζeq : ζ.1 = η := hgen ζ.1 hζT ζ.2
    have hηx : η ⤳ x.1 := by
      have := hζx.map continuous_subtype_val
      rwa [hζeq] at this
    exact Topology.IsInducing.subtypeVal.specializes_iff.mp hηx

theorem fst_base_eq_bot (w : ↥(pullback (𝟙 (Spec (CommRingCat.of R))) ιK)) :
    (pullback.fst (𝟙 (Spec (CommRingCat.of R))) ιK).base w = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  have h1 : pullback.fst (𝟙 (Spec (CommRingCat.of R))) ιK = pullback.snd (𝟙 _) ιK ≫ ιK := by
    simpa using (pullback.condition (f := 𝟙 (Spec (CommRingCat.of R))) (g := ιK))
  rw [h1, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]

  apply PrimeSpectrum.ext
  show Ideal.comap (algebraMap R K) ((pullback.snd (𝟙 _) ιK).base w).asIdeal = ⊥
  have hK : ((pullback.snd (𝟙 _) ιK).base w).asIdeal = ⊥ := by
    haveI : ((pullback.snd (𝟙 _) ιK).base w).asIdeal.IsPrime := inferInstance
    exact Ideal.eq_bot_of_prime _
  rw [hK, Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)]

scoped instance : Nonempty ↥(pullback (𝟙 (Spec (CommRingCat.of R))) ιK) :=
  ⟨(pullback.lift ιK (𝟙 _) (by simp)).base (IsLocalRing.closedPoint K)⟩

theorem main
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hext : Function.Surjective (genericFibreRestrict R K f (𝟙 (Spec (CommRingCat.of R)))))
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t ιK) (pullback.snd f ιK))
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
      (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) ιK t ιK U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  classical

  obtain ⟨G, hηG, hint, -, hirr⟩ := exists_integral_opens R t η hηs hgen
  haveI := hint
  let g : (G : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := G.ι ≫ t
  let η' : (G : Scheme.{u}) := ⟨η, hηG⟩
  have hη' : g.base η' = IsLocalRing.closedPoint R := by
    show t.base (G.ι.base η') = _
    exact hηs
  have hgen' : ∀ y : (G : Scheme.{u}), y ⤳ η' → g.base y = IsLocalRing.closedPoint R → y = η' := by
    intro y hy hys
    have h1 : G.ι.base y ⤳ η := hy.map G.ι.base.hom.continuous
    have h2 : G.ι.base y = η := hgen _ h1 hys
    exact G.ι.isOpenEmbedding.injective (h2.trans rfl)

  haveI : Smooth g := inferInstance
  obtain ⟨_, hdvr⟩ := Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R g η' hη' hgen'
  haveI := hdvr

  let φK : pullback g ιK ⟶ pullback f ιK :=
    pullback.map g ιK t ιK G.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1
  have hφK : φK ≫ pullback.snd f ιK = pullback.snd g ιK := by
    simp only [φK, Category.assoc, uK.2, pullback.lift_snd, Category.comp_id]

  let D : Set (G : Scheme.{u}) := {x | g.base x = IsLocalRing.closedPoint R ∧
    ∃ s : Spec (CommRingCat.of R) ⟶ (G : Scheme.{u}), s ≫ g = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) = x}
  have hD : ∀ z ∈ D, g.base z = IsLocalRing.closedPoint R := fun z hz => hz.1
  have hDη : η' ∈ closure D := by
    have hdense := Smooth.dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed g

    have hmem : (⟨η', hη'⟩ : {x : (G : Scheme.{u}) // g.base x = IsLocalRing.closedPoint R}) ∈
        closure {x : {x : (G : Scheme.{u}) // g.base x = IsLocalRing.closedPoint R} |
          ∃ s : Spec (CommRingCat.of R) ⟶ (G : Scheme.{u}), s ≫ g = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) = x.1} := by
      rw [hdense.closure_eq]; trivial
    rw [closure_subtype] at hmem
    refine closure_mono ?_ hmem
    rintro _ ⟨⟨x, hx⟩, ⟨s, hs, hsx⟩, rfl⟩
    exact ⟨hx, s, hs, hsx⟩
  have hpts : ∀ z ∈ D, ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
      (c : Spec (CommRingCat.of A) ⟶ pullback g f),
      (c ≫ pullback.fst g f).base (IsLocalRing.closedPoint A) = z ∧
      c.base ⟨⊥, Ideal.isPrime_bot⟩ ∈ Set.range
        (pullback.lift (pullback.fst g ιK) (φK ≫ pullback.fst f ιK)
          (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).base := by
    rintro z ⟨-, s, hs, hsz⟩
    let sR : SchemeHomOver (𝟙 _) g := ⟨s, hs⟩
    let sK := genericFibreRestrict R K g (𝟙 _) sR
    let xK : SchemeHomOver (pullback.snd (𝟙 (Spec (CommRingCat.of R))) ιK) (pullback.snd f ιK) :=
      ⟨sK.1 ≫ φK, by rw [Category.assoc, hφK, sK.2]⟩
    obtain ⟨gx, hgx⟩ := hext xK
    refine ⟨R, inferInstance, inferInstance, inferInstance, pullback.lift s gx.1 (hs.trans gx.2.symm), ?_, ?_⟩
    · rw [pullback.lift_fst]; exact hsz
    ·
      obtain ⟨w⟩ := (inferInstance : Nonempty ↥(pullback (𝟙 (Spec (CommRingCat.of R))) ιK))
      refine ⟨sK.1.base w, ?_⟩
      have key : sK.1 ≫ pullback.lift (pullback.fst g ιK) (φK ≫ pullback.fst f ιK)
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition]) =
          pullback.fst (𝟙 _) ιK ≫ pullback.lift s gx.1 (hs.trans gx.2.symm) := by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst]
          exact pullback.lift_fst _ _ _
        · simp only [Category.assoc, pullback.lift_snd]
          have e1 : (genericFibreRestrict R K f (𝟙 _) gx).1 = xK.1 := by rw [hgx]
          have e2 : (genericFibreRestrict R K f (𝟙 _) gx).1 ≫ pullback.fst f ιK = pullback.fst (𝟙 _) ιK ≫ gx.1 :=
            pullback.lift_fst _ _ _
          rw [← e2, e1]
          simp only [xK, φK, Category.assoc]
      have hk := congrArg (fun φ => φ.base w) key
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hk
      rw [hk, fst_base_eq_bot]

  obtain ⟨V, v, hv, -, hηV, hle, hcompat⟩ :=
    Scheme.exists_opens_extension_of_pointwise_extension_dense K g f η' hη' hirr φK hφK D hD hDη hpts
  exact repack R K f t uK G η hηG V v hv hηV hle hcompat

end NeronModelInfra.NBHDEXT
p2m_reactivate "P2MW.S_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth.NeronModelInfra P2MW.S_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth.NeronModelInfra.NBHDEXT"
p2m_reactivate "P2MW.S_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth.NeronModelInfra"

open _root_.NeronModelInfra _root_.P2MW.S_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth.NeronModelInfra in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hext : Function.Surjective (genericFibreRestrict R K f (𝟙 (Spec (CommRingCat.of R)))))
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
      (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  exact NBHDEXT.main R K f hext t uK η hηs hgen

end S_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth
end P2MW
export P2MW.S_NeronModelInfra_exists_nhds_extension_of_surjective_genericFibreRestrict_of_smooth (solution)
