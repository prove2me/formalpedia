-- Prove2me | solution 1 for NeronModelInfra.exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b6ae4552-5de4-5c12-add2-899246ffdac4

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
import Theorems.Thm_AlgebraicGeometry_isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace Completion21

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (q : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion q.1]

noncomputable def F : WidePushoutShape Bool ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan (pullback f (specGenericFibreInclusion R K))
    (fun b : Bool => bif b then Y else XK)
    (fun b => match b with
      | true => pullback.fst f (specGenericFibreInclusion R K)
      | false => q.1)

scoped instance F_map_isOpenImmersion : ∀ {i j : WidePushoutShape Bool} (a : i ⟶ j), IsOpenImmersion ((F K gK f q).map a) := by
  rintro i j ⟨⟩
  · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
  · rename_i b
    cases b
    · exact inferInstanceAs (IsOpenImmersion q.1)
    · exact inferInstanceAs (IsOpenImmersion (pullback.fst f (specGenericFibreInclusion R K)))

noncomputable def Y' : Scheme.{u} := colimit (F K gK f q)

noncomputable def j : Y ⟶ Y' K gK f q := colimit.ι (F K gK f q) (some true)
noncomputable def jX : XK ⟶ Y' K gK f q := colimit.ι (F K gK f q) (some false)
noncomputable def j0 : pullback f (specGenericFibreInclusion R K) ⟶ Y' K gK f q := colimit.ι (F K gK f q) none

scoped instance : IsOpenImmersion (j K gK f q) := inferInstanceAs (IsOpenImmersion (colimit.ι (F K gK f q) (some true)))
scoped instance : IsOpenImmersion (jX K gK f q) := inferInstanceAs (IsOpenImmersion (colimit.ι (F K gK f q) (some false)))

theorem fst_j : pullback.fst f (specGenericFibreInclusion R K) ≫ j K gK f q = j0 K gK f q :=
  colimit.w (F K gK f q) (WidePushoutShape.Hom.init true)

theorem q_jX : q.1 ≫ jX K gK f q = j0 K gK f q :=
  colimit.w (F K gK f q) (WidePushoutShape.Hom.init false)

noncomputable def f' : Y' K gK f q ⟶ Spec (CommRingCat.of R) :=
  colimit.desc (F K gK f q)
    (WidePushoutShape.mkCocone
      (pullback.fst f (specGenericFibreInclusion R K) ≫ f)
      (fun b => match b with
        | true => f
        | false => gK ≫ specGenericFibreInclusion R K)
      (by
        rintro ⟨⟩
        · show q.1 ≫ gK ≫ specGenericFibreInclusion R K = pullback.fst f _ ≫ f
          rw [← Category.assoc, q.2, pullback.condition]
        · rfl))

theorem j_f' : j K gK f q ≫ f' K gK f q = f :=
  colimit.ι_desc _ _

theorem jX_f' : jX K gK f q ≫ f' K gK f q = gK ≫ specGenericFibreInclusion R K :=
  colimit.ι_desc _ _

theorem cover (y : ↥(Y' K gK f q)) :
    y ∈ Set.range (j K gK f q).base ∨ y ∈ Set.range (jX K gK f q).base := by
  obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (F K gK f q) y
  rcases i with _ | _ | _
  · left
    refine ⟨(pullback.fst f (specGenericFibreInclusion R K)).base x, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    rw [fst_j]; exact hx
  · right; exact ⟨x, hx⟩
  · left; exact ⟨x, hx⟩

local notation "ιK" => specGenericFibreInclusion R K

theorem j0_f' : j0 K gK f q ≫ f' K gK f q = pullback.fst f ιK ≫ f := by
  rw [← fst_j, Category.assoc, j_f']

theorem closedPoint_not_mem_range : IsLocalRing.closedPoint R ∉ Set.range (specGenericFibreInclusion R K).base := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [range_specGenericFibreInclusion_eq_basicOpen R K hϖ]
  intro h
  have h' : ϖ ∉ (IsLocalRing.closedPoint R).asIdeal := (PrimeSpectrum.mem_basicOpen ϖ _).mp h
  exact h' ((IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit)

theorem lft [LocallyOfFiniteType gK] [LocallyOfFiniteType f] : LocallyOfFiniteType (f' K gK f q) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (F K gK f q))).mpr
  rintro (_ | _ | _)
  · rw [Scheme.IsLocallyDirected.openCover_f]
    change LocallyOfFiniteType (j0 K gK f q ≫ f' K gK f q)
    rw [j0_f']; infer_instance
  · rw [Scheme.IsLocallyDirected.openCover_f]
    change LocallyOfFiniteType (jX K gK f q ≫ f' K gK f q)
    rw [jX_f']; infer_instance
  · rw [Scheme.IsLocallyDirected.openCover_f]
    change LocallyOfFiniteType (j K gK f q ≫ f' K gK f q)
    rw [j_f']; infer_instance

theorem smooth (hgK : Smooth gK) (hf : Smooth f) : Smooth (f' K gK f q) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth)
    (Scheme.IsLocallyDirected.openCover (F K gK f q))).mpr
  rintro (_ | _ | _)
  · rw [Scheme.IsLocallyDirected.openCover_f]
    change Smooth (j0 K gK f q ≫ f' K gK f q)
    rw [j0_f']; infer_instance
  · rw [Scheme.IsLocallyDirected.openCover_f]
    change Smooth (jX K gK f q ≫ f' K gK f q)
    rw [jX_f']; infer_instance
  · rw [Scheme.IsLocallyDirected.openCover_f]
    change Smooth (j K gK f q ≫ f' K gK f q)
    rw [j_f']; infer_instance

theorem qc [QuasiCompact gK] [QuasiCompact f] : QuasiCompact (f' K gK f q) := by
  haveI : CompactSpace ↥Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI : CompactSpace ↥XK := QuasiCompact.compactSpace_of_compactSpace gK
  haveI : CompactSpace ↥(Y' K gK f q) := by
    constructor
    have h : Set.range (j K gK f q).base ∪ Set.range (jX K gK f q).base = Set.univ :=
      Set.eq_univ_of_forall fun y => cover K gK f q y
    rw [← h]
    exact (isCompact_range (j K gK f q).base.hom.continuous).union
      (isCompact_range (jX K gK f q).base.hom.continuous)
  exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹_›

theorem special (y : ↥(Y' K gK f q)) (hy : (f' K gK f q).base y = IsLocalRing.closedPoint R) :
    y ∈ Set.range (j K gK f q).base := by
  rcases cover K gK f q y with h | ⟨x, hx⟩
  · exact h
  · exfalso
    apply closedPoint_not_mem_range (R := R) K
    refine ⟨gK.base x, ?_⟩
    rw [← hy, ← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, jX_f']

noncomputable def eInv : XK ⟶ pullback (f' K gK f q) ιK :=
  pullback.lift (jX K gK f q) gK (jX_f' K gK f q)

theorem eInv_fst : eInv K gK f q ≫ pullback.fst (f' K gK f q) ιK = jX K gK f q := pullback.lift_fst _ _ _
theorem eInv_snd : eInv K gK f q ≫ pullback.snd (f' K gK f q) ιK = gK := pullback.lift_snd _ _ _

scoped instance : IsOpenImmersion (eInv K gK f q) := by
  have : IsOpenImmersion (eInv K gK f q ≫ pullback.fst (f' K gK f q) ιK) := by
    rw [eInv_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst (f' K gK f q) ιK)

theorem eInv_surjective : Function.Surjective (eInv K gK f q).base := by
  intro z

  have key : ∀ x : ↥XK, (jX K gK f q).base x = (pullback.fst (f' K gK f q) ιK).base z →
      ∃ x' : ↥XK, (eInv K gK f q).base x' = z := by
    intro x hx
    refine ⟨x, (pullback.fst (f' K gK f q) ιK).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, eInv_fst]
    exact hx
  rcases cover K gK f q ((pullback.fst (f' K gK f q) ιK).base z) with ⟨y, hy⟩ | ⟨x, hx⟩
  ·
    have hyK : y ∈ Set.range (pullback.fst f ιK).base := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(pullback.snd (f' K gK f q) ιK).base z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ← hy,
        ← Scheme.Hom.comp_apply, j_f']
    obtain ⟨w, rfl⟩ := hyK
    apply key (q.1.base w)
    rw [← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, q_jX, fst_j]
  · exact key x hx

scoped instance : IsIso (eInv K gK f q) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨eInv_surjective K gK f q⟩⟩

noncomputable def e : SchemeHomOver (pullback.snd (f' K gK f q) ιK) gK :=
  ⟨inv (eInv K gK f q), by rw [IsIso.inv_comp_eq, eInv_snd]⟩

scoped instance : IsIso (e K gK f q).1 := inferInstanceAs (IsIso (inv (eInv K gK f q)))

theorem comp_e :
    schemeHomOverComp (genericFibreRestrict R K (f' K gK f q) f ⟨j K gK f q, j_f' K gK f q⟩) (e K gK f q) = q := by
  apply Subtype.ext
  rw [schemeHomOverComp_coe]
  change (genericFibreRestrict R K (f' K gK f q) f ⟨j K gK f q, j_f' K gK f q⟩).1 ≫ inv (eInv K gK f q) = q.1
  rw [IsIso.comp_inv_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, eInv_fst, q_jX, ← fst_j]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, eInv_snd, q.2]
    exact pullback.lift_snd _ _ _

theorem isPullback : IsPullback (pullback.fst f ιK) q.1 (j K gK f q) (jX K gK f q) := by
  have hw : pullback.fst f ιK ≫ j K gK f q = q.1 ≫ jX K gK f q := by rw [fst_j, q_jX]
  let s : pullback f ιK ⟶ pullback (j K gK f q) (jX K gK f q) := pullback.lift (pullback.fst f ιK) q.1 hw
  have hr : pullback.fst (j K gK f q) (jX K gK f q) ≫ f =
      (pullback.snd (j K gK f q) (jX K gK f q) ≫ gK) ≫ ιK := by
    rw [Category.assoc, ← jX_f' K gK f q, ← Category.assoc, ← pullback.condition, Category.assoc, j_f']
  let r : pullback (j K gK f q) (jX K gK f q) ⟶ pullback f ιK :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ gK) hr
  have hrq : r ≫ q.1 = pullback.snd (j K gK f q) (jX K gK f q) := by
    rw [← cancel_mono (jX K gK f q), Category.assoc, q_jX, ← fst_j, ← Category.assoc, pullback.lift_fst,
      pullback.condition]
  have hsr : s ≫ r = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp, q.2]
  have hrs : r ≫ s = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, hrq]
  haveI : IsIso s := ⟨⟨r, hsr, hrs⟩⟩
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso s) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem graph_isClosedImmersion [IsSeparated gK] (w : pullback.fst f ιK ≫ f = q.1 ≫ gK ≫ ιK) :
    IsClosedImmersion (pullback.lift (pullback.fst f ιK) q.1 w : pullback f ιK ⟶ pullback f (gK ≫ ιK)) := by
  let Γ : pullback f ιK ⟶ pullback (q.1 ≫ gK) gK := pullback.lift (𝟙 _) q.1 (Category.id_comp _)
  have hΓ : IsClosedImmersion Γ := inferInstance
  let c : pullback (q.1 ≫ gK) gK ≅ pullback (pullback.snd f ιK) gK := pullback.congrHom q.2 rfl
  let G : pullback (pullback.snd f ιK) gK ≅ pullback f (gK ≫ ιK) := pullbackLeftPullbackSndIso f ιK gK
  have heq : pullback.lift (pullback.fst f ιK) q.1 w = Γ ≫ c.hom ≫ G.hom := by
    apply pullback.hom_ext
    · simp only [Γ, c, G, Category.assoc, pullback.lift_fst, pullbackLeftPullbackSndIso_hom_fst,
        pullback.congrHom_hom, pullback.lift_fst_assoc, Category.comp_id, Category.id_comp]
    · simp only [Γ, c, G, Category.assoc, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd,
        pullback.congrHom_hom, Category.comp_id]
  rw [heq]
  infer_instance

theorem sep [IsSeparated gK] [IsSeparated f] : IsSeparated (f' K gK f q) :=
  AlgebraicGeometry.isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
    (f' K gK f q) (j K gK f q) (jX K gK f q) (Set.eq_univ_of_forall fun y => cover K gK f q y)
    f (gK ≫ ιK) (j_f' K gK f q) (jX_f' K gK f q)
    (pullback.fst f ιK) q.1 (isPullback K gK f q) (graph_isClosedImmersion K gK f q _)

end Main

end Completion21
p2m_reactivate "P2MW.S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart.Completion21"

open Completion21 in

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (q : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion q.1] :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ Y') (hj : j ≫ f' = f)
      (e : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K)) gK),
      IsOpenImmersion j ∧ IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧ IsIso e.1 ∧
      (∀ y' : Y', f'.base y' = IsLocalRing.closedPoint R → y' ∈ Set.range j.base) ∧
      schemeHomOverComp (genericFibreRestrict R K f' f ⟨j, hj⟩) e = q ∧
      (Smooth gK → Smooth f → Smooth f') := by
  refine ⟨Y' K gK f q, f' K gK f q, j K gK f q, j_f' K gK f q, e K gK f q, inferInstance, sep K gK f q,
    lft K gK f q, qc K gK f q, inferInstance, special K gK f q, comp_e K gK f q, fun h₁ h₂ => smooth K gK f q h₁ h₂⟩

end S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
end P2MW
export P2MW.S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart (solution)
