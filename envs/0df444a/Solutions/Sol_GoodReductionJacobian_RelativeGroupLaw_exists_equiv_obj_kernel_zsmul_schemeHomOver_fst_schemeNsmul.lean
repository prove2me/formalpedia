-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d39c2eaf-bea6-55b8-9149-253496c79f3a

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul.CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian"
universe w v

namespace S17KerSec

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

noncomputable def kerObjIso {F G : Sheaf J Ab.{w}} (f : F ⟶ G) (U : Cᵒᵖ) :
    (kernel f).obj.obj U ≅ AddCommGrpCat.of ((f.hom.app U).hom).ker :=
  ((PreservesKernel.iso (sheafToPresheaf J Ab.{w}) f).app U).trans
    ((PreservesKernel.iso ((evaluation Cᵒᵖ Ab.{w}).obj U) f.hom).trans
      (AddCommGrpCat.kernelIsoKer (f.hom.app U)))

theorem kerObjIso_hom_apply {F G : Sheaf J Ab.{w}} (f : F ⟶ G) (U : Cᵒᵖ) (x : (kernel f).obj.obj U) :
    (kerObjIso J f U).hom x = (AddCommGrpCat.kernelIsoKer (f.hom.app U)).hom
      (kernelComparison f.hom ((evaluation Cᵒᵖ Ab.{w}).obj U) ((kernelComparison f (sheafToPresheaf J Ab.{w})).app U x)) := by
  have e0 : (kerObjIso J f U).hom = (kernelComparison f (sheafToPresheaf J Ab.{w})).app U ≫
      (kernelComparison f.hom ((evaluation Cᵒᵖ Ab.{w}).obj U) ≫ (AddCommGrpCat.kernelIsoKer (f.hom.app U)).hom) := by
    simp only [kerObjIso, Iso.trans_hom, Iso.app_hom, PreservesKernel.iso_hom]
  rw [e0]
  rfl

end S17KerSec

namespace CategoryTheory p2m_export "CategoryTheory" "Category sheafToPresheaf ConcreteCategory.congr_hom MorphismProperty.Over.w MorphismProperty.Over MorphismProperty NatTrans Injective inv Iso.app_hom over evaluation NatTrans.app Sheaf Over Iso.trans_hom ConcreteCategory.comp_apply comp_apply GrothendieckTopology Over.w ConcreteCategory bijection NatTrans.comp_app Iso NatTrans.app_zsmul Category.assoc" namespace Sheaf p2m_export "CategoryTheory.Sheaf" "over val" end CategoryTheory.Sheaf
p2m_open_scoped "CategoryTheory CategoryTheory.Sheaf" in

theorem CategoryTheory.Sheaf.exists_addEquiv_obj_kernel_forall_coe_eq_ι_app
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G : Sheaf J Ab.{w}} (f : F ⟶ G) :
    ∃ e : ∀ U : Cᵒᵖ, (kernel f).obj.obj U ≃+ ((f.hom.app U).hom).ker,
      ∀ (U : Cᵒᵖ) (x : (kernel f).obj.obj U), ((e U x : ((f.hom.app U).hom).ker) : F.obj.obj U) = (kernel.ι f).hom.app U x := by
  refine ⟨fun U => (S17KerSec.kerObjIso J f U).addCommGroupIsoToAddEquiv, fun U x => ?_⟩

  have step0 : ((S17KerSec.kerObjIso J f U).addCommGroupIsoToAddEquiv x : ((f.hom.app U).hom).ker)
      = (S17KerSec.kerObjIso J f U).hom x := rfl
  rw [step0, S17KerSec.kerObjIso_hom_apply]
  set y := kernelComparison f.hom ((evaluation Cᵒᵖ Ab.{w}).obj U)
    ((kernelComparison f (sheafToPresheaf J Ab.{w})).app U x) with hy

  have h3 := ConcreteCategory.congr_hom (AddCommGrpCat.kernelIsoKer_hom_comp_subtype (f.hom.app U)) y
  rw [ConcreteCategory.comp_apply] at h3
  change (AddCommGrpCat.ofHom ((f.hom.app U).hom).ker.subtype) ((AddCommGrpCat.kernelIsoKer (f.hom.app U)).hom y) = _
  rw [h3, hy]

  have h2 := ConcreteCategory.congr_hom (kernelComparison_comp_ι f.hom ((evaluation Cᵒᵖ Ab.{w}).obj U))
    ((kernelComparison f (sheafToPresheaf J Ab.{w})).app U x)
  rw [ConcreteCategory.comp_apply] at h2
  erw [h2]

  have h1 := kernelComparison_comp_ι f (sheafToPresheaf J Ab.{w})
  have h1U := congrArg (fun α => NatTrans.app α U) h1
  simp only [NatTrans.comp_app] at h1U
  have h1x := ConcreteCategory.congr_hom h1U x
  rw [ConcreteCategory.comp_apply] at h1x
  exact h1x

namespace S17TorsSec

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
  (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
  (he_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))

theorem zsmul_id_app (n : ℤ) (U : ((Spec (CommRingCat.of R))).Fppfᵒᵖ) (s : 𝒢.1.obj U) :
    ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)).1.app U s = n • s := by
  have h1 : ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)).1 = n • (𝟙 𝒢 : 𝒢 ⟶ 𝒢).1 :=
    (sheafToPresheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1}).map_zsmul
  have h2 : ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)).1.app U = n • ((𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app U) := by
    rw [h1, NatTrans.app_zsmul]
  rw [h2]
  change (AddCommGrpCat.Hom.hom (n • ((𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app U))) s = n • s
  rw [AddCommGrpCat.hom_zsmul, AddMonoidHom.zsmul_apply]
  rfl

include he_add in
theorem e_zero (U : (Spec (CommRingCat.of R)).Fppf) : e U 0 = G.one U.hom := by
  have h : G.mul U.hom (e U 0) (e U 0) = G.mul U.hom (G.one U.hom) (e U 0) := by
    rw [← he_add, add_zero, G.one_mul]

  have := congrArg (fun z => G.mul U.hom z (G.inv U.hom (e U 0))) h
  rwa [G.mul_assoc, G.mul_assoc, G.mul_inv_cancel, G.mul_one, G.mul_one] at this

include he_add in
theorem e_nsmul (U : (Spec (CommRingCat.of R)).Fppf) (k : ℕ) (s : 𝒢.1.obj (op U)) :
    e U (k • s) = G.nsmul U.hom k (e U s) := by
  induction k with
  | zero => rw [zero_smul, RelativeGroupLaw.nsmul_zero]; exact e_zero G 𝒢 e he_add U
  | succ k ih => rw [add_smul, one_smul, he_add, ih, RelativeGroupLaw.nsmul_succ]

end S17TorsSec

open S17TorsSec in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (k : ℕ) (n : ℤ) (hkn : (k : ℤ) = n) :
    ∃ (LK : RelativeGroupLaw R (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
      (eK : ∀ U : (Spec (CommRingCat.of R)).Fppf,
        (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U) ≃ SchemeHomOver U.hom (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),

      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        LK.mul t x y = LK.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul t x y) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
          G.mul t (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        Function.Injective (fun y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) =>
          NeronModelInfra.schemeHomOverComp y (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f))) ∧

      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
        eK U (s + s') = LK.mul U.hom (eK U s) (eK U s')) ∧
      (∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op V)),
        eK U ((kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.map k.op s) =
          schemeHomOverComp k.left (MorphismProperty.Over.w k) (eK V s)) ∧
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
        NeronModelInfra.schemeHomOverComp (eK U s) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
          e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) s)) := by
  classical

  obtain ⟨LK, hstr, hLKcomm, hLKhom, hLKinj, htors⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff G hcomm k

  obtain ⟨e₁, he₁⟩ := CategoryTheory.Sheaf.exists_addEquiv_obj_kernel_forall_coe_eq_ι_app
    (smallFppfTopology (Spec (CommRingCat.of R))) ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))

  have htor : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (z : 𝒢.1.obj (op U)), n • z = 0 →
      e U z ∈ G.torsionSubset U.hom k := by
    intro U z hz
    change G.nsmul U.hom k (e U z) = G.one U.hom
    rw [← e_nsmul G 𝒢 e he_add, ← e_zero G 𝒢 e he_add U]
    congr 1
    rw [← natCast_zsmul, hkn, hz]
  have hker : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
      n • ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) s) = 0 := by
    intro U s
    have h := (e₁ (op U) s).2
    rw [AddMonoidHom.mem_ker] at h
    rw [← he₁ (op U) s, ← zsmul_id_app 𝒢 n (op U)]
    exact h

  have hex : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
      ∃ y : SchemeHomOver U.hom (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f),
        NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ =
          e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) s) :=
    fun U s => (htors U.hom _).mp (htor U _ (hker U s))
  let eKf : ∀ U : (Spec (CommRingCat.of R)).Fppf,
      (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U) → SchemeHomOver U.hom (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) :=
    fun U s => (hex U s).choose
  have heKf : ∀ U s, NeronModelInfra.schemeHomOverComp (eKf U s) ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ =
      e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) s) := fun U s => (hex U s).choose_spec

  have hιinj : ∀ U : (Spec (CommRingCat.of R)).Fppf, Function.Injective ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U)) := by
    intro U s s' h
    apply (e₁ (op U)).injective
    apply Subtype.ext
    rw [he₁, he₁]
    exact h

  have hinjK : ∀ U, Function.Injective (eKf U) := by
    intro U s s' h
    apply hιinj U
    apply (e U).injective
    rw [← heKf, ← heKf, h]
  have hsurjK : ∀ U, Function.Surjective (eKf U) := by
    intro U y

    set x := NeronModelInfra.schemeHomOverComp y
      (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ :
        SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) with hx
    have hxt : x ∈ G.torsionSubset U.hom k := (htors U.hom x).mpr ⟨y, rfl⟩
    set z := (e U).symm x with hz
    have hz' : e U z = x := (e U).apply_symm_apply x
    have hnz : n • z = 0 := by
      apply (e U).injective
      rw [e_zero G 𝒢 e he_add, ← hkn, natCast_zsmul, e_nsmul G 𝒢 e he_add, hz']
      exact hxt
    have hz1 : (𝟙 𝒢 : 𝒢 ⟶ 𝒢) = 𝟙 𝒢 := rfl
    have hmem : z ∈ ((((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)).1.app (op U)).hom).ker := by
      rw [AddMonoidHom.mem_ker]
      change ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)).1.app (op U) z = 0
      rw [zsmul_id_app]; exact hnz
    refine ⟨(e₁ (op U)).symm ⟨z, hmem⟩, ?_⟩
    apply hLKinj U.hom
    change NeronModelInfra.schemeHomOverComp (eKf U _) _ = NeronModelInfra.schemeHomOverComp y _
    refine (heKf U ((e₁ (op U)).symm ⟨z, hmem⟩)).trans ?_
    rw [← hx, ← hz']
    congr 1
    have := he₁ (op U) ((e₁ (op U)).symm ⟨z, hmem⟩)
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨LK, fun U => Equiv.ofBijective (eKf U) ⟨hinjK U, hsurjK U⟩, hLKcomm, hLKhom, hLKinj, ?_, ?_, ?_⟩
  ·
    intro U s s'
    apply hLKinj U.hom
    change NeronModelInfra.schemeHomOverComp (eKf U (s + s')) _ = NeronModelInfra.schemeHomOverComp (LK.mul U.hom (eKf U s) (eKf U s')) _
    rw [hLKhom]
    refine (heKf U (s + s')).trans ?_
    rw [map_add, he_add]
    congr 1
    · exact (heKf U s).symm
    · exact (heKf U s').symm
  ·
    intro U V j s
    apply hLKinj U.hom
    change NeronModelInfra.schemeHomOverComp (eKf U _) _ = NeronModelInfra.schemeHomOverComp (schemeHomOverComp j.left _ (eKf V s)) _
    refine (heKf U _).trans ?_
    have hnat : (kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) ((kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.map j.op s)
        = 𝒢.1.map j.op ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op V) s) := by
      have := (kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.naturality j.op
      exact (ConcreteCategory.congr_hom this s)
    rw [hnat, he]
    apply Subtype.ext
    have hV := congrArg Subtype.val (heKf V s)
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc] at hV ⊢
    rw [← hV]
  ·
    intro U s
    exact heKf U s

end S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul (solution)
