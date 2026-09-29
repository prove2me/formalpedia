-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/88542429-dcd0-5013-8706-505f9fa07692

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_of_idempotent
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom
import Theorems.Thm_CategoryTheory_Sheaf_exists_iso_of_addEquiv_obj_natural
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

universe w v u

namespace S17SheafHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

noncomputable def ofSections {F G : Sheaf J Ab.{w}} (φ : ∀ U : Cᵒᵖ, F.obj.obj U →+ G.obj.obj U)
    (hφ : ∀ {U V : Cᵒᵖ} (g : U ⟶ V) (x : F.obj.obj U), φ V (F.obj.map g x) = G.obj.map g (φ U x)) : F ⟶ G :=
  (sheafToPresheaf J Ab.{w}).preimage
    { app := fun U => AddCommGrpCat.ofHom (φ U)
      naturality := by
        intro U V g
        ext x
        exact hφ g x }

theorem ofSections_app {F G : Sheaf J Ab.{w}} (φ : ∀ U : Cᵒᵖ, F.obj.obj U →+ G.obj.obj U)
    (hφ : ∀ {U V : Cᵒᵖ} (g : U ⟶ V) (x : F.obj.obj U), φ V (F.obj.map g x) = G.obj.map g (φ U x))
    (U : Cᵒᵖ) (x : F.obj.obj U) : (ofSections φ hφ).hom.app U x = φ U x := by
  have h : (ofSections φ hφ).hom = { app := fun U => AddCommGrpCat.ofHom (φ U), naturality := _ } :=
    (sheafToPresheaf J Ab.{w}).map_preimage _
  rw [h]
  rfl

theorem hom_ext_apply {F G : Sheaf J Ab.{w}} (α β : F ⟶ G)
    (h : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), α.hom.app U x = β.hom.app U x) : α = β := by
  apply (sheafToPresheaf J Ab.{w}).map_injective
  ext U x
  exact h U x

theorem comp_app_apply {F G H : Sheaf J Ab.{w}} (α : F ⟶ G) (β : G ⟶ H) (U : Cᵒᵖ) (x : F.obj.obj U) :
    (α ≫ β).hom.app U x = β.hom.app U (α.hom.app U x) := by
  change ((sheafToPresheaf J Ab.{w}).map (α ≫ β)).app U x = _
  rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app]
  rfl

theorem id_app_apply {F : Sheaf J Ab.{w}} (U : Cᵒᵖ) (x : F.obj.obj U) : (𝟙 F : F ⟶ F).hom.app U x = x := by
  change ((sheafToPresheaf J Ab.{w}).map (𝟙 F)).app U x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

end S17SheafHom

open S17SheafHom in
theorem solution
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of ℤ)} (G : RelativeGroupLaw ℤ f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (g : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map g.op s) = GoodReductionJacobian.schemeHomOverComp g.left (MorphismProperty.Over.w g) (e V s))
    (k : ℕ) (n : ℤ) (hkn : (k : ℤ) = n)

    (ρs : 𝒢 ⟶ 𝒢) (φ : SchemeHomOver f f)
    (hφ_sec : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U (ρs.1.app (op U) s)).1 = (e U s).1 ≫ φ.1)
    (eKm : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f))
    (heKm_idem : eKm.1 ≫ eKm.1 = eKm.1)
    (heφ : eKm.1 ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φ.1)
    (heKm_hom : ∀ (LK : RelativeGroupLaw ℤ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
      (∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f) f) =
          G.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
      ∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) eKm =
          LK.mul s (NeronModelInfra.schemeHomOverComp x eKm) (NeronModelInfra.schemeHomOverComp y eKm))

    (E : Scheme.{0}) (gX : E ⟶ (Spec (CommRingCat.of ℤ))) (i : E ⟶ A) (j : E ⟶ G.schemeKer k)
    (LE : RelativeGroupLaw ℤ gX)
    (hi : i ≫ f = gX) [IsClosedImmersion i] (hj : j ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = i) [IsClosedImmersion j]
    [IsAffineHom gX] [Flat gX] [LocallyOfFiniteType gX]
    (hfix : ∀ (hj' : j ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f = gX) {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp x eKm = x ↔
        ∃ y : SchemeHomOver s gX, NeronModelInfra.schemeHomOverComp y (⟨j, hj'⟩ : SchemeHomOver gX (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)) = x)
    (hcommE : ∀ {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX), LE.mul t x y = LE.mul t y x)
    (hi_hom : ∀ (hi' : i ≫ f = gX) {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX),
      NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, hi'⟩ : SchemeHomOver gX f) =
        G.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, hi'⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, hi'⟩))
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gX)
    (hePts_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LE.mul _ (ePts T φ) (ePts T ψ))
    (hePts_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1)
    (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (sE : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (hsE : ∀ {U V : specInt.Fppf} (g : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sE U (𝒥.1.map g.op s))) h = (Scheme.Γ.map g.left.op) ((Additive.toMul (sE V s)) h)) :
    ∃ (ι : 𝒥 ⟶ kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))) (π : kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)) ⟶ 𝒥)
      (w : (n • 𝟙 𝒢) ≫ ρs = ρs ≫ (n • 𝟙 𝒢)),
      ι ≫ π = 𝟙 𝒥 ∧
      π ≫ ι = kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w ∧
      (∀ (U : specInt.Fppf) (x : 𝒥.1.obj (op U)),
        (e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) (ι.1.app (op U) x))).1 =
          U.left.toSpecΓ ≫ (ePts Γ(U.left, ⊤) (Additive.toMul (sE U x))).1 ≫ i) := by
  classical

  subst hi
  subst hj

  have w : (n • 𝟙 𝒢) ≫ ρs = ρs ≫ (n • 𝟙 𝒢) := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, Category.comp_id]

  obtain ⟨LK, eK, hLKcomm, hLKhom, hLKinj, heK_add, heK_nat, heK_ι⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul
      G hcomm 𝒢 e he_add he k n hkn

  obtain ⟨𝒢E, eE, heE_add, heE_nat, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative LE
      (fun t x y => hcommE t x y)

  have hρs : ∀ (U : specInt.Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
      eK U ((kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w).1.app (op U) s) = NeronModelInfra.schemeHomOverComp (eK U s) eKm := by
    intro U s
    apply hLKinj U.hom
    change NeronModelInfra.schemeHomOverComp (eK U _) _ = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (eK U s) eKm) _
    rw [heK_ι]
    have hkm : (kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w) ≫ kernel.ι (n • 𝟙 𝒢) = kernel.ι (n • 𝟙 𝒢) ≫ ρs :=
      kernel.lift_ι _ _ _
    have h1 : (kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) ((kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w).1.app (op U) s)
        = ρs.1.app (op U) ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) s) := by
      rw [← comp_app_apply, ← comp_app_apply, hkm]
    rw [h1]
    apply Subtype.ext
    rw [hφ_sec]
    have h2 := congrArg Subtype.val (heK_ι U s)
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc] at h2 ⊢
    rw [← h2, heφ]
    exact Category.assoc _ _ _

  have hj_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t (j ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f))),
      NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)) =
        LK.mul t (NeronModelInfra.schemeHomOverComp x ⟨j, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨j, rfl⟩) := by
    intro T t x y
    apply hLKinj t
    change NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (LE.mul t x y) _) _ = NeronModelInfra.schemeHomOverComp (LK.mul t _ _) _
    rw [hLKhom, NeronModelInfra.schemeHomOverComp_assoc, NeronModelInfra.schemeHomOverComp_assoc,
      NeronModelInfra.schemeHomOverComp_assoc]
    have e3 : NeronModelInfra.schemeHomOverComp (⟨j, rfl⟩ : SchemeHomOver (j ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f))
        (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f) f) = (⟨j ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (j ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)) f) := by
      apply Subtype.ext; simp only [NeronModelInfra.schemeHomOverComp_coe]
    rw [e3]
    exact hi_hom rfl t x y

  obtain ⟨ι₀, π₀, hιπ₀, hπι₀, hι₀, hπ₀⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_of_idempotent
      G 𝒢 e he_add he k n hkn LK hLKhom hLKinj eK heK_add heK_nat ρs w eKm heKm_idem (heKm_hom LK hLKhom) hρs
      E j LE hj_hom (fun t x => hfix rfl t x) 𝒢E eE heE_add heE_nat

  obtain ⟨eU, heU, heU_mul, heU_nat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_equiv_schemeHomOver_withConv_algHom_of_isAffineHom
      LE H ePts hePts_mul hePts_nat

  let θf : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) → 𝒢E.1.obj (op U) :=
    fun U x => (eE U).symm ((eU U.left U.hom).symm (Additive.toMul (sE U x)))
  have hθf : ∀ U x, eE U (θf U x) = (eU U.left U.hom).symm (Additive.toMul (sE U x)) :=
    fun U x => (eE U).apply_symm_apply _
  have heU_symm_mul : ∀ (U : specInt.Fppf) (a b : WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))),
      (eU U.left U.hom).symm (a * b) = LE.mul U.hom ((eU U.left U.hom).symm a) ((eU U.left U.hom).symm b) := by
    intro U a b
    apply (eU U.left U.hom).injective
    refine Eq.trans ?_ (heU_mul U.left U.hom ((eU U.left U.hom).symm a) ((eU U.left U.hom).symm b)).symm
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hθf_add : ∀ U x x', θf U (x + x') = θf U x + θf U x' := by
    intro U x x'
    apply (eE U).injective
    rw [hθf, heE_add, hθf, hθf, map_add, toMul_add, heU_symm_mul]
  have hθf_nat : ∀ {U V : specInt.Fppf} (g : U ⟶ V) (x : 𝒥.1.obj (op V)),
      θf U (𝒥.1.map g.op x) = 𝒢E.1.map g.op (θf V x) := by
    intro U V g x
    apply (eE U).injective
    rw [hθf, heE_nat, hθf]
    apply (eU U.left U.hom).injective
    rw [Equiv.apply_symm_apply]

    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    rw [hsE g x h]
    refine Eq.trans ?_ (heU_nat V.left U.left V.hom U.hom g.left (MorphismProperty.Over.w g)
      ((eU V.left V.hom).symm (Additive.toMul (sE V x))) h).symm
    rw [Equiv.apply_symm_apply]
  let θeq : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃ 𝒢E.1.obj (op U) :=
    fun U => ((sE U).toEquiv.trans Additive.toMul).trans (((eU U.left U.hom).symm).trans (eE U).symm)
  have hθeq : ∀ U x, θeq U x = θf U x := fun U x => rfl
  obtain ⟨Θ, hΘ⟩ := CategoryTheory.Sheaf.exists_iso_of_addEquiv_obj_natural (smallFppfTopology specInt) 𝒥 𝒢E
    (fun U => AddEquiv.mk' (θeq U.unop) (fun x x' => hθf_add U.unop x x'))
    (fun {U V} g x => hθf_nat g.unop x)
  have hΘapp : ∀ (U : specInt.Fppf) (x : 𝒥.1.obj (op U)), Θ.hom.1.app (op U) x = θf U x := fun U x => hΘ (op U) x
  refine ⟨Θ.hom ≫ ι₀, π₀ ≫ Θ.inv, w, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc ι₀, hιπ₀, Category.id_comp, Iso.hom_inv_id]
  · rw [Category.assoc, ← Category.assoc Θ.inv, Iso.inv_hom_id, Category.id_comp, hπι₀]
  · intro U x
    rw [comp_app_apply, hΘapp]
    have eA := congrArg Subtype.val (heK_ι U (ι₀.1.app (op U) (θf U x)))
    have eB := congrArg Subtype.val (hι₀ U (θf U x))
    have eC : (eE U (θf U x)).1 = U.left.toSpecΓ ≫ (ePts Γ(U.left, ⊤) (Additive.toMul (sE U x))).1 := by
      rw [hθf]
      refine (heU U.left U.hom ((eU U.left U.hom).symm (Additive.toMul (sE U x)))).trans ?_
      rw [Equiv.apply_symm_apply]
    simp only [NeronModelInfra.schemeHomOverComp_coe] at eA eB
    calc (e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) (ι₀.1.app (op U) (θf U x)))).1
        = (eK U (ι₀.1.app (op U) (θf U x))).1 ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := eA.symm
      _ = ((eE U (θf U x)).1 ≫ j) ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 :=
          congrArg (· ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) eB
      _ = ((U.left.toSpecΓ ≫ (ePts Γ(U.left, ⊤) (Additive.toMul (sE U x))).1) ≫ j) ≫
            pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 :=
          congrArg (fun z => (z ≫ j) ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) eC
      _ = U.left.toSpecΓ ≫ (ePts Γ(U.left, ⊤) (Additive.toMul (sE U x))).1 ≫ j ≫
            pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
          simp only [Category.assoc]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent (solution)
