-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c3895c16-2a2e-5fe1-9a82-babb81f94d17

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul smooth_of_geometricallyReduced_of_locallyOfFiniteType"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Represent

variable {k : Type u} [CommRing k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.one_natural' {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  have h := L.mul_natural t t' ψ hψ (L.one t) (L.one t)
  rw [L.one_mul] at h

  have : (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) : SchemeHomOver t' f) =
      (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t)) * (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t)) := h
  exact left_eq_mul.mp this |>.symm ▸ rfl

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "one_natural'"

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.inv_natural' {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  have h := L.mul_natural t t' ψ hψ (L.inv t x) x
  rw [L.inv_mul_cancel, one_natural'] at h

  exact (eq_inv_of_mul_eq_one_left h.symm : _)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "inv_natural'"

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.mulMor : pullback f f ⟶ J :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mulMor"
theorem mulMor_over : L.mulMor ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

noncomputable def pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y : SchemeHomOver t f) : T ⟶ pullback f f :=
  pullback.lift x.1 y.1 (x.2.trans y.2.symm)

@[scoped simp] theorem pair_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y : SchemeHomOver t f) :
    pair x y ≫ pullback.fst f f = x.1 := pullback.lift_fst _ _ _
@[scoped simp] theorem pair_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y : SchemeHomOver t f) :
    pair x y ≫ pullback.snd f f = y.1 := pullback.lift_snd _ _ _

theorem mul_eq_pair_mulMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) :
    (L.mul t x y).1 = pair x y ≫ L.mulMor := by
  have h := L.mul_natural (pullback.fst f f ≫ f) t (pair x y) (by rw [← Category.assoc, pair_fst, x.2])
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have hx : GoodReductionJacobian.schemeHomOverComp (pair x y) (by rw [← Category.assoc, pair_fst, x.2])
      (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = x := Subtype.ext (pair_fst x y)
  have hy : GoodReductionJacobian.schemeHomOverComp (pair x y) (by rw [← Category.assoc, pair_fst, x.2])
      (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = y :=
    Subtype.ext (pair_snd x y)
  rw [hx, hy] at h
  rw [← h]; rfl

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.invMor : J ⟶ J := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).1

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "invMor"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.invMor_over : L.invMor ≫ f = f := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).2

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "invMor_over"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.inv_eq_comp_invMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f) :
    (L.inv t x).1 = x.1 ≫ L.invMor := by
  have h := L.inv_natural' f t x.1 x.2 ⟨𝟙 J, Category.id_comp f⟩
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]; rfl

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "inv_eq_comp_invMor"

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.oneMor : Spec (CommRingCat.of k) ⟶ J := (L.one (𝟙 _)).1

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "oneMor"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.oneMor_over : L.oneMor ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "oneMor_over"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.one_eq_comp_oneMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    (L.one t).1 = t ≫ L.oneMor := by
  have h := L.one_natural' (𝟙 _) t t (Category.comp_id t)
  rw [← h]; rfl

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "one_eq_comp_oneMor"
end Represent

end GoodReductionJacobian.RelativeGroupLaw
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace ImageHom
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Image

variable {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
  (hJ : AbelianSchemePropertyBundle k f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] (σ : SchemeHomOver g f)

include hJ in
theorem isProper_val : IsProper σ.1 := by
  have : IsProper (σ.1 ≫ f) := by rw [σ.2]; infer_instance
  have : IsProper f := hJ.proper
  exact IsProper.of_comp σ.1 f

include hJ in
theorem quasiCompact_val : QuasiCompact σ.1 := by
  have := isProper_val hJ σ; infer_instance

include hJ in

theorem surjective_toImage : Function.Surjective σ.1.toImage := by
  have := isProper_val hJ σ
  intro b
  have hb : σ.1.imageι b ∈ (σ.1.ker.support : Set J) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨b, rfl⟩
  rw [Scheme.Hom.support_ker, (σ.1.isClosedMap.isClosed_range).closure_eq] at hb
  obtain ⟨x, hx⟩ := hb
  refine ⟨x, σ.1.imageι.isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι, hx]

include hJ in
theorem surjective_toImage' : Surjective σ.1.toImage := ⟨surjective_toImage hJ σ⟩

include hJ in

theorem isSchemeTheoreticallyDominant_toImage : IsSchemeTheoreticallyDominant σ.1.toImage := by
  have := quasiCompact_val hJ σ
  rw [isSchemeTheoreticallyDominant_iff]

  let U : J.affineOpens → σ.1.image.affineOpens := fun V => ⟨σ.1.imageι ⁻¹ᵁ V.1, V.2.preimage σ.1.imageι⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ ?_
  · rw [← top_le_iff]
    intro b _
    obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := J.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (σ.1.imageι b)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hbV⟩
  · intro V
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
    intro s hs
    exact (σ.1.toImage_app_injective V ((RingHom.mem_ker).mp hs |>.trans (map_zero _).symm) : _)

end Image
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw"

end GoodReductionJacobian.RelativeGroupLaw.ImageHom
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace ImageHom
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Closure

variable {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  (hJ : AbelianSchemePropertyBundle k f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] (LX : RelativeGroupLaw k g)
  (σ : SchemeHomOver g f)
  (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))

noncomputable def toImageOver : SchemeHomOver g (σ.1.imageι ≫ f) :=
  ⟨σ.1.toImage, by rw [← Category.assoc, Scheme.Hom.toImage_imageι]; exact σ.2⟩

noncomputable def imageιOver : SchemeHomOver (σ.1.imageι ≫ f) f := ⟨σ.1.imageι, rfl⟩

@[scoped simp] theorem toImageOver_coe : (toImageOver σ).1 = σ.1.toImage := rfl
@[scoped simp] theorem imageιOver_coe : (imageιOver σ).1 = σ.1.imageι := rfl

theorem comp_toImageOver_imageιOver :
    NeronModelInfra.schemeHomOverComp (toImageOver σ) (imageιOver σ) = σ :=
  Subtype.ext σ.1.toImage_imageι

include hσ in

theorem comp_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    NeronModelInfra.schemeHomOverComp (LX.one t) σ = L.one t := by
  letI := L.pointGroup t
  have h := hσ t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h
  have : (NeronModelInfra.schemeHomOverComp (LX.one t) σ : SchemeHomOver t f) =
      NeronModelInfra.schemeHomOverComp (LX.one t) σ * NeronModelInfra.schemeHomOverComp (LX.one t) σ := h
  exact (left_eq_mul.mp this).symm ▸ rfl

include hσ in

theorem comp_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t g) :
    NeronModelInfra.schemeHomOverComp (LX.inv t x) σ = L.inv t (NeronModelInfra.schemeHomOverComp x σ) := by
  letI := L.pointGroup t
  have h := hσ t (LX.inv t x) x
  rw [LX.inv_mul_cancel, comp_one L LX σ hσ] at h
  exact (eq_inv_of_mul_eq_one_left h.symm : _)

noncomputable def mulJB : pullback (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ⟶ J :=
  (L.mul (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f)
    ⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩).1

theorem mulJB_over : mulJB L σ ≫ f = pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f :=
  (L.mul _ _ _).2

noncomputable def prodToImage : pullback g g ⟶ pullback (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) :=
  pullback.map g g (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) σ.1.toImage σ.1.toImage (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc, Scheme.Hom.toImage_imageι]; exact σ.2.symm)
    (by rw [Category.comp_id, ← Category.assoc, Scheme.Hom.toImage_imageι]; exact σ.2.symm)

@[scoped simp] theorem prodToImage_fst : prodToImage σ ≫ pullback.fst _ _ = pullback.fst g g ≫ σ.1.toImage :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem prodToImage_snd : prodToImage σ ≫ pullback.snd _ _ = pullback.snd g g ≫ σ.1.toImage :=
  pullback.lift_snd _ _ _

include hσ in
theorem prodToImage_mulJB :
    prodToImage σ ≫ mulJB L σ = (LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
      ⟨pullback.snd g g, pullback.condition.symm⟩).1 ≫ σ.1 := by
  have hover : prodToImage σ ≫ pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f = pullback.fst g g ≫ g := by
    rw [← Category.assoc, prodToImage_fst, Category.assoc, ← Category.assoc σ.1.toImage, Scheme.Hom.toImage_imageι, σ.2]
  have h := L.mul_natural _ (pullback.fst g g ≫ g) (prodToImage σ) hover
    ⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (prodToImage σ) hover
      (⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩ : SchemeHomOver (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f) f) =
      NeronModelInfra.schemeHomOverComp (⟨pullback.fst g g, rfl⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) σ := by
    apply Subtype.ext
    change prodToImage σ ≫ pullback.fst _ _ ≫ σ.1.imageι = pullback.fst g g ≫ σ.1
    rw [← Category.assoc, prodToImage_fst, Category.assoc, Scheme.Hom.toImage_imageι]
  have h2 : GoodReductionJacobian.schemeHomOverComp (prodToImage σ) hover
      (⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f) f) =
      NeronModelInfra.schemeHomOverComp (⟨pullback.snd g g, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) σ := by
    apply Subtype.ext
    change prodToImage σ ≫ pullback.snd _ _ ≫ σ.1.imageι = pullback.snd g g ≫ σ.1
    rw [← Category.assoc, prodToImage_snd, Category.assoc, Scheme.Hom.toImage_imageι]
  rw [h1, h2, ← hσ] at h
  exact congrArg Subtype.val h

include hJ in

theorem isSchemeTheoreticallyDominant_prodToImage : IsSchemeTheoreticallyDominant (prodToImage σ) := by
  have hdom := isSchemeTheoreticallyDominant_toImage hJ σ
  have hqc : QuasiCompact σ.1.toImage := by have := quasiCompact_val hJ σ; infer_instance
  have hπ : σ.1.toImage ≫ σ.1.imageι ≫ f = g := by rw [← Category.assoc, Scheme.Hom.toImage_imageι]; exact σ.2

  have t₁ := IsPullback.of_hasPullback (σ.1.imageι ≫ f) g
  have s₁ : IsPullback (pullback.fst g g) (pullback.snd g g) (σ.1.toImage ≫ σ.1.imageι ≫ f) g := by
    rw [hπ]; exact IsPullback.of_hasPullback g g
  have H₁ := IsPullback.of_bot' s₁ t₁
  haveI : IsSchemeTheoreticallyDominant (t₁.lift (pullback.fst g g ≫ σ.1.toImage) (pullback.snd g g)
      (by rw [Category.assoc, s₁.w])) := IsSchemeTheoreticallyDominant.of_isPullback H₁

  have t₂ := (IsPullback.of_hasPullback (σ.1.imageι ≫ f) (σ.1.imageι ≫ f)).flip
  have s₂ : IsPullback (pullback.snd (σ.1.imageι ≫ f) g) (pullback.fst (σ.1.imageι ≫ f) g)
      (σ.1.toImage ≫ σ.1.imageι ≫ f) (σ.1.imageι ≫ f) := by
    rw [hπ]; exact (IsPullback.of_hasPullback (σ.1.imageι ≫ f) g).flip
  have H₂ := IsPullback.of_bot' s₂ t₂
  haveI : IsSchemeTheoreticallyDominant (t₂.lift (pullback.snd (σ.1.imageι ≫ f) g ≫ σ.1.toImage)
      (pullback.fst (σ.1.imageι ≫ f) g) (by rw [Category.assoc, s₂.w])) := IsSchemeTheoreticallyDominant.of_isPullback H₂

  have heq : prodToImage σ = t₁.lift (pullback.fst g g ≫ σ.1.toImage) (pullback.snd g g) (by rw [Category.assoc, s₁.w]) ≫
      t₂.lift (pullback.snd (σ.1.imageι ≫ f) g ≫ σ.1.toImage) (pullback.fst (σ.1.imageι ≫ f) g)
        (by rw [Category.assoc, s₂.w]) := by
    apply pullback.hom_ext
    · rw [prodToImage_fst, Category.assoc, t₂.lift_snd, t₁.lift_fst]
    · rw [prodToImage_snd, Category.assoc, t₂.lift_fst, t₁.lift_snd_assoc]
  rw [heq]; infer_instance

include hJ hσ in
theorem ker_le_ker_mulJB : σ.1.ker ≤ (mulJB L σ).ker := by
  have hdom := isSchemeTheoreticallyDominant_prodToImage hJ σ
  calc σ.1.ker = (⊥ : X.IdealSheafData).map σ.1 := (Scheme.IdealSheafData.map_bot _).symm
    _ ≤ ((LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩).1.ker).map σ.1 :=
        Scheme.IdealSheafData.map_mono _ bot_le
    _ = ((LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩).1 ≫ σ.1).ker :=
        (Scheme.Hom.ker_comp _ _).symm
    _ = (prodToImage σ ≫ mulJB L σ).ker := by rw [prodToImage_mulJB L LX σ hσ]
    _ = (prodToImage σ).ker.map (mulJB L σ) := Scheme.Hom.ker_comp _ _
    _ = (mulJB L σ).ker := by rw [hdom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

noncomputable def invJB : σ.1.image ⟶ J := σ.1.imageι ≫ L.invMor

include hJ hσ in
theorem ker_le_ker_invJB : σ.1.ker ≤ (invJB L σ).ker := by
  have hdom := isSchemeTheoreticallyDominant_toImage hJ σ
  have hcomp : σ.1.toImage ≫ invJB L σ = LX.invMor ≫ σ.1 := by
    change σ.1.toImage ≫ σ.1.imageι ≫ L.invMor = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, ← L.inv_eq_comp_invMor g σ]
    have h := comp_inv L LX σ hσ g ⟨𝟙 X, Category.id_comp g⟩
    have hx : NeronModelInfra.schemeHomOverComp (⟨𝟙 X, Category.id_comp g⟩ : SchemeHomOver g g) σ = σ :=
      Subtype.ext (Category.id_comp _)
    rw [hx] at h
    rw [← h]; rfl
  calc σ.1.ker = (⊥ : X.IdealSheafData).map σ.1 := (Scheme.IdealSheafData.map_bot _).symm
    _ ≤ (LX.invMor.ker).map σ.1 := Scheme.IdealSheafData.map_mono _ bot_le
    _ = (LX.invMor ≫ σ.1).ker := (Scheme.Hom.ker_comp _ _).symm
    _ = (σ.1.toImage ≫ invJB L σ).ker := by rw [hcomp]
    _ = (σ.1.toImage).ker.map (invJB L σ) := Scheme.Hom.ker_comp _ _
    _ = (invJB L σ).ker := by rw [hdom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

noncomputable def mulB : pullback (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ⟶ σ.1.image :=
  IsClosedImmersion.lift σ.1.imageι (mulJB L σ) ((Scheme.IdealSheafData.ker_subschemeι _).trans_le (ker_le_ker_mulJB L hJ LX σ hσ))

theorem mulB_imageι : mulB L hJ LX σ hσ ≫ σ.1.imageι = mulJB L σ := IsClosedImmersion.lift_fac _ _ _

noncomputable def invB : σ.1.image ⟶ σ.1.image :=
  IsClosedImmersion.lift σ.1.imageι (invJB L σ) ((Scheme.IdealSheafData.ker_subschemeι _).trans_le (ker_le_ker_invJB L hJ LX σ hσ))

theorem invB_imageι : invB L hJ LX σ hσ ≫ σ.1.imageι = σ.1.imageι ≫ L.invMor := IsClosedImmersion.lift_fac _ _ _

noncomputable def oneB : Spec (CommRingCat.of k) ⟶ σ.1.image := LX.oneMor ≫ σ.1.toImage

include hσ in
theorem oneB_imageι : oneB LX σ ≫ σ.1.imageι = L.oneMor := by
  change (LX.oneMor ≫ σ.1.toImage) ≫ σ.1.imageι = _
  rw [Category.assoc, Scheme.Hom.toImage_imageι]
  have h := comp_one L LX σ hσ (𝟙 _)
  exact congrArg Subtype.val h

end Closure
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw"

end GoodReductionJacobian.RelativeGroupLaw.ImageHom
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace ImageHom
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section GroupLaw

variable {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  (hJ : AbelianSchemePropertyBundle k f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] (LX : RelativeGroupLaw k g)
  (σ : SchemeHomOver g f)
  (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))

noncomputable def incl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (σ.1.imageι ≫ f)) :
    SchemeHomOver t f :=
  NeronModelInfra.schemeHomOverComp x (imageιOver σ)

@[scoped simp] theorem incl_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (σ.1.imageι ≫ f)) :
    (incl σ x).1 = x.1 ≫ σ.1.imageι := rfl

theorem incl_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (incl σ (T := T) (t := t)) := fun x y h =>
  Subtype.ext ((cancel_mono σ.1.imageι).mp (congrArg Subtype.val h))

theorem incl_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t (σ.1.imageι ≫ f)) :
    incl σ (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = GoodReductionJacobian.schemeHomOverComp ψ hψ (incl σ x) :=
  Subtype.ext (Category.assoc _ _ _)

noncomputable def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)) :
    SchemeHomOver t (σ.1.imageι ≫ f) :=
  ⟨pair x y ≫ mulB L hJ LX σ hσ, by
    rw [Category.assoc, ← Category.assoc (mulB L hJ LX σ hσ), mulB_imageι, mulJB_over, ← Category.assoc, pair_fst]
    exact x.2⟩

theorem incl_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)) :
    incl σ (mulPt L hJ LX σ hσ t x y) = L.mul t (incl σ x) (incl σ y) := by
  have hψ : pair x y ≫ pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f = t := by
    rw [← Category.assoc, pair_fst]; exact x.2
  have h := L.mul_natural _ t (pair x y) hψ
    ⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pair x y) hψ
      (⟨pullback.fst _ _ ≫ σ.1.imageι, by rw [Category.assoc]⟩ :
        SchemeHomOver (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f) f) = incl σ x := by
    apply Subtype.ext; change pair x y ≫ pullback.fst _ _ ≫ σ.1.imageι = x.1 ≫ σ.1.imageι
    rw [← Category.assoc, pair_fst]
  have h2 : GoodReductionJacobian.schemeHomOverComp (pair x y) hψ
      (⟨pullback.snd _ _ ≫ σ.1.imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst (σ.1.imageι ≫ f) (σ.1.imageι ≫ f) ≫ σ.1.imageι ≫ f) f) = incl σ y := by
    apply Subtype.ext; change pair x y ≫ pullback.snd _ _ ≫ σ.1.imageι = y.1 ≫ σ.1.imageι
    rw [← Category.assoc, pair_snd]
  rw [h1, h2] at h
  rw [← h]
  apply Subtype.ext
  change (pair x y ≫ mulB L hJ LX σ hσ) ≫ σ.1.imageι = pair x y ≫ mulJB L σ
  rw [Category.assoc, mulB_imageι]

noncomputable def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (σ.1.imageι ≫ f) :=
  ⟨t ≫ oneB LX σ, by
    rw [Category.assoc, ← Category.assoc (oneB LX σ), oneB_imageι L LX σ hσ, L.oneMor_over, Category.comp_id]⟩

theorem incl_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : incl σ (onePt L LX σ hσ t) = L.one t := by
  apply Subtype.ext
  change (t ≫ oneB LX σ) ≫ σ.1.imageι = (L.one t).1
  rw [Category.assoc, oneB_imageι L LX σ hσ, L.one_eq_comp_oneMor]

noncomputable def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (σ.1.imageι ≫ f)) :
    SchemeHomOver t (σ.1.imageι ≫ f) :=
  ⟨x.1 ≫ invB L hJ LX σ hσ, by
    rw [Category.assoc, ← Category.assoc (invB L hJ LX σ hσ), invB_imageι, Category.assoc, L.invMor_over]
    exact x.2⟩

theorem incl_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (σ.1.imageι ≫ f)) :
    incl σ (invPt L hJ LX σ hσ t x) = L.inv t (incl σ x) := by
  apply Subtype.ext
  change (x.1 ≫ invB L hJ LX σ hσ) ≫ σ.1.imageι = (L.inv t (incl σ x)).1
  rw [Category.assoc, invB_imageι, L.inv_eq_comp_invMor, incl_coe, Category.assoc]

noncomputable def lawB : RelativeGroupLaw k (σ.1.imageι ≫ f) where
  mul t x y := mulPt L hJ LX σ hσ t x y
  one t := onePt L LX σ hσ t
  inv t x := invPt L hJ LX σ hσ t x
  mul_assoc t x y z := incl_injective σ (by rw [incl_mulPt, incl_mulPt, incl_mulPt, incl_mulPt, L.mul_assoc])
  one_mul t x := incl_injective σ (by rw [incl_mulPt, incl_onePt, L.one_mul])
  mul_one t x := incl_injective σ (by rw [incl_mulPt, incl_onePt, L.mul_one])
  inv_mul_cancel t x := incl_injective σ (by rw [incl_mulPt, incl_invPt, incl_onePt, L.inv_mul_cancel])
  mul_natural t t' ψ hψ x y := incl_injective σ (by
    rw [incl_comp, incl_mulPt, incl_mulPt, incl_comp, incl_comp, L.mul_natural])

theorem lawB_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)) :
    (lawB L hJ LX σ hσ).mul t x y = mulPt L hJ LX σ hσ t x y := rfl

include hσ in
theorem lawB_comm (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)) :
    (lawB L hJ LX σ hσ).mul t x y = (lawB L hJ LX σ hσ).mul t y x :=
  incl_injective σ (by rw [lawB_mul, lawB_mul, incl_mulPt, incl_mulPt, hcomm])

theorem lawB_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)) :
    NeronModelInfra.schemeHomOverComp ((lawB L hJ LX σ hσ).mul t x y) (imageιOver σ) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (imageιOver σ)) (NeronModelInfra.schemeHomOverComp y (imageιOver σ)) :=
  incl_mulPt L hJ LX σ hσ t x y

end GroupLaw
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"

end GoodReductionJacobian.RelativeGroupLaw.ImageHom
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul smooth_of_geometricallyReduced_of_locallyOfFiniteType"
namespace ImageHom
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Bundle

variable {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  (hJ : AbelianSchemePropertyBundle k f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] (LX : RelativeGroupLaw k g)
  (σ : SchemeHomOver g f)
  (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))

theorem isPullback_baseChange {K : Type u} [Field K] (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {Z : Scheme.{u}} {fst : Z ⟶ σ.1.image} {snd : Z ⟶ Spec (CommRingCat.of K)}
    (t : IsPullback fst snd (σ.1.imageι ≫ f) y) :
    ∃ π' : pullback g y ⟶ Z, IsPullback (pullback.fst g y) π' σ.1.toImage fst ∧ π' ≫ snd = pullback.snd g y := by
  have hπ : σ.1.toImage ≫ σ.1.imageι ≫ f = g := by rw [← Category.assoc, Scheme.Hom.toImage_imageι]; exact σ.2
  have s : IsPullback (pullback.fst g y) (pullback.snd g y) (σ.1.toImage ≫ σ.1.imageι ≫ f) y := by
    rw [hπ]; exact IsPullback.of_hasPullback g y
  exact ⟨_, IsPullback.of_bot' s t, t.lift_snd _ _ _⟩

include hJ in
theorem geometricallyReduced [GeometricallyReduced g] : GeometricallyReduced (σ.1.imageι ≫ f) := by
  have hdom := isSchemeTheoreticallyDominant_toImage hJ σ
  have hqc : QuasiCompact σ.1.toImage := by have := quasiCompact_val hJ σ; infer_instance
  rw [geometricallyReduced_iff]
  intro K _ y Z fst snd t
  obtain ⟨π', H, -⟩ := isPullback_baseChange σ y t
  haveI : Flat fst := MorphismProperty.of_isPullback (P := @Flat) t.flip inferInstance
  haveI := IsSchemeTheoreticallyDominant.of_isPullback H
  haveI : QuasiCompact π' := MorphismProperty.of_isPullback H hqc
  haveI : IsReduced (pullback g y) := pullback_of_geometrically (geometricallyReduced_iff _ |>.mp inferInstance) K y
  exact IsSchemeTheoreticallyDominant.isReduced π'

include hJ in
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ImageHom.connectedSpace [ConnectedSpace X] : ConnectedSpace σ.1.image :=
  (surjective_toImage hJ σ).connectedSpace σ.1.toImage.continuous

p2m_export "GoodReductionJacobian.RelativeGroupLaw.ImageHom" "connectedSpace"
include L hJ LX hσ in
theorem abelianSchemePropertyBundle [GeometricallyReduced g] [ConnectedSpace X] :
    AbelianSchemePropertyBundle k (σ.1.imageι ≫ f) := by
  haveI := hJ.proper
  haveI := geometricallyReduced hJ σ
  haveI := connectedSpace hJ σ
  refine ⟨?_, inferInstance, ?_, ⟨lawB L hJ LX σ hσ⟩⟩
  · exact GoodReductionJacobian.RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType (lawB L hJ LX σ hσ)
  · intro s
    have : (σ.1.imageι ≫ f).base ⁻¹' {s} = Set.univ := by
      ext b; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact isConnected_univ

end Bundle
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"

section Points

variable {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
  (hJ : AbelianSchemePropertyBundle k f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] (σ : SchemeHomOver g f)

include hJ in
theorem points_iff (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f) :
    (∃ b : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (σ.1.imageι ≫ f),
        NeronModelInfra.schemeHomOverComp b (imageιOver σ) = z) ↔
      ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) g,
        NeronModelInfra.schemeHomOverComp y σ = z := by
  constructor
  · rintro ⟨b, rfl⟩

    let yΩ := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
    obtain ⟨π', H, hπ'⟩ := isPullback_baseChange σ yΩ (IsPullback.of_hasPullback (σ.1.imageι ≫ f) yΩ)
    haveI : Surjective π' := MorphismProperty.of_isPullback H (surjective_toImage' hJ σ)
    haveI := hJ.proper
    haveI : LocallyOfFiniteType (pullback.snd (σ.1.imageι ≫ f) yΩ) := inferInstance
    haveI : LocallyOfFiniteType (pullback.snd g yΩ) := inferInstance
    haveI : JacobsonSpace (pullback g yΩ : Scheme.{u}) := LocallyOfFiniteType.jacobsonSpace (pullback.snd g yΩ)

    let b' : Spec (CommRingCat.of Ω) ⟶ pullback (σ.1.imageι ≫ f) yΩ := pullback.lift b.1 (𝟙 _) (by rw [Category.id_comp]; exact b.2)
    have hb' : b' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    let β := pointEquivClosedPoint (pullback.snd (σ.1.imageι ≫ f) yΩ) ⟨b', hb'⟩

    obtain ⟨ξ, hξβ, hξ⟩ := nonempty_inter_closedPoints ((π'.surjective β.1).elim fun x hx => ⟨x, hx⟩)
      (IsClosed.preimage π'.continuous β.2).isLocallyClosed
    let y' := pointOfClosedPoint (pullback.snd g yΩ) ξ hξ
    have hy' : y' ≫ pullback.snd g yΩ = 𝟙 _ := pointOfClosedPoint_comp _ _ _

    have hsec : y' ≫ π' = b' := by
      refine ext_of_apply_closedPoint_eq (pullback.snd (σ.1.imageι ≫ f) yΩ) (by rw [Category.assoc, hπ', hy']) hb' ?_
      rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
      exact hξβ
    refine ⟨⟨y' ≫ pullback.fst g yΩ, by rw [Category.assoc, pullback.condition, ← Category.assoc, hy', Category.id_comp]⟩, ?_⟩
    apply Subtype.ext
    change (y' ≫ pullback.fst g yΩ) ≫ σ.1 = b.1 ≫ σ.1.imageι
    have e0 : pullback.fst g yΩ ≫ σ.1 = π' ≫ pullback.fst (σ.1.imageι ≫ f) yΩ ≫ σ.1.imageι := by
      rw [← H.w_assoc, Scheme.Hom.toImage_imageι]
    rw [Category.assoc, e0, ← Category.assoc y', hsec, ← Category.assoc, pullback.lift_fst]
  · rintro ⟨y, rfl⟩
    exact ⟨NeronModelInfra.schemeHomOverComp y (toImageOver σ), by
      rw [NeronModelInfra.schemeHomOverComp_assoc, comp_toImageOver_imageιOver]⟩

end Points
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"

end GoodReductionJacobian.RelativeGroupLaw.ImageHom
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism.GoodReductionJacobian.RelativeGroupLaw.ImageHom"

open GoodReductionJacobian.RelativeGroupLaw.ImageHom in
theorem solution
    {k : Type u} [Field k]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hJ : AbelianSchemePropertyBundle k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of k)} [IsProper g] [GeometricallyReduced g]
    [ConnectedSpace X] (LX : RelativeGroupLaw k g) (σ : SchemeHomOver g f)
    (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ LB : RelativeGroupLaw k (σ.1.imageι ≫ f),
      AbelianSchemePropertyBundle k (σ.1.imageι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
        LB.mul t x y = LB.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (σ.1.imageι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y) (⟨σ.1.imageι, rfl⟩ : SchemeHomOver (σ.1.imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨σ.1.imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨σ.1.imageι, rfl⟩)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω],
        ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f,
          (∃ b : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (σ.1.imageι ≫ f),
              NeronModelInfra.schemeHomOverComp b ⟨σ.1.imageι, rfl⟩ = z) ↔
            ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) g,
              NeronModelInfra.schemeHomOverComp y σ = z) :=
  ⟨lawB L hJ LX σ hσ, abelianSchemePropertyBundle L hJ LX σ hσ, fun t x y => lawB_comm L hJ LX σ hσ hcomm t x y,
    fun t x y => lawB_hom L hJ LX σ hσ t x y, fun Ω _ _ _ z => points_iff hJ σ Ω z⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism (solution)
