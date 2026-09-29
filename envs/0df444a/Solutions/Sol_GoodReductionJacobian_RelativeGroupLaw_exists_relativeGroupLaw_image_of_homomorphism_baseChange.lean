-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_image_of_homomorphism_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bc7a0248-e352-51ad-9ab3-e39e9ce82020

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul baseChangePointToBase baseChangePointToBase_coe baseChange baseChangePointToBase_mul fibre"
namespace BCImage
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Represent

variable {k : Type u} [CommRing k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

theorem one_natural' {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) = L.one t' := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  have h := L.mul_natural t t' ψ hψ (L.one t) (L.one t)
  rw [L.one_mul] at h

  have : (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) : SchemeHomOver t' f) =
      (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t)) * (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t)) := h
  exact left_eq_mul.mp this |>.symm ▸ rfl

theorem inv_natural' {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  have h := L.mul_natural t t' ψ hψ (L.inv t x) x
  rw [L.inv_mul_cancel, one_natural'] at h

  exact (eq_inv_of_mul_eq_one_left h.symm : _)

noncomputable def mulMor : pullback f f ⟶ J :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1

theorem mulMor_over : mulMor L ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).2

noncomputable def pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y : SchemeHomOver t f) : T ⟶ pullback f f :=
  pullback.lift x.1 y.1 (x.2.trans y.2.symm)

@[scoped simp] theorem pair_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y : SchemeHomOver t f) :
    pair x y ≫ pullback.fst f f = x.1 := pullback.lift_fst _ _ _
@[scoped simp] theorem pair_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x y : SchemeHomOver t f) :
    pair x y ≫ pullback.snd f f = y.1 := pullback.lift_snd _ _ _

theorem mul_eq_pair_mulMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) :
    (L.mul t x y).1 = pair x y ≫ mulMor L := by
  have h := L.mul_natural (pullback.fst f f ≫ f) t (pair x y) (by rw [← Category.assoc, pair_fst, x.2])
    ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have hx : GoodReductionJacobian.schemeHomOverComp (pair x y) (by rw [← Category.assoc, pair_fst, x.2])
      (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = x := Subtype.ext (pair_fst x y)
  have hy : GoodReductionJacobian.schemeHomOverComp (pair x y) (by rw [← Category.assoc, pair_fst, x.2])
      (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f) = y :=
    Subtype.ext (pair_snd x y)
  rw [hx, hy] at h
  rw [← h]; rfl

noncomputable def invMor : J ⟶ J := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).1

theorem invMor_over : invMor L ≫ f = f := (L.inv f ⟨𝟙 J, Category.id_comp f⟩).2

theorem inv_eq_comp_invMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f) :
    (L.inv t x).1 = x.1 ≫ invMor L := by
  have h := inv_natural' L f t x.1 x.2 ⟨𝟙 J, Category.id_comp f⟩
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (⟨𝟙 J, Category.id_comp f⟩ : SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]; rfl

noncomputable def oneMor : Spec (CommRingCat.of k) ⟶ J := (L.one (𝟙 _)).1

theorem oneMor_over : oneMor L ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

theorem one_eq_comp_oneMor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    (L.one t).1 = t ≫ oneMor L := by
  have h := one_natural' L (𝟙 _) t t (Category.comp_id t)
  rw [← h]; rfl

end Represent

end GoodReductionJacobian.RelativeGroupLaw.BCImage
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul baseChangePointToBase baseChangePointToBase_coe baseChange baseChangePointToBase_mul fibre"
namespace BCImage
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Image

variable {X J : Scheme.{u}} (τ : X ⟶ J) [QuasiCompact τ]

theorem isSchemeTheoreticallyDominant_toImage : IsSchemeTheoreticallyDominant τ.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let U : J.affineOpens → τ.image.affineOpens := fun V => ⟨τ.imageι ⁻¹ᵁ V.1, V.2.preimage τ.imageι⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ ?_
  · rw [← top_le_iff]
    intro b _
    obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ := J.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (τ.imageι b)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hbV⟩
  · intro V
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
    intro s hs
    exact (τ.toImage_app_injective V ((RingHom.mem_ker).mp hs |>.trans (map_zero _).symm) : _)

end Image
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"

section Closure

variable {R R' : Type u} [CommRing R] [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) [Mono ι] [Flat ι] [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R')} [Flat g] (LX : RelativeGroupLaw R' g)
  (σ : SchemeHomOver g (pullback.snd f ι))
  [QuasiCompact (σ.1 ≫ pullback.fst f ι)] [Flat ((σ.1 ≫ pullback.fst f ι).imageι ≫ f)]
  (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        (L.baseChange ι).mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))

noncomputable abbrev τ : X ⟶ J := σ.1 ≫ pullback.fst f ι

theorem τ_over : τ ι σ ≫ f = g ≫ ι := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, σ.2]

noncomputable def τPt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t g) :
    SchemeHomOver (t ≫ ι) f :=
  ⟨x.1 ≫ τ ι σ, by rw [Category.assoc, τ_over, ← Category.assoc, x.2]⟩

@[scoped simp] theorem τPt_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t g) :
    (τPt ι σ x).1 = x.1 ≫ τ ι σ := rfl

theorem τPt_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t g) :
    τPt ι σ x = RelativeGroupLaw.baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp x σ) :=
  Subtype.ext (by rw [τPt_coe, RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc])

include hσ in

theorem hom_τ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t g) :
    τPt ι σ (LX.mul t x y) = L.mul (t ≫ ι) (τPt ι σ x) (τPt ι σ y) := by
  rw [τPt_eq, τPt_eq, τPt_eq, hσ, RelativeGroupLaw.baseChangePointToBase_mul]

include hσ in
theorem hom_τ_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) : τPt ι σ (LX.one t) = L.one (t ≫ ι) := by
  letI := L.pointGroup (t ≫ ι)
  have h := hom_τ ι L LX σ hσ t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h
  have : (τPt ι σ (LX.one t) : SchemeHomOver (t ≫ ι) f) = τPt ι σ (LX.one t) * τPt ι σ (LX.one t) := h
  exact (left_eq_mul.mp this).symm ▸ rfl

include hσ in
theorem hom_τ_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t g) :
    τPt ι σ (LX.inv t x) = L.inv (t ≫ ι) (τPt ι σ x) := by
  letI := L.pointGroup (t ≫ ι)
  have h := hom_τ ι L LX σ hσ t (LX.inv t x) x
  rw [LX.inv_mul_cancel, hom_τ_one ι L LX σ hσ] at h
  exact (eq_inv_of_mul_eq_one_left h.symm : _)

noncomputable def mulJB : pullback ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ⟶ J :=
  (L.mul (pullback.fst ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ≫ (τ ι σ).imageι ≫ f)
    ⟨pullback.fst _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩).1

theorem mulJB_over : mulJB ι L σ ≫ f = pullback.fst ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ≫ (τ ι σ).imageι ≫ f :=
  (L.mul _ _ _).2

noncomputable def prodToImage : pullback g g ⟶ pullback ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) :=
  pullback.map g g ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) (τ ι σ).toImage (τ ι σ).toImage ι
    (by rw [← Category.assoc, Scheme.Hom.toImage_imageι, τ_over])
    (by rw [← Category.assoc, Scheme.Hom.toImage_imageι, τ_over])

@[scoped simp] theorem prodToImage_fst : prodToImage ι σ ≫ pullback.fst _ _ = pullback.fst g g ≫ (τ ι σ).toImage :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem prodToImage_snd : prodToImage ι σ ≫ pullback.snd _ _ = pullback.snd g g ≫ (τ ι σ).toImage :=
  pullback.lift_snd _ _ _

include hσ in
theorem prodToImage_mulJB :
    prodToImage ι σ ≫ mulJB ι L σ = (LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
      ⟨pullback.snd g g, pullback.condition.symm⟩).1 ≫ τ ι σ := by
  have hover : prodToImage ι σ ≫ pullback.fst ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ≫ (τ ι σ).imageι ≫ f =
      (pullback.fst g g ≫ g) ≫ ι := by
    rw [← Category.assoc, prodToImage_fst, Category.assoc, ← Category.assoc (τ ι σ).toImage, Scheme.Hom.toImage_imageι,
      τ_over, Category.assoc]
  have h := L.mul_natural _ ((pullback.fst g g ≫ g) ≫ ι) (prodToImage ι σ) hover
    ⟨pullback.fst _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (prodToImage ι σ) hover
      (⟨pullback.fst _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]⟩ :
        SchemeHomOver (pullback.fst ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ≫ (τ ι σ).imageι ≫ f) f) =
      τPt ι σ (⟨pullback.fst g g, rfl⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) := by
    apply Subtype.ext
    change prodToImage ι σ ≫ pullback.fst _ _ ≫ (τ ι σ).imageι = pullback.fst g g ≫ τ ι σ
    rw [← Category.assoc, prodToImage_fst, Category.assoc, Scheme.Hom.toImage_imageι]
  have h2 : GoodReductionJacobian.schemeHomOverComp (prodToImage ι σ) hover
      (⟨pullback.snd _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ≫ (τ ι σ).imageι ≫ f) f) =
      τPt ι σ (⟨pullback.snd g g, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst g g ≫ g) g) := by
    apply Subtype.ext
    change prodToImage ι σ ≫ pullback.snd _ _ ≫ (τ ι σ).imageι = pullback.snd g g ≫ τ ι σ
    rw [← Category.assoc, prodToImage_snd, Category.assoc, Scheme.Hom.toImage_imageι]
  rw [h1, h2, ← hom_τ ι L LX σ hσ] at h
  exact congrArg Subtype.val h

theorem isSchemeTheoreticallyDominant_prodToImage : IsSchemeTheoreticallyDominant (prodToImage ι σ) := by
  have hdom := isSchemeTheoreticallyDominant_toImage (τ ι σ)
  have hqc : QuasiCompact (τ ι σ).toImage := inferInstance
  have hπ : (τ ι σ).toImage ≫ (τ ι σ).imageι ≫ f = g ≫ ι := by rw [← Category.assoc, Scheme.Hom.toImage_imageι, τ_over]

  have s₀ : IsPullback (pullback.fst g g) (pullback.snd g g) (g ≫ ι) (g ≫ ι) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono g g ι)

  have t₁ := IsPullback.of_hasPullback ((τ ι σ).imageι ≫ f) (g ≫ ι)
  have s₁ : IsPullback (pullback.fst g g) (pullback.snd g g) ((τ ι σ).toImage ≫ (τ ι σ).imageι ≫ f) (g ≫ ι) := by
    rw [hπ]; exact s₀
  have H₁ := IsPullback.of_bot' s₁ t₁
  haveI : IsSchemeTheoreticallyDominant (t₁.lift (pullback.fst g g ≫ (τ ι σ).toImage) (pullback.snd g g)
      (by rw [Category.assoc, s₁.w])) := IsSchemeTheoreticallyDominant.of_isPullback H₁

  have t₂ := (IsPullback.of_hasPullback ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f)).flip
  have s₂ : IsPullback (pullback.snd ((τ ι σ).imageι ≫ f) (g ≫ ι)) (pullback.fst ((τ ι σ).imageι ≫ f) (g ≫ ι))
      ((τ ι σ).toImage ≫ (τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) := by
    rw [hπ]; exact (IsPullback.of_hasPullback ((τ ι σ).imageι ≫ f) (g ≫ ι)).flip
  have H₂ := IsPullback.of_bot' s₂ t₂
  haveI : IsSchemeTheoreticallyDominant (t₂.lift (pullback.snd ((τ ι σ).imageι ≫ f) (g ≫ ι) ≫ (τ ι σ).toImage)
      (pullback.fst ((τ ι σ).imageι ≫ f) (g ≫ ι)) (by rw [Category.assoc, s₂.w])) := IsSchemeTheoreticallyDominant.of_isPullback H₂
  have heq : prodToImage ι σ = t₁.lift (pullback.fst g g ≫ (τ ι σ).toImage) (pullback.snd g g) (by rw [Category.assoc, s₁.w]) ≫
      t₂.lift (pullback.snd ((τ ι σ).imageι ≫ f) (g ≫ ι) ≫ (τ ι σ).toImage) (pullback.fst ((τ ι σ).imageι ≫ f) (g ≫ ι))
        (by rw [Category.assoc, s₂.w]) := by
    apply pullback.hom_ext
    · rw [prodToImage_fst, Category.assoc, t₂.lift_snd, t₁.lift_fst]
    · rw [prodToImage_snd, Category.assoc, t₂.lift_fst, t₁.lift_snd_assoc]
  rw [heq]; infer_instance

include hσ in
theorem ker_le_ker_mulJB : (τ ι σ).ker ≤ (mulJB ι L σ).ker := by
  have hdom := isSchemeTheoreticallyDominant_prodToImage ι σ
  calc (τ ι σ).ker = (⊥ : X.IdealSheafData).map (τ ι σ) := (Scheme.IdealSheafData.map_bot _).symm
    _ ≤ ((LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩).1.ker).map (τ ι σ) :=
        Scheme.IdealSheafData.map_mono _ bot_le
    _ = ((LX.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩).1 ≫ τ ι σ).ker :=
        (Scheme.Hom.ker_comp _ _).symm
    _ = (prodToImage ι σ ≫ mulJB ι L σ).ker := by rw [prodToImage_mulJB ι L LX σ hσ]
    _ = (prodToImage ι σ).ker.map (mulJB ι L σ) := Scheme.Hom.ker_comp _ _
    _ = (mulJB ι L σ).ker := by rw [hdom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

noncomputable def invJB : (τ ι σ).image ⟶ J := (τ ι σ).imageι ≫ invMor L

include hσ in
theorem ker_le_ker_invJB : (τ ι σ).ker ≤ (invJB ι L σ).ker := by
  have hdom := isSchemeTheoreticallyDominant_toImage (τ ι σ)
  have hcomp : (τ ι σ).toImage ≫ invJB ι L σ = invMor LX ≫ τ ι σ := by
    change (τ ι σ).toImage ≫ (τ ι σ).imageι ≫ invMor L = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    have h := congrArg Subtype.val (hom_τ_inv ι L LX σ hσ g ⟨𝟙 X, Category.id_comp g⟩)
    rw [inv_eq_comp_invMor L, τPt_coe, τPt_coe, inv_eq_comp_invMor LX] at h
    simpa using h.symm
  calc (τ ι σ).ker = (⊥ : X.IdealSheafData).map (τ ι σ) := (Scheme.IdealSheafData.map_bot _).symm
    _ ≤ ((invMor LX).ker).map (τ ι σ) := Scheme.IdealSheafData.map_mono _ bot_le
    _ = (invMor LX ≫ τ ι σ).ker := (Scheme.Hom.ker_comp _ _).symm
    _ = ((τ ι σ).toImage ≫ invJB ι L σ).ker := by rw [hcomp]
    _ = ((τ ι σ).toImage).ker.map (invJB ι L σ) := Scheme.Hom.ker_comp _ _
    _ = (invJB ι L σ).ker := by rw [hdom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

include hσ in

theorem ker_le_ker_oneMor : (τ ι σ).ker ≤ (oneMor L).ker := by
  have hcomp : ι ≫ oneMor L = oneMor LX ≫ τ ι σ := by
    have h := congrArg Subtype.val (hom_τ_one ι L LX σ hσ (𝟙 _))
    rw [τPt_coe, one_eq_comp_oneMor L, Category.id_comp] at h
    rw [one_eq_comp_oneMor LX, Category.id_comp] at h
    exact h.symm
  calc (τ ι σ).ker = (⊥ : X.IdealSheafData).map (τ ι σ) := (Scheme.IdealSheafData.map_bot _).symm
    _ ≤ ((oneMor LX).ker).map (τ ι σ) := Scheme.IdealSheafData.map_mono _ bot_le
    _ = (oneMor LX ≫ τ ι σ).ker := (Scheme.Hom.ker_comp _ _).symm
    _ = (ι ≫ oneMor L).ker := by rw [hcomp]
    _ = (Scheme.Hom.ker ι).map (oneMor L) := Scheme.Hom.ker_comp _ _
    _ = (oneMor L).ker := by rw [Scheme.Hom.ker_eq_bot ι, Scheme.IdealSheafData.map_bot]

noncomputable def mulB : pullback ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ⟶ (τ ι σ).image :=
  IsClosedImmersion.lift (τ ι σ).imageι (mulJB ι L σ) ((Scheme.IdealSheafData.ker_subschemeι _).trans_le (ker_le_ker_mulJB ι L LX σ hσ))

theorem mulB_imageι : mulB ι L LX σ hσ ≫ (τ ι σ).imageι = mulJB ι L σ := IsClosedImmersion.lift_fac _ _ _

noncomputable def invB : (τ ι σ).image ⟶ (τ ι σ).image :=
  IsClosedImmersion.lift (τ ι σ).imageι (invJB ι L σ) ((Scheme.IdealSheafData.ker_subschemeι _).trans_le (ker_le_ker_invJB ι L LX σ hσ))

theorem invB_imageι : invB ι L LX σ hσ ≫ (τ ι σ).imageι = (τ ι σ).imageι ≫ invMor L := IsClosedImmersion.lift_fac _ _ _

noncomputable def oneB : Spec (CommRingCat.of R) ⟶ (τ ι σ).image :=
  IsClosedImmersion.lift (τ ι σ).imageι (oneMor L) ((Scheme.IdealSheafData.ker_subschemeι _).trans_le (ker_le_ker_oneMor ι L LX σ hσ))

theorem oneB_imageι : oneB ι L LX σ hσ ≫ (τ ι σ).imageι = oneMor L := IsClosedImmersion.lift_fac _ _ _

end Closure
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"

end GoodReductionJacobian.RelativeGroupLaw.BCImage
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul baseChangePointToBase baseChangePointToBase_coe baseChange baseChangePointToBase_mul fibre"
namespace BCImage
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section GroupLaw

variable {R R' : Type u} [CommRing R] [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) [Mono ι] [Flat ι] [QuasiCompact ι] [IsSchemeTheoreticallyDominant ι]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R')} [Flat g] (LX : RelativeGroupLaw R' g)
  (σ : SchemeHomOver g (pullback.snd f ι))
  [QuasiCompact (σ.1 ≫ pullback.fst f ι)] [Flat ((σ.1 ≫ pullback.fst f ι).imageι ≫ f)]
  (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        (L.baseChange ι).mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))

noncomputable def imageιOver : SchemeHomOver ((τ ι σ).imageι ≫ f) f := ⟨(τ ι σ).imageι, rfl⟩

noncomputable def incl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    SchemeHomOver t f :=
  NeronModelInfra.schemeHomOverComp x (imageιOver ι σ)

@[scoped simp] theorem incl_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    (incl ι σ x).1 = x.1 ≫ (τ ι σ).imageι := rfl

theorem incl_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} :
    Function.Injective (incl ι σ (T := T) (t := t)) := fun x y h =>
  Subtype.ext ((cancel_mono (τ ι σ).imageι).mp (congrArg Subtype.val h))

theorem incl_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    incl ι σ (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = GoodReductionJacobian.schemeHomOverComp ψ hψ (incl ι σ x) :=
  Subtype.ext (Category.assoc _ _ _)

noncomputable def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    SchemeHomOver t ((τ ι σ).imageι ≫ f) :=
  ⟨pair x y ≫ mulB ι L LX σ hσ, by
    rw [Category.assoc, ← Category.assoc (mulB ι L LX σ hσ), mulB_imageι, mulJB_over, ← Category.assoc, pair_fst]
    exact x.2⟩

theorem incl_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    incl ι σ (mulPt ι L LX σ hσ t x y) = L.mul t (incl ι σ x) (incl ι σ y) := by
  have hψ : pair x y ≫ pullback.fst ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ≫ (τ ι σ).imageι ≫ f = t := by
    rw [← Category.assoc, pair_fst]; exact x.2
  have h := L.mul_natural _ t (pair x y) hψ
    ⟨pullback.fst _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]⟩
    ⟨pullback.snd _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pair x y) hψ
      (⟨pullback.fst _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]⟩ :
        SchemeHomOver (pullback.fst ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ≫ (τ ι σ).imageι ≫ f) f) = incl ι σ x := by
    apply Subtype.ext; change pair x y ≫ pullback.fst _ _ ≫ (τ ι σ).imageι = x.1 ≫ (τ ι σ).imageι
    rw [← Category.assoc, pair_fst]
  have h2 : GoodReductionJacobian.schemeHomOverComp (pair x y) hψ
      (⟨pullback.snd _ _ ≫ (τ ι σ).imageι, by rw [Category.assoc]; exact pullback.condition.symm⟩ :
        SchemeHomOver (pullback.fst ((τ ι σ).imageι ≫ f) ((τ ι σ).imageι ≫ f) ≫ (τ ι σ).imageι ≫ f) f) = incl ι σ y := by
    apply Subtype.ext; change pair x y ≫ pullback.snd _ _ ≫ (τ ι σ).imageι = y.1 ≫ (τ ι σ).imageι
    rw [← Category.assoc, pair_snd]
  rw [h1, h2] at h
  rw [← h]
  apply Subtype.ext
  change (pair x y ≫ mulB ι L LX σ hσ) ≫ (τ ι σ).imageι = pair x y ≫ mulJB ι L σ
  rw [Category.assoc, mulB_imageι]

noncomputable def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t ((τ ι σ).imageι ≫ f) :=
  ⟨t ≫ oneB ι L LX σ hσ, by
    rw [Category.assoc, ← Category.assoc (oneB ι L LX σ hσ), oneB_imageι, oneMor_over L, Category.comp_id]⟩

theorem incl_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : incl ι σ (onePt ι L LX σ hσ t) = L.one t := by
  apply Subtype.ext
  change (t ≫ oneB ι L LX σ hσ) ≫ (τ ι σ).imageι = (L.one t).1
  rw [Category.assoc, oneB_imageι, one_eq_comp_oneMor L]

noncomputable def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    SchemeHomOver t ((τ ι σ).imageι ≫ f) :=
  ⟨x.1 ≫ invB ι L LX σ hσ, by
    rw [Category.assoc, ← Category.assoc (invB ι L LX σ hσ), invB_imageι, Category.assoc, invMor_over L]
    exact x.2⟩

theorem incl_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    incl ι σ (invPt ι L LX σ hσ t x) = L.inv t (incl ι σ x) := by
  apply Subtype.ext
  change (x.1 ≫ invB ι L LX σ hσ) ≫ (τ ι σ).imageι = (L.inv t (incl ι σ x)).1
  rw [Category.assoc, invB_imageι, inv_eq_comp_invMor L, incl_coe, Category.assoc]

noncomputable def lawB : RelativeGroupLaw R ((τ ι σ).imageι ≫ f) where
  mul t x y := mulPt ι L LX σ hσ t x y
  one t := onePt ι L LX σ hσ t
  inv t x := invPt ι L LX σ hσ t x
  mul_assoc t x y z := incl_injective ι σ (by rw [incl_mulPt, incl_mulPt, incl_mulPt, incl_mulPt, L.mul_assoc])
  one_mul t x := incl_injective ι σ (by rw [incl_mulPt, incl_onePt, L.one_mul])
  mul_one t x := incl_injective ι σ (by rw [incl_mulPt, incl_onePt, L.mul_one])
  inv_mul_cancel t x := incl_injective ι σ (by rw [incl_mulPt, incl_invPt, incl_onePt, L.inv_mul_cancel])
  mul_natural t t' ψ hψ x y := incl_injective ι σ (by
    rw [incl_comp, incl_mulPt, incl_mulPt, incl_comp, incl_comp, L.mul_natural])

theorem lawB_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    (lawB ι L LX σ hσ).mul t x y = mulPt ι L LX σ hσ t x y := rfl

theorem lawB_comm (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    (lawB ι L LX σ hσ).mul t x y = (lawB ι L LX σ hσ).mul t y x :=
  incl_injective ι σ (by rw [lawB_mul, lawB_mul, incl_mulPt, incl_mulPt, hcomm])

theorem lawB_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t ((τ ι σ).imageι ≫ f)) :
    NeronModelInfra.schemeHomOverComp ((lawB ι L LX σ hσ).mul t x y) (imageιOver ι σ) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (imageιOver ι σ)) (NeronModelInfra.schemeHomOverComp y (imageιOver ι σ)) :=
  incl_mulPt ι L LX σ hσ t x y

end GroupLaw
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"

end GoodReductionJacobian.RelativeGroupLaw.BCImage
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange.GoodReductionJacobian.RelativeGroupLaw.BCImage"

open GoodReductionJacobian.RelativeGroupLaw.BCImage in

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) [Mono ι] [Flat ι] [QuasiCompact ι]
    [IsSchemeTheoreticallyDominant ι]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R')} [Flat g] (LX : RelativeGroupLaw R' g)
    (σ : SchemeHomOver g (pullback.snd f ι))
    [QuasiCompact (σ.1 ≫ pullback.fst f ι)] [Flat ((σ.1 ≫ pullback.fst f ι).imageι ≫ f)]
    (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) σ =
        (L.baseChange ι).mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ)) :
    ∃ LB : RelativeGroupLaw R ((σ.1 ≫ pullback.fst f ι).imageι ≫ f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t ((σ.1 ≫ pullback.fst f ι).imageι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LB.mul t x y)
            (⟨(σ.1 ≫ pullback.fst f ι).imageι, rfl⟩ : SchemeHomOver ((σ.1 ≫ pullback.fst f ι).imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨(σ.1 ≫ pullback.fst f ι).imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨(σ.1 ≫ pullback.fst f ι).imageι, rfl⟩)) ∧
      ((∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t ((σ.1 ≫ pullback.fst f ι).imageι ≫ f)),
          LB.mul t x y = LB.mul t y x) :=
  ⟨lawB ι L LX σ hσ, fun t x y => lawB_hom ι L LX σ hσ t x y, fun hcomm _ t x y => lawB_comm ι L LX σ hσ hcomm t x y⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_image_of_homomorphism_baseChange (solution)
