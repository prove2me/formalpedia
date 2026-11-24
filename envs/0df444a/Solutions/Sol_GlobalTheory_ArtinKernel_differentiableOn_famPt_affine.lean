-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.differentiableOn_famPt_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:34.222887+00:00
-- url     : https://prove2.me/submissions/e5042e90-dff5-484a-bc1b-8fe705e0adec

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_congr
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_appLE
import Theorems.Thm_P2M_GlobalTheory_ArtinKernel_evalPt__eq_aeda6690487c
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_const
import Theorems.Thm_GlobalTheory_ArtinKernel_top_le_const
import Theorems.Thm_GlobalTheory_ArtinKernel_famPt_fst
import Theorems.Thm_GlobalTheory_ArtinKernel_famPt_snd
import Theorems.Thm_GlobalTheory_ArtinKernel_famPt_mem
import Theorems.Thm_GlobalTheory_ArtinKernel_differentiableOn_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
section Points
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}
end Points
section Family
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {A : Over (Sp ℂ)}
variable [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
private lemma appLE_comp_presheaf_map {X Y : Scheme.{0}} (f : X ⟶ Y) (W : Y.Opens) (V V' : X.Opens)
    (e : V ≤ f ⁻¹ᵁ W) (i : Opposite.op V ⟶ Opposite.op V') (e' : V' ≤ f ⁻¹ᵁ W) :
    f.appLE W V e ≫ X.presheaf.map i = f.appLE W V' e' := by
  rw [Scheme.Hom.appLE_map]
private lemma app_comp_map_comp_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (W : Y.Opens) (V V' : X.Opens)
    (i : Opposite.op (f ⁻¹ᵁ W) ⟶ Opposite.op V) (i' : Opposite.op V ⟶ Opposite.op V') (e' : V' ≤ f ⁻¹ᵁ W) :
    (f.app W ≫ X.presheaf.map i) ≫ X.presheaf.map i' = f.appLE W V' e' := by
  rw [Category.assoc, ← Functor.map_comp]
  rfl
variable [Module.Finite ℂ R]
end Family
end GlobalTheory.ArtinKernel
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {A : Over (Sp ℂ)}
variable [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable [Module.Finite ℂ R]
namespace GlobalTheory.ArtinKernel
theorem _root_.solution {U : A.left.Opens} (hU : IsAffineOpen U)
    (f : Γ((spO R ⊗ A).left, (snd (spO R) A).left ⁻¹ᵁ U)) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (evalPt' (R := R) (famPt u R z).left _ f))
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
  have hE : ∀ z ∈ {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U},
      ⊤ ≤ (famPt u R z).left ⁻¹ᵁ ((snd (spO R) A).left ⁻¹ᵁ U) := fun z hz => famPt_mem u z hz
  let T : Subring Γ((spO R ⊗ A).left, (snd (spO R) A).left ⁻¹ᵁ U) :=
    { carrier := {f | ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ
          (fun z => lam (evalPt' (R := R) (famPt u R z).left _ f)) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U}}
      mul_mem' := fun {a b} ha hb lam => by
        refine (GlobalTheory.ArtinKernel.differentiableOn_mul ha hb lam).congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_mul]
      one_mem' := fun lam => by
        refine (differentiableOn_const (lam 1)).congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_one]
      add_mem' := fun {a b} ha hb lam => by
        refine ((ha lam).add (hb lam)).congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_add, Pi.add_apply]
      zero_mem' := fun lam => by
        refine (differentiableOn_const (0 : ℂ)).congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_zero]
      neg_mem' := fun {a} ha lam => by
        refine (ha lam).neg.congr fun z hz => ?_
        simp only [evalPt'_eq _ (hE z hz), map_neg, Pi.neg_apply] }
  have gen1 : ∀ (W : A.left.Opens) (hUW : U ≤ W)
      (e : (snd (spO R) A).left ⁻¹ᵁ U ≤ (snd (spO R) A).left ⁻¹ᵁ W) (s : Γ(A.left, W)),
      ((snd (spO R) A).left.appLE W _ e).hom s ∈ T := by
    intro W hUW e s lam
    have hW : ∀ z ∈ {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ W :=
      fun z hz => hz.trans ((u.ex z).left.preimage_mono hUW)
    refine (((u.hol W s).2.mono hW).mul_const (lam 1)).congr fun z hz => ?_
    have h1 : ⊤ ≤ (toUnit (spO R) ≫ u.ex z).left ⁻¹ᵁ W := top_le_const (u.ex z) W (hW z hz)
    have h2 : ⊤ ≤ ((famPt u R z).left ≫ (snd (spO R) A).left) ⁻¹ᵁ W := by
      rw [famPt_snd]
      exact h1
    simp only [evalPt'_eq _ (hE z hz), evalPt_appLE _ _ _ rfl W _ e (hE z hz) h2,
      evalPt_congr (famPt_snd u z) W h2 h1, evalPt_const (u.ex z) W h1 (hW z hz),
      Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have gen2 : ∀ (e : (snd (spO R) A).left ⁻¹ᵁ U ≤ (fst (spO R) A).left ⁻¹ᵁ ⊤) (t : Γ(Sp R, ⊤)),
      ((fst (spO R) A).left.appLE ⊤ _ e).hom t ∈ T := by
    intro e t lam
    have h0 : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ⊤ := le_rfl
    refine (differentiableOn_const (lam (evalPt (𝟙 (Sp R)) ⊤ h0 t))).congr fun z hz => ?_
    have h2 : ⊤ ≤ ((famPt u R z).left ≫ (fst (spO R) A).left) ⁻¹ᵁ ⊤ := le_rfl
    simp only [evalPt'_eq _ (hE z hz), evalPt_appLE _ _ _ rfl ⊤ _ e (hE z hz) h2,
      evalPt_congr (famPt_fst u z) ⊤ h2 h0]
  have : IsAffine U := hU
  have : IsAffine (spO R).left := inferInstanceAs (IsAffine (Sp R))
  have hpb : IsPullback ((snd (spO R) A).left ∣_ U) (((snd (spO R) A).left ⁻¹ᵁ U).ι ≫ (fst (spO R) A).left)
      (U.ι ≫ A.hom) (spO R).hom :=
    (isPullback_morphismRestrict (snd (spO R) A).left U).paste_vert (IsPullback.of_hasPullback (spO R).hom A.hom).flip
  have hpo := isPushout_appTop_of_isPullback hpb
  have e1 : (snd (spO R) A).left ⁻¹ᵁ U ≤ (snd (spO R) A).left ⁻¹ᵁ (U.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]
  have k1 : ((snd (spO R) A).left ∣_ U).appTop ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom =
      (snd (spO R) A).left.appLE (U.ι ''ᵁ ⊤) _ e1 := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE, Scheme.Opens.topIso_hom]
    exact appLE_comp_presheaf_map _ _ _ _ _ _ _
  have k2 : (((snd (spO R) A).left ⁻¹ᵁ U).ι ≫ (fst (spO R) A).left).appTop ≫
      ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom = (fst (spO R) A).left.appLE ⊤ _ le_top := by
    rw [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    exact app_comp_map_comp_map_eq_appLE _ _ _ _ _ _ _
  have m1 : ∀ s, (((snd (spO R) A).left ∣_ U).appTop ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom s ∈ T := by
    intro s
    rw [k1]
    exact gen1 _ (Scheme.Opens.ι_image_top U).ge e1 s
  have m2 : ∀ t, ((((snd (spO R) A).left ⁻¹ᵁ U).ι ≫ (fst (spO R) A).left).appTop ≫
      ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom t ∈ T := by
    intro t
    rw [k2]
    exact gen2 le_top t
  let c1 := CommRingCat.ofHom (RingHom.codRestrict
    (((snd (spO R) A).left ∣_ U).appTop ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom T m1)
  let c2 := CommRingCat.ofHom (RingHom.codRestrict ((((snd (spO R) A).left ⁻¹ᵁ U).ι ≫
    (fst (spO R) A).left).appTop ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom T m2)
  have hw : (U.ι ≫ A.hom).appTop ≫ c1 = (spO R).hom.appTop ≫ c2 := by
    ext s
    have := congrArg (fun m => (m ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom s) hpo.w
    simp only [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  have hd : hpo.desc c1 c2 hw ≫ CommRingCat.ofHom T.subtype = ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom := by
    apply hpo.hom_ext
    · rw [← Category.assoc, hpo.inl_desc]
      rfl
    · rw [← Category.assoc, hpo.inr_desc]
      rfl
  have hf : f ∈ T := by
    have : ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom.hom (((snd (spO R) A).left ⁻¹ᵁ U).topIso.inv.hom f) = f := by
      show (((snd (spO R) A).left ⁻¹ᵁ U).topIso.inv ≫ ((snd (spO R) A).left ⁻¹ᵁ U).topIso.hom).hom f = f
      rw [Iso.inv_hom_id]
      rfl
    rw [← this, ← hd]
    exact ((hpo.desc c1 c2 hw).hom (((snd (spO R) A).left ⁻¹ᵁ U).topIso.inv.hom f)).2
  exact hf lam
end GlobalTheory.ArtinKernel
