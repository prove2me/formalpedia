-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.expF_zeroU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:01:20.342052+00:00
-- url     : https://prove2.me/submissions/df9dab91-4c43-43ec-ade9-4d877c3732b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_RelModel_sval_const
import Theorems.Thm_GlobalTheory_UU_RelModel_gs_scal
import Theorems.Thm_GlobalTheory_UU_RelModel_expT_zeroU
import Theorems.Thm_GlobalTheory_UnifZero_exists_secConst
import Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
namespace GlobalTheory.UU.RelModel
theorem _root_.solution [IsHausdorff I R] {t s} (h : (zeroU R I).ExpF F k t s) {a b : F}
    (ha : SecConst t (scal (fst (TFK (R := R) F) (𝟙_ _)).left a))
    (hb : SecConst (s PUnit.unit) (scal (fst (TF (R := R) F) (𝟙_ _)).left b)) : a = b := by
  obtain ⟨n, c, σ, f, h₁, h₂, h₃⟩ := h
  have hi : IsIso (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left :=
    (inferInstance : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (𝟙 _)))
  have hσ : ∀ i, ∃ a, SecConst (σ i) (scal (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left a) := fun i => by
    obtain ⟨a', ha⟩ := exists_secConst (σ i)
    obtain ⟨a, rfl⟩ := (scal_bijective (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left).2 a'
    exact ⟨a, ha⟩
  have hf : ∀ i, ∃ a, SecConst (f i PUnit.unit) (scal (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left a) :=
    fun i => by
    obtain ⟨a', ha⟩ := exists_secConst (f i PUnit.unit)
    obtain ⟨a, rfl⟩ := (scal_bijective (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left).2 a'
    exact ⟨a, ha⟩
  choose p hp using hσ
  choose p' hp' using hf
  obtain rfl : p = p' := funext fun i => expT_zeroU R I k (h₁ i) (hp i) (hp' i)
  refine (scal_bijective (𝟙 _)).1 (fn_ext fun z _ => ?_)
  let j := jFK (R := R) F
  let rA : Spec (CommRingCat.of F) ⟶ (TFK (R := R) F ⊗ 𝟙_ _).left := pullback.lift (𝟙 _) j (by simp [j])
  let rF : Spec (CommRingCat.of F) ⟶ (TF (R := R) F ⊗ 𝟙_ _).left := pullback.lift (𝟙 _) (j ≫ jK R) (by simp [j])
  let y : Spec (CommRingCat.of F) ⟶ ((Over.pullback (jK R)).obj (𝟙_ _)).left := pullback.lift (j ≫ jK R) j (by simp)
  let r : Spec (CommRingCat.of F) ⟶ (𝟙_ _ ⊗ 𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    pullback.lift (j ≫ jK R) (j ≫ jK R) rfl
  have hr : r ≫ (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left = j ≫ jK R := pullback.lift_snd _ _ _
  have hA : rA ≫ (fst (TFK (R := R) F) (𝟙_ _)).left = 𝟙 _ := pullback.lift_fst _ _ _
  have hF : rF ≫ (fst (TF (R := R) F) (𝟙_ _)).left = 𝟙 _ := pullback.lift_fst _ _ _
  have g : (zeroU R I).gen.hom.left = pullback.snd _ _ :=
    (Category.comp_id _).symm.trans (Over.w (zeroU R I).gen.hom)
  have e₂ := h₂ _ rA y r ((pullback.lift_snd _ _ _).trans ((congrArg (y ≫ ·) g).trans (pullback.lift_snd _ _ _)).symm)
    (hr.trans (pullback.lift_fst _ _ _).symm) z (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    (fun _ => trivial) (fun _ => trivial)
  have e₃ := h₃ PUnit.unit _ rF r (hr.trans (pullback.lift_snd _ _ _).symm) z (fun _ => PUnit.unit) (fun _ => trivial)
  have w1 : gw (zeroU R I).wA y z PUnit.unit (fun _ => PUnit.unit) = 1 := map_one _
  erw [w1, Units.val_one, one_pow, _root_.one_mul] at e₂
  have va := sval_const ha rA z (fun _ => PUnit.unit)
  have vb := sval_const hb rF z (fun _ => PUnit.unit)
  erw [hA] at va
  erw [hF] at vb
  refine va.symm.trans (e₂.trans (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (e₃.symm.trans vb)))
  refine congrArg₂ (· * ·) ?_ ((sval_const (hp i) r z _).trans (sval_const (hp' i) r z _).symm)
  refine (gs_scal _ _ rA z).trans (Eq.trans ?_ (gs_scal _ _ rF z).symm)
  exact (congrArg (fun q => gs (𝟙 _) z ⊤ (scal q (c i))) hA).trans (congrArg (fun q => gs (𝟙 _) z ⊤ (scal q (c i))) hF).symm
end GlobalTheory.UU.RelModel
