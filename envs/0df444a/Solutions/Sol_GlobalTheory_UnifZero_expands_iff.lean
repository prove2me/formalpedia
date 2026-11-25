-- Prove2me | solution 1 for GlobalTheory.UnifZero.expands_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:28.349733+00:00
-- url     : https://prove2.me/submissions/e8a203cb-d91c-4f8f-b5ea-dbf4003d9587

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Theorems.Thm_GlobalTheory_UnifZero_exists_secConst
import Theorems.Thm_GlobalTheory_UnifZero_secScal_iff
import Theorems.Thm_GlobalTheory_UnifZero_appTop_scal
import Theorems.Thm_GlobalTheory_UnifZero_scal_specMap
import Theorems.Thm_GlobalTheory_UnifZero_scal_mul
import Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
import Theorems.Thm_GlobalTheory_UnifZero_expandsAt_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)
variable {R I}
namespace GlobalTheory.UnifZero
theorem _root_.solution [IsHausdorff I R] (k : ℕ) {s : (zeroPre R I).SecK k}
    {F : Fam (zeroData R I).toPre (FractionRing R) k} {x y : FractionRing R}
    (hs : SecConst s (scal pGK x)) (hF : SecConst (F.s PUnit.unit) (scal pBK y)) :
    (zeroPre R I).Expands k s F ↔ x = y := by
  have e1 : ∀ a r : R, (pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (jK R)).appTop.hom (scal (𝟙 _) a) =
      scal (pGK ≫ jK R) r * scal pGK x ↔ algebraMap R _ a = algebraMap R _ r * x := fun a r => by
    rw [← (scal_bijective pGK).1.eq_iff, scal_mul, ← scal_specMap, ← scal_specMap]
    exact Eq.congr_left ((appTop_scal _ _ _).trans (congrArg (scal · a) pullback.condition))
  have hB : ∀ a : R, scal (DegPre.BF (zeroData R I).toPre (FractionRing R)).hom a =
      scal pBK (algebraMap R (FractionRing R) a) := fun a => by
    rw [← Over.w (fst (TF (R := R) (FractionRing R)) _)]
    exact (congrArg (scal · a) (Category.assoc _ _ _).symm).trans
      ((scal_specMap _ _ _).trans (scal_specMap _ _ _))
  have e2 : ∀ a r : R, (DegPre.prB (zeroData R I).toPre (FractionRing R)).left.appTop.hom (scal (𝟙 _) a) =
      scal (DegPre.BF (zeroData R I).toPre (FractionRing R)).hom r * scal pBK y ↔
      algebraMap R _ a = algebraMap R _ r * y := fun a r => by
    rw [← (scal_bijective (pBK (I := I))).1.eq_iff, scal_mul, ← hB, ← hB]
    exact Eq.congr_left ((appTop_scal _ _ _).trans (congrArg (scal · a)
      (Over.w (DegPre.prB (zeroData R I).toPre (FractionRing R)))))
  constructor
  · rintro ⟨r, hr, σ, f, h1, h2, h3⟩
    obtain ⟨a', ha⟩ := exists_secConst σ
    obtain ⟨a, rfl⟩ := (scal_bijective (𝟙 (Spec (CommRingCat.of R)))).2 a'
    obtain ⟨b', hb⟩ := exists_secConst (f PUnit.unit)
    obtain ⟨b, rfl⟩ := (scal_bijective (𝟙 (Spec (CommRingCat.of R)))).2 b'
    have hab : a = b := by
      rw [← sub_eq_zero]
      refine IsHausdorff.haus' (I := I) _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (Nat.le_succ n) ((expandsAt_iff n k ha hb).1 (h3 n))
    have hx := (e1 a r).1 ((secScal_iff hs ha _ _).1 h1)
    have hy := (e2 b r).1 ((secScal_iff hF hb _ _).1 (h2 PUnit.unit))
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
      (hx.symm.trans (hab ▸ hy))
  · rintro rfl
    obtain ⟨⟨a, r⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) x
    have h' : algebraMap R (FractionRing R) a = algebraMap R _ r * x := h.symm.trans (mul_comm _ _)
    exact ⟨r, nonZeroDivisors.ne_zero r.2, cs _ _ (scal (𝟙 _) a), fun _ => cs _ _ (scal (𝟙 _) a),
      (secScal_iff hs (cs_const _ _ _) _ _).2 ((e1 a r).2 h'),
      fun _ => (secScal_iff hF (cs_const _ _ _) _ _).2 ((e2 a r).2 h'),
      fun e => (expandsAt_iff e k (cs_const _ _ _) (cs_const _ _ _)).2 (by rw [sub_self]; exact zero_mem _)⟩
end GlobalTheory.UnifZero
