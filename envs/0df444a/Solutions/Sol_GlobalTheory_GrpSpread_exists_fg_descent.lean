-- Prove2me | solution 1 for GlobalTheory.GrpSpread.exists_fg_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:37.867476+00:00
-- url     : https://prove2.me/submissions/5a6038bc-ea8f-4ad1-94fe-eeaddbe6f42c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_exists_fg_comp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.GrpSpread
open GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
namespace GlobalTheory.GrpSpread
theorem _root_.solution {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {B B' X : Scheme.{0}}
    (pB : B ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] (p : X ⟶ Sp k) [LocallyOfFinitePresentation p]
    {q' : B' ⟶ Sp V} {b : B' ⟶ B} (hb : IsPullback b q' pB (spMap (algebraMap k V))) (f : B' ⟶ X)
    (hf : f ≫ p = b ≫ pB) :
    ∃ R : Subalgebra k V, R.FG ∧ ∀ (R' : Subalgebra k V), R ≤ R' → ∀ (B₁ : Scheme.{0}) (q₁ : B₁ ⟶ Sp R')
      (b₁ : B₁ ⟶ B) (c : B' ⟶ B₁), b₁ ≫ pB = q₁ ≫ spMap (algebraMap k R') → c ≫ b₁ = b →
      c ≫ q₁ = q' ≫ spMap R'.val.toRingHom →
      ∃ g : B₁ ⟶ X, c ≫ g = f ∧ g ≫ p = q₁ ≫ spMap (algebraMap k R') := by
  let φ' : pullback pB (spMap (algebraMap k V)) ⟶ X := hb.isoPullback.inv ≫ f
  have hφ' : φ' ≫ p = pullback.fst _ _ ≫ pB := by
    simp only [φ', Category.assoc, hf, hb.isoPullback_inv_fst_assoc]
  obtain ⟨R, ψ, hR, hψp, hψ⟩ := GlobalTheory.Spread.exists_fg_comp_eq pB p φ' hφ'
  refine ⟨R, hR, fun R' hRR' B₁ q₁ b₁ c h1 h2 h3 => ?_⟩
  have cond : b₁ ≫ pB = (q₁ ≫ spMap (Subalgebra.inclusion hRR').toRingHom) ≫ spMap (algebraMap k R) := by
    rw [h1, Category.assoc, GlobalTheory.Spread.spMap_algHom_comp]
  refine ⟨pullback.lift b₁ _ cond ≫ ψ, ?_, ?_⟩
  · have e : (R'.val.toRingHom).comp (Subalgebra.inclusion hRR').toRingHom = R.val.toRingHom := by
      ext; rfl
    have key : c ≫ pullback.lift b₁ _ cond = hb.isoPullback.hom ≫ GlobalTheory.Spread.bcMap pB R.val := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, GlobalTheory.Spread.bcMap_fst, hb.isoPullback_hom_fst, h2]
      · simp only [Category.assoc, pullback.lift_snd, GlobalTheory.Spread.bcMap_snd, hb.isoPullback_hom_snd_assoc]
        rw [← Category.assoc, h3, Category.assoc, ← spMap_comp, e]
    rw [← Category.assoc, key, Category.assoc, hψ, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hψp, pullback.lift_fst_assoc, h1]
end GlobalTheory.GrpSpread
