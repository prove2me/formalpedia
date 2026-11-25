-- Prove2me | solution 1 for GlobalTheory.KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:47.562365+00:00
-- url     : https://prove2.me/submissions/f11f29ee-97e8-4ef4-a49b-8efe014d32e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Theorems.Thm_GlobalTheory_KernelNoTorsion_eq_of_generic
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33
import Theorems.Thm_GlobalTheory_KernelNoTorsion_torsion_hom_ext
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c
import Theorems.Thm_P2M_GlobalTheory_isOpenImmersion_equalizer___left_of_unramified_3c023f0a11ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KernelNoTorsion
namespace GlobalTheory.KernelNoTorsion
theorem _root_.solution :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] [IsCommMonObj Ga] [IsCommMonObj G] (p : Ga ⟶ G) (n : ℕ), IsMonHom p → IsSeparated Ga.hom → Etale (torsion Ga n).hom → Etale (torsion G n).hom → IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → ∀ (Y : Over (Sp T)) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ p = 1 → x = 1 := by
  intro T K _ _ _ _ _ _ Ga G _ _ _ _ p n hp hsep hA hB hiso Y x hx hxp
  have hq : (torsion.ι Ga n ≫ p) ^ n = 1 := by
    rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp]
  let q : torsion Ga n ⟶ torsion G n := torsionLift _ hq
  let e : torsion Ga n ⟶ torsion G n := torsionLift 1 (one_pow n)
  have hopen := GlobalTheory.isOpenImmersion_equalizer_ι_left_of_unramified q e
  have hflat : Flat (equalizer q e).hom := by
    rw [← Over.w (equalizer.ι q e)]
    infer_instance
  have h1 : (equalizer.ι q e ≫ torsion.ι Ga n) ≫ p = (1 : equalizer q e ⟶ Ga) ≫ p := by
    have := equalizer.condition q e =≫ torsion.ι G n
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one] at this
    rw [Category.assoc, this, MonObj.one_comp]
  have h2 : equalizer.ι q e ≫ torsion.ι Ga n = 1 := by
    apply eq_of_generic T K
    rw [← cancel_mono ((Over.pullback (spMap (algebraMap T K))).map p), ← Functor.map_comp,
      ← Functor.map_comp, h1]
  have h3 : torsionLift x hx ≫ q = torsionLift x hx ≫ e := by
    apply torsion_hom_ext
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one,
      ← Category.assoc, torsionLift_ι, hxp]
  rw [← torsionLift_ι x hx, ← equalizer.lift_ι (torsionLift x hx) h3, Category.assoc, h2,
    MonObj.comp_one]
end GlobalTheory.KernelNoTorsion
