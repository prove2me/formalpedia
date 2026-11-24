-- Prove2me | solution 1 for GlobalTheory.HodgeTateImage.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:23:28.133903+00:00
-- url     : https://prove2.me/submissions/826c122a-1dc4-4c6b-8b9a-617135c665a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Theorems.Thm_GlobalTheory_HodgeTateImage_unitAt_map
import Theorems.Thm_GlobalTheory_HodgeTateImage_pow_quot
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HodgeTateImage
open GlobalTheory.TangentPow GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}
variable (χ : Tv G p)
namespace GlobalTheory.HodgeTateImage
theorem _root_.solution (n : ℕ) (x : LieG G) : ∃ a : O, ∀ (R : Type) [CommRing R] [Algebra O R]
    (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (unitAt χ (pow_quot (O := O) n) x).snd
  refine ⟨a, fun R _ _ hR => ?_⟩
  let φ : (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O] R :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId O R) fun c hc => by
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      simp [hR]
  rw [unitAt_map χ φ (pow_quot n) hR, ← ha]
  exact (φ.commutes a).symm
end GlobalTheory.HodgeTateImage
