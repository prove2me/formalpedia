-- Prove2me | solution 1 for GlobalTheory.sec_eq_zero_of_thickenings_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:22:57.850883+00:00
-- url     : https://prove2.me/submissions/db6c9eb7-0391-4f5e-81de-49695742f87a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Theorems.Thm_GlobalTheory_ThickeningDetermines_eq_zero_of_secIdeal_eq_bot
import Theorems.Thm_GlobalTheory_ThickeningDetermines_secIdeal_le_ker
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres
import Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_thickenings


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
open GlobalTheory
open ThickeningDetermines
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [Smooth H.hom] [GeometricallyConnected H.hom] (e : 𝟙_ _ ⟶ H) (N : LB H.left) (hN : N.IsLB)
    (s : LB.Sec N) (hs : ∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) (j) :
    s.f j = 0 := by
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom
  have key := isIso_of_isClosedImmersion_of_thickenings R I hI H e (fun p ↦ inferInstance)
  refine eq_zero_of_secIdeal_eq_bot hN s ?_ j
  have := key _ (secIdeal hN s).subschemeι fun n ↦ by
    have : IsClosedImmersion (thick R I n) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : QuasiCompact (fstG I n H).left :=
      inferInstanceAs (QuasiCompact (pullback.fst H.hom (thick R I n)))
    exact ⟨IsClosedImmersion.lift _ (fstG I n H).left (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact secIdeal_le_ker hN s _ (hs n)), IsClosedImmersion.lift_fac _ _ _⟩
  rw [← Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 this
end GlobalTheory
