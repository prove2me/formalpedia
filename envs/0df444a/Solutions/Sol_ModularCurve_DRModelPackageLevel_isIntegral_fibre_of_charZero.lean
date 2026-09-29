-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.isIntegral_fibre_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9919fd5a-3697-5071-aca1-ac3d850445dc

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel IgusaScheme"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "geomIntegral_generic comp"
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

namespace GenAux

theorem ringHom_eq_comp {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [CharZero k] (toκ : R q →+* k) :
    toκ = (algebraMap ℚ k).comp (algebraMap (R q) ℚ) := by
  have hq : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(q : ℤ)}).primeCompl (RingHom.ext_int _ _)

end GenAux

end ModularCurve.DRModelPackageLevel

open _root_.ModularCurve.DRModelPackageLevel _root_.P2MW.S_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero.ModularCurve.DRModelPackageLevel in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (k : Type) [Field k] [CharZero k] (toκ : R q →+* k) :
    IsIntegral (fibre (N₀ := N₀) toκ) := by
  have hS : Spec.map (CommRingCat.ofHom toκ) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ k)) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R q) ℚ)) := by
    rw [GenAux.ringHom_eq_comp toκ, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI := 𝔓.geomIntegral_generic
  haveI : IsIntegral (pullback (pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) ℚ))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ k)))) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  exact IsIntegral.of_isIso
    ((pullbackLeftPullbackSndIso (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) ℚ)))
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ k)))) ≪≫ pullback.congrHom rfl hS.symm).hom

end S_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero (solution)
