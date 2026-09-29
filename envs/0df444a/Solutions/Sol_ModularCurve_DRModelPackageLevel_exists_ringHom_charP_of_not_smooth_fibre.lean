-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_ringHom_charP_of_not_smooth_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c17fd575-c7c5-59a9-a36e-37e58e53c7b7

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_ringHom_charP_of_not_smooth_fibre

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    {k : Type} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q)))
    (hns : ¬ Smooth (pullback.snd (DRLevel.toBase N₀ q) s)) :
    ∃ (toκ : DRLevel.R q →+* k) (_ : CharP k q), s = Spec.map (CommRingCat.ofHom toκ) := by
  classical
  let toκ : DRLevel.R q →+* k := (Spec.preimage s).hom
  have hs : Spec.map (CommRingCat.ofHom toκ) = s := by
    simp only [toκ, CommRingCat.ofHom_hom, Spec.map_preimage]
  letI : Algebra (DRLevel.R q) k := toκ.toAlgebra
  have hqp : q.Prime := Fact.out
  rcases GaloisRep.charZero_or_charP_of_algebra_ratLocalizedAt q k with h0 | hq
  ·
    exfalso
    apply hns
    haveI := h0
    haveI := GaloisRep.isFractionRing_ratLocalizedAt q
    haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
    haveI := GaloisRep.ratLocalizedAt.isLocalRing hqp

    have hinj : Function.Injective toκ := by
      rw [RingHom.injective_iff_ker_eq_bot]
      by_contra hne
      have hprime : (RingHom.ker toκ).IsPrime := RingHom.ker_isPrime toκ
      have hmax : (RingHom.ker toκ).IsMaximal := by
        haveI := hprime
        exact IsPrime.to_maximal_ideal hne
      have heq : RingHom.ker toκ = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal hmax
      have hqmem : ((q : ℕ) : DRLevel.R q) ∈ RingHom.ker toκ := by
        rw [heq, GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hqp]
        exact Ideal.subset_span rfl
      rw [RingHom.mem_ker, map_natCast] at hqmem
      exact hqp.ne_zero ((Nat.cast_eq_zero (R := k)).mp hqmem)
    let f : ℚ →+* k := IsFractionRing.lift hinj
    have hf : f.comp (algebraMap (DRLevel.R q) ℚ) = toκ :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    have hs' : s = Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) ℚ)) := by
      rw [← hs, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
    rw [hs']
    haveI := 𝔓.smooth_generic
    have hsnd : pullback.snd (DRLevel.toBase N₀ q)
        (Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) ℚ))) =
        (pullbackLeftPullbackSndIso (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) ℚ)))
          (Spec.map (CommRingCat.ofHom f))).inv ≫
        pullback.snd (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) ℚ))))
          (Spec.map (CommRingCat.ofHom f)) := by
      rw [← pullbackLeftPullbackSndIso_hom_snd, Iso.inv_hom_id_assoc]
    rw [hsnd]
    infer_instance
  · exact ⟨toκ, hq, hs.symm⟩

end S_ModularCurve_DRModelPackageLevel_exists_ringHom_charP_of_not_smooth_fibre
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_ringHom_charP_of_not_smooth_fibre (solution)
