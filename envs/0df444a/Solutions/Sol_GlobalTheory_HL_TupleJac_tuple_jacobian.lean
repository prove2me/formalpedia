-- Prove2me | solution 1 for GlobalTheory.HL.TupleJac.tuple_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:32:29.712925+00:00
-- url     : https://prove2.me/submissions/4f621cdf-1195-4641-b473-50a16890eb0f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
import Theorems.Thm_GlobalTheory_HL_TupleJac_cont_linearEquiv
import Theorems.Thm_GlobalTheory_HL_TupleJac_det_rmulL
import Theorems.Thm_GlobalTheory_HL_TupleJac_det_isom
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.TupleJac
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m
  refine ⟨fun A hA => ?_, fun g hg T hT => ?_⟩
  · obtain ⟨N, hN⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by simp [L.cj_cj, mul_comm])
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [map_zero] at hN
      exact (hA.mul (hA.map L.cj)).ne_zero hN.symm
    obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).2.2.2 N hN0
    have hdet : IsUnit (LinearMap.det (TupleJac.rmulL (n := n) A)) := by
      rw [TupleJac.det_rmulL]; exact hA.pow n
    have hφ : (LinearMap.equivOfIsUnitDet hdet).toLinearMap = TupleJac.rmulL (n := n) A :=
      LinearMap.coe_equivOfIsUnitDet hdet
    have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m (LinearMap.equivOfIsUnitDet hdet)
      (vE L ϖ (A.det * L.cj A.det) * n) (u ^ n) (by
        rw [hφ, TupleJac.det_rmulL, map_pow, ← mul_pow, ← hN, ← map_pow]
        congr 1
        conv_lhs => rw [hu]
        rw [mul_pow, zpow_mul, zpow_natCast]
        simp)
    have hfun : (LinearMap.equivOfIsUnitDet hdet : _ → _) = fun x => rmul x A :=
      funext fun x => LinearMap.congr_fun hφ x
    rw [hfun] at key
    exact key
  · have key := TupleJac.cont_linearEquiv L ϖ hϖ Hm hH Λ hΛ m
      (LinearEquiv.piCongrRight fun _ => g) 0 1 (by
        have h : (LinearEquiv.piCongrRight fun _ : Fin m => g).toLinearMap =
            LinearMap.pi fun i : Fin m => g.toLinearMap ∘ₗ LinearMap.proj i := rfl
        rw [h, LinearMap.det_pi, Finset.prod_const, map_pow, ← mul_pow,
          TupleJac.det_isom L Hm hH.2 g hg]
        simp) T hT
    rw [neg_zero, zpow_zero, one_mul] at key
    exact key
end GlobalTheory.HL.TupleJac
