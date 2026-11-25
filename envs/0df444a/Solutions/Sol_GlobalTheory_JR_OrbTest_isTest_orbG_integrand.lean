-- Prove2me | solution 1 for GlobalTheory.JR.OrbTest.isTest_orbG_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:39:54.893545+00:00
-- url     : https://prove2.me/submissions/7d5be89e-f130-47b8-b692-03fbb77e56a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProperStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCo
import Theorems.Thm_GlobalTheory_JR_OrbTest_isLocallyConstant_eta_comp
import Theorems.Thm_GlobalTheory_JR_OrbTest_continuous_act
import Theorems.Thm_GlobalTheory_T_jacquetRallis_borderedMatrix_normalForm_invariants
import Theorems.Thm_GlobalTheory_T_jacquetRallis_orbit_invariant_map_proper
import Theorems.Thm_GlobalTheory_T_jacquetRallis_transfer_factor_krylov_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbTest
namespace GlobalTheory.JR.OrbTest
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f' : Gl r F → ℂ) (hf : IsTest f') (Y : Gl r F)
    (hY : Delta (inv Y) ≠ 0) :
    IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y)) := by
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨-, hL1b, hL1c, hL1d, hL1e⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  obtain ⟨hL6a, hL6b⟩ := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  obtain ⟨-, -, -, hL4⟩ := GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper F E r
  have hC : (Cm Y).det ≠ 0 := by
    intro h0; apply hY; rw [Delta, ← hL1c Y, Matrix.det_mul, h0, zero_mul]
  have hld : (fun g : GL (Fin r) F => lastDet (act g Y)) = fun g =>
      (-1) ^ r * ((Cm Y).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) := by
    funext g; rw [hL6a, hL6b, Matrix.det_mul]
  refine ⟨?_, ?_⟩
  · refine IsLocallyConstant.comp₂ (hf.1.comp_continuous (continuous_act Y)) ?_ (fun a b => a * b)
    show IsLocallyConstant (fun g : GL (Fin r) F => eta (lastDet (act g Y)))
    refine isLocallyConstant_eta_comp (fun g : GL (Fin r) F => lastDet (act g Y)) ?_ ?_
    · rw [hld]
      exact continuous_const.mul (continuous_const.mul Units.continuous_coe_inv.matrix_det)
    · intro g
      rw [show lastDet (act g Y) = _ from congrFun hld g]
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hC ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit).ne_zero
  · have ha : Delta (inv (sec (inv Y))) ≠ 0 := by rw [hL1b]; exact hY
    obtain ⟨g₀, ⟨hg₀, -⟩, -⟩ := hL1e (sec (inv Y)) Y ha (hL1b _).symm
    have hS : IsCompact {h : GL (Fin r) F | act h (sec (inv Y)) ∈ tsupport f'} := by
      have := hL4 (tsupport f') {inv Y} hf.2 isCompact_singleton (by rintro b rfl; exact hY)
      convert this.image continuous_fst using 1
      ext h; constructor
      · intro hh; exact ⟨(h, inv Y), ⟨rfl, hh⟩, rfl⟩
      · rintro ⟨⟨h', a'⟩, ⟨ha', hc⟩, rfl⟩
        simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
    have hK : IsCompact {g : GL (Fin r) F | act g Y ∈ tsupport f'} := by
      have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
      convert this using 1
      ext g; simp [Homeomorph.coe_mulRight, hL1d, hg₀]
    refine HasCompactSupport.intro' hK ((isClosed_tsupport f').preimage (continuous_act Y)) ?_
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [image_eq_zero_of_notMem_tsupport hg, zero_mul]
end GlobalTheory.JR.OrbTest
