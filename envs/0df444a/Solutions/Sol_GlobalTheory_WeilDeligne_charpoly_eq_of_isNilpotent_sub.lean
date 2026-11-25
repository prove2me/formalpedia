-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.charpoly_eq_of_isNilpotent_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:34.385739+00:00
-- url     : https://prove2.me/submissions/8bdf4139-8090-405c-9739-e00a347ebb46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {f g : End K V} (hc : Commute f g)
    (hn : IsNilpotent (g - f)) : f.charpoly = g.charpoly := by
  refine eq_of_infinite_eval_eq _ _ ((f.charpoly.finite_setOfPred_isRoot
    (LinearMap.charpoly_monic f).ne_zero).infinite_compl.mono fun t ht => ?_)
  have hu : IsUnit (algebraMap K (End K V) t - f) := by
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.eval_charpoly]
    exact isUnit_iff_ne_zero.mpr ht
  obtain ⟨u, hu⟩ := hu
  have h1 : Commute (u : End K V) (g - f) := by
    rw [hu]
    exact (Algebra.commute_algebraMap_left t _).sub_left (hc.sub_right (Commute.refl f))
  have h2 : IsNilpotent ((↑u⁻¹ : End K V) * (g - f)) :=
    h1.units_inv_left.isNilpotent_mul_left hn
  have h3 : LinearMap.det (1 - (↑u⁻¹ : End K V) * (g - f)) = 1 := by
    have := LinearMap.eval_charpoly ((↑u⁻¹ : End K V) * (g - f)) 1
    rw [h2.charpoly_eq_X_pow_finrank, map_one] at this
    simpa using this.symm
  have h4 : algebraMap K (End K V) t - g = u * (1 - (↑u⁻¹ : End K V) * (g - f)) := by
    rw [mul_sub, Units.mul_inv_cancel_left, mul_one, hu]; abel
  show _ = _
  rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly, h4, map_mul, h3, mul_one, hu]
end GlobalTheory.WeilDeligne
