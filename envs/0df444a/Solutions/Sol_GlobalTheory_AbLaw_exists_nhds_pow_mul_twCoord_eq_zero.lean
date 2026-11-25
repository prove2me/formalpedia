-- Prove2me | solution 1 for GlobalTheory.AbLaw.exists_nhds_pow_mul_twCoord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:50.330664+00:00
-- url     : https://prove2.me/submissions/37106e8e-eb6c-4877-bb8f-217998d86160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNhdsPowMulTwCoordEqZero
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution {Y : Scheme.{0}} {H M : LB Y} {d : ℤ}
    (σ : LB.Sec (pw H d)) {t : ℤ} (hH : H.IsLB) (hM : M.IsLB) (a : SecOn (tw M H t) ⊤)
    (ha : SecOn.restrict _ (le_top : nonzeroLocus σ ≤ ⊤) a = 0) (x : Y) :
    ∃ (W : Y.Opens) (n : ℕ), x ∈ W ∧ ∀ (p : M.ι) (l : H.ι) (O : Y.Opens) (_ : O ≤ W)
      (h : O ≤ ⊤ ⊓ (M.U p ⊓ H.U l)),
      rs Y (h.trans (inf_le_right.trans inf_le_right) : O ≤ H.U l) (σ.f l) ^ n *
        rs Y h (SecOn.twCoord a p l) = 0 := by
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))
  have hx : x ∈ (⊤ ⊓ (M.U q ⊓ H.U k) : Y.Opens) := ⟨trivial, hq, hk⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (⊤ ⊓ (M.U q ⊓ H.U k) : Y.Opens).2
  have hWU' : W ≤ ⊤ ⊓ (M.U q ⊓ H.U k) := hWU
  have hWk : W ≤ H.U k := hWU'.trans (inf_le_right.trans inf_le_right)
  have hb : Y.basicOpen (rs Y hWk (σ.f k)) ≤ nonzeroLocus σ ⊓ (M.U q ⊓ H.U k) := by
    refine le_inf ?_ ((Y.basicOpen_le _).trans (hWU'.trans inf_le_right))
    refine le_trans ?_ (le_iSup (fun j => Y.basicOpen (σ.f j)) k)
    exact (Scheme.basicOpen_res Y (σ.f k) (homOfLE hWk).op).le.trans inf_le_right
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hW
    (rs Y hWU' (SecOn.twCoord a q k)) (rs Y hWk (σ.f k)) (by
      have e := congrArg (fun y => rs Y hb (SecOn.twCoord y q k)) ha
      simp only [SecOn.twCoord_restrict, rs_rs] at e
      exact (rs_rs _ (Y.basicOpen_le _) _).trans (e.trans (map_zero _)))
  refine ⟨W, n, hxW, fun p l O hO h => ?_⟩
  have e := congrArg (rs Y hO) hn
  rw [map_mul, map_pow, rs_rs, rs_rs (U := H.U k) hWk hO (σ.f k), map_zero] at e
  have hl : O ≤ H.U l := h.trans (inf_le_right.trans inf_le_right)
  have hp : O ≤ M.U p := h.trans (inf_le_right.trans inf_le_left)
  have hq' : O ≤ M.U q := hO.trans (hWU'.trans (inf_le_right.trans inf_le_left))
  have e₁ : rs Y hl (σ.f l) = rs Y (le_inf hl (hO.trans hWk)) ((pw H d).g l k).val *
      rs Y (hO.trans hWk) (σ.f k) :=
    GlobalTheory.LB.sec_rel σ l k hl (hO.trans hWk) (le_inf hl (hO.trans hWk))
  rw [SecOn.twCoord_compat a p q l k h (hO.trans hWU') (le_inf hp hq') (le_inf hl (hO.trans hWk)),
    e₁, mul_pow, mul_mul_mul_comm, e, mul_zero]
end GlobalTheory.AbLaw
