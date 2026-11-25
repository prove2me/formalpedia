-- Prove2me | solution 1 for GlobalTheory.JR.Step.MatchNotIm.hasInv_liftH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:39:56.30584+00:00
-- url     : https://prove2.me/submissions/96f59ea3-1817-404a-9491-10472d66bc8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_full_act
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_conj_last
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_eL_dot
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_full_glMap
import Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_conj_pow
import Theorems.Thm_GlobalTheory_JR_Step_InvMap_Delta_map
import Theorems.Thm_GlobalTheory_JR_Step_InvMap_inv_glMap
import Theorems.Thm_GlobalTheory_T_jacquetRallis_borderedMatrix_normalForm_invariants


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.MatchNotIm
namespace GlobalTheory.JR.Step.MatchNotIm
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 →
    HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν _ _ hΔ hX
  have hΔ' : Delta (inv (glMap (algebraMap F E) Z)) ≠ 0 := by
    rw [InvMap.inv_glMap, InvMap.Delta_map]
    exact (map_ne_zero (algebraMap F E)).2 hΔ
  have hX' : inv X.toGl = inv (glMap (algebraMap F E) Z) := by
    rw [InvMap.inv_glMap]; exact hX
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E r).2.2.2.2 _ _ hΔ' hX'
  have hfull : full X.toGl = embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
    rw [← hg, full_act, full_glMap]
  have hPQ : embHom r E (g : Matrix (Fin r) (Fin r) E) * embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hQP : embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * embHom r E (g : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hs : star (ν • eL r E) = star ν • eL r E := by
    funext j
    simp only [Pi.star_apply, Pi.smul_apply, eL, Pi.single_apply, smul_eq_mul, star_mul']
    split_ifs <;> simp [mul_comm]
  replace hfull : full ((X.1.1, X.2.1, star X.2.1, algebraMap F E X.2.2) : Gl r E) =
      embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := hfull
  unfold HasInv
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift]
    rw [hfull]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift, mom]
    rw [hs, hfull, conj_pow _ _ _ hPQ hQP, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, eL_dot, eL_dot, conj_last]
    have hp : ((full Z).map (algebraMap F E)) ^ (i : ℕ) = ((full Z) ^ (i : ℕ)).map (algebraMap F E) := by
      have := map_pow (algebraMap F E).mapMatrix (full Z) (i : ℕ)
      simpa only [RingHom.mapMatrix_apply] using this.symm
    rw [hp, Matrix.map_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, ← hν]
    ring
end GlobalTheory.JR.Step.MatchNotIm
