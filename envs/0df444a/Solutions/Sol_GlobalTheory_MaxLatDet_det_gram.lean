-- Prove2me | solution 1 for GlobalTheory.MaxLatDet.det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:53.177431+00:00
-- url     : https://prove2.me/submissions/a7250cf3-6597-45aa-ba41-c1f10d5782f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDet
import Theorems.Thm_GlobalTheory_MaxLatDet_form_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MaxLatDet
open IsDedekindDomain
variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
namespace GlobalTheory.MaxLatDet
theorem _root_.solution [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (e b : Module.Basis ι K V)
    (he : ∀ i l, i ≠ l → h (e i) (e l) = 0) :
    ∃ δ : K, δ ≠ 0 ∧ (Matrix.of fun i l => h (b i) (b l)).det = star δ * δ * ∏ i, h (e i) (e i) := by
  have hT : IsUnit (e.toMatrix b).det := by
    letI := e.invertibleToMatrix b
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨(e.toMatrix b).det, hT.ne_zero, ?_⟩
  have : (Matrix.of fun i l => h (b i) (b l)) =
      (e.toMatrix b)ᴴ * Matrix.diagonal (fun i => h (e i) (e i)) * e.toMatrix b := by
    ext i l
    rw [Matrix.of_apply, form_eq_sum h e he, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Module.Basis.toMatrix_apply,
      Module.Basis.toMatrix_apply]
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal]
  ring
end GlobalTheory.MaxLatDet
