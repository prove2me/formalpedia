-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.expG_expChartFlow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:04.980718+00:00
-- url     : https://prove2.me/submissions/f62d454e-c809-4156-b373-6acbc2f185e3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_val_expG_mul_expG
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {p : EuclideanSpace ℝ (Fin d) × ℝ} (hp : expChartProd b X p ∈ h.nhdOne) :
    h.expG (coordEquiv b (expChartFlow b X p)) = h.expG (coordEquiv b p.1) * h.expG (p.2 • X) := by
  set w : G := h.expG (coordEquiv b p.1) * h.expG (p.2 • X) with hw
  have hwv : ((w : 𝔸ˣ) : 𝔸) = expChartProd b X p := h.val_expG_mul_expG b X p
  have hwN : ((w : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hwv ▸ hp
  have hmem := h.symm_mem_lie hwN
  have e1 : coordEquiv b (expChartFlow b X p) =
      subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm ((w : 𝔸ˣ) : 𝔸)) := by
    rw [hwv]; exact (coordEquiv b).apply_symm_apply _
  apply Subtype.ext; apply Units.ext
  rw [coe_expG, e1, subspaceProj_of_mem hmem, h.exp_symm hwN]
end GroundTheory.Automorphic.IsExpLieAlgebra
