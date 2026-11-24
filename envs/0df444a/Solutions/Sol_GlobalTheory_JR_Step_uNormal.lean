-- Prove2me | solution 1 for GlobalTheory.JR.Step.uNormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:18.438877+00:00
-- url     : https://prove2.me/submissions/29266300-3d91-43b1-a086-da8cf2fc5704

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant
import Theorems.Thm_GlobalTheory_JR_Step_UNormal_exists_algebraMap_of_star_eq
import Theorems.Thm_GlobalTheory_JR_Step_UNormal_full_cc
import Theorems.Thm_GlobalTheory_JR_Step_UNormal_full_cl
import Theorems.Thm_GlobalTheory_JR_Step_UNormal_full_lc
import Theorems.Thm_GlobalTheory_JR_Step_UNormal_full_ll
import Theorems.Thm_GlobalTheory_T_exists_mul_star_eq_of_norm_one_unramifiedQuadratic
import Theorems.Thm_GlobalTheory_unitary_transitive_of_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
open GlobalTheory.JR.Step.UNormal
namespace GlobalTheory.JR.Step
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (X : Hn (r + 1) F E) (a : Inv (r + 1) F), HasInv X a →
    ‖a.2.1 0‖ = 1 → ∃ (g : Matrix.unitaryGroup (Fin (r + 1)) E) (X' : Hn r F E) (ν : E),
      ν * star ν = algebraMap F E (a.2.1 0) ∧ actU g X = GlobalTheory.JR.Step.liftH X' ν a.2.2 := by
  intro F E _ _ _ _ _ r X a hX ha
  have h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0) := by
    have := congrArg (fun p => p.2.1 0) hX
    simpa [inv, mom, Hn.toGl, Inv.map] using this
  have hl : X.2.2 = a.2.2 := by
    have := congrArg (fun p => p.2.2) hX
    simp only [inv, Hn.toGl, Inv.map] at this
    exact (algebraMap F E).injective this
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (a.2.1 0) ha
  have ha0 : algebraMap F E (a.2.1 0) ≠ 0 := by
    rw [map_ne_zero]
    intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hνn : star (ν • eL r E) ⬝ᵥ (ν • eL r E) = ν * star ν := by
    simp [eL, dotProduct, Pi.single_apply, mul_comm]
  have hv : star X.2.1 ⬝ᵥ X.2.1 = star (ν • eL r E) ⬝ᵥ (ν • eL r E) := by
    rw [h0, hνn, hν]
  obtain ⟨g, hg⟩ := GlobalTheory.unitary_transitive_of_norm F E (r + 1) X.2.1 _ hv (h0 ▸ ha0)
  set M := g.1 * X.1.1 * star g.1 with hMdef
  have hM : Mᴴ = M := IsSelfAdjoint.conjugate X.1.2 g.1
  have hMe : ∀ i j, M j i = star (M i j) := by
    intro i j
    have := congrFun (congrFun hM j) i
    rw [conjTranspose_apply] at this
    exact this.symm
  obtain ⟨l', hl'⟩ := exists_algebraMap_of_star_eq (F := F) (M (Fin.last r) (Fin.last r))
    (hMe _ _).symm
  have hsub : M.submatrix Fin.castSucc Fin.castSucc ∈ selfAdjoint (Matrix (Fin r) (Fin r) E) := by
    rw [selfAdjoint.mem_iff, star_eq_conjTranspose, conjTranspose_submatrix, hM]
  refine ⟨g, (⟨M.submatrix Fin.castSucc Fin.castSucc, hsub⟩, fun i => M (Fin.castSucc i) (Fin.last r), l'), ν, hν, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Subtype.ext
    show M = full _
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rw [full_ll]; simp [Hn.toGl, hl']
      | cast j => rw [full_lc]; simp [Hn.toGl, hMe (Fin.castSucc j) (Fin.last r)]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [full_cl]; simp [Hn.toGl]
      | cast j => rw [full_cc]; simp [Hn.toGl]
  · exact hg
  · exact hl
end GlobalTheory.JR.Step
