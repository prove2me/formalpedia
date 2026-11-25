-- Prove2me | solution 1 for GlobalTheory.Published.SvN.plane_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:07:21.921836+00:00
-- url     : https://prove2.me/submissions/e4e3161d-7056-4a7e-b6b7-f6e9f71c2bf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_Heisenberg_mul_ne_mul
import Theorems.Thm_GlobalTheory_Published_StoneVonNeumann_holds
import Theorems.Thm_GlobalTheory_Published_SvN_exists_char
import Theorems.Thm_GlobalTheory_Published_SvN_planeForm_isAlt
import Theorems.Thm_GlobalTheory_Published_SvN_planeForm_nondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
namespace GlobalTheory.Published.SvN
theorem _root_.solution (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (h2 : (2 : F) ≠ 0) :
    (∃ g k : Heisenberg (planeForm F), g * k ≠ k * g) ∧
    ∃ ψ : AddChar F ℂ, Continuous ψ ∧ ψ ≠ 1 ∧ ∃ (S : Type) (_ : AddCommGroup S) (_ : Module ℂ S)
      (ρ : Representation ℂ (Heisenberg (planeForm F)) S), Heisenberg.IsIrrSmoothOf ψ ρ := by
  refine ⟨⟨_, _, Heisenberg.mul_ne_mul h2 (planeForm_isAlt F) (x := (1, 0)) (y := (0, 1)) (by simp [planeForm])⟩, ?_⟩
  obtain ⟨ψ, h, h'⟩ := exists_char F
  exact ⟨ψ, h, h', (StoneVonNeumann_holds F h2 (F × F) _ (planeForm_isAlt F) (planeForm_nondegenerate F) ψ h h').1⟩
end GlobalTheory.Published.SvN
