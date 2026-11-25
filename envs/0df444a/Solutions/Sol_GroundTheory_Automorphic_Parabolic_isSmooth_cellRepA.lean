-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_cellRepA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:24.982802+00:00
-- url     : https://prove2.me/submissions/734ddd01-4ef5-4fbe-80bc-c54849321b6a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_cellRep_fixed
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_continuous_permGL_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hσ : IsSmooth σ) : IsSmooth (cellRepA β γ w σ) := by
  intro v
  obtain ⟨j, hj⟩ := exists_cellRep_fixed (w := w) hσ v
  let U : Subgroup (cellUnipotent F β γ w) :=
    ((congruenceSubgroup F n j).comap (MulAut.conj (permGL F w)).toMonoidHom).subgroupOf _
  refine Subgroup.isOpen_mono (H₁ := U) (fun a ha => ?_) ?_
  · rw [mem_stabilizerOf]
    exact hj _ ha
  · show IsOpen (Subtype.val ⁻¹' ((fun x : GL (Fin n) F => permGL F w * x * (permGL F w)⁻¹) ⁻¹'
      (congruenceSubgroup F n j : Set (GL (Fin n) F))))
    exact ((isOpen_congruenceSubgroup F n j).preimage (continuous_permGL_conj w)).preimage
      continuous_subtype_val
end GroundTheory.Automorphic.Parabolic
