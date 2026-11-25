-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellUnion_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:46:10.206971+00:00
-- url     : https://prove2.me/submissions/59412a99-f67c-4186-aa9e-9bd34d7f83b2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaGraded
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaUnnormalized
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_cellUnion


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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {k : ℕ} (w : Fin k → Equiv.Perm (Fin n)) (j : ℕ) :
    (∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) j, ∀ q ∈ blockUpper F n γ, g * q ∈ cellUnion (fun l => doubleCoset
          (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j) ∧
      (∀ p ∈ blockUpper F n β, ∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j, p * g ∈ cellUnion
          (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
            (blockUpper F n γ)) j) := by
  constructor
  · intro g hg q hq
    obtain ⟨l, hl, hgl⟩ := (mem_cellUnion _).1 hg
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_doubleCoset.1 hgl
    exact (mem_cellUnion _).2 ⟨l, hl, mem_doubleCoset.2 ⟨p', hp', q' * q,
      (blockUpper F n γ).mul_mem hq' hq, by group⟩⟩
  · intro p hp g hg
    obtain ⟨l, hl, hgl⟩ := (mem_cellUnion _).1 hg
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_doubleCoset.1 hgl
    exact (mem_cellUnion _).2 ⟨l, hl, mem_doubleCoset.2 ⟨p * p',
      (blockUpper F n β).mul_mem hp hp', q', hq', by group⟩⟩
end GroundTheory.Automorphic.Parabolic
