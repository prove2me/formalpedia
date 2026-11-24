-- Prove2me | solution 1 for GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:31.113856+00:00
-- url     : https://prove2.me/submissions/3e5182d1-e474-407a-8374-fa4811487499

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOver
import Theorems.Thm_GlobalTheory_FibrePowerProper_isProper_fan_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibrePowerProper
namespace GlobalTheory.FibrePowerProper
theorem _root_.solution : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)),
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) →
    IsProper C.hom → IsProper B.hom := by
  intro T B C pr hu hC
  have hl : IsLimit (Fan.mk B pr) :=
    Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose)
      (fun s a => (hu s.pt s.proj).choose_spec.1 a)
      (fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm)
  exact isProper_fan_pt 8 (fun _ => C) (fun _ => hC) _ hl
end GlobalTheory.FibrePowerProper
