-- Prove2me | solution 1 for GlobalTheory.NonUnitShift.exists_not_isUnit_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:42:37.188722+00:00
-- url     : https://prove2.me/submissions/0770478c-ee32-41d3-bb39-4f5e4993d932

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentResolvent
import Theorems.Thm_GlobalTheory_NonUnitShift_linearIndependent_resolvent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonUnitShift
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.NonUnitShift
theorem _root_.solution : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] [Nontrivial V], Module.rank ℂ V ≤ Cardinal.aleph0 → ∀ (T : Module.End ℂ V), ∃ (c : ℂ), ¬IsUnit (T - (Algebra.algebraMap ℂ (Module.End ℂ V) : ℂ → Module.End ℂ V) c) := by
  intro V _ _ _ hrank T
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let w : ℂ → V := fun c => (((hcon c).unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) v
  have hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v := fun c => by
    have h1 : ((hcon c).unit : Module.End ℂ V) * (((hcon c).unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = 1 :=
      (hcon c).unit.mul_inv
    rw [IsUnit.unit_spec] at h1
    have h2 := congrArg (fun f : Module.End ℂ V => f v) h1
    simp only [Module.End.mul_apply, Module.End.one_apply] at h2
    exact h2
  have hli := linearIndependent_resolvent T hcon v hv w hw
  have h1 : Cardinal.mk ℂ ≤ Cardinal.aleph0 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)
end GlobalTheory.NonUnitShift
