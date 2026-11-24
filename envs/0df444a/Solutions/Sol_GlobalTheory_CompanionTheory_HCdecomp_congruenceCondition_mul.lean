-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.congruenceCondition_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:38:20.650825+00:00
-- url     : https://prove2.me/submissions/392d34dc-3169-4fc9-9644-4a4f8d356e04

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_mul
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.HCdecomp
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} {T S : Module.End ℂ V} (hT : T ∈ PP E)
    {m : ℕ} (hS : adH E S = (m : ℂ) • S) : T * S ∈ PP E := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨k, hk⟩ := h
    refine Submodule.subset_span ⟨k + m, ?_⟩
    rw [adH_mul, hk, hS, smul_mul_assoc, mul_smul_comm, ← add_smul]
    congr 1; push_cast; ring
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact (PP E).add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact (PP E).smul_mem c hx
end GlobalTheory.CompanionTheory.HCdecomp
