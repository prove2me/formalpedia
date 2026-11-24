-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.mem_JJ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:05:24.127694+00:00
-- url     : https://prove2.me/submissions/20e27e42-2c02-4823-a96a-553c8c4db81c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_JJ
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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) {t p : Module.End ℂ V}
    (ht : adH E t = 0) (hp : p ∈ PP E) (h : t - p ∈ JJ E) : t ∈ JJ E := by
  set D : Module.End ℂ (Module.End ℂ V ⧸ JJ E) := (JJ E).mapQ (JJ E) (adH E) (adH_JJ hE) with hD
  have hd := iSupIndep_def.mp (Module.End.eigenspaces_iSupIndep D) 0
  have h1 : (JJ E).mkQ t ∈ D.eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, ht]
    rfl
  have h2 : (JJ E).mkQ p ∈ ⨆ j, ⨆ (_ : j ≠ (0 : ℂ)), D.eigenspace j := by
    clear h
    induction hp using Submodule.span_induction with
    | mem T h =>
      obtain ⟨k, hk⟩ := h
      refine Submodule.mem_iSup_of_mem ((k : ℂ) + 1) (Submodule.mem_iSup_of_mem
        (Nat.cast_add_one_ne_zero k) ?_)
      rw [Module.End.mem_eigenspace_iff, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, hk]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h3 : (JJ E).mkQ t = (JJ E).mkQ p := (Submodule.Quotient.eq _).mpr h
  rw [← h3] at h2
  have := (Submodule.disjoint_def.mp hd) _ h1 h2
  exact (Submodule.Quotient.mk_eq_zero _).mp this
end GlobalTheory.CompanionTheory.HCdecomp
