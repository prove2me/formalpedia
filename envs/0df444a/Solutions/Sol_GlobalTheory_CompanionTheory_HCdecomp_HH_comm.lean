-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.HH_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:28.978142+00:00
-- url     : https://prove2.me/submissions/9cc100ed-0f09-4d0b-aba0-fc8c3f03f4cb

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    HH E * E a b - E a b * HH E = (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) • E a b := by
  have h : ∀ c : Fin n, ((c : ℕ) : ℂ) • E c c * E a b - E a b * ((c : ℕ) : ℂ) • E c c =
      (if c = a then ((a : ℕ) : ℂ) • E a b else 0) - (if c = b then ((b : ℕ) : ℂ) • E a b else 0) := by
    intro c
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hE c c a b, smul_sub]
    congr 1
    · split_ifs with h
      · subst h; rfl
      · simp
    · by_cases h : b = c
      · subst h; simp
      · simp [h, Ne.symm h]
  rw [HH, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_smul]
end GlobalTheory.CompanionTheory.HCdecomp
