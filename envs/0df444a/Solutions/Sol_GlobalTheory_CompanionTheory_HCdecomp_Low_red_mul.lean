-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.Low.red_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:22.42688+00:00
-- url     : https://prove2.me/submissions/0875533c-2437-4382-b579-d9662419f33c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_mem_NV
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HCdecomp_ev___e9a5711aa8dc
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Low_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_add
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_of_low
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_mul_low
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
namespace GlobalTheory.CompanionTheory.HCdecomp
namespace Low
theorem _root_.solution {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) :
    ∀ p : Fin n × Fin n, Red (u * FreeAlgebra.ι ℂ p) := by
  induction hu with
  | one =>
    intro p
    rcases le_or_gt p.2 p.1 with h | h
    · exact Red.of_low (Low.mul _ p Low.one h)
    · refine ⟨0, Low.zero, fun V _ _ E _ => ?_⟩
      rw [one_mul, map_zero, sub_zero, ev_ι]
      exact fun x => mem_NV E h x
  | mul u y _ hy ih =>
    intro p
    have h1 : Red (if y.2 = p.1 then u * FreeAlgebra.ι ℂ (y.1, p.2) else 0) := by
      split_ifs
      · exact ih _
      · exact Red.of_low Low.zero
    have h2 : Red (if p.2 = y.1 then u * FreeAlgebra.ι ℂ (p.1, y.2) else 0) := by
      split_ifs
      · exact ih _
      · exact Red.of_low Low.zero
    refine ((((ih p).mul_low y hy).add h1).add (h2.smul (-1))).congr fun V _ _ E hE => ?_
    have h := sub_eq_iff_eq_add.mp (hE y.1 y.2 p.1 p.2)
    simp only [map_add, map_mul, ev_ι, map_smul, apply_ite (ev E), map_zero, mul_assoc, h]
    split_ifs <;> simp [mul_add, mul_sub] <;> abel
  | add u v _ _ hu hv => intro p; rw [add_mul]; exact (hu p).add (hv p)
  | smul c u _ hu => intro p; rw [smul_mul_assoc]; exact (hu p).smul c
end Low
end GlobalTheory.CompanionTheory.HCdecomp
