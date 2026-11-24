-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.Red.mul_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:25.428685+00:00
-- url     : https://prove2.me/submissions/6149a8ab-fc88-403f-add4-aee61dc17a49

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_JJ_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.HCdecomp
namespace Red
theorem _root_.solution {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (p : Fin n × Fin n)
    (hp : p.2 ≤ p.1) : Red (a * FreeAlgebra.ι ℂ p) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨_, Low.mul u p hu hp, fun V _ _ E hE => ?_⟩
  rw [map_mul, map_mul, ← sub_mul]
  exact JJ_mul E (h V E hE) _
end Red
end GlobalTheory.CompanionTheory.HCdecomp
