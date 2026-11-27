-- Prove2me | solution 1 for GlobalTheory.cechClass_eq_zero_iff_prev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:47.965483+00:00
-- url     : https://prove2.me/submissions/a170ca1a-b976-4e61-a98b-55e41cf93b4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (q p : ℕ)
    (h : (ComplexShape.up ℕ).prev p = q) (x : LinearMap.ker (Cube.d A (p + 1))) :
    cechClass A p x = 0 ↔ ∃ y, ((cechComplex A).d q p).hom y = x.1 := by
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk _ _ ((cechComplex A).toCycles_comp_homologyπ q p))
      ((cechComplex A).homologyIsCokernel q p h))
  refine (hex ((cechCyclesIso A p).inv.hom x)).trans (exists_congr fun y => ?_)
  rw [← iCycles_cechCyclesIso_inv A p x, ← (cechComplex A).toCycles_i q p]
  exact ((ModuleCat.mono_iff_injective ((cechComplex A).iCycles p)).1 inferInstance).eq_iff.symm
end GlobalTheory
