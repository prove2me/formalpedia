-- Prove2me | solution 1 for GlobalTheory.lTensor_liftQ_injective_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:27.817804+00:00
-- url     : https://prove2.me/submissions/4f2cd683-a58c-47c2-b343-bf099b3a560a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
namespace GlobalTheory
theorem _root_.solution (N : Type*) [AddCommGroup N] [Module R N]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : LinearMap.range f ≤ LinearMap.ker g)
    (h : Exact (f.lTensor N) (g.lTensor N)) :
    Injective (((LinearMap.range f).liftQ g hfg).lTensor N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective N (Submodule.mkQ_surjective _) x
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ] at hx
  obtain ⟨z, rfl⟩ := (h y).1 hx
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    f.exact_map_mkQ_range.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]
end GlobalTheory
