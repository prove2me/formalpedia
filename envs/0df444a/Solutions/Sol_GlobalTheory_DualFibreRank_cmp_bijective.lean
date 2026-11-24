-- Prove2me | solution 1 for GlobalTheory.DualFibreRank.cmp_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:50.539796+00:00
-- url     : https://prove2.me/submissions/ce95b08b-987f-4369-995e-0e920ac2064a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Theorems.Thm_GlobalTheory_DualFibreRank_cmp_natural_apply
import Theorems.Thm_GlobalTheory_DualFibreRank_cmp_bijective_of_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.DualFibreRank
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]
variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
namespace GlobalTheory.DualFibreRank
theorem _root_.solution [Module.Projective O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
  have hF := cmp_bijective_of_free A (O := O) (M := Fin n → O)
  have h1 : ∀ x, i.dualMap.baseChange A (p.dualMap.baseChange A x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hpi]
    simp [LinearMap.dualMap_id]
  have h2 : ∀ y, (i.baseChange A).dualMap ((p.baseChange A).dualMap y) = y := by
    intro y
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi]
    simp [LinearMap.dualMap_id]
  constructor
  · intro x y hxy
    rw [← h1 x, ← h1 y]
    congr 1
    apply hF.1
    rw [cmp_natural_apply, cmp_natural_apply, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hF.2 ((p.baseChange A).dualMap y)
    exact ⟨i.dualMap.baseChange A z, by rw [cmp_natural_apply, hz, h2]⟩
end GlobalTheory.DualFibreRank
