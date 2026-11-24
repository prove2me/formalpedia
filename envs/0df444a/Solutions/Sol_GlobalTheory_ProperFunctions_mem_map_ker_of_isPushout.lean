-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.mem_map_ker_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:50.56499+00:00
-- url     : https://prove2.me/submissions/7a1b77f0-d5bd-4cf5-aadf-efc1475b912e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_of_tmul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {R A K P : CommRingCat.{u}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : φ.hom.Flat) (x : A)
    (hx : inl x = 0) : x ∈ (RingHom.ker ψ.hom).map φ.hom := by
  algebraize [φ.hom, ψ.hom]
  let e := (CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H
  refine mem_map_of_tmul_eq_zero x (1 : K) _ (fun r hr ↦ ?_) ?_
  · rwa [← Algebra.algebraMap_eq_smul_one] at hr
  · have := congr($((CommRingCat.isPushout_tensorProduct R A K).inl_isoIsPushout_inv _ _ H).hom x)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [show inl.hom x = 0 from hx, map_zero] at this
    exact this.symm
end GlobalTheory.ProperFunctions
