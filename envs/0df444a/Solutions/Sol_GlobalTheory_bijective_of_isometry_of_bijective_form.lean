-- Prove2me | solution 1 for GlobalTheory.bijective_of_isometry_of_bijective_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:21.660507+00:00
-- url     : https://prove2.me/submissions/4829afb3-dd3f-4327-8367-ce3c227afcfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R L L' : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup L] [Module R L] [Module.Free R L] [Module.Finite R L]
    [AddCommGroup L'] [Module R L'] [Module.Free R L'] [Module.Finite R L']
    (hrk : Module.finrank R L = Module.finrank R L')
    (E : LinearMap.BilinForm R L) (E' : LinearMap.BilinForm R L') (hE : Function.Bijective E)
    (g : L →ₗ[R] L') (hg : ∀ a b, E' (g a) (g b) = E a b) : Function.Bijective g := by
  let e : L ≃ₗ[R] Module.Dual R L := LinearEquiv.ofBijective E hE
  let r : L' →ₗ[R] L := e.symm.toLinearMap ∘ₗ g.dualMap ∘ₗ E'
  have hr : Function.LeftInverse r g := fun a => by
    change e.symm (g.dualMap (E' (g a))) = a
    rw [LinearEquiv.symm_apply_eq]
    ext b
    exact hg a b
  have hi : Function.Injective r :=
    OrzechProperty.injective_of_surjective_of_injective
      (LinearEquiv.ofFinrankEq L' L hrk.symm).toLinearMap r (LinearEquiv.injective _) hr.surjective
  exact ⟨hr.injective, fun y => ⟨r y, hi (hr _)⟩⟩
end GlobalTheory
