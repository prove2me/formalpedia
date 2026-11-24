-- Prove2me | solution 1 for GlobalTheory.UnitarySemisimple.orth_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:09.951179+00:00
-- url     : https://prove2.me/submissions/666b671d-09cc-47f3-abd4-74b68489ae96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Theorems.Thm_GlobalTheory_UnitarySemisimple_rho_rho_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.UnitarySemisimple
theorem _root_.solution (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v) (Z : Subrepresentation ρ) (s : W)
    (hs : ∀ z ∈ Z.toSubmodule, B z s = 0) (g : H) : ∀ z ∈ Z.toSubmodule, B z (ρ g s) = 0 := by
  intro z hz
  calc B z (ρ g s) = B (ρ g (ρ g⁻¹ z)) (ρ g s) := by rw [rho_rho_inv]
    _ = B (ρ g⁻¹ z) s := hinv _ _ _
    _ = 0 := hs _ (Z.apply_mem_toSubmodule _ hz)
end GlobalTheory.UnitarySemisimple
