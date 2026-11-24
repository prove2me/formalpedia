-- Prove2me | solution 1 for GlobalTheory.BruhatRep.t_n_th
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:38.088177+00:00
-- url     : https://prove2.me/submissions/47b31ebe-7c8a-423a-a361-3948f9cdab67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_weyl_unipotent_weyl_extendUnitsMapByOneAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
variable (n : K → M) (m : Kˣ → M) (t : M)
namespace GlobalTheory.BruhatRep
theorem _root_.solution (htnt : ∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K)))
    {u : K} (hu : u ≠ 0) (X : M) : X * t * n u * t = X * n (-u⁻¹) * mx m (-u⁻¹) * t * n (-u⁻¹) := by
  simpa only [mul_assoc] using congrArg (X * ·) (weyl_unipotent_weyl_extendUnitsMapByOneAtZero n m t htnt hu)
end GlobalTheory.BruhatRep
