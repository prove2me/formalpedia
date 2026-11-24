-- Prove2me | solution 1 for GlobalTheory.BruhatRep.weyl_unipotent_weyl_extendUnitsMapByOneAtZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:06:54.475812+00:00
-- url     : https://prove2.me/submissions/2222bab1-9cca-42b3-923e-023e5cfbec4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_mx_ne

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
    {u : K} (hu : u ≠ 0) : t * n u * t = n (-u⁻¹) * mx m (-u⁻¹) * t * n (-u⁻¹) := by
  have := htnt (Units.mk0 u hu)
  rw [mx_ne m (neg_ne_zero.2 (inv_ne_zero hu))]
  rw [Units.val_mk0] at this
  rw [this, show Units.mk0 (-u⁻¹) (neg_ne_zero.2 (inv_ne_zero hu)) = -(Units.mk0 u hu)⁻¹ from by ext; simp]
  simp
end GlobalTheory.BruhatRep
