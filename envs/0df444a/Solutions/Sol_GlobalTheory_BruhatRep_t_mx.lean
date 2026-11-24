-- Prove2me | solution 1 for GlobalTheory.BruhatRep.t_mx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:04:01.159018+00:00
-- url     : https://prove2.me/submissions/5e556bfe-b818-4719-8d27-ba513ef03043

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
theorem _root_.solution (htm : ∀ s, t * m s = m s⁻¹ * t) {x : K} (hx : x ≠ 0) : t * mx m x = mx m x⁻¹ * t := by
  rw [mx_ne m hx, mx_ne m (inv_ne_zero hx), htm]; congr 2; ext; simp
end GlobalTheory.BruhatRep
