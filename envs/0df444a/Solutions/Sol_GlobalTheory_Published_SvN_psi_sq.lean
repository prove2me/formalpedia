-- Prove2me | solution 1 for GlobalTheory.Published.SvN.psi_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:40:03.167802+00:00
-- url     : https://prove2.me/submissions/182d2f5c-3d6a-4168-a4e8-443d485ef554

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {W : Type} [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.Published.SvN
theorem _root_.solution (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (t : F) : ψ (t / 2) ^ 2 = ψ t := by
  rw [pow_two, ← AddChar.map_add_eq_mul]; congr 1; field_simp; ring
end GlobalTheory.Published.SvN
