-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.differentiableOn_modularJC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:15.57357+00:00
-- url     : https://prove2.me/submissions/2ee0b26a-fe19-4197-a791-7202361718c2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantSurjective
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____29e4a99442e2
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_one
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_two
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_zero
attribute [local simp] P2M_GroundTheory_Global_Elliptic_latticeOfTau____29e4a99442e2
attribute [local simp] P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620



set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution : DifferentiableOn ℂ modularJC {z : ℂ | 0 < z.im} := by
  have h4 : DifferentiableOn ℂ ((fun τ : ℍ ↦ E₄ τ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo E₄)
  have hΔ : DifferentiableOn ℂ ((fun τ : ℍ ↦ ModularForm.discriminant τ) ∘ ofComplex)
      {z : ℂ | 0 < z.im} := by
    have := UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo CuspForm.discriminant)
    simpa [CuspForm.coe_discriminant] using this
  refine (h4.pow 3).div hΔ fun z _ ↦ ModularForm.discriminant_ne_zero _
end GroundTheory.Global.Elliptic
