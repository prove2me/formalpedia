-- Prove2me | solution 1 for GlobalTheory.UnimodOver.discrete_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:50.039724+00:00
-- url     : https://prove2.me/submissions/dabdde7f-8677-4d5e-ad9c-35b2812928b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Theorems.Thm_GlobalTheory_UnimodOver_exists_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.UnimodOver
theorem _root_.solution (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    DiscreteTopology (B.dualSubmodule Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
  infer_instance
end GlobalTheory.UnimodOver
