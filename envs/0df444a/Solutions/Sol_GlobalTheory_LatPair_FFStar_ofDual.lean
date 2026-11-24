-- Prove2me | solution 1 for GlobalTheory.LatPair.FFStar_ofDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:43.586511+00:00
-- url     : https://prove2.me/submissions/edb9fa30-1bf5-40d4-b80d-98bcb5a20d28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_FFStar_apply
import Theorems.Thm_GlobalTheory_LatPair_cross_up_ofDual
import Theorems.Thm_GlobalTheory_LatPair_sum_withKer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
variable (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
namespace GlobalTheory.LatPair
theorem _root_.solution [Fintype {x : Red L // x ≠ 0}] (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) :
    FFStar q χ φ (ofDual L f) = ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) • φ (up L q x) := by
  simp only [FFStar_apply, ofDual_lat, sum_withKer L q, cross_up_ofDual]
end GlobalTheory.LatPair
