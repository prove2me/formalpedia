-- Prove2me | solution 1 for GlobalTheory.FormalInv.subst_mem_coeffsInDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:15.733018+00:00
-- url     : https://prove2.me/submissions/c2a89bdf-ee3d-40af-b1e6-7afc85633c16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_subst_mem_coeffsIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
namespace GlobalTheory.FormalInv
theorem _root_.solution [Finite σ] {S : Subring R} {g : ℕ} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (haS : ∀ s, a s ∈ coeffsInDeg τ S g)
    {f : MvPowerSeries σ R} (hf : f ∈ coeffsInDeg σ S g) : f.subst a ∈ coeffsInDeg τ S g :=
  subst_mem_coeffsIn (hasSubst_of_constantCoeff_zero ha)
    (fun _ s => mem_degGe_one.2 (ha s)) haS hf
end GlobalTheory.FormalInv
