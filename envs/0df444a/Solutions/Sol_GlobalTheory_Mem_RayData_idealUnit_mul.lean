-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.idealUnit_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:07.222817+00:00
-- url     : https://prove2.me/submissions/8435014e-9d7e-4496-9568-4f286f6cf4b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIntegralOfMemRayI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.RayData
section aux
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma coe_idealUnit_eq (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ((_root_.GlobalTheory.Mem.RayData.idealUnit I hI : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I := rfl
variable {M : ℕ} (D : RayData K M)
end aux
end GlobalTheory.Mem.RayData
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.RayData
namespace _root_.GlobalTheory.Mem.RayData
theorem _root_.solution (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : I * J ≠ ⊥) :
    _root_.GlobalTheory.Mem.RayData.idealUnit (I * J) h = _root_.GlobalTheory.Mem.RayData.idealUnit I hI * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ := by
  ext
  simp [coe_idealUnit_eq, FractionalIdeal.coeIdeal_mul]
end _root_.GlobalTheory.Mem.RayData
end GlobalTheory.Mem.RayData
