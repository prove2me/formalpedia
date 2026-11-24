-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.idealUnit_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:12.668982+00:00
-- url     : https://prove2.me/submissions/23c54af7-51b0-48b8-b9f9-293587b45270

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
theorem _root_.solution {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    _root_.GlobalTheory.Mem.RayData.idealUnit I hI = _root_.GlobalTheory.Mem.RayData.idealUnit J hJ ↔ I = J := by
  rw [Units.ext_iff, coe_idealUnit_eq, coe_idealUnit_eq, FractionalIdeal.coeIdeal_inj]
end _root_.GlobalTheory.Mem.RayData
end GlobalTheory.Mem.RayData
