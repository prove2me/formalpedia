-- Prove2me | solution 1 for GlobalTheory.FixedPoint.exists_ringHom_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:27:08.752695+00:00
-- url     : https://prove2.me/submissions/d8dead4f-2000-4610-ad78-1d0a892152b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
import Theorems.Thm_GlobalTheory_FixedPoint_mem_range_of_algebraMap_fixed
import Theorems.Thm_GlobalTheory_FixedPoint_exists_ringHom_of_forall_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
variable {K₀ : Type u} {K₁ : Type v} {L : Type w} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]
namespace GlobalTheory.FixedPoint
theorem _root_.solution [PerfectField K₀] [IsAlgClosed L] {A : Type*} [CommRing A]
    (φ : A →+* K₁)
    (h : ∀ (s : L ≃ₐ[K₀] L) (a : A), s (algebraMap K₁ L (φ a)) = algebraMap K₁ L (φ a)) :
    ∃ ψ : A →+* K₀, (algebraMap K₀ K₁).comp ψ = φ :=
  exists_ringHom_of_forall_mem_range φ fun a => mem_range_of_algebraMap_fixed _ fun s => h s a
end GlobalTheory.FixedPoint
