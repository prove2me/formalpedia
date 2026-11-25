-- Prove2me | solution 1 for GlobalTheory.QCoh.topologicalKrullDim_le_of_irreducibleCloseds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:27:17.68525+00:00
-- url     : https://prove2.me/submissions/cb24cf84-1fed-4335-b63d-79cedb2b7c7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_isIrreducible_of_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {T : Type*} [TopologicalSpace T]
    {d : WithBot ℕ∞} (h : ∀ Z : IrreducibleCloseds T, topologicalKrullDim (Z : Set T) ≤ d) :
    topologicalKrullDim T ≤ d := by
  refine iSup_le fun p ↦ le_trans ?_ (h p.last)
  let L : Set T := (p.last : IrreducibleCloseds T)
  have hle (i : Fin (p.length + 1)) : ((p i : IrreducibleCloseds T) : Set T) ⊆ L := p.monotone (Fin.le_last i)
  have him (i : Fin (p.length + 1)) :
      Subtype.val '' ((Subtype.val : L → T) ⁻¹' (p i : IrreducibleCloseds T)) = (p i : IrreducibleCloseds T) := by
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 (hle i)]
  let q : LTSeries (IrreducibleCloseds L) := LTSeries.mk p.length
    (fun i ↦ ⟨Subtype.val ⁻¹' ((p i : IrreducibleCloseds T) : Set T),
      isIrreducible_of_image .subtypeVal
      ((him i).symm ▸ (p i).isIrreducible), (p i).isClosed.preimage continuous_subtype_val⟩)
    fun i j hij ↦ by
      refine lt_of_le_of_ne (fun z hz ↦ p.monotone hij.le hz) fun e ↦
        (p.strictMono hij).ne (IrreducibleCloseds.ext ?_)
      rw [← him i, ← him j]
      exact congrArg (fun Z : IrreducibleCloseds L ↦
        Subtype.val '' (Z : Set L)) e
  exact Order.LTSeries.length_le_krullDim q
end GlobalTheory.QCoh
