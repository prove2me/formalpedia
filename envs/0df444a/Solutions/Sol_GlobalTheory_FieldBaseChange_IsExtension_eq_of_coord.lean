-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.IsExtension.eq_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:57.255824+00:00
-- url     : https://prove2.me/submissions/6c742b16-2de1-47c0-80c8-23c4592378bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_expansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
namespace GlobalTheory.FieldBaseChange
namespace IsExtension
theorem _root_.solution {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) {x y : W}
    (e : ∀ ℓ Λ, IsCoord a ℓ Λ → Λ x = Λ y) : x = y := by
  classical
  let β := Module.Free.chooseBasis K F
  choose Λ hΛ using fun i => h.coord (β.coord i)
  obtain ⟨S₁, -, h₁⟩ := exists_expansion β h.span hΛ x
  obtain ⟨S₂, -, h₂⟩ := exists_expansion β h.span hΛ y
  rw [h₁ (S₁ ∪ S₂) Finset.subset_union_left, h₂ (S₁ ∪ S₂) Finset.subset_union_right]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [e _ _ (hΛ i)]
end IsExtension
end GlobalTheory.FieldBaseChange
