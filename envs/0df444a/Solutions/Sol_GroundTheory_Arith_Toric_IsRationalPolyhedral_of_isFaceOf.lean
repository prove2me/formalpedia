-- Prove2me | solution 1 for GroundTheory.Arith.Toric.IsRationalPolyhedral.of_isFaceOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:23.331803+00:00
-- url     : https://prove2.me/submissions/a95c2f54-1833-451a-8ff7-97f3d28bd3f4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
namespace GroundTheory.Arith.Toric
namespace IsRationalPolyhedral
theorem _root_.solution {L E : Type*} [AddCommGroup L] [AddCommGroup E]
    [Module ℝ E] {ι : L →ₗ[ℤ] E} {σ τ : PointedCone ℝ E} (hσ : IsRationalPolyhedral ι σ)
    (hτ : τ.IsFaceOf σ) : IsRationalPolyhedral ι τ := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  have hτ' : τ.IsFaceOf (hull ℝ ((S.image ι : Finset E) : Set E)) := by
    rwa [Finset.coe_image]
  refine ⟨S.filter (fun n => ι n ∈ τ), ?_⟩
  conv_rhs => rw [isFaceOf_eq_hull_filter _ hτ']
  congr 1
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨hnS, hnτ⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hn)
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hnS, hnτ⟩)
  · intro hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hy1
    exact ⟨n, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hn, hy2⟩), rfl⟩
end IsRationalPolyhedral
end GroundTheory.Arith.Toric
