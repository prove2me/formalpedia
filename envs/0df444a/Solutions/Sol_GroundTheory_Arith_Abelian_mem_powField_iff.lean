-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.mem_powField_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:19.149453+00:00
-- url     : https://prove2.me/submissions/64e964a9-8341-435a-9f50-7498c6a14ce4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_mem_frobImage
import Theorems.Thm_GroundTheory_Arith_Abelian_adjoin_genX_genY
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (z : E.toAffine.FunctionField) :
    z ∈ powField E p ↔ ∃ g, g ^ p = z := by
  constructor
  · intro hz
    have hle : powField E p ≤ frobImage E p ⊤ := by
      rw [powField, adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact (mem_frobImage E p).mpr ⟨genX E, trivial, rfl⟩
      · exact (mem_frobImage E p).mpr ⟨genY E, trivial, rfl⟩
    obtain ⟨g, -, hg⟩ := (mem_frobImage E p).mp (hle hz)
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    let Q : IntermediateField F E.toAffine.FunctionField :=
      ((powField E p).toSubfield.comap (frobenius E.toAffine.FunctionField p)).toIntermediateField
        fun c => by
          show (algebraMap F _ c) ^ p ∈ powField E p
          rw [← map_pow]; exact IntermediateField.algebraMap_mem _ _
    have htop : (⊤ : IntermediateField F E.toAffine.FunctionField) ≤ Q := by
      rw [← adjoin_genX_genY E, adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact (subset_adjoin F _ (by simp) : genX E ^ p ∈ powField E p)
      · exact (subset_adjoin F _ (by simp) : genY E ^ p ∈ powField E p)
    exact htop trivial
end GroundTheory.Arith.Abelian
