-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.degree_mulIsogeny
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:38.449041+00:00
-- url     : https://prove2.me/submissions/99ff2fcb-b2a6-4960-aebf-40fd7976bfa6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Theorems.Thm_GroundTheory_Arith_Abelian_Isogeny_comap_genX
import Theorems.Thm_GroundTheory_Arith_Abelian_map_top_eq_fieldRange
import Theorems.Thm_GroundTheory_Arith_Abelian_fieldRange_ratEmb
import Theorems.Thm_GroundTheory_Arith_Abelian_mulIsogeny_alt
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian_finrank_adjoin_rat___60f1bb1f96c8
import Theorems.Thm_GroundTheory_Arith_Abelian_finrank_adjoin_genX


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
universe u
variable {F : Type u} [Field F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℤ} (hn : n ≠ 0) : (mulIsogeny E n hn).degree = n.natAbs ^ 2 := by
  set φ := mulIsogeny E n hn
  set α := φ.comap
  set E1 : IntermediateField F E.toAffine.FunctionField := F⟮genX E⟯
  set M := α.fieldRange
  set E0 : IntermediateField F E.toAffine.FunctionField := F⟮φ.x⟯
  have hx : φ.x = ratEmb E (ratΦΨ E n) := by rw [ratEmb_ratΦΨ]; exact mulIsogeny_alt E hn
  have hxE1 : φ.x ∈ E1 := by
    have hE1 : E1 = (ratEmb E).fieldRange := (fieldRange_ratEmb E).symm
    rw [hx, hE1]; exact ⟨_, rfl⟩
  have hxM : φ.x ∈ M := ⟨genX E, φ.comap_genX⟩
  have h01 : E0 ≤ E1 := adjoin_simple_le_iff.mpr hxE1
  have h0M : E0 ≤ M := adjoin_simple_le_iff.mpr hxM

  have e1 : relfinrank E1 ⊤ = 2 := by rw [relfinrank_top_right, finrank_adjoin_genX]

  have e2 : relfinrank E0 M = 2 := by
    have hE0 : E0 = E1.map α := by
      rw [adjoin_map, Set.image_singleton, φ.comap_genX]
    have hM : M = (⊤ : IntermediateField F _).map α := (map_top_eq_fieldRange α).symm
    rw [hE0, hM, relfinrank_map_map, e1]

  have e3 : relfinrank E0 E1 = n.natAbs ^ 2 := by
    have hE0 : E0 = (F⟮ratΦΨ E n⟯).map (ratEmb E) := by
      rw [adjoin_map, Set.image_singleton, ← hx]
    have hE1 : E1 = (⊤ : IntermediateField F (RatFunc F)).map (ratEmb E) := by
      rw [map_top_eq_fieldRange, fieldRange_ratEmb]
    rw [hE0, hE1, relfinrank_map_map, relfinrank_top_right, finrank_adjoin_ratΦΨ E hn]
  have t1 := relfinrank_mul_relfinrank h01 (le_top : E1 ≤ ⊤)
  have t2 := relfinrank_mul_relfinrank h0M (le_top : M ≤ ⊤)
  rw [e1, e3] at t1
  rw [e2, ← t1] at t2
  have hdeg : φ.degree = relfinrank M ⊤ := by rw [Isogeny.degree, relfinrank_top_right]
  rw [hdeg]
  omega
end GroundTheory.Arith.Abelian
