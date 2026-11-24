-- Prove2me | solution 1 for GlobalTheory.MapComapIso.map_eq_comap_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:13:32.982169+00:00
-- url     : https://prove2.me/submissions/a770a39f-0008-4e7a-88de-4088745ed861

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapFlatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapIdealSheafEqOfIsIsoRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory GlobalTheory.MapComapIso
namespace GlobalTheory.MapComapIso
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (K : X.IdealSheafData) :
    K.map f = K.comap (inv f) := by
  apply le_antisymm
  · calc K.map f = (K.map f).comap (inv f ≫ f) := by simp
      _ = ((K.map f).comap f).comap (inv f) := by rw [Scheme.IdealSheafData.comap_comp]
      _ ≤ K.comap (inv f) :=
          Scheme.IdealSheafData.comap_mono (inv f) ((Scheme.IdealSheafData.map_gc f).l_u_le K)
  · calc K.comap (inv f) ≤ ((K.comap (inv f)).comap f).map f :=
          (Scheme.IdealSheafData.map_gc f).le_u_l _
      _ = (K.comap (f ≫ inv f)).map f := by rw [Scheme.IdealSheafData.comap_comp]
      _ = K.map f := by simp
end GlobalTheory.MapComapIso
