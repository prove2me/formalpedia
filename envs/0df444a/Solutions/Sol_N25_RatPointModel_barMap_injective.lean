-- Prove2me | solution 1 for N25.RatPointModel.barMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:26.776071+00:00
-- url     : https://prove2.me/submissions/eef67e5e-1345-4011-980e-8f96d8273075

import Mathlib
import Definitions.Def_N25_RatPointModel

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory AlgebraicGeometry GoodReductionJacobian

namespace N25

local instance instL_N25_RatPointModel_barMap_injective_bfd51b_s2a8473 : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance instL_N25_RatPointModel_barMap_injective_3dbe1c_s2a8473 : IsScalarTower ℚ ℚ_[5] (PadicAlgCl 5) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/-- Scalar extension of points along a field embedding is injective. -/
theorem _root_.solution (D : RatPointModel) :
    Function.Injective D.barMap := by
  let a := padicEmbedding 5
  let s := Spec.map (CommRingCat.ofHom a.toRingHom)
  letI : Epi s := Flat.epi_of_flat_of_surjective s
  intro x y h
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  apply Subtype.ext
  apply (cancel_epi s).mp
  exact congrArg (fun z => (RelativeGroupLaw.AlgPoints.toPoint z).1) h

end N25
