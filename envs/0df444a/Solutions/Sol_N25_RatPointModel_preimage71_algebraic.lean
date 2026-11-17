-- Prove2me | solution 1 for N25.RatPointModel.preimage71_algebraic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:53.422553+00:00
-- url     : https://prove2.me/submissions/d9cedbb4-b468-40a6-b3bc-2f45f771b93d

import Mathlib
import Definitions.Def_N25_RatPointModel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

namespace N25

local instance instL_N25_RatPointModel_preimage71_algebraic_bfd51b_s2e44fc : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A division point above a globally algebraic point descends through the finite
multiplication fibre over the algebraically closed global field. -/
theorem _root_.solution
    (D : RatPointModel) (y : D.Omega)
    (hy : (71 : ℕ) • y ∈ D.barMap.range) :
    y ∈ D.barMap.range := by
  obtain ⟨P, hP⟩ := hy
  let j := Spec.map (CommRingCat.ofHom (padicEmbedding 5).toRingHom)
  let yp := (RelativeGroupLaw.AlgPoints.toPoint y).1
  let Pp := (RelativeGroupLaw.AlgPoints.toPoint P).1
  let m := D.G.schemeNsmul 71
  haveI : IsFinite m := (D.G.isFinite_and_flat_schemeNsmul D.abelian D.comm 71 (by decide)).1
  have hmul : yp ≫ m = j ≫ Pp := by
    have hh := congrArg (fun z : D.Omega => (RelativeGroupLaw.AlgPoints.toPoint z).1) hP
    rw [RelativeGroupLaw.AlgPoints.toPoint_nsmul,
      D.G.coe_nsmul_eq_comp_schemeNsmul] at hh
    exact hh.symm
  let t : Spec (CommRingCat.of (PadicAlgCl 5)) ⟶ pullback m Pp :=
    pullback.lift yp j hmul
  obtain ⟨z, hz, _⟩ := existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
    (padicEmbedding 5).toRingHom (pullback.snd m Pp) t (pullback.lift_snd _ _ _)
  let xp := z ≫ pullback.fst m Pp
  have hxp : j ≫ xp = yp := by
    dsimp [xp]
    rw [← Category.assoc, hz.2]
    exact pullback.lift_fst _ _ _
  haveI : Epi j := Flat.epi_of_flat_of_surjective j
  have hover : xp ≫ D.f = Spec.map (CommRingCat.ofHom
      (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    apply (cancel_epi j).mp
    rw [← Category.assoc, hxp]
    exact (RelativeGroupLaw.AlgPoints.toPoint y).2.trans
      (RelativeGroupLaw.AlgPoints.specMap_comp_algebraMap (padicEmbedding 5)).symm
  refine ⟨RelativeGroupLaw.AlgPoints.ofPoint ⟨xp, hover⟩, ?_⟩
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  apply Subtype.ext
  exact hxp

end N25
