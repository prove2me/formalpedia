-- Prove2me | solution 1 for MazurTransfer.CurveModelPointDifferenceInjectivity.point_map_injective_of_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T01:46:48.992934+00:00
-- url     : https://prove2.me/submissions/d3393576-adfd-4724-86a4-5f04930c85f6

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: any actual point-difference Picard dictionary on a
positive-genus curve makes its point map injective, with an arbitrary
base point. Named downstream consumer: injectivity of the integral
order13 Abel-Jacobi map on geometric and rational points. -/
import Mathlib
import Definitions.Def_MazurTransfer_CurveModelPointDifference
import Definitions.Def_MazurTransfer_RationalPlacePicardPointClass
import Theorems.Thm_MazurTransfer_RationalPlacePicardInjection_pointClass_injective
open CategoryTheory AlgebraicGeometry AlgebraicCurve MazurTransfer
open MazurTransfer.CurveModelPointDifferenceInjectivity
universe u v z

theorem solution {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (M : CurveModel K F) (hC : ConstantsAreBase K F)
    (hgen : 0 < genusFF K F) {S : Type z} (pts : Pic0 K F ≃ S)
    (j : ModelPoint M → S) (s : ModelPoint M)
    (h : ∀ p, ∃ E : Divisor.degZero (K := K) (F := F),
      (E : Divisor K F) = Finsupp.single (M.pointEquivPlace p) 1 -
        Finsupp.single (M.pointEquivPlace s) 1 ∧ pts (Pic0.mk E) = j p) :
    Function.Injective j := by
  have hread (p : ModelPoint M) :
      pts (RationalPlacePicardInjection.pointClass (rationalPointPlace M s) (rationalPointPlace M p)) = j p := by
    obtain ⟨E,hE,hp⟩ := h p
    have he : E = ⟨Finsupp.single (M.pointEquivPlace p) 1 - Finsupp.single (M.pointEquivPlace s) 1,
        by
          have hp : (M.pointEquivPlace p).deg = 1 := (rationalPointPlace M p).property
          have hs : (M.pointEquivPlace s).deg = 1 := (rationalPointPlace M s).property
          rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hp, hs]
          norm_num⟩ :=
      Subtype.ext hE
    exact (congrArg (fun D => pts (Pic0.mk D)) he).symm.trans hp
  intro p q hpq
  have hc := pts.injective ((hread p).trans (hpq.trans (hread q).symm))
  have hv := RationalPlacePicardInjection.pointClass_injective hC hgen (rationalPointPlace M s) hc
  exact M.pointEquivPlace.injective (congrArg Subtype.val hv)
#print axioms solution
