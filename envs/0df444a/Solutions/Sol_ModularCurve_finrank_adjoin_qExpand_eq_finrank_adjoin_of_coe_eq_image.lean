-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/35499daa-d2b6-559a-b9d5-69e79560ae32

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image

set_option autoImplicit false

open ModularCurve Polynomial

universe u

namespace KummerTransport

theorem finrank_adjoin_eq_zero_of_not_isIntegral {κ : Type u} [Field κ] (E : IntermediateField κ (LaurentSeries κ))
    (z : LaurentSeries κ) (hz : ¬ IsIntegral (↥E) z) :
    Module.finrank ↥E ↥(IntermediateField.adjoin ↥E ({z} : Set (LaurentSeries κ))) = 0 := by
  apply Module.finrank_of_infinite_dimensional
  intro hfin
  apply hz
  haveI : Module.Finite ↥E ↥(IntermediateField.adjoin ↥E ({z} : Set (LaurentSeries κ))) := hfin
  have h1 : IsIntegral (↥E) (IntermediateField.AdjoinSimple.gen (↥E) z) := IsIntegral.of_finite (↥E) _
  rwa [IntermediateField.AdjoinSimple.isIntegral_gen] at h1

end KummerTransport

theorem solution
    (κ : Type u) [Field κ] (n : ℕ) [NeZero n]
    (F F' : IntermediateField κ (LaurentSeries κ))
    (hF' : (F' : Set (LaurentSeries κ)) = ModularCurve.qExpand κ n '' (F : Set (LaurentSeries κ)))
    (x : LaurentSeries κ) :
    Module.finrank ↥F' ↥(IntermediateField.adjoin ↥F' ({ModularCurve.qExpand κ n x} : Set (LaurentSeries κ))) =
      Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) := by
  classical
  set φ : LaurentSeries κ →ₐ[κ] LaurentSeries κ := qExpandAlgHomC κ n with hφdef
  have hφ : ∀ f : LaurentSeries κ, φ f = qExpand κ n f := fun f => rfl
  have hφinj : Function.Injective φ := (qExpand κ n).injective
  have hFF' : F' = F.map φ := SetLike.coe_injective (by rw [hF', IntermediateField.coe_map]; rfl)
  subst hFF'
  change Module.finrank ↥(F.map φ) ↥(IntermediateField.adjoin ↥(F.map φ) ({φ x} : Set (LaurentSeries κ))) =
    Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ)))

  set e : ↥F ≃ₐ[κ] ↥(F.map φ) := IntermediateField.equivMap F φ with hedef
  have he : ∀ a : ↥F, ((e a : ↥(F.map φ)) : LaurentSeries κ) = φ a := fun a => IntermediateField.coe_equivMap_apply F φ a
  set ee : ↥F →+* ↥(F.map φ) := e.toRingEquiv.toRingHom with hee
  set es : ↥(F.map φ) →+* ↥F := e.symm.toRingEquiv.toRingHom with hes
  have hee_app : ∀ a, ee a = e a := fun a => rfl
  have hes_app : ∀ b, es b = e.symm b := fun b => rfl
  have heeinj : Function.Injective ee := e.toRingEquiv.injective
  have hcomp : (algebraMap ↥(F.map φ) (LaurentSeries κ)).comp ee =
      (φ : LaurentSeries κ →+* LaurentSeries κ).comp (algebraMap ↥F (LaurentSeries κ)) :=
    RingHom.ext fun a => by rw [RingHom.comp_apply, RingHom.comp_apply, hee_app]; exact he a
  have hcomp' : ((φ : LaurentSeries κ →+* LaurentSeries κ).comp (algebraMap ↥F (LaurentSeries κ))).comp
      es = algebraMap ↥(F.map φ) (LaurentSeries κ) := by
    rw [← hcomp, RingHom.comp_assoc]
    refine RingHom.ext fun b => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, hee_app, hes_app, AlgEquiv.apply_symm_apply]

  have heval : ∀ p : Polynomial ↥F, eval₂ (algebraMap ↥(F.map φ) (LaurentSeries κ)) (φ x) (p.map ee) =
      φ (aeval x p) := by
    intro p
    rw [eval₂_map, hcomp, aeval_def]
    exact (hom_eval₂ p (algebraMap ↥F (LaurentSeries κ)) (φ : LaurentSeries κ →+* LaurentSeries κ) x).symm
  have heval' : ∀ p : Polynomial ↥(F.map φ), φ (aeval x (p.map es)) =
      eval₂ (algebraMap ↥(F.map φ) (LaurentSeries κ)) (φ x) p := by
    intro p
    rw [aeval_def]
    show (φ : LaurentSeries κ →+* LaurentSeries κ) (eval₂ _ x _) = _
    rw [hom_eval₂, eval₂_map, hcomp']
    rfl
  by_cases hint : IsIntegral (↥F) x
  ·
    have hint' : IsIntegral (↥(F.map φ)) (φ x) :=
      ⟨(minpoly (↥F) x).map ee, (minpoly.monic hint).map _, by rw [heval, minpoly.aeval, map_zero]⟩
    have hmin : (minpoly (↥F) x).map ee = minpoly (↥(F.map φ)) (φ x) := by
      apply minpoly.eq_of_irreducible_of_monic
      · have h := (MulEquiv.irreducible_iff (Polynomial.mapEquiv e.toRingEquiv)).mpr (minpoly.irreducible hint)
        exact h
      · rw [aeval_def, heval, minpoly.aeval, map_zero]
      · exact (minpoly.monic hint).map _
    rw [IntermediateField.adjoin.finrank hint, IntermediateField.adjoin.finrank hint', ← hmin,
      natDegree_map_eq_of_injective heeinj]
  ·
    have hint' : ¬ IsIntegral (↥(F.map φ)) (φ x) := by
      rintro ⟨p, hp, hp0⟩
      apply hint
      refine ⟨p.map es, hp.map es, ?_⟩
      apply hφinj
      rw [map_zero, ← aeval_def, heval', hp0]
    rw [KummerTransport.finrank_adjoin_eq_zero_of_not_isIntegral F x hint,
      KummerTransport.finrank_adjoin_eq_zero_of_not_isIntegral (F.map φ) (φ x) hint']

end S_ModularCurve_finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image (solution)
