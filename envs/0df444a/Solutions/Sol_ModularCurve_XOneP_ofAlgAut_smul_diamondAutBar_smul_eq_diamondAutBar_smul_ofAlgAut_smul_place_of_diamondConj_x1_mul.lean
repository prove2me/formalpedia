-- Prove2me | solution 1 for ModularCurve.XOneP.ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2a28c761-e146-55b7-ae56-53cd7315d312

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul

set_option autoImplicit false

open AlgebraicCurve

set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    [Algebra L (AlgebraicClosure ℚ)]

    (σ : ↥K ≃ₐ[L] ↥K)
    (σbar : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hσbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((σbar f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L))

    (d d' : ℕ) (hd : d.Coprime (M * p)) (hd' : d'.Coprime (M * p))
    (hdM : (d' : ZMod M) = (d : ZMod M)) (hdp : (d' : ZMod p) * (d : ZMod p) = 1)

    (θd θd' : ↥K ≃ₐ[L] ↥K)
    (hθd : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θd x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))
    (hθd' : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θd' x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))

    (hθdbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((ModularCurve.diamondAutBar (M * p) d f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((θd b : ↥K) : LaurentSeries L))
    (hθd'bar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((ModularCurve.diamondAutBar (M * p) d' f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((θd' b : ↥K) : LaurentSeries L))

    (hconj : ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L)) :
    ∀ P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)),
      AlgebraicCurve.SemilinearAut.ofAlgAut σbar • (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d) • P) =
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d') • (AlgebraicCurve.SemilinearAut.ofAlgAut σbar • P) := by
  classical
  intro P
  let Qb := AlgebraicClosure ℚ
  let E := ↥(ModularCurve.x1FunctionFieldBar (M * p))
  let ι : LaurentSeries L →+* LaurentSeries Qb := ModularCurve.coeffMap (algebraMap L Qb)
  set Dd := ModularCurve.diamondAutBar (M * p) d with hDd
  set Dd' := ModularCurve.diamondAutBar (M * p) d' with hDd'

  have hagree : ∀ (f : E) (b : ↥K), (f : LaurentSeries Qb) = ι ((b : ↥K) : LaurentSeries L) →
      σbar (Dd f) = Dd' (σbar f) := by
    intro f b hf
    apply Subtype.ext
    have h1 : ((Dd f : E) : LaurentSeries Qb) = ι ((θd b : ↥K) : LaurentSeries L) := hθdbar f b hf
    have h2 : ((σbar (Dd f) : E) : LaurentSeries Qb) = ι ((σ (θd b) : ↥K) : LaurentSeries L) := hσbar _ _ h1
    have h3 : ((σbar f : E) : LaurentSeries Qb) = ι ((σ b : ↥K) : LaurentSeries L) := hσbar f b hf
    have h4 : ((Dd' (σbar f) : E) : LaurentSeries Qb) = ι ((θd' (σ b) : ↥K) : LaurentSeries L) := hθd'bar _ _ h3
    rw [h2, h4, ← hconj (σ b), AlgEquiv.symm_apply_apply]

  have hιemb : ∀ y : LaurentSeries ℚ, ι (ModularCurve.coeffEmb L y) = ModularCurve.coeffEmb Qb y := by
    intro y
    ext k
    change algebraMap L Qb ((ModularCurve.coeffEmb L y).coeff k) = (ModularCurve.coeffEmb Qb y).coeff k
    rw [ModularCurve.coeffEmb_coeff, ModularCurve.coeffEmb_coeff]
    have : (algebraMap L Qb).comp (algebraMap ℚ L) = algebraMap ℚ Qb := Subsingleton.elim _ _
    exact RingHom.congr_fun this (y.coeff k)
  have hmul : σbar * Dd = Dd' * σbar := by
    apply AlgEquiv.ext
    intro f
    have key : (σbar * Dd : E ≃ₐ[Qb] E).toAlgHom = (Dd' * σbar : E ≃ₐ[Qb] E).toAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin Qb (S := ModularCurve.x1FunctionFieldBar (M * p))
        (s := ⇑(ModularCurve.coeffEmb Qb) '' ((ModularCurve.x1FunctionField (M * p)) : Set (LaurentSeries ℚ))) rfl ?_
      rintro _ ⟨y, hy, rfl⟩
      change σbar (Dd _) = Dd' (σbar _)
      refine hagree _ ⟨ModularCurve.coeffEmb L y, ?_⟩ ?_
      · rw [hK]; exact ModularCurve.coeffEmb_mem_laurentBaseChange L hy
      · change ModularCurve.coeffEmb Qb y = ι (ModularCurve.coeffEmb L y)
        rw [hιemb]
    exact AlgHom.congr_fun key f
  rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, hmul]

end S_ModularCurve_XOneP_ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul (solution)
