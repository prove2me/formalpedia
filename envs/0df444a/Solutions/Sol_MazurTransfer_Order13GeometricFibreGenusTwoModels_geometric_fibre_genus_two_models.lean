-- Prove2me | solution 1 for MazurTransfer.Order13GeometricFibreGenusTwoModels.geometric_fibre_genus_two_models
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:35:50.654161+00:00
-- url     : https://prove2.me/submissions/6bebe734-d937-4e7b-a88d-accac8952253

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every geometric fibre of the literal curve is its explicit
base-field curve, with an original genus-two CurveModel and Riemann-Roch.
Named downstream consumer: the actual integral Picard chart sections.
-/
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_Order13ActualCurveBaseChangeMap
import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualArithmeticCurveModel MazurTransfer.Order13ActualCurveBaseChange
namespace GeometricFibreGenusTwoPublicProof20261017
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal good-characteristic curve and its actual
function field form the original CurveModel and satisfy genus-two
Riemann-Roch over an algebraically closed field.
Named downstream consumer: geometric fibre models in SixSectionPicardChartCriterion.
Reuses complete official Anthropic FLT model and Riemann-Roch APIs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
theorem actual_genus_two_riemannRoch [IsAlgClosed K] :
    ∃ Kc : Divisor K (actualCurveFunctionField K),
      ∀ D : Divisor K (actualCurveFunctionField K),
        (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - 2 := by
  obtain ⟨Kc,g,hRR⟩ := exists_canonicalDivisor_genus_riemannRoch K (actualCurveFunctionField K)
  have hg := eq_genusFF_of_forall_ell_sub_ell_eq
    (actual_constantsAreBase_good_characteristic K) hRR
  rw [actual_genusFF_eq_two_good_characteristic K] at hg
  refine ⟨Kc, ?_⟩
  simpa only [hg, Nat.cast_ofNat] using hRR
end GeometricFibreGenusTwoPublicProof20261017
open GeometricFibreGenusTwoPublicProof20261017
theorem solution (R : Type u) [CommRing R]  (h104 : IsUnit (104 : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (s : Spec (.of k) ⟶ Spec (.of R)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L)
      (M : CurveModel k L) (e : M.C ≅ pullback (curveToBase R) s)
      (he : e.hom ≫ pullback.snd (curveToBase R) s = M.toBase)
      (Kc : Divisor k L),
      ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - 2 := by
  obtain ⟨φ,rfl⟩ := Spec.map_surjective s
  letI : Algebra R k := φ.hom.toAlgebra
  have hk : IsUnit (104 : k) := by
    simpa only [map_ofNat] using h104.map φ.hom
  letI : Fact ((104 : k) ≠ 0) := ⟨hk.ne_zero⟩
  obtain ⟨Kc,hRR⟩ := actual_genus_two_riemannRoch k
  refine ⟨actualCurveFunctionField k, inferInstance, inferInstance, inferInstance,
    actualCurveModel k, (wholeCurve_isPullback R k).isoPullback, ?_, Kc,hRR⟩
  exact (wholeCurve_isPullback R k).isoPullback_hom_snd
#print axioms solution
