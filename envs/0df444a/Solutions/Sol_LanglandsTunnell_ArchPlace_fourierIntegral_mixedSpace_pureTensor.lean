-- Prove2me | solution 1 for LanglandsTunnell.ArchPlace.fourierIntegral_mixedSpace_pureTensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/49f1fc1f-9f78-5513-8eee-6beaecb22da5

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_ArchPlace
import Theorems.Thm_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun
import Theorems.Thm_LanglandsTunnell_ArchPlace_tateFourier_psiComplex_complexTestFun
import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedSpace_apply
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchPlace_fourierIntegral_mixedSpace_pureTensor
p2m_attr_erase "simp" "LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField LanglandsTunnell.ArchPlace

namespace MixedSpacePureTensorTransform

open scoped Classical

private theorem fourierChar_finsetSum_coe_eq_prod {ι : Type} (s : Finset ι) (t : ι → ℝ) :
    (Real.fourierChar (∑ i ∈ s, t i) : ℂ) = ∏ i ∈ s, (Real.fourierChar (t i) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

private theorem psiReal_eq_fourierChar_neg (x : ℝ) : psiReal x = (Real.fourierChar (-x) : ℂ) := by
  rw [psiReal_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem psiComplex_eq_fourierChar_neg (z : ℂ) :
    psiComplex z = (Real.fourierChar (-(2 * z.re)) : ℂ) := by
  simp only [psiComplex_apply, Complex.add_conj, Real.fourierChar_apply]
  push_cast
  ring_nf

private theorem addChar_neg_mul_eq_prod_psiReal_mul_prod_psiComplex (K : Type) [Field K] [NumberField K]
    (ψ : AddChar (mixedEmbedding.mixedSpace K) ℂ)
    (hψ : ∀ v : mixedEmbedding.mixedSpace K,
      ψ v = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace K) v) : ℂ))
    (v x : mixedEmbedding.mixedSpace K) :
    ψ (-(v * x)) = (∏ w, psiReal (v.1 w * x.1 w)) * ∏ w, psiComplex (v.2 w * x.2 w) := by
  rw [hψ, map_neg, mixedEmbedding.trace_mixedSpace_apply, neg_add, ← Finset.sum_neg_distrib,
    ← Finset.sum_neg_distrib, AddChar.map_add_eq_mul, Circle.coe_mul, fourierChar_finsetSum_coe_eq_prod,
    fourierChar_finsetSum_coe_eq_prod]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => (psiReal_eq_fourierChar_neg _).symm
  · exact Finset.prod_congr rfl fun w _ => (psiComplex_eq_fourierChar_neg _).symm

private theorem integral_complexTestFun_mul_psiComplex_eq_half_mul (m : ℤ) (u : ℂ) :
    ∫ t : ℂ, complexTestFun m t * psiComplex (t * u)
      = (1 / 2 : ℂ) * ((-Complex.I) ^ m.natAbs * complexTestFun (-m) u) := by
  have h : ∫ t : ℂ, complexTestFun m t * psiComplex (t * u) ∂((2 : ENNReal) • volume)
      = (-Complex.I) ^ m.natAbs * complexTestFun (-m) u :=
    LanglandsTunnell.ArchPlace.tateFourier_psiComplex_complexTestFun m u
  rw [integral_smul_measure] at h
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat] at h
  rw [← h]
  ring

private theorem transform_pureTensor_mixedSpace_eq (K : Type) [Field K] [NumberField K]
    (a : {w : InfinitePlace K // w.IsReal} → ZMod 2) (k : {w : InfinitePlace K // w.IsComplex} → ℤ)
    (ψ : AddChar (mixedEmbedding.mixedSpace K) ℂ)
    (hψ : ∀ v : mixedEmbedding.mixedSpace K,
      ψ v = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace K) v) : ℂ))
    (x : mixedEmbedding.mixedSpace K) :
    NumberField.AdelicFourier.fourierIntegral ψ volume
        (fun v => (∏ w, realTestFun (a w) (v.1 w)) * ∏ w, complexTestFun (k w) (v.2 w)) x
      = (∏ w, (-Complex.I) ^ (a w).val) * (∏ w, (-Complex.I) ^ (k w).natAbs)
          * (1 / 2 : ℂ) ^ InfinitePlace.nrComplexPlaces K
          * ((∏ w, realTestFun (a w) (x.1 w)) * ∏ w, complexTestFun (-k w) (x.2 w)) := by
  have hint : ∀ v : mixedEmbedding.mixedSpace K,
      ψ (-(v * x)) * ((∏ w, realTestFun (a w) (v.1 w)) * ∏ w, complexTestFun (k w) (v.2 w))
        = (∏ w, realTestFun (a w) (v.1 w) * psiReal (v.1 w * x.1 w))
            * ∏ w, complexTestFun (k w) (v.2 w) * psiComplex (v.2 w * x.2 w) := by
    intro v
    rw [addChar_neg_mul_eq_prod_psiReal_mul_prod_psiComplex K ψ hψ v x, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib]
    ring
  have hcard : Fintype.card {w : InfinitePlace K // w.IsComplex} = InfinitePlace.nrComplexPlaces K :=
    Fintype.card_congr (Equiv.refl _)
  calc NumberField.AdelicFourier.fourierIntegral ψ volume
          (fun v => (∏ w, realTestFun (a w) (v.1 w)) * ∏ w, complexTestFun (k w) (v.2 w)) x
      = ∫ v : mixedEmbedding.mixedSpace K, (∏ w, realTestFun (a w) (v.1 w) * psiReal (v.1 w * x.1 w))
          * ∏ w, complexTestFun (k w) (v.2 w) * psiComplex (v.2 w * x.2 w) := by
        rw [NumberField.AdelicFourier.fourierIntegral_def]
        congr 1
        funext v
        exact hint v
    _ = (∫ y : {w : InfinitePlace K // w.IsReal} → ℝ, ∏ w, realTestFun (a w) (y w) * psiReal (y w * x.1 w))
          * ∫ z : {w : InfinitePlace K // w.IsComplex} → ℂ,
              ∏ w, complexTestFun (k w) (z w) * psiComplex (z w * x.2 w) :=
        integral_prod_mul (μ := volume) (ν := volume)
          (fun y : {w : InfinitePlace K // w.IsReal} → ℝ => ∏ w, realTestFun (a w) (y w) * psiReal (y w * x.1 w))
          (fun z : {w : InfinitePlace K // w.IsComplex} → ℂ =>
            ∏ w, complexTestFun (k w) (z w) * psiComplex (z w * x.2 w))
    _ = (∏ w : {w : InfinitePlace K // w.IsReal}, ∫ t : ℝ, realTestFun (a w) t * psiReal (t * x.1 w))
          * ∏ w : {w : InfinitePlace K // w.IsComplex}, ∫ t : ℂ, complexTestFun (k w) t * psiComplex (t * x.2 w) := by
        congr 1
        · exact MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ => volume)
            (fun (w : {w : InfinitePlace K // w.IsReal}) (t : ℝ) => realTestFun (a w) t * psiReal (t * x.1 w))
        · exact MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ => volume)
            (fun (w : {w : InfinitePlace K // w.IsComplex}) (t : ℂ) => complexTestFun (k w) t * psiComplex (t * x.2 w))
    _ = (∏ w : {w : InfinitePlace K // w.IsReal}, (-Complex.I) ^ (a w).val * realTestFun (a w) (x.1 w))
          * ∏ w : {w : InfinitePlace K // w.IsComplex},
              (1 / 2 : ℂ) * ((-Complex.I) ^ (k w).natAbs * complexTestFun (-k w) (x.2 w)) := by
        congr 1
        · exact Finset.prod_congr rfl fun w _ =>
            LanglandsTunnell.ArchPlace.tateFourier_psiReal_realTestFun (a w) (x.1 w)
        · exact Finset.prod_congr rfl fun w _ => integral_complexTestFun_mul_psiComplex_eq_half_mul (k w) (x.2 w)
    _ = (∏ w, (-Complex.I) ^ (a w).val) * (∏ w, (-Complex.I) ^ (k w).natAbs)
          * (1 / 2 : ℂ) ^ InfinitePlace.nrComplexPlaces K
          * ((∏ w, realTestFun (a w) (x.1 w)) * ∏ w, complexTestFun (-k w) (x.2 w)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, hcard]
        ring

end MixedSpacePureTensorTransform

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (a : {w : InfinitePlace K // w.IsReal} → ZMod 2) (k : {w : InfinitePlace K // w.IsComplex} → ℤ)
    (ψ : AddChar (mixedEmbedding.mixedSpace K) ℂ)
    (hψ : ∀ v : mixedEmbedding.mixedSpace K,
      ψ v = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace K) v) : ℂ))
    (x : mixedEmbedding.mixedSpace K) :
    NumberField.AdelicFourier.fourierIntegral ψ volume
        (fun v => (∏ w, realTestFun (a w) (v.1 w)) * ∏ w, complexTestFun (k w) (v.2 w)) x
      = (∏ w, (-Complex.I) ^ (a w).val) * (∏ w, (-Complex.I) ^ (k w).natAbs)
          * (1 / 2 : ℂ) ^ InfinitePlace.nrComplexPlaces K
          * ((∏ w, realTestFun (a w) (x.1 w)) * ∏ w, complexTestFun (-k w) (x.2 w)) :=
  MixedSpacePureTensorTransform.transform_pureTensor_mixedSpace_eq K a k ψ hψ x

end S_LanglandsTunnell_ArchPlace_fourierIntegral_mixedSpace_pureTensor
end P2MW
export P2MW.S_LanglandsTunnell_ArchPlace_fourierIntegral_mixedSpace_pureTensor (solution)
