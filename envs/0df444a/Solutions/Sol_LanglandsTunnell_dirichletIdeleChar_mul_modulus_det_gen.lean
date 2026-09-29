-- Prove2me | solution 1 for LanglandsTunnell.dirichletIdeleChar_mul_modulus_det_gen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bb27f41f-fc5b-5455-b3c7-998230b2722b

import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

namespace P2GProbe
namespace C2prime

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel
open RatIdele Rat.HeightOneSpectrum
open scoped NNReal

noncomputable section

private theorem det_diagOne_eq {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = (a : A)
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_gen_eq_uniformizerIdele (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)
      = Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v)) := by
  rw [productionPinsCompact_gen]
  show Matrix.GeneralLinearGroup.det
      (diagOne (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))))
    = Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))
  exact det_diagOne_eq _

private theorem toNNReal_exp_neg_one_eq_inv {e : ℝ≥0} (he : e ≠ 0) :
    WithZeroMulInt.toNNReal he (WithZero.exp (-1 : ℤ)) = e⁻¹ := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]
  have h1 : WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ))) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.mp (WithZero.coe_unzero _)
  rw [h1, toAdd_ofAdd, zpow_neg_one]

private theorem absNorm_asIdeal_eq_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = natGenerator v := by
  rw [asIdeal_eq_span_natGenerator v, Ideal.absNorm_span_singleton,
    ← map_natCast (algebraMap ℤ (𝓞 ℚ)) (natGenerator v), Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]

private theorem coe_distribHaarChar_uniformizerIdele
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)
        (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))) : ℝ)
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [hprod, Finset.prod_eq_one, one_mul, finprod_eq_single _ v]
  · rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_self, FinitePlace.norm_def,
      valued_uniformizerUnit, toNNReal_exp_neg_one_eq_inv, NNReal.coe_inv, NNReal.coe_natCast]
  · intro w hw
    rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hw, norm_one]
  · intro w _
    rw [Units.coe_map, finIncl_apply_fst]
    simp only [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]

private theorem coe_modulusChar_uniformizerIdele
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((((Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
          (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits)
        (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))) : ℂˣ) : ℂ)
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by
  show ((MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)
      (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))) : ℝ) : ℂ)
    = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹
  rw [coe_distribHaarChar_uniformizerIdele hprod v, Complex.ofReal_inv, Complex.ofReal_natCast]

private theorem value_at_det_gen_of_prod {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)})
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)
        = χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by
  intro v hv
  have hvn : ¬ natGenerator v ∣ n := fun h =>
    hS v hv (Ideal.dvd_span_singleton.mpr ((natCast_mem_asIdeal_iff v n).mpr h))
  rw [MonoidHom.comp_apply, det_gen_eq_uniformizerIdele v, MonoidHom.mul_apply, Units.val_mul,
    DirichletCharacter.coe_dirichletIdeleChar_finIncl_localUnit_of_valued_exp_neg_one χ hvn
      (uniformizerUnit ℚ v) (valued_uniformizerUnit ℚ v),
    coe_modulusChar_uniformizerIdele hprod v, absNorm_asIdeal_eq_natGenerator v]

end

end P2GProbe.C2prime

open NumberField AutomorphicForm in
open IsDedekindDomain in
theorem solution
    {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)
        = χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by
  have hprod := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm ℚ
  exact P2GProbe.C2prime.value_at_det_gen_of_prod χ S hS hprod

end S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen
end P2MW
export P2MW.S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen (solution)
