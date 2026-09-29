-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ea299983-a20d-5fe2-a237-8bb7a0cffcc1

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt.LanglandsTunnell LanglandsTunnell.Converse"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg"
open AutomorphicForm

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "HasSphericalTorusValuesAt LocalGL3 IsInducedSphericalAt IsTwistRamifiedAbove IsBadPlace localMaximalCompact3 inducedCoeff isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul"
namespace TwistSph
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem ringHom_ringOfIntegers_rat_ext {S : Type*} [Ring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  ext x
  have hx : x = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h _

theorem algebra_ringOfIntegers_rat_eq (X : Type) [Field X] [NumberField X] (i : Algebra (𝓞 ℚ) (𝓞 X)) :
    i = NumberField.inst_ringOfIntegersAlgebra ℚ X :=
  Algebra.algebra_ext i (NumberField.inst_ringOfIntegersAlgebra ℚ X) fun r =>
    RingHom.congr_fun
      (ringHom_ringOfIntegers_rat_ext (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ i)
        (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ X))) r

theorem localChar_twist_apply_eq_of_mem_integers (K : Type) [Field K] [NumberField K]
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : v.Extension (𝓞 K)) (hχ : IsUnramifiedCharAt χ v)
    (t : (W.1.adicCompletion K)ˣ) (ht : (t : W.1.adicCompletion K) ∈ W.1.adicCompletionIntegers K)
    (ht' : ((t⁻¹ : (W.1.adicCompletion K)ˣ) : W.1.adicCompletion K) ∈ W.1.adicCompletionIntegers K) :
    localChar (ν * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) W.1 t = localChar ν W.1 t := by
  rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange ℚ K ν χ v W, MonoidHom.mul_apply,
    MonoidHom.comp_apply]
  have h1 : localChar χ v (Units.map (Algebra.norm (v.adicCompletion ℚ)) t) = 1 := by
    refine hχ _ ?_ ?_
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.coe_map,
        M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg ℚ K v W]
      exact pow_le_one₀ zero_le' ht
    · rw [← map_inv, HeightOneSpectrum.mem_adicCompletionIntegers, Units.coe_map,
        M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg ℚ K v W]
      exact pow_le_one₀ zero_le' ht'
  rw [h1, mul_one]

theorem isUnramifiedCharAt_twist_iff (K : Type) [Field K] [NumberField K]
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v)
    (w : HeightOneSpectrum (𝓞 K)) (hw : w ∈ primeFibre ℚ K v) :
    IsUnramifiedCharAt (ν * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w ↔
      IsUnramifiedCharAt ν w := by
  have key := localChar_twist_apply_eq_of_mem_integers K ν χ v ⟨w, hw⟩ hχ
  constructor
  · intro h t ht ht'
    rw [← key t ht ht']
    exact h t ht ht'
  · intro h t ht ht'
    rw [key t ht ht']
    exact h t ht ht'

theorem isBadPlace_twist_iff (K : Type) [Field K] [NumberField K]
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v) :
    IsBadPlace K (ν * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v ↔ IsBadPlace K ν v := by
  unfold IsBadPlace IsTwistRamifiedAbove
  refine or_congr Iff.rfl (exists_congr fun w => and_congr_right fun hw => not_congr ?_)
  exact isUnramifiedCharAt_twist_iff K ν χ v hχ w hw

theorem coe_twist_uniformizerIdele (K : Type) [Field K] [NumberField K]
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (𝔓 : HeightOneSpectrum (𝓞 K))
    (hχ𝔓 : IsUnramifiedCharAt χ (𝔓.under (𝓞 ℚ))) :
    (((ν * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
          (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
      ((ν (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) *
        ((χ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  obtain ⟨t, ht, hN⟩ := M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit ℚ K 𝔓
  have ht_int : ((t : (𝔓.under (𝓞 ℚ)).adicCompletion ℚ)) ∈ (𝔓.under (𝓞 ℚ)).adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ht]
  have ht_inv_int : (((t⁻¹ : ((𝔓.under (𝓞 ℚ)).adicCompletion ℚ)ˣ)) : (𝔓.under (𝓞 ℚ)).adicCompletion ℚ)
      ∈ (𝔓.under (𝓞 ℚ)).adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
  have hunit :
      χ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) t)) = 1 :=
    hχ𝔓 t ht_int ht_inv_int
  show ((ν (uniformizerIdele K 𝔓) *
      χ ((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm (uniformizerIdele K 𝔓)) : ℂˣ) : ℂ) = _
  rw [hN, map_mul, map_pow, hunit, mul_one, Units.val_mul, Units.val_pow_eq_pow_val]

theorem inducedCoeff_twist (K : Type) [Field K] [NumberField K]
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v) :
    ∀ w ∈ primeFibre ℚ K v,
      inducedCoeff K (ν * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w =
        (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * inducedCoeff K ν w := by
  intro w hw
  have hw' : w.under (𝓞 ℚ) = v := hw
  have hiff := isUnramifiedCharAt_twist_iff K ν χ v hχ w hw
  unfold inducedCoeff
  by_cases hνw : IsUnramifiedCharAt ν w
  · rw [if_pos (hiff.mpr hνw), if_pos hνw, coe_twist_uniformizerIdele K ν χ w (by rw [hw']; exact hχ), hw',
      mul_comm]
  · rw [if_neg (mt hiff.mp hνw), if_neg hνw, mul_zero]

end LanglandsTunnell.CubicInduction.TwistSph

open LanglandsTunnell.CubicInduction.TwistSph in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (v : HeightOneSpectrum (𝓞 ℚ)) (_hχv : IsUnramifiedCharAt χA v) :
    (IsBadPlace K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v ↔ IsBadPlace K ν v) ∧
    (∀ W : LocalGL3 v → ℂ, HasSphericalTorusValuesAt (inducedCoeff K ν) v W →
      HasSphericalTorusValuesAt (inducedCoeff K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) v
        (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) ∧
    (∀ W : LocalGL3 v → ℂ,
      IsInducedSphericalAt (inducedCoeff K ν) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W →
      IsInducedSphericalAt (inducedCoeff K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) v (localMaximalCompact3 (𝓞 ℚ) ℚ v)
        (fun x : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) := by
  classical
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  have hc := inducedCoeff_twist K ν χA v _hχv
  refine ⟨isBadPlace_twist_iff K ν χA v _hχv, fun W hW => ?_, fun W hW => ?_⟩
  · exact (isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul K χA v _hχv
      (inducedCoeff K ν) (inducedCoeff K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm))
      hc W).2.mp hW
  · exact (isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul K χA v _hχv
      (inducedCoeff K ν) (inducedCoeff K (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm))
      hc W).1.mp hW

#print axioms solution

end S_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt (solution)
