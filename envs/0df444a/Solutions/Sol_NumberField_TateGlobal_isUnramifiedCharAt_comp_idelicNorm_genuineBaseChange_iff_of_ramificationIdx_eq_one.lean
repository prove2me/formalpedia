-- Prove2me | solution 1 for NumberField.TateGlobal.isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/25589931-b0ba-506f-9d74-d4818f6755cd

import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.TateGlobal NumberField.AdelicLevel M4aHerbrand.GenuineDescent

namespace UnrNorm

private theorem valued_eq_one_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) :
    Valued.v (t : v.adicCompletion K) = 1 ↔
      (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
        ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨h1, h2⟩
    have h0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
    have h3 : 1 ≤ Valued.v (t : v.adicCompletion K) := by rwa [inv_le_one₀ (zero_lt_iff.mpr h0)] at h2
    exact le_antisymm h1 h3

private theorem localChar_one_mul_apply {K : Type} [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    localChar ((1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) * χ) v t = localChar χ v t := by
  rw [localChar_apply, localChar_apply, MonoidHom.mul_apply, MonoidHom.one_apply, one_mul]

private theorem localChar_one_apply {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    localChar (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v t = 1 := by
  rw [localChar_apply, MonoidHom.one_apply]

end UnrNorm

open UnrNorm in
theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 M))
    (he : Ideal.ramificationIdx' (w.under (𝓞 E)).asIdeal w.asIdeal = 1) :
    IsUnramifiedCharAt (μ.comp (genuineBaseChange E M).idelicNorm) w ↔
      IsUnramifiedCharAt μ (w.under (𝓞 E)) := by

  set v : HeightOneSpectrum (𝓞 E) := w.under (𝓞 E) with hv
  let W : v.Extension (𝓞 M) := ⟨w, rfl⟩

  obtain ⟨f, himg, hloc⟩ : ∃ f : (W.1.adicCompletion M)ˣ →* (v.adicCompletion E)ˣ,
      f '' LanglandsTunnell.TateLocal.higherUnitsAt M W.1 0 = LanglandsTunnell.TateLocal.higherUnitsAt E v 0 ∧
        localChar ((1 : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) * μ.comp (genuineBaseChange E M).idelicNorm) W.1 =
          localChar (1 : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) W.1 * (localChar μ v).comp f :=
    ⟨_, LanglandsTunnell.TateLocal.image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one E M v W he 0,
      NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange E M 1 μ v W⟩
  have key : ∀ t : (W.1.adicCompletion M)ˣ,
      localChar (μ.comp (genuineBaseChange E M).idelicNorm) w t = localChar μ v (f t) := by
    intro t
    have h := DFunLike.congr_fun hloc t
    rw [localChar_one_mul_apply, MonoidHom.mul_apply, localChar_one_apply, one_mul, MonoidHom.comp_apply] at h
    exact h
  constructor
  ·
    intro h s hs hs'
    have hs1 : s ∈ LanglandsTunnell.TateLocal.higherUnitsAt E v 0 :=
      (LanglandsTunnell.TateLocal.mem_higherUnitsAt_zero_iff E v).mpr ((valued_eq_one_iff v s).mpr ⟨hs, hs'⟩)
    rw [← himg] at hs1
    obtain ⟨t, ht, rfl⟩ := hs1
    have ht1 := (valued_eq_one_iff W.1 t).mp ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_zero_iff M W.1).mp ht)
    rw [← key t]
    exact h t ht1.1 ht1.2
  ·
    intro h t ht ht'
    rw [key t]
    have ht1 : t ∈ LanglandsTunnell.TateLocal.higherUnitsAt M W.1 0 :=
      (LanglandsTunnell.TateLocal.mem_higherUnitsAt_zero_iff M W.1).mpr ((valued_eq_one_iff W.1 t).mpr ⟨ht, ht'⟩)
    have hs1 : f t ∈ LanglandsTunnell.TateLocal.higherUnitsAt E v 0 := by
      rw [← himg]
      exact ⟨t, ht1, rfl⟩
    have hs2 := (valued_eq_one_iff v (f t)).mp ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_zero_iff E v).mp hs1)
    exact h (f t) hs2.1 hs2.2

end S_NumberField_TateGlobal_isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_TateGlobal_isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one (solution)
