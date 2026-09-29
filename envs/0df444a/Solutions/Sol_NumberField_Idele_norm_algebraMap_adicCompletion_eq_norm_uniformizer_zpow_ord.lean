-- Prove2me | solution 1 for NumberField.Idele.norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f557b3d2-37f4-5c2d-a931-bb473c8af71e

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (u : Kˣ) :
    ‖algebraMap K (v.adicCompletion K) (u : K)‖ =
      ‖(ϖ : v.adicCompletion K)‖ ^
        NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)  := by
  set y : v.adicCompletion K := algebraMap K (v.adicCompletion K) (u : K) with hy
  set n : ℤ := NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) with hn

  have hvy : Valued.v y = WithZero.exp (-n) := by
    have h := NumberField.Idele.valued_snd_eq_exp_neg_ord K v
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)
    exact h

  have hϖ1 : Valued.v (ϖ : v.adicCompletion K) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have hϖ0 : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro h; apply hϖ.ne_zero; exact_mod_cast h
  have hvϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1) := by
    apply le_antisymm
    ·
      obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (ϖ : v.adicCompletion K) = WithZero.exp m :=
        ⟨WithZero.log (Valued.v (ϖ : v.adicCompletion K)), (WithZero.exp_log hϖ0).symm⟩
      rw [hm] at hϖ1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hϖ1
      rw [WithZero.exp_le_exp]
      omega
    ·
      obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
      have hπv : Valued.v ((π : K) : v.adicCompletion K) = WithZero.exp (-1) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
      have hπO : ((π : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπv, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
      have hmax : (⟨((π : K) : v.adicCompletion K), hπO⟩ : v.adicCompletionIntegers K) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
        rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v]
        show Valued.v ((π : K) : v.adicCompletion K) < 1
        rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmax
      obtain ⟨a, ha⟩ := hmax
      have ha' : (a : v.adicCompletion K) * (ϖ : v.adicCompletion K) = ((π : K) : v.adicCompletion K) := by
        have := congrArg (fun x : v.adicCompletionIntegers K => (x : v.adicCompletion K)) ha
        simpa using this
      calc WithZero.exp (-1) = Valued.v ((π : K) : v.adicCompletion K) := hπv.symm
        _ = Valued.v (a : v.adicCompletion K) * Valued.v (ϖ : v.adicCompletion K) := by rw [← ha', map_mul]
        _ ≤ 1 * Valued.v (ϖ : v.adicCompletion K) := mul_le_mul_left a.2 _
        _ = _ := one_mul _

  have hϖne : (ϖ : v.adicCompletion K) ≠ 0 := fun h => hϖ0 (by rw [h, map_zero])
  have hval : Valued.v y = Valued.v ((ϖ : v.adicCompletion K) ^ n) := by
    rw [hvy, map_zpow₀, hvϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]
  have e : ‖y‖ = ‖(ϖ : v.adicCompletion K) ^ n‖ :=
    le_antisymm (Valued.toNormedField.norm_le_iff.mpr hval.le) (Valued.toNormedField.norm_le_iff.mpr hval.ge)
  rw [e, norm_zpow]

end S_NumberField_Idele_norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord
end P2MW
export P2MW.S_NumberField_Idele_norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord (solution)
