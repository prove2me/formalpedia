-- Prove2me | solution 1 for LipschitzModulus.comp_real_functional_general
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:52.297203+00:00
-- url     : https://prove2.me/submissions/5606a1b6-958b-4cab-aedb-08d1533f7012

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

/- Adapted from RegMTProof.modulus_comp by Prove2me user sometik179, accepted submission c137b972-b60a-4d9e-9e5f-2c13f3596d16 (Apache-2.0). -/
open WassersteinDRO.Duality
open scoped ENNReal NNReal BigOperators Topology Classical

namespace RegMTProof
variable {E : Type*} [NormedAddCommGroup E]

theorem modulus_le (f : E → ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    lipschitzModulus f ≤ K := by
  refine iSup_le fun x => iSup_le fun y => iSup_le fun hxy => ?_
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h := hK.dist_le_mul x y
  simp only [dist_eq_norm, Real.norm_eq_abs] at h
  calc
    ENNReal.ofReal (|f x-f y| / ‖x-y‖) ≤ ENNReal.ofReal K :=
      ENNReal.ofReal_le_ofReal ((div_le_iff₀ hd).mpr h)
    _ = K := by simp

theorem modulus_ne_top (f : E → ℝ) (hLip : ∃ K, LipschitzWith K f) :
    lipschitzModulus f ≠ ⊤ := by
  obtain ⟨K,hK⟩ := hLip
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (modulus_le f hK)

theorem modulus_bound (f : E → ℝ) (hLip : ∃ K, LipschitzWith K f) (x y : E) :
    |f x-f y| ≤ (lipschitzModulus f).toReal * ‖x-y‖ := by
  by_cases hxy : x=y
  · subst y; simp
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h : ENNReal.ofReal (|f x-f y| / ‖x-y‖) ≤ lipschitzModulus f :=
    le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy le_rfl))
  have hr := ENNReal.toReal_mono (modulus_ne_top f hLip) h
  rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) hd.le)] at hr
  exact (div_le_iff₀ hd).mp hr

theorem modulus_lipschitz (f : E → ℝ) (hLip : ∃ K, LipschitzWith K f) :
    LipschitzWith ⟨(lipschitzModulus f).toReal, ENNReal.toReal_nonneg⟩ f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs]
  change |f x-f y| ≤ (lipschitzModulus f).toReal * ‖x-y‖
  exact modulus_bound f hLip x y

variable [NormedSpace ℝ E]

theorem comp_lipschitz (L : ℝ → ℝ) (hLip : ∃ K, LipschitzWith K L)
    (beta : E →L[ℝ] ℝ) : ∃ K, LipschitzWith K (fun x => L (beta x)) := by
  obtain ⟨K,hK⟩ := hLip
  exact ⟨K * ‖beta‖₊, hK.comp beta.lipschitz⟩

theorem modulus_comp (L : ℝ → ℝ) (hLip : ∃ K, LipschitzWith K L)
    (beta : E →L[ℝ] ℝ) :
    lipschitzModulus (fun x => L (beta x)) = lipschitzModulus L * ENNReal.ofReal ‖beta‖ := by
  let F : E → ℝ := fun x => L (beta x)
  have hF : ∃ K, LipschitzWith K F := comp_lipschitz L hLip beta
  have hfin := modulus_ne_top F hF
  apply le_antisymm
  · have h := modulus_le F ((modulus_lipschitz L hLip).comp beta.lipschitz)
    rw [ENNReal.coe_nnreal_eq] at h
    change lipschitzModulus F ≤ ENNReal.ofReal ((lipschitzModulus L).toReal * ‖beta‖) at h
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (modulus_ne_top L hLip)] at h
    exact h
  · unfold lipschitzModulus
    simp only [ENNReal.iSup_mul]
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    let s : ℝ := |L a-L b| / ‖a-b‖
    have hs : 0 ≤ s := div_nonneg (abs_nonneg _) (norm_nonneg _)
    have habpos : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hab)
    have hbnd : ∀ v : E, ‖(s • beta) v‖ ≤ (lipschitzModulus F).toReal * ‖v‖ := by
      intro v
      by_cases hv : beta v=0
      · simp [hv, mul_nonneg ENNReal.toReal_nonneg (norm_nonneg v)]
      have hvpos : 0 < |beta v| := abs_pos.mpr hv
      have hh := modulus_bound F hF ((a / beta v) • v) ((b / beta v) • v)
      have hleft : F ((a / beta v) • v) = L a := by simp [F, hv]
      have hright : F ((b / beta v) • v) = L b := by simp [F, hv]
      rw [hleft, hright, ← sub_smul, norm_smul, Real.norm_eq_abs,
        ← sub_div, abs_div] at hh
      have hh' : |L a-L b| * |beta v| ≤
          (lipschitzModulus F).toReal * |a-b| * ‖v‖ := by
        apply (le_div_iff₀ hvpos).mp
        calc
          |L a-L b| ≤ (lipschitzModulus F).toReal * (|a-b| / |beta v| * ‖v‖) := hh
          _ = ((lipschitzModulus F).toReal * |a-b| * ‖v‖) / |beta v| := by ring
      rw [smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs, Real.norm_eq_abs]
      change (|L a-L b| / |a-b|) * |beta v| ≤ _
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ habpos).mpr (by nlinarith [hh'])
    have ho := (s • beta).opNorm_le_bound ENNReal.toReal_nonneg hbnd
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] at ho
    change ENNReal.ofReal s * ENNReal.ofReal ‖beta‖ ≤ _
    rw [← ENNReal.ofReal_mul hs]
    exact (ENNReal.ofReal_le_ofReal ho).trans_eq (ENNReal.ofReal_toReal hfin)

end RegMTProof

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ) (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (φ : E →L[ℝ] ℝ) :
    WassersteinDRO.Duality.lipschitzModulus (fun x => f (φ x)) =
      WassersteinDRO.Duality.lipschitzModulus f * ENNReal.ofReal ‖φ‖ := by
  exact RegMTProof.modulus_comp f hf φ
