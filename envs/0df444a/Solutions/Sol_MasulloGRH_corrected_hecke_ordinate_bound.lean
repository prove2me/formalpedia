-- Prove2me | solution 1 for MasulloGRH.corrected_hecke_ordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:04:38.569996+00:00
-- url     : https://prove2.me/submissions/2842aec4-1978-49b3-b608-aa44f0efddf2

import Definitions.Def_MasulloGRH_IdeleNorm
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Theorems.Thm_MasulloGRH_uniform_finite_euler_product_on_signed_ordinates

open NumberField IsDedekindDomain MasulloGRH

theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℝ, 0 < N ∧ ∀ (χ : HeckeCharacter F), (∀ v ∈ Sf, χ.IsUnramifiedAt v) →
      ∃ T : ℤ → ℝ, (∀ k : ℤ, T k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) ∧
        (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
        (∀ k, T k ≤ T (k+1)) ∧
        Filter.Tendsto (fun k => |T k|) Filter.cofinite Filter.atTop ∧
        ∀ k (σ : ℝ), 1 ≤ N * ∏ v ∈ Sf, ‖eulerFactorInv χ v ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ := by
  classical
  let e := (Fintype.equivFin Sf).symm
  let q (i : Fin (Fintype.card Sf)) : ℝ := (Ideal.absNorm (e i).1.asIdeal : ℕ)
  have hq (i) : 1 < q i := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (e i).1
  obtain ⟨c, hc, hall⟩ := MasulloGRH.uniform_finite_euler_product_on_signed_ordinates q hq
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro χ hχ
  let z (i : Fin (Fintype.card Sf)) := χ.primeValue (e i).1
  have hz (i) : ‖z i‖ = 1 := by
    let v := (e i).1
    obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
    have hne : a ≠ 0 := by
      rintro rfl
      exact WithZero.exp_ne_zero (ha.symm.trans (map_zero _))
    have hunif : ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x :=
      ⟨Units.mk0 a hne, ha⟩
    change ‖χ.primeValue v‖ = 1
    unfold HeckeCharacter.primeValue
    rw [dif_pos ⟨hχ _ (e i).2, hunif⟩]
    exact Circle.norm_coe _
  obtain ⟨T, hcell, hpos, hneg, hmon, hlim, hb⟩ := hall z hz
  refine ⟨T, hcell, hpos, hneg, hmon, hlim, ?_⟩
  intro k σ
  let s : ℂ := σ + (T k : ℂ) * Complex.I
  have hprod : (∏ i, ‖1 - z i * (q i : ℂ) ^ (-s)‖) = ∏ v ∈ Sf, ‖eulerFactorInv χ v s‖ := by
    rw [← Finset.prod_coe_sort Sf (fun v => ‖eulerFactorInv χ v s‖),
        ← e.prod_comp (fun v : Sf => ‖eulerFactorInv χ v.1 s‖)]
    simp [z,q,eulerFactorInv,primeNorm]
  calc
    1 = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
    _ ≤ c⁻¹ * ∏ i, ‖1 - z i * (q i : ℂ) ^ (-s)‖ :=
      mul_le_mul_of_nonneg_left (hb k σ) (inv_nonneg.mpr hc.le)
    _ = _ := by rw [hprod]

