-- Prove2me | solution 1 for MasulloGRH.exists_sequence_bounded_inv_partial_euler
-- status  : ACCEPTED   (disprove)
-- author  : @Yi
-- created : 2026-11-21T04:02:17.350023+00:00
-- url     : https://prove2.me/submissions/2444c2bd-c345-47fe-8a49-b284fdbbfed4

import Definitions.Def_MasulloGRH_IdeleNorm

set_option autoImplicit false
open MasulloGRH
open NumberField IsDedekindDomain

theorem solution : ¬ (∀
    (F : Type) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : HeckeCharacter F) (_hχ : ∀ v ∈ Sf, χ.IsUnramifiedAt v),
    ∃ (N : ℝ) (T : ℤ → ℝ), 0 < N ∧
      (∀ k : ℤ, 0 ≤ k → 0 ≤ T k) ∧ (∀ k : ℤ, k ≤ 0 → T k ≤ 0) ∧ (∀ k : ℤ, T k ≤ T (k + 1)) ∧
      Filter.Tendsto (fun k : ℤ => |T k|) Filter.cofinite Filter.atTop ∧
      ∀ k : ℤ, 1 ≤ N * ∏ v ∈ Sf, ‖eulerFactorInv χ v (T k * Complex.I)‖) := by
  classical
  intro h
  let F := ℚ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let := hm
  let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have unram : (1 : HeckeCharacter F).IsUnramifiedAt v := by
    intro x _
    rfl
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
  have hne : a ≠ 0 := by
    intro haz
    subst a
    exact WithZero.exp_ne_zero (ha.symm.trans (map_zero _))
  have hunif : ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x := ⟨Units.mk0 a hne, ha⟩
  have prime_one : (1 : HeckeCharacter F).primeValue v = 1 := by
    unfold HeckeCharacter.primeValue
    rw [dif_pos ⟨unram, hunif⟩]
    rfl
  have hh : ∀ w ∈ ({v} : Finset _), (1 : HeckeCharacter F).IsUnramifiedAt w := by
    simpa using unram
  obtain ⟨N,T,_,hpos,hneg,_,_,hb⟩ := h F {v} 1 hh
  have hz : T 0 = 0 := le_antisymm (hneg 0 le_rfl) (hpos 0 le_rfl)
  have hc : (1 : ℝ) ≤ 0 := by simpa [hz, eulerFactorInv, prime_one] using hb 0
  exact (not_le_of_gt zero_lt_one) hc

