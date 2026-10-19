-- Prove2me | solution 1 for InvariantSubspaceProblem.normal_exists_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:08:48.769004+00:00
-- url     : https://prove2.me/submissions/66f2936d-aa64-4dc2-a894-e51ff1c2d031

import Mathlib
import Definitions.Def_InvariantSubspaceProblem_Defs

open InvariantSubspaceProblem in
theorem solution (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hdim : 1 < Module.rank ℂ H) (T : H →L[ℂ] H) [IsStarNormal T] :
    HasNontrivialClosedInvariantSubspace T := by
  have hnt : Nontrivial H := by
    exact (rank_pos_iff_nontrivial (R := ℂ)).1 (lt_trans zero_lt_one hdim)
  have hne : (spectrum ℂ T).Nonempty := spectrum.nonempty T
  by_cases hsing : ∃ l₁ ∈ spectrum ℂ T, ∃ l₂ ∈ spectrum ℂ T, l₁ ≠ l₂
  · obtain ⟨l₁, h₁, l₂, h₂, h12⟩ := hsing
    set δ : ℝ := ‖l₁ - l₂‖ / 2 with hδ
    have hδ0 : 0 < δ := by
      have : 0 < ‖l₁ - l₂‖ := norm_pos_iff.2 (sub_ne_zero.2 h12)
      positivity
    let f : ℂ → ℂ := fun z => ((max 0 (δ - ‖z - l₁‖) : ℝ) : ℂ)
    let g : ℂ → ℂ := fun z => ((max 0 (δ - ‖z - l₂‖) : ℝ) : ℂ)
    have hfc : Continuous f := by fun_prop
    have hgc : Continuous g := by fun_prop
    have hfg : f * g = 0 := by
      funext z
      simp only [Pi.mul_apply, Pi.zero_apply, f, g]
      by_cases ha : δ - ‖z - l₁‖ ≤ 0
      · rw [max_eq_left ha]; simp
      · by_cases hb : δ - ‖z - l₂‖ ≤ 0
        · rw [max_eq_left hb]; simp
        · exfalso
          push_neg at ha hb
          have : ‖l₁ - l₂‖ ≤ ‖z - l₁‖ + ‖z - l₂‖ := by
            calc ‖l₁ - l₂‖ = ‖(z - l₂) - (z - l₁)‖ := by ring_nf
              _ ≤ ‖z - l₂‖ + ‖z - l₁‖ := norm_sub_le _ _
              _ = _ := add_comm _ _
          linarith
    set A := cfc f T with hA
    set B := cfc g T with hB
    have hAB : A * B = 0 := by
      rw [hA, hB, ← cfc_mul f g T]
      rw [show (fun x => f x * g x) = (0 : ℂ → ℂ) from hfg, cfc_zero]
    have hA0 : A ≠ 0 := by
      intro h
      have h' : cfc f T = cfc (0 : ℂ → ℂ) T := by rw [cfc_zero]; exact h
      have := (eqOn_of_cfc_eq_cfc h' (hf := hfc.continuousOn) (hg := continuousOn_const)) h₁
      simp only [f, sub_self, norm_zero, sub_zero, Pi.zero_apply, Complex.ofReal_eq_zero] at this
      rw [max_eq_right hδ0.le] at this
      exact hδ0.ne' this
    have hB0 : B ≠ 0 := by
      intro h
      have h' : cfc g T = cfc (0 : ℂ → ℂ) T := by rw [cfc_zero]; exact h
      have := (eqOn_of_cfc_eq_cfc h' (hf := hgc.continuousOn) (hg := continuousOn_const)) h₂
      simp only [g, sub_self, norm_zero, sub_zero, Pi.zero_apply, Complex.ofReal_eq_zero] at this
      rw [max_eq_right hδ0.le] at this
      exact hδ0.ne' this
    have hcomm : Commute T A := by
      have := cfc_commute_cfc (id : ℂ → ℂ) f T
      rwa [cfc_id ℂ T] at this
    refine ⟨LinearMap.ker (A : H →ₗ[ℂ] H), A.isClosed_ker, ?_, ?_, ?_⟩
    · intro h
      apply hB0
      ext y
      have : B y ∈ LinearMap.ker (A : H →ₗ[ℂ] H) := by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        have := congrArg (fun M : H →L[ℂ] H => M y) hAB
        simpa using this
      rw [h] at this
      simpa using this
    · intro h
      apply hA0
      ext y
      have : y ∈ LinearMap.ker (A : H →ₗ[ℂ] H) := by rw [h]; trivial
      simpa using this
    · intro x hx
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      have := congrArg (fun M : H →L[ℂ] H => M x) hcomm.eq
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [← this, hx, map_zero]
  · push_neg at hsing
    obtain ⟨l, hl⟩ := hne
    have hT : T = l • (1 : H →L[ℂ] H) := by
      have h1 : cfc (id : ℂ → ℂ) T = cfc (fun _ => l) T :=
        cfc_congr (fun z hz => by simp [hsing z hz l hl])
      rw [cfc_id ℂ T, cfc_const l T] at h1
      rw [h1, Algebra.algebraMap_eq_smul_one]
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    refine ⟨Submodule.span ℂ {v}, Submodule.closed_of_finiteDimensional _, ?_, ?_, ?_⟩
    · rw [Ne, Submodule.span_singleton_eq_bot]; exact hv
    · intro h
      have h1 := rank_span_le (R := ℂ) ({v} : Set H)
      rw [h, rank_top, Cardinal.mk_singleton] at h1
      exact absurd hdim (not_lt.2 h1)
    · intro x hx
      rw [hT]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
      exact Submodule.smul_mem _ _ hx
