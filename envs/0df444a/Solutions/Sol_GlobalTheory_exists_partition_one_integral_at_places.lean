-- Prove2me | solution 1 for GlobalTheory.exists_partition_one_integral_at_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:29.727393+00:00
-- url     : https://prove2.me/submissions/1a8dba63-c364-4204-bd1c-1c3def6544c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPartitionOneIntegralAtPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (L : Type) [Field L] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : S.Nonempty) (Y : S → Finset L)
    (hY : ∀ la, ∀ y ∈ Y la, la.1.valuation L y ≤ 1) :
    ∃ e : S → L, ∑ la, e la = 1 ∧
      ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, la'.valuation L (e la * y) ≤ 1 := by
  classical
  have hb : ∀ (_la : S) (y : L) (la' : HeightOneSpectrum (𝓞 L)),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) * la'.valuation L y ≤ 1 := by
    intro _ y la'
    by_cases hy : la'.valuation L y = 0
    · exact ⟨0, by simp [hy]⟩
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = la'.valuation L y := ⟨_, WithZero.exp_log hy⟩
      refine ⟨m.toNat, ?_⟩
      rw [← hm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  choose n hn using hb
  let N : ℕ := ∑ la : S, ∑ y ∈ Y la, ∑ la' ∈ S, n la y la'
  have hN : ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, n la y la' ≤ N := by
    intro la y hy la' hla'
    calc n la y la' ≤ ∑ la'' ∈ S, n la y la'' :=
          Finset.single_le_sum (f := fun la'' => n la y la'') (fun _ _ => Nat.zero_le _) hla'
      _ ≤ ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'' :=
          Finset.single_le_sum (f := fun y' => ∑ la'' ∈ S, n la y' la'') (fun _ _ => Nat.zero_le _) hy
      _ ≤ N := Finset.single_le_sum (f := fun la => ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'')
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ la)
  let J : S → Ideal (𝓞 L) := fun la => ∏ la' ∈ S.erase la.1, la'.asIdeal ^ N
  have htop : ⨆ la ∈ (Finset.univ : Finset S), J la = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hJM : ∀ la : S, J la ≤ M := fun la =>
      le_trans (le_iSup₂_of_le (f := fun la (_ : la ∈ (Finset.univ : Finset S)) => J la)
        la (Finset.mem_univ _) le_rfl) hle
    obtain ⟨la0, hla0⟩ := hS
    obtain ⟨la1, hla1, h1⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la0, hla0⟩)
    have hle1 : la1.asIdeal ≤ M := hM.isPrime.le_of_pow_le h1
    have heq : la1.asIdeal = M := la1.isMaximal.eq_of_le hM.ne_top hle1
    have hla1S : la1 ∈ S := Finset.mem_of_mem_erase hla1
    obtain ⟨la2, hla2, h2⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la1, hla1S⟩)
    have hle2 : la2.asIdeal ≤ la1.asIdeal := heq ▸ hM.isPrime.le_of_pow_le h2
    have h22 : la2.asIdeal = la1.asIdeal := la2.isMaximal.eq_of_le la1.isPrime.ne_top hle2
    exact (Finset.ne_of_mem_erase hla2) (HeightOneSpectrum.ext h22)
  have h1 : (1 : 𝓞 L) ∈ ⨆ la ∈ (Finset.univ : Finset S), J la := htop ▸ Submodule.mem_top
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 h1
  refine ⟨fun la => ((μ la : 𝓞 L) : L), ?_, ?_⟩
  · have := congrArg (fun x : 𝓞 L => (x : L)) hμ
    simpa using this
  · intro la y hy la' hla'
    rw [map_mul]
    by_cases h : la' = la.1
    · subst h
      calc la.1.valuation L ((μ la : 𝓞 L) : L) * la.1.valuation L y ≤ 1 * 1 :=
            mul_le_mul' (HeightOneSpectrum.valuation_le_one _ _) (hY la y hy)
        _ = 1 := one_mul 1
    · have hmem : (μ la : 𝓞 L) ∈ la'.asIdeal ^ N := by
        have hm : (μ la : 𝓞 L) ∈ J la := (μ la).2
        have hs : la' ∈ S.erase la.1 := Finset.mem_erase.2 ⟨h, hla'⟩
        have : J la ≤ la'.asIdeal ^ N := by
          show ∏ la'' ∈ S.erase la.1, la''.asIdeal ^ N ≤ _
          rw [← Finset.mul_prod_erase _ _ hs]
          exact le_trans Ideal.mul_le_inf inf_le_left
        exact this hm
      have hv : la'.valuation L ((μ la : 𝓞 L) : L) ≤ WithZero.exp (-(N : ℤ)) := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
          Ideal.dvd_span_singleton]
        exact hmem
      calc la'.valuation L ((μ la : 𝓞 L) : L) * la'.valuation L y
          ≤ WithZero.exp (-(N : ℤ)) * la'.valuation L y := mul_le_mul' hv le_rfl
        _ ≤ WithZero.exp (-(n la y la' : ℤ)) * la'.valuation L y := by
            refine mul_le_mul' ?_ le_rfl
            rw [WithZero.exp_le_exp]
            have := hN la y hy la' hla'
            omega
        _ ≤ 1 := hn la y la'
end GlobalTheory
