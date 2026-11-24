-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:45:21.98816+00:00
-- url     : https://prove2.me/submissions/7562a907-9548-499a-afb7-ec622c3dc746

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_exists_pow_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_exists_mem_pow_not_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_val_le_of_mem_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_val_eq_one_of_not_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_mem_ballV_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_ballV_add
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_exists_near
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
namespace GlobalTheory.CompanionTheory.Equi.CosetStep
variable {F : Type} [Field F] [NumberField F]
private theorem exists_add_eq_one_lemma {v : HeightOneSpectrum (𝓞 F)} {C : Ideal (𝓞 F)}
    (hC : ¬ C ≤ v.asIdeal) (M : ℕ) : ∃ e ∈ C, ∃ f ∈ v.asIdeal ^ M, e + f = 1 := by
  have hcop : C ⊔ v.asIdeal ^ M = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    have h1 : v.asIdeal ^ M ≤ P := le_sup_right.trans hle
    have h2 : C ≤ P := le_sup_left.trans hle
    have h3 : v.asIdeal ≤ P := hP.isPrime.le_of_pow_le h1
    have h4 : v.asIdeal = P := v.isMaximal.eq_of_le hP.ne_top h3
    exact hC (h4 ▸ h2)
  have h1 : (1 : 𝓞 F) ∈ C ⊔ v.asIdeal ^ M := hcop ▸ Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  exact ⟨e, he, f, hf, hef⟩
end GlobalTheory.CompanionTheory.Equi.CosetStep
end
end

set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetStep
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetStep
theorem _root_.solution {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    (x0 : F) (c : Fv F v) :
    ∃ x1 : F, (∀ w, w ≠ v → LocMem I w (x1 - x0)) ∧ algebraMap F (Fv F v) x1 - c ∈ ballV v k := by
  obtain ⟨a, ha⟩ := exists_near v k c
  obtain ⟨a', b', hb', hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (a - x0)
  have hb0 : b' ≠ 0 := nonZeroDivisors.ne_zero hb'
  have hbF : algebraMap (𝓞 F) F b' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb'
  have hspan : Ideal.span {b'} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨r, B', hbB, hB'v⟩ := exists_pow_mul v hspan
  obtain ⟨m, B, hIB, hBv⟩ := exists_pow_mul v hI
  have hCv : ¬ B' * B ≤ v.asIdeal := fun hle => (v.isPrime.mul_le.mp hle).elim hB'v hBv
  obtain ⟨e, he, f, hf, hef⟩ := exists_add_eq_one_lemma hCv (k + r)
  obtain ⟨g, hgB', hgv⟩ := SetLike.not_le_iff_exists.mp hB'v
  have hgF : algebraMap (𝓞 F) F g ≠ 0 := by
    intro h0
    apply hgv
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mp h0]
    exact v.asIdeal.zero_mem
  have hfg : f * g ∈ Ideal.span {b'} * v.asIdeal ^ k := by
    have e1 : v.asIdeal ^ (k + r) * B' = Ideal.span {b'} * v.asIdeal ^ k := by
      rw [hbB, pow_add]
      ring
    rw [← e1]
    exact Ideal.mul_mem_mul hf hgB'
  obtain ⟨h, hh, hbh⟩ := Ideal.mem_span_singleton_mul.mp hfg
  refine ⟨x0 + (a - x0) * algebraMap (𝓞 F) F e, fun w hw => ?_, ?_⟩
  · rw [add_sub_cancel_left]
    obtain ⟨s1, hs1, hs1w⟩ := exists_mem_pow_not_mem hw r
    obtain ⟨s2, hs2, hs2w⟩ := exists_mem_pow_not_mem hw m
    have hs1e : s1 * e ∈ Ideal.span {b'} * B := by
      have e2 : v.asIdeal ^ r * (B' * B) = Ideal.span {b'} * B := by
        rw [hbB]
        ring
      rw [← e2]
      exact Ideal.mul_mem_mul hs1 he
    obtain ⟨β, hβ, hbβ⟩ := Ideal.mem_span_singleton_mul.mp hs1e
    refine ⟨s2 * s1, fun hm => (w.isPrime.mem_or_mem hm).elim hs2w hs1w, s2 * (a' * β), ?_, ?_⟩
    · rw [hIB]
      exact Ideal.mul_mem_mul hs2 (B.mul_mem_left _ hβ)
    · have h1 := congrArg (algebraMap (𝓞 F) F) hbβ
      rw [map_mul, map_mul] at h1
      have e1 : ((s2 * s1 : 𝓞 F) : F) = algebraMap (𝓞 F) F s2 * algebraMap (𝓞 F) F s1 := by
        rw [← map_mul]
      have e2 : ((s2 * (a' * β) : 𝓞 F) : F) =
          algebraMap (𝓞 F) F s2 * (algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F β) := by
        rw [← map_mul, ← map_mul]
      rw [e1, e2, ← hab]
      field_simp
      linear_combination (-(algebraMap (𝓞 F) F s2 * algebraMap (𝓞 F) F a')) * h1
  · have hy : algebraMap F (Fv F v) (x0 + (a - x0) * algebraMap (𝓞 F) F e) - c =
        algebraMap F (Fv F v) ((a - x0) * algebraMap (𝓞 F) F e - (a - x0)) +
          (algebraMap F (Fv F v) a - c) := by
      rw [map_sub, map_add, map_mul, map_sub]
      ring
    rw [hy]
    refine ballV_add ((mem_ballV_iff v k _).mpr ?_) ha
    have e3 : (a - x0) * algebraMap (𝓞 F) F e - (a - x0) =
        -(algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F h / algebraMap (𝓞 F) F g) := by
      have h1 := congrArg (algebraMap (𝓞 F) F) hbh
      have h2 := congrArg (algebraMap (𝓞 F) F) hef
      rw [map_mul, map_mul] at h1
      rw [map_add, map_one] at h2
      rw [← hab]
      field_simp
      linear_combination (algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F g) * h2 +
        algebraMap (𝓞 F) F a' * h1
    rw [e3, Valuation.map_neg, map_div₀, map_mul, val_eq_one_of_not_mem v hgv, div_one]
    calc _ ≤ 1 * WithZero.exp (-(k : ℤ)) :=
          mul_le_mul' (HeightOneSpectrum.valuation_le_one v a') (val_le_of_mem_pow v hh)
      _ = _ := one_mul _
end GlobalTheory.CompanionTheory.Equi.CosetStep
