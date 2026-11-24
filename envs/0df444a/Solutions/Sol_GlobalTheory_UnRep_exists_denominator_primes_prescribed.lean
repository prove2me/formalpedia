-- Prove2me | solution 1 for GlobalTheory.UnRep.exists_denominator_primes_prescribed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:07.898072+00:00
-- url     : https://prove2.me/submissions/09315444-f66e-4853-b2ba-ef82c352b9be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Theorems.Thm_GlobalTheory_UnRep_exists_pow_eq_span_singleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (Q : Ideal (𝓞 E) → Prop) (ι : Type) [Finite ι]
      (x : ι → E),
      (∀ i, ∀ P : HeightOneSpectrum (𝓞 E), ¬ Q P.asIdeal → P.valuation E (x i) ≤ 1) →
      ∃ s : 𝓞 E, s ≠ 0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Q P) ∧
        ∀ i, ∃ b : 𝓞 E, (s : E) * x i = (b : E) := by
  intro E _ _ Q ι _ x hx
  classical
  have : Fintype ι := Fintype.ofFinite ι

  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : E), v.valuation E y ≤ 1 →
      ∃ u : 𝓞 E, u ∉ v.asIdeal ∧ ∃ b : 𝓞 E, (u : E) * y = (b : E) := by
    intro v y hy
    obtain ⟨n, d, hnd | hnd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact hnd⟩
    · have hd : v.valuation E (algebraMap (𝓞 E) E d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
        exact d.2
      have hprod : v.valuation E y * v.valuation E (algebraMap (𝓞 E) E n) = 1 := by
        rw [← map_mul, hnd, hd]
      have hn1 : 1 ≤ v.valuation E (algebraMap (𝓞 E) E n) := by
        calc (1 : _) = v.valuation E y * v.valuation E (algebraMap (𝓞 E) E n) := hprod.symm
          _ ≤ v.valuation E (algebraMap (𝓞 E) E n) := mul_le_of_le_one_left' hy
      have hn : n ∉ v.asIdeal := by
        rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
        exact le_antisymm (HeightOneSpectrum.valuation_le_one _ _) hn1
      exact ⟨n, hn, d, by rw [mul_comm]; exact hnd⟩

  let A : ι → Ideal (𝓞 E) := fun i =>
    { carrier := {r | ∃ b : 𝓞 E, (r : E) * x i = (b : E)}
      add_mem' := by
        rintro r₁ r₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
        exact ⟨b₁ + b₂, by push_cast; rw [add_mul, h₁, h₂]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c r ⟨b, h⟩
        exact ⟨c * b, by simp only [smul_eq_mul]; push_cast; rw [mul_assoc, h]⟩ }
  have memA : ∀ i r, r ∈ A i ↔ ∃ b : 𝓞 E, (r : E) * x i = (b : E) := fun _ _ => Iff.rfl
  let A0 : Ideal (𝓞 E) := ⨅ i, A i
  have hA0 : A0 ≠ ⊥ := by
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) x
    have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    intro hbot
    apply hc0
    have hcmem : (c : 𝓞 E) ∈ A0 := by
      refine (Submodule.mem_iInf _).mpr fun i => (memA i _).mpr ?_
      obtain ⟨b, hb⟩ := hc i
      exact ⟨b, by rw [Algebra.smul_def] at hb; exact hb.symm⟩
    rw [hbot] at hcmem
    exact (Submodule.mem_bot _).mp hcmem
  obtain ⟨h, s, hh, hs⟩ := exists_pow_eq_span_singleton E A0 hA0
  have hsA : s ∈ A0 := Ideal.pow_le_self hh (hs ▸ Ideal.mem_span_singleton_self s)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hs
    exact hA0 (pow_eq_zero_iff hh |>.mp hs)
  refine ⟨s, hs0, ?_, fun i => (memA i s).mp ((Submodule.mem_iInf _).mp hsA i)⟩
  intro P hP hsP
  by_contra hQ
  have hPne : P ≠ ⊥ := fun hb => hs0 ((Submodule.mem_bot _).mp (hb ▸ hsP))
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hP, hPne⟩
  have hle : A0 ≤ P := by
    refine hP.le_of_pow_le (n := h) ?_
    rw [hs, Ideal.span_le, Set.singleton_subset_iff]
    exact hsP
  choose u hu b hb using fun i => key v (x i) (hx i v hQ)
  have hU : (∏ i, u i) ∉ P := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hu i hi
  apply hU
  refine hle ((Submodule.mem_iInf _).mpr fun i => ?_)
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem u (Finset.mem_univ i)) ((memA i _).mpr ⟨b i, hb i⟩)
end GlobalTheory.UnRep
