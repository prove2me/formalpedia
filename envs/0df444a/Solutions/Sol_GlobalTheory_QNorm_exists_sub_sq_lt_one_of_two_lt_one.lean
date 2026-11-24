-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_sub_sq_lt_one_of_two_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:49.856011+00:00
-- url     : https://prove2.me/submissions/5742e0a5-1554-4c0d-9099-e5b0b840e63c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Theorems.Thm_GlobalTheory_QNorm_exists_sub_sq_mem_of_two_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      Valued.v (2 : v.adicCompletion F) < 1 → ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
        ∃ y : v.adicCompletion F, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ 2) < 1 := by
  intro F _ _ v h2 x hx
  set φ := algebraMap F (v.adicCompletion F) with hφ
  have hval : ∀ k : F, Valued.v (φ k) = v.valuation F k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have hmem : ∀ r : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal :=
    fun r => HeightOneSpectrum.valuation_lt_one_iff_mem v r

  have h2' : (2 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hmem, ← hval, map_ofNat, map_ofNat]
    exact h2

  obtain ⟨k, hk⟩ : ∃ k : F, Valued.v (φ k - x) < 1 := by
    have hU : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x := by
      rw [Valued.mem_nhds]
      refine ⟨1, fun y hy => ?_⟩
      have hy' : Valued.v.restrict (y - x) < Valued.v.restrict 1 := by simpa using hy
      simpa using Valued.v.restrict_lt_iff.mp hy'
    exact (HeightOneSpectrum.denseRange_algebraMap F v).mem_nhds hU
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← hval]
    have e : φ k = (φ k - x) + x := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le hk.le hx)

  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by
    obtain ⟨s, m, hs, hsm⟩ : ∃ s m : 𝓞 F, s ∉ v.asIdeal ∧
        k * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F m := by
      obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := F) v k
      · exact ⟨d, n, d.2, h⟩
      · refine ⟨n, d, fun hn => d.2 ?_, h⟩
        show (d : 𝓞 F) ∈ v.asIdeal
        rw [← hmem, ← h, map_mul]
        exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem n).2 hn)
    obtain ⟨t, i, hi, hti⟩ := (Ideal.IsPrime.isMaximal v.isPrime v.ne_bot).exists_inv hs
    refine ⟨t * m, ?_⟩
    have hi' : i = 1 - t * s := by rw [← hti]; ring
    have e : k - algebraMap (𝓞 F) F (t * m) = k * algebraMap (𝓞 F) F i := by
      rw [hi', map_mul, ← hsm, map_sub, map_one, map_mul]; ring
    rw [e, map_mul]
    exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem i).2 hi)

  obtain ⟨b, hb⟩ := exists_sub_sq_mem_of_two_mem F v h2' r
  refine ⟨φ (algebraMap (𝓞 F) F b), ?_, ?_⟩
  · rw [hval]
    exact HeightOneSpectrum.valuation_le_one v b
  · have e : x - φ (algebraMap (𝓞 F) F b) ^ 2 =
        -(φ k - x) + (φ (k - algebraMap (𝓞 F) F r) + φ (algebraMap (𝓞 F) F (r - b ^ 2))) := by
      simp only [map_sub, map_pow]; ring
    rw [e]
    refine Valuation.map_add_lt _ (by rwa [Valuation.map_neg]) (Valuation.map_add_lt _ ?_ ?_)
    · rw [hval]; exact hr
    · rw [hval]; exact (hmem _).2 hb
end GlobalTheory.QNorm
