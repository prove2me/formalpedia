-- Prove2me | solution 1 for GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:51:40.029977+00:00
-- url     : https://prove2.me/submissions/37842ad2-4639-40ce-a207-d1562571695d

import Mathlib
open NumberField IsDedekindDomain Filter Topology Set
set_option maxHeartbeats 4000000
noncomputable section
private theorem ideal_series (E : Type*) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    Summable (fun I : Ideal (𝓞 E) => (Ideal.absNorm I : ℝ) ^ (-s)) := by
  classical
  let A (n : ℕ) := Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n}
  let f (n : ℕ) : ℂ := (A n : ℂ)
  have hnz := (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT E).eventually_ne
    (Complex.ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_ne_zero E))
  have hlt : ∀ᶠ r : ℝ in 𝓝[>] 1, r < s := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)
  obtain ⟨r, hr, hz⟩ := (hlt.and hnz).exists
  have hsum : LSeriesSummable f (r:ℂ) := by
    by_contra bad
    apply hz
    have hzero : NumberField.dedekindZeta E (r : ℂ) = 0 := tsum_eq_zero_of_not_summable bad
    simp [hzero]
  have H : LSeriesSummable f (s:ℂ) := hsum.of_re_le_re (by simpa using hr.le)
  have Hn : Summable (fun n : ℕ => (A n : ℝ) * (n : ℝ) ^ (-s)) := by
    apply H.norm.congr; intro n
    rw [LSeries.norm_term_eq]; by_cases hn : n = 0
    · subst n; simp [Real.zero_rpow (show -s ≠ 0 by linarith)]
    · simp [hn,f,Real.rpow_neg (Nat.cast_nonneg _),div_eq_mul_inv]
  refine summable_of_sum_le (c := ∑' n : ℕ, (A n : ℝ) * (n : ℝ) ^ (-s)) (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_
  intro T
  let N : Ideal (𝓞 E) → ℕ := Ideal.absNorm
  let v (n : ℕ) := (n : ℝ) ^ (-s)
  calc
    _ = ∑ n ∈ T.image N, ∑ I ∈ T.filter (fun I => N I = n), v (N I) :=
      (Finset.sum_fiberwise_of_maps_to (fun _ => Finset.mem_image_of_mem N) _).symm
    _ ≤ ∑ n ∈ T.image N, (A n : ℝ) * v n := by
      apply Finset.sum_le_sum; intro n _
      let S := T.filter (fun I => N I = n)
      have hsub (I) (hI : I ∈ S) : N I = n := (Finset.mem_filter.mp hI).2
      haveI : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
      have hc : S.card ≤ A n := by
        let g : S → {I : Ideal (𝓞 E) // Ideal.absNorm I = n} := fun I => ⟨I.1, hsub _ I.2⟩
        simpa [A] using Nat.card_le_card_of_injective g (fun a b h => Subtype.ext (congrArg (fun I : {I : Ideal (𝓞 E) // Ideal.absNorm I = n} => I.val) h))
      calc
        _ = ∑ _I ∈ S, v n := Finset.sum_congr rfl (fun I hI => congrArg v (hsub I hI))
        _ = (S.card : ℝ) * v n := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := Hn.sum_le_tsum _ (fun n _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
private theorem complex_series (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) : Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := by
  apply (ideal_series K hs).congr; intro I
  by_cases h : Ideal.absNorm I = 0
  · rw [h]; simp [Real.zero_rpow (show -s.re ≠ 0 by linarith), Complex.zero_cpow (neg_ne_zero.mpr (show s ≠ 0 from fun he => by rw [he] at hs; norm_num at hs))]
  · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h), Complex.neg_re]


theorem solution (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
  classical
  let N : Ideal (𝓞 K) → ℕ := Ideal.absNorm
  let f (I : Ideal (𝓞 K)) := ((N I : ℕ) : ℂ) ^ (-s)
  have H : Summable f := (complex_series K hs).of_norm
  have Hf := H.hasSum.tsum_fiberwise N
  unfold NumberField.dedekindZeta LSeries
  rw [← Hf.tsum_eq]; apply tsum_congr; intro n
  have hom (I : N ⁻¹' {n}) : f I.val = (n : ℂ) ^ (-s) := by
    have he : N I.val = n := I.property; simp [f,he]
  rw [tsum_congr hom]
  haveI : Finite (N ⁻¹' {n}) := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  letI := Fintype.ofFinite (N ⁻¹' {n})
  rw [tsum_fintype]; simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  change LSeries.term _ s n = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) * (n : ℂ) ^ (-s)
  by_cases hn : n = 0
  · subst n; simp [LSeries.term_def, Complex.zero_cpow (neg_ne_zero.mpr (show s ≠ 0 from fun he => by rw [he] at hs; norm_num at hs))]
  · simp [LSeries.term_def,hn,Complex.cpow_neg,div_eq_mul_inv]
