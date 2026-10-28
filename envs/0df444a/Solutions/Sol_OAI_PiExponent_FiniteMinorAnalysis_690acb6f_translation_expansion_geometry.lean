-- Prove2me | solution 1 for OAI.PiExponent.FiniteMinorAnalysis_690acb6f.translation_expansion_geometry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T10:03:39.229006+00:00
-- url     : https://prove2.me/submissions/1bade8ca-dba8-4bd4-9858-039732de54d1

import Definitions.Def_PiExponent_FiniteTranslationData_690acb6f
import Mathlib
open OAI.PiExponent OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open scoped BigOperators

namespace S39TE
open MvPolynomial

variable {R : Type} [CommRing R]

theorem coeff_mon {m : ℕ} (c : Fin m → R) (a : Fin m → ℕ) (e : Fin m →₀ ℕ) :
    coeff e (∏ i, (C (c i) + X i) ^ a i) = ∏ i, ((a i).choose (e i) : R) * c i ^ (a i - e i) := by
  classical
  have hexp : ∀ i, (C (c i) + X i : MvPolynomial (Fin m) R) ^ a i =
      ∑ k ∈ Finset.range (a i + 1), C ((a i).choose k * c i ^ (a i - k)) * X i ^ k := by
    intro i
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, map_natCast]; ring
  simp_rw [hexp]
  rw [Finset.prod_univ_sum]
  rw [coeff_sum]
  have hterm : ∀ κ : Fin m → ℕ, (∏ i, C ((a i).choose (κ i) * c i ^ (a i - κ i)) * X i ^ (κ i) :
      MvPolynomial (Fin m) R) = monomial (Finsupp.equivFunOnFinite.symm κ)
        (∏ i, ((a i).choose (κ i) : R) * c i ^ (a i - κ i)) := by
    intro κ
    rw [Finset.prod_mul_distrib, ← map_prod, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp
  simp_rw [hterm, coeff_monomial]
  by_cases he : ∀ i, e i ≤ a i
  · rw [Finset.sum_eq_single (⇑e)]
    · simp
    · intro κ _ hκ
      rw [if_neg]; intro h; apply hκ
      rw [← h]; simp
    · intro h; exfalso; apply h
      rw [Fintype.mem_piFinset]; intro i; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (he i)
  · push_neg at he
    obtain ⟨i, hi⟩ := he
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi]; simp)]
    refine Finset.sum_eq_zero fun κ hκ => ?_
    rw [if_neg]; intro h
    rw [Fintype.mem_piFinset] at hκ
    have := hκ i; rw [Finset.mem_range] at this
    have : κ i = e i := by rw [← h]; simp
    omega

theorem binom_shift (L δ : R) (a β : ℕ) :
    ∑ a' ∈ Finset.range (a + 1), ((a.choose a' : R) * (a'.choose β)) * (L ^ (a - a') * δ ^ (a' - β)) =
      (a.choose β : R) * (L + δ) ^ (a - β) := by
  by_cases hβ : a < β
  · rw [Nat.choose_eq_zero_of_lt hβ, Nat.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun a' ha' => ?_
    rw [Finset.mem_range] at ha'
    rw [Nat.choose_eq_zero_of_lt (by omega : a' < β)]; simp
  push_neg at hβ
  have hsplit : a + 1 = β + (a - β + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun a' ha' => by
    rw [Finset.mem_range] at ha'; rw [Nat.choose_eq_zero_of_lt ha']; simp), zero_add]
  rw [add_comm L δ, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  have h1 : (a.choose (β + n) : R) * ((β + n).choose β) = (a.choose β) * ((a - β).choose n) := by
    have : a.choose (β + n) * (β + n).choose β = a.choose β * (a - β).choose (β + n - β) :=
      Nat.choose_mul (by omega)
    rw [show β + n - β = n by omega] at this
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  rw [h1, show a - (β + n) = a - β - n by omega, show β + n - β = n by omega]
  ring

end S39TE

theorem S39TE.mem_rws {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0 < u i) {R : ℝ} {a : Fin n → ℕ} :
    a ∈ OAI.PiExponent.realWeightedSimplex u R ↔ ∑ i, u i * (a i : ℝ) ≤ R := by
  classical
  simp only [OAI.PiExponent.realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  apply Nat.lt_succ_of_le
  apply Nat.le_floor
  rw [le_div_iff₀ (hu i), mul_comm]
  have := Finset.single_le_sum (f := fun j => u j * (a j : ℝ))
    (fun j _ => mul_nonneg (hu j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  linarith

theorem S39TE.entry_expansion {m : ℕ} (K : ℕ) (w0 v theta F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hw0 : 0 < w0) (hq : ∀ i, 2 ≤ q i)
    (selection : Rows K v theta q H → Columns w0 q H)
    (r c : Rows K v theta q H) :
    (MatrixArithmetic.selectedMinor K w0 v theta F H p q selection) r c =
      ∑ t : RowChoice r, scalar F p q r t *
        PowerSeries.coeff (r.2.1 0 - (t.2.2 : ℕ))
          ((periodMonomial r.1.val ((selection c).1 0)
            (fun i => (selection c).1 i.succ)).coeff t.1.1) := by
  classical
  set j : ℕ := r.1.val with hj
  set s : ℕ := r.2.1 0 with hs
  set β : Fin m →₀ ℕ := beta r with hβ
  set h : ℕ := (selection c).1 0 with hh
  set a : Fin m → ℕ := fun i => (selection c).1 i.succ with ha
  set T : Fin m → ℕ := MatrixArithmetic.truncationOrders q F v with hT
  set rc := MatrixArithmetic.rationalCenters p q with hrc
  set L : Fin m → PowerSeries ℂ := fun i => PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ with hL
  set z : Fin m → ℂ := fun i => (j : ℂ) * (rc i - period) with hz
  set δ : Fin m → PowerSeries ℂ := fun i => PowerSeries.C (z i) + logTail (T i) with hδ
  have hLHS : (MatrixArithmetic.selectedMinor K w0 v theta F H p q selection) r c = PowerSeries.coeff s
      ((1 + PowerSeries.X) ^ h * ∏ i, ((a i).choose (β i) : PowerSeries ℂ) * (L i + δ i) ^ (a i - β i)) := by
    show ((InterpolationMatrix.monomialImage rc (fun i => InterpolationMatrix.truncatedLog (T i)) j h a).coeff
      (InterpolationMatrix.exponentVector (fun i => r.2.1 i.succ))).coeff s = _
    rw [InterpolationMatrix.monomialImage, MvPolynomial.coeff_C_mul, S39TE.coeff_mon]
    rw [← Polynomial.coeff_coe]
    congr 1
    have hcoe : ∀ p : Polynomial ℂ, (p : PowerSeries ℂ) = Polynomial.coeToPowerSeries.ringHom p :=
      fun _ => rfl
    rw [hcoe, map_mul, map_prod]
    congr 1
    · simp [← hcoe]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_add, map_natCast]
    congr 2
    simp only [← hcoe, hL, hδ, hz, logTail, InterpolationMatrix.truncatedLog, Polynomial.coe_C]
    simp only [map_mul, map_sub]
    ring
  have hconv : ∀ (P Q : PowerSeries ℂ) (n : ℕ),
      ∑ k : Fin (n + 1), PowerSeries.coeff (k : ℕ) P * PowerSeries.coeff (n - k) Q =
        PowerSeries.coeff n (P * Q) := by
    intro P Q n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Fin.sum_univ_eq_sum_range (fun k => PowerSeries.coeff k P * PowerSeries.coeff (n - k) Q)]
  have hper : ∀ a' : Fin m →₀ ℕ, (periodMonomial j h a).coeff a' =
      (1 + PowerSeries.X) ^ h * ∏ i, ((a i).choose (a' i) : PowerSeries ℂ) * L i ^ (a i - a' i) := by
    intro a'
    rw [periodMonomial, MvPolynomial.coeff_C_mul, S39TE.coeff_mon]
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_prod_type]
  have step1 : ∀ (a' : Transverse q H) (σ : ∀ i, Fin (a'.1 i - beta r i + 1)),
      ∑ k : Fin (r.2.1 0 + 1), scalar F p q r ⟨a', (σ, k)⟩ *
        PowerSeries.coeff (s - k) ((periodMonomial j h a).coeff a'.1) =
      PowerSeries.coeff s (PowerSeries.C ((((∏ i, (a'.1 i).choose (β i) * (a'.1 i - β i).choose (σ i) : ℕ) : ℂ)) *
          ∏ i, z i ^ (a'.1 i - β i - σ i)) *
        ((∏ i, logTail (T i) ^ (σ i : ℕ)) * (periodMonomial j h a).coeff a'.1)) := by
    intro a' σ
    rw [PowerSeries.coeff_C_mul, ← hconv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [scalar]
    ring
  refine Eq.trans ?_ (Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun σ _ => step1 a' σ).symm
  simp only [← map_sum]
  rw [hLHS]
  congr 1
  have hσsum : ∀ (a' : Fin m →₀ ℕ), ∑ σ : (∀ i, Fin (a' i - β i + 1)),
      ∏ i, (PowerSeries.C ((((a' i).choose (β i) * (a' i - β i).choose (σ i) : ℕ) : ℂ) *
        z i ^ (a' i - β i - σ i)) * logTail (T i) ^ (σ i : ℕ)) =
      ∏ i, ((a' i).choose (β i) : PowerSeries ℂ) * δ i ^ (a' i - β i) := by
    intro a'
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (t := fun i => (Finset.univ : Finset (Fin (a' i - β i + 1))))
      (f := fun i x => PowerSeries.C ((((a' i).choose (β i) * (a' i - β i).choose x : ℕ) : ℂ) *
        z i ^ (a' i - β i - x)) * logTail (T i) ^ (x : ℕ))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun x => PowerSeries.C ((((a' i).choose (β i) * (a' i - β i).choose x : ℕ) : ℂ) *
        z i ^ (a' i - β i - x)) * logTail (T i) ^ x)]
    simp only [hδ]
    rw [add_comm (PowerSeries.C (z i)) (logTail (T i)), add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [map_mul, map_pow, map_natCast, Nat.cast_mul]
    ring
  have step2 : ∀ (a' : Transverse q H), ∑ σ : (∀ i, Fin (a'.1 i - beta r i + 1)),
      PowerSeries.C ((((∏ i, (a'.1 i).choose (β i) * (a'.1 i - β i).choose (σ i) : ℕ) : ℂ)) *
          ∏ i, z i ^ (a'.1 i - β i - σ i)) *
        ((∏ i, logTail (T i) ^ (σ i : ℕ)) * (periodMonomial j h a).coeff a'.1) =
      (1 + PowerSeries.X) ^ h * ∏ i, (((a i).choose (a'.1 i) : PowerSeries ℂ) * ((a'.1 i).choose (β i))) *
        (L i ^ (a i - a'.1 i) * δ i ^ (a'.1 i - β i)) := by
    intro a'
    have hre : ∀ σ : (∀ i, Fin (a'.1 i - beta r i + 1)),
        PowerSeries.C ((((∏ i, (a'.1 i).choose (β i) * (a'.1 i - β i).choose (σ i) : ℕ) : ℂ)) *
          ∏ i, z i ^ (a'.1 i - β i - σ i)) *
        ((∏ i, logTail (T i) ^ (σ i : ℕ)) * (periodMonomial j h a).coeff a'.1) =
        ((1 + PowerSeries.X) ^ h * ∏ i, ((a i).choose (a'.1 i) : PowerSeries ℂ) * L i ^ (a i - a'.1 i)) *
        ∏ i, (PowerSeries.C ((((a'.1 i).choose (β i) * (a'.1 i - β i).choose (σ i) : ℕ) : ℂ) *
          z i ^ (a'.1 i - β i - σ i)) * logTail (T i) ^ (σ i : ℕ)) := by
      intro σ
      rw [hper, Nat.cast_prod, ← Finset.prod_mul_distrib, map_prod]
      simp only [Finset.prod_mul_distrib]
      ring
    simp_rw [hre]
    rw [← Finset.mul_sum, hσsum, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  simp_rw [step2]
  rw [← Finset.mul_sum]
  congr 1
  set G : Fin m → ℕ → PowerSeries ℂ := fun i x =>
    (((a i).choose x : PowerSeries ℂ) * (x.choose (β i))) * (L i ^ (a i - x) * δ i ^ (x - β i)) with hG
  have hbin : ∀ i, ((a i).choose (β i) : PowerSeries ℂ) * (L i + δ i) ^ (a i - β i) =
      ∑ x ∈ Finset.range (a i + 1), G i x := fun i => (S39TE.binom_shift (L i) (δ i) (a i) (β i)).symm
  simp_rw [hbin]
  rw [Finset.prod_univ_sum]
  rw [Finset.sum_coe_sort (transverseIndices q H) (fun a' => ∏ i, G i (a' i))]
  rw [transverseIndices, Finset.sum_map]
  simp only [Equiv.coe_toEmbedding, Finsupp.coe_equivFunOnFinite_symm]
  have hfw : ∀ i, 0 < MatrixArithmetic.logWeights q i := by
    intro i
    simp only [MatrixArithmetic.logWeights]
    have : 0 < Real.log (q i) := Real.log_pos (by exact_mod_cast (by have := hq i; omega : 1 < q i))
    exact_mod_cast Nat.ceil_pos.mpr this
  have hcw : ∀ i, 0 < InterpolationMatrix.columnWeights w0 (MatrixArithmetic.logWeights q) i := by
    intro i; refine Fin.cases ?_ (fun k => ?_) i
    · simpa [InterpolationMatrix.columnWeights] using hw0
    · simpa [InterpolationMatrix.columnWeights] using hfw k
  have hcol := (selection c).2
  rw [S39TE.mem_rws hcw, Fin.sum_univ_succ] at hcol
  simp only [InterpolationMatrix.columnWeights, Fin.cases_zero, Fin.cases_succ] at hcol
  have hcolH : ∑ i, MatrixArithmetic.logWeights q i * (a i : ℝ) ≤ H := by
    have : 0 ≤ w0 * ((selection c).1 0 : ℝ) := mul_nonneg hw0.le (by positivity)
    simp only [ha]; linarith
  apply Finset.sum_subset
  · intro κ hκ
    rw [Fintype.mem_piFinset] at hκ
    rw [S39TE.mem_rws hfw]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hcolH
    have : (κ i : ℝ) ≤ a i := by
      have := hκ i; rw [Finset.mem_range] at this; exact_mod_cast Nat.lt_succ_iff.mp this
    exact mul_le_mul_of_nonneg_left this (hfw i).le
  · intro κ _ hκ
    rw [Fintype.mem_piFinset] at hκ
    push_neg at hκ
    obtain ⟨i, hi⟩ := hκ
    rw [Finset.mem_range, not_lt] at hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hG]
    rw [Nat.choose_eq_zero_of_lt (by omega : a i < κ i)]
    simp

theorem S39TE.det_expand {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
    (M : Matrix ι ι ℂ) (g : ∀ i, α i → ℂ) (P : ∀ i, α i → ι → ℂ)
    (hM : ∀ i c, M i c = ∑ t, g i t * P i t c) :
    M.det = ∑ f : (∀ i, α i), (∏ i, g i (f i)) * (Matrix.of fun i c => P i (f i) c).det := by
  have hM' : M = fun i => ∑ t, g i t • P i t := by
    funext i c; rw [hM]; simp [Finset.sum_apply]
  rw [hM']
  change (Matrix.detRowAlternating (n := ι) (R := ℂ)).toMultilinearMap (fun i => ∑ t, g i t • P i t) = _
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem S39TE.logWeights_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (i : Fin m) :
    1 ≤ MatrixArithmetic.logWeights q i := by
  simp only [MatrixArithmetic.logWeights]
  have : 0 < Real.log (q i) := Real.log_pos (by exact_mod_cast (by have := hq i; omega : 1 < q i))
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr this).ne'

theorem solution
    {m : ℕ} (K : ℕ) (w0 v theta F A H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv : 0 < v) (htheta : 0 < theta)
    (hA : 0 ≤ A) (hH : 0 < H) (hq : ∀ i, 2 ≤ q i) :
    0 < rowCount K v theta q H ∧
    Fintype.card (Choices K v theta q H) ≤
      termCount m v H ^ rowCount K v theta q H ∧
    (∑ r : Rows K v theta q H, weight q (beta r)) =
      (rowCount K v theta q H : ℝ) * H *
        MatrixArithmetic.meanRowWeight K v theta q H ∧
    (∀ a : Transverse q H, 0 ≤ weight q a.1) ∧
    0 < lowCount q A H ∧
    (((Finset.univ : Finset (Transverse q H)).filter
      (fun a => weight q a.1 ≤ A * H)).card : ℝ) ≤ (lowCount q A H : ℝ) ∧
    (∀ selection : Rows K v theta q H → Columns w0 q H,
      (MatrixArithmetic.selectedMinor K w0 v theta F H p q selection).det =
        ∑ f : Choices K v theta q H,
          (∏ r, scalar F p q r (f r)) * (periodMatrix selection f).det) := by
  classical
  have hw1 := S39TE.logWeights_pos q hq
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i := fun i => lt_of_lt_of_le one_pos (hw1 i)
  have hrow : 0 < rowCount K v theta q H := by
    rw [rowCount, Fintype.card_pos_iff]
    refine ⟨⟨⟨0, hK⟩, ⟨0, ?_⟩⟩⟩
    simp [strictWeightedSimplex, realWeightedSimplex, hH, hH.le]
  refine ⟨hrow, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- card of choices
    have htr : (transverseIndices q H).card ≤ (⌊H⌋₊ + 1) ^ m := by
      rw [transverseIndices, Finset.card_map]
      calc (realWeightedSimplex (MatrixArithmetic.logWeights q) H).card
          ≤ (Fintype.piFinset fun _ : Fin m => Finset.range (⌊H⌋₊ + 1)).card := by
            apply Finset.card_le_card
            intro a ha
            rw [S39TE.mem_rws hw] at ha
            rw [Fintype.mem_piFinset]; intro i
            rw [Finset.mem_range, Nat.lt_succ_iff]
            apply Nat.le_floor
            have h1 : MatrixArithmetic.logWeights q i * (a i : ℝ) ≤ ∑ j, MatrixArithmetic.logWeights q j * (a j : ℝ) :=
              Finset.single_le_sum (f := fun j => MatrixArithmetic.logWeights q j * (a j : ℝ))
              (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
            have h2 : (a i : ℝ) ≤ MatrixArithmetic.logWeights q i * a i :=
              le_mul_of_one_le_left (Nat.cast_nonneg _) (hw1 i)
            linarith
        _ = (⌊H⌋₊ + 1) ^ m := by simp
    have hbound : ∀ r : Rows K v theta q H, Fintype.card (RowChoice r) ≤ termCount m v H := by
      intro r
      rw [Fintype.card_sigma]
      have hr0 : r.2.1 0 + 1 ≤ ⌊H / v⌋₊ + 1 := by
        have hm := r.2.2
        simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
          Finset.mem_range] at hm
        have := hm.1.1 0
        simp only [InterpolationMatrix.rowWeights, Fin.cases_zero] at this
        omega
      calc ∑ a : Transverse q H, Fintype.card ((∀ i : Fin m, Fin (a.1 i - beta r i + 1)) × Fin (r.2.1 0 + 1))
          ≤ ∑ _a : Transverse q H, (⌊H⌋₊ + 1) ^ m * (⌊H / v⌋₊ + 1) := by
            apply Finset.sum_le_sum
            intro a _
            rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
            apply Nat.mul_le_mul _ hr0
            calc ∏ i, Fintype.card (Fin (a.1 i - beta r i + 1)) ≤ ∏ _i : Fin m, (⌊H⌋₊ + 1) := by
                  apply Finset.prod_le_prod' 
                  intro i _
                  rw [Fintype.card_fin]
                  have ha : a.1 ∈ transverseIndices q H := a.2
                  unfold transverseIndices at ha
                  rw [Finset.mem_map] at ha
                  obtain ⟨b, hb, hab⟩ := ha
                  rw [S39TE.mem_rws hw] at hb
                  have h1 : MatrixArithmetic.logWeights q i * (b i : ℝ) ≤ ∑ j, MatrixArithmetic.logWeights q j * (b j : ℝ) :=
                    Finset.single_le_sum (f := fun j => MatrixArithmetic.logWeights q j * (b j : ℝ))
                    (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
                  have h2 : (b i : ℝ) ≤ MatrixArithmetic.logWeights q i * b i :=
                    le_mul_of_one_le_left (Nat.cast_nonneg _) (hw1 i)
                  have h3 : b i ≤ ⌊H⌋₊ := Nat.le_floor (by linarith)
                  have h4 : a.1 i = b i := by rw [← hab]; simp
                  omega
              _ = (⌊H⌋₊ + 1) ^ m := by simp
        _ = Fintype.card (Transverse q H) * ((⌊H⌋₊ + 1) ^ m * (⌊H / v⌋₊ + 1)) := by simp
        _ ≤ (⌊H⌋₊ + 1) ^ m * ((⌊H⌋₊ + 1) ^ m * (⌊H / v⌋₊ + 1)) := by
            apply Nat.mul_le_mul_right
            simpa using htr
        _ = termCount m v H := by rw [termCount]; ring
    show Fintype.card (∀ r : Rows K v theta q H, RowChoice r) ≤ _
    rw [Fintype.card_pi, rowCount, ← Finset.card_univ]
    exact Finset.prod_le_pow_card _ _ _ fun r _ => hbound r
  · -- weighted sum
    have hne : ((rowCount K v theta q H : ℝ) * H) ≠ 0 := by
      have : (0 : ℝ) < rowCount K v theta q H := by exact_mod_cast hrow
      positivity
    rw [mul_assoc, ← mul_assoc, MatrixArithmetic.meanRowWeight, ← rowCount, mul_div_cancel₀ _ hne,
      MatrixArithmetic.rowWeightedSum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
    simp [weight, beta, InterpolationMatrix.exponentVector, mul_comm]
  · intro a
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (Nat.cast_nonneg _)
  · rw [lowCount, Finset.card_pos]
    refine ⟨0, ?_⟩
    rw [S39TE.mem_rws hw]
    simp; positivity
  · norm_cast
    rw [lowCount]
    apply Finset.card_le_card_of_injOn (fun a : Transverse q H => (⇑a.1 : Fin m → ℕ))
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
      simp only [Finset.mem_coe]
      rw [S39TE.mem_rws hw]
      exact ha
    · intro a _ b _ hab
      exact Subtype.ext (DFunLike.coe_injective hab)
  · intro selection
    exact S39TE.det_expand _ (fun r t => scalar F p q r t)
      (fun r t c => PowerSeries.coeff (r.2.1 0 - (t.2.2 : ℕ))
          ((periodMonomial r.1.val ((selection c).1 0)
            (fun i => (selection c).1 i.succ)).coeff t.1.1))
      (fun r c => S39TE.entry_expansion K w0 v theta F H p q hw0 hq selection r c)
