-- Prove2me | solution 1 for LLLFactor.Factors.prop_2_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T21:59:38.725535+00:00
-- url     : https://prove2.me/submissions/3514679f-50e5-4557-967e-e0dce718cb77

import Definitions.Def_LLLFactor_Factors_Setting
import Theorems.Thm_LLLFactor_Factors_prop_2_5
import Theorems.Thm_LLLFactor_Factors_claim_2_11

open Polynomial Finset Matrix LLLFactor.Factors
open scoped nonZeroDivisors

namespace Prop27Proof
noncomputable section

lemma polyNorm_nonneg (f : ℤ[X]) : 0 ≤ polyNorm f := Real.sqrt_nonneg _

lemma polyNorm_sq (f : ℤ[X]) :
    polyNorm f ^ 2 = ∑ i ∈ f.support, (f.coeff i : ℝ) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma sum_coeff_sq_le (f : ℤ[X]) (s : Finset ℕ) :
    (∑ i ∈ s, (f.coeff i : ℝ) ^ 2) ≤ polyNorm f ^ 2 := by
  rw [polyNorm_sq]
  calc
    _ ≤ ∑ i ∈ f.support ∪ s, (f.coeff i : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (by intros; positivity)
    _ = _ := (Finset.sum_subset Finset.subset_union_left (by
      intro i _ hi
      simp [Polynomial.notMem_support_iff.mp hi])).symm

lemma one_le_polyNorm {f : ℤ[X]} (hf : f ≠ 0) : 1 ≤ polyNorm f := by
  have hc : (1 : ℝ) ≤ |(f.leadingCoeff : ℝ)| := by
    exact_mod_cast (Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hf))
  have hs := sum_coeff_sq_le f {f.natDegree}
  simp only [Finset.sum_singleton, coeff_natDegree] at hs
  have hn := polyNorm_nonneg f
  nlinarith [sq_abs (f.leadingCoeff : ℝ)]

lemma polyNorm_X_pow_mul (f : ℤ[X]) (k : ℕ) : polyNorm (X ^ k * f) = polyNorm f := by
  have hs : (X ^ k * f).support = f.support.image (fun i => i + k) := by
    ext i
    constructor
    · intro hi
      have hn := Polynomial.mem_support_iff.mp hi
      rw [Polynomial.coeff_X_pow_mul'] at hn
      have hk : k ≤ i := by by_contra h; simp [h] at hn
      rw [if_pos hk] at hn
      exact Finset.mem_image.mpr ⟨i - k, Polynomial.mem_support_iff.mpr hn, by omega⟩
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      simpa only [Polynomial.mem_support_iff, Polynomial.coeff_X_pow_mul] using hj
  unfold polyNorm
  rw [hs, Finset.sum_image]
  · simp only [Polynomial.coeff_X_pow_mul]
  · intro i _ j _ hij
    exact Nat.add_right_cancel hij

lemma modPk_surjective (q : ℕ) : Function.Surjective (modPk q) :=
  Polynomial.map_surjective _ ZMod.intCast_surjective

lemma modPk_eq_zero_iff (q : ℕ) (f : ℤ[X]) :
    modPk q f = 0 ↔ C (q : ℤ) ∣ f := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro hf i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (f.coeff i) q).mp
    have hi := congrArg (fun g : (ZMod q)[X] => g.coeff i) hf
    simpa [modPk] using hi
  · intro hf
    ext i
    simpa [modPk] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (f.coeff i) q).mpr (hf i)

lemma coprime_mod_prime_power {p k : ℕ} {h g : ℤ[X]}
    (hc : IsCoprime (modPk p h) (modPk p g)) :
    IsCoprime (modPk (p ^ k) h) (modPk (p ^ k) g) := by
  obtain ⟨a, c, hac⟩ := hc
  obtain ⟨A, rfl⟩ := modPk_surjective p a
  obtain ⟨C', rfl⟩ := modPk_surjective p c
  have hz : modPk p (1 - (A * h + C' * g)) = 0 := by
    simpa [modPk, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul] using
      sub_eq_zero.mpr hac.symm
  obtain ⟨V, hV⟩ := (modPk_eq_zero_iff p _).mp hz
  let R := (ZMod (p ^ k))[X]
  let v : R := Polynomial.C (p : ZMod (p ^ k)) * modPk (p ^ k) V
  have hv : v ^ k = 0 := by
    dsimp [v]
    rw [mul_pow, ← map_pow]
    have hp : (p : ZMod (p ^ k)) ^ k = 0 := by
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self (p ^ k)
    rw [hp, map_zero, zero_mul]
  have he : modPk (p ^ k) A * modPk (p ^ k) h +
      modPk (p ^ k) C' * modPk (p ^ k) g = 1 - v := by
    have ht := congrArg (modPk (p ^ k)) hV
    simp only [modPk, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_add,
      Polynomial.map_mul, map_natCast, Polynomial.map_natCast] at ht
    dsimp [v, modPk]
    simp only [map_natCast]
    linear_combination -ht
  refine ⟨(∑ i ∈ Finset.range k, v ^ i) * modPk (p ^ k) A,
    (∑ i ∈ Finset.range k, v ^ i) * modPk (p ^ k) C', ?_⟩
  calc
    _ = (∑ i ∈ Finset.range k, v ^ i) *
        (modPk (p ^ k) A * modPk (p ^ k) h +
          modPk (p ^ k) C' * modPk (p ^ k) g) := by ring
    _ = 1 := by rw [he, geom_sum_mul_neg, hv, sub_zero]

lemma cancel_mod_prime_power {p k : ℕ} {h g u : ℤ[X]}
    (hc : IsCoprime (modPk p h) (modPk p g))
    (hd : modPk (p ^ k) h ∣ modPk (p ^ k) (g * u)) :
    modPk (p ^ k) h ∣ modPk (p ^ k) u := by
  apply (coprime_mod_prime_power (k := k) hc).dvd_of_dvd_mul_left
  simpa [modPk, Polynomial.map_mul] using hd

lemma primitive_integer_associate {q : ℚ[X]} (hq : q ≠ 0) :
    ∃ g : ℤ[X], g.IsPrimitive ∧ Associated (g.map (Int.castRingHom ℚ)) q := by
  let P : ℤ[X] := IsLocalization.integerNormalization ℤ⁰ q
  have hP : P ≠ 0 := by
    exact mt IsFractionRing.integerNormalization_eq_zero_iff.mp hq
  obtain ⟨c, hc, he⟩ := IsLocalization.integerNormalization_spec ℤ⁰ q
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  have he' : P.map (Int.castRingHom ℚ) = C (c : ℚ) * q := by
    simpa [P, Algebra.smul_def, Polynomial.algebraMap_apply] using he
  have hu : IsUnit (C (c : ℚ) : ℚ[X]) := by
    exact (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hc0)).map C
  have hcontent : P.content ≠ 0 := by
    intro hc
    exact hP (content_eq_zero_iff.mp hc)
  have hv : IsUnit (C (P.content : ℚ) : ℚ[X]) :=
    (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hcontent)).map C
  have hp : Associated (P.map (Int.castRingHom ℚ))
      (P.primPart.map (Int.castRingHom ℚ)) := by
    conv_lhs => rw [P.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
    exact associated_unit_mul_left _ _ hv
  refine ⟨P.primPart, P.isPrimitive_primPart, hp.symm.trans ?_⟩
  rw [he']
  exact associated_unit_mul_left _ _ hu

lemma exists_integer_gcd_quotients {f b : ℤ[X]} (hf : f ≠ 0) :
    ∃ g F B : ℤ[X], g ≠ 0 ∧ f = g * F ∧ b = g * B ∧
      IsCoprime (F.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) := by
  let fq := f.map (Int.castRingHom ℚ)
  let bq := b.map (Int.castRingHom ℚ)
  have hfq : fq ≠ 0 := by
    intro he
    apply hf
    exact (Polynomial.map_injective _ Int.cast_injective) (by simpa [fq] using he)
  let D := GCDMonoid.gcd fq bq
  have hD : D ≠ 0 := gcd_ne_zero_of_left hfq
  obtain ⟨g, hg, ha⟩ := primitive_integer_associate hD
  have hgf : g ∣ f := by
    apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast g f hg).mpr
    exact ha.dvd.trans (gcd_dvd_left fq bq)
  have hgb : g ∣ b := by
    apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast g b hg).mpr
    exact ha.dvd.trans (gcd_dvd_right fq bq)
  obtain ⟨F, hF⟩ := hgf
  obtain ⟨B, hB⟩ := hgb
  refine ⟨g, F, B, hg.ne_zero, hF, hB, ?_⟩
  obtain ⟨u, hu⟩ := ha
  obtain ⟨a, c, hac⟩ := exists_gcd_eq_mul_add_mul fq bq
  have hgq : g.map (Int.castRingHom ℚ) ≠ 0 := by
    exact fun he => hg.ne_zero ((Polynomial.map_injective _ Int.cast_injective)
      (by simpa using he))
  have hlin : a * F.map (Int.castRingHom ℚ) + c * B.map (Int.castRingHom ℚ) = u := by
    apply mul_left_cancel₀ hgq
    calc
      _ = fq * a + bq * c := by
        dsimp [fq, bq]
        rw [hF, hB, Polynomial.map_mul, Polynomial.map_mul]
        ring
      _ = D := hac.symm
      _ = _ := hu.symm
  refine ⟨(↑(u⁻¹) : ℚ[X]) * a, (↑(u⁻¹) : ℚ[X]) * c, ?_⟩
  calc
    _ = (↑(u⁻¹) : ℚ[X]) *
        (a * F.map (Int.castRingHom ℚ) + c * B.map (Int.castRingHom ℚ)) := by ring
    _ = 1 := by rw [hlin]; exact u.inv_mul

lemma pow_dvd_det_of_rows {l r : ℕ} (q : ℤ)
    (M : Matrix (Fin (l + r)) (Fin (l + r)) ℤ)
    (hrow : ∀ i : Fin (l + r), (i : ℕ) < l → ∀ j, q ∣ M i j) :
    q ^ l ∣ M.det := by
  classical
  let d : Fin (l + r) → ℤ := fun i => if (i : ℕ) < l then q else 1
  have hd : ∀ i j, d i ∣ M i j := by
    intro i j
    dsimp [d]
    split_ifs with hi
    · exact hrow i hi j
    · exact one_dvd _
  choose C hC using hd
  have he : M = diagonal d * Matrix.of C := by
    ext i j
    simpa only [diagonal_mul, Matrix.of_apply] using hC i j
  have hp : ∏ i, d i = q ^ l := by
    rw [Fin.prod_univ_add]
    simp [d]
  rw [he, det_mul, det_diagonal, hp]
  exact dvd_mul_right _ _

def monicDivisionBasis (h : ℤ[X]) (l : ℕ) (j : ℕ) : ℤ[X] :=
  if j < l then X ^ j else X ^ (j - l) * h

lemma monicDivisionBasis_monic {h : ℤ[X]} (hh : h.Monic) (l j : ℕ) :
    (monicDivisionBasis h l j).Monic := by
  unfold monicDivisionBasis
  split_ifs
  · exact monic_X_pow _
  · exact (monic_X_pow _).mul hh

lemma monicDivisionBasis_degree {h : ℤ[X]} (hh : h.Monic) (j : ℕ) :
    (monicDivisionBasis h h.natDegree j).natDegree = j := by
  unfold monicDivisionBasis
  split_ifs with hj
  · exact natDegree_X_pow (R := ℤ) j
  · rw [natDegree_X_pow_mul _ hh.ne_zero]
    omega

def monicDivisionMatrix (h : ℤ[X]) (r : ℕ) :
    Matrix (Fin (h.natDegree + r)) (Fin (h.natDegree + r)) ℤ :=
  fun i j => (monicDivisionBasis h h.natDegree j).coeff i

lemma monicDivisionMatrix_det {h : ℤ[X]} (hh : h.Monic) (r : ℕ) :
    (monicDivisionMatrix h r).det = 1 := by
  have hu : (monicDivisionMatrix h r).IsUpperTriangular := by
    intro i j hji
    apply coeff_eq_zero_of_natDegree_lt
    rw [monicDivisionBasis_degree hh]
    exact hji
  rw [det_of_isUpperTriangular hu]
  apply Finset.prod_eq_one
  intro i _
  change (monicDivisionBasis h h.natDegree i).coeff i = 1
  simpa only [monicDivisionBasis_degree hh] using
    (monicDivisionBasis_monic hh h.natDegree i).coeff_natDegree

lemma ofFn_eq_coeff_sum (n : ℕ) (p : ℤ[X]) :
    ofFn n (fun i => p.coeff i) = ∑ i : Fin n, C (p.coeff i) * X ^ (i : ℕ) := by
  rw [ofFn_eq_sum_monomial]
  simp only [C_mul_X_pow_eq_monomial]

lemma monic_division_reconstruction {h p : ℤ[X]} (hh : h.Monic)
    (hl : 0 < h.natDegree) (r : ℕ) (hp : p.natDegree < h.natDegree + r) :
    p = ∑ j : Fin (h.natDegree + r),
      C (if (j : ℕ) < h.natDegree then (p %ₘ h).coeff j
        else (p /ₘ h).coeff ((j : ℕ) - h.natDegree)) *
      monicDivisionBasis h h.natDegree j := by
  have hr : ofFn h.natDegree (fun i => (p %ₘ h).coeff i) = p %ₘ h := by
    apply ofFn_comp_toFn_eq_id_of_natDegree_lt
    apply natDegree_modByMonic_lt p hh
    intro he
    simp [he] at hl
  have hq : ofFn r (fun i => (p /ₘ h).coeff i) = p /ₘ h := by
    by_cases hr0 : r = 0
    · subst r
      have hz : p /ₘ h = 0 := (divByMonic_eq_zero_iff hh).mpr
        (degree_lt_degree (by simpa using hp))
      simp [hz]
    · have hd : (p /ₘ h).natDegree < r := by
        rw [natDegree_divByMonic p hh]
        omega
      exact ofFn_comp_toFn_eq_id_of_natDegree_lt hd
  rw [Fin.sum_univ_add]
  have hfirst : (∑ i : Fin h.natDegree,
      C (if ((Fin.castAdd r i : Fin (h.natDegree + r)) : ℕ) < h.natDegree
        then (p %ₘ h).coeff (Fin.castAdd r i)
        else (p /ₘ h).coeff ((Fin.castAdd r i : ℕ) - h.natDegree)) *
      monicDivisionBasis h h.natDegree (Fin.castAdd r i)) = p %ₘ h := by
    simpa [monicDivisionBasis, ofFn_eq_coeff_sum] using hr
  rw [hfirst]
  have hsecond : (∑ i : Fin r,
      C (if ((Fin.natAdd h.natDegree i : Fin (h.natDegree + r)) : ℕ) < h.natDegree
        then (p %ₘ h).coeff (Fin.natAdd h.natDegree i)
        else (p /ₘ h).coeff ((Fin.natAdd h.natDegree i : ℕ) - h.natDegree)) *
      monicDivisionBasis h h.natDegree (Fin.natAdd h.natDegree i)) = h * (p /ₘ h) := by
    calc
      _ = ∑ i : Fin r, C ((p /ₘ h).coeff i) * (X ^ (i : ℕ) * h) := by
        apply Finset.sum_congr rfl
        intro i _
        have hn : ¬ h.natDegree + (i : ℕ) < h.natDegree := by omega
        simp [monicDivisionBasis, hn]
      _ = h * ofFn r (fun i => (p /ₘ h).coeff i) := by
        rw [ofFn_eq_coeff_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hq]
  rw [hsecond, modByMonic_add_div]

lemma monic_determinant_divisibility {h : ℤ[X]} (hh : h.Monic)
    (hl : 0 < h.natDegree) {d q : ℕ} (hd : h.natDegree ≤ d)
    (v : Fin d → ℤ[X]) (hv : ∀ j, (v j).natDegree < d)
    (hdiv : ∀ j, modPk q h ∣ modPk q (v j)) :
    (q : ℤ) ^ h.natDegree ∣ (Matrix.of (fun i j : Fin d => (v j).coeff i)).det := by
  classical
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hd
  let U : Matrix (Fin (h.natDegree + r)) (Fin (h.natDegree + r)) ℤ :=
    fun i j => (v j).coeff i
  let C' : Matrix (Fin (h.natDegree + r)) (Fin (h.natDegree + r)) ℤ :=
    fun i j => if (i : ℕ) < h.natDegree then ((v j) %ₘ h).coeff i
      else ((v j) /ₘ h).coeff ((i : ℕ) - h.natDegree)
  have he : U = monicDivisionMatrix h r * C' := by
    ext i j
    have hr := congrArg (fun f : ℤ[X] => f.coeff i)
      (monic_division_reconstruction hh hl r (hv j))
    simp only [finsetSum_coeff, coeff_C_mul] at hr
    change (v j).coeff i = ∑ k, monicDivisionMatrix h r i k * C' k j
    rw [hr]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [monicDivisionMatrix, C']
    ring
  have hrows : ∀ i : Fin (h.natDegree + r), (i : ℕ) < h.natDegree →
      ∀ j, (q : ℤ) ∣ C' i j := by
    intro i hi j
    dsimp [C']
    rw [if_pos hi]
    have hz : modPk q ((v j) %ₘ h) = 0 := by
      rw [modPk, map_modByMonic _ hh]
      exact (modByMonic_eq_zero_iff_dvd (hh.map _)).mpr (hdiv j)
    exact (C_dvd_iff_dvd_coeff _ _).mp ((modPk_eq_zero_iff q _).mp hz) i
  change (q : ℤ) ^ h.natDegree ∣ U.det
  rw [he, det_mul, monicDivisionMatrix_det hh, one_mul]
  exact pow_dvd_det_of_rows (q : ℤ) C' hrows

def highMultiplicationMatrix (g : ℤ[X]) (d : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => (g * X ^ (j : ℕ)).coeff (g.natDegree + i)

lemma highMultiplicationMatrix_det {g : ℤ[X]} (hg : g ≠ 0) (d : ℕ) :
    (highMultiplicationMatrix g d).det = g.leadingCoeff ^ d := by
  have hu : (highMultiplicationMatrix g d).IsUpperTriangular := by
    intro i j hji
    change (j : ℕ) < (i : ℕ) at hji
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_mul_X_pow _ hg]
    omega
  rw [det_of_isUpperTriangular hu]
  simp only [highMultiplicationMatrix, coeff_mul_X_pow, coeff_natDegree,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma projected_multiplication_matrix (g : ℤ[X]) {d : ℕ}
    (v : Fin d → ℤ[X]) (hv : ∀ j, (v j).natDegree < d) :
    (Matrix.of (fun i j : Fin d => (g * v j).coeff (g.natDegree + i))) =
      highMultiplicationMatrix g d *
        (Matrix.of (fun i j : Fin d => (v j).coeff i)) := by
  ext i j
  have hp : v j = ∑ k : Fin d, C ((v j).coeff k) * X ^ (k : ℕ) := by
    rw [← ofFn_eq_coeff_sum]
    exact (ofFn_comp_toFn_eq_id_of_natDegree_lt (hv j)).symm
  have he : g * v j = ∑ k : Fin d, C ((v j).coeff k) * (g * X ^ (k : ℕ)) := by
    nth_rw 1 [hp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hc := congrArg (fun p : ℤ[X] => p.coeff (g.natDegree + i)) he
  simp only [finsetSum_coeff, coeff_C_mul] at hc
  change (g * v j).coeff (g.natDegree + i) =
    ∑ k, highMultiplicationMatrix g d i k * (v j).coeff k
  rw [hc]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [highMultiplicationMatrix]
  ring

lemma projected_multiplication_det {g : ℤ[X]} (hg : g ≠ 0) {d : ℕ}
    (v : Fin d → ℤ[X]) (hv : ∀ j, (v j).natDegree < d) :
    (Matrix.of (fun i j : Fin d => (g * v j).coeff (g.natDegree + i))).det =
      g.leadingCoeff ^ d * (Matrix.of (fun i j : Fin d => (v j).coeff i)).det := by
  rw [projected_multiplication_matrix g v hv, det_mul, highMultiplicationMatrix_det hg]

def shiftedColumns (F B : ℤ[X]) : Fin (B.natDegree + F.natDegree) → ℤ[X] :=
  Fin.addCases (fun i : Fin B.natDegree => X ^ (i : ℕ) * F)
    (fun i : Fin F.natDegree => X ^ (i : ℕ) * B)

lemma shiftedColumns_degree {F B : ℤ[X]} (hF : F ≠ 0) (hB : B ≠ 0)
    (j : Fin (B.natDegree + F.natDegree)) :
    (shiftedColumns F B j).natDegree < B.natDegree + F.natDegree := by
  induction j using Fin.addCases
  · simp only [shiftedColumns, Fin.addCases_left, natDegree_X_pow_mul _ hF]
    omega
  · simp only [shiftedColumns, Fin.addCases_right, natDegree_X_pow_mul _ hB]
    omega

lemma shifted_coeff_formula (F : ℤ[X]) (s i : ℕ) :
    (X ^ s * F).coeff i =
      if i ∈ Set.Icc s (s + F.natDegree) then F.coeff (i - s) else 0 := by
  rw [coeff_X_pow_mul']
  by_cases hsi : s ≤ i
  · rw [if_pos hsi]
    by_cases hi : i ≤ s + F.natDegree
    · rw [if_pos ⟨hsi, hi⟩]
    · rw [if_neg (by simp [Set.mem_Icc, hi])]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [if_neg hsi, if_neg (by simp [Set.mem_Icc, hsi])]

lemma shiftedColumns_matrix (F B : ℤ[X]) :
    (Matrix.of (fun i j : Fin (B.natDegree + F.natDegree) => (shiftedColumns F B j).coeff i)) =
      sylvester B F B.natDegree F.natDegree := by
  ext i j
  induction j using Fin.addCases
  · simpa only [shiftedColumns, sylvester, Matrix.of_apply, Fin.addCases_left] using
      shifted_coeff_formula F _ _
  · simpa only [shiftedColumns, sylvester, Matrix.of_apply, Fin.addCases_right] using
      shifted_coeff_formula B _ _

lemma shiftedColumns_det_ne_zero {F B : ℤ[X]}
    (hc : IsCoprime (F.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))) :
    (Matrix.of (fun i j : Fin (B.natDegree + F.natDegree) => (shiftedColumns F B j).coeff i)).det ≠ 0 := by
  rw [shiftedColumns_matrix]
  change resultant B F ≠ 0
  intro hz
  apply resultant_ne_zero _ _ hc.symm
  simp only [natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int,
    resultant_map_map, hz, map_zero]

lemma abs_det_le_prod_euclidean_columns {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ j, ‖(WithLp.toLp 2 (fun i => A i j) : EuclideanSpace ℝ (Fin n))‖ := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)
  let o := e.toBasis.orientation
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have hb := o.abs_volumeForm_apply_le v
  rw [o.volumeForm_robust' e, Module.Basis.det_apply] at hb
  have he : e.toBasis.toMatrix v = A := by ext i j; rfl
  rw [he] at hb
  exact hb

lemma norm_projected_coefficients_le (f : ℤ[X]) (n e : ℕ) :
    ‖(WithLp.toLp 2 (fun i : Fin n => (f.coeff (e + i) : ℝ)) :
      EuclideanSpace ℝ (Fin n))‖ ≤ polyNorm f := by
  apply (sq_le_sq₀ (norm_nonneg _) (polyNorm_nonneg f)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin n, (f.coeff (e + i) : ℝ) ^ 2) ≤ _
  have hs := sum_coeff_sq_le f (Finset.univ.image (fun i : Fin n => e + (i : ℕ)))
  rw [Finset.sum_image] at hs
  · exact hs
  · intro i _ j _ hij
    apply Fin.ext
    exact Nat.add_left_cancel hij

lemma abs_projected_det_le {n : ℕ} (v : Fin n → ℤ[X]) (e : ℕ) :
    |((Matrix.of (fun i j : Fin n => (v j).coeff (e + i))).det : ℝ)| ≤
      ∏ j, polyNorm (v j) := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => ((v j).coeff (e + i) : ℝ)
  have hd := abs_det_le_prod_euclidean_columns A
  have he : A.det = ((Matrix.of (fun i j : Fin n => (v j).coeff (e + i))).det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) _).symm
  rw [he] at hd
  apply hd.trans
  apply Finset.prod_le_prod
  · intro i _
    exact norm_nonneg _
  · intro i _
    exact norm_projected_coefficients_le (v i) n e

lemma setting_mod_f_ne_zero {p k : ℕ} {f h : ℤ[X]} (hS : IsSetting p k f h) :
    modPk p f ≠ 0 := by
  intro hf
  exact hS.sq_not_dvd_mod_p (hf ▸ dvd_zero _)

lemma setting_h_degree_pos {p k : ℕ} {f h : ℤ[X]} (hS : IsSetting p k f h) :
    0 < h.natDegree := by
  apply hS.monic.natDegree_pos.mpr
  intro he
  apply hS.irreducible_mod_p.not_isUnit
  simp [he, modPk]

lemma degree_h_le_quotient {p k : ℕ} {f h h0 g F : ℤ[X]}
    (hS : IsSetting p k f h) (hh0 : IsH0 p f h h0)
    (hf : f = g * F) (hn : ¬ modPk p h ∣ modPk p g) : h.natDegree ≤ F.natDegree := by
  let : Fact p.Prime := ⟨hS.prime⟩
  have hcop := hS.irreducible_mod_p.coprime_iff_not_dvd.mpr hn
  have hdf : modPk p h ∣ modPk p f :=
    hh0.2.2.trans (Polynomial.map_dvd (Int.castRingHom (ZMod p)) hh0.2.1)
  have hdF : modPk p h ∣ modPk p F := by
    apply hcop.dvd_of_dvd_mul_left
    simpa [hf, modPk, Polynomial.map_mul] using hdf
  have hF : modPk p F ≠ 0 := by
    intro hz
    apply setting_mod_f_ne_zero hS
    simp [hf, modPk, Polynomial.map_mul, show F.map (Int.castRingHom (ZMod p)) = 0 from hz]
  have hdeg := natDegree_le_of_dvd hdF hF
  rw [modPk, hS.monic.natDegree_map] at hdeg
  exact hdeg.trans natDegree_map_le

lemma nat_le_abs_of_dvd_int {q : ℕ} {z : ℤ} (hd : (q : ℤ) ∣ z) (hz : z ≠ 0) :
    (q : ℝ) ≤ |(z : ℝ)| := by
  obtain ⟨c, hc⟩ := hd
  have hc0 : c ≠ 0 := by
    intro he
    apply hz
    simpa [he] using hc
  have habs : (1 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast Int.one_le_abs hc0
  rw [hc, Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
  nlinarith [Nat.cast_nonneg q (α := ℝ)]

lemma prod_norm_mul_shiftedColumns (g F B : ℤ[X]) :
    (∏ j, polyNorm (g * shiftedColumns F B j)) =
      polyNorm (g * F) ^ B.natDegree * polyNorm (g * B) ^ F.natDegree := by
  rw [Fin.prod_univ_add]
  have hleft : (∏ i : Fin B.natDegree,
      polyNorm (g * shiftedColumns F B (Fin.castAdd F.natDegree i))) =
      polyNorm (g * F) ^ B.natDegree := by
    simp only [shiftedColumns, Fin.addCases_left]
    have he : ∀ i : Fin B.natDegree, g * (X ^ (i : ℕ) * F) = X ^ (i : ℕ) * (g * F) :=
      fun _ => by ring
    simp only [he, polyNorm_X_pow_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hright : (∏ i : Fin F.natDegree,
      polyNorm (g * shiftedColumns F B (Fin.natAdd B.natDegree i))) =
      polyNorm (g * B) ^ F.natDegree := by
    simp only [shiftedColumns, Fin.addCases_right]
    have he : ∀ i : Fin F.natDegree, g * (X ^ (i : ℕ) * B) = X ^ (i : ℕ) * (g * B) :=
      fun _ => by ring
    simp only [he, polyNorm_X_pow_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hleft, hright]

lemma determinant_short_vector_bound {p k : ℕ} {f h h0 g F B : ℤ[X]}
    (hS : IsSetting p k f h) (hh0 : IsH0 p f h h0)
    (hg : g ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hf : f = g * F)
    (hc : IsCoprime (F.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)))
    (hdB : modPk (p ^ k) h ∣ modPk (p ^ k) (g * B))
    (hn : ¬ modPk p h ∣ modPk p g) :
    (p : ℝ) ^ (k * h.natDegree) ≤
      polyNorm f ^ B.natDegree * polyNorm (g * B) ^ F.natDegree := by
  classical
  let : Fact p.Prime := ⟨hS.prime⟩
  let v := shiftedColumns F B
  let d := B.natDegree + F.natDegree
  have hcop := hS.irreducible_mod_p.coprime_iff_not_dvd.mpr hn
  have hdF : modPk (p ^ k) h ∣ modPk (p ^ k) F :=
    cancel_mod_prime_power hcop (hf ▸ hS.dvd_mod_pk)
  have hdB' : modPk (p ^ k) h ∣ modPk (p ^ k) B := cancel_mod_prime_power hcop hdB
  have hv : ∀ j : Fin d, (v j).natDegree < d := shiftedColumns_degree hF hB
  have hdiv : ∀ j : Fin d, modPk (p ^ k) h ∣ modPk (p ^ k) (v j) := by
    intro j
    induction j using Fin.addCases
    · rename_i i
      simpa only [v, shiftedColumns, Fin.addCases_left, modPk, Polynomial.map_mul] using
        dvd_mul_of_dvd_right hdF (modPk (p ^ k) (X ^ (i : ℕ)))
    · rename_i i
      simpa only [v, shiftedColumns, Fin.addCases_right, modPk, Polynomial.map_mul] using
        dvd_mul_of_dvd_right hdB' (modPk (p ^ k) (X ^ (i : ℕ)))
  have hld : h.natDegree ≤ d := (degree_h_le_quotient hS hh0 hf hn).trans (by dsimp [d]; omega)
  let U : Matrix (Fin d) (Fin d) ℤ := Matrix.of (fun i j => (v j).coeff i)
  let V : Matrix (Fin d) (Fin d) ℤ := Matrix.of (fun i j => (g * v j).coeff (g.natDegree + i))
  have hU : U.det ≠ 0 := shiftedColumns_det_ne_zero hc
  have hUd' : ((p ^ k : ℕ) ^ h.natDegree : ℤ) ∣ U.det := by
    simpa only [Nat.cast_pow] using
      monic_determinant_divisibility hS.monic (setting_h_degree_pos hS) hld v hv hdiv
  have he : V.det = g.leadingCoeff ^ d * U.det := projected_multiplication_det hg v hv
  have hV : V.det ≠ 0 := by
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hg)) hU
  have hVd : ((p ^ k : ℕ) ^ h.natDegree : ℤ) ∣ V.det := by
    rw [he]
    exact dvd_mul_of_dvd_right hUd' _
  have hlow := nat_le_abs_of_dvd_int hVd hV
  have hupp := abs_projected_det_le (fun j => g * v j) g.natDegree
  have hnorm := prod_norm_mul_shiftedColumns g F B
  rw [← hf] at hnorm
  rw [show (∏ j : Fin d, polyNorm (g * v j)) =
      polyNorm f ^ B.natDegree * polyNorm (g * B) ^ F.natDegree from hnorm] at hupp
  have hcst : (((p ^ k : ℕ) ^ h.natDegree : ℕ) : ℝ) = (p : ℝ) ^ (k * h.natDegree) := by
    simp only [Nat.cast_pow, ← pow_mul]
  rw [hcst] at hlow
  exact hlow.trans hupp

end
end Prop27Proof

theorem solution {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (_hm : h.natDegree ≤ m) (h₀ : ℤ[X]) (hh₀ : IsH0 p f h h₀)
    (b : ℤ[X]) (hbL : b ∈ latticeL p k h m)
    (h28 : polyNorm f ^ m * polyNorm b ^ f.natDegree < (p : ℝ) ^ (k * h.natDegree)) :
    h₀ ∣ b ∧ ∃ d : ℤ[X], d ∣ f ∧ d ∣ b ∧ ¬ IsUnit d := by
  have hdvd : h₀ ∣ b := by
    by_cases hb0 : b = 0
    · simp [hb0]
    have hf0 : f ≠ 0 := by
      intro he
      have hd := hS.deg_f_pos
      simp [he] at hd
    obtain ⟨g, F, B, hg, hF, hB, hc⟩ := Prop27Proof.exists_integer_gcd_quotients (b := b) hf0
    have hF0 : F ≠ 0 := by
      intro he
      apply hf0
      simp [hF, he]
    have hB0 : B ≠ 0 := by
      intro he
      apply hb0
      simp [hB, he]
    have hhg : modPk p h ∣ modPk p g := by
      by_contra hn
      have hlow := Prop27Proof.determinant_short_vector_bound hS hh₀ hg hF0 hB0 hF hc
        (hB ▸ hbL.2) hn
      rw [← hB] at hlow
      have hdegF : F.natDegree ≤ f.natDegree := by
        rw [hF, natDegree_mul hg hF0]
        omega
      have hdegB : B.natDegree ≤ m := by
        have hd := hbL.1
        rw [hB, natDegree_mul hg hB0] at hd
        omega
      have hupp : polyNorm f ^ B.natDegree * polyNorm b ^ F.natDegree ≤
          polyNorm f ^ m * polyNorm b ^ f.natDegree :=
        mul_le_mul (pow_le_pow_right₀ (Prop27Proof.one_le_polyNorm hf0) hdegB)
          (pow_le_pow_right₀ (Prop27Proof.one_le_polyNorm hb0) hdegF)
          (pow_nonneg (Prop27Proof.polyNorm_nonneg b) _)
          (pow_nonneg (Prop27Proof.polyNorm_nonneg f) _)
      exact (not_lt_of_ge (hlow.trans hupp)) h28
    have h25 := (prop_2_5 f h hS).2.2.1 h₀ hh₀ g ⟨F, hF⟩
    exact (h25.2.mp (h25.1.mp hhg)).trans ⟨B, hB⟩
  exact ⟨hdvd, h₀, hh₀.2.1, hdvd, hh₀.1.not_isUnit⟩
