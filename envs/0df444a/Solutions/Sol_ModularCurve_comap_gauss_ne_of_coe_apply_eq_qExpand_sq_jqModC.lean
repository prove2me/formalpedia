-- Prove2me | solution 1 for ModularCurve.comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f95d0234-ad6f-5f3b-afe0-5e9f07aa7ffc

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC

set_option autoImplicit false

namespace OneWitnessAux

open PowerSeries

theorem coeff_pow_char {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (f : PowerSeries R) (m : ℕ) :
    coeff m (f ^ p) = if p ∣ m then (coeff (m / p) f) ^ p else 0 := by
  haveI : CharP (PowerSeries R) p := charP_of_injective_ringHom (C_injective (R := R)) p
  induction m using Nat.strong_induction_on generalizing f with
  | _ m ih =>

    set g : PowerSeries R := mk fun n => coeff (n + 1) f with hg
    have hf : f = X * g + C (constantCoeff f) := by rw [hg]; exact eq_X_mul_shift_add_const f
    have hpow : f ^ p = X ^ p * g ^ p + C ((constantCoeff f) ^ p) := by
      nth_rewrite 1 [hf]
      rw [add_pow_char, mul_pow, map_pow]
    rw [hpow, map_add, coeff_X_pow_mul', coeff_C]
    by_cases hpm : p ≤ m
    · rw [if_pos hpm, ih (m - p) (Nat.sub_lt (le_trans hp.out.pos hpm |> fun h => Nat.lt_of_lt_of_le hp.out.pos hpm) hp.out.pos) g]
      have hm0 : m ≠ 0 := by have := hp.out.pos; omega
      rw [if_neg hm0, add_zero]
      by_cases hdvd : p ∣ m
      · have hdvd' : p ∣ m - p := Nat.dvd_sub hdvd (dvd_refl p)
        rw [if_pos hdvd', if_pos hdvd]
        have hq : (m - p) / p + 1 = m / p := by
          obtain ⟨k, rfl⟩ := hdvd
          have hk : 1 ≤ k := by
            rcases k with _ | k
            · simp at hpm; have := hp.out.pos; omega
            · omega
          rw [show p * k - p = p * (k - 1) by rw [Nat.mul_sub_one], Nat.mul_div_cancel_left _ hp.out.pos,
            Nat.mul_div_cancel_left _ hp.out.pos]
          omega
        rw [← hq, hg, coeff_mk]
      · have hdvd' : ¬ p ∣ m - p := fun h => hdvd (by
          have := Nat.dvd_add h (dvd_refl p); rwa [Nat.sub_add_cancel hpm] at this)
        rw [if_neg hdvd', if_neg hdvd]
    · push_neg at hpm
      rw [if_neg (not_le.mpr hpm), zero_add]
      by_cases hm0 : m = 0
      · subst hm0
        simp only [if_true, dvd_zero, Nat.zero_div, ← coeff_zero_eq_constantCoeff_apply]
      · rw [if_neg hm0, if_neg]
        intro h
        exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h) (not_le.mpr hpm)

theorem coeff_pow_char_sq {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (f : PowerSeries R) (m : ℕ) :
    coeff m (f ^ (p * p)) = if p * p ∣ m then (coeff (m / (p * p)) f) ^ (p * p) else 0 := by
  rw [pow_mul, coeff_pow_char p (f ^ p) m]
  by_cases h1 : p ∣ m
  · rw [if_pos h1, coeff_pow_char p f (m / p)]
    by_cases h2 : p ∣ m / p
    · have h12 : p * p ∣ m := by
        obtain ⟨a, rfl⟩ := h1; rw [Nat.mul_div_cancel_left _ hp.out.pos] at h2
        exact Nat.mul_dvd_mul_left p h2
      rw [if_pos h2, if_pos h12, ← pow_mul, Nat.div_div_eq_div_mul]
    · have h12 : ¬ p * p ∣ m := by
        rintro ⟨a, rfl⟩; apply h2
        rw [mul_assoc, Nat.mul_div_cancel_left _ hp.out.pos]; exact dvd_mul_right p a
      rw [if_neg h2, if_neg h12, zero_pow hp.out.ne_zero]
  · have h12 : ¬ p * p ∣ m := fun h => h1 (dvd_trans (dvd_mul_right p p) h)
    rw [if_neg h1, if_neg h12]

noncomputable def expandPS {R : Type*} [CommRing R] (N : ℕ) (f : PowerSeries R) : PowerSeries R :=
  mk fun n => if N ∣ n then coeff (n / N) f else 0

theorem coeff_expandPS {R : Type*} [CommRing R] (N : ℕ) (f : PowerSeries R) (n : ℕ) :
    coeff n (expandPS N f) = if N ∣ n then coeff (n / N) f else 0 := by
  rw [expandPS, coeff_mk]

theorem map_expandPS {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (N : ℕ) (f : PowerSeries R) :
    (expandPS N f).map g = expandPS N (f.map g) := by
  ext n; simp only [coeff_map, coeff_expandPS]; split_ifs <;> simp

theorem ofPowerSeries_coeff_neg {R : Type*} [CommRing R] (g : PowerSeries R) (k : ℤ) (hk : k < 0) :
    (HahnSeries.ofPowerSeries ℤ R g).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨n, hn⟩
  have : (n : ℤ) = k := hn
  omega

theorem ofPowerSeries_expandPS {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : PowerSeries R) :
    HahnSeries.ofPowerSeries ℤ R (expandPS N f) = ModularCurve.qExpand R N (HahnSeries.ofPowerSeries ℤ R f) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.qExpand_coeff_mul]
    rcases le_or_gt 0 m with hm | hm
    · lift m to ℕ using hm with m
      have : ((N : ℤ) * (m : ℤ)) = ((N * m : ℕ) : ℤ) := by push_cast; ring
      rw [this, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, coeff_expandPS,
        if_pos (dvd_mul_right N m), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))]
    · rw [ofPowerSeries_coeff_neg _ _ hm, ofPowerSeries_coeff_neg _ _ (by
        have : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
        nlinarith)]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd _ _ hk]
    rcases le_or_gt 0 k with h0 | h0
    · lift k to ℕ using h0 with k
      rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_expandPS, if_neg]
      intro h; exact hk (by exact_mod_cast h)
    · rw [ofPowerSeries_coeff_neg _ _ h0]

end OneWitnessAux

open OneWitnessAux PowerSeries in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (φ : ↥K ≃ₐ[L] ↥K)
    (j : ↥K) (hj : (j : LaurentSeries L) = ModularCurve.jqModC L)
    (hφj : ((φ j : ↥K) : LaurentSeries L) = ModularCurve.qExpand L (q ^ 2) (ModularCurve.jqModC L)) :
    W₀.comap φ.toAlgHom.toRingHom ≠ W₀ := by
  classical
  intro hfix
  haveI hq : Fact q.Prime := inferInstance
  have hq1 : 1 < q := hq.out.one_lt
  have hqq1 : 1 < q ^ 2 := by nlinarith
  have hsq : q ^ 2 = q * q := sq q

  set ι : A →+* L := algebraMap A L with hιdef
  have hι : Function.Injective ι := by rw [hιdef]; exact IsFractionRing.injective A L
  set res : A →+* IsLocalRing.ResidueField A := IsLocalRing.residue A with hres

  haveI : CharP (IsLocalRing.ResidueField A) q := by
    have h0 : (q : IsLocalRing.ResidueField A) = 0 := by
      rw [← map_natCast res, hres, IsLocalRing.residue_eq_zero_iff]; exact hAq
    exact (CharP.charP_iff_prime_eq_zero hq.out).mpr h0

  set E : PowerSeries A →+* LaurentSeries L := (HahnSeries.ofPowerSeries ℤ L).comp (PowerSeries.map ι) with hE
  have hEapp : ∀ a, E a = HahnSeries.ofPowerSeries ℤ L (a.map ι) := fun a => by rw [hE]; rfl
  have hEinj : Function.Injective E := by
    intro a b h
    rw [hEapp, hEapp] at h
    exact PowerSeries.map_injective ι hι (HahnSeries.ofPowerSeries_injective h)
  have hW : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map res ≠ 0 ∧ (f : LaurentSeries L) * E y = E x := by
    intro f; rw [hW₀ f]; simp only [hEapp]

  have hmem : ∀ g : ↥K, g ∈ W₀ ↔ φ g ∈ W₀ := by
    intro g
    have := (ValuationSubring.mem_comap (A := W₀) (f := φ.toAlgHom.toRingHom) (x := g))
    rw [hfix] at this
    exact this

  have hN_of_small : ∀ f : ↥K, (∃ x y : PowerSeries A, y.map res ≠ 0 ∧ x.map res = 0 ∧
      (f : LaurentSeries L) * E y = E x) → (f = 0 ∨ f⁻¹ ∉ W₀) := by
    rintro f ⟨x, y, hy, hx, hf⟩
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    right
    intro hinv
    obtain ⟨x', y', hy', hf'⟩ := (hW _).mp hinv
    have hff : (f : LaurentSeries L) * ((f⁻¹ : ↥K) : LaurentSeries L) = 1 := by
      rw [← IntermediateField.coe_mul, mul_inv_cancel₀ hf0]; rfl
    have hprod : E (y * y') = E (x * x') := by
      rw [map_mul, map_mul, ← hf, ← hf']
      calc E y * E y' = ((f : LaurentSeries L) * ((f⁻¹ : ↥K) : LaurentSeries L)) * (E y * E y') := by
              rw [hff, one_mul]
        _ = (f : LaurentSeries L) * E y * (((f⁻¹ : ↥K) : LaurentSeries L) * E y') := by ring
    have hyy : y * y' = x * x' := hEinj hprod
    have := congrArg (PowerSeries.map res) hyy
    rw [map_mul, map_mul, hx, zero_mul] at this
    exact mul_ne_zero hy hy' this

  have hsmall_of_N : ∀ f : ↥K, f ∈ W₀ → (f = 0 ∨ f⁻¹ ∉ W₀) →
      ∃ x y : PowerSeries A, y.map res ≠ 0 ∧ x.map res = 0 ∧ (f : LaurentSeries L) * E y = E x := by
    intro f hfW hN
    obtain ⟨x, y, hy, hf⟩ := (hW _).mp hfW
    by_cases hx : x.map res = 0
    · exact ⟨x, y, hy, hx, hf⟩
    exfalso
    have hf0 : f ≠ 0 := by
      rintro rfl
      apply hx
      have h0 : E x = 0 := by rw [← hf]; simp
      have : x = 0 := hEinj (by rw [h0, map_zero])
      rw [this, map_zero]
    rcases hN with h | h
    · exact hf0 h
    · apply h
      rw [hW]
      refine ⟨y, x, hx, ?_⟩
      have hff : ((f⁻¹ : ↥K) : LaurentSeries L) * (f : LaurentSeries L) = 1 := by
        rw [← IntermediateField.coe_mul, inv_mul_cancel₀ hf0]; rfl
      calc ((f⁻¹ : ↥K) : LaurentSeries L) * E x = ((f⁻¹ : ↥K) : LaurentSeries L) * ((f : LaurentSeries L) * E y) := by
              rw [hf]
        _ = E y := by rw [← mul_assoc, hff, one_mul]

  set PA : PowerSeries A := ModularCurve.jNum.map (Int.castRingHom A) with hPA
  have hmapmap : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
      (a : PowerSeries R), (a.map f).map g = a.map (g.comp f) := by
    intro R S T _ _ _ f g a
    rw [PowerSeries.map_comp]; rfl
  have hcompZ : ι.comp (Int.castRingHom A) = Int.castRingHom L := RingHom.ext_int _ _
  have hPL : PA.map ι = ModularCurve.jNum.map (Int.castRingHom L) := by
    rw [hPA, hmapmap, hcompZ]
  have hEX : E X = HahnSeries.single (1 : ℤ) 1 := by
    rw [hEapp]; simp only [PowerSeries.map_X]; exact HahnSeries.ofPowerSeries_X
  have hEXpow : ∀ n : ℕ, E (X ^ n) = HahnSeries.single (n : ℤ) 1 := by
    intro n; rw [map_pow, hEX, HahnSeries.single_pow]; simp
  have hjq : ModularCurve.jqModC L = HahnSeries.single (-1 : ℤ) 1 * E PA := by
    rw [hEapp, hPL]; rfl
  have hEPA : E PA = HahnSeries.single (1 : ℤ) 1 * ModularCurve.jqModC L := by
    rw [hjq, ← mul_assoc, HahnSeries.single_mul_single]; simp

  have hjW : j ∈ W₀ := by
    rw [hW]
    refine ⟨PA, X, ?_, ?_⟩
    · rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero
    · rw [hj, hEX, hEPA, mul_comm]

  set w : ↥K := φ.symm j with hw
  have hφw : φ w = j := by rw [hw]; exact φ.apply_symm_apply j
  have hwW : w ∈ W₀ := by rw [hmem, hφw]; exact hjW
  set D : ↥K := w ^ (q ^ 2) - j with hD
  have hφD : ((φ D : ↥K) : LaurentSeries L) =
      ModularCurve.jqModC L ^ (q ^ 2) - ModularCurve.qExpand L (q ^ 2) (ModularCurve.jqModC L) := by
    rw [hD, map_sub, map_pow, hφw]
    push_cast
    rw [hj, hφj]

  set x₀ : PowerSeries A := PA ^ (q ^ 2) - expandPS (q ^ 2) PA with hx₀
  have hsmallφD : ∃ x y : PowerSeries A, y.map res ≠ 0 ∧ x.map res = 0 ∧
      ((φ D : ↥K) : LaurentSeries L) * E y = E x := by
    refine ⟨x₀, X ^ (q ^ 2), ?_, ?_, ?_⟩
    · rw [map_pow, PowerSeries.map_X]; exact pow_ne_zero _ PowerSeries.X_ne_zero
    ·
      rw [hx₀, map_sub, map_pow, map_expandPS, sub_eq_zero]
      ext m
      rw [hsq, coeff_pow_char_sq q, coeff_expandPS, ← hsq]
      split_ifs with hdvd
      ·
        rw [hPA, hmapmap, PowerSeries.coeff_map]
        set c : ℤ := coeff (m / q ^ 2) ModularCurve.jNum
        have hfix1 : ∀ z : ℤ, ((res.comp (Int.castRingHom A)) z) ^ q = (res.comp (Int.castRingHom A)) z := by
          intro z
          rw [eq_intCast, ← frobenius_def (p := q), map_intCast]
        rw [hsq, pow_mul, hfix1, hfix1]
      · rfl
    · rw [hφD, hEXpow, hx₀, map_sub, map_pow, hEPA]
      rw [show E (expandPS (q ^ 2) PA) = ModularCurve.qExpand L (q ^ 2) (E PA) by
        rw [hEapp, map_expandPS, ofPowerSeries_expandPS, ← hEapp]]
      rw [hEPA, map_mul, ModularCurve.qExpand_single, mul_pow, HahnSeries.single_pow]
      simp only [nsmul_eq_mul, mul_one, one_pow]
      push_cast
      ring

  have hφDW : φ D ∈ W₀ := by
    obtain ⟨x, y, hy, -, h⟩ := hsmallφD; exact (hW _).mpr ⟨x, y, hy, h⟩
  have hNφD := hN_of_small (φ D) hsmallφD
  have hDW : D ∈ W₀ := (hmem D).mpr hφDW
  have hND : D = 0 ∨ D⁻¹ ∉ W₀ := by
    rcases hNφD with h | h
    · exact Or.inl (φ.injective (by rw [h, map_zero]))
    · right; intro hinv; apply h; rw [← map_inv₀]; exact (hmem _).mp hinv
  obtain ⟨xD, yD, hyD, hxD, hDeq⟩ := hsmall_of_N D hDW hND
  obtain ⟨xw, yw, hyw, hweq⟩ := (hW w).mp hwW

  have hDcoe : (D : LaurentSeries L) = (w : LaurentSeries L) ^ (q ^ 2) - (j : LaurentSeries L) := by
    rw [hD]; push_cast; rfl
  have hid : xD * yw ^ (q ^ 2) * X = xw ^ (q ^ 2) * yD * X - PA * yD * yw ^ (q ^ 2) := by
    apply hEinj
    simp only [map_mul, map_sub, map_pow]
    rw [← hDeq, ← hweq, hEPA, hEX, hDcoe, hj]
    ring
  have hidκ : X * (xw.map res) ^ (q ^ 2) = (PA.map res) * (yw.map res) ^ (q ^ 2) := by
    have h := congrArg (PowerSeries.map res) hid
    simp only [map_mul, map_sub, map_pow, hxD, zero_mul, PowerSeries.map_X] at h

    have h2 : (yD.map res) * (X * (xw.map res) ^ (q ^ 2)) = (yD.map res) * ((PA.map res) * (yw.map res) ^ (q ^ 2)) := by
      have := sub_eq_zero.mp h.symm
      linear_combination this
    exact mul_left_cancel₀ hyD h2

  set V := yw.map res with hV
  set U := xw.map res with hU
  set Pκ := PA.map res with hPκ
  have hex : ∃ n, coeff n V ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hyw (PowerSeries.ext (by simpa using hcon))
  let k₀ := Nat.find hex
  have hk₀ : coeff k₀ V ≠ 0 := Nat.find_spec hex
  have hmin : ∀ i < k₀, coeff i V = 0 := fun i hi => by
    have := Nat.find_min hex hi; simpa using this
  have hVpow : ∀ m : ℕ, coeff m (V ^ (q ^ 2)) = if q ^ 2 ∣ m then (coeff (m / q ^ 2) V) ^ (q ^ 2) else 0 := by
    intro m; rw [hsq]; exact coeff_pow_char_sq q V m
  have hUpow : ∀ m : ℕ, coeff m (U ^ (q ^ 2)) = if q ^ 2 ∣ m then (coeff (m / q ^ 2) U) ^ (q ^ 2) else 0 := by
    intro m; rw [hsq]; exact coeff_pow_char_sq q U m
  have hP0 : coeff 0 Pκ = 1 := by
    rw [hPκ, hPA, hmapmap, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ModularCurve.constantCoeff_jNum, map_one]

  have hR : coeff (q ^ 2 * k₀) (Pκ * V ^ (q ^ 2)) ≠ 0 := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, q ^ 2 * k₀)]
    · rw [hP0, one_mul, hVpow, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by positivity)]
      exact pow_ne_zero _ hk₀
    · rintro ⟨i, j'⟩ hij hne
      have hij' : i + j' = q ^ 2 * k₀ := by simpa [Finset.HasAntidiagonal.mem_antidiagonal] using hij
      have hj' : j' < q ^ 2 * k₀ := by
        rcases Nat.eq_zero_or_pos i with hi | hi
        · exfalso; apply hne; subst hi; simp at hij'; rw [hij']
        · omega
      rw [hVpow]
      split_ifs with hd
      · obtain ⟨c, hc⟩ := hd
        rw [hc, Nat.mul_div_cancel_left _ (by positivity), hmin c (by nlinarith), zero_pow (by positivity), mul_zero]
      · rw [mul_zero]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) h

  have hL : coeff (q ^ 2 * k₀) (X * U ^ (q ^ 2)) = 0 := by
    rcases Nat.eq_zero_or_pos (q ^ 2 * k₀) with h0 | hpos
    · rw [h0, PowerSeries.coeff_zero_X_mul]
    · obtain ⟨m', hm'⟩ : ∃ m', q ^ 2 * k₀ = m' + 1 := ⟨q ^ 2 * k₀ - 1, by omega⟩
      rw [hm', PowerSeries.coeff_succ_X_mul, hUpow, if_neg]
      rintro ⟨c, hc⟩
      have : q ^ 2 ∣ 1 := by
        have h1 : q ^ 2 * k₀ = q ^ 2 * c + 1 := by rw [hm', hc]
        exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp (h1 ▸ dvd_mul_right _ _)
      exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  exact hR (by rw [← hidκ, hL])

end S_ModularCurve_comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC
end P2MW
export P2MW.S_ModularCurve_comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC (solution)
