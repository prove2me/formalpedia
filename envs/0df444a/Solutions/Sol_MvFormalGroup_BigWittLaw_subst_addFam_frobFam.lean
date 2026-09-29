-- Prove2me | solution 1 for MvFormalGroup.BigWittLaw.subst_addFam_frobFam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2135abe5-6101-5031-a09a-5ea537bde478

import Mathlib
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_BigWittLaw_subst_addFam_frobFam

set_option autoImplicit false

universe u

noncomputable section

namespace LambdaGhost

open PowerSeries

section Ghost

variable {A : Type*} [CommRing A]

abbrev inv1 (f : A⟦X⟧) : A⟦X⟧ := f.invOfUnit 1

theorem mul_inv1 {f : A⟦X⟧} (hf : constantCoeff f = 1) : f * inv1 f = 1 :=
  mul_invOfUnit f 1 (by rw [hf, Units.val_one])

theorem constantCoeff_inv1 (f : A⟦X⟧) : constantCoeff (inv1 f) = 1 := by
  rw [inv1, constantCoeff_invOfUnit, inv_one, Units.val_one]

def gh (f : A⟦X⟧) : A⟦X⟧ := X * d⁄dX A f * inv1 f

theorem mul_gh {f : A⟦X⟧} (hf : constantCoeff f = 1) : f * gh f = X * d⁄dX A f := by
  rw [gh, mul_comm f, mul_assoc, mul_assoc, mul_comm (inv1 f), mul_inv1 hf, mul_one]

theorem eq_gh {f g : A⟦X⟧} (hf : constantCoeff f = 1) (h : f * g = X * d⁄dX A f) : g = gh f := by
  have : inv1 f * (f * g) = inv1 f * (f * gh f) := by rw [h, mul_gh hf]
  rwa [← mul_assoc, ← mul_assoc, mul_comm (inv1 f), mul_inv1 hf, one_mul, one_mul] at this

@[scoped simp] theorem gh_one : gh (1 : A⟦X⟧) = 0 := by
  symm; apply eq_gh (by simp)
  simp [Derivation.map_one_eq_zero]

theorem gh_mul {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    gh (f * g) = gh f + gh g := by
  symm
  apply eq_gh (by rw [map_mul, hf, hg, mul_one])
  rw [Derivation.leibniz, mul_add, smul_eq_mul, smul_eq_mul]
  have h1 : f * g * gh f = g * (X * d⁄dX A f) := by rw [mul_comm f g, mul_assoc, mul_gh hf]
  have h2 : f * g * gh g = f * (X * d⁄dX A g) := by rw [mul_assoc, mul_gh hg]
  rw [h1, h2]; ring

theorem gh_prod {ι : Type*} (s : Finset ι) (f : ι → A⟦X⟧) (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
    gh (∏ i ∈ s, f i) = ∑ i ∈ s, gh (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      gh_mul (hf i (Finset.mem_insert_self i s)) ?_, ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    rw [map_prod]
    exact Finset.prod_eq_one fun j hj => hf j (Finset.mem_insert_of_mem hj)

theorem gh_pow {f : A⟦X⟧} (hf : constantCoeff f = 1) (d : ℕ) : gh (f ^ d) = d • gh f := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, gh_mul (by rw [map_pow, hf, one_pow]) hf, ih, succ_nsmul]

theorem coeff_zero_gh (f : A⟦X⟧) : coeff 0 (gh f) = 0 := by
  rw [gh, mul_assoc, coeff_zero_X_mul]

theorem map_gh {B : Type*} [CommRing B] (φ : A →+* B) {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    map φ (gh f) = gh (map φ f) := by
  apply eq_gh (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hf, map_one])
  rw [← map_mul, mul_gh hf, map_mul, map_X]
  congr 1
  ext n
  rw [coeff_map, coeff_derivative, coeff_derivative, coeff_map, map_mul]
  simp

theorem eq_of_gh_eq [IsAddTorsionFree A] {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (h : gh f = gh g) : f = g := by

  have hg' : constantCoeff (inv1 g) = 1 := constantCoeff_inv1 g
  have hinv : gh (inv1 g) = -gh g := by
    have := gh_mul hg hg'
    rw [mul_inv1 hg, gh_one] at this
    linear_combination -this
  have h0 : gh (f * inv1 g) = 0 := by rw [gh_mul hf hg', hinv, h, add_neg_cancel]
  have hder : d⁄dX A (f * inv1 g) = 0 := by
    have := mul_gh (f := f * inv1 g) (by rw [map_mul, hf, hg', mul_one])
    rw [h0, mul_zero] at this

    ext n
    have := congrArg (coeff (n + 1)) this
    rwa [map_zero, coeff_succ_X_mul, eq_comm] at this
  have hconst : f * inv1 g = 1 := by
    apply derivative.ext (by rw [hder, Derivation.map_one_eq_zero])
    rw [map_mul, hf, hg', map_one, mul_one]
  calc f = f * (inv1 g * g) := by rw [mul_comm (inv1 g), mul_inv1 hg, mul_one]
    _ = g := by rw [← mul_assoc, hconst, one_mul]

theorem coeff_gh_eq_of_coeff_eq {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (K : ℕ)
    (h : ∀ j ≤ K, coeff j f = coeff j g) : ∀ j ≤ K, coeff j (gh f) = coeff j (gh g) := by

  have hdvd : (X : A⟦X⟧) ^ (K + 1) ∣ f - g := by
    rw [X_pow_dvd_iff]; intro j hj; rw [map_sub, h j (by omega), sub_self]

  have key : f * g * (gh f - gh g) = X * (d⁄dX A (f - g) * g - d⁄dX A g * (f - g)) := by
    rw [mul_sub, show f * g * gh f = g * (f * gh f) by ring, mul_gh hf, mul_assoc, mul_gh hg, map_sub]
    ring
  have hdvd2 : (X : A⟦X⟧) ^ (K + 1) ∣ f * g * (gh f - gh g) := by
    rw [key]
    obtain ⟨r, hr⟩ := hdvd
    have hd' : (X : A⟦X⟧) ^ K ∣ d⁄dX A (f - g) := by
      rw [X_pow_dvd_iff]; intro j hj
      rw [coeff_derivative, hr, coeff_X_pow_mul', if_neg (by omega), zero_mul]
    obtain ⟨r', hr'⟩ := hd'
    rw [hr', hr]
    exact ⟨r' * g - X * d⁄dX A g * r, by ring⟩

  have hdvd3 : (X : A⟦X⟧) ^ (K + 1) ∣ gh f - gh g := by
    have hu : constantCoeff (f * g) = 1 := by rw [map_mul, hf, hg, mul_one]
    have : gh f - gh g = inv1 (f * g) * (f * g * (gh f - gh g)) := by
      rw [← mul_assoc, mul_comm (inv1 _), mul_inv1 hu, one_mul]
    rw [this]
    exact Dvd.dvd.mul_left hdvd2 _
  intro j hj
  have := (X_pow_dvd_iff.mp hdvd3) j (by omega)
  rwa [map_sub, sub_eq_zero] at this

end Ghost

section Lambda

open MvFormalGroup.BigWittLaw

variable {A : Type*} [CommRing A]

theorem inv1_eq_of_mul_eq_one {f g : A⟦X⟧} (hf : constantCoeff f = 1) (h : f * g = 1) : inv1 f = g := by
  calc inv1 f = inv1 f * (f * g) := by rw [h, mul_one]
    _ = g := by rw [← mul_assoc, mul_comm (inv1 f), mul_inv1 hf, one_mul]

theorem coeff_mul_eq_of_dvd_sub_one {f g : A⟦X⟧} {j : ℕ} (hg : (X : A⟦X⟧) ^ (j + 1) ∣ g - 1)
    (i : ℕ) (hi : i ≤ j) : coeff i (f * g) = coeff i f := by
  have : f * g = f + f * (g - 1) := by ring
  rw [this, map_add, add_eq_left]
  exact (X_pow_dvd_iff.mp (Dvd.dvd.mul_left hg f)) i (by omega)

theorem dvd_prod_sub_one {ι : Type*} (s : Finset ι) (g : ι → A⟦X⟧) (N : ℕ)
    (h : ∀ i ∈ s, (X : A⟦X⟧) ^ N ∣ g i - 1) : (X : A⟦X⟧) ^ N ∣ (∏ i ∈ s, g i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have e : g i * ∏ x ∈ s, g x - 1 = (g i - 1) * ∏ x ∈ s, g x + (∏ x ∈ s, g x - 1) := by ring
    rw [e]
    exact dvd_add (Dvd.dvd.mul_right (h i (Finset.mem_insert_self i s)) _)
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

theorem dvd_pow_sub_one {g : A⟦X⟧} {N : ℕ} (h : (X : A⟦X⟧) ^ N ∣ g - 1) (d : ℕ) :
    (X : A⟦X⟧) ^ N ∣ g ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have e : g ^ (d + 1) - 1 = (g - 1) * g ^ d + (g ^ d - 1) := by ring
    rw [e]
    exact dvd_add (Dvd.dvd.mul_right h _) ih

theorem X_pow_dvd_geomSeries_sub_one (c : A) {e : ℕ} (he : e ≠ 0) :
    (X : A⟦X⟧) ^ e ∣ geomSeries c e - 1 := by
  rw [X_pow_dvd_iff]
  intro i hi
  rw [map_sub, coeff_geomSeries, coeff_one]
  by_cases hi0 : i = 0
  · subst hi0; simp
  · rw [if_neg, if_neg hi0, sub_zero]
    rintro ⟨r, rfl⟩
    rcases r with _ | r
    · exact hi0 (mul_zero e)
    · have : e * (r + 1) ≥ e := Nat.le_mul_of_pos_right e (Nat.succ_pos r)
      omega

theorem coeff_gh_geomSeries (c : A) {e : ℕ} (he : e ≠ 0) (m : ℕ) :
    coeff m (gh (geomSeries c e)) = if e ∣ m ∧ m ≠ 0 then (e : A) * c ^ (m / e) else 0 := by
  set q : A⟦X⟧ := 1 - C c * X ^ e with hq
  have hq1 : constantCoeff q = 1 := by
    rw [hq, map_sub, map_one, map_mul, map_pow, constantCoeff_C, constantCoeff_X, zero_pow he,
      mul_zero, sub_zero]
  have hg1 : constantCoeff (geomSeries c e) = 1 := constantCoeff_geomSeries c e
  have hqg : q * geomSeries c e = 1 := one_sub_C_mul_X_pow_mul_geomSeries c he
  have hinv : inv1 q = geomSeries c e := inv1_eq_of_mul_eq_one hq1 hqg

  have hXd : X * d⁄dX A q = -(C ((e : A) * c) * X ^ e) := by
    ext j
    rcases j with _ | j
    · simp [coeff_zero_X_mul, he]
    · rw [coeff_succ_X_mul, coeff_derivative, hq, map_sub, coeff_one, if_neg (Nat.succ_ne_zero j),
        zero_sub]
      simp only [map_neg, coeff_C_mul, coeff_X_pow]
      split_ifs with h
      · subst h; push_cast; ring
      · simp

  have hsum : gh q + gh (geomSeries c e) = 0 := by rw [← gh_mul hq1 hg1, hqg, gh_one]
  have hgeom : gh (geomSeries c e) = C ((e : A) * c) * X ^ e * geomSeries c e := by
    have : gh q = -(C ((e : A) * c) * X ^ e * geomSeries c e) := by
      rw [gh, hXd, hinv]; ring
    linear_combination hsum - this
  rw [hgeom, mul_assoc, coeff_C_mul]
  by_cases hem : e ≤ m
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hem
    rw [add_comm, coeff_X_pow_mul, coeff_geomSeries]
    by_cases hd : e ∣ m'
    · have hd' : e ∣ m' + e := Nat.dvd_add hd (dvd_refl e)
      rw [if_pos hd, if_pos ⟨hd', by omega⟩]
      obtain ⟨r, rfl⟩ := hd
      rw [show e * r + e = e * (r + 1) by ring, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he), pow_succ]
      ring
    · have hd' : ¬ (e ∣ m' + e) := fun h => hd (by simpa using (Nat.dvd_add_right (dvd_refl e)).mp (by rwa [add_comm] at h))
      rw [if_neg hd, if_neg (fun h => hd' h.1), mul_zero]
  · rw [coeff_X_pow_mul', if_neg hem, mul_zero, if_neg]
    rintro ⟨⟨r, rfl⟩, h0⟩
    rcases r with _ | r
    · exact h0 (mul_zero e)
    · exact hem (Nat.le_mul_of_pos_right e (Nat.succ_pos r))

theorem coeff_gh_genSeries (m : ℕ) (hm : m ≠ 0) :
    coeff m (gh genSeries) = ∑ k ∈ Finset.range m,
      if (k + 1) ∣ m then ((k + 1 : ℕ) : MvPolynomial ℕ ℤ) * wittCoord k ^ (m / (k + 1)) else 0 := by
  have hgen1 : constantCoeff genSeries = 1 := constantCoeff_genSeries
  have hP1 : constantCoeff (∏ k ∈ Finset.range m, geomSeries (wittCoord k) (k + 1)) = 1 := by
    rw [map_prod]; exact Finset.prod_eq_one fun k _ => constantCoeff_geomSeries _ _
  rw [coeff_gh_eq_of_coeff_eq hgen1 hP1 m (fun j hj => (coeff_prod_geomSeries_wittCoord hj).symm) m le_rfl,
    gh_prod _ _ (fun k _ => constantCoeff_geomSeries _ _), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_gh_geomSeries _ (Nat.succ_ne_zero k)]
  simp only [hm, ne_eq, not_false_eq_true, and_true, Nat.cast_succ]

variable (n : ℕ)

def frobSeries : PowerSeries (MvPolynomial ℕ ℤ) :=
  PowerSeries.mk fun j => if j = 0 then 1 else frobPoly n (j - 1)

@[scoped simp] theorem constantCoeff_frobSeries : constantCoeff (frobSeries n) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, frobSeries, coeff_mk, if_pos rfl]

theorem coeff_frobSeries_succ (m : ℕ) : coeff (m + 1) (frobSeries n) = frobPoly n m := by
  rw [frobSeries, coeff_mk, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]

theorem X_pow_dvd_frobFactor_sub_one {n k j : ℕ} (hn : 0 < n) (hk : n * j ≤ k) :
    (X : (MvPolynomial ℕ ℤ)⟦X⟧) ^ (j + 1) ∣ frobFactor n k - 1 := by
  rw [frobFactor]
  set d := Nat.gcd (k + 1) n with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right _ hn
  have hdk : d ∣ k + 1 := Nat.gcd_dvd_left _ _
  have hdn : d ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_right _ _)
  set e := (k + 1) / d with he
  have hed : e * d = k + 1 := Nat.div_mul_cancel hdk
  have hej : j + 1 ≤ e := by
    by_contra h
    have h' : e ≤ j := by omega
    have : e * d ≤ n * j := by
      calc e * d ≤ j * n := Nat.mul_le_mul h' hdn
        _ = n * j := mul_comm _ _
    omega
  have he0 : e ≠ 0 := by omega
  obtain ⟨r, hr⟩ := X_pow_dvd_geomSeries_sub_one (wittCoord k ^ (n / d)) he0
  apply dvd_pow_sub_one
  refine ⟨X ^ (e - (j + 1)) * r, ?_⟩
  rw [hr, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hej]

theorem coeff_frobSeries_eq_coeff_prod {n : ℕ} (hn : 0 < n) {m j : ℕ} (hj : j ≤ m) :
    coeff j (frobSeries n) = coeff j (∏ k ∈ Finset.range (n * m), frobFactor n k) := by
  rcases j with _ | j
  · rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_frobSeries, coeff_zero_eq_constantCoeff_apply,
      map_prod, Finset.prod_eq_one fun k _ => constantCoeff_frobFactor n k]
  · rw [coeff_frobSeries_succ, frobPoly]
    have hsplit : Finset.range (n * m) =
        Finset.range (n * (j + 1)) ∪ (Finset.range (n * m) \ Finset.range (n * (j + 1))) := by
      rw [Finset.union_sdiff_of_subset]
      exact Finset.range_subset_range.2 (Nat.mul_le_mul_left n hj)
    rw [hsplit, Finset.prod_union Finset.disjoint_sdiff,
      coeff_mul_eq_of_dvd_sub_one (dvd_prod_sub_one _ _ _ fun k hk => ?_) _ le_rfl]
    have hk : n * (j + 1) ≤ k := by
      have := (Finset.mem_sdiff.mp hk).2
      rw [Finset.mem_range, not_lt] at this
      exact this
    exact X_pow_dvd_frobFactor_sub_one hn hk

theorem frob_term_eq (b : MvPolynomial ℕ ℤ) {n : ℕ} (hn : 0 < n) (k m : ℕ) (hm : m ≠ 0) :
    (Nat.gcd (k + 1) n : MvPolynomial ℕ ℤ) *
        (if (k + 1) / Nat.gcd (k + 1) n ∣ m ∧ m ≠ 0 then
          (((k + 1) / Nat.gcd (k + 1) n : ℕ) : MvPolynomial ℕ ℤ) *
            (b ^ (n / Nat.gcd (k + 1) n)) ^ (m / ((k + 1) / Nat.gcd (k + 1) n))
        else 0) =
      if (k + 1) ∣ n * m then ((k + 1 : ℕ) : MvPolynomial ℕ ℤ) * b ^ (n * m / (k + 1)) else 0 := by
  have hdpos : 0 < Nat.gcd (k + 1) n := Nat.gcd_pos_of_pos_right _ hn
  have hcop := Nat.coprime_div_gcd_div_gcd (m := k + 1) (n := n) hdpos
  obtain ⟨e, hed⟩ := Nat.gcd_dvd_left (k + 1) n
  obtain ⟨n', hnd⟩ := Nat.gcd_dvd_right (k + 1) n
  set d := Nat.gcd (k + 1) n with hd
  have he' : (k + 1) / d = e := by rw [hed, Nat.mul_div_cancel_left _ hdpos]
  have hn'' : n / d = n' := by rw [hnd, Nat.mul_div_cancel_left _ hdpos]
  rw [he', hn''] at hcop ⊢
  have hepos : 0 < e := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hed; omega
  have hiff : (k + 1) ∣ n * m ↔ e ∣ m := by
    rw [hed, hnd, mul_assoc, Nat.mul_dvd_mul_iff_left hdpos]
    exact ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩
  by_cases h : e ∣ m
  · rw [if_pos ⟨h, hm⟩, if_pos (hiff.2 h), ← mul_assoc, ← Nat.cast_mul, ← hed, ← pow_mul]
    congr 2
    obtain ⟨r, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ hepos, hed, hnd, show d * n' * (e * r) = (d * e) * (n' * r) by ring,
      Nat.mul_div_cancel_left _ (Nat.mul_pos hdpos hepos)]
  · rw [if_neg (fun h' => h h'.1), if_neg (fun h' => h (hiff.1 h')), mul_zero]

theorem coeff_gh_frobSeries {n : ℕ} (hn : 0 < n) (m : ℕ) :
    coeff m (gh (frobSeries n)) = coeff (n * m) (gh genSeries) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [mul_zero, coeff_zero_gh, coeff_zero_gh]
  have hm0 : m ≠ 0 := by omega
  have hP1 : constantCoeff (∏ k ∈ Finset.range (n * m), frobFactor n k) = 1 := by
    rw [map_prod]; exact Finset.prod_eq_one fun k _ => constantCoeff_frobFactor n k
  rw [coeff_gh_eq_of_coeff_eq (constantCoeff_frobSeries n) hP1 m
      (fun j hj => coeff_frobSeries_eq_coeff_prod hn hj) m le_rfl,
    gh_prod _ _ (fun k _ => constantCoeff_frobFactor n k), map_sum,
    coeff_gh_genSeries (n * m) (Nat.mul_ne_zero hn.ne' hm0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hdpos : 0 < Nat.gcd (k + 1) n := Nat.gcd_pos_of_pos_right _ hn
  have he0 : (k + 1) / Nat.gcd (k + 1) n ≠ 0 := by
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left (k + 1) n)
    intro h; rw [h, zero_mul] at this; omega
  rw [frobFactor, gh_pow (constantCoeff_geomSeries _ _), map_nsmul, coeff_gh_geomSeries _ he0, nsmul_eq_mul]
  exact frob_term_eq (wittCoord k) hn k m hm0

end Lambda

section TwoVar

open MvFormalGroup.BigWittLaw MvPolynomial

abbrev B2 : Type := MvPolynomial (Fin 2 × ℕ) ℤ

abbrev emb (i : Fin 2) : MvPolynomial ℕ ℤ →+* B2 := (rename (Prod.mk i)).toRingHom

abbrev coadd : MvPolynomial ℕ ℤ →+* B2 := (aeval fun m => addPoly m).toRingHom

theorem constantCoeff_map_of {S : Type*} [CommRing S] (φ : MvPolynomial ℕ ℤ →+* S) {f : PowerSeries (MvPolynomial ℕ ℤ)}
    (hf : PowerSeries.constantCoeff f = 1) : PowerSeries.constantCoeff (PowerSeries.map φ f) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_one]

theorem ext_succ {S : Type*} [CommRing S] {F G : PowerSeries S} (hF : PowerSeries.constantCoeff F = 1)
    (hG : PowerSeries.constantCoeff G = 1) (h : ∀ m, PowerSeries.coeff (m + 1) F = PowerSeries.coeff (m + 1) G) :
    F = G := by
  ext j
  rcases j with _ | m
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF, hG]
  · exact h m

theorem pair_eq (F G : PowerSeries B2) (im : Fin 2 × ℕ) :
    (![fun m => PowerSeries.coeff (m + 1) F, fun m => PowerSeries.coeff (m + 1) G] : Fin 2 → ℕ → B2) im.1 im.2 =
      Fin.cases (PowerSeries.coeff (im.2 + 1) F) (fun _ => PowerSeries.coeff (im.2 + 1) G) im.1 := by
  rcases im with ⟨i, m⟩
  fin_cases i <;> rfl

theorem map_coadd_genSeries :
    PowerSeries.map coadd genSeries = PowerSeries.map (emb 0) genSeries * PowerSeries.map (emb 1) genSeries := by
  have h0 := constantCoeff_map_of (emb 0) constantCoeff_genSeries
  have h1 := constantCoeff_map_of (emb 1) constantCoeff_genSeries
  refine ext_succ (constantCoeff_map_of coadd constantCoeff_genSeries) (by rw [map_mul, h0, h1, mul_one]) fun m => ?_
  rw [coeff_succ_mul_eq_aeval h0 h1, PowerSeries.coeff_map, coeff_genSeries_succ]
  change aeval (fun m => addPoly m) (X m : MvPolynomial ℕ ℤ) = _
  rw [aeval_X]
  rw [aeval_addPoly]
  simp [addPoly, PowerSeries.coeff_map, coeff_genSeries_succ, rename_X]

variable {n : ℕ} (hn : 0 < n)

include hn in

theorem map_coadd_frobSeries :
    PowerSeries.map coadd (frobSeries n) =
      PowerSeries.map (emb 0) (frobSeries n) * PowerSeries.map (emb 1) (frobSeries n) := by
  have hc := constantCoeff_map_of coadd (constantCoeff_frobSeries n)
  have h0 := constantCoeff_map_of (emb 0) (constantCoeff_frobSeries n)
  have h1 := constantCoeff_map_of (emb 1) (constantCoeff_frobSeries n)
  have g0 := constantCoeff_map_of (emb 0) constantCoeff_genSeries
  have g1 := constantCoeff_map_of (emb 1) constantCoeff_genSeries
  apply eq_of_gh_eq hc (by rw [map_mul, h0, h1, mul_one])
  rw [gh_mul h0 h1, ← map_gh _ (constantCoeff_frobSeries n), ← map_gh _ (constantCoeff_frobSeries n),
    ← map_gh _ (constantCoeff_frobSeries n)]
  ext m
  rw [map_add, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, coeff_gh_frobSeries hn,
    ← PowerSeries.coeff_map, ← PowerSeries.coeff_map, ← PowerSeries.coeff_map,
    map_gh _ constantCoeff_genSeries, map_gh _ constantCoeff_genSeries, map_gh _ constantCoeff_genSeries,
    map_coadd_genSeries, gh_mul g0 g1, map_add]

include hn in

theorem aeval_addPoly_frobPoly (m : ℕ) :
    aeval (fun j => addPoly j) (frobPoly n m) =
      aeval (fun im : Fin 2 × ℕ => (![fun j => rename (Prod.mk (0 : Fin 2)) (frobPoly n j),
        fun j => rename (Prod.mk (1 : Fin 2)) (frobPoly n j)] : Fin 2 → ℕ → B2) im.1 im.2) (addPoly m) := by
  have h0 := constantCoeff_map_of (emb 0) (constantCoeff_frobSeries n)
  have h1 := constantCoeff_map_of (emb 1) (constantCoeff_frobSeries n)
  have := congrArg (PowerSeries.coeff (m + 1)) (map_coadd_frobSeries hn)
  rw [PowerSeries.coeff_map, coeff_frobSeries_succ, coeff_succ_mul_eq_aeval h0 h1] at this
  have hF : (fun im : Fin 2 × ℕ => (![fun j => rename (Prod.mk (0 : Fin 2)) (frobPoly n j),
        fun j => rename (Prod.mk (1 : Fin 2)) (frobPoly n j)] : Fin 2 → ℕ → B2) im.1 im.2) =
      fun im : Fin 2 × ℕ => (![fun m => PowerSeries.coeff (m + 1) (PowerSeries.map (emb 0) (frobSeries n)),
        fun m => PowerSeries.coeff (m + 1) (PowerSeries.map (emb 1) (frobSeries n))] : Fin 2 → ℕ → B2)
        im.1 im.2 := by
    funext im
    rcases im with ⟨i, j⟩
    fin_cases i <;> simp [PowerSeries.coeff_map, coeff_frobSeries_succ]
  rw [hF]
  exact this

end TwoVar

section Transport

open MvFormalGroup MvFormalGroup.BigWittLaw MvPolynomial

variable (R : Type u) [CommRing R]

theorem subst_blk_toFam (i : Fin 2) (P : MvPolynomial ℕ ℤ) :
    MvPowerSeries.subst (WittLaw.blk (R := R) i) (toFam R P) =
      ((MvPolynomial.map (Int.castRingHom R) (rename (Prod.mk i) P) : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  rw [toFam, MvPowerSeries.subst_coe]
  let ψ₁ : MvPolynomial ℕ ℤ →+* MvPowerSeries (Fin 2 × ℕ) R :=
    (MvPolynomial.aeval (WittLaw.blk (R := R) i)).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial ℕ ℤ →+* MvPowerSeries (Fin 2 × ℕ) R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 2 × ℕ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (rename (Prod.mk i)).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp C) (ψ₂.comp C)) r
    · simp [ψ₁, ψ₂, WittLaw.blk]
  exact RingHom.congr_fun hψ P

theorem subst_addFam_toFam (P : MvPolynomial ℕ ℤ) :
    MvPowerSeries.subst (addFam R) (toFam R P) =
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.aeval (fun j => addPoly j) P) :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
  rw [toFam, MvPowerSeries.subst_coe]
  let ψ₁ : MvPolynomial ℕ ℤ →+* MvPowerSeries (Fin 2 × ℕ) R :=
    (MvPolynomial.aeval (addFam R)).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial ℕ ℤ →+* MvPowerSeries (Fin 2 × ℕ) R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 2 × ℕ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (MvPolynomial.aeval fun j => addPoly j).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp C) (ψ₂.comp C)) r
    · simp [ψ₁, ψ₂, addFam]
  exact RingHom.congr_fun hψ P

end Transport

end LambdaGhost
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_addFam_frobFam.LambdaGhost"

end
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_addFam_frobFam.LambdaGhost"

open MvFormalGroup MvFormalGroup.BigWittLaw in
theorem solution
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (m : ℕ) :
    MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (MvFormalGroup.BigWittLaw.frobFam R n m) =
      MvPowerSeries.subst
        (MvFormalGroup.WittLaw.pairFam (MvFormalGroup.BigWittLaw.frobFam R n))
        (MvFormalGroup.BigWittLaw.addFam R m) := by
  have hpair : WittLaw.pairFam (frobFam R n) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.rename (Prod.mk im.1) (frobPoly n im.2)) :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext im
    rcases im with ⟨i, j⟩
    show MvPowerSeries.subst (WittLaw.blk i) (toFam R (frobPoly n j)) = _
    exact LambdaGhost.subst_blk_toFam R i (frobPoly n j)
  have hfam : (fun im : Fin 2 × ℕ => (![fun j => MvPolynomial.rename (Prod.mk (0 : Fin 2)) (frobPoly n j),
        fun j => MvPolynomial.rename (Prod.mk (1 : Fin 2)) (frobPoly n j)] : Fin 2 → ℕ → LambdaGhost.B2) im.1 im.2) =
      fun im : Fin 2 × ℕ => MvPolynomial.rename (Prod.mk im.1) (frobPoly n im.2) := by
    funext im
    rcases im with ⟨i, j⟩
    fin_cases i <;> rfl
  rw [hpair, subst_coe_addFam (fun im : Fin 2 × ℕ => MvPolynomial.rename (Prod.mk im.1) (frobPoly n im.2)) m,
    show frobFam R n m = toFam R (frobPoly n m) from rfl, LambdaGhost.subst_addFam_toFam,
    LambdaGhost.aeval_addPoly_frobPoly hn m, hfam]

end S_MvFormalGroup_BigWittLaw_subst_addFam_frobFam
end P2MW
export P2MW.S_MvFormalGroup_BigWittLaw_subst_addFam_frobFam (solution)
