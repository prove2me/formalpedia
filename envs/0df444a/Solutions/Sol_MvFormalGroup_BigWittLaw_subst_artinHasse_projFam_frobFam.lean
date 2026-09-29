-- Prove2me | solution 1 for MvFormalGroup.BigWittLaw.subst_artinHasse_projFam_frobFam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c4d2a0b6-b9c5-597e-93b4-5e6a2ca27a19

import Mathlib
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_ArtinHasse
import Theorems.Thm_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam

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

namespace AHGhost

open Classical
open PowerSeries LambdaGhost

section generic

variable {A : Type*} [CommRing A]

theorem constantCoeff_subst_of_constantCoeff_eq_zero {a : A⟦X⟧} (ha : constantCoeff a = 0) (f : A⟦X⟧) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hS : HasSubst a := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hS, finsum_eq_single _ 0]
  · simp
  · intro d hd
    have : coeff 0 (a ^ d) = 0 := by
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow hd]
    rw [this, smul_zero]

theorem gh_exp_subst [Algebra ℚ A] {G : A⟦X⟧} (hG : constantCoeff G = 0) :
    gh ((exp A).subst G) = X * d⁄dX A G := by
  have hS : HasSubst G := HasSubst.of_constantCoeff_zero' hG
  have h1 : constantCoeff ((exp A).subst G) = 1 := by
    rw [constantCoeff_subst_of_constantCoeff_eq_zero hG, ← coeff_zero_eq_constantCoeff_apply, coeff_exp]
    simp
  symm
  apply eq_gh h1
  rw [derivative_subst hS, derivative_exp]
  ring

theorem X_mul_derivative_subst_smul_X_pow (f : A⟦X⟧) (z : A) {q : ℕ} (hq : q ≠ 0) :
    X * d⁄dX A (f.subst (z • X ^ q)) = (q : A⟦X⟧) * (X * d⁄dX A f).subst (z • X ^ q) := by
  have ha : constantCoeff (z • (X : A⟦X⟧) ^ q) = 0 := by
    rw [constantCoeff_smul, map_pow, constantCoeff_X, zero_pow hq, smul_zero]
  have hS : HasSubst (z • (X : A⟦X⟧) ^ q) := HasSubst.of_constantCoeff_zero' ha
  have hd : d⁄dX A (z • (X : A⟦X⟧) ^ q) = C z * ((q : A⟦X⟧) * X ^ (q - 1)) := by
    rw [smul_eq_C_mul, Derivation.leibniz, derivative_C, smul_zero, add_zero, derivative_pow, derivative_X, mul_one,
      smul_eq_mul]
  rw [derivative_subst hS, subst_mul hS, subst_X hS, hd]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  rw [Nat.succ_sub_one, smul_eq_C_mul, pow_succ]
  ring

theorem gh_subst_smul_X_pow {f : A⟦X⟧} (hf : constantCoeff f = 1) (z : A) {q : ℕ} (hq : q ≠ 0) :
    gh (f.subst (z • X ^ q)) = (q : A⟦X⟧) * (gh f).subst (z • X ^ q) := by
  have ha : constantCoeff (z • (X : A⟦X⟧) ^ q) = 0 := by
    rw [constantCoeff_smul, map_pow, constantCoeff_X, zero_pow hq, smul_zero]
  have hS : HasSubst (z • (X : A⟦X⟧) ^ q) := HasSubst.of_constantCoeff_zero' ha
  symm
  apply eq_gh (by rw [constantCoeff_subst_of_constantCoeff_eq_zero ha, hf])
  rw [X_mul_derivative_subst_smul_X_pow f z hq, ← mul_gh hf, subst_mul hS]
  ring

theorem coeff_subst_smul_X_pow (g : A⟦X⟧) (z : A) {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    coeff n (g.subst (z • X ^ q)) = if q ∣ n then z ^ (n / q) * coeff (n / q) g else 0 := by
  have : (z • (X : A⟦X⟧) ^ q) = subst (X ^ q) (z • (X : A⟦X⟧)) := by
    rw [subst_smul (HasSubst.X_pow hq), subst_X (HasSubst.X_pow hq)]
  rw [this, ← subst_comp_subst_apply (HasSubst.smul_X' z) (HasSubst.X_pow hq), ← rescale_eq_subst,
    coeff_subst_X_pow hq]
  split_ifs with h
  · rw [Algebra.algebraMap_self, RingHom.id_apply, coeff_rescale]
  · rfl

end generic

section artinHasse

variable (p : ℕ) [Fact p.Prime]

def Lser : ℚ⟦X⟧ := PowerSeries.mk fun k : ℕ => if ∃ m : ℕ, k = p ^ m then (k : ℚ)⁻¹ else 0

def Theta (A : Type*) [CommRing A] : A⟦X⟧ := PowerSeries.mk fun k : ℕ => if ∃ m : ℕ, k = p ^ m then 1 else 0

theorem coeff_Theta (A : Type*) [CommRing A] (k : ℕ) :
    coeff k (Theta p A) = if ∃ m : ℕ, k = p ^ m then 1 else 0 := coeff_mk _ _

theorem map_Theta {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) :
    map φ (Theta p A) = Theta p B := by
  ext k; rw [coeff_map, coeff_Theta, coeff_Theta]; split_ifs <;> simp

theorem constantCoeff_Lser : constantCoeff (Lser p) = 0 := by
  rw [Lser, PowerSeries.constantCoeff_mk, if_neg]
  rintro ⟨m, hm⟩
  exact absurd hm.symm (pow_ne_zero m (Fact.out : p.Prime).ne_zero)

theorem X_mul_derivative_Lser : X * d⁄dX ℚ (Lser p) = Theta p ℚ := by
  ext k
  rcases k with _ | k
  · rw [coeff_zero_X_mul, coeff_Theta, if_neg]
    rintro ⟨m, hm⟩; exact absurd hm.symm (pow_ne_zero m (Fact.out : p.Prime).ne_zero)
  · rw [coeff_succ_X_mul, coeff_derivative, Lser, coeff_mk, coeff_Theta]
    split_ifs with h
    · rw [← Nat.cast_succ, inv_mul_cancel₀]; exact_mod_cast Nat.succ_ne_zero k
    · rw [zero_mul]

theorem gh_series_padicInt : gh (MvFormalGroup.ArtinHasse.series p) = Theta p ℤ_[p] := by
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b h => Subtype.ext h
  apply map_injective (algebraMap ℤ_[p] ℚ_[p]) hinj
  rw [map_gh _ (MvFormalGroup.ArtinHasse.constantCoeff_series p), MvFormalGroup.ArtinHasse.map_series_eq_map_exp_subst,
    map_Theta]
  have hL : constantCoeff (map (algebraMap ℚ ℚ_[p]) (Lser p)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, constantCoeff_Lser, map_zero]
  have e1 : map (algebraMap ℚ ℚ_[p]) ((exp ℚ).subst (Lser p)) = (exp ℚ_[p]).subst (map (algebraMap ℚ ℚ_[p]) (Lser p)) := by
    have := map_subst (HasSubst.of_constantCoeff_zero' (constantCoeff_Lser p)) (h := algebraMap ℚ ℚ_[p]) (exp ℚ)
    rw [map_exp] at this
    exact this
  change gh (map (algebraMap ℚ ℚ_[p]) ((exp ℚ).subst (Lser p))) = Theta p ℚ_[p]
  rw [e1, gh_exp_subst hL]
  have : X * d⁄dX ℚ_[p] (map (algebraMap ℚ ℚ_[p]) (Lser p)) = map (algebraMap ℚ ℚ_[p]) (X * d⁄dX ℚ (Lser p)) := by
    ext n
    rcases n with _ | n
    · simp [coeff_zero_X_mul]
    · rw [coeff_succ_X_mul, coeff_map, coeff_succ_X_mul, coeff_derivative, coeff_derivative, coeff_map, map_mul,
        map_add, map_natCast, map_one]
  rw [this, X_mul_derivative_Lser, map_Theta]

variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

theorem scaled_eq_subst (q : ℕ) (hq : q ≠ 0) (z : A) :
    MvFormalGroup.ArtinHasse.scaled p q z = (map (algebraMap ℤ_[p] A) (MvFormalGroup.ArtinHasse.series p)).subst (z • X ^ q) := by
  ext n
  rw [MvFormalGroup.ArtinHasse.coeff_scaled, coeff_subst_smul_X_pow _ z hq, coeff_map]
  split_ifs <;> ring

theorem coeff_gh_scaled (q : ℕ) (hq : q ≠ 0) (z : A) (n : ℕ) :
    coeff n (gh (MvFormalGroup.ArtinHasse.scaled p q z)) =
      if q ∣ n ∧ ∃ m : ℕ, n / q = p ^ m then (q : A) * z ^ (n / q) else 0 := by
  rw [scaled_eq_subst p q hq z, gh_subst_smul_X_pow (by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
        MvFormalGroup.ArtinHasse.constantCoeff_series, map_one]) z hq,
    ← map_gh _ (MvFormalGroup.ArtinHasse.constantCoeff_series p), gh_series_padicInt, map_Theta,
    ← map_natCast (C : A →+* A⟦X⟧) q, coeff_C_mul, coeff_subst_smul_X_pow _ z hq, coeff_Theta]
  by_cases hdiv : q ∣ n
  · rw [if_pos hdiv]
    by_cases hm : ∃ m : ℕ, n / q = p ^ m
    · rw [if_pos hm, if_pos ⟨hdiv, hm⟩, mul_one]
    · rw [if_neg hm, if_neg (fun h => hm h.2), mul_zero, mul_zero]
  · rw [if_neg hdiv, if_neg (fun h => hdiv h.1), mul_zero]

end artinHasse

end AHGhost

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
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam.LambdaGhost"

namespace LambdaGhost

section Projector

open MvFormalGroup MvFormalGroup.BigWittLaw MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]

def AHser : PowerSeries (MvPolynomial ℕ ℤ_[p]) :=
  PowerSeries.mk fun i => if i = 0 then 1 else ArtinHasse.coord p (i - 1)

@[scoped simp] theorem constantCoeff_AHser : PowerSeries.constantCoeff (AHser p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, AHser, PowerSeries.coeff_mk, if_pos rfl]

theorem coeff_AHser_succ (i : ℕ) : PowerSeries.coeff (i + 1) (AHser p) = ArtinHasse.coord p i := by
  rw [AHser, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]

theorem coeff_AHser_eq_coeff_prodSeries (K j : ℕ) (hj : j ≤ K) :
    PowerSeries.coeff j (AHser p) =
      PowerSeries.coeff j (ArtinHasse.prodSeries p (fun m => (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p])) (K + 1)) := by

  have hfac : ∀ (N m : ℕ), N ≤ m →
      (PowerSeries.X : PowerSeries (MvPolynomial ℕ ℤ_[p])) ^ (N + 1) ∣
        ArtinHasse.scaled p (p ^ m) (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p]) - 1 := by
    intro N m hNm
    have hpm : N + 1 ≤ p ^ m := by
      have := Nat.lt_pow_self hp.out.one_lt (n := m)
      omega
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    rw [map_sub, ArtinHasse.coeff_scaled, PowerSeries.coeff_one]
    by_cases hi0 : i = 0
    · subst hi0
      rw [if_pos (dvd_zero _), if_pos rfl, Nat.zero_div, pow_zero, mul_one,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, ArtinHasse.constantCoeff_series, map_one, sub_self]
    · rw [if_neg, if_neg hi0, sub_zero]
      intro hdvd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdvd
      omega
  rcases j with _ | j
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_AHser,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ArtinHasse.constantCoeff_prodSeries]
  · rw [coeff_AHser_succ, ArtinHasse.coord, ArtinHasse.prodSeries, ArtinHasse.prodSeries]
    have hsplit : Finset.range (K + 1) = Finset.range (j + 1) ∪ (Finset.range (K + 1) \ Finset.range (j + 1)) := by
      rw [Finset.union_sdiff_of_subset]
      exact Finset.range_subset_range.2 (by omega)
    rw [hsplit, Finset.prod_union Finset.disjoint_sdiff,
      coeff_mul_eq_of_dvd_sub_one (dvd_prod_sub_one _ _ _ fun m hm => ?_) _ le_rfl]
    have hm : j + 1 ≤ m := by
      have := (Finset.mem_sdiff.mp hm).2
      rw [Finset.mem_range, not_lt] at this
      exact this
    exact hfac (j + 1) m hm

theorem coeff_gh_AHser_pow (j : ℕ) :
    PowerSeries.coeff (p ^ j) (gh (AHser p)) =
      ∑ i ∈ Finset.range (j + 1), (p : MvPolynomial ℕ ℤ_[p]) ^ i * MvPolynomial.X i ^ (p ^ (j - i)) := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  set n : ℕ := p ^ j with hn
  have hP1 : PowerSeries.constantCoeff (ArtinHasse.prodSeries p (fun m => (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p])) (n + 1)) = 1 :=
    ArtinHasse.constantCoeff_prodSeries p _ _
  have heq := coeff_gh_eq_of_coeff_eq (constantCoeff_AHser p) hP1 n
    (fun i hi => coeff_AHser_eq_coeff_prodSeries p n i hi) n le_rfl
  rw [heq, ArtinHasse.prodSeries, gh_prod _ _ (fun m _ => ArtinHasse.constantCoeff_scaled p _ _), map_sum]
  have hterm : ∀ m ∈ Finset.range (n + 1),
      PowerSeries.coeff n (gh (ArtinHasse.scaled p (p ^ m) (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p]))) =
        if m ≤ j then (p : MvPolynomial ℕ ℤ_[p]) ^ m * MvPolynomial.X m ^ (p ^ (j - m)) else 0 := by
    intro m _
    rw [AHGhost.coeff_gh_scaled p (p ^ m) (pow_ne_zero m hp.out.ne_zero)]
    by_cases hm : m ≤ j
    · have hdvd : p ^ m ∣ n := by rw [hn]; exact pow_dvd_pow p hm
      have hdiv : n / p ^ m = p ^ (j - m) := by rw [hn, Nat.pow_div hm hp.out.pos]
      rw [if_pos ⟨hdvd, ⟨j - m, hdiv⟩⟩, if_pos hm, hdiv, Nat.cast_pow]
    · rw [if_neg, if_neg hm]
      rintro ⟨hdvd, -⟩
      rw [hn, Nat.pow_dvd_pow_iff_le_right hp1] at hdvd
      exact hm hdvd
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, hm⟩; omega
  · intro hm
    have : j < n + 1 := by
      rw [hn]; exact Nat.lt_succ_of_le (Nat.lt_pow_self hp1).le
    omega

theorem coeff_gh_AHser_of_not_pow (n : ℕ) (hn : ¬ ∃ j, n = p ^ j) :
    PowerSeries.coeff n (gh (AHser p)) = 0 := by
  classical
  have hP1 : PowerSeries.constantCoeff (ArtinHasse.prodSeries p (fun m => (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p])) (n + 1)) = 1 :=
    ArtinHasse.constantCoeff_prodSeries p _ _
  have heq := coeff_gh_eq_of_coeff_eq (constantCoeff_AHser p) hP1 n
    (fun i hi => coeff_AHser_eq_coeff_prodSeries p n i hi) n le_rfl
  rw [heq, ArtinHasse.prodSeries, gh_prod _ _ (fun m _ => ArtinHasse.constantCoeff_scaled p _ _), map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [AHGhost.coeff_gh_scaled p (p ^ m) (pow_ne_zero m hp.out.ne_zero), if_neg]
  rintro ⟨hdvd, ⟨i, hi⟩⟩
  apply hn
  refine ⟨m + i, ?_⟩
  rw [pow_add, ← hi, Nat.mul_div_cancel' hdvd]

abbrev U : Type := MvPolynomial ℕ ℤ_[p]

abbrev ιU : MvPolynomial ℕ ℤ →+* U p := MvPolynomial.map (Int.castRingHom ℤ_[p])

abbrev πU (k : ℕ) : U p := ιU p (projPoly p k)

abbrev eU (i : ℕ) : U p := MvPolynomial.aeval (πU p) (ArtinHasse.coord p i)

abbrev ZU : PowerSeries (U p) := PowerSeries.map (ιU p) genSeries

abbrev EU : PowerSeries (U p) := PowerSeries.map (MvPolynomial.aeval (πU p)).toRingHom (AHser p)

theorem constantCoeff_ZU : PowerSeries.constantCoeff (ZU p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, coeff_genSeries_zero, map_one]

theorem constantCoeff_EU : PowerSeries.constantCoeff (EU p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_AHser, map_one]

theorem coeff_EU_succ (i : ℕ) : PowerSeries.coeff (i + 1) (EU p) = eU p i := by
  rw [PowerSeries.coeff_map, coeff_AHser_succ]; rfl

theorem coeff_gh_ZU_pow (j : ℕ) :
    PowerSeries.coeff (p ^ j) (gh (ZU p)) =
      ∑ i ∈ Finset.range (j + 1), (p : U p) ^ i * πU p i ^ (p ^ (j - i)) := by
  have hpj : p ^ j ≠ 0 := pow_ne_zero j hp.out.ne_zero
  rw [← map_gh _ constantCoeff_genSeries, PowerSeries.coeff_map, coeff_gh_genSeries (p ^ j) hpj, map_sum]

  symm
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p ^ j)) (fun k => (k + 1) ∣ p ^ j)]
  rw [Finset.sum_eq_zero (s := Finset.filter (fun k => ¬ (k + 1) ∣ p ^ j) _) (fun k hk => by
    rw [if_neg (Finset.mem_filter.mp hk).2, map_zero]), add_zero]
  refine Finset.sum_bij (fun i _ => p ^ i - 1) (fun i hi => ?_) (fun i₁ h₁ i₂ h₂ h => ?_) (fun k hk => ?_)
    (fun i hi => ?_)
  · beta_reduce
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have h1 := Nat.one_le_pow i p hp.out.pos
      have h2 := Nat.pow_le_pow_right hp.out.pos hi'
      show p ^ i - 1 < p ^ j
      omega
    · show (p ^ i - 1 + 1) ∣ p ^ j
      rw [Nat.sub_add_cancel (Nat.one_le_pow i p hp.out.pos)]
      exact pow_dvd_pow p hi'
  · beta_reduce at h
    have h1 := Nat.one_le_pow i₁ p hp.out.pos
    have h2 := Nat.one_le_pow i₂ p hp.out.pos
    have h' : p ^ i₁ - 1 = p ^ i₂ - 1 := h
    have : p ^ i₁ = p ^ i₂ := by omega
    exact Nat.pow_right_injective hp.out.two_le this
  · obtain ⟨hk, hdvd⟩ := Finset.mem_filter.mp hk
    obtain ⟨i, hi, hki⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    refine ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), ?_⟩
    show p ^ i - 1 = k
    rw [← hki, Nat.add_sub_cancel]
  · beta_reduce
    have h1 := Nat.one_le_pow i p hp.out.pos
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    show _ = (ιU p) (if (p ^ i - 1 + 1) ∣ p ^ j then
      ((p ^ i - 1 + 1 : ℕ) : MvPolynomial ℕ ℤ) * wittCoord (p ^ i - 1) ^ (p ^ j / (p ^ i - 1 + 1)) else 0)
    rw [Nat.sub_add_cancel h1, if_pos (pow_dvd_pow p hi'), map_mul, map_pow, map_natCast,
      Nat.pow_div hi' hp.out.pos, Nat.cast_pow]
    rfl

open Classical in

theorem coeff_gh_EU (n : ℕ) :
    PowerSeries.coeff n (gh (EU p)) = if ∃ j, n = p ^ j then PowerSeries.coeff n (gh (ZU p)) else 0 := by
  rw [← map_gh _ (constantCoeff_AHser p), PowerSeries.coeff_map]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    rw [coeff_gh_AHser_pow, coeff_gh_ZU_pow, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, map_natCast]
    change _ * (MvPolynomial.aeval (πU p) (MvPolynomial.X i)) ^ _ = _
    rw [MvPolynomial.aeval_X]
  · rw [coeff_gh_AHser_of_not_pow p n h, map_zero]

scoped instance : IsAddTorsionFree (U p) := inferInstance

end Projector
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam.LambdaGhost"

end LambdaGhost
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam.LambdaGhost"

namespace LambdaGhost

section ProjectorIdentities

open MvFormalGroup MvFormalGroup.BigWittLaw MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]

theorem not_pow_mul {m : ℕ} (hm : ¬ ∃ j, m = p ^ j) (k : ℕ) (hk : k ≠ 0) : ¬ ∃ j, m * k = p ^ j := by
  rintro ⟨j, hj⟩
  have hdvd : m ∣ p ^ j := ⟨k, hj.symm⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  exact hm ⟨i, rfl⟩

theorem pow_mul_iff (n : ℕ) : (∃ j, p * n = p ^ j) ↔ ∃ j, n = p ^ j := by
  constructor
  · rintro ⟨j, hj⟩
    have hdvd : n ∣ p ^ j := ⟨p, by rw [mul_comm]; exact hj.symm⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    exact ⟨i, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j + 1, by rw [pow_succ, mul_comm]⟩

abbrev ψe : MvPolynomial ℕ ℤ →+* U p := (MvPolynomial.aeval (eU p)).toRingHom.comp (ιU p)

theorem map_ψe_genSeries : PowerSeries.map (ψe p) genSeries = EU p := by
  refine ext_succ (constantCoeff_map_of _ constantCoeff_genSeries) (constantCoeff_EU p) fun i => ?_
  rw [PowerSeries.coeff_map, coeff_genSeries_succ, coeff_EU_succ]
  simp

abbrev FeU (m : ℕ) : PowerSeries (U p) := PowerSeries.map (ψe p) (frobSeries m)

theorem constantCoeff_FeU (m : ℕ) : PowerSeries.constantCoeff (FeU p m) = 1 :=
  constantCoeff_map_of _ (constantCoeff_frobSeries m)

theorem coeff_FeU_succ (m k : ℕ) :
    PowerSeries.coeff (k + 1) (FeU p m) = MvPolynomial.aeval (eU p) (ιU p (frobPoly m k)) := by
  rw [PowerSeries.coeff_map, coeff_frobSeries_succ]; rfl

open Classical in
theorem coeff_gh_FeU {m : ℕ} (hm : 0 < m) (k : ℕ) :
    PowerSeries.coeff k (gh (FeU p m)) =
      if ∃ j, m * k = p ^ j then PowerSeries.coeff (m * k) (gh (ZU p)) else 0 := by
  rw [← map_gh _ (constantCoeff_frobSeries m), PowerSeries.coeff_map, coeff_gh_frobSeries hm,
    ← PowerSeries.coeff_map, map_gh _ constantCoeff_genSeries, map_ψe_genSeries, coeff_gh_EU]

theorem FeU_eq_one {m : ℕ} (hm : ¬ ∃ j, m = p ^ j) : FeU p m = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine ext_succ (constantCoeff_FeU p 0) (by simp) fun k => ?_
    rw [coeff_FeU_succ, frobPoly_zero_left, map_zero, map_zero, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k)]
  · apply eq_of_gh_eq (constantCoeff_FeU p m) (by simp)
    rw [gh_one]
    ext k
    rw [coeff_gh_FeU p hm0, map_zero]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [mul_zero, coeff_zero_gh]; split_ifs <;> rfl
    · rw [if_neg (not_pow_mul p hm k hk.ne')]

theorem aeval_eU_frobPoly_eq_zero {m : ℕ} (hm : ¬ ∃ j, m = p ^ j) (k : ℕ) :
    MvPolynomial.aeval (eU p) (ιU p (frobPoly m k)) = 0 := by
  rw [← coeff_FeU_succ, FeU_eq_one p hm, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k)]

abbrev ψF : MvPolynomial ℕ ℤ →+* U p :=
  (MvPolynomial.aeval fun j => ιU p (frobPoly p j)).toRingHom.comp (ιU p)

abbrev FZU : PowerSeries (U p) := PowerSeries.map (ιU p) (frobSeries p)

theorem map_ψF_genSeries : PowerSeries.map (ψF p) genSeries = FZU p := by
  refine ext_succ (constantCoeff_map_of _ constantCoeff_genSeries)
    (constantCoeff_map_of _ (constantCoeff_frobSeries p)) fun i => ?_
  rw [PowerSeries.coeff_map, coeff_genSeries_succ, PowerSeries.coeff_map, coeff_frobSeries_succ]
  simp

abbrev EFU : PowerSeries (U p) :=
  PowerSeries.map (MvPolynomial.aeval fun j => ιU p (frobPoly p j)).toRingHom (EU p)

theorem map_aeval_ZU :
    PowerSeries.map (MvPolynomial.aeval fun j => ιU p (frobPoly p j)).toRingHom (ZU p) = FZU p := by
  rw [← map_ψF_genSeries]
  show ((PowerSeries.map (MvPolynomial.aeval fun j => ιU p (frobPoly p j)).toRingHom).comp
    (PowerSeries.map (ιU p))) genSeries = _
  rw [← PowerSeries.map_comp]

theorem constantCoeff_EFU : PowerSeries.constantCoeff (EFU p) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_EU, map_one]

open Classical in
theorem coeff_gh_EFU (n : ℕ) :
    PowerSeries.coeff n (gh (EFU p)) = if ∃ j, n = p ^ j then PowerSeries.coeff (p * n) (gh (ZU p)) else 0 := by
  rw [← map_gh _ (constantCoeff_EU p), PowerSeries.coeff_map, coeff_gh_EU]
  split_ifs with h
  · rw [← PowerSeries.coeff_map, map_gh _ (constantCoeff_ZU p), map_aeval_ZU, ← map_gh _ (constantCoeff_frobSeries p),
      PowerSeries.coeff_map, coeff_gh_frobSeries hp.out.pos, ← PowerSeries.coeff_map, map_gh _ constantCoeff_genSeries]
  · rw [map_zero]

theorem FeU_eq_EFU : FeU p p = EFU p := by
  apply eq_of_gh_eq (constantCoeff_FeU p p) (constantCoeff_EFU p)
  ext n
  classical
  rw [coeff_gh_FeU p hp.out.pos, coeff_gh_EFU, pow_mul_iff]

theorem aeval_eU_frobPoly_p (k : ℕ) :
    MvPolynomial.aeval (eU p) (ιU p (frobPoly p k)) =
      MvPolynomial.aeval (fun j => ιU p (frobPoly p j)) (eU p k) := by
  rw [← coeff_FeU_succ, FeU_eq_EFU, PowerSeries.coeff_map, coeff_EU_succ]
  rfl

end ProjectorIdentities
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam.LambdaGhost"

section TransportK2b

open MvFormalGroup MvFormalGroup.BigWittLaw MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R]

theorem subst_coe_map_eq (g : ℕ → MvPolynomial ℕ ℤ_[p]) (Q : MvPolynomial ℕ ℤ_[p]) :
    MvPowerSeries.subst (fun i => ((MvPolynomial.map (algebraMap ℤ_[p] R) (g i) : MvPolynomial ℕ R) : MvPowerSeries ℕ R))
        ((MvPolynomial.map (algebraMap ℤ_[p] R) Q : MvPolynomial ℕ R) : MvPowerSeries ℕ R) =
      ((MvPolynomial.map (algebraMap ℤ_[p] R) (MvPolynomial.aeval g Q) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
  rw [MvPowerSeries.subst_coe]
  let ψ₁ : MvPolynomial ℕ ℤ_[p] →+* MvPowerSeries ℕ R :=
    (MvPolynomial.aeval fun i => ((MvPolynomial.map (algebraMap ℤ_[p] R) (g i) : MvPolynomial ℕ R) :
      MvPowerSeries ℕ R)).toRingHom.comp (MvPolynomial.map (algebraMap ℤ_[p] R))
  let ψ₂ : MvPolynomial ℕ ℤ_[p] →+* MvPowerSeries ℕ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := ℕ) (R := R)).comp
      ((MvPolynomial.map (algebraMap ℤ_[p] R)).comp (MvPolynomial.aeval g).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp [ψ₁, ψ₂, MvPolynomial.algebraMap_eq]
      rw [MvPowerSeries.c_eq_algebraMap]
    · simp [ψ₁, ψ₂]
  exact RingHom.congr_fun hψ Q

theorem map_ιU (P : MvPolynomial ℕ ℤ) :
    MvPolynomial.map (algebraMap ℤ_[p] R) (ιU p P) = MvPolynomial.map (Int.castRingHom R) P := by
  show MvPolynomial.map (algebraMap ℤ_[p] R) (MvPolynomial.map (Int.castRingHom ℤ_[p]) P) = _
  rw [MvPolynomial.map_map (Int.castRingHom ℤ_[p]) (algebraMap ℤ_[p] R) P,
    RingHom.ext_int ((algebraMap ℤ_[p] R).comp (Int.castRingHom ℤ_[p])) (Int.castRingHom R)]

theorem toFam_eq (P : MvPolynomial ℕ ℤ) :
    toFam R P = ((MvPolynomial.map (algebraMap ℤ_[p] R) (ιU p P) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
  rw [toFam, map_ιU]

theorem projFam_eq :
    projFam R p = fun k => ((MvPolynomial.map (algebraMap ℤ_[p] R) (πU p k) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
  funext k
  exact toFam_eq p R (projPoly p k)

theorem eR_eq (i : ℕ) :
    MvPowerSeries.subst (projFam R p)
        ((MvPolynomial.map (algebraMap ℤ_[p] R) (ArtinHasse.coord p i) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) =
      ((MvPolynomial.map (algebraMap ℤ_[p] R) (eU p i) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
  rw [projFam_eq, subst_coe_map_eq]

end TransportK2b
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam.LambdaGhost"

end LambdaGhost
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam.LambdaGhost"

end
p2m_reactivate "P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam.LambdaGhost"

open MvFormalGroup MvFormalGroup.BigWittLaw in
theorem solution
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] :
    (∀ m : ℕ, (¬ ∃ k : ℕ, m = p ^ k) → ∀ k : ℕ,
      MvPowerSeries.subst
        (fun i => MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p)
          ((↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p i)) : MvPowerSeries ℕ R)))
        (MvFormalGroup.BigWittLaw.frobFam R m k) = 0) ∧
    (∀ k : ℕ,
      MvPowerSeries.subst
        (fun i => MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p)
          ((↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p i)) : MvPowerSeries ℕ R)))
        (MvFormalGroup.BigWittLaw.frobFam R p k)
      = MvPowerSeries.subst (MvFormalGroup.BigWittLaw.frobFam R p)
          (MvPowerSeries.subst (MvFormalGroup.BigWittLaw.projFam R p)
            ((↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p k)) : MvPowerSeries ℕ R)))) := by
  have he : (fun i => MvPowerSeries.subst (projFam R p)
      ((↑(MvPolynomial.map (algebraMap ℤ_[p] R) (ArtinHasse.coord p i)) : MvPowerSeries ℕ R))) =
      fun i => ((MvPolynomial.map (algebraMap ℤ_[p] R) (LambdaGhost.eU p i) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) :=
    funext fun i => LambdaGhost.eR_eq p R i
  have hF : ∀ m k, frobFam R m k =
      ((MvPolynomial.map (algebraMap ℤ_[p] R) (LambdaGhost.ιU p (frobPoly m k)) : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := fun m k => LambdaGhost.toFam_eq p R (frobPoly m k)
  refine ⟨fun m hm k => ?_, fun k => ?_⟩
  · rw [he, hF, LambdaGhost.subst_coe_map_eq, LambdaGhost.aeval_eU_frobPoly_eq_zero p hm k, map_zero,
      MvPolynomial.coe_zero]
  · rw [he, hF, LambdaGhost.subst_coe_map_eq, LambdaGhost.aeval_eU_frobPoly_p, LambdaGhost.eR_eq,
      show frobFam R p = fun j => ((MvPolynomial.map (algebraMap ℤ_[p] R) (LambdaGhost.ιU p (frobPoly p j)) :
        MvPolynomial ℕ R) : MvPowerSeries ℕ R) from funext fun j => hF p j,
      LambdaGhost.subst_coe_map_eq]

end S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam
end P2MW
export P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_projFam_frobFam (solution)
