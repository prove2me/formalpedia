-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.finsum_torusResidue_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:41:23.15943+00:00
-- url     : https://prove2.me/submissions/80eac227-43d2-4588-b7e0-ffb0a3cecb21

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Theorems.Thm_GroundTheory_Global_Elliptic_torusResidue_mk
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic____ne_zero_e23ca4e0a06a
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_im____div____ne_zero_771d9968722c
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_analyticAt_add_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_Torus_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_inter_singularSet
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_eq_sum_residue
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_eq_zero_of_periodic
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_comp_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_zero_of_analyticAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped Interval Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, torusResidue L f x = 0 := by
  classical
  obtain ⟨hmer, hper⟩ := hf
  have hω₁ : L.ω₁ ≠ 0 := ω₁_ne_zero L
  set c := L.ω₁ with hc_def
  have hc : c ≠ 0 := ω₁_ne_zero L
  have hcL : c ∈ L.lattice := L.ω₁_mem_lattice
  obtain ⟨τ, s, hs, hω₂, hτ⟩ : ∃ τ : ℂ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      L.ω₂ = (s : ℂ) * (c * τ) ∧ 0 < τ.im := by
    rcases lt_or_gt_of_ne (im_ω₂_div_ω₁_ne_zero L) with h | h
    · refine ⟨-(L.ω₂ / L.ω₁), -1, Or.inr rfl, ?_, by simpa using h⟩
      rw [hc_def]
      have h0 := ω₁_ne_zero L
      field_simp
      push_cast
      ring
    · refine ⟨L.ω₂ / L.ω₁, 1, Or.inl rfl, ?_, h⟩
      rw [hc_def]
      have h0 := ω₁_ne_zero L
      field_simp
      push_cast
      ring
  have hτL : c * τ ∈ L.lattice := by
    have h2 := L.ω₂_mem_lattice
    rcases hs with rfl | rfl
    · simpa [hω₂] using h2
    · simpa [hω₂] using L.lattice.neg_mem h2
  set h := τ.im with hh
  set g : ℂ → ℂ := fun w ↦ f (c * w) with hg_def
  have hg1 : ∀ u, g (u + 1) = g u := fun u ↦ by
    simp only [hg_def, mul_add, mul_one]
    exact hper _ _ hcL
  have hgτ : ∀ u, g (u + τ) = g u := fun u ↦ by
    simp only [hg_def, mul_add]
    exact hper _ _ hτL
  have hgmer : Meromorphic g := fun w ↦
    (hmer (c * w)).comp_analyticAt (g := fun w ↦ c * w) (by fun_prop)

  have hScount : (singularSet g).Countable := by
    have e : singularSet g = ⋃ n : ℕ, Metric.closedBall (0 : ℂ) n ∩ singularSet g := by
      ext z
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
        exact ⟨n, hn, hz⟩
      · rintro ⟨n, -, hz⟩
        exact hz
    rw [e]
    exact countable_iUnion fun n ↦
      (finite_inter_singularSet hgmer (isCompact_closedBall 0 (n : ℝ))).countable

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ ((fun s : ℂ ↦ s.re) '' singularSet g ∪
      (fun s : ℂ ↦ s.re - 1) '' singularSet g)ᶜ :=
    (((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ ∈ ((fun s : ℂ ↦ s.im) '' singularSet g ∪
      (fun s : ℂ ↦ s.im - h) '' singularSet g)ᶜ :=
    (((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty
  set a : ℂ := x₀ + y₀ * I with ha
  set b : ℂ := a + 1 + h * I with hb
  have ha_re : a.re = x₀ := by simp [ha]
  have ha_im : a.im = y₀ := by simp [ha]
  have hb_re : b.re = x₀ + 1 := by simp [hb, ha]
  have hb_im : b.im = y₀ + h := by simp [hb, ha]
  set K : Set ℂ := [[a.re, b.re]] ×ℂ [[a.im, b.im]] with hK_def
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hKmem : ∀ u : ℂ, u ∈ K ↔ u.re ∈ Icc x₀ (x₀ + 1) ∧ u.im ∈ Icc y₀ (y₀ + h) := by
    intro u
    rw [hK_def, mem_reProdIm, ha_re, hb_re, ha_im, hb_im, uIcc_of_le (by linarith),
      uIcc_of_le (by linarith)]
  set T : Finset ℂ := (finite_inter_singularSet hgmer hK).toFinset with hT
  have hTmem : ∀ p, p ∈ T ↔ p ∈ K ∧ p ∈ singularSet g := by
    intro p
    simp [hT]

  have hTin : ∀ p ∈ T, x₀ < p.re ∧ p.re < x₀ + 1 ∧ y₀ < p.im ∧ p.im < y₀ + h := by
    intro p hp
    obtain ⟨hpK, hpS⟩ := (hTmem p).1 hp
    obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := (hKmem p).1 hpK
    have nr1 : p.re ≠ x₀ := fun e ↦ hx₀ (Or.inl ⟨p, hpS, e⟩)
    have nr2 : p.re ≠ x₀ + 1 := fun e ↦ hx₀ (Or.inr ⟨p, hpS, by simp [e]⟩)
    have ni1 : p.im ≠ y₀ := fun e ↦ hy₀ (Or.inl ⟨p, hpS, e⟩)
    have ni2 : p.im ≠ y₀ + h := fun e ↦ hy₀ (Or.inr ⟨p, hpS, by simp [e]⟩)
    exact ⟨lt_of_le_of_ne r1 (Ne.symm nr1), lt_of_le_of_ne r2 nr2,
      lt_of_le_of_ne i1 (Ne.symm ni1), lt_of_le_of_ne i2 ni2⟩

  have hsum0 : ∑ p ∈ T, residue g p = 0 := by
    have hres := rectIntegral_eq_sum_residue (f := g) (z := a) (w := b) T
      (fun p hp ↦ by
        obtain ⟨r1, r2, i1, i2⟩ := hTin p hp
        exact ⟨by rwa [ha_re], by rwa [hb_re], by rwa [ha_im], by rwa [hb_im]⟩)
      (fun p _ ↦ hgmer p)
      (fun u hu huT ↦ by
        by_contra hna
        exact huT ((hTmem u).2 ⟨hu, hna⟩))
    have hper0 : rectIntegral g a b = 0 := rectIntegral_eq_zero_of_periodic hg1 hgτ a
    rw [hper0] at hres
    have h2pi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
    exact (mul_eq_zero.1 hres.symm).resolve_left h2pi

  set φ : ℂ → Torus L := fun p ↦ Torus.mk L (c * p) with hφ
  have hlat : ∀ m n : ℤ, (m : ℂ) * c + (n : ℂ) * (c * τ) ∈ L.lattice := fun m n ↦
    L.lattice.add_mem (by simpa [zsmul_eq_mul] using L.lattice.smul_mem m hcL)
      (by simpa [zsmul_eq_mul] using L.lattice.smul_mem n hτL)

  have hsupp : Function.support (torusResidue L f) ⊆ ↑(T.image φ) := by
    intro x hx
    set z := x.out with hz
    have hxz : Torus.mk L z = x := QuotientAddGroup.out_eq' x
    have hnz : residue f z ≠ 0 := hx
    have hfz : ¬ AnalyticAt ℂ f z := fun ha ↦ hnz (residue_eq_zero_of_analyticAt ha)
    set w := z / c with hw
    set n : ℤ := ⌊(w.im - y₀) / h⌋ with hn
    set p₁ : ℂ := w - n * τ with hp₁
    set m : ℤ := ⌊p₁.re - x₀⌋ with hm
    set p : ℂ := p₁ - m with hp
    have hp_re : p.re = p₁.re - m := by simp [hp]
    have hp_im : p.im = w.im - n * h := by simp [hp, hp₁, hh]
    have hn1 := Int.floor_le ((w.im - y₀) / h)
    have hn2 := Int.lt_floor_add_one ((w.im - y₀) / h)
    have hm1 := Int.floor_le (p₁.re - x₀)
    have hm2 := Int.lt_floor_add_one (p₁.re - x₀)
    rw [← hn] at hn1 hn2
    rw [← hm] at hm1 hm2
    rw [le_div_iff₀ hτ] at hn1
    rw [div_lt_iff₀ hτ] at hn2
    have hpK : p ∈ K := by
      rw [hKmem, hp_re, hp_im]
      refine ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
    have hcp : z = c * p + ((m : ℂ) * c + (n : ℂ) * (c * τ)) := by
      simp only [hp, hp₁, hw]
      field_simp
      ring
    have hpS : p ∈ singularSet g := by
      intro hga
      apply hfz
      have h1 : AnalyticAt ℂ (fun z' ↦ g (c⁻¹ * z')) (c * p) := by
        have : AnalyticAt ℂ (fun z' ↦ c⁻¹ * z') (c * p) := by fun_prop
        exact hga.comp_of_eq this (by field_simp)
      have h2 : (fun z' ↦ g (c⁻¹ * z')) = f := by
        funext z'
        simp only [hg_def]
        congr 1
        field_simp
      rw [h2] at h1
      rw [hcp]
      exact (hper.analyticAt_add_iff (hlat m n) (c * p)).2 h1
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hTmem p).2 ⟨hpK, hpS⟩, ?_⟩)
    rw [← hxz, hφ]
    exact ((Torus.mk_eq_mk_iff L).2 (by rw [hcp]; simpa using hlat m n)).symm

  have hinj : Set.InjOn φ ↑T := by
    intro p hp q hq hpq
    obtain ⟨pr1, pr2, pi1, pi2⟩ := hTin p hp
    obtain ⟨qr1, qr2, qi1, qi2⟩ := hTin q hq
    have hdiff := (Torus.mk_eq_mk_iff L).1 hpq
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 hdiff
    have hk : p - q = (m : ℂ) + ((n * s : ℤ) : ℂ) * τ := by
      have e : c * (p - q) = c * ((m : ℂ) + ((n * s : ℤ) : ℂ) * τ) := by
        rw [mul_sub, ← hmn, hω₂]
        push_cast
        ring
      exact mul_left_cancel₀ hc e
    set k : ℤ := n * s with hkdef
    have him := congrArg Complex.im hk
    have hre := congrArg Complex.re hk
    simp only [sub_im, add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add,
      sub_re, add_re, intCast_re, mul_re, intCast_im, zero_mul, sub_zero] at him hre
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) * h < h := by rw [hh]; linarith
      have h2 : -h < (k : ℝ) * h := by rw [hh]; linarith
      have h3 : (k : ℝ) < 1 := by
        by_contra hc'
        rw [not_lt] at hc'
        nlinarith
      have h4 : (-1 : ℝ) < k := by
        by_contra hc'
        rw [not_lt] at hc'
        nlinarith
      have h5 : k < 1 := by exact_mod_cast h3
      have h6 : -1 < k := by exact_mod_cast h4
      omega
    rw [hk0] at hre him
    simp only [Int.cast_zero, zero_mul, add_zero, sub_eq_zero] at hre him
    have hm0 : m = 0 := by
      have h3 : (m : ℝ) < 1 := by linarith
      have h4 : (-1 : ℝ) < m := by linarith
      have h5 : m < 1 := by exact_mod_cast h3
      have h6 : -1 < m := by exact_mod_cast h4
      omega
    rw [hm0] at hre
    simp only [Int.cast_zero, sub_eq_zero] at hre
    exact Complex.ext hre him
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]
  have hterm : ∀ p ∈ T, torusResidue L f (φ p) = c * residue g p := by
    intro p _
    rw [hφ, torusResidue_mk ⟨hmer, hper⟩,
      show residue g p = c⁻¹ * residue f (c * p) from residue_comp_mul hc (hmer _)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum0, mul_zero]
end GroundTheory.Global.Elliptic
