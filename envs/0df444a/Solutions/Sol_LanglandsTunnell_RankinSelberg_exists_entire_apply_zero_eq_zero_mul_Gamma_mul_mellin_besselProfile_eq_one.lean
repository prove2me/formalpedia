-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fb325cab-b7dd-5855-a4d6-5e383c0cf779

import Definitions.Def_LanglandsTunnell_ArchBessel
import Theorems.Thm_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one

set_option autoImplicit false

p2m_open "MeasureTheory Set LanglandsTunnell.ArchBessel P2MW.S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one.LanglandsTunnell.ArchBessel"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ArchBessel.mellin_besselKernel_mul_besselKernel_eq"
namespace ArchBessel
p2m_export "LanglandsTunnell.ArchBessel" "besselKernel mellin_besselKernel_mul_besselKernel_eq"
namespace RecipPS
p2m_open "LanglandsTunnell.ArchBessel LanglandsTunnell"

theorem conj_besselKernel (ν : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (besselKernel ν x) = besselKernel ((starRingEnd ℂ) ν) x := by
  unfold besselKernel
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht : 0 < t := ht
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  have harg : ((t : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (t : ℂ) (ν - 1) harg
  rw [Complex.conj_ofReal] at h
  rw [← h, map_sub, map_one]

theorem normSq_besselKernel (ν : ℂ) (x : ℝ) :
    (((‖besselKernel ν x‖ ^ 2 : ℝ) : ℝ) : ℂ) = besselKernel ν x * besselKernel ((starRingEnd ℂ) ν) x := by
  rw [← conj_besselKernel, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem ofReal_norm_besselKernel_sq (ν : ℂ) (x : ℝ) :
    ((‖besselKernel ν x‖ : ℝ) : ℂ) ^ 2 = besselKernel ν x * besselKernel ((starRingEnd ℂ) ν) x := by
  rw [← Complex.ofReal_pow, normSq_besselKernel]

theorem prod_range_mul_Gamma (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    (∏ j ∈ Finset.range n, (s + j)) * Complex.Gamma s = Complex.Gamma (s + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, mul_comm _ (s + n), mul_assoc, ih, Nat.cast_succ, ← add_assoc,
      Complex.Gamma_add_one]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith

end LanglandsTunnell.ArchBessel.RecipPS

open LanglandsTunnell.ArchBessel.RecipPS in
theorem solution
    (C : ℝ) (hC : 0 < C) (a : ℕ) (ha : 1 ≤ a) (ν : ℂ) (hν : a = 1 → ν.re = 0 ∨ ν.im = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ H 0 = 0 ∧
      ∀ s : ℂ, 1 - (a : ℝ) + 2 * |ν.re| < s.re → 0 < s.re →
        H s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, (((C * |y| ^ a * ‖besselKernel ν (2 * Real.pi * |y|)‖ ^ 2 : ℝ) : ℝ) : ℂ) *
            ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
  have h2π0 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2π.ne'
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hC0 : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  set νc : ℂ := (starRingEnd ℂ) ν with hνc

  set w₁ : ℂ → ℂ := fun s => (s + (a : ℂ) - 1 + ν + νc) / 2 with hw₁
  set w₂ : ℂ → ℂ := fun s => (s + (a : ℂ) - 1 + ν - νc) / 2 with hw₂
  set w₃ : ℂ → ℂ := fun s => (s + (a : ℂ) - 1 - ν + νc) / 2 with hw₃
  set w₄ : ℂ → ℂ := fun s => (s + (a : ℂ) - 1 - ν - νc) / 2 with hw₄
  refine ⟨fun s => (C : ℂ)⁻¹ * (Real.pi : ℂ) ^ s * ((2 * Real.pi : ℝ) : ℂ) ^ (s + (a : ℂ) - 1) *
      (2 : ℂ) ^ (1 - (s + (a : ℂ) - 1)) * (∏ j ∈ Finset.range (a - 1), (s + j)) *
      ((Complex.Gamma (w₁ s))⁻¹ * (Complex.Gamma (w₂ s))⁻¹ * (Complex.Gamma (w₃ s))⁻¹ *
        (Complex.Gamma (w₄ s))⁻¹), ?_, ?_, ?_⟩
  ·
    intro s
    have hid : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
    have haff : ∀ c d : ℂ, DifferentiableAt ℂ (fun z : ℂ => (z + c) / d) s := fun c d =>
      (differentiableAt_id.add_const c).div_const d
    have hG : ∀ (c : ℂ), DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma ((z + c) / 2))⁻¹) s := by
      intro c
      have hg : DifferentiableAt ℂ (fun w : ℂ => (Complex.Gamma w)⁻¹) ((s + c) / 2) :=
        Complex.differentiable_one_div_Gamma _
      have hcomp := hg.comp s (haff c 2)
      exact hcomp
    have e₁ : (fun z : ℂ => (Complex.Gamma (w₁ z))⁻¹) = fun z => (Complex.Gamma ((z + ((a : ℂ) - 1 + ν + νc)) / 2))⁻¹ := by
      funext z; simp only [hw₁]; ring_nf
    have e₂ : (fun z : ℂ => (Complex.Gamma (w₂ z))⁻¹) = fun z => (Complex.Gamma ((z + ((a : ℂ) - 1 + ν - νc)) / 2))⁻¹ := by
      funext z; simp only [hw₂]; ring_nf
    have e₃ : (fun z : ℂ => (Complex.Gamma (w₃ z))⁻¹) = fun z => (Complex.Gamma ((z + ((a : ℂ) - 1 - ν + νc)) / 2))⁻¹ := by
      funext z; simp only [hw₃]; ring_nf
    have e₄ : (fun z : ℂ => (Complex.Gamma (w₄ z))⁻¹) = fun z => (Complex.Gamma ((z + ((a : ℂ) - 1 - ν - νc)) / 2))⁻¹ := by
      funext z; simp only [hw₄]; ring_nf
    have hΓ₁ : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma (w₁ z))⁻¹) s := by rw [e₁]; exact hG _
    have hΓ₂ : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma (w₂ z))⁻¹) s := by rw [e₂]; exact hG _
    have hΓ₃ : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma (w₃ z))⁻¹) s := by rw [e₃]; exact hG _
    have hΓ₄ : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma (w₄ z))⁻¹) s := by rw [e₄]; exact hG _
    have hp1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ z) s := hid.const_cpow (Or.inl hπ0)
    have hp2 : DifferentiableAt ℂ (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (z + (a : ℂ) - 1)) s :=
      ((hid.add_const _).sub_const _).const_cpow (Or.inl h2π0)
    have hp3 : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (1 - (z + (a : ℂ) - 1))) s :=
      (((hid.add_const _).sub_const _).const_sub _).const_cpow (Or.inl h20)
    have hP : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (a - 1), (z + j)) s := by
      have hfn : (fun z : ℂ => ∏ j ∈ Finset.range (a - 1), (z + (j : ℂ))) =
          ∏ j ∈ Finset.range (a - 1), (fun z : ℂ => z + (j : ℂ)) := (Finset.prod_fn _ _).symm
      rw [hfn]
      exact DifferentiableAt.finset_prod (fun j _ => hid.add_const _)
    exact (((((differentiableAt_const _).mul hp1).mul hp2).mul hp3).mul hP).mul
      (((hΓ₁.mul hΓ₂).mul hΓ₃).mul hΓ₄)
  ·
    beta_reduce
    rcases Nat.lt_or_ge 1 a with h2 | h1
    ·
      have hmem : 0 ∈ Finset.range (a - 1) := Finset.mem_range.mpr (by omega)
      have hP0 : ∏ j ∈ Finset.range (a - 1), ((0 : ℂ) + j) = 0 :=
        Finset.prod_eq_zero hmem (by simp)
      rw [hP0]; simp
    ·
      have ha1 : a = 1 := le_antisymm h1 ha
      rcases hν ha1 with hre | him
      · have : w₁ 0 = 0 := by
          simp only [hw₁, ha1, hνc]
          rw [show (0 : ℂ) + ((1 : ℕ) : ℂ) - 1 + ν + (starRingEnd ℂ) ν = ν + (starRingEnd ℂ) ν by push_cast; ring,
            Complex.add_conj]
          simp [hre]
        simp [this, Complex.Gamma_zero]
      · have : w₂ 0 = 0 := by
          simp only [hw₂, ha1, hνc]
          rw [show (0 : ℂ) + ((1 : ℕ) : ℂ) - 1 + ν - (starRingEnd ℂ) ν = ν - (starRingEnd ℂ) ν by push_cast; ring,
            Complex.sub_conj]
          simp [him]
        simp [this, Complex.Gamma_zero]
  · intro s hs1 hs0
    beta_reduce
    have hν0 : 0 ≤ |ν.re| := abs_nonneg _

    set s' : ℂ := s + (a : ℂ) - 1 with hs'
    have hs're : s'.re = s.re + a - 1 := by simp [hs']
    have hνcre : νc.re = ν.re := by simp [hνc]
    have hKK := LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq ν νc s'
      (by rw [hs're, hνcre]; linarith)
    obtain ⟨hconv, hval⟩ := hKK

    set G : ℝ → ℂ := fun y => (((C * |y| ^ a * ‖besselKernel ν (2 * Real.pi * |y|)‖ ^ 2 : ℝ) : ℝ) : ℂ) *
      ((|y| : ℝ) : ℂ) ^ (s - 2) with hG
    have hGeven : ∀ y : ℝ, G (-y) = G y := fun y => by simp only [hG, abs_neg]

    have hGpos : EqOn G (fun y : ℝ => (C : ℂ) • ((y : ℂ) ^ (s' - 1) •
        (besselKernel ν (2 * Real.pi * y) * besselKernel νc (2 * Real.pi * y)))) (Ioi 0) := by
      intro y hy
      have hy : 0 < y := hy
      have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      simp only [hG, abs_of_pos hy, smul_eq_mul]
      push_cast
      rw [ofReal_norm_besselKernel_sq, ← hνc]
      have e : (y : ℂ) ^ (a : ℕ) * (y : ℂ) ^ (s - 2) = (y : ℂ) ^ (s' - 1) := by
        rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hy0, hs']
        congr 1; ring
      calc (C : ℂ) * (y : ℂ) ^ a * (besselKernel ν (2 * Real.pi * y) * besselKernel νc (2 * Real.pi * y)) *
            (y : ℂ) ^ (s - 2)
          = (C : ℂ) * ((y : ℂ) ^ (a : ℕ) * (y : ℂ) ^ (s - 2)) *
            (besselKernel ν (2 * Real.pi * y) * besselKernel νc (2 * Real.pi * y)) := by ring
        _ = _ := by rw [e]; ring

    have hconv2π : MellinConvergent
        (fun y : ℝ => besselKernel ν (2 * Real.pi * y) * besselKernel νc (2 * Real.pi * y)) s' :=
      (MellinConvergent.comp_mul_left h2π).mpr hconv
    have hIoi : IntegrableOn G (Ioi 0) := by
      have h1 : IntegrableOn (fun y : ℝ => (C : ℂ) • ((y : ℂ) ^ (s' - 1) •
          (besselKernel ν (2 * Real.pi * y) * besselKernel νc (2 * Real.pi * y)))) (Ioi 0) :=
        hconv2π.smul (C : ℂ)
      exact h1.congr_fun hGpos.symm measurableSet_Ioi
    have hvalIoi : ∫ y in Ioi 0, G y = (C : ℂ) * (((2 * Real.pi : ℝ) : ℂ) ^ (-s') *
        ((2 : ℂ) ^ (s' - 1) * (Complex.Gamma ((s' + ν + νc) / 2) * Complex.Gamma ((s' + ν - νc) / 2) *
          Complex.Gamma ((s' - ν + νc) / 2) * Complex.Gamma ((s' - ν - νc) / 2)) / Complex.Gamma s')) := by
      rw [setIntegral_congr_fun measurableSet_Ioi hGpos, integral_smul, smul_eq_mul]
      congr 1
      have := mellin_comp_mul_left
        (fun x : ℝ => besselKernel ν x * besselKernel νc x) s' h2π
      rw [hval, smul_eq_mul] at this
      rw [← this]
      rfl

    have hIio : IntegrableOn G (Iio 0) := by
      have h := hIoi.comp_neg
      rw [Set.neg_Ioi, neg_zero] at h
      exact h.congr_fun (fun y _ => hGeven y) measurableSet_Iio
    have hIic : IntegrableOn G (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio).mpr hIio
    have hsplit : ∫ y : ℝ, G y = 2 * ∫ y in Ioi 0, G y := by
      have hu : (Iic (0 : ℝ) ∪ Ioi 0) = univ := Iic_union_Ioi
      rw [← setIntegral_univ, ← hu, setIntegral_union (Set.disjoint_left.mpr fun x hx hx' =>
        not_lt.mpr (mem_Iic.mp hx) (mem_Ioi.mp hx')) measurableSet_Ioi hIic hIoi]
      have hneg : ∫ y in Iic 0, G y = ∫ y in Ioi 0, G y := by
        have h := integral_comp_neg_Iic 0 G
        rw [neg_zero] at h
        rw [← h]
        exact setIntegral_congr_fun measurableSet_Iic (fun y _ => (hGeven y).symm)
      rw [hneg]; ring

    rw [hsplit, hvalIoi]

    have hfac : (∏ j ∈ Finset.range (a - 1), (s + j)) * Complex.Gamma s = Complex.Gamma s' := by
      rw [prod_range_mul_Gamma s hs0 (a - 1), hs']
      congr 1
      rw [Nat.cast_sub ha]; push_cast; ring

    have hΓs : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
    have hΓs' : Complex.Gamma s' ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hs're]; linarith)
    have hre1 : 0 < ((s' + ν + νc) / 2).re := by
      simp [hs', hνc]; have := neg_abs_le ν.re; linarith
    have hre2 : 0 < ((s' + ν - νc) / 2).re := by
      simp [hs', hνc]; linarith
    have hre3 : 0 < ((s' - ν + νc) / 2).re := by
      simp [hs', hνc]; linarith
    have hre4 : 0 < ((s' - ν - νc) / 2).re := by
      simp [hs', hνc]; have := le_abs_self ν.re; linarith
    have hΓ1 := Complex.Gamma_ne_zero_of_re_pos hre1
    have hΓ2 := Complex.Gamma_ne_zero_of_re_pos hre2
    have hΓ3 := Complex.Gamma_ne_zero_of_re_pos hre3
    have hΓ4 := Complex.Gamma_ne_zero_of_re_pos hre4
    have hw1s : w₁ s = (s' + ν + νc) / 2 := by simp only [hw₁, hs']
    have hw2s : w₂ s = (s' + ν - νc) / 2 := by simp only [hw₂, hs']
    have hw3s : w₃ s = (s' - ν + νc) / 2 := by simp only [hw₃, hs']
    have hw4s : w₄ s = (s' - ν - νc) / 2 := by simp only [hw₄, hs']
    have hP1 : (Real.pi : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hπ0)
    have hP2 : ((2 * Real.pi : ℝ) : ℂ) ^ s' ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h2π0)
    have hP3 : (2 : ℂ) ^ (s' - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h20)
    have hPne : (∏ j ∈ Finset.range (a - 1), (s + (j : ℂ))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr (fun j _ h => ?_)
      have := congrArg Complex.re h
      simp at this
      linarith
    simp only [hw1s, hw2s, hw3s, hw4s]
    rw [← hfac, Complex.cpow_neg, Complex.cpow_neg,
      show (1 - s' : ℂ) = -(s' - 1) by ring, Complex.cpow_neg]
    field_simp

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_besselProfile_eq_one (solution)
