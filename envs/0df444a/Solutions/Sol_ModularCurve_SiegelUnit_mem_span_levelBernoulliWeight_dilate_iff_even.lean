-- Prove2me | solution 1 for ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/638e4d5b-1942-51e6-9e17-994a4fe5c582

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset Real

namespace Ws47
namespace BSpan

def wt (N : ℕ) (t : ℕ) : ℤ := 6 * (t : ℤ) ^ 2 - 6 * (N : ℤ) * (t : ℤ) + (N : ℤ) ^ 2

theorem wt_cast (N t : ℕ) : (wt N t : ℝ) = 6 * (t : ℝ) ^ 2 - 6 * (N : ℝ) * t + (N : ℝ) ^ 2 := by
  unfold wt; push_cast; ring

theorem eval_map_bernoulli_two (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval x = x ^ 2 - x + 1 / 6 := by
  simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_one, bernoulli_two, Polynomial.eval_monomial]
  ring

theorem hasSum_cos_div_sq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * x)) (π ^ 2 * (x ^ 2 - x + 1 / 6)) := by
  have h := hasSum_one_div_nat_pow_mul_cos one_ne_zero hx
  rw [show 2 * 1 = 2 from rfl, eval_map_bernoulli_two] at h
  have e : ((-1 : ℝ) ^ (1 + 1) * (2 * π) ^ 2 / 2 / ((Nat.factorial 2 : ℕ) : ℝ)) = π ^ 2 := by
    norm_num [Nat.factorial]; ring
  rw [e] at h
  exact h

theorem hasSum_cos_wt (N t : ℕ) (hN : N ≠ 0) (ht : t ≤ N) :
    HasSum (fun n : ℕ => 6 * (N : ℝ) ^ 2 / π ^ 2 * (1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * (t / N))))
      (wt N t : ℝ) := by
  have hx : (t : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    exact ⟨by positivity, by rw [div_le_one hNpos]; exact_mod_cast ht⟩
  have h := (hasSum_cos_div_sq hx).mul_left (6 * (N : ℝ) ^ 2 / π ^ 2)
  convert h using 1
  · rfl
  rw [wt_cast]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp

variable {N : ℕ} [NeZero N]

noncomputable def cosZ (a : ZMod N) : ℝ := Real.cos (2 * π * a.val / N)

theorem cosZ_intCast (m : ℤ) : cosZ ((m : ZMod N)) = Real.cos (2 * π * m / N) := by
  unfold cosZ
  have hval : (((m : ZMod N).val : ℤ)) = m % (N : ℤ) := ZMod.val_intCast m
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hdecomp : (m : ℝ) = (N : ℝ) * ((m / (N : ℤ) : ℤ) : ℝ) + (((m : ZMod N).val : ℕ) : ℝ) := by
    have := Int.mul_ediv_add_emod m N
    have h2 : ((((m : ZMod N).val : ℕ) : ℤ) : ℝ) = (((m : ZMod N).val : ℕ) : ℝ) := by norm_cast
    rw [← h2, hval]
    exact_mod_cast this.symm
  rw [hdecomp]
  rw [show 2 * π * ((N : ℝ) * ((m / (N : ℤ) : ℤ) : ℝ) + (((m : ZMod N).val : ℕ) : ℝ)) / N
      = 2 * π * (((m : ZMod N).val : ℕ) : ℝ) / N + ((m / (N : ℤ) : ℤ) : ℝ) * (2 * π) by field_simp; ring]
  rw [Real.cos_add_int_mul_two_pi]

theorem cosZ_natCast (m : ℕ) : cosZ ((m : ZMod N)) = Real.cos (2 * π * m / N) := by
  have := cosZ_intCast (N := N) (m : ℤ)
  push_cast at this
  exact this

theorem cos_nat_mul_eq_cosZ (n : ℕ) (a : ZMod N) :
    Real.cos (2 * π * n * (a.val / N)) = cosZ ((n : ZMod N) * a) := by
  rw [← ZMod.natCast_zmod_val a, ← Nat.cast_mul, cosZ_natCast, ZMod.natCast_zmod_val]
  push_cast
  ring_nf

theorem cosZ_neg (a : ZMod N) : cosZ (-a) = cosZ a := by
  unfold cosZ
  rw [ZMod.neg_val]
  split_ifs with h
  · subst h; simp
  · have hle : a.val ≤ N := (ZMod.val_lt a).le
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    rw [Nat.cast_sub hle, show 2 * π * ((N : ℝ) - (a.val : ℝ)) / N = 2 * π - 2 * π * (a.val : ℝ) / N by
      field_simp, Real.cos_two_pi_sub]

end Ws47.BSpan

namespace Ws47
namespace BSpan

open Finset Real

variable {N : ℕ} [NeZero N]

noncomputable def psi (g : ZMod N → ℝ) (k : ZMod N) : ℝ := ∑ r : ZMod N, g r * cosZ (k * r)

theorem abs_psi_le (g : ZMod N → ℝ) (k : ZMod N) : |psi g k| ≤ ∑ r : ZMod N, |g r| := by
  unfold psi
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem tsum_psi_div_sq_eq_zero (g : ZMod N → ℝ)
    (horth : ∀ s : ZMod N, ∑ r : ZMod N, g r * (wt N (s * r).val : ℝ) = 0) (s : ZMod N) :
    ∑' n : ℕ, psi g ((n : ZMod N) * s) / (n : ℝ) ^ 2 = 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  have hsum : ∀ r : ZMod N, HasSum (fun n : ℕ => 6 * (N : ℝ) ^ 2 / π ^ 2 *
      (1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * (((s * r).val : ℝ) / N)))) (wt N (s * r).val : ℝ) :=
    fun r => hasSum_cos_wt N (s * r).val hN (ZMod.val_lt _).le
  have h1 : HasSum (fun n : ℕ => ∑ r : ZMod N, g r * (6 * (N : ℝ) ^ 2 / π ^ 2 *
      (1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * (((s * r).val : ℝ) / N)))))
      (∑ r : ZMod N, g r * (wt N (s * r).val : ℝ)) :=
    hasSum_sum fun r _ => (hsum r).mul_left (g r)
  rw [horth s] at h1
  have h2 : (fun n : ℕ => ∑ r : ZMod N, g r * (6 * (N : ℝ) ^ 2 / π ^ 2 *
      (1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * (((s * r).val : ℝ) / N))))) =
      fun n : ℕ => 6 * (N : ℝ) ^ 2 / π ^ 2 * (psi g ((n : ZMod N) * s) / (n : ℝ) ^ 2) := by
    funext n
    simp only [psi, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [cos_nat_mul_eq_cosZ, mul_assoc ((n : ℕ) : ZMod N) s r]
    ring
  rw [h2] at h1
  have h3 := h1.tsum_eq
  rw [tsum_mul_left] at h3
  have hc : 6 * (N : ℝ) ^ 2 / π ^ 2 ≠ 0 := by
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    positivity
  exact (mul_eq_zero.mp h3).resolve_left hc

theorem summable_psi_div_sq (g : ZMod N → ℝ) (s : ZMod N) :
    Summable fun n : ℕ => psi g ((n : ZMod N) * s) / (n : ℝ) ^ 2 := by
  refine Summable.of_norm_bounded ((summable_one_div_nat_pow.mpr one_lt_two).mul_left (∑ r : ZMod N, |g r|))
    fun n => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2), one_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (abs_psi_le g _) (by positivity)

theorem psi_zero_eq_zero (g : ZMod N → ℝ)
    (horth : ∀ s : ZMod N, ∑ r : ZMod N, g r * (wt N (s * r).val : ℝ) = 0) : psi g 0 = 0 := by
  have h := tsum_psi_div_sq_eq_zero g horth 0
  simp only [mul_zero] at h
  have hz : ∑' n : ℕ, psi g 0 / (n : ℝ) ^ 2 = psi g 0 * (π ^ 2 / 6) := by
    rw [← hasSum_zeta_two.tsum_eq, ← tsum_mul_left]
    exact tsum_congr fun n => by ring
  rw [hz] at h
  have : π ^ 2 / 6 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h).resolve_right this

noncomputable def Zres (M : ℕ) (c : ZMod M) : ℝ := ∑' m : ℕ, 1 / ((c.val + M * m : ℕ) : ℝ) ^ 2

theorem summable_Zres (M : ℕ) [NeZero M] (c : ZMod M) :
    Summable fun m : ℕ => 1 / ((c.val + M * m : ℕ) : ℝ) ^ 2 := by
  have hinj : Function.Injective fun m : ℕ => c.val + M * m := by
    intro a b h
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    simpa [Nat.add_left_cancel_iff, Nat.mul_left_cancel_iff hM] using h
  exact (summable_one_div_nat_pow.mpr one_lt_two).comp_injective hinj

omit [NeZero N] in

theorem natCast_mul_eq_of_mod (k : ZMod N) (x : ℕ) :
    ((x : ℕ) : ZMod N) * k = (((x % addOrderOf k : ℕ) : ℕ) : ZMod N) * k := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, mod_addOrderOf_nsmul]

theorem tsum_psi_eq_sum_residues (g : ZMod N → ℝ) (k : ZMod N) (M : ℕ) [NeZero M] (hM : addOrderOf k = M)
    (u : ℕ) :
    ∑' n : ℕ, psi g ((n : ZMod N) * (((u : ℕ) : ZMod N) * k)) / (n : ℝ) ^ 2 =
      ∑ c : ZMod M, psi g ((((c * (u : ZMod M)).val : ℕ) : ZMod N) * k) * Zres M c := by
  rw [Nat.sumByResidueClasses (summable_psi_div_sq g (((u : ℕ) : ZMod N) * k)) M]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hval : ∀ m : ℕ, psi g ((((c.val + M * m : ℕ) : ℕ) : ZMod N) * (((u : ℕ) : ZMod N) * k)) =
      psi g ((((c * (u : ZMod M)).val : ℕ) : ZMod N) * k) := by
    intro m
    have hidx : ((c.val + M * m) * u) % M = (c * (u : ZMod M)).val := by
      rw [ZMod.val_mul, ZMod.val_natCast, add_mul, mul_assoc, Nat.add_mul_mod_self_left, Nat.mul_mod,
        Nat.mul_mod c.val (u % M), Nat.mod_mod]
    rw [← mul_assoc, ← Nat.cast_mul, natCast_mul_eq_of_mod k, hM, hidx]
  simp_rw [hval]
  rw [Zres, ← tsum_mul_left]
  exact tsum_congr fun m => by ring

theorem sum_units_eq_sum {M : ℕ} [NeZero M] (F : ZMod M → ℂ) (hF : ∀ c : ZMod M, ¬ IsUnit c → F c = 0) :
    ∑ u : (ZMod M)ˣ, F u = ∑ c : ZMod M, F c := by
  classical
  have hinj : Set.InjOn (fun u : (ZMod M)ˣ => (u : ZMod M)) ↑(Finset.univ : Finset (ZMod M)ˣ) :=
    fun u _ v _ h => Units.ext h
  rw [← Finset.sum_image hinj]
  refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => hF c ?_
  rintro ⟨u, rfl⟩
  exact hc (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)

open Complex in

theorem sum_char_mul_Zres (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) :
    ∑ c : ZMod M, χ c * (Zres M c : ℂ) = LSeries (fun n : ℕ => χ (n : ZMod M)) 2 := by
  have hs : Summable fun n : ℕ => χ (n : ZMod M) / ((n : ℂ)) ^ 2 := by
    refine Summable.of_norm_bounded (summable_one_div_nat_pow.mpr one_lt_two) fun n => ?_
    rw [norm_div, norm_pow, Complex.norm_natCast, one_div, div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  have hL : LSeries (fun n : ℕ => χ (n : ZMod M)) 2 = ∑' n : ℕ, χ (n : ZMod M) / ((n : ℂ)) ^ 2 := by
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn.ne', show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  rw [hL, Nat.sumByResidueClasses hs M]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Zres, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have : ((c.val + M * m : ℕ) : ZMod M) = c := by
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]
  rw [this]
  push_cast
  ring

open Complex in

theorem eq_zero_of_forall_sum_char_inv_mul_eq_zero (M : ℕ) [NeZero M] (a : ZMod M → ℂ)
    (h : ∀ χ : DirichletCharacter ℂ M, ∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * a v = 0)
    (b : (ZMod M)ˣ) : a b = 0 := by
  have hswap : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M) * ∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * a v
      = ∑ v : (ZMod M)ˣ, (∑ χ : DirichletCharacter ℂ M, χ ((v : ZMod M)⁻¹) * χ (b : ZMod M)) * a v := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun χ _ => ?_
    rw [ZMod.inv_coe_unit]
    ring
  have key : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M) * ∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * a v
      = (M.totient : ℂ) * a b := by
    rw [hswap]
    simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit _) (b : ZMod M)]
    rw [Finset.sum_eq_single b]
    · simp
    · intro v _ hv
      rw [if_neg (fun h' => hv (Units.ext h')), zero_mul]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have hzero : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M) *
      ∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * a v = 0 :=
    Finset.sum_eq_zero fun χ _ => by rw [h χ, mul_zero]
  rw [key] at hzero
  have htot : (M.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
  exact (mul_eq_zero.mp hzero).resolve_left htot

open Complex in

theorem eq_zero_of_convolution (M : ℕ) [NeZero M] (a : ZMod M → ℝ)
    (hnu : ∀ c : ZMod M, ¬ IsUnit c → a c = 0)
    (hconv : ∀ u : (ZMod M)ˣ, ∑ c : ZMod M, a (c * u) * Zres M c = 0) (b : (ZMod M)ˣ) : a b = 0 := by
  set A : ZMod M → ℂ := fun c => (a c : ℂ) with hA
  suffices hAb : A b = 0 by simpa [hA] using hAb
  refine eq_zero_of_forall_sum_char_inv_mul_eq_zero M A (fun χ => ?_) b
  have hL : LSeries (fun n : ℕ => χ (n : ZMod M)) 2 ≠ 0 :=
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ (by norm_num)

  have hconvU : ∀ u : (ZMod M)ˣ, ∑ c : (ZMod M)ˣ, A ((c : ZMod M) * u) * (Zres M c : ℂ) = 0 := by
    intro u
    have h := congrArg (fun x : ℝ => (x : ℂ)) (hconv u)
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero] at h
    rw [← h, eq_comm]
    refine (sum_units_eq_sum (fun c => A (c * (u : ZMod M)) * (Zres M c : ℂ)) fun c hc => ?_).symm
    have hcu : ¬ IsUnit (c * (u : ZMod M)) := fun h' => hc (by simpa using h'.mul (Units.isUnit u⁻¹))
    simp [hA, hnu _ hcu]

  have hfactor : ∑ u : (ZMod M)ˣ, χ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) *
        ∑ c : (ZMod M)ˣ, A ((c : ZMod M) * u) * (Zres M c : ℂ)
      = (∑ v : (ZMod M)ˣ, χ ((v⁻¹ : (ZMod M)ˣ) : ZMod M) * A v) *
          ∑ c : (ZMod M)ˣ, χ (c : ZMod M) * (Zres M c : ℂ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_

    rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulLeft c⁻¹)]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, Units.val_mul, map_mul, Units.mul_inv_cancel_left]
    ring
  have htotal : ∑ u : (ZMod M)ˣ, χ ((u⁻¹ : (ZMod M)ˣ) : ZMod M) *
      ∑ c : (ZMod M)ˣ, A ((c : ZMod M) * u) * (Zres M c : ℂ) = 0 :=
    Finset.sum_eq_zero fun u _ => by rw [hconvU u, mul_zero]
  rw [hfactor] at htotal

  have hsecond : ∑ c : (ZMod M)ˣ, χ (c : ZMod M) * (Zres M c : ℂ) = LSeries (fun n : ℕ => χ (n : ZMod M)) 2 := by
    rw [sum_units_eq_sum (fun c => χ c * (Zres M c : ℂ)) fun c hc => by simp [MulChar.map_nonunit χ hc]]
    exact sum_char_mul_Zres M χ
  rw [hsecond] at htotal
  exact (mul_eq_zero.mp htotal).resolve_right hL

end Ws47.BSpan

namespace Ws47
namespace BSpan

open Finset Real

section D
variable {N : ℕ} [NeZero N]

theorem psi_eq_zero (g : ZMod N → ℝ)
    (horth : ∀ s : ZMod N, ∑ r : ZMod N, g r * (wt N (s * r).val : ℝ) = 0) (k : ZMod N) : psi g k = 0 := by
  suffices H : ∀ M : ℕ, ∀ k : ZMod N, addOrderOf k = M → psi g k = 0 from H _ k rfl
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; exact psi_zero_eq_zero g horth
    have hM1 : M ≠ 1 := fun h1 => hk0 (AddMonoid.addOrderOf_eq_one_iff.mp (hk.trans h1))
    have hMpos : 0 < M := hk ▸ addOrderOf_pos k
    haveI : NeZero M := ⟨hMpos.ne'⟩
    have hM2 : 1 < M := lt_of_le_of_ne hMpos (Ne.symm hM1)
    haveI : Fact (1 < M) := ⟨hM2⟩
    set a : ZMod M → ℝ := fun c => psi g (((c.val : ℕ) : ZMod N) * k) with ha

    have hnu : ∀ c : ZMod M, ¬ IsUnit c → a c = 0 := by
      intro c hc
      by_cases hc0 : c.val = 0
      · simp only [ha, hc0, Nat.cast_zero, zero_mul]; exact psi_zero_eq_zero g horth
      refine ih (addOrderOf (((c.val : ℕ) : ZMod N) * k)) ?_ _ rfl
      rw [← nsmul_eq_mul, addOrderOf_nsmul' k hc0, hk]
      have hg : 1 < Nat.gcd M c.val := by
        have hcop : ¬ Nat.Coprime c.val M := by
          intro hcop; apply hc
          rw [← ZMod.natCast_zmod_val c]
          exact (ZMod.isUnit_iff_coprime c.val M).mpr hcop
        rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] at hcop
        have hpos : 0 < Nat.gcd M c.val := Nat.gcd_pos_of_pos_left _ hMpos
        omega
      exact Nat.div_lt_self hMpos hg

    have hconv : ∀ u : (ZMod M)ˣ, ∑ c : ZMod M, a (c * u) * Zres M c = 0 := by
      intro u
      have h := tsum_psi_div_sq_eq_zero g horth (((((u : ZMod M)).val : ℕ) : ZMod N) * k)
      rw [tsum_psi_eq_sum_residues g k M hk ((u : ZMod M)).val] at h
      simpa only [ha, ZMod.natCast_zmod_val] using h
    have h1 := eq_zero_of_convolution M a hnu hconv 1
    simpa only [ha, Units.val_one, ZMod.val_one, Nat.cast_one, one_mul] using h1

end D

section E
variable {N : ℕ} [NeZero N]

noncomputable def sinZ (a : ZMod N) : ℝ := Real.sin (2 * π * a.val / N)

theorem sinZ_neg (a : ZMod N) : sinZ (-a) = -sinZ a := by
  unfold sinZ
  rw [ZMod.neg_val]
  split_ifs with h
  · subst h; simp
  · have hle : a.val ≤ N := (ZMod.val_lt a).le
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    rw [Nat.cast_sub hle, show 2 * π * ((N : ℝ) - (a.val : ℝ)) / N = 2 * π - 2 * π * (a.val : ℝ) / N by
      field_simp, Real.sin_two_pi_sub]

theorem stdAddChar_eq_cosZ_add_sinZ (a : ZMod N) :
    (ZMod.stdAddChar a : ℂ) = (cosZ a : ℂ) + (sinZ a : ℂ) * Complex.I := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, cosZ, sinZ]
  rw [show (2 * (π : ℂ) * Complex.I * (a.val : ℂ) / (N : ℂ)) = ((2 * π * (a.val : ℝ) / N : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_mul_I]
  push_cast
  ring

theorem eq_zero_of_psi_eq_zero (g : ZMod N → ℝ) (heven : ∀ r : ZMod N, g (-r) = g r)
    (hpsi : ∀ k : ZMod N, psi g k = 0) : g = 0 := by
  set G : ZMod N → ℂ := fun r => (g r : ℂ) with hG

  have hsin : ∀ k : ZMod N, ∑ j : ZMod N, g j * sinZ (j * k) = 0 := by
    intro k
    have h := (Equiv.sum_comp (Equiv.neg (ZMod N)) (fun j => g j * sinZ (j * k))).symm
    simp only [Equiv.neg_apply, heven, neg_mul, sinZ_neg, mul_neg, Finset.sum_neg_distrib] at h
    linarith
  have hF : ZMod.dft G = 0 := by
    funext k
    rw [ZMod.dft_apply, Pi.zero_apply]
    simp only [smul_eq_mul, stdAddChar_eq_cosZ_add_sinZ, cosZ_neg, sinZ_neg, hG]
    have hc : ∑ j : ZMod N, g j * cosZ (j * k) = 0 := by
      have := hpsi k; unfold psi at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm j k]
    have h1 : ∑ x : ZMod N, ((cosZ (x * k) : ℂ) + ((-sinZ (x * k) : ℝ) : ℂ) * Complex.I) * (g x : ℂ)
        = ((∑ j : ZMod N, g j * cosZ (j * k) : ℝ) : ℂ) - ((∑ j : ZMod N, g j * sinZ (j * k) : ℝ) : ℂ) * Complex.I := by
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, hc, hsin]
    simp
  have hG0 : G = 0 := (LinearEquiv.map_eq_zero_iff ZMod.dft).mp hF
  funext r
  have := congrFun hG0 r
  simpa [hG] using this

end E

section F
variable (N : ℕ) [NeZero N]

def fam (s : ZMod N) : ZMod N → ℚ := fun r : ZMod N =>
  ((6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2 : ℤ) : ℚ)

omit [NeZero N] in
theorem fam_apply (s r : ZMod N) : fam N s r = ((wt N (s * r).val : ℤ) : ℚ) := rfl

variable {N}

omit [NeZero N] in
theorem wt_sub (t : ℕ) (ht : t ≤ N) : wt N (N - t) = wt N t := by
  unfold wt; push_cast [Nat.cast_sub ht]; ring

theorem fam_neg (s r : ZMod N) : fam N s (-r) = fam N s r := by
  rw [fam_apply, fam_apply, mul_neg, ZMod.neg_val]
  split_ifs with h
  · rw [h, ZMod.val_zero]
  · rw [wt_sub _ (ZMod.val_lt _).le]

noncomputable def T : (ZMod N → ℚ) →ₗ[ℚ] (ZMod N → ℚ) :=
  ∑ s : ZMod N, (LinearMap.proj s : (ZMod N → ℚ) →ₗ[ℚ] ℚ).smulRight (fam N s)

theorem T_apply (c : ZMod N → ℚ) (r : ZMod N) : T c r = ∑ s : ZMod N, c s * fam N s r := by
  simp [T, LinearMap.sum_apply, LinearMap.smulRight_apply, Finset.sum_apply, smul_eq_mul]

theorem T_mem_span (c : ZMod N → ℚ) : T c ∈ Submodule.span ℚ (Set.range (fam N)) := by
  rw [T, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

theorem T_neg (c : ZMod N → ℚ) (r : ZMod N) : T c (-r) = T c r := by
  simp only [T_apply, fam_neg]

def evenSub (N : ℕ) [NeZero N] : Submodule ℚ (ZMod N → ℚ) where
  carrier := {φ | ∀ r : ZMod N, φ (-r) = φ r}
  add_mem' ha hb r := by simp [Pi.add_apply, ha r, hb r]
  zero_mem' r := rfl
  smul_mem' c φ hφ r := by simp [Pi.smul_apply, hφ r]

theorem mem_evenSub {φ : ZMod N → ℚ} : φ ∈ evenSub N ↔ ∀ r : ZMod N, φ (-r) = φ r := Iff.rfl

theorem T_eq_zero_imp (c : ZMod N → ℚ) (hc : ∀ r : ZMod N, c (-r) = c r) (hT : T c = 0) : c = 0 := by
  set g : ZMod N → ℝ := fun r => (c r : ℝ) with hg
  have horth : ∀ s : ZMod N, ∑ r : ZMod N, g r * (wt N (s * r).val : ℝ) = 0 := by
    intro s
    have h := congrFun hT s
    rw [T_apply, Pi.zero_apply] at h
    have h' : ((∑ r : ZMod N, c r * fam N r s : ℚ) : ℝ) = 0 := by rw [h]; norm_cast
    push_cast [fam_apply] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_comm r s]
  have hzero := eq_zero_of_psi_eq_zero g (fun r => by simp [hg, hc r]) (psi_eq_zero g horth)
  funext r
  have := congrFun hzero r
  simp only [hg, Pi.zero_apply, Rat.cast_eq_zero] at this
  exact this

noncomputable def TE : evenSub N →ₗ[ℚ] evenSub N :=
  (T (N := N)).restrict fun φ _ => fun r => T_neg φ r

theorem TE_surjective : Function.Surjective (TE (N := N)) := by
  rw [← LinearMap.injective_iff_surjective]
  intro x y hxy
  apply Subtype.ext
  have h : T (x : ZMod N → ℚ) - T (y : ZMod N → ℚ) = 0 := by
    have := congrArg Subtype.val hxy
    simp only [TE, LinearMap.restrict_apply] at this
    rw [this, sub_self]
  rw [← map_sub] at h
  have := T_eq_zero_imp (x - y : ZMod N → ℚ) (fun r => by
    have hx := x.2 r; have hy := y.2 r
    simp only [Pi.sub_apply, hx, hy]) h
  exact sub_eq_zero.mp this

theorem mem_span_iff_even (φ : ZMod N → ℚ) :
    φ ∈ Submodule.span ℚ (Set.range (fam N)) ↔ ∀ r : ZMod N, φ (-r) = φ r := by
  constructor
  · intro h
    have hle : Submodule.span ℚ (Set.range (fam N)) ≤ evenSub N := by
      rw [Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      exact fun r => fam_neg s r
    exact hle h
  · intro h
    obtain ⟨c, hc⟩ := TE_surjective (N := N) ⟨φ, h⟩
    have : T (c : ZMod N → ℚ) = φ := by
      have := congrArg Subtype.val hc
      simpa only [TE, LinearMap.restrict_apply] using this
    rw [← this]
    exact T_mem_span _

end F

end Ws47.BSpan

theorem solution (N : ℕ) [NeZero N]
    (φ : ZMod N → ℚ) :
    φ ∈ Submodule.span ℚ (Set.range fun s : ZMod N => fun r : ZMod N =>
        ((6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2 : ℤ) : ℚ)) ↔
      ∀ r : ZMod N, φ (-r) = φ r :=
  Ws47.BSpan.mem_span_iff_even φ

end S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even (solution)
