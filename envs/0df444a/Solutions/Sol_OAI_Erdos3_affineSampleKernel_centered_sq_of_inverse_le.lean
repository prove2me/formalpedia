-- Prove2me | solution 1 for OAI.Erdos3.affineSampleKernel_centered_sq_of_inverse_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:51:07.662103+00:00
-- url     : https://prove2.me/submissions/c90f2de0-2a53-4942-9071-fe48075f6604

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

end Erdos3

end

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

variable {G : Type*} [Fintype G] [AddCommGroup G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.Chang

variable {G : Type*} [Fintype G] [AddCommGroup G]

end Erdos3.Chang

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem additiveCharacterKernel_ne_top {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    additiveCharacterKernel χ ≠ ⊤ := by
  intro h
  apply hχ
  ext x
  change χ x = 1
  have hx : x ∈ additiveCharacterKernel χ := by rw [h]; trivial
  exact hx

variable [Fintype G]

theorem primePowerCharacter_kernel_index {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    p ≤ (additiveCharacterKernel χ).index := by
  have hd : (additiveCharacterKernel χ).index ∣ p ^ a := by
    rw [← hG, ← Nat.card_eq_fintype_card]
    exact (additiveCharacterKernel χ).index_dvd_card
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hbpos : 0 < b := by
    by_contra hn
    have hbzero : b = 0 := by omega
    rw [hbzero, pow_zero] at hb
    exact additiveCharacterKernel_ne_top hχ ((additiveCharacterKernel χ).index_eq_one.mp hb)
  rw [hb]
  simpa only [pow_one] using Nat.pow_le_pow_right hp.one_le hbpos

theorem primePowerCharacter_kernel_probability {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ≤ (p : ℝ)⁻¹ := by
  classical
  let K := additiveCharacterKernel χ
  have hindex := primePowerCharacter_kernel_index hp hG hχ
  have hc : (Fintype.card K : ℝ) * K.index = Fintype.card G := by
    have h : Fintype.card K * K.index = Fintype.card G := by
      simpa only [Nat.card_eq_fintype_card] using K.card_mul_index
    exact_mod_cast h
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcard : (Finset.univ.filter (fun x : G => χ x = 1)).card = Fintype.card K := by
    simp [K, additiveCharacterKernel, Fintype.card_subtype]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_boole, hcard]
  apply (div_le_iff₀ hN).mpr
  have hi : (p : ℝ) ≤ K.index := by exact_mod_cast hindex
  calc
    _ ≤ (p : ℝ)⁻¹ * ((Fintype.card K : ℝ) * K.index) := by
      apply (le_inv_mul_iff₀ hp0).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card K)]
    _ = _ := by rw [hc]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

noncomputable section

open _root_.Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

end Erdos3.RelativeChangSanders

end

end

section

namespace Erdos3.Chang

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.Chang

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

omit [NeZero q] in
theorem residueColumnMap_single (V : J → G) (j : J) :
    residueColumnMap (q := q) V (Pi.single j (1 : ZMod q)) = V j := by
  simp [residueColumnMap, Pi.single_apply, ite_smul]

theorem additiveCharacter_zmod_smul (χ : AddChar G ℂ) (t : ZMod q) (x : G) :
    χ (t • x) = χ x ^ t.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul]
  exact χ.map_nsmul_eq_pow t.val x

theorem residueColumn_character_zero_iff (V : J → G) (χ : AddChar G ℂ) :
    χ.compAddMonoidHom (residueColumnMap (q := q) V) = 0 ↔ ∀ j, χ (V j) = 1 := by
  constructor
  · intro h j
    have hh := DFunLike.congr_fun h (Pi.single j (1 : ZMod q))
    simpa only [AddChar.compAddMonoidHom_apply, residueColumnMap_single, AddChar.zero_apply] using hh
  · intro h
    ext t
    change χ (∑ j, t j • V j) = 1
    exact (additiveCharacterKernel χ).sum_mem (fun j _ => by
      change χ (t j • V j) = 1
      rw [additiveCharacter_zmod_smul, h, one_pow])

theorem residueColumn_character_mean (V : J → G) (χ : AddChar G ℂ) :
    (𝔼 t : J → ZMod q, χ (residueColumnMap (q := q) V t)) =
      if ∀ j, χ (V j) = 1 then 1 else 0 := by
  have h := AddChar.expect_eq_ite (χ.compAddMonoidHom (residueColumnMap (q := q) V))
  simpa only [AddChar.compAddMonoidHom_apply, residueColumn_character_zero_iff] using h

variable [Fintype G]

theorem finiteFourierCoeff_residueColumnAverage (V : J → G) (f : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (residueColumnAverage (q := q) V f) χ =
      (if ∀ j, χ (V j) = 1 then 1 else 0) * finiteFourierCoeff f χ := by
  have htranslate (a : G) : finiteFourierCoeff (fun x => f (x + a)) χ =
      χ a * finiteFourierCoeff f χ := by
    have h := finiteFourierCoeff_translate f (-a) χ
    rw [AddChar.map_neg_eq_conj] at h
    simpa only [sub_neg_eq_add, Complex.star_def, starRingEnd_self_apply] using h
  unfold finiteFourierCoeff residueColumnAverage
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  change (𝔼 t : J → ZMod q, finiteFourierCoeff (fun x => f (x + residueColumnMap (q := q) V t)) χ) = _
  simp_rw [htranslate]
  rw [← Finset.expect_mul, residueColumn_character_mean]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J G : Type*} [Fintype J] [AddCommGroup G] [Fintype G]

theorem residueColumn_survival_probability (χ : AddChar G ℂ) :
    (𝔼 V : J → G, if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) =
      (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J := by
  have hpoint (V : J → G) :
      (if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) =
        ∏ j, if χ (V j) = 1 then (1 : ℝ) else 0 := by
    by_cases h : ∀ j, χ (V j) = 1
    · simp [h]
    · rw [if_neg h]
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  calc
    _ = 𝔼 V : J → G, ∏ j, if χ (V j) = 1 then (1 : ℝ) else 0 :=
      Finset.expect_congr rfl (fun V _ => hpoint V)
    _ = (∑ x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J /
        (Fintype.card G : ℝ) ^ Fintype.card J := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Nat.cast_pow]
      congr 1
      simpa using (Fintype.prod_sum
        (fun _j : J => fun x : G => if χ x = 1 then (1 : ℝ) else 0)).symm
    _ = _ := by rw [Fintype.expect_eq_sum_div_card, div_pow]

variable {q : ℕ} [NeZero q] [Module (ZMod q) G]

theorem residueColumnAverage_energy (V : J → G) (f : G → ℂ) :
    (𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) =
      ∑ χ : AddChar G ℂ,
        (if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) * ‖finiteFourierCoeff f χ‖ ^ 2 := by
  rw [← finiteFourier_parseval]
  apply Finset.sum_congr rfl
  intro χ _
  rw [finiteFourierCoeff_residueColumnAverage]
  split_ifs <;> simp

theorem residueColumnAverage_mean_energy (f : G → ℂ) :
    (𝔼 V : J → G, 𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) =
      ∑ χ : AddChar G ℂ,
        (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J *
          ‖finiteFourierCoeff f χ‖ ^ 2 := by
  simp_rw [residueColumnAverage_energy]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [← Finset.expect_mul, residueColumn_survival_probability]

theorem primeAffine_contraction_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℂ) (hf : (𝔼 x, f x) = 0) :
    (𝔼 V : J → G, 𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (𝔼 x : G, ‖f x‖ ^ 2) := by
  rw [residueColumnAverage_mean_energy]
  calc
    _ ≤ ∑ χ : AddChar G ℂ, (p : ℝ)⁻¹ ^ Fintype.card J *
        ‖finiteFourierCoeff f χ‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro χ _
      by_cases hχ : χ = 0
      · subst χ
        have hz : finiteFourierCoeff f 0 = 0 := by
          simpa [finiteFourierCoeff] using hf
        simp [hz]
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_pow_left₀
          (Finset.expect_nonneg (fun x _ => by split_ifs <;> norm_num))
          (primePowerCharacter_kernel_probability hp hG hχ) _
    _ = _ := by rw [← Finset.mul_sum, finiteFourier_parseval]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]
  {p a : ℕ} [NeZero (p ^ a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

theorem residueColumnAverage_ofReal (V : J → G) (f : G → ℝ) (x : G) :
    residueColumnAverage (q := q) V (fun y => (f y : ℂ)) x =
      (residueColumnRealAverage (q := q) V f x : ℂ) := by
  simp only [residueColumnAverage, residueColumnRealAverage, Fintype.expect_eq_sum_div_card,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

variable [Fintype G]

theorem primeAffine_real_contraction_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℝ) (hf : (𝔼 x, f x) = 0) :
    (𝔼 V : J → G, 𝔼 x : G, residueColumnRealAverage (q := q) V f x ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (𝔼 x : G, f x ^ 2) := by
  have hfc : (𝔼 x : G, (f x : ℂ)) = 0 := by
    have hc := congrArg (fun y : ℝ => (y : ℂ)) hf
    simpa only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum,
      Complex.ofReal_natCast, Complex.ofReal_zero] using hc
  have h := primeAffine_contraction_sq (q := q) (J := J) hp hG (fun x => (f x : ℂ)) hfc
  simpa only [residueColumnAverage_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G] [Fintype G]

theorem residueAffineKernel_centered_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℝ)
    (hf : (FiniteProbabilityWeights.uniform G).mean f = 0) :
    (residueAffineSource (J := J) (G := G)).mean (fun z => (residueAffineKernel (q := q) z).mean f ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (FiniteProbabilityWeights.uniform G).mean (fun x => f x ^ 2) := by
  simp only [residueAffineSource, FiniteProbabilityWeights.mean_prod, residueAffineKernel_mean,
    FiniteProbabilityWeights.uniform_mean]
  exact primeAffine_real_contraction_sq hp hG f (by simpa only [FiniteProbabilityWeights.uniform_mean] using hf)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (p q a : ι → ℕ) [∀ i, NeZero (q i)] {G : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module (ZMod (q i)) (G i)] [∀ i, Fintype (G i)]
  (hp : ∀ i, (p i).Prime) (hcard : ∀ i, Fintype.card (G i) = p i ^ a i)

include hp hcard

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

universe u v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

theorem affineSampleKernel_centered_sq {p a : ℕ} (hp : p.Prime) (hq : q = p ^ a)
    (f : (I → ZMod q) → ℝ) (hf : (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f = 0) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (FiniteProbabilityWeights.uniform (I → ZMod q)).mean (fun x => f x ^ 2) := by
  unfold affineSampleKernel
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => (residueAffineKernel (q := q) z).mean f ^ 2)]
  have hcard : Fintype.card (I → ZMod q) = p ^ (a * Fintype.card I) := by simp [hq, pow_mul]
  exact residueAffineKernel_centered_sq hp hcard f hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem inverse_prime_power_le_square {p ell : ℕ} {κ : ℝ}
    (hp : p.Prime) (hell : 2 ≤ ell) (_hκ : 0 ≤ κ) (hlarge : (p : ℝ)⁻¹ ≤ κ) :
    (p : ℝ)⁻¹ ^ ell ≤ κ ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hi1 : (p : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp1
  exact (pow_le_pow_of_le_one (inv_nonneg.mpr (Nat.cast_nonneg p)) hi1 hell).trans
    (pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg p)) hlarge 2)

theorem affineSampleKernel_centered_sq_of_inverse_le {J I : Type*} [Fintype J] [Fintype I]
    {q p a : ℕ} [NeZero q] {κ : ℝ} (hp : p.Prime) (hq : q = p ^ a)
    (hJ : 2 ≤ Fintype.card J) (hκ : 0 ≤ κ) (hlarge : (p : ℝ)⁻¹ ≤ κ)
    (f : (I → ZMod q) → ℝ) (hf : (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f = 0) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f ^ 2) ≤
      κ ^ 2 * (FiniteProbabilityWeights.uniform (I → ZMod q)).mean (fun y => f y ^ 2) := by
  exact (affineSampleKernel_centered_sq hp hq f hf).trans
    (mul_le_mul_of_nonneg_right (inverse_prime_power_le_square hp hJ hκ hlarge)
      ((FiniteProbabilityWeights.uniform (I → ZMod q)).mean_nonneg (fun _ => sq_nonneg _)))

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype J] [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I Ω Θ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype J] [Fintype I] [Fintype Ω] [Fintype Θ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]
  (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
  (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
    (fun _ => 1) (fun _ => 0)))
  (paramLo : J → ℤ) (paramN : J → ℕ)
  (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
    (fun _ => 1) (fun _ => 0)))
  (siteLo : I → ℤ) (siteN : I → ℕ)
  (siteHne : Nonempty (IntegerResidueBox siteLo (fun i => siteLo i + siteN i)
    (fun _ => 1) (fun _ => 0)))
  (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (f : (I → ℤ) → ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.affineSampleKernel_centered_sq_of_inverse_le.{u_1, u_2} := @OAI.Erdos3.affineSampleKernel_centered_sq_of_inverse_le.{u_1, u_2}
