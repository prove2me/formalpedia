-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.localReference_uncharged_density
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T01:50:18.446981+00:00
-- url     : https://prove2.me/submissions/7cbd3a13-8c9c-4b3f-9c4c-0bf5f9dd8c6a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1331
import Definitions.Def_OAIErdos3B1372

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularTagGap
namespace OAI

section

namespace Erdos3

theorem modularTagWeight_pos (h : ℕ) : 0 < modularTagWeight h :=
  Nat.mul_pos (pow_pos (by decide) _) (Nat.factorial_pos _)

theorem modularTagWeight_mono : Monotone modularTagWeight := by
  intro i j hij
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hij) (Nat.factorial_le hij)

theorem modularTagWeight_succ (h : ℕ) :
    modularTagWeight (h + 1) = 2 * (h + 1) * modularTagWeight h := by
  simp only [modularTagWeight, pow_succ, Nat.factorial_succ]
  ring

theorem exists_modular_tag_gap {s : ℕ} (hs : 0 < s) (depth : Fin s → ℕ) :
    ∃ h : Fin s,
      (∀ i, depth i ≤ (2 ^ s * s.factorial) * depth h) ∧
      (∀ j : Fin s, h.val < j.val → 2 * (h.val + 1) * depth j < depth h) := by
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  let weight (i : Fin s) := depth i * modularTagWeight i.val
  let score (i : Fin s) := weight i * (s + 1) + i.val
  obtain ⟨h, _, hmax⟩ := Finset.exists_max_image Finset.univ score Finset.univ_nonempty
  have hweight (i : Fin s) : weight i ≤ weight h := by
    have hi := hmax i (Finset.mem_univ i)
    dsimp only [score] at hi
    have hh := h.isLt
    have hs0 : 0 < s + 1 := by omega
    nlinarith
  refine ⟨h, ?_, ?_⟩
  · intro i
    have hi1 : 1 ≤ modularTagWeight i.val := modularTagWeight_pos i.val
    have hhbound : modularTagWeight h.val ≤ modularTagWeight s := modularTagWeight_mono h.isLt.le
    calc
      _ ≤ weight i := by dsimp only [weight]; nlinarith
      _ ≤ weight h := hweight i
      _ ≤ (2 ^ s * s.factorial) * depth h := by
        dsimp only [weight]
        simpa only [modularTagWeight, Nat.mul_comm] using Nat.mul_le_mul_left (depth h) hhbound
  · intro j hj
    by_contra! hbad
    have hwj : 2 * (h.val + 1) * modularTagWeight h.val ≤ modularTagWeight j.val := by
      rw [← modularTagWeight_succ]
      exact modularTagWeight_mono (Nat.succ_le_of_lt hj)
    have hW : weight h ≤ weight j := by
      calc
        _ = depth h * modularTagWeight h.val := rfl
        _ ≤ (2 * (h.val + 1) * depth j) * modularTagWeight h.val :=
          Nat.mul_le_mul_right _ hbad
        _ = depth j * (2 * (h.val + 1) * modularTagWeight h.val) := by ring
        _ ≤ depth j * modularTagWeight j.val := Nat.mul_le_mul_left _ hwj
        _ = weight j := rfl
    have hscore := hmax j (Finset.mem_univ j)
    dsimp only [score] at hscore
    nlinarith

theorem exists_modular_uncharged_depth {s : ℕ} (hs : 0 < s)
    (depth : Fin s → ℕ) (a b e : ℕ)
    (hmax : ∀ i, depth i ≤ a) (hattained : ∃ i, depth i = a)
    (hlarge : 4 * s * (2 ^ s * s.factorial) * (b + e) < a) :
    ∃ (h : Fin s) (k B : ℕ),
      a ≤ (2 ^ s * s.factorial) * depth h ∧
      e ≤ k ∧ (∀ j : Fin s, h.val < j.val → depth j ≤ k) ∧
      2 * (h.val + 1) * k < depth h ∧
      B = depth h - (h.val + 1) * k ∧
      depth h < 2 * B ∧ b < B ∧ B ≤ a - k := by
  classical
  obtain ⟨h, hbound, hgap⟩ := exists_modular_tag_gap hs depth
  obtain ⟨i, hi⟩ := hattained
  have habound : a ≤ (2 ^ s * s.factorial) * depth h := hi ▸ hbound i
  let D := 2 ^ s * s.factorial
  have hD : 0 < D := Nat.mul_pos (pow_pos (by decide) _) (Nat.factorial_pos _)
  have hsmall : 4 * s * (b + e) < depth h := by
    apply (Nat.mul_lt_mul_left hD).mp
    have hlarge' : D * (4 * s * (b + e)) < a := by
      dsimp only [D]
      nlinarith [hlarge]
    exact hlarge'.trans_le habound
  have hdeg : h.val + 1 ≤ s := Nat.succ_le_of_lt h.isLt
  have he : 2 * (h.val + 1) * e < depth h := by
    calc
      _ ≤ 2 * s * e := Nat.mul_le_mul_right e (Nat.mul_le_mul_left 2 hdeg)
      _ ≤ 4 * s * (b + e) := by nlinarith
      _ < _ := hsmall
  let Q := insert e ((Finset.univ.filter (fun j : Fin s => h.val < j.val)).image depth)
  have hQ : Q.Nonempty := Finset.insert_nonempty _ _
  let k := Q.max' hQ
  have hek : e ≤ k := Finset.le_max' Q e (Finset.mem_insert_self _ _)
  have hjk (j : Fin s) (hj : h.val < j.val) : depth j ≤ k :=
    Finset.le_max' Q _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩))
  have hk : 2 * (h.val + 1) * k < depth h := by
    have hkQ : k ∈ Q := Finset.max'_mem Q hQ
    rcases Finset.mem_insert.mp hkQ with hke | hki
    · simpa only [hke] using he
    · obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hki
      simpa only [← hjk] using hgap j (Finset.mem_filter.mp hj).2
  have hk2 : 2 * ((h.val + 1) * k) < depth h := by nlinarith [hk]
  let B := depth h - (h.val + 1) * k
  have hprod : (h.val + 1) * k ≤ depth h := by omega
  have hsum : B + (h.val + 1) * k = depth h := Nat.sub_add_cancel hprod
  have hb : 2 * b < depth h := by
    have h := Nat.mul_le_mul_right (b + e) (show 2 ≤ 4 * s by omega)
    omega
  have hkprod : k ≤ (h.val + 1) * k := by nlinarith
  refine ⟨h, k, B, habound, hek, hjk, hk, rfl, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hh := hmax h
    omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModularDecayBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem modularTagGap_exponent {s a d B n : ℕ} (hn : n < s)
    (ha : a ≤ (2 ^ s * s.factorial) * d) (hd : d ≤ 2 * B)
    {C : ℝ} (hC : 0 ≤ C) :
    (C / ((2 ^ s * s.factorial : ℕ) : ℝ) / (2 ^ s : ℕ)) * a ≤
      C * B / (2 ^ n : ℕ) := by
  let D := 2 ^ s * s.factorial
  have hD : (0 : ℝ) < D := by dsimp only [D]; positivity
  have hpow : 2 * 2 ^ n ≤ 2 ^ s := by
    rw [mul_comm, ← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hn)
  have hprod : a * 2 ^ n ≤ D * B * 2 ^ s := by
    calc
      _ ≤ (D * (2 * B)) * 2 ^ n :=
        Nat.mul_le_mul_right _ (ha.trans (Nat.mul_le_mul_left _ hd))
      _ = D * B * (2 * 2 ^ n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hpow
  have hprodR : (a : ℝ) * (2 ^ n : ℕ) ≤ (D : ℝ) * B * (2 ^ s : ℕ) := by
    exact_mod_cast hprod
  have hn0 : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have hs0 : (0 : ℝ) < (2 ^ s : ℕ) := by positivity
  change (C / (D : ℝ) / (2 ^ s : ℕ)) * a ≤ _
  rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hD hs0) hn0]
  calc
    _ = C * ((a : ℝ) * (2 ^ n : ℕ)) := by ring
    _ ≤ C * ((D : ℝ) * B * (2 ^ s : ℕ)) := mul_le_mul_of_nonneg_left hprodR hC
    _ = _ := by ring

theorem exists_modular_uncharged_decay_parameters {s : ℕ} (hs : 0 < s)
    (depth : Fin s → ℕ) (a b e : ℕ)
    (hmax : ∀ i, depth i ≤ a) (hattained : ∃ i, depth i = a)
    (hlarge : 4 * s * (2 ^ s * s.factorial) * (b + e) < a)
    (p C : ℝ) (hp : 1 ≤ p) (hC : 0 ≤ C) :
    ∃ (h : Fin s) (k B : ℕ),
      e ≤ k ∧ (∀ j : Fin s, h.val < j.val → depth j ≤ k) ∧
      B = depth h - (h.val + 1) * k ∧ b < B ∧ B ≤ a - k ∧
      p ^ (-C * B / (2 ^ h.val : ℕ)) ≤
        p ^ (-(C / ((2 ^ s * s.factorial : ℕ) : ℝ) / (2 ^ s : ℕ)) * a) := by
  obtain ⟨h, k, B, ha, he, hj, _, hB, hd, hb, hBa⟩ :=
    exists_modular_uncharged_depth hs depth a b e hmax hattained hlarge
  refine ⟨h, k, B, he, hj, hB, hb, hBa, ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le hp
  have hexp := modularTagGap_exponent h.isLt ha hd.le hC
  simpa only [neg_mul, neg_div] using neg_le_neg hexp

theorem modular_local_decay_budget {p P K charge a x : ℝ}
    (hp : 1 ≤ p) (hP : 0 ≤ P) (hK : 0 ≤ K) (hcharge : 0 ≤ charge)
    (hx : x ≤ 1) (hlarge : K * charge < a → x ≤ p ^ (-P * a)) :
    x ≤ p ^ (P * K * charge) * p ^ (-P * a) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases ha : K * charge < a
  · apply (hlarge ha).trans
    have hfactor : 1 ≤ p ^ (P * K * charge) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hp
        (show (0 : ℝ) ≤ P * K * charge by positivity)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor
      (Real.rpow_nonneg hp0.le (-P * a))
  · apply hx.trans
    rw [← Real.rpow_add hp0]
    have hnonneg : 0 ≤ P * K * charge + -P * a := by
      have := mul_le_mul_of_nonneg_left (le_of_not_gt ha) hP
      nlinarith
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hp hnonneg

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_series_truncation_le {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (c ψ : K → ℂ) (hψ : ∀ k, ‖ψ k‖ ≤ 1) :
    ‖(∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k‖ ≤ spectrumTail S (fun k => ‖c k‖) := by
  have hid : (∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k =
      ∑ k, if k ∈ S then 0 else c k * ψ k := by
    calc
      _ = ∑ k, (c k * ψ k - if k ∈ S then c k * ψ k else 0) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false, sub_self, sub_zero]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ S
  · simp only [hk, ite_true, norm_zero, le_refl]
  · simp only [hk, ite_false, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ k)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

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

theorem finiteImageFourier_inversion {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    (∑ χ : AddChar H ℂ, finiteImageCharacteristic p Y χ * star (χ z)) =
      (Fintype.card H : ℂ) * finiteImageMass p Y z := by
  classical
  calc
    _ = ∑ x, (p.weight x : ℂ) * (∑ χ : AddChar H ℂ, χ (Y x - z)) := by
      simp only [finiteImageCharacteristic, FiniteProbabilityWeights.complexMean, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [addChar_sub_star]
      ring
    _ = (Fintype.card H : ℂ) * finiteImageMass p Y z := by
      simp only [AddChar.sum_apply_eq_ite, sub_eq_zero, finiteImageMass,
        FiniteProbabilityWeights.mean, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : Y x = z <;> simp [hx, mul_comm]

theorem finiteImageFourier_truncation {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (S : Finset (AddChar H ℂ)) (z : H)
    {scale : ℝ} (hscale : 0 ≤ scale) :
    ‖(scale : ℂ) * finiteImageMass p Y z -
      ((scale : ℂ) / Fintype.card H) * ∑ χ ∈ S, finiteImageCharacteristic p Y χ * star (χ z)‖ ≤
      (scale / Fintype.card H) * spectrumTail S (fun χ => ‖finiteImageCharacteristic p Y χ‖) := by
  have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (scale : ℂ) * finiteImageMass p Y z = ((scale : ℂ) / Fintype.card H) *
      ∑ χ : AddChar H ℂ, finiteImageCharacteristic p Y χ * star (χ z) := by
    rw [finiteImageFourier_inversion]
    field_simp
  rw [he, ← mul_sub, norm_mul]
  have hn : ‖(scale : ℂ) / Fintype.card H‖ = scale / Fintype.card H := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hscale, Complex.norm_natCast]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact finite_series_truncation_le S _ (fun χ => star (χ z))
    (fun χ => by simp only [norm_star, AddChar.norm_apply, le_refl])

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

variable [Fintype G]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exists_primePower_character_descent {I : Type*} {p A a : ℕ}
    [NeZero (p ^ A)] (ha : a ≤ A) (χ : AddChar (I → ZMod (p ^ A)) ℂ)
    (hχ : orderOf χ = p ^ a) :
    ∃ ψ : AddChar (I → ZMod (p ^ a)) ℂ,
      characterPullback (zmodPiReduction (pow_dvd_pow p ha)) ψ = χ ∧
      orderOf ψ = p ^ a := by
  have hpow : χ ^ (p ^ a) = 1 := by
    rw [← hχ]
    exact pow_orderOf_eq_one χ
  obtain ⟨ψ, hψ, hord⟩ := exists_zmodPiReduction_character (pow_dvd_pow p ha) χ hpow
  exact ⟨ψ, hψ, hord.trans hχ⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stdAddChar_mul_modulus_ratio {n m d : ℕ} [NeZero n] [NeZero m] [NeZero d]
    (h : m ∣ n) (hn : n = m * d) (x : ZMod n) :
    ZMod.stdAddChar ((d : ZMod n) * x) =
      ZMod.stdAddChar (ZMod.castHom h (ZMod m) x) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [← Int.cast_natCast d, ← Int.cast_mul, ZMod.stdAddChar_coe,
    map_intCast, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [hn, Nat.cast_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

theorem stdAddChar_primePower_scaling {p A a : ℕ} [NeZero p]
    (ha : a ≤ A) (x : ZMod (p ^ A)) :
    ZMod.stdAddChar (((p ^ (A - a) : ℕ) : ZMod (p ^ A)) * x) =
      ZMod.stdAddChar (ZMod.castHom (pow_dvd_pow p ha) (ZMod (p ^ a)) x) :=
  stdAddChar_mul_modulus_ratio (pow_dvd_pow p ha) (pow_mul_pow_sub p ha).symm x

theorem stdAddChar_primePower_row_scaling {I : Type*} [Fintype I]
    {p A a : ℕ} [NeZero p] (ha : a ≤ A)
    (coeff : I → ZMod (p ^ a)) (x : I → ZMod (p ^ A)) :
    ZMod.stdAddChar (∑ i,
      ((p ^ (A - a) : ℕ) : ZMod (p ^ A)) * ((coeff i).val : ZMod (p ^ A)) * x i) =
    ZMod.stdAddChar (∑ i, coeff i * zmodPiReduction (pow_dvd_pow p ha) x i) := by
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [stdAddChar_primePower_scaling ha]
  congr 1
  simp only [map_sum, map_mul, map_natCast, ZMod.natCast_zmod_val,
    zmodPiReduction_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductImageDecay
namespace OAI

section

namespace Erdos3
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {H : J → Type*} [∀ j, AddCommGroup (H j)]

theorem finiteProductCharacter_decomposition (χ : AddChar (∀ j, H j) ℂ) :
    finiteProductCharacter (finiteProductCharacterCoordinate χ) = χ := by
  ext x
  change (∏ j, χ (Pi.single j (x j))) = χ x
  have hsum : (∑ j, Pi.single j (x j)) = x := by
    ext i
    simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, ite_true]
  have h := map_sum χ.toAddMonoidHom (fun j => Pi.single j (x j)) Finset.univ
  change χ (∑ j, Pi.single j (x j)) = ∏ j, χ (Pi.single j (x j)) at h
  exact (hsum ▸ h).symm

variable [∀ j, Fintype (H j)] {X : J → Type*} [∀ j, Fintype (X j)]

omit [Fintype J] [∀ j, Fintype (H j)] in

theorem finiteProductCharacterCoordinate_order_dvd
    (χ : AddChar (∀ j, H j) ℂ) (q : J → ℕ)
    (hkill : ∀ j (x : H j), q j • x = 0) (j : J) :
    orderOf (finiteProductCharacterCoordinate χ j) ∣ q j := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hkill, AddChar.map_zero_eq_one,
    AddChar.one_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

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

theorem torsionLatticeCharacter_card_le (I : Type*) [Fintype I] (a : ℕ) [NeZero a] :
    Fintype.card (TorsionLatticeCharacter I a) ≤ a ^ Fintype.card I := by
  classical
  let _ : Fintype (rootsOfUnity a ℂ) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective torsionCharacterCoordinates
    (torsionCharacterCoordinates_injective (I := I) (a := a))
  have hc : Fintype.card (rootsOfUnity a ℂ) = a := by
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  rw [Fintype.card_fun, hc] at h
  exact h

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteCharacterOrderTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I H : Type*} [Fintype I]
  [AddCommGroup H] [Fintype H]

theorem finiteCharacter_exactOrder_card_le
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π) (q : ℕ) (hq : 0 < q) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ = q)).card ≤ q ^ Fintype.card I := by
  let : NeZero q := ⟨hq.ne'⟩
  let f : {χ : AddChar H ℂ // orderOf χ = q} → TorsionLatticeCharacter I q :=
    fun χ => ⟨characterPullback π χ.val, by
      simpa only [map_pow, map_one, χ.property] using
        congrArg (characterPullback π) (pow_orderOf_eq_one χ.val)⟩
  have hf : Function.Injective f := by
    intro χ ψ h
    apply Subtype.ext
    exact AddChar.compAddMonoidHom_injective_left π hπ (congrArg Subtype.val h)
  have hc := (Fintype.card_le_of_injective f hf).trans (torsionLatticeCharacter_card_le I q)
  simpa only [Fintype.card_subtype] using hc

theorem finiteCharacter_integer_decay_of_rpow {C P : ℝ} (hC : 0 ≤ C)
    (hP : ((Fintype.card I + 2 : ℕ) : ℝ) ≤ P) (f : AddChar H ℂ → ℝ)
    (hf : ∀ χ, f χ ≤ C * (orderOf χ : ℝ) ^ (-P)) :
    ∀ χ, f χ ≤ C / (orderOf χ : ℝ) ^ (Fintype.card I + 2) := by
  intro χ
  have hq : (1 : ℝ) ≤ orderOf χ := by
    exact_mod_cast (isOfFinOrder_of_finite χ).orderOf_pos
  have hq0 : 0 < (orderOf χ : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hpow : (orderOf χ : ℝ) ^ (Fintype.card I + 2) ≤ (orderOf χ : ℝ) ^ P := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq hP
  apply (hf χ).trans
  rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hC (pow_pos hq0 _) hpow

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TaggedZModOrderBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem taggedIntegerResidue_surjective {Tag : Type*} (J : Tag → Type*) (N : ℕ) :
    Function.Surjective (taggedIntegerResidue J N) := by
  intro y
  choose x hx using fun s : Sigma J => ZMod.intCast_surjective (y s.1 s.2)
  exact ⟨x, funext fun h => funext fun j => hx ⟨h, j⟩⟩

variable {Tag X : Type*} [Fintype Tag] [Fintype X]
  (J : Tag → Type*) [∀ h, Fintype (J h)] (N : ℕ) [NeZero N]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators Classical Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformHomFiberWeights
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom_fiber {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => if f x = y then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ)⁻¹ := by
  have h := uniformPMF_map_hom_index f y
  have hr : f.range = ⊤ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact hf z
  have hy : y ∈ f.range := hf y
  rw [if_pos hy, hr] at h
  simp only [AddSubgroup.index_top, Nat.cast_one, one_div] at h
  rw [uniformPMF_map_fiber] at h
  calc
    _ = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
      rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
      simp
    _ = _ := h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialCharacterRowPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I V R S : Type*} [Fintype I] [CommRing R] [CommRing S]

theorem polynomialCharacterRow_totalDegree_le (row : I → R)
    (F : I → MvPolynomial V R) {d : ℕ} (hF : ∀ i, (F i).totalDegree ≤ d) :
    (polynomialCharacterRow row F).totalDegree ≤ d := by
  unfold polynomialCharacterRow
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simpa using hF i)

theorem polynomialCharacterRow_eval (row : I → R) (F : I → MvPolynomial V R)
    (x : V → R) :
    eval x (polynomialCharacterRow row F) = ∑ i, row i * eval x (F i) := by
  simp only [polynomialCharacterRow, map_sum, map_mul, eval_C]

theorem polynomialCharacterRow_homogeneousComponent (row : I → R)
    (F : I → MvPolynomial V R) (d : ℕ) :
    homogeneousComponent d (polynomialCharacterRow row F) =
      polynomialCharacterRow row (fun i => homogeneousComponent d (F i)) := by
  simp only [polynomialCharacterRow, map_sum, homogeneousComponent_C_mul]

theorem polynomialCharacterRow_map (φ : R →+* S) (row : I → R)
    (F : I → MvPolynomial V R) :
    map φ (polynomialCharacterRow row F) =
      polynomialCharacterRow (fun i => φ (row i)) (fun i => map φ (F i)) := by
  simp only [polynomialCharacterRow, map_sum, map_mul, map_C]

theorem map_homogeneousComponent (φ : R →+* S) (d : ℕ) (P : MvPolynomial V R) :
    map φ (homogeneousComponent d P) = homogeneousComponent d (map φ P) := by
  ext e
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterDepth
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem primePower_character_tag_depth_max
    {Tag : Type*} [Fintype Tag] [DecidableEq Tag] [Nonempty Tag]
    {H : Tag → Type*} [∀ j, AddCommGroup (H j)]
    {p a : ℕ} (hp : p.Prime) (χ : AddChar (∀ j, H j) ℂ)
    (depth : Tag → ℕ)
    (hcoord : ∀ j, orderOf (finiteProductCharacterCoordinate χ j) = p ^ depth j)
    (horder : orderOf χ = p ^ a) :
    (∀ j, depth j ≤ a) ∧ ∃ j, depth j = a := by
  classical
  have hpow : χ ^ (p ^ a) = 1 := by rw [← horder]; exact pow_orderOf_eq_one χ
  have hcoordPow (j : Tag) : (finiteProductCharacterCoordinate χ j) ^ (p ^ a) = 1 := by
    ext x
    exact congrArg (fun ψ : AddChar (∀ j, H j) ℂ => ψ (Pi.single j x)) hpow
  have hdepth (j : Tag) : depth j ≤ a := by
    have hdvd := orderOf_dvd_of_pow_eq_one (hcoordPow j)
    rw [hcoord j] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  refine ⟨hdepth, ?_⟩
  by_cases ha : a = 0
  · obtain ⟨j⟩ := ‹Nonempty Tag›
    exact ⟨j, by have := hdepth j; omega⟩
  by_contra! hmax
  have hsmall (j : Tag) : depth j ≤ a - 1 := by have := hdepth j; have := hmax j; omega
  have hkilled (j : Tag) : (finiteProductCharacterCoordinate χ j) ^ (p ^ (a - 1)) = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hcoord j]
    exact pow_dvd_pow p (hsmall j)
  have hkill : χ ^ (p ^ (a - 1)) = 1 := by
    rw [← finiteProductCharacter_decomposition χ, ← map_pow]
    have hpi : (finiteProductCharacterCoordinate χ) ^ (p ^ (a - 1)) = 1 := by
      funext j
      exact hkilled j
    rw [hpi, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hkill
  rw [horder] at hdvd
  have hle := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerTaggedCharacterRows
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem zmodAddEquiv_apply_eq_std {q : ℕ} [NeZero q] (a x : ZMod q) :
    AddChar.zmodAddEquiv a x = ZMod.stdAddChar (a * x) := by
  rfl

theorem exists_zmod_character_row {I : Type*} [Fintype I] [DecidableEq I]
    {q : ℕ} [NeZero q] (χ : AddChar (I → ZMod q) ℂ) :
    ∃ coeff : I → ZMod q, ∀ x, χ x = ZMod.stdAddChar (∑ i, coeff i * x i) := by
  choose coeff hcoeff using fun i => AddChar.zmodAddEquiv.surjective
    (finiteProductCharacterCoordinate χ i)
  refine ⟨coeff, ?_⟩
  intro x
  have h := congrArg (fun ψ : AddChar (I → ZMod q) ℂ => ψ x)
    (finiteProductCharacter_decomposition χ)
  calc
    χ x = ∏ i, finiteProductCharacterCoordinate χ i (x i) := h.symm
    _ = ∏ i, ZMod.stdAddChar (coeff i * x i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← hcoeff i, zmodAddEquiv_apply_eq_std]
    _ = ZMod.stdAddChar (∑ i, coeff i * x i) := by
      exact (map_sum ZMod.stdAddChar.toAddMonoidHom (fun i => coeff i * x i) Finset.univ).symm

theorem primePower_character_row_primitive {I : Type*} [Fintype I]
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) [NeZero (p ^ a)]
    (χ : AddChar (I → ZMod (p ^ a)) ℂ) (coeff : I → ZMod (p ^ a))
    (hrow : ∀ x, χ x = ZMod.stdAddChar (∑ i, coeff i * x i))
    (horder : orderOf χ = p ^ a) : ∃ i, IsUnit (coeff i) := by
  classical
  by_contra! hunit
  have hdiv (i : I) : p ∣ (coeff i).val := by
    by_contra hh
    apply hunit i
    rw [← ZMod.natCast_zmod_val (coeff i)]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp ha).mpr hh
  have hkill (i : I) : (p ^ (a - 1) : ℕ) * coeff i = (0 : ZMod (p ^ a)) := by
    obtain ⟨b, hb⟩ := hdiv i
    rw [← ZMod.natCast_zmod_val (coeff i), hb, ← Nat.cast_mul,
      ← Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
    simp only [Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hpow : χ ^ (p ^ (a - 1)) = 1 := by
    ext x
    rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hrow, AddChar.one_apply]
    have hz : (∑ i, coeff i * ((p ^ (a - 1)) • x) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, ← mul_assoc, hkill, zero_mul]
    rw [hz, AddChar.map_zero_eq_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [horder] at hdvd
  have hle := Nat.le_of_dvd (pow_pos hp.pos _) hdvd
  have hlt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

theorem primePower_primitive_row_cast {I : Type*} {p a b : ℕ} (hab : b ≤ a)
    (coeff : I → ZMod (p ^ a)) (hcoeff : ∃ i, IsUnit (coeff i)) :
    ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ b)) (coeff i)) := by
  obtain ⟨i, hi⟩ := hcoeff
  exact ⟨i, hi.map (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ b)))⟩

theorem exists_primePower_character_conductor_row {I : Type*} [Fintype I]
    {p A a : ℕ} (hp : p.Prime) (ha : a ≤ A) [NeZero (p ^ A)] [NeZero (p ^ a)]
    (χ : AddChar (I → ZMod (p ^ A)) ℂ) (horder : orderOf χ = p ^ a) :
    ∃ coeff : I → ZMod (p ^ a),
      (0 < a → ∀ {b : ℕ} (hab : b ≤ a),
        ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ b)) (coeff i))) ∧
      ∀ x, χ x = ZMod.stdAddChar
        (∑ i, coeff i * ZMod.castHom (pow_dvd_pow p ha) (ZMod (p ^ a)) (x i)) := by
  classical
  obtain ⟨ψ, hψ, hord⟩ := exists_primePower_character_descent ha χ horder
  obtain ⟨coeff, hcoeff⟩ := exists_zmod_character_row ψ
  refine ⟨coeff, ?_, ?_⟩
  · intro ha0 b hab
    exact primePower_primitive_row_cast hab coeff
      (primePower_character_row_primitive hp ha0 ψ coeff hcoeff hord)
  · intro x
    calc
      χ x = ψ (zmodPiReduction (pow_dvd_pow p ha) x) :=
        (congrArg (fun θ : AddChar (I → ZMod (p ^ A)) ℂ => θ x) hψ).symm
      _ = _ := hcoeff _

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem exists_primePower_tagged_conductor_rows
    {Tag : Type*} [Fintype Tag] [DecidableEq Tag]
    {I : Tag → Type*} [∀ j, Fintype (I j)]
    {p A : ℕ} [NeZero p] (hp : p.Prime)
    (χ : AddChar (∀ j, I j → ZMod (p ^ A)) ℂ) :
    ∃ (depth : Tag → ℕ) (hdepth : ∀ j, depth j ≤ A)
      (coeff : ∀ j, I j → ZMod (p ^ depth j)),
      (∀ j, orderOf (finiteProductCharacterCoordinate χ j) = p ^ depth j) ∧
      (∀ j, 0 < depth j → ∀ {b : ℕ} (hb : b ≤ depth j),
        ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p hb) (ZMod (p ^ b)) (coeff j i))) ∧
      (∀ j (x : I j → ZMod (p ^ A)), finiteProductCharacterCoordinate χ j x =
        ZMod.stdAddChar (∑ i, coeff j i *
          ZMod.castHom (pow_dvd_pow p (hdepth j)) (ZMod (p ^ depth j)) (x i))) ∧
      ∀ x, χ x = ∏ j, ZMod.stdAddChar (∑ i, coeff j i *
        ZMod.castHom (pow_dvd_pow p (hdepth j)) (ZMod (p ^ depth j)) (x j i)) := by
  classical
  have hkill : ∀ j (x : I j → ZMod (p ^ A)), (p ^ A) • x = 0 := by
    intro j x
    ext i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have horderDiv (j : Tag) : orderOf (finiteProductCharacterCoordinate χ j) ∣ p ^ A :=
    finiteProductCharacterCoordinate_order_dvd χ (fun _ => p ^ A) hkill j
  choose depth hdepth horder using fun j => (Nat.dvd_prime_pow hp).mp (horderDiv j)
  choose coeff hcoeff hrow using fun j =>
    exists_primePower_character_conductor_row hp (hdepth j)
      (finiteProductCharacterCoordinate χ j) (horder j)
  refine ⟨depth, hdepth, coeff, horder, hcoeff, hrow, ?_⟩
  intro x
  calc
    χ x = ∏ j, finiteProductCharacterCoordinate χ j (x j) :=
      (congrArg (fun θ : AddChar (∀ j, I j → ZMod (p ^ A)) ℂ => θ x)
        (finiteProductCharacter_decomposition χ)).symm
    _ = _ := Finset.prod_congr rfl (fun j _ => hrow j (x j))

theorem exists_primePower_tagged_ambient_rows
    {Tag : Type*} [Fintype Tag] [DecidableEq Tag]
    {I : Tag → Type*} [∀ j, Fintype (I j)]
    {p A : ℕ} [NeZero p] (hp : p.Prime)
    (χ : AddChar (∀ j, I j → ZMod (p ^ A)) ℂ) :
    ∃ (depth : Tag → ℕ) (hdepth : ∀ j, depth j ≤ A)
      (coeff : ∀ j, I j → ZMod (p ^ A)),
      (∀ j, orderOf (finiteProductCharacterCoordinate χ j) = p ^ depth j) ∧
      (∀ j, 0 < depth j → ∀ {b : ℕ} (hb : b ≤ depth j),
        ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p (hb.trans (hdepth j)))
          (ZMod (p ^ b)) (coeff j i))) ∧
      ∀ x, χ x = ZMod.stdAddChar
        (∑ j, ((p ^ (A - depth j) : ℕ) : ZMod (p ^ A)) * ∑ i, coeff j i * x j i) := by
  classical
  obtain ⟨depth, hdepth, c, horder, hunit, hrow, hphase⟩ :=
    exists_primePower_tagged_conductor_rows hp χ
  let coeff := fun j i => ((c j i).val : ZMod (p ^ A))
  refine ⟨depth, hdepth, coeff, horder, ?_, ?_⟩
  · intro j hj b hb
    obtain ⟨i, hi⟩ := hunit j hj hb
    refine ⟨i, ?_⟩
    simpa only [coeff, map_natCast, ZMod.castHom_apply, ZMod.cast_eq_val] using hi
  · intro x
    rw [hphase]
    calc
      _ = ∏ j, ZMod.stdAddChar
          (((p ^ (A - depth j) : ℕ) : ZMod (p ^ A)) * ∑ i, coeff j i * x j i) := by
        apply Finset.prod_congr rfl
        intro j _
        simpa only [coeff, zmodPiReduction_apply, mul_assoc, ← Finset.mul_sum] using
          (stdAddChar_primePower_row_scaling (hdepth j) (c j) (x j)).symm
      _ = ZMod.stdAddChar (∑ j, ((p ^ (A - depth j) : ℕ) : ZMod (p ^ A)) *
          ∑ i, coeff j i * x j i) :=
        (map_sum ZMod.stdAddChar.toAddMonoidHom
          (fun j => ((p ^ (A - depth j) : ℕ) : ZMod (p ^ A)) *
            ∑ i, coeff j i * x j i) Finset.univ).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FiniteAffineClassAverage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]
    [Fintype H] [Fintype K]

theorem expect_affine_class_refinement (e : H →+ G) (d : K →+ H)
    (r : G) (f : G → ℂ) :
    (𝔼 y : H, 𝔼 x : K, f ((r + e y) + e (d x))) =
      𝔼 y : H, f (r + e y) := by
  rw [Finset.expect_comm]
  have hpoint (x : K) : (𝔼 y : H, f ((r + e y) + e (d x))) =
      𝔼 y : H, f (r + e y) := by
    calc
      _ = 𝔼 y : H, f (r + e (d x + y)) := by
        apply Finset.expect_congr rfl
        intro y _
        rw [map_add]
        congr 1
        abel
      _ = _ := expect_translate (fun y => f (r + e y)) (d x)
  simp only [hpoint, Fintype.expect_const]

theorem norm_affine_class_mean_le_of_refinement (e : H →+ G) (d : K →+ H)
    (r : G) (f : G → ℂ) (β : ℝ)
    (hbound : ∀ y : H, ‖𝔼 x : K, f ((r + e y) + e (d x))‖ ≤ β) :
    ‖𝔼 y : H, f (r + e y)‖ ≤ β := by
  rw [← expect_affine_class_refinement e d r f]
  exact (RCLike.norm_expect_le (K := ℂ)).trans
    ((Finset.expect_le_expect (fun y _ => hbound y)).trans_eq (Fintype.expect_const β))

theorem norm_scalar_affine_class_mean_le {I R : Type*} [Fintype I]
    [CommRing R] [Fintype R] (e d : R) (r : I → R) (f : (I → R) → ℂ) (β : ℝ)
    (hbound : ∀ t : I → R,
      ‖𝔼 x : I → R, f (fun i => t i + (e * d) * x i)‖ ≤ β) :
    ‖𝔼 y : I → R, f (fun i => r i + e * y i)‖ ≤ β := by
  apply norm_affine_class_mean_le_of_refinement (scalarTupleHom e) (scalarTupleHom d) r f β
  intro y
  change ‖𝔼 x : I → R, f (fun i => (r i + e * y i) + e * (d * x i))‖ ≤ β
  simpa only [mul_assoc] using hbound (fun i => r i + e * y i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformHomExpectation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => g (f x)) =
      (FiniteProbabilityWeights.uniform H).mean g := by
  calc
    _ = ∑ y : H, (FiniteProbabilityWeights.uniform G).mean
        (fun x => if f x = y then (1 : ℝ) else 0) * g y := by
      unfold FiniteProbabilityWeights.mean
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [mul_ite, ite_mul]
    _ = ∑ y : H, (Fintype.card H : ℝ)⁻¹ * g y := by
      simp_rw [uniform_mean_surjective_hom_fiber f hf]
    _ = _ := rfl

theorem expect_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (𝔼 x : G, g (f x)) = 𝔼 y : H, g y := by
  simpa only [FiniteProbabilityWeights.uniform_mean] using
    uniform_mean_surjective_hom f hf g

theorem nestedTupleResidueReduction_surjective {I : Type*} (n : ℕ)
    {M N : ℕ} (hMN : M ∣ N) :
    Function.Surjective (nestedTupleResidueReduction (I := I) n hMN) := by
  intro y
  choose x hx using fun a i => ZMod.castHom_surjective hMN (y a i)
  exact ⟨x, funext fun a => funext (hx a)⟩

theorem expect_nestedTupleResidueReduction {I : Type*} [Fintype I]
    (n : ℕ) {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (g : (Fin n → I → ZMod M) → ℝ) :
    (𝔼 x : Fin n → I → ZMod N,
      g (fun a i => ZMod.castHom hMN (ZMod M) (x a i))) =
        𝔼 y : Fin n → I → ZMod M, g y :=
  expect_surjective_hom (nestedTupleResidueReduction n hMN)
    (nestedTupleResidueReduction_surjective n hMN) g

theorem expect_mul_modulus_reduction {I : Type*} [Fintype I]
    (n M d : ℕ) [NeZero M] [NeZero d]
    (g : (Fin n → I → ZMod M) → ℝ) :
    (𝔼 x : Fin n → I → ZMod (M * d),
      g (fun a i => ZMod.castHom (dvd_mul_right M d) (ZMod M) (x a i))) =
        𝔼 y : Fin n → I → ZMod M, g y :=
  expect_nestedTupleResidueReduction n (dvd_mul_right M d) g

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

theorem polynomialIterDifference_add {I R : Type*} [CommRing R] (n : ℕ)
    (P Q : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (P + Q) u =
      polynomialIterDifference n P u + polynomialIterDifference n Q u := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference, map_add]
    exact ih _ _ _

theorem polynomialIterDifference_smul {I R : Type*} [CommRing R] (n : ℕ)
    (c : R) (P : MvPolynomial I R) (u : Fin n → I → R) :
    polynomialIterDifference n (c • P) u = c • polynomialIterDifference n P u := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference, map_smul]
    exact ih _ _

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [Fintype I] [CommRing R] [Fintype R]

theorem polynomial_phase_difference_mean_sq_le (P : MvPolynomial I R)
    (χ : AddChar R ℂ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ ^ 2 ≤
      𝔼 u : I → R, ‖𝔼 x : I → R, χ (eval x (polynomialDifference u P))‖ := by
  let f : (I → R) → ℂ := fun x => χ (eval x P)
  have hpoint (u x : I → R) : χ (eval x (polynomialDifference u P)) =
      star (multiplicativeDerivative f u x) := by
    rw [polynomialDifference_eval, addChar_sub_star]
    simp only [multiplicativeDerivative, star_mul, star_star, f]
  have hmean (u : I → R) :
      ‖𝔼 x, χ (eval x (polynomialDifference u P))‖ =
      ‖𝔼 x, multiplicativeDerivative f u x‖ := by
    simp only [hpoint, expect_star, norm_star]
  simp_rw [hmean]
  calc
    _ = ‖gowersMoment 1 f‖ := by
      rw [gowersMoment_one, norm_mul, norm_star, pow_two]
    _ ≤ 𝔼 u : I → R, ‖𝔼 x : I → R, multiplicativeDerivative f u x‖ :=
      RCLike.norm_expect_le (K := ℂ)

theorem polynomial_phase_iterDifference_bound (n : ℕ) (P : MvPolynomial I R)
    (χ : AddChar R ℂ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → R,
        ‖𝔼 x : I → R, χ (eval x (polynomialIterDifference n P u))‖ := by
  induction n generalizing P with
  | zero => simp [polynomialIterDifference]
  | succ n ih =>
    calc
      _ = (‖𝔼 x : I → R, χ (eval x P)‖ ^ 2) ^ (2 ^ n) := by
        rw [← pow_mul, pow_succ]; congr 1; omega
      _ ≤ (𝔼 u : I → R,
          ‖𝔼 x : I → R, χ (eval x (polynomialDifference u P))‖) ^ (2 ^ n) :=
        pow_le_pow_left₀ (sq_nonneg _) (polynomial_phase_difference_mean_sq_le P χ) _
      _ ≤ 𝔼 u : I → R,
          ‖𝔼 x : I → R, χ (eval x (polynomialDifference u P))‖ ^ (2 ^ n) :=
        expect_pow_two_pow_le n _ (fun _ => norm_nonneg _)
      _ ≤ 𝔼 u : I → R, 𝔼 v : Fin n → I → R,
          ‖𝔼 x : I → R, χ (eval x (polynomialIterDifference n
            (polynomialDifference u P) v))‖ :=
        Finset.expect_le_expect (fun u _ => ih (polynomialDifference u P))
      _ = _ := by rw [expect_fin_cons]; rfl

theorem affine_polynomial_phase_mean_zero (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ 1) (χ : AddChar R ℂ) (hχ : Function.Injective χ)
    (hrow : polynomialLinearRow P ≠ 0) :
    (𝔼 x : I → R, χ (eval x P)) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, polynomialLinearRow P i ≠ 0 := by
    by_contra! h
    exact hrow (funext h)
  let u : I → R := Pi.single i 1
  have hlin : (∑ j, polynomialLinearRow P j * u j) = polynomialLinearRow P i := by
    simp [u, Pi.single_apply]
  have heval (x : I → R) : eval (x + u) P = eval x P + polynomialLinearRow P i := by
    have h := congrArg (eval x) (polynomialDifference_affine u P hP)
    rw [polynomialDifference_eval, eval_C, hlin] at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  have hshift := expect_translate (fun x : I → R => χ (eval x P)) u
  have hmul : (𝔼 x : I → R, χ (eval x P)) * χ (polynomialLinearRow P i) =
      (𝔼 x : I → R, χ (eval x P)) := by
    conv_rhs => rw [← hshift]
    simp_rw [add_comm u, heval, χ.map_add_eq_mul]
    exact Finset.expect_mul _ _ _
  have hne : χ (polynomialLinearRow P i) ≠ 1 := by
    intro h
    exact hi (hχ (h.trans χ.map_zero_eq_one.symm))
  have hz : (𝔼 x : I → R, χ (eval x P)) * (χ (polynomialLinearRow P i) - 1) = 0 := by
    linear_combination hmul
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hne)

theorem norm_affine_polynomial_phase_mean (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ 1) (χ : AddChar R ℂ) (hχ : Function.Injective χ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ =
      if polynomialLinearRow P = 0 then (1 : ℝ) else 0 := by
  split_ifs with hrow
  · have hp : P = C (P.coeff 0) := by
      rw [degree_le_one_eq_constant_add_row P hP, hrow]
      simp [rowPolynomial]
    conv_lhs => rw [hp]
    simp only [eval_C, Fintype.expect_const, χ.norm_apply]
  · rw [affine_polynomial_phase_mean_zero P hP χ hχ hrow, norm_zero]

theorem polynomial_phase_bias_le_linearRow_probability (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1)
    (χ : AddChar R ℂ) (hχ : Function.Injective χ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → R,
        if polynomialLinearRow (polynomialIterDifference n P u) = 0 then (1 : ℝ) else 0 := by
  have h := polynomial_phase_iterDifference_bound n P χ
  simpa only [norm_affine_polynomial_phase_mean _
    (polynomialIterDifference_degree n 1 P hP _) χ hχ] using h

omit [Fintype I] [Fintype R] in

theorem polynomialIterDifference_linearRow_top_component (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1)
    (u : Fin n → I → R) :
    polynomialLinearRow (polynomialIterDifference n P u) =
      polynomialLinearRow (polynomialIterDifference n (homogeneousComponent (n + 1) P) u) := by
  let Q := P - homogeneousComponent (n + 1) P
  have hQ : Q.totalDegree ≤ n := totalDegree_sub_top_component_le n P hP
  have hdiff : (polynomialIterDifference n Q u).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero (polynomialIterDifference_degree n 0 Q (by simpa using hQ) u)
  have hconst := totalDegree_eq_zero_iff_eq_C.mp hdiff
  have hrowQ : polynomialLinearRow (polynomialIterDifference n Q u) = 0 := by
    funext i
    dsimp [polynomialLinearRow]
    rw [hconst, coeff_C]
    have hz : (0 : I →₀ ℕ) ≠ Finsupp.single i 1 := by
      intro h
      have hi := congrArg (fun a : I →₀ ℕ => a i) h
      simp at hi
    simp only [if_neg hz]
  have hsplit : P = homogeneousComponent (n + 1) P + Q := by dsimp [Q]; abel
  conv_lhs => rw [hsplit, polynomialIterDifference_add]
  funext i
  simp only [polynomialLinearRow, MvPolynomial.coeff_add]
  have hi := congrFun hrowQ i
  change (polynomialIterDifference n Q u).coeff (Finsupp.single i 1) = 0 at hi
  rw [hi, add_zero]

theorem polynomial_phase_bias_le_top_linearRow_probability (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1)
    (χ : AddChar R ℂ) (hχ : Function.Injective χ) :
    ‖𝔼 x : I → R, χ (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → R,
        if polynomialLinearRow
          (polynomialIterDifference n (homogeneousComponent (n + 1) P) u) = 0
        then (1 : ℝ) else 0 := by
  have h := polynomial_phase_bias_le_linearRow_probability n P hP χ hχ
  simpa only [polynomialIterDifference_linearRow_top_component n P hP] using h

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

theorem polynomialCommonScale_monomial (c r : R) (a : I →₀ ℕ) :
    polynomialCommonScale c (monomial a r) =
      C (c ^ a.degree) * monomial a r := by
  rw [polynomialCommonScale, aeval_monomial]
  simp only [algebraMap_eq, Finsupp.prod,
    mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.degree_apply]
  ring

theorem polynomialCommonScale_homogeneousComponent (c : R) (d : ℕ)
    (P : MvPolynomial I R) :
    homogeneousComponent d (polynomialCommonScale c P) =
      C (c ^ d) * homogeneousComponent d P := by
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum, map_sum]
  conv_rhs => rw [← P.support_sum_monomial_coeff, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [polynomialCommonScale_monomial, homogeneousComponent_C_mul]
  rw [homogeneousComponent_of_mem (isHomogeneous_monomial (P.coeff a) rfl)]
  by_cases hd : d = a.degree
  · simp only [hd, ite_true]
  · simp only [if_neg hd, mul_zero]

theorem polynomialTranslate_top_component (r : I → R) (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1) :
    homogeneousComponent (n + 1) (polynomialTranslate r P) =
      homogeneousComponent (n + 1) P := by
  have hd := polynomialDifference_degree r P hP
  have hz := homogeneousComponent_eq_zero (n + 1) (polynomialDifference r P) (by omega)
  rw [polynomialDifference_apply, map_sub] at hz
  exact sub_eq_zero.mp hz

theorem polynomialAffineClass_eval (r x : I → R) (c : R) (P : MvPolynomial I R) :
    eval x (polynomialAffineClass r c P) = eval (fun i => r i + c * x i) P := by
  change aeval x (polynomialCommonScale c (polynomialTranslate r P)) = _
  rw [polynomialCommonScale, comp_aeval_apply, polynomialTranslate, comp_aeval_apply]
  simp only [map_mul, map_add, aeval_C, aeval_X, Algebra.algebraMap_self_apply]
  change eval (fun i => c * x i + r i) P = eval (fun i => r i + c * x i) P
  exact congrArg (fun y : I → R => eval y P) (funext (fun i => add_comm _ _))

theorem polynomialAffineClass_apply (r : I → R) (c : R) (P : MvPolynomial I R) :
    polynomialAffineClass r c P = aeval (fun i => C c * X i + C (r i)) P := by
  change polynomialCommonScale c (polynomialTranslate r P) = _
  rw [polynomialTranslate, polynomialCommonScale, comp_aeval_apply]
  simp only [map_add, aeval_X, aeval_C, algebraMap_eq]

theorem polynomialAffineClass_degree (r : I → R) (c : R) (d : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ d) :
    (polynomialAffineClass r c P).totalDegree ≤ d := by
  rw [polynomialAffineClass_apply]
  apply (mem_weightedSupportLE_one_iff _ d).mp
  apply weightedSupportLE_aeval (1 : I → ℕ) (1 : I → ℕ) _ _
    ((mem_weightedSupportLE_one_iff P d).mpr hP)
  intro i
  apply (weightedSupportLE (1 : I → ℕ) 1).add_mem
  · exact weightedSupportLE_mul (weightedSupportLE_C _ 0 c) (weightedSupportLE_X _ i)
  · exact weightedSupportLE_C _ 1 (r i)

theorem polynomialAffineClass_mul_eq_constant (r : I → R) (c a : R)
    (hac : a * c = 0) (P : MvPolynomial I R) :
    C a * polynomialAffineClass r c P = C (a * eval r P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [polynomialAffineClass, polynomialCommonScale, polynomialTranslate]
  | add P Q hP hQ =>
    simp only [map_add, mul_add, hP, hQ]
  | mul_X P i hP =>
    have hX : polynomialAffineClass r c (X i) = C c * X i + C (r i) := by
      simp [polynomialAffineClass_apply]
    have heval : eval r (P * X i) = eval r P * r i := by simp
    rw [map_mul, hX, heval]
    calc
      _ = (C a * C c) * (polynomialAffineClass r c P * X i) +
          (C a * polynomialAffineClass r c P) * C (r i) := by ring
      _ = C (a * eval r P) * C (r i) := by
        rw [← map_mul, hac, map_zero, zero_mul, zero_add, hP]
      _ = _ := by rw [← map_mul, mul_assoc]

theorem polynomialAffineClass_top_component (r : I → R) (c : R) (n : ℕ)
    (P : MvPolynomial I R) (hP : P.totalDegree ≤ n + 1) :
    homogeneousComponent (n + 1) (polynomialAffineClass r c P) =
      C (c ^ (n + 1)) * homogeneousComponent (n + 1) P := by
  change homogeneousComponent (n + 1) (polynomialCommonScale c (polynomialTranslate r P)) = _
  rw [polynomialCommonScale_homogeneousComponent, polynomialTranslate_top_component r n P hP]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R S : Type*} [CommRing R] [CommRing S]

theorem polynomialTranslate_map_coefficients (φ : R →+* S) (u : I → R)
    (P : MvPolynomial I R) :
    map φ (polynomialTranslate u P) =
      polynomialTranslate (fun i => φ (u i)) (map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, map_X, polynomialTranslate_X, map_add, map_C, hP]

theorem polynomialDifference_map_coefficients (φ : R →+* S) (u : I → R)
    (P : MvPolynomial I R) :
    map φ (polynomialDifference u P) =
      polynomialDifference (fun i => φ (u i)) (map φ P) := by
  simp only [polynomialDifference_apply, map_sub, polynomialTranslate_map_coefficients]

theorem polynomialIterDifference_map_coefficients (φ : R →+* S) (n : ℕ)
    (u : Fin n → I → R) (P : MvPolynomial I R) :
    map φ (polynomialIterDifference n P u) =
      polynomialIterDifference n (map φ P) (fun j i => φ (u j i)) := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    simp only [polynomialIterDifference, ih, polynomialDifference_map_coefficients]
    rfl

theorem polynomialIterDifference_C_mul (c : R) (n : ℕ)
    (u : Fin n → I → R) (P : MvPolynomial I R) :
    polynomialIterDifference n (C c * P) u = C c * polynomialIterDifference n P u := by
  simpa only [smul_eq_C_mul] using polynomialIterDifference_smul n c P u

theorem zmod_mul_denominator_eq_zero_iff (M d : ℕ) [NeZero M] [NeZero d]
    (x : ZMod (M * d)) :
    (d : ZMod (M * d)) * x = 0 ↔
      ZMod.castHom (dvd_mul_right M d) (ZMod M) x = 0 := by
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  rw [mul_comm M d, Nat.mul_dvd_mul_iff_left (NeZero.pos d)]

theorem polynomialIterDifference_scaled_row_reduction (M d : ℕ) [NeZero M] [NeZero d]
    (n : ℕ) (H : MvPolynomial I (ZMod (M * d))) (u : Fin n → I → ZMod (M * d)) :
    polynomialLinearRow (polynomialIterDifference n (C (d : ZMod (M * d)) * H) u) = 0 ↔
      polynomialLinearRow (polynomialIterDifference n
        (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H)
        (fun j i => ZMod.castHom (dvd_mul_right M d) (ZMod M) (u j i))) = 0 := by
  rw [polynomialIterDifference_C_mul, ← polynomialIterDifference_map_coefficients]
  simp only [funext_iff, polynomialLinearRow, coeff_C_mul, coeff_map, Pi.zero_apply,
    zmod_mul_denominator_eq_zero_iff]

theorem polynomialIterDifference_scaled_row_probability [Fintype I]
    (M d : ℕ) [NeZero M] [NeZero d] (n : ℕ)
    (H : MvPolynomial I (ZMod (M * d))) :
    (𝔼 u : Fin n → I → ZMod (M * d),
      if polynomialLinearRow (polynomialIterDifference n (C (d : ZMod (M * d)) * H) u) = 0
      then (1 : ℝ) else 0) =
    𝔼 u : Fin n → I → ZMod M,
      if polynomialLinearRow (polynomialIterDifference n
        (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H) u) = 0
      then (1 : ℝ) else 0 := by
  calc
    _ = 𝔼 u : Fin n → I → ZMod (M * d),
        if polynomialLinearRow (polynomialIterDifference n
          (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H)
          (fun j i => ZMod.castHom (dvd_mul_right M d) (ZMod M) (u j i))) = 0
        then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro u _
      have hevent := polynomialIterDifference_scaled_row_reduction M d n H u
      simp only [hevent]
    _ = _ := expect_mul_modulus_reduction (I := I) n M d
      (fun v => if polynomialLinearRow (polynomialIterDifference n
        (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H) v) = 0
        then (1 : ℝ) else 0)

theorem zmod_polynomial_phase_bias_reduced_denominator [Fintype I]
    (M d : ℕ) [NeZero M] [NeZero d] (n : ℕ)
    (P H : MvPolynomial I (ZMod (M * d))) (hP : P.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = C (d : ZMod (M * d)) * H) :
    ‖𝔼 x : I → ZMod (M * d), ZMod.stdAddChar (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → ZMod M,
        if polynomialLinearRow (polynomialIterDifference n
          (map (ZMod.castHom (dvd_mul_right M d) (ZMod M)) H) u) = 0
        then (1 : ℝ) else 0 := by
  have h := polynomial_phase_bias_le_top_linearRow_probability n P hP
    ZMod.stdAddChar ZMod.injective_stdAddChar
  rw [htop] at h
  apply h.trans_eq
  convert polynomialIterDifference_scaled_row_probability M d n H using 1
  apply Finset.expect_congr rfl
  intro u _
  split_ifs <;> rfl

theorem zmod_polynomial_phase_bias_reduced_denominator_of_mul [Fintype I]
    (N M d : ℕ) [NeZero N] [NeZero M] [NeZero d] (hN : N = M * d) (n : ℕ)
    (P H : MvPolynomial I (ZMod N)) (hP : P.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = C (d : ZMod N) * H) :
    ‖𝔼 x : I → ZMod N, ZMod.stdAddChar (eval x P)‖ ^ (2 ^ n) ≤
      𝔼 u : Fin n → I → ZMod M,
        if polynomialLinearRow (polynomialIterDifference n
          (map (ZMod.castHom (show M ∣ N from ⟨d, hN⟩) (ZMod M)) H) u) = 0
        then (1 : ℝ) else 0 := by
  subst N
  exact zmod_polynomial_phase_bias_reduced_denominator M d n P H hP htop

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [CommRing R]

theorem tagged_affine_phase_degree {s : ℕ} (h : Fin s)
    (F : Fin s → MvPolynomial I R) (hF : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (a : Fin s → R) (r : I → R) (c : R)
    (hkill : ∀ j, h < j → a j * c = 0) :
    (∑ j, C (a j) * polynomialAffineClass r c (F j)).totalDegree ≤ h.val + 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  by_cases hj : h < j
  · rw [polynomialAffineClass_mul_eq_constant r c (a j) (hkill j hj), totalDegree_C]
    exact Nat.zero_le _
  · have hjh : j.val ≤ h.val := by simpa using le_of_not_gt hj
    have hd := totalDegree_mul (C (a j)) (polynomialAffineClass r c (F j))
    rw [totalDegree_C, zero_add] at hd
    exact hd.trans ((polynomialAffineClass_degree r c (j.val + 1) (F j) (hF j)).trans
      (Nat.add_le_add_right hjh 1))

theorem tagged_affine_phase_top_component {s : ℕ} (h : Fin s)
    (F : Fin s → MvPolynomial I R) (hF : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (a : Fin s → R) (r : I → R) (c : R)
    (hkill : ∀ j, h < j → a j * c = 0) :
    homogeneousComponent (h.val + 1) (∑ j, C (a j) * polynomialAffineClass r c (F j)) =
      C (a h * c ^ (h.val + 1)) * homogeneousComponent (h.val + 1) (F h) := by
  rw [map_sum, Finset.sum_eq_single h]
  · rw [homogeneousComponent_C_mul, polynomialAffineClass_top_component r c h.val (F h) (hF h),
      ← mul_assoc, ← map_mul]
  · intro j _ hj
    by_cases hjh : h < j
    · rw [polynomialAffineClass_mul_eq_constant r c (a j) (hkill j hjh)]
      exact homogeneousComponent_eq_zero _ _ (by rw [totalDegree_C]; omega)
    · have hjh' : j.val < h.val := by
        have hle : j ≤ h := le_of_not_gt hjh
        exact_mod_cast (show j < h from lt_of_le_of_ne hle hj)
      apply homogeneousComponent_eq_zero
      have hd := totalDegree_mul (C (a j)) (polynomialAffineClass r c (F j))
      rw [totalDegree_C, zero_add] at hd
      exact (hd.trans (polynomialAffineClass_degree r c (j.val + 1) (F j) (hF j))).trans_lt
        (Nat.add_lt_add_right hjh' 1)
  · simp

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem pow_tag_killed {R : Type*} [CommRing R]
    (p ell : R) (A a k : ℕ) (ha : a ≤ A) (hk : a ≤ k) (hzero : p ^ A = 0) :
    (p ^ (A - a) * ell) * p ^ k = 0 := by
  have hAk : A ≤ A - a + k := by omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hAk
  have hpow : p ^ (A - a + k) = 0 := by rw [ht, pow_add, hzero, zero_mul]
  calc
    _ = p ^ (A - a + k) * ell := by rw [pow_add]; ring
    _ = 0 := by rw [hpow, zero_mul]

theorem pow_tag_top_factor {R : Type*} [CommRing R]
    (p ell : R) (A a k h B : ℕ) (ha : a ≤ A)
    (hB : B = a - h * k) (hBp : 0 < B) :
    (p ^ (A - a) * ell) * (p ^ k) ^ h = p ^ (A - B) * ell := by
  have hka : h * k < a := Nat.sub_pos_iff_lt.mp (hB ▸ hBp)
  have he : A - a + k * h = A - B := by rw [Nat.mul_comm k h]; omega
  calc
    _ = p ^ (A - a + k * h) * ell := by rw [pow_add, pow_mul]; ring
    _ = _ := by rw [he]

theorem zmod_primePower_tagged_affine_phase_bias_at_modulus {Index : Type*} [Fintype Index]
    (p A B k : ℕ) [NeZero p] (hBA : B ≤ A) {s : ℕ} (h : Fin s)
    (depth : Fin s → ℕ) (hdepth : ∀ j, depth j ≤ A)
    (hB : B = depth h - (h.val + 1) * k) (hBp : 0 < B)
    (hhigher : ∀ j, h < j → depth j ≤ k)
    (F : Fin s → MvPolynomial Index (ZMod (p ^ A)))
    (hF : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (ell : Fin s → ZMod (p ^ A)) (r : Index → ZMod (p ^ A)) :
    ‖𝔼 x : Index → ZMod (p ^ A),
      ZMod.stdAddChar (∑ j, (p : ZMod (p ^ A)) ^ (A - depth j) * ell j *
        eval (fun i => r i + (p : ZMod (p ^ A)) ^ k * x i) (F j))‖ ^ (2 ^ h.val) ≤
      𝔼 u : Fin h.val → Index → ZMod (p ^ B),
        if polynomialLinearRow (polynomialIterDifference h.val
          (map (ZMod.castHom (Nat.pow_dvd_pow p hBA) (ZMod (p ^ B)))
            (C (ell h) * homogeneousComponent (h.val + 1) (F h))) u) = 0
        then (1 : ℝ) else 0 := by
  let c : ZMod (p ^ A) := (p : ZMod (p ^ A)) ^ k
  let a : Fin s → ZMod (p ^ A) := fun j => (p : ZMod (p ^ A)) ^ (A - depth j) * ell j
  have hzero : (p : ZMod (p ^ A)) ^ A = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ A)
  have hkill : ∀ j, h < j → a j * c = 0 := by
    intro j hj
    exact pow_tag_killed _ _ A (depth j) k (hdepth j) (hhigher j hj) hzero
  have hdenom : a h * c ^ (h.val + 1) = (p ^ (A - B) : ℕ) * ell h := by
    simpa only [Nat.cast_pow] using
      pow_tag_top_factor (p : ZMod (p ^ A)) (ell h) A (depth h) k (h.val + 1) B
        (hdepth h) hB hBp
  have htop : homogeneousComponent (h.val + 1)
      (∑ j, C (a j) * polynomialAffineClass r c (F j)) =
      C (p ^ (A - B) : ZMod (p ^ A)) *
        (C (ell h) * homogeneousComponent (h.val + 1) (F h)) := by
    rw [tagged_affine_phase_top_component h F hF a r c hkill, hdenom,
      Nat.cast_pow, map_mul, mul_assoc]
  have hN : p ^ A = p ^ B * p ^ (A - B) := by
    rw [← pow_add, Nat.add_sub_of_le hBA]
  have hbound := zmod_polynomial_phase_bias_reduced_denominator_of_mul
    (p ^ A) (p ^ B) (p ^ (A - B)) hN h.val
    (∑ j, C (a j) * polynomialAffineClass r c (F j))
    (C (ell h) * homogeneousComponent (h.val + 1) (F h))
    (tagged_affine_phase_degree h F hF a r c hkill) (by simpa only [Nat.cast_pow] using htop)
  simpa only [map_sum, map_mul, eval_C, polynomialAffineClass_eval, a, c] using hbound

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem norm_le_rpow_div_two_pow (n : ℕ) (z : ℂ) (p t : ℝ) (hp : 0 < p)
    (hbound : ‖z‖ ^ (2 ^ n) ≤ p ^ t) :
    ‖z‖ ≤ p ^ (t / (2 ^ n : ℕ)) := by
  apply le_of_pow_le_pow_left₀ (by positivity : (2 ^ n : ℕ) ≠ 0)
    (Real.rpow_nonneg hp.le _)
  calc
    _ ≤ p ^ t := hbound
    _ = (p ^ (t / (2 ^ n : ℕ))) ^ (2 ^ n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      congr 1
      have hn : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
      exact (div_mul_cancel₀ _ hn).symm

theorem primePower_row_phase_decay_large
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A a b e : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V (ZMod (p ^ A)))
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ) (_ : b < B) (hBA : B ≤ A) (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      primePowerHomogeneousRankProbability p A B j.val hBA (F j) row ≤
        (p : ℝ) ^ (-C * B))
    (depth : Fin s → ℕ) (hdepth : ∀ j, depth j ≤ A)
    (hmax : ∀ j, depth j ≤ a) (hattained : ∃ j, depth j = a)
    (coeff : ∀ j, J j → ZMod (p ^ A))
    (hunit : ∀ j, 0 < depth j → ∀ {B : ℕ} (hB : B ≤ depth j),
      ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p (hB.trans (hdepth j)))
        (ZMod (p ^ B)) (coeff j i)))
    (hlarge : modularRankChargeFactor s * (b + e) < a)
    (r : V → ZMod (p ^ A)) :
    ‖𝔼 x : V → ZMod (p ^ A),
      ZMod.stdAddChar (∑ j, (p : ZMod (p ^ A)) ^ (A - depth j) *
        ∑ i, coeff j i * eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ ≤
      (p : ℝ) ^ (-modularRankDecayExponent s C * a) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  obtain ⟨h, k, B, hek, hhigher, hB, hbB, hBa, hnumeric⟩ :=
    exists_modular_uncharged_decay_parameters hs depth a b e hmax hattained hlarge p C hpR hC
  have hBh : B ≤ depth h := hB ▸ Nat.sub_le _ _
  have hBA : B ≤ A := hBh.trans (hdepth h)
  have hBp : 0 < B := (Nat.zero_le b).trans_lt hbB
  let Fs (j : Fin s) : MvPolynomial V (ZMod (p ^ A)) := polynomialCharacterRow (coeff j) (F j)
  have hFs : ∀ j, (Fs j).totalDegree ≤ j.val + 1 := by
    intro j
    exact polynomialCharacterRow_totalDegree_le _ _ (hF j)
  let f : (V → ZMod (p ^ A)) → ℂ := fun t =>
    ZMod.stdAddChar (∑ j, (p : ZMod (p ^ A)) ^ (A - depth j) * ∑ i, coeff j i * eval t (F j i))
  have hclasses (t : V → ZMod (p ^ A)) :
      ‖𝔼 x : V → ZMod (p ^ A), f (fun v => t v + (p : ZMod (p ^ A)) ^ k * x v)‖ ≤
        (p : ℝ) ^ (-C * B / (2 ^ h.val : ℕ)) := by
    have hphase := zmod_primePower_tagged_affine_phase_bias_at_modulus p A B k hBA h
      depth hdepth hB hBp hhigher Fs hFs (fun _ => 1) t
    have hr := hrank B hbB hBA h
      (fun i => ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)) (coeff h i))
      (hunit h (hBp.trans_le hBh) hBh)
    have hprob : (𝔼 u : Fin h.val → V → ZMod (p ^ B),
        if polynomialLinearRow (polynomialIterDifference h.val
          (map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
            (homogeneousComponent (h.val + 1) (Fs h))) u) = 0 then (1 : ℝ) else 0) ≤
          (p : ℝ) ^ (-C * B) := by
      simpa only [primePowerHomogeneousRankProbability, Fs,
        polynomialCharacterRow_homogeneousComponent, polynomialCharacterRow_map] using hr
    have hbias : ‖𝔼 x : V → ZMod (p ^ A),
        f (fun v => t v + (p : ZMod (p ^ A)) ^ k * x v)‖ ^ (2 ^ h.val) ≤
          (p : ℝ) ^ (-C * B) := by
      apply le_trans ?_ hprob
      simpa only [mul_one, map_one, one_mul, f, Fs, polynomialCharacterRow_eval] using hphase
    exact norm_le_rpow_div_two_pow h.val _ p (-C * B) (by exact_mod_cast hp.pos) hbias
  have hcoarse := norm_scalar_affine_class_mean_le
    ((p : ZMod (p ^ A)) ^ e) ((p : ZMod (p ^ A)) ^ (k - e)) r f
    ((p : ℝ) ^ (-C * B / (2 ^ h.val : ℕ))) (by
      simpa only [← pow_add, Nat.add_sub_of_le hek] using hclasses)
  exact hcoarse.trans hnumeric

theorem primePower_polynomial_character_decay
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A a b e : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V (ZMod (p ^ A)))
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ) (_ : b < B) (hBA : B ≤ A) (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      primePowerHomogeneousRankProbability p A B j.val hBA (F j) row ≤
        (p : ℝ) ^ (-C * B))
    (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) (horder : orderOf χ = p ^ a)
    (r : V → ZMod (p ^ A)) :
    ‖𝔼 x : V → ZMod (p ^ A),
      χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ ≤
      (p : ℝ) ^ (modularRankDecayExponent s C * modularRankChargeFactor s * (b + e)) *
        (p : ℝ) ^ (-modularRankDecayExponent s C * a) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hP : 0 ≤ modularRankDecayExponent s C := by
    dsimp [modularRankDecayExponent]
    positivity
  have hnorm : ‖𝔼 x : V → ZMod (p ^ A),
      χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ ≤ 1 := by
    calc
      _ ≤ 𝔼 x : V → ZMod (p ^ A),
          ‖χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ :=
        RCLike.norm_expect_le (K := ℂ)
      _ = 1 := by simp only [χ.norm_apply, Fintype.expect_const]
  apply modular_local_decay_budget hpR hP (by positivity) (by positivity) hnorm
  intro hlargeR
  have hlarge : modularRankChargeFactor s * (b + e) < a := by
    exact_mod_cast hlargeR
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  obtain ⟨depth, hdepth, coeff, hcoord, hunit, hphase⟩ :=
    exists_primePower_tagged_ambient_rows hp χ
  obtain ⟨hmax, hattained⟩ := primePower_character_tag_depth_max hp χ depth hcoord horder
  have h := primePower_row_phase_decay_large hs p A a b e hp C hC F hF hrank
    depth hdepth hmax hattained coeff hunit hlarge r
  simpa only [hphase, Nat.cast_pow] using h

theorem primePower_polynomial_image_characteristic_decay
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A b e : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V (ZMod (p ^ A)))
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ) (_ : b < B) (hBA : B ≤ A) (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      primePowerHomogeneousRankProbability p A B j.val hBA (F j) row ≤
        (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) :
    ‖finiteImageCharacteristic (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (fun x j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i)) χ‖ ≤
      ((p ^ (b + e) : ℕ) : ℝ) ^ (modularRankDecayExponent s C * modularRankChargeFactor s) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
  have hkill : χ ^ (p ^ A) = 1 := by
    ext x
    rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow]
    have hz : (p ^ A) • x = 0 := by
      ext j i
      simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
    rw [hz, AddChar.map_zero_eq_one, AddChar.one_apply]
  obtain ⟨a, _, horder⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hkill)
  have h := primePower_polynomial_character_decay hs p A a b e hp C hC F hF hrank χ horder r
  rw [finiteImageCharacteristic, FiniteProbabilityWeights.uniform_complexMean]
  apply h.trans_eq
  rw [horder, Nat.cast_pow, Nat.cast_pow,
    ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ p),
    ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ p)]
  congr 1 <;> congr 1 <;> push_cast <;> ring

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem map_integerPolynomial_homogeneousComponent
    {V : Type*} (p A B d : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : MvPolynomial V ℤ) :
    map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
      (homogeneousComponent d (map (Int.castRingHom (ZMod (p ^ A))) F)) =
      map (Int.castRingHom (ZMod (p ^ B))) (homogeneousComponent d F) := by
  have hcomp : (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))).comp
      (Int.castRingHom (ZMod (p ^ A))) = Int.castRingHom (ZMod (p ^ B)) :=
    RingHom.eq_intCast' _
  rw [← map_homogeneousComponent, MvPolynomial.map_map, hcomp]

theorem primePowerHomogeneousRankProbability_integerPolynomial
    {V J : Type*} [Fintype V] [Fintype J]
    (p A B n : ℕ) [NeZero p] (hBA : B ≤ A)
    (F : J → MvPolynomial V ℤ) (row : J → ZMod (p ^ B)) :
    primePowerHomogeneousRankProbability p A B n hBA
      (fun i => map (Int.castRingHom (ZMod (p ^ A))) (F i)) row =
      integerPolynomialRankProbability p B n F row := by
  unfold primePowerHomogeneousRankProbability integerPolynomialRankProbability
  have hF : (fun i => map (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B)))
      (homogeneousComponent (n + 1) (map (Int.castRingHom (ZMod (p ^ A))) (F i)))) =
      (fun i => map (Int.castRingHom (ZMod (p ^ B)))
        (homogeneousComponent (n + 1) (F i))) := by
    funext i
    exact map_integerPolynomial_homogeneousComponent p A B (n + 1) hBA (F i)
  rw [hF]

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

namespace Erdos3
open scoped BigOperators Classical

theorem largestTestedBadDepth_not_bad {Ω : Type*} (A : ℕ → ℕ)
    (bad : ℕ → ℕ → Ω → Prop) (p : ℕ) (x : Ω) {a : ℕ}
    (ha : largestTestedBadDepth A bad p x < a) (hA : a ≤ A p) : ¬ bad p a x := by
  intro hbad
  have hmem : a ∈ (Finset.Icc 1 (A p)).filter (fun a => bad p a x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hA⟩, hbad⟩
  exact (not_le_of_gt ha) (Finset.le_sup (f := id) hmem)

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

theorem modularBoundedCoefficientPolynomial_degree {K R : Type*}
    [Fintype K] [CommRing R] (h : ℕ)
    (c : BoundedCoefficientExponent K h → R) :
    (modularBoundedCoefficientPolynomial h c).totalDegree ≤ h := by
  unfold modularBoundedCoefficientPolynomial
  apply totalDegree_finsetSum_le
  intro e _
  exact (totalDegree_monomial_le e.val (c e)).trans e.property

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)


end Erdos3

end

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FiniteUnchargedPrimeDensity
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem finite_prime_depth_mass {p : ℕ} (hp : 2 ≤ p) (A : ℕ) :
    (∑ a ∈ Finset.range A, 1 / ((p : ℝ) ^ (a + 1)) ^ 2) ≤ 2 / (p : ℝ) ^ 2 := by
  let r : ℝ := 1 / (p : ℝ) ^ 2
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hr : r ≤ 1 / 2 := by
    dsimp only [r]
    apply (div_le_div_iff₀ (pow_pos hp0 2) (by norm_num)).mpr
    nlinarith
  calc
    _ = r * ∑ a ∈ Finset.range A, r ^ a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [r]
      simp only [one_div, inv_pow]
      rw [pow_right_comm, pow_succ' _ a, mul_inv]
    _ ≤ r * ∑ a ∈ Finset.range A, (1 / (2 : ℝ)) ^ a := by
      apply mul_le_mul_of_nonneg_left _ hr0
      exact Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ hr0 hr a)
    _ ≤ r * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le A) hr0
    _ = _ := by dsimp only [r]; ring

theorem finiteCharacter_order_dvd_of_annihilation {H : Type*} [AddCommGroup H]
    (N : ℕ) (hN : ∀ x : H, N • x = 0) (χ : AddChar H ℂ) : orderOf χ ∣ N := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hN x]
  exact χ.map_zero_eq_one

theorem finiteCharacter_uncharged_prime_mass {I H : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (f : AddChar H ℂ → ℝ)
    (hdecay : ∀ χ, χ ≠ 1 → f χ ≤ 1 / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) :
    (∑ χ : AddChar H ℂ with χ ≠ 1, f χ) ≤ 2 / (p : ℝ) ^ 2 := by
  let S := Finset.univ.filter (fun χ : AddChar H ℂ => χ ≠ 1)
  let orders := (Finset.range A).image (fun a => p ^ (a + 1))
  have hmap : (S : Set (AddChar H ℂ)).MapsTo orderOf orders := by
    intro χ hχ
    obtain ⟨a, ha, heq⟩ := (Nat.dvd_prime_pow hp).mp
      (finiteCharacter_order_dvd_of_annihilation (p ^ A) hann χ)
    have ha0 : 0 < a := by
      by_contra hz
      have haZ : a = 0 := by omega
      have ho : orderOf χ = 1 := by simpa only [haZ, pow_zero] using heq
      exact (Finset.mem_filter.mp hχ).2 (orderOf_eq_one_iff.mp ho)
    exact Finset.mem_image.mpr ⟨a - 1, Finset.mem_range.mpr (by omega),
      by rw [Nat.sub_add_cancel ha0]; exact heq.symm⟩
  change (∑ χ ∈ S, f χ) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  have hinner (q : ℕ) (hq : q ∈ orders) :
      (∑ χ ∈ S with orderOf χ = q, f χ) ≤ 1 / (q : ℝ) ^ 2 := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
    have hq0 : 0 < p ^ (a + 1) := pow_pos hp.pos _
    have hqR : (0 : ℝ) < ((p ^ (a + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr hq0
    have hc : (S.filter (fun χ => orderOf χ = p ^ (a + 1))).card ≤
        (p ^ (a + 1)) ^ Fintype.card I :=
      (Finset.card_le_card (by
        intro χ hχ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hχ).2⟩)).trans
          (finiteCharacter_exactOrder_card_le π hπ _ hq0)
    calc
      _ ≤ ∑ _χ ∈ S with orderOf _χ = p ^ (a + 1),
          1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2) := by
        apply Finset.sum_le_sum
        intro χ hχ
        simpa only [(Finset.mem_filter.mp hχ).2] using
          hdecay χ (Finset.mem_filter.mp (Finset.mem_filter.mp hχ).1).2
      _ = (S.filter (fun χ => orderOf χ = p ^ (a + 1))).card *
          (1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((p ^ (a + 1) : ℕ) : ℝ) ^ Fintype.card I *
          (1 / ((p ^ (a + 1) : ℕ) : ℝ) ^ (Fintype.card I + 2)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = _ := by
        rw [pow_add (((p ^ (a + 1) : ℕ) : ℝ)) (Fintype.card I) 2]
        field_simp
  calc
    _ ≤ ∑ q ∈ orders, 1 / (q : ℝ) ^ 2 := Finset.sum_le_sum hinner
    _ = ∑ a ∈ Finset.range A, 1 / ((p : ℝ) ^ (a + 1)) ^ 2 := by
      rw [Finset.sum_image]
      · simp only [Nat.cast_pow]
      · intro a _ b _ hab
        exact Nat.add_right_cancel (Nat.pow_right_injective hp.two_le hab)
    _ ≤ _ := finite_prime_depth_mass hp.two_le A

theorem finiteImage_uncharged_prime_density {I H X : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [Fintype X]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (w : FiniteProbabilityWeights X) (Y : X → H)
    (hdecay : ∀ χ : AddChar H ℂ, χ ≠ 1 → ‖finiteImageCharacteristic w Y χ‖ ≤
      1 / (orderOf χ : ℝ) ^ (Fintype.card I + 2)) (z : H) :
    |(Fintype.card H : ℝ) * finiteImageMass w Y z - 1| ≤ 2 / (p : ℝ) ^ 2 := by
  have he := finiteImageFourier_truncation w Y {1} z (Nat.cast_nonneg (Fintype.card H))
  have hcard : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardC : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Complex.ofReal_natCast, div_self hcard, div_self hcardC, one_mul,
    Finset.sum_singleton, finiteImageCharacteristic, AddChar.one_apply,
    FiniteProbabilityWeights.complexMean_const, star_one, mul_one] at he
  have htail := finiteCharacter_uncharged_prime_mass π hπ hp hann _ hdecay
  have htail' : spectrumTail {1} (fun χ => ‖finiteImageCharacteristic w Y χ‖) ≤ 2 / (p : ℝ) ^ 2 := by
    simpa only [spectrumTail, Finset.mem_singleton, Finset.sum_filter, ite_not] using htail
  have hbound := he.trans htail'
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hbound

theorem finiteImage_uncharged_prime_density_rpow {I H X : Type*} [Fintype I]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [Fintype X]
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π)
    {p A : ℕ} (hp : p.Prime) (hann : ∀ x : H, (p ^ A) • x = 0)
    (w : FiniteProbabilityWeights X) (Y : X → H) {P : ℝ}
    (hP : ((Fintype.card I + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar H ℂ, χ ≠ 1 → ‖finiteImageCharacteristic w Y χ‖ ≤
      (orderOf χ : ℝ) ^ (-P)) (z : H) :
    |(Fintype.card H : ℝ) * finiteImageMass w Y z - 1| ≤ 2 / (p : ℝ) ^ 2 := by
  have hfull (χ : AddChar H ℂ) : ‖finiteImageCharacteristic w Y χ‖ ≤
      1 * (orderOf χ : ℝ) ^ (-P) := by
    by_cases hχ : χ = 1
    · subst χ
      simp only [finiteImageCharacteristic, AddChar.one_apply,
        FiniteProbabilityWeights.complexMean_const, norm_one, orderOf_one,
        Nat.cast_one, Real.one_rpow, mul_one, le_refl]
    · simpa only [one_mul] using hdecay χ hχ
  have hinteger := finiteCharacter_integer_decay_of_rpow (I := I)
    (show (0 : ℝ) ≤ 1 by norm_num) hP _ hfull
  exact finiteImage_uncharged_prime_density π hπ hp hann w Y (fun χ _ => hinteger χ) z

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem modularForecastRankConstant_decay (s D : ℕ) :
    modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) = (D + 2 : ℕ) := by
  unfold modularRankDecayExponent modularForecastRankConstant
  push_cast
  have htwo : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem modularForecastRankConstant_dimension (s D d : ℕ) (hd : d ≤ D) :
    ((d + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) := by
  rw [modularForecastRankConstant_decay]
  exact_mod_cast Nat.add_le_add_right hd 2

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

section RankBounds

variable {s : ℕ} (hs : 0 < s) {J : Fin s → Type*} [∀ j, Fintype (J j)]
  (p A b e : L → ℕ) [∀ l, NeZero (p l)]
  (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
  (C : ℝ) (hC : 0 ≤ C)
  (F : ∀ j, J j → MvPolynomial V ℤ)
  (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
  (hrank : ∀ (l : L) (B : ℕ), b l < B → B ≤ A l → ∀ (j : Fin s)
    (row : J j → ZMod (p l ^ B)), (∃ i, IsUnit (row i)) →
    integerPolynomialRankProbability (p l) B j.val (F j) row ≤ (p l : ℝ) ^ (-C * B))
  (r : ∀ l, V → ZMod (p l ^ A l))

include hs hp hinj hC hF hrank

end RankBounds

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem finiteImageMass_outputEquiv {X Z W : Type*} [Fintype X]
    [DecidableEq Z] [DecidableEq W] (law : FiniteProbabilityWeights X)
    (Y : X → Z) (e : Z ≃ W) (z : Z) :
    finiteImageMass law (fun x => e (Y x)) (e z) = finiteImageMass law Y z := by
  unfold finiteImageMass
  simp only [e.injective.eq_iff]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

section TopPart

variable {I J R : Type*} [CommRing R]

end TopPart

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

section RingMap

variable {K L A R S : Type*} [CommRing R] [CommRing S]

theorem homogeneousComponent_map_ringHom (f : R →+* S) (h : ℕ) (P : MvPolynomial K R) :
    homogeneousComponent h (P.map f) = (homogeneousComponent h P).map f := by
  ext a
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp only [map_zero]

theorem modularBoundedCoefficientPolynomial_map [Fintype K]
    (f : R →+* S) (h : ℕ) (c : BoundedCoefficientExponent K h → R) :
    modularBoundedCoefficientPolynomial h (fun e => f (c e)) =
      (modularBoundedCoefficientPolynomial h c).map f := by
  simp only [modularBoundedCoefficientPolynomial, map_sum, MvPolynomial.map_monomial]

end RingMap

section ActualResidual

variable {D G R S : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R] [CommRing S]

end ActualResidual
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {L : ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)


theorem allocatedCongruenceModulusBad_good (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N)
    (hgood : ¬ allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C N x)
    (v : LayerSamplerVariables G I n B → ZMod N) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) (hw : ∃ o, IsUnit (w o)) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
      (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
      spatial (kernel j) (block j) (fun o l => x ⟨j,(o,l)⟩) v w ≤ (N : ℝ) ^ (-C) :=
  le_of_not_gt (fun hbad => hgood ⟨v, j, w, hw, hbad⟩)

theorem allocatedCongruenceRankBad_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)
    (p : P) (a : ℕ) (x : AllocatedCongruenceScalarIndex X E inactive L → ℤ)
    (hgood : ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a x)
    (v : LayerSamplerVariables G I n B → ZMod (p.val ^ a)) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p.val ^ a))
    (hw : ∃ o, IsUnit (w o)) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod (p.val ^ a)))
      (fun j q i => (r j q i : ZMod (p.val ^ a)))
      (fun b q => (projection j b q : ZMod (p.val ^ a)))
      spatial (kernel j) (block j) (fun o l => (x ⟨j,(o,l)⟩ : ZMod (p.val ^ a))) v w ≤
        ((p.val ^ a : ℕ) : ℝ) ^ (-C) := by
  have hmod : ¬ allocatedCongruenceModulusBad inactive noise r projection spatial kernel block
      C (p.val ^ a) (fun i => (x i : ZMod (p.val ^ a))) :=
    fun hbad => hgood ⟨p.property, hbad⟩
  exact allocatedCongruenceModulusBad_good inactive noise r projection spatial kernel block C
    (p.val ^ a) (fun i => (x i : ZMod (p.val ^ a))) hmod v j w hw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)]
    [∀ a, Fintype (B a)] {N L : ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ConditionPolynomialMapDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R S : Type*} [CommRing R] [CommRing S]

theorem conditionPolynomial_totalDegree_le (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) :
    (conditionPolynomial f hf v P).totalDegree ≤ P.totalDegree := by
  let u : I → R := fun i => if i ∈ Set.range f then 0 else v i
  have ht : polynomialTranslate u P ∈ weightedSupportLE (1 : I → ℕ) P.totalDegree := by
    apply weightedSupportLE_aeval (1 : I → ℕ) (1 : I → ℕ)
      (fun i => X i + C (u i))
    · intro i
      exact (weightedSupportLE (1 : I → ℕ) 1).add_mem
        (weightedSupportLE_X _ i) (weightedSupportLE_C _ _ _)
    · exact (mem_weightedSupportLE_one_iff P _).mpr le_rfl
  apply (mem_weightedSupportLE_one_iff _ _).mp
  intro a ha
  change a ∈ (conditionPolynomial f hf v P).support at ha
  have hmem : a.mapDomain f ∈ (polynomialTranslate u P).support := by
    simpa only [conditionPolynomial, u, mem_support_iff, coeff_killCompl] using ha
  have h : Finsupp.weight (fun _ : I => 1) (a.mapDomain f) ≤ P.totalDegree := ht hmem
  change Finsupp.weight (fun _ : J => 1) a ≤ P.totalDegree
  simpa only [← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using h

theorem conditionPolynomial_map (φ : R →+* S) (f : J → I)
    (hf : Function.Injective f) (v : I → R) (P : MvPolynomial I R) :
    map φ (conditionPolynomial f hf v P) =
      conditionPolynomial f hf (fun i => φ (v i)) (map φ P) := by
  unfold conditionPolynomial
  rw [← killCompl_map, polynomialTranslate_map_coefficients]
  apply congrArg (fun u : I → S => killCompl hf (polynomialTranslate u (map φ P)))
  funext i
  split_ifs <;> simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

theorem allocatedCongruenceIntegerPolynomial_degree
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o).totalDegree ≤
      j.val + 1 := by
  rcases o with x | i | a
  · apply (conditionPolynomial_totalDegree_le _ _ _ _).trans
    apply (totalDegree_add _ _).trans
    apply max_le
    · rw [totalDegree_C]
      exact Nat.zero_le _
    · exact (spatialRankPolynomial_degree _).trans (by omega)
  · exact (conditionPolynomial_totalDegree_le _ _ _ _).trans
      (modularBoundedCoefficientPolynomial_degree _ _)
  · exact (conditionPolynomial_totalDegree_le _ _ _ _).trans
      (modularBoundedCoefficientPolynomial_degree _ _)

theorem allocatedCongruenceIntegerPolynomial_top_reduce
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (homogeneousComponent (j.val + 1)
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o)).map
        (Int.castRingHom (ZMod N)) =
      allocatedOriginalTaggedTop inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
        (fun k => (v k : ZMod N)) (allocatedCongruenceOutputEmbedding inactive j o) := by
  rw [← homogeneousComponent_map_ringHom]
  rcases o with x | i | a
  · have hx : j.val + 1 = 1 := by simp only [x.property, zero_add]
    simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_spatial, allocatedOriginalTaggedTop, hx,
      map_add, map_C, Int.coe_castRingHom]
    have hs : (spatialRankPolynomial (fun d => noise (d, x.val))).map
        (Int.castRingHom (ZMod N)) =
        spatialRankPolynomial (fun d => (noise (d, x.val) : ZMod N)) := by
      simp only [spatialRankPolynomial, map_sum, MvPolynomial.map_monomial,
        Int.coe_castRingHom]
    rw [hs]
    simp only [conditionPolynomial, map_add, polynomialTranslate_C, killCompl_C]
    have hc : homogeneousComponent 1 (C (base x.val : ZMod N) :
        MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)) = 0 :=
      homogeneousComponent_eq_zero _ _ (by rw [totalDegree_C]; exact zero_lt_one)
    rw [hc, zero_add]
  · simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop,
      modularDeckPolynomial, ← modularBoundedCoefficientPolynomial_map,
      Int.coe_castRingHom]
  · simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop,
      ← modularBoundedCoefficientPolynomial_map, Int.coe_castRingHom,
      allocatedCongruenceIntegerEmbedding]
    rfl

theorem allocatedCongruenceIntegerPolynomial_top_eq_actual_rank
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (homogeneousComponent (j.val + 1)
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o)).map
        (Int.castRingHom (ZMod N)) =
      allocatedCongruenceRankPolynomial inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
        spatial kernel block
        (fun z => allocatedSelectedRankCoefficients inactive j (fun q => (noise q : ZMod N))
          (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
          spatial kernel block (allocatedCongruenceOutputEmbedding inactive j z))
        (fun k => (v k : ZMod N)) o := by
  rw [allocatedCongruenceRankPolynomial_original]
  exact allocatedCongruenceIntegerPolynomial_top_reduce N inactive j base noise r projection v o

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients
  inactive noise r projection spatial kernel block

theorem allocatedCongruenceIntegerPolynomial_rank_probability
    (p a : ℕ) [NeZero p] (base : X → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p ^ a)) :
    integerPolynomialRankProbability p a j.val
      (allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) w =
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod (p ^ a)))
      (fun j q i => (r j q i : ZMod (p ^ a)))
      (fun b q => (projection j b q : ZMod (p ^ a))) spatial (kernel j) (block j)
      (fun o l => (selected ⟨j,(o,l)⟩ : ZMod (p ^ a))) (fun k => (v k : ZMod (p ^ a))) w := by
  unfold integerPolynomialRankProbability allocatedCongruenceRankFailureProbability
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceIntegerPolynomial_top_eq_actual_rank
      (p ^ a) inactive j base noise r (projection j) spatial (kernel j) (block j)]
  simp only [polynomialCharacterRow, smul_eq_C_mul]

theorem allocatedCongruenceIntegerPolynomial_rank_of_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p : P) (a : ℕ)
    (hgood : ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a selected)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p.val ^ a))
    (hw : ∃ o, IsUnit (w o)) :
    integerPolynomialRankProbability p.val a j.val
      (allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) w ≤
      (p.val : ℝ) ^ (-C * a) := by
  rw [allocatedCongruenceIntegerPolynomial_rank_probability inactive noise r projection spatial kernel block]
  have h := allocatedCongruenceRankBad_good inactive noise r projection spatial kernel block
    P C p a selected hgood (fun k => (v k : ZMod (p.val ^ a))) j w hw
  calc
    _ ≤ ((p.val ^ a : ℕ) : ℝ) ^ (-C) := h
    _ = (p.val : ℝ) ^ (-C * a) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p.val)]
      congr 1
      ring

theorem allocatedCongruence_largest_bad_depth_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ)
    (p : P) (a : ℕ)
    (ha : largestTestedBadDepth A
      (allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C)
      p.val selected < a) (hA : a ≤ A p.val) :
    ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a selected :=
  largestTestedBadDepth_not_bad A _ p.val selected ha hA

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTInactiveDensityGoodPrimeDeletion
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem primePower_integer_polynomial_shifted_uncharged_density
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ), 0 < B → B ≤ A → ∀ (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability p B j.val (F j) row ≤ (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (z : ∀ j, J j → ZMod (p ^ A)) :
    let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
    let Y := fun (x : V → ZMod (p ^ A)) j i =>
      eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i)
    |(Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z - 1| ≤
      2 / (p : ℝ) ^ 2 ∧
    (Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z ≤
      1 + 2 / (p : ℝ) ^ 2 := by
  dsimp only
  let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
  let Y := fun (x : V → ZMod (p ^ A)) j i =>
    eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i)
  have hdecay (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) (_hχ : χ ≠ 1) :
      ‖finiteImageCharacteristic law Y χ‖ ≤
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
    have hlocal := primePower_polynomial_image_characteristic_decay hs p A 0 0 hp C hC
      (fun j i => map (Int.castRingHom (ZMod (p ^ A))) (F j i))
      (fun j i => (totalDegree_map_le _ _).trans (hF j i))
      (by
        intro B hB hBA j row hunit
        rw [primePowerHomogeneousRankProbability_integerPolynomial]
        exact hrank B hB hBA j row hunit)
      r χ
    simpa only [law, Y, eval_map, Nat.zero_add, pow_zero, Nat.cast_one, Real.one_rpow,
      one_mul] using hlocal
  have hann (x : ∀ j, J j → ZMod (p ^ A)) : (p ^ A) • x = 0 := by
    ext j i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have h := finiteImage_uncharged_prime_density_rpow (taggedIntegerResidue J (p ^ A))
    (taggedIntegerResidue_surjective J (p ^ A)) hp hann law Y hP hdecay z
  have hd : |(Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z - 1| ≤
      2 / (p : ℝ) ^ 2 := by
    simpa only [← Nat.card_eq_fintype_card] using h
  exact ⟨hd, by linarith [(abs_le.mp hd).2]⟩

theorem localPrimePowerIntegerPolynomialOutput_uncharged_density
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ), 0 < B → B ≤ A → ∀ (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability p B j.val (F j) row ≤ (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (z : Sigma J → ZMod (p ^ A)) :
    |rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z - 1| ≤
        2 / (p : ℝ) ^ 2 ∧
    rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z ≤
        1 + 2 / (p : ℝ) ^ 2 := by
  let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
  let Y := fun (x : V → ZMod (p ^ A)) (j : Sigma J) =>
    (localPrimePowerIntegerPolynomialOutput p A 0 F r x j : ZMod (p ^ A))
  let curry := (taggedPolynomialOutputCurry J (p ^ A)).toEquiv
  have hY : (fun x => curry (Y x)) = fun x j i =>
      eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i) := by
    funext x j i
    change (localPrimePowerIntegerPolynomialOutput p A 0 F r x ⟨j, i⟩ : ZMod (p ^ A)) = _
    rw [localPrimePowerIntegerPolynomialOutput_reduce]
    simp only [pow_zero, one_mul]
  have hdensity : rationalOutputDensity law
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z =
      (Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law
        (fun x j i => eval₂ (Int.castRingHom (ZMod (p ^ A)))
          (fun v => r v + x v) (F j i)) (curry z) := by
    change (Fintype.card (Sigma J → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z = _
    rw [Fintype.card_congr curry, ← finiteImageMass_outputEquiv law Y curry z, hY]
  rw [hdensity]
  exact primePower_integer_polynomial_shifted_uncharged_density hs p A hp C hC hP
    F hF hrank r (curry z)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

omit [∀ j, Fintype (I j)] in

theorem allocatedCongruenceForecastRankConstant_dimension
    (hm : 0 < m) (D : ℕ)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D) :
    ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E inactive)) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) := by
  apply modularForecastRankConstant_dimension
  rw [Fintype.card_sigma]
  exact (allocatedCongruenceRankOutput_sum_card_le hm inactive).trans hD

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ActualFixedSpatialUnchargedDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem localReference_degree
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value) j) :
    (path.localReferencePolynomial raw j o).totalDegree ≤ j.val + 1 :=
  allocatedCongruenceIntegerPolynomial_degree (allocatedShortAxis (I := I) U b S.value)
    j path.base path.noise (allocatedReadDeck path.read)
    (fun a => allocatedReadProjection path.read ⟨j, a.val⟩)
    (samplerFrozenRaw (layerSamplerDegree I n) raw) o

omit [Fintype Tsp] in

theorem localReference_rank
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (p : path.primes) (a : ℕ) (ha : path.referenceBadDepth p.val < a)
    (hA : a ≤ path.exponent p.val) (j : Fin m)
    (row : AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value) j → ZMod (p.val ^ a))
    (hunit : ∃ o, IsUnit (row o)) :
    letI := path.primeNeZero
    integerPolynomialRankProbability p.val a j.val
      (path.localReferencePolynomial raw j) row ≤
      (p.val : ℝ) ^ (-(modularForecastRankConstant m Dmod : ℝ) * a) := by
  let := path.primeNeZero
  exact allocatedCongruenceIntegerPolynomial_rank_of_good
    (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    spatial kernel block path.primes (modularForecastRankConstant m Dmod : ℝ) p a
    (allocatedCongruence_largest_bad_depth_good
      (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
      (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
      spatial kernel block path.primes path.exponent
      (modularForecastRankConstant m Dmod : ℝ) p a ha hA)
    path.base (samplerFrozenRaw (layerSamplerDegree I n) raw) j row hunit

omit [Fintype Tsp] in

theorem localReference_uncharged_density_oai
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (p : path.primes) (hbad : path.referenceBadDepth p.val = 0)
    (hpres : path.prescribed p.val = 0)
    (z : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod (p.val ^ path.exponent p.val)) :
    letI := path.primeNeZero
    let density := rationalOutputDensity
      (FiniteProbabilityWeights.uniform
        (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
          ZMod (p.val ^ path.exponent p.val)))
      (localPrimePowerIntegerPolynomialOutput p.val (path.exponent p.val) (path.prescribed p.val)
        (path.localReferencePolynomial raw) (path.origin p))
      (p.val ^ path.exponent p.val) z
    |density - 1| ≤ 2 / (p.val : ℝ) ^ 2 ∧ density ≤ 1 + 2 / (p.val : ℝ) ^ 2 := by
  let := path.primeNeZero
  have hdim :
      ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
        (allocatedShortAxis (I := I) U b S.value))) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) :=
    allocatedCongruenceForecastRankConstant_dimension
      (allocatedShortAxis (I := I) U b S.value) hm Dmod hD
  have hrank (a : ℕ) (ha : 0 < a) (hA : a ≤ path.exponent p.val) (j : Fin m)
      (row : AllocatedCongruenceRankOutput X Eout
        (allocatedShortAxis (I := I) U b S.value) j → ZMod (p.val ^ a))
      (hunit : ∃ o, IsUnit (row o)) :
      integerPolynomialRankProbability p.val a j.val (path.localReferencePolynomial raw j) row ≤
        (p.val : ℝ) ^ (-(modularForecastRankConstant m Dmod : ℝ) * a) :=
    path.localReference_rank raw p a (by simpa only [hbad] using ha) hA j row hunit
  have hdensity := localPrimePowerIntegerPolynomialOutput_uncharged_density hm p.val
    (path.exponent p.val) (path.prime p.val p.property)
    (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _) hdim
    (path.localReferencePolynomial raw) (path.localReference_degree raw) hrank (path.origin p) z
  simpa only [hpres, rationalOutputDensity, ← Nat.card_eq_fintype_card] using hdensity

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.localReference_uncharged_density_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.localReference_uncharged_density_oai
