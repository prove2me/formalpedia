-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:32:04.4757+00:00
-- url     : https://prove2.me/submissions/427113b2-5742-47e7-8ca6-ac85ddf10288

import Mathlib
import Definitions.Def_OAIQ095D008
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_diagonal_whole_shell_masked_rate
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_movingPattern_half_log_good_masked_whole_shell_rate

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing internal frequencies from the root downwards -/

namespace Ostmann

open scoped BigOperators

theorem frequencyTreeWeight_nonneg {A : Type} (K : A → A → A → ℝ) (W : A → ℝ)
    (hK : ∀ a b c, 0 ≤ K a b c) (hW : ∀ a, 0 ≤ W a)
    (n : ℕ) (x : FrequencyTree A n) : 0 ≤ frequencyTreeWeight K W n x := by
  induction n with
  | zero => exact hW x
  | succ n ih => exact mul_nonneg (mul_nonneg (hK _ _ _) (ih x.2.1)) (ih x.2.2)

/-- Each pair of parent frequencies is summed before either child pair.
Only the leaf mass remains after all internal frequencies are eliminated. -/
theorem frequencyTree_sum_le {A : Type} [Fintype A]
    (K : A → A → A → ℝ) (W : A → ℝ) (C : ℝ)
    (hK : ∀ a b c, 0 ≤ K a b c) (hW : ∀ a, 0 ≤ W a) (hC : 0 ≤ C)
    (hsum : ∀ b c, ∑ a : A, K a b c ≤ C) (n : ℕ) :
    (∑ x : FrequencyTree A n, frequencyTreeWeight K W n x) ≤
      C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n) := by
  induction n with
  | zero => simp [FrequencyTree, frequencyTreeWeight]
  | succ n ih =>
    have hweight := frequencyTreeWeight_nonneg K W hK hW n
    have hsum0 : 0 ≤ ∑ x : FrequencyTree A n, frequencyTreeWeight K W n x :=
      Finset.sum_nonneg fun x _ => hweight x
    have hbound0 : 0 ≤ C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n) :=
      mul_nonneg (pow_nonneg hC _) (pow_nonneg (Finset.sum_nonneg fun a _ => hW a) _)
    change (∑ x : A × FrequencyTree A n × FrequencyTree A n,
      K x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) *
        frequencyTreeWeight K W n x.2.1 * frequencyTreeWeight K W n x.2.2) ≤ _
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x : FrequencyTree A n, ∑ y : FrequencyTree A n,
          (∑ a : A, K a (frequencyRoot n x) (frequencyRoot n y)) *
            frequencyTreeWeight K W n x * frequencyTreeWeight K W n y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        simp only [Finset.sum_mul]
      _ ≤ ∑ x : FrequencyTree A n, ∑ y : FrequencyTree A n,
          C * frequencyTreeWeight K W n x * frequencyTreeWeight K W n y := by
        exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hsum _ _) (hweight x)) (hweight y)
      _ = C * ((∑ x : FrequencyTree A n, frequencyTreeWeight K W n x) *
          (∑ y : FrequencyTree A n, frequencyTreeWeight K W n y)) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring
      _ ≤ C * ((C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n)) *
          (C ^ (2 ^ n - 1) * (∑ a : A, W a) ^ (2 ^ n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul ih ih hsum0 hbound0) hC
      _ = _ := by
        have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by omega
        have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have hnodes : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + (2 ^ n - 1) + 1 := by omega
        rw [hnodes, hpow, pow_add, pow_add, pow_add, pow_one]
        ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_LcmFrequencySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reciprocal-lcm sum in the frequency budget

The gcd coordinates embed each frequency pair into three independent
positive harmonic sums. No asymptotic divisor estimate is used here.
-/

namespace Ostmann

open scoped BigOperators

theorem gcdFrequencyCoordinates_recover (x : ℕ × ℕ) :
    (gcdFrequencyCoordinates x).1 * (gcdFrequencyCoordinates x).2.1 = x.1 ∧
    (gcdFrequencyCoordinates x).1 * (gcdFrequencyCoordinates x).2.2 = x.2 := by
  exact ⟨Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)⟩

theorem gcdFrequencyCoordinates_injective : Function.Injective gcdFrequencyCoordinates := by
  intro x y h
  obtain ⟨hx₁, hx₂⟩ := gcdFrequencyCoordinates_recover x
  obtain ⟨hy₁, hy₂⟩ := gcdFrequencyCoordinates_recover y
  apply Prod.ext
  · exact hx₁.symm.trans ((congrArg (fun z : ℕ × ℕ × ℕ => z.1 * z.2.1) h).trans hy₁)
  · exact hx₂.symm.trans ((congrArg (fun z : ℕ × ℕ × ℕ => z.1 * z.2.2) h).trans hy₂)

theorem gcdFrequencyCoordinates_lcm (a b : ℕ) (ha : 0 < a) :
    (gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.1 *
      (gcdFrequencyCoordinates (a, b)).2.2 = a.lcm b := by
  have hg := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨ha', hb'⟩ := gcdFrequencyCoordinates_recover (a, b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    _ = ((gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.1) *
        ((gcdFrequencyCoordinates (a, b)).1 * (gcdFrequencyCoordinates (a, b)).2.2) := by
      dsimp [gcdFrequencyCoordinates]
      ring
    _ = a * b := by rw [ha', hb']
    _ = _ := (Nat.gcd_mul_lcm a b).symm

theorem gcdFrequencyCoordinates_mem {N a b : ℕ}
    (ha : a ∈ Finset.Icc 1 N) (hb : b ∈ Finset.Icc 1 N) :
    gcdFrequencyCoordinates (a, b) ∈
      (Finset.Icc 1 N).product ((Finset.Icc 1 N).product (Finset.Icc 1 N)) := by
  obtain ⟨ha₀, haN⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb₀, hbN⟩ := Finset.mem_Icc.mp hb
  have hap : 0 < a := ha₀
  have hbp : 0 < b := hb₀
  have hg := Nat.gcd_pos_of_pos_left b hap
  have hga := Nat.le_of_dvd hap (Nat.gcd_dvd_left a b)
  have hgb := Nat.le_of_dvd hbp (Nat.gcd_dvd_right a b)
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hg, hga.trans haN⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_Icc.mpr ⟨Nat.div_pos hga hg, (Nat.div_le_self _ _).trans haN⟩
  · exact Finset.mem_Icc.mpr ⟨Nat.div_pos hgb hg, (Nat.div_le_self _ _).trans hbN⟩

/-- Exact finite bound before estimating the harmonic sum. -/
theorem reciprocal_lcm_sum_le_harmonic_cube (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹) ≤
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ^ 3 := by
  let S := Finset.Icc 1 N
  let w : ℕ × ℕ × ℕ → ℝ := fun z => (z.1 : ℝ)⁻¹ * (z.2.1 : ℝ)⁻¹ * (z.2.2 : ℝ)⁻¹
  have hw (x : ℕ × ℕ) (hx : x ∈ S.product S) :
      ((x.1.lcm x.2 : ℕ) : ℝ)⁻¹ = w (gcdFrequencyCoordinates x) := by
    have ha : 0 < x.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
    rw [← gcdFrequencyCoordinates_lcm x.1 x.2 ha]
    simp only [w, Nat.cast_mul, mul_inv_rev]
    ring
  have hsub : (S.product S).image gcdFrequencyCoordinates ⊆ S.product (S.product S) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact gcdFrequencyCoordinates_mem (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2
  calc
    _ = ∑ x ∈ S.product S, w (gcdFrequencyCoordinates x) := by
      simp only [Finset.product_eq_sprod]
      rw [Finset.sum_product S S (fun x => w (gcdFrequencyCoordinates x))]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hw (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)
    _ = ∑ z ∈ (S.product S).image gcdFrequencyCoordinates, w z := by
      exact (Finset.sum_image (fun _ _ _ _ h => gcdFrequencyCoordinates_injective h)).symm
    _ ≤ ∑ z ∈ S.product (S.product S), w z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp [w]; positivity)
    _ = ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (a : ℝ)⁻¹ * (b : ℝ)⁻¹ * (c : ℝ)⁻¹ := by
      simp only [Finset.product_eq_sprod]
      rw [Finset.sum_product S (S ×ˢ S) w]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_product S S (fun z => w (a, z))
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      dsimp [S]
      ring

/-- The quantitative frequency-pair estimate used by the norm comparison. -/
theorem reciprocal_lcm_sum_le_log_cube (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹) ≤
      (1 + Real.log N) ^ 3 := by
  have hH : (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ≤ 1 + Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log N
  exact (reciprocal_lcm_sum_le_harmonic_cube N).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hH 3)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReducedFrequencySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicity of the reduced frequency modulus -/

namespace Ostmann

open scoped BigOperators

theorem reducedFrequency_mul_gcd (g s : ℕ) : reducedFrequency g s * s.gcd g = s :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left s g)

theorem reducedFrequency_mem {N g s : ℕ} (hs : s ∈ Finset.Icc 1 N) :
    reducedFrequency g s ∈ Finset.Icc 1 N := by
  obtain ⟨hs₀, hsN⟩ := Finset.mem_Icc.mp hs
  have hg := Nat.gcd_pos_of_pos_left g (show 0 < s from hs₀)
  exact Finset.mem_Icc.mpr ⟨Nat.div_pos
    (Nat.le_of_dvd hs₀ (Nat.gcd_dvd_left s g)) hg, (Nat.div_le_self _ _).trans hsN⟩

/-- A fixed reduced modulus has at most one frequency for each divisor
of the gcd of the two child frequencies. -/
theorem reducedFrequency_fiber_card_le (N g a : ℕ) (hg : g ≠ 0) :
    ((Finset.Icc 1 N).filter fun s => reducedFrequency g s = a).card ≤ g.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun s => s.gcd g)
  · intro s _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right s g, hg⟩
  · intro s hs t ht heq
    change s.gcd g = t.gcd g at heq
    have hsa := (Finset.mem_filter.mp hs).2
    have hta := (Finset.mem_filter.mp ht).2
    calc
      s = reducedFrequency g s * s.gcd g := (reducedFrequency_mul_gcd g s).symm
      _ = reducedFrequency g t * t.gcd g := by rw [hsa, hta, heq]
      _ = t := reducedFrequency_mul_gcd g t

theorem sum_reducedFrequency_le (N g : ℕ) (hg : g ≠ 0)
    (F : ℕ → ℝ) (hF : ∀ a ∈ Finset.Icc 1 N, 0 ≤ F a) :
    (∑ s ∈ Finset.Icc 1 N, F (reducedFrequency g s)) ≤
      g.divisors.card * ∑ a ∈ Finset.Icc 1 N, F a := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun s hs => reducedFrequency_mem (g := g) hs)
    (fun s => F (reducedFrequency g s))]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, (g.divisors.card : ℝ) * F a := by
      apply Finset.sum_le_sum
      intro a ha
      have heq : (∑ s ∈ (Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a),
          F (reducedFrequency g s)) =
          (((Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a)).card : ℝ) * F a := by
        calc
          _ = ∑ _s ∈ (Finset.Icc 1 N).filter (fun s => reducedFrequency g s = a), F a :=
            Finset.sum_congr rfl fun _ hs => congrArg F (Finset.mem_filter.mp hs).2
          _ = _ := by simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast reducedFrequency_fiber_card_le N g a hg)
        (hF a ha)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- After fixing the child frequencies, summing the two parent reduced
moduli costs only the divisor multiplicities and a cubic logarithm. -/
theorem reducedFrequency_lcm_sum_le (N g h : ℕ) (hg : g ≠ 0) (hh : h ≠ 0) :
    (∑ s ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
      (((reducedFrequency g s).lcm (reducedFrequency h t) : ℕ) : ℝ)⁻¹) ≤
      (g.divisors.card : ℝ) * h.divisors.card * (1 + Real.log N) ^ 3 := by
  have hfirst := sum_reducedFrequency_le N g hg
    (fun a => ∑ t ∈ Finset.Icc 1 N, ((a.lcm (reducedFrequency h t) : ℕ) : ℝ)⁻¹)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
  calc
    _ ≤ (g.divisors.card : ℝ) *
        ∑ a ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          ((a.lcm (reducedFrequency h t) : ℕ) : ℝ)⁻¹ := hfirst
    _ ≤ (g.divisors.card : ℝ) *
        ∑ a ∈ Finset.Icc 1 N, (h.divisors.card : ℝ) *
          ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro a _
      exact sum_reducedFrequency_le N h hh
        (fun b => ((a.lcm b : ℕ) : ℝ)⁻¹) (fun _ _ => by positivity)
    _ = (g.divisors.card : ℝ) * h.divisors.card *
        (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ((a.lcm b : ℕ) : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_lcm_sum_le_log_cube N)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_SignedFrequencySum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both signs in the internal-frequency sum -/

namespace Ostmann

open scoped BigOperators Classical

theorem natAbs_fiber_card_le_two (S : Finset ℤ) (a : ℕ) :
    (S.filter fun s => s.natAbs = a).card ≤ 2 := by
  have hsub : (S.filter fun s => s.natAbs = a) ⊆ {(a : ℤ), -(a : ℤ)} := by
    intro s hs
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (Int.natAbs_eq_iff.mp (Finset.mem_filter.mp hs).2)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_insert_le _ _).trans_eq (by simp))

theorem sum_signed_magnitudes_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (F : ℕ → ℝ) (hF : ∀ a ∈ Finset.Icc 1 N, 0 ≤ F a) :
    (∑ s ∈ S, F s.natAbs) ≤ 2 * ∑ a ∈ Finset.Icc 1 N, F a := by
  have hmem (s : ℤ) (hs : s ∈ S) : s.natAbs ∈ Finset.Icc 1 N :=
    Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (Int.natAbs_ne_zero.mpr (hS s hs).1), (hS s hs).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun s => F s.natAbs)]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, 2 * F a := by
      apply Finset.sum_le_sum
      intro a ha
      have heq : (∑ s ∈ S.filter (fun s => s.natAbs = a), F s.natAbs) =
          ((S.filter (fun s => s.natAbs = a)).card : ℝ) * F a := by
        calc
          _ = ∑ _s ∈ S.filter (fun s => s.natAbs = a), F a :=
            Finset.sum_congr rfl fun _ hs => congrArg F (Finset.mem_filter.mp hs).2
          _ = _ := by simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast natAbs_fiber_card_le_two S a) (hF a ha)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The factor four is exactly the two possible signs in each history. -/
theorem signed_reducedFrequency_lcm_sum_le (S T : Finset ℤ) (N g h : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hT : ∀ t ∈ T, t ≠ 0 ∧ t.natAbs ≤ N) (hg : g ≠ 0) (hh : h ≠ 0) :
    (∑ s ∈ S, ∑ t ∈ T,
      (((reducedFrequency g s.natAbs).lcm (reducedFrequency h t.natAbs) : ℕ) : ℝ)⁻¹) ≤
      4 * (g.divisors.card : ℝ) * h.divisors.card * (1 + Real.log N) ^ 3 := by
  calc
    _ ≤ 2 * ∑ a ∈ Finset.Icc 1 N, ∑ t ∈ T,
        (((reducedFrequency g a).lcm (reducedFrequency h t.natAbs) : ℕ) : ℝ)⁻¹ :=
      sum_signed_magnitudes_le S N hS _ (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    _ ≤ 2 * ∑ a ∈ Finset.Icc 1 N, 2 * ∑ b ∈ Finset.Icc 1 N,
        (((reducedFrequency g a).lcm (reducedFrequency h b) : ℕ) : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro a _
      exact sum_signed_magnitudes_le T N hT
        (fun b => (((reducedFrequency g a).lcm (reducedFrequency h b) : ℕ) : ℝ)⁻¹)
        (fun _ _ => by positivity)
    _ = 4 * (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        (((reducedFrequency g a).lcm (reducedFrequency h b) : ℕ) : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have hbound := mul_le_mul_of_nonneg_left (reducedFrequency_lcm_sum_le N g h hg hh)
        (show (0 : ℝ) ≤ 4 by norm_num)
      convert hbound using 1
      all_goals try with_reducible_and_instances rfl
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticFrequencyTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full arithmetic frequency-tree budget -/

namespace Ostmann

open scoped BigOperators Classical

theorem pairedFrequencyKernel_sum_le (S : Finset ℤ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ v ∈ S, ∀ w ∈ S, ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D)
    (left right : S × S) :
    (∑ root : S × S, pairedFrequencyKernel S D root left right) ≤
      8 * D ^ 4 * (1 + Real.log N) ^ 3 := by
  let g := (left.1 : ℤ).natAbs.gcd (right.1 : ℤ).natAbs
  let h := (left.2 : ℤ).natAbs.gcd (right.2 : ℤ).natAbs
  have hg : g ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _
    (Int.natAbs_pos.mpr (hS _ left.1.property).1))
  have hh : h ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _
    (Int.natAbs_pos.mpr (hS _ left.2.property).1))
  have hgd : (g.divisors.card : ℝ) ≤ D := hdiv _ left.1.property _ right.1.property
  have hhd : (h.divisors.card : ℝ) ≤ D := hdiv _ left.2.property _ right.2.property
  have hpair :
      (∑ s : S, ∑ t : S,
        (((reducedFrequency g (s : ℤ).natAbs).lcm (reducedFrequency h (t : ℤ).natAbs) : ℕ) : ℝ)⁻¹) =
      ∑ s ∈ S, ∑ t ∈ S,
        (((reducedFrequency g s.natAbs).lcm (reducedFrequency h t.natAbs) : ℕ) : ℝ)⁻¹ := by
    rw [Finset.sum_coe_sort S (fun s : ℤ => ∑ t : S,
      (((reducedFrequency g s.natAbs).lcm (reducedFrequency h (t : ℤ).natAbs) : ℕ) : ℝ)⁻¹)]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_coe_sort S (fun t : ℤ =>
      (((reducedFrequency g s.natAbs).lcm (reducedFrequency h t.natAbs) : ℕ) : ℝ)⁻¹)
  calc
    _ = 2 * D ^ 2 * (∑ s : S, ∑ t : S,
        (((reducedFrequency g (s : ℤ).natAbs).lcm (reducedFrequency h (t : ℤ).natAbs) : ℕ) : ℝ)⁻¹) := by
      simp only [pairedFrequencyKernel, Fintype.sum_prod_type, ← Finset.mul_sum, g, h]
    _ ≤ 2 * D ^ 2 * (4 * (g.divisors.card : ℝ) * h.divisors.card * (1 + Real.log N) ^ 3) := by
      rw [hpair]
      exact mul_le_mul_of_nonneg_left (signed_reducedFrequency_lcm_sum_le S S N g h hS hS hg hh)
        (by positivity)
    _ ≤ 2 * D ^ 2 * (4 * D * D * (1 + Real.log N) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hlog : 0 ≤ (1 + Real.log N) ^ 3 := by
        have hbase := Real.log_natCast_nonneg N
        positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hgd (by norm_num)) hhd
          (Nat.cast_nonneg _) (by positivity)) hlog
    _ = _ := by ring

theorem pairedFrequencyLeaf_sum_le (S : Finset ℤ) (V : ℕ)
    (hS : ∀ s ∈ S, s ≠ 0) :
    (∑ x : S × S, pairedFrequencyLeaf S V x) ≤ (2 * (V : ℝ)) ^ 2 := by
  let T := S.filter fun s => s.natAbs ≤ V
  have hT : ∀ s ∈ T, s ≠ 0 ∧ s.natAbs ≤ V := by
    intro s hs
    exact ⟨hS s (Finset.mem_filter.mp hs).1, (Finset.mem_filter.mp hs).2⟩
  have hcard : (T.card : ℝ) ≤ 2 * V := by
    have hbound := sum_signed_magnitudes_le T V hT (fun _ => (1 : ℝ)) (by intros; norm_num)
    simpa using hbound
  have hsingle : (∑ s : S, if (s : ℤ).natAbs ≤ V then (1 : ℝ) else 0) = T.card := by
    rw [Finset.sum_coe_sort S (fun s : ℤ => if s.natAbs ≤ V then (1 : ℝ) else 0)]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, T]
  have hterm (x y : S) : pairedFrequencyLeaf S V (x, y) =
      (if (x : ℤ).natAbs ≤ V then (1 : ℝ) else 0) *
        (if (y : ℤ).natAbs ≤ V then (1 : ℝ) else 0) := by
    unfold pairedFrequencyLeaf
    split_ifs <;> simp_all
  calc
    _ = (T.card : ℝ) ^ 2 := by
      rw [Fintype.sum_prod_type, pow_two, ← hsingle, Finset.sum_mul_sum]
      simp only [hterm]
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2

/-- Root-first elimination leaves only the two histories' leaf frequencies.
The exponent `2^n-1` is the exact number of internal nodes. -/
theorem arithmetic_frequency_tree_sum_le (S : Finset ℤ) (N V : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ v ∈ S, ∀ w ∈ S, ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D)
    (n : ℕ) :
    (∑ x : FrequencyTree (S × S) n,
      frequencyTreeWeight (pairedFrequencyKernel S D) (pairedFrequencyLeaf S V) n x) ≤
      (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 * 2 ^ n) := by
  have hC : 0 ≤ 8 * D ^ 4 * (1 + Real.log N) ^ 3 := by
    have hlog := Real.log_natCast_nonneg N
    positivity
  have hmain := frequencyTree_sum_le (pairedFrequencyKernel S D) (pairedFrequencyLeaf S V)
    (8 * D ^ 4 * (1 + Real.log N) ^ 3) (by intros; unfold pairedFrequencyKernel; positivity)
    (by intros; unfold pairedFrequencyLeaf; split_ifs <;> norm_num) hC
    (pairedFrequencyKernel_sum_le S N D hD hS hdiv) n
  apply hmain.trans
  have hleaf := pairedFrequencyLeaf_sum_le S V (fun s hs => (hS s hs).1)
  calc
    _ ≤ (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
        ((2 * (V : ℝ)) ^ 2) ^ (2 ^ n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (Finset.sum_nonneg fun x _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num)
        hleaf _) (pow_nonneg hC _)
    _ = _ := by rw [← pow_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_UniformDivisorBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform subexponential divisor loss on the arithmetic moduli -/

namespace Ostmann

theorem divisors_subexponential_uniform (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ Real.exp (C * m) →
      (n.divisors.card : ℝ) ≤ Real.exp (ε * m) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (C / ε)
  have hgap : 0 < ε * k - C := by
    have h := (div_lt_iff₀ hε).mp hk
    nlinarith
  have hk0 : k ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, mul_zero] at hgap
    linarith
  obtain ⟨D, hD, hbound⟩ := exists_divisors_power_bound k
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D from hD)
  refine ⟨Real.log D / (ε * k - C), fun m hm n hn hnupper => ?_⟩
  have hlog : Real.log D + C * m ≤ ε * k * m := by
    have h := (div_le_iff₀ hgap).mp hm
    nlinarith
  have hpower : (n.divisors.card : ℝ) ^ k ≤ Real.exp (ε * m) ^ k := by
    calc
      _ ≤ (D : ℝ) * n := by exact_mod_cast hbound n hn
      _ ≤ (D : ℝ) * Real.exp (C * m) := mul_le_mul_of_nonneg_left hnupper hDpos.le
      _ = Real.exp (Real.log D + C * m) := by rw [Real.exp_add, Real.exp_log hDpos]
      _ ≤ Real.exp (ε * k * m) := Real.exp_le_exp.mpr hlog
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (Real.exp_pos _).le hk0).mp hpower

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyBudgetRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency-tree cost is subexponential at fixed depth -/

namespace Ostmann

open Filter

theorem cubic_log_budget (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ Real.exp (C * m) →
      8 * (1 + Real.log N) ^ 3 ≤ Real.exp (ε * m) := by
  have he := ((isLittleO_pow_exp_pos_mul_atTop 3 hε).const_mul_left
    (8 * (1 + C) ^ 3)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with m hm hm1 N hN
  have hm0 : 0 ≤ m := by linarith
  have hlog : Real.log N ≤ C * m := by
    by_cases hn : N = 0
    · subst N
      simpa using mul_nonneg hC hm0
    · exact (Real.log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr hN
  have hlog0 := Real.log_natCast_nonneg N
  have hlin : 1 + Real.log N ≤ (1 + C) * m := by nlinarith
  have hpoly : 8 * (1 + C) ^ 3 * m ^ 3 ≤ Real.exp (ε * m) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 8 * (1 + C) ^ 3 * m ^ 3), abs_of_pos (Real.exp_pos _), one_mul] using hm
  calc
    _ ≤ 8 * ((1 + C) * m) ^ 3 := by gcongr
    _ = 8 * (1 + C) ^ 3 * m ^ 3 := by ring
    _ ≤ _ := hpoly

/-- One value of `D` controls every frequency divisor and every joint
square modulus up to `exp(2*C*m)`, with the total cost at most `exp(epsilon*m)`. -/
theorem frequency_budget_subexponential (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ Real.exp (2 * C * m) →
        (n.divisors.card : ℝ) ≤ D) ∧
      (∀ N : ℕ, (N : ℝ) ≤ Real.exp (C * m) →
        8 * D ^ 4 * (1 + Real.log N) ^ 3 ≤ Real.exp (ε * m)) := by
  obtain ⟨M, hM⟩ := divisors_subexponential_uniform (2 * C) (ε / 8)
    (by positivity) (by positivity)
  filter_upwards [eventually_ge_atTop M, cubic_log_budget C (ε / 2) hC (by positivity)]
    with m hm hpoly
  refine ⟨Real.exp ((ε / 8) * m), (Real.exp_pos _).le, hM m hm, fun N hN => ?_⟩
  have hexp : Real.exp ((ε / 8) * m) ^ 4 = Real.exp ((ε / 2) * m) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ = Real.exp ((ε / 2) * m) * (8 * (1 + Real.log N) ^ 3) := by ring
    _ ≤ Real.exp ((ε / 2) * m) * Real.exp ((ε / 2) * m) :=
      mul_le_mul_of_nonneg_left (hpoly N hN) (Real.exp_pos _).le
    _ = Real.exp (ε * m) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSplitTreeSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the actual split probabilities at fixed frequencies -/

namespace Ostmann

open scoped BigOperators Classical

theorem pairFrequencySupportBound_nonneg (D : ℝ) (f : NodeFrequencies × NodeFrequencies) :
    0 ≤ pairFrequencySupportBound D f := by unfold pairFrequencySupportBound; positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeNodes
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder frequency data and its exact product of split costs -/

namespace Ostmann

open scoped BigOperators Classical

theorem pairedNodeFrequencies_bound (S : Finset ℤ) (D : ℝ) (root left right : S × S) :
    pairFrequencySupportBound D (pairedNodeFrequencies S root left right) =
      pairedFrequencyKernel S D root left right := by
  simp only [pairFrequencySupportBound, pairedNodeFrequencies, NodeFrequencies.reducedModulus,
    pairedFrequencyKernel, div_eq_mul_inv]

theorem frequencyLeafWeight_nonneg {A : Type} (W : A → ℝ) (hW : ∀ a, 0 ≤ W a)
    (n : ℕ) (x : FrequencyTree A n) : 0 ≤ frequencyLeafWeight W n x := by
  induction n with
  | zero => exact hW x
  | succ n ih => exact mul_nonneg (ih _) (ih _)

theorem frequencyTreeWeight_eq_splitList (S : Finset ℤ) (D : ℝ) (W : S × S → ℝ)
    (n : ℕ) (x : FrequencyTree (S × S) n) :
    frequencyTreeWeight (pairedFrequencyKernel S D) W n x =
      ((frequencySplitList S n x).map (pairFrequencySupportBound D)).prod *
        frequencyLeafWeight W n x := by
  induction n with
  | zero => simp [frequencyTreeWeight, frequencySplitList, frequencyLeafWeight]
  | succ n ih =>
    simp only [frequencyTreeWeight, frequencySplitList, frequencyLeafWeight,
      List.map_cons, List.map_append, List.prod_cons, List.prod_append,
      pairedNodeFrequencies_bound, ih]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticHistorySupportSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the original two-history congruence support over frequencies -/

namespace Ostmann

open scoped BigOperators Classical

theorem gcd_frequency_divisor_bound (S : Finset ℤ) (N : ℕ) (D : ℝ)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (v : ℤ) (hv : v ∈ S) (w : ℤ) (_hw : w ∈ S) :
    ((v.natAbs.gcd w.natAbs).divisors.card : ℝ) ≤ D := by
  have hv0 : 0 < v.natAbs := Int.natAbs_pos.mpr (hS v hv).1
  have hN : 0 < N := hv0.trans_le (hS v hv).2
  apply hdiv
  · exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ hv0)
  · calc
      _ ≤ v.natAbs := Nat.gcd_le_left _ hv0
      _ ≤ N := (hS v hv).2
      _ ≤ N ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right N hN

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_nonneg (P Q : Finset ℕ) (p : P) :
    0 ≤ primeSubsetPrior P Q p := by
  unfold primeSubsetPrior
  split_ifs
  · exact div_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact le_rfl

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

theorem primeSubsetPrior_atom (P Q : Finset ℕ) (p : P) :
    primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := by
  unfold primeSubsetPrior
  split_ifs
  · exact le_of_eq (by ring)
  · positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_LeafFrequencyBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining leaf-frequency budget in the norm comparison -/

namespace Ostmann

theorem sqrt_cost_sublinear (A B ε : ℝ) (_hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → A * Real.sqrt m + B ≤ ε * m := by
  refine ⟨max ((2 * A / ε) ^ 2) (2 * max B 0 / ε), fun m hm => ?_⟩
  have hmA : (2 * A / ε) ^ 2 ≤ m := (le_max_left _ _).trans hm
  have hmB : 2 * max B 0 / ε ≤ m := (le_max_right _ _).trans hm
  have hm0 : 0 ≤ m := (sq_nonneg _).trans hmA
  have hr := Real.le_sqrt_of_sq_le hmA
  have hA' : A ≤ ε / 2 * Real.sqrt m := by
    have h := (div_le_iff₀ hε).mp hr
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hA' (Real.sqrt_nonneg m)
  have hsq := Real.sq_sqrt hm0
  have hB' : B ≤ ε / 2 * m := by
    have h := (div_le_iff₀ hε).mp hmB
    have hmax := le_max_left B 0
    nlinarith
  nlinarith

theorem leaf_frequency_budget (r V : ℕ) (Δ m K : ℝ)
    (hV : (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m)) :
    (2 * (V : ℝ)) ^ (2 * r) * Real.exp (-(r : ℝ) * Δ + K) ≤
      Real.exp ((r : ℝ) * Δ + 2 * r * Real.sqrt m + 2 * r * Real.log 2 + K) := by
  calc
    _ ≤ (2 * Real.exp (Δ + Real.sqrt m)) ^ (2 * r) * Real.exp (-(r : ℝ) * Δ + K) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) _) (Real.exp_pos _).le
    _ = _ := by
      nth_rw 1 [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- After the smooth factor `exp(-r*Delta)`, summing the two histories'
leaf frequencies costs `exp(r*Delta + o(m))`. -/
theorem leaf_frequency_budget_sublinear (r : ℕ) (K ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → ∀ Δ : ℝ, ∀ V : ℕ,
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (2 * (V : ℝ)) ^ (2 * r) * Real.exp (-(r : ℝ) * Δ + K) ≤
        Real.exp ((r : ℝ) * Δ + ε * m) := by
  obtain ⟨M, hM⟩ := sqrt_cost_sublinear (2 * r) (2 * r * Real.log 2 + K) ε
    (by positivity) hε
  refine ⟨M, fun m hm Δ V hV => (leaf_frequency_budget r V Δ m K hV).trans ?_⟩
  apply Real.exp_le_exp.mpr
  have h := hM m hm
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true, if_true]

theorem recursiveTransferWeight_nonzero_valid {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n σ t ≠ 0) :
    ValidTransferHistory sys n σ t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP] at ht
      have hl : recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 ≠ 0 := by
        intro hz
        simp only [hz, mul_zero, zero_mul, ne_eq, not_true_eq_false] at ht
      have hr : recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 ≠ 0 := by
        intro hz
        simp only [hz, star_zero, mul_zero, ne_eq, not_true_eq_false] at ht
      exact ⟨P, hP, ih _ _ hl, ih _ _ hr⟩
    · exact False.elim (ht (by simp only [recursiveTransferWeight, P, hP, ite_false, if_false]))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveFrequencySupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original leaf-frequency cutoffs in the recursive squared weights -/

namespace Ostmann

open scoped Classical

theorem frequencyLeafWeight_map {A B : Type} (f : A → B) (W : B → ℝ)
    (n : ℕ) (x : FrequencyTree A n) :
    frequencyLeafWeight W n (frequencyTreeMap f n x) = frequencyLeafWeight (fun a => W (f a)) n x := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg₂ (· * ·) (ih x.2.1) (ih x.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SingleFrequencyModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The modulus attached to one fixed frequency history -/

namespace Ostmann

open scoped BigOperators Classical

theorem historyFrequencyProduct_pos (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n : ℕ) (t : FrequencyTree S n) : 0 < historyFrequencyProduct S n t := by
  induction n with
  | zero => exact Int.natAbs_pos.mpr (hS _ t.property)
  | succ n ih =>
      exact Nat.mul_pos
        (Nat.mul_pos (Int.natAbs_pos.mpr (hS _ t.1.property)) (ih _)) (ih _)

theorem historyFrequencyProduct_le (S : Finset ℤ) (N : ℕ)
    (hS : ∀ s ∈ S, s.natAbs ≤ N) (n : ℕ) (t : FrequencyTree S n) :
    historyFrequencyProduct S n t ≤ N ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simpa [historyFrequencyProduct] using hS _ t.property
  | succ n ih =>
    have he : 2 ^ (n + 1 + 1) - 1 = 1 + (2 ^ (n + 1) - 1) + (2 ^ (n + 1) - 1) := by
      have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    calc
      _ ≤ N * N ^ (2 ^ (n + 1) - 1) * N ^ (2 ^ (n + 1) - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (hS _ t.1.property) (ih _)) (ih _)
      _ = _ := by rw [he]; simp only [pow_add, pow_one]

/-- All actual primes exceed the frequency range. Consequently they are
units for the full history modulus, including its precision exponent. -/
theorem prime_coprime_historyFrequencyModulus (S : Finset ℤ) (N p : ℕ)
    (hp : p.Prime) (hpN : N < p)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) (n k : ℕ) (t : FrequencyTree S n) :
    p.Coprime (historyFrequencyModulus S n k t) := by
  have hfreq (s : S) : p.Coprime (s : ℤ).natAbs := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hpos : 0 < (s : ℤ).natAbs := Int.natAbs_pos.mpr (hS _ s.property).1
    have hle := Nat.le_of_dvd hpos hd
    have hbound := (hS _ s.property).2
    omega
  have hprod : p.Coprime (historyFrequencyProduct S n t) := by
    induction n with
    | zero => exact hfreq t
    | succ n ih => exact (hfreq t.1).mul_right (ih t.2.1) |>.mul_right (ih t.2.2)
  exact hprod.pow_right (k + 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFullPeriod
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full small-frequency modulus, including every node's unit tests -/

namespace Ostmann

open scoped Classical

theorem frequencyRoot_mem_allFrequencyList (n : ℕ) (t : FrequencyTree ℤ n) :
    frequencyRoot n t ∈ allFrequencyList n t := by
  cases n <;> simp [allFrequencyList, frequencyRoot]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

theorem movingNaturalProduct_append {σ : Type*} (value : σ → ℕ) (x y : List σ) :
    MovingSlotReversal.naturalProduct value (x ++ y) =
      MovingSlotReversal.naturalProduct value x * MovingSlotReversal.naturalProduct value y := by
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original recursive weight on moving-giant states

A reconstructed pivot is the composite `u*p`; only its quotient `p` becomes
the new giant. The compensation primes remain in the regular child lists.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Follows.root {σ : Type*} {n : ℕ} {T : MovingSlotData σ n}
    {t : FrequencyTree ℤ n} (h : T.Follows t) : T.frequency = frequencyRoot n t := by
  cases T with
  | leaf => exact h
  | node => exact h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PermutedAdditiveCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem tupleCofactor_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (i : I) :
    tupleCofactor (fun i => p (e i)) i = tupleCofactor p (e i) := by
  apply mul_left_cancel₀ (hp (e i))
  calc
    _ = ∏ j, p (e j) := tupleCofactor_mul _ i
    _ = ∏ j, p j := e.prod_comp p
    _ = _ := (tupleCofactor_mul p (e i)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerIntervalVariation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Abel variation for the original external integer measure -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem integerResidueAtom_nonneg (q a : ℕ) (G : ℝ) (n : ℕ) :
    0 ≤ integerResidueAtom q a G n := by
  unfold integerResidueAtom
  split_ifs <;> positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticErrorRates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the fixed-depth arithmetic comparison costs

The polynomial and spectator costs in Section 8 are dominated by the
double-exponential savings. The strict numerical gaps in the manuscript
therefore survive the finite history and equality-pattern sums.
-/

namespace Ostmann

open Filter Asymptotics

theorem arithmetic_exponent_absorption (a b d C c : ℝ) (n : ℕ)
    (hb : 0 < b) (hab : a < b) (hdb : d < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ n + C * L * Real.exp (a * L) - c * Real.exp (b * L) ≤
        -Real.exp (d * L) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop n hb).const_mul_left C
  have hm : (fun L : ℝ => C * (Real.exp (a * L) * L)) =o[atTop]
      (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_one] using (isLittleO_exp_mul_rpow_of_lt 1 hab).const_mul_left C
  have he : (fun L : ℝ => Real.exp (d * L)) =o[atTop] (fun L => Real.exp (b * L)) := by
    simpa only [Real.rpow_zero, mul_one] using isLittleO_exp_mul_rpow_of_lt 0 hdb
  have h := ((hp.add hm).add he).bound hc
  filter_upwards [h] with L hL
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hL
  have hle := (le_abs_self _).trans hL
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full original support as local guards in the sampled recursion

All current-state coprimalities and all descendant-frequency unit tests are
retained. This puts the existing fully supported coefficient into the local
recursion form, without conditioning any internal sample prior.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_node {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (s : ℤ) (CL CR u : List σ) (l r : MovingSlotData σ n) (XL XR : ℕ) :
    let T := MovingSlotData.node s CL CR u l r
    let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
    movingFullSupport value outside T XL XR ↔
      movingLocalSupport value outside ⟨n + 1, T, XL, XR⟩ ∧
      movingFullSupport value outside l p XL ∧ movingFullSupport value outside r p XR := by
  simp only [movingFullSupport, movingLocalSupport, movingFullOutsidePairwise, movingNaturalGiantUnits]
  tauto

theorem movingSlotCutoff_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E) x s v w =
      if movingLocalSupport value outside x then
        movingSlotCutoff value childBound pivotBound E x s v w else 0 := by
  unfold movingSlotCutoff movingGuardedExtra
  split_ifs <;> rfl

/-- The fully supported original history coefficient equals the recursive
coefficient with the literal local support test at each node and leaf. -/
theorem movingSupportedWeight_recursive {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E))
      n ⟨n, T, XL, XR⟩ t =
        movingSupportedWeight value outside T XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n ⟨n, T, XL, XR⟩ t) := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutg := movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)
  induction T generalizing XL XR with
  | leaf s regular => rfl
  | @node n s CL CR u l r hl hr =>
      let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u l r, XL, XR⟩
      let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
      have hp : P / MovingSlotReversal.naturalProduct value u = p := by
        simp only [P, p, historyPivot, sys, movingSlotSystem, x, MovingSlotState.leftProduct,
          MovingSlotState.rightProduct, MovingSlotReversal.naturalPivot, MovingSlotData.step,
          movingGiantPivot, Nat.mul_one, ← hT.1, ← hT.2.1.root, ← hT.2.2.root]
      by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
      · rw [recursiveTransferWeight_node sys _ cutg n x t P hv]
        change (cutg x t.1 _ _ : ℂ) *
            recursiveTransferWeight sys _ cutg n ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ t.2.1 *
            star (recursiveTransferWeight sys _ cutg n ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ t.2.2) = _
        rw [hp, hl t.2.1 hT.2.1 p XL, hr t.2.2 hT.2.2 p XR]
        have hg := movingSlotCutoff_guarded value outside childBound pivotBound E x
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
        change cutg x t.1 _ _ = if movingLocalSupport value outside x then cut x t.1 _ _ else 0 at hg
        rw [hg]
        unfold movingSupportedWeight
        have hs := movingFullSupport_node value outside s CL CR u l r XL XR
        dsimp only at hs
        rw [hs]
        rw [recursiveTransferWeight_node sys F cut n x t P hv]
        have hleft : sys.leftState x P =
            ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ := rfl
        have hright : sys.rightState x P =
            ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ := rfl
        rw [hleft, hright, hp]
        by_cases hA : movingLocalSupport value outside x <;>
          by_cases hB : movingFullSupport value outside l p XL <;>
          by_cases hC : movingFullSupport value outside r p XR
        all_goals dsimp only [x, p] at hA hB hC ⊢
        all_goals simp only [hA, hB, hC, and_true, and_false,
          ite_true, if_true, ite_false, if_false, Complex.ofReal_zero, zero_mul, mul_zero, star_zero]
        rfl
      · have hz₁ : recursiveTransferWeight sys (movingGuardedLeaf value outside F) cutg
            (n + 1) x t = 0 := by simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
          simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        rw [hz₁, hz₂]
        unfold movingSupportedWeight
        split_ifs <;> rfl

theorem movingFrequencySkeleton_frequencyTree (σ : Type*) (n : ℕ)
    (t : FrequencyTree ℤ n) :
    (movingFrequencySkeleton σ n t).frequencyTree = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [movingFrequencySkeleton, MovingSlotData.frequencyTree, ih]
    rfl

theorem MovingSlotData.skeleton_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) :
    (movingFrequencySkeleton σ n T.frequencyTree).frequencyProduct = T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR u l r hl hr =>
    simp only [MovingSlotData.frequencyTree, movingFrequencySkeleton, frequencyProduct, hl, hr]

theorem MovingSlotData.rootData_regularSlots {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.regularSlots = T.regularSlots := by
  cases T <;> rfl

theorem MovingSlotData.rootData_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.frequencyProduct = T.frequencyProduct := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, frequencyProduct, skeleton_frequencyProduct]

theorem MovingSlotData.rootData_idempotent {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.rootData = T.rootData := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, movingFrequencySkeleton_frequencyTree]

theorem movingLocalSupport_rootData {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (x : MovingSlotState σ) :
    movingLocalSupport value outside ⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ ↔
      movingLocalSupport value outside x := by
  simp only [movingLocalSupport, MovingSlotData.currentSlots, movingLocalGiantUnits,
    MovingSlotData.rootData_regularSlots, MovingSlotData.rootData_frequencyProduct]

theorem movingLocalExtra_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingGuardedExtra value outside (movingLocalExtra E)) =
      movingGuardedExtra value outside (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingGuardedExtra, movingLocalSupport_rootData,
    MovingSlotData.rootData_idempotent]

/-- The sample expansion of the fully supported original coefficient. Every
sample retains its original weight, including samples whose support fails. -/
theorem movingSampledWeight_supported {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra E)) n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
        movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  unfold movingSampledWeight
  rw [movingLocalExtra_guarded]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedWeight_recursive value outside childBound pivotBound F (movingLocalExtra E)
    _ t (buildMovingSlotData_follows n t small bulk a)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticNormRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numerical rate after the actual arithmetic frequency sum -/

namespace Ostmann
open Filter

/-- The divisor constant is chosen uniformly before the history-dependent
modulus. This is the numerical estimate used by the same-assignment norm. -/
theorem arithmetic_frequency_budget_rate (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
      ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) *
        ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
          (2 * (V : ℝ)) ^ (2 * 2 ^ n)) ≤
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
  let r : ℕ := 2 ^ n
  have hr : (0 : ℝ) < r := by exact_mod_cast (Nat.two_pow_pos n)
  let δ : ℝ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδr : δ * r = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨M, hM⟩ := leaf_frequency_budget_sublinear r K (ε / 8) (by positivity)
  filter_upwards [frequency_budget_subexponential C δ hC hδ,
    eventually_ge_atTop (M / 4), eventually_ge_atTop (0 : ℝ)] with m hrate hm hm0
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have hC0 : 0 ≤ 8 * D ^ 4 * (1 + Real.log N) ^ 3 := by
    have := Real.log_natCast_nonneg N
    positivity
  have hnode : (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (r - 1) ≤
      Real.exp ((ε / 2) * m) := by
    calc
      _ ≤ Real.exp (δ * m) ^ (r - 1) := pow_le_pow_left₀ hC0 (hcost N hN) _
      _ = Real.exp ((r - 1 : ℕ) * (δ * m)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hcount : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
        have h := mul_le_mul_of_nonneg_right hcount (mul_nonneg hδ.le hm0)
        nlinarith [hδr]
  have hleaf : (2 * (V : ℝ)) ^ (2 * r) * Real.exp (-(r : ℝ) * Δ + K) ≤
      Real.exp ((r : ℝ) * Δ + (ε / 2) * m) := by
    convert hM (4 * m) (by linarith) Δ V hV using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  calc
    _ = (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (r - 1) *
        ((2 * (V : ℝ)) ^ (2 * r) * Real.exp (-(r : ℝ) * Δ + K)) := by ring
    _ ≤ Real.exp ((ε / 2) * m) * Real.exp ((r : ℝ) * Δ + (ε / 2) * m) :=
      mul_le_mul hnode hleaf (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; dsimp [r]; congr 1; ring

/-- Fixed profile constants are absorbed without changing the coefficient
`log 6` of the bulk cost. -/
theorem arithmetic_norm_budget_rate (n : ℕ) (A C ε : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
      ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      (A * Real.exp (-(2 ^ n : ℕ) * Δ)) *
        ((2 * Real.exp (Real.log 6 * (2 ^ n : ℕ) * m)) *
          ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) ≤
        Real.exp ((2 ^ n : ℕ) * Δ + Real.log 6 * (2 ^ n : ℕ) * m + ε * m) := by
  let K := Real.log (2 * A + 1)
  have hK : 2 * A ≤ Real.exp K := by
    dsimp only [K]
    rw [Real.exp_log (by positivity : 0 < 2 * A + 1)]
    linarith
  filter_upwards [arithmetic_frequency_budget_rate n K C ε hC hε] with m hm
  obtain ⟨D, hD, hdiv, hcost⟩ := hm
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have hb : 0 ≤ (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
      (2 * (V : ℝ)) ^ (2 * 2 ^ n) := by
    have := Real.log_natCast_nonneg N
    positivity
  calc
    _ = Real.exp (Real.log 6 * (2 ^ n : ℕ) * m) *
        ((2 * A) * Real.exp (-(2 ^ n : ℕ) * Δ) *
          ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) := by ring
    _ ≤ Real.exp (Real.log 6 * (2 ^ n : ℕ) * m) *
        (Real.exp (-(2 ^ n : ℕ) * Δ + K) *
          ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le).trans_eq (mul_comm _ _)) hb
    _ ≤ Real.exp (Real.log 6 * (2 ^ n : ℕ) * m) *
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) :=
      mul_le_mul_of_nonneg_left (hcost N V Δ hN hV) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_FourierWindowDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The leaf-window decay retained in the Section 8 norm bound -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- Exact exponential decay of the paired Fourier window budget. -/
theorem fourier_window_pair_exp (ψ : 𝓢(ℝ, ℂ)) (n : ℕ) (B Δ : ℝ) :
    ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
      B ^ (2 ^ n - 1)) ^ 2 =
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        Real.exp (-(2 ^ n : ℕ) * Δ) := by
  have hd : (Real.sqrt (Real.exp Δ) ^ (2 ^ n)) ^ 2 = Real.exp ((2 ^ n : ℕ) * Δ) := by
    rw [← pow_mul, Nat.mul_comm (2 ^ n) 2, pow_mul,
      Real.sq_sqrt (Real.exp_pos Δ).le, ← Real.exp_nat_mul]
  rw [div_pow, mul_pow, div_pow, hd, div_eq_mul_inv, ← Real.exp_neg]
  simp only [neg_mul]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The even bulk size and the accumulated giant loss in Section 9 -/

namespace Ostmann
open Filter
open scoped BigOperators

theorem spectatorBulkCount_lower (k : ℕ) (L : ℝ) :
    (k : ℝ) ^ 4 * L - 2 < (spectatorBulkCount k L : ℝ) := by
  have h := Nat.sub_one_lt_floor ((k : ℝ) ^ 4 * L / 2)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_upper (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (spectatorBulkCount k L : ℝ) ≤ (k : ℝ) ^ 4 * L := by
  have h := Nat.floor_le (show 0 ≤ (k : ℝ) ^ 4 * L / 2 by positivity)
  unfold spectatorBulkCount
  push_cast
  linarith

theorem spectatorBulkCount_half (k : ℕ) (L : ℝ)
    (hL : 4 ≤ (k : ℝ) ^ 4 * L) :
    (k : ℝ) ^ 4 * L / 2 ≤ (spectatorBulkCount k L : ℝ) := by
  linarith [spectatorBulkCount_lower k L]

theorem spectatorBulkCount_tendsto (k : ℕ) (hk : 0 < k) :
    Tendsto (fun L : ℝ => (spectatorBulkCount k L : ℝ)) atTop atTop := by
  have hk0 : 0 < (k : ℝ) ^ 4 := by positivity
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) / (k : ℝ) ^ 4)] with L hL
  have h := (div_le_iff₀ hk0).mp hL
  linarith [spectatorBulkCount_lower k L]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticPrimeNormRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The frequency budget after return to the original prime law -/

namespace Ostmann
open Filter
open scoped SchwartzMap

theorem arithmetic_prime_page_spectator_cost (n m : ℕ) :
    ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) * 2 ^ (2 ^ n * m) =
      2 * Real.exp (Real.log 12 * (2 ^ n : ℕ) * m) := by
  have hbase : (2 : ℝ) * 3 * 2 = 12 := by norm_num
  calc
    _ = 2 * (((2 : ℝ) * 3 * 2) ^ (2 ^ n * m)) := by
      simp only [mul_pow]
      ring
    _ = _ := by
      rw [hbase]
      congr 1
      rw [show Real.log 12 * (2 ^ n : ℕ) * m =
        ((2 ^ n * m : ℕ) : ℝ) * Real.log 12 by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 12)]

/-- The prime-cell mixture adds one factor two per bulk coordinate. This
changes the constant in the exponential from log six to log twelve. -/
theorem arithmetic_prime_norm_budget_rate (n : ℕ) (A C ε : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
      ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      (A * Real.exp (-(2 ^ n : ℕ) * Δ)) *
        ((2 * Real.exp (Real.log 12 * (2 ^ n : ℕ) * m)) *
          ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) ≤
        Real.exp ((2 ^ n : ℕ) * Δ + Real.log 12 * (2 ^ n : ℕ) * m + ε * m) := by
  have hlog : Real.log 12 = Real.log 2 + Real.log 6 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (6 : ℝ) ≠ 0)]
    norm_num
  filter_upwards [arithmetic_norm_budget_rate n A C ε hA hC hε] with m hm
  obtain ⟨D, hD, hdiv, hcost⟩ := hm
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have h := mul_le_mul_of_nonneg_left (hcost N V Δ hN hV)
    (Real.exp_pos (Real.log 2 * (2 ^ n : ℕ) * m)).le
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (rw [hlog] <;>
    simp only [add_mul, Real.exp_add] <;> ring)

/-- Specialization to the actual even bulk size, with the literal window and
Page/spectator constants of the prime norm estimate. -/
theorem arithmetic_prime_fourier_budget_rate (ψ : 𝓢(ℝ, ℂ)) (n k : ℕ) (hk : 0 < k)
    (B C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
        ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
          B ^ (2 ^ n - 1)) ^ 2 *
          (((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
            ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
              (2 * (V : ℝ)) ^ (2 * 2 ^ n)))) * 2 ^ (2 ^ n * m) ≤
          Real.exp ((2 ^ n : ℕ) * Δ + Real.log 12 * (2 ^ n : ℕ) * m + ε * m) := by
  let A : ℝ := ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2
  have hrate := (spectatorBulkCount_tendsto k hk).eventually
    (arithmetic_prime_norm_budget_rate n A C ε (sq_nonneg _) hC hε)
  filter_upwards [hrate] with L hrate
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have h := hcost N V Δ hN hV
  rw [← arithmetic_prime_page_spectator_cost n (spectatorBulkCount k L)] at h
  rw [fourier_window_pair_exp]
  exact le_trans (le_of_eq (by dsimp only [A]; ring)) h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous product fibers for an arbitrary partition of the leaves -/

namespace Ostmann

open scoped BigOperators

theorem sum_card_partition {L C : Type*} [Fintype L] [Fintype C]
    [DecidableEq C] (component : L → C) :
    (∑ c : C, Fintype.card {i : L // component i = c}) = Fintype.card L := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv component)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed coordinates for the actual internal prime samples

The coordinates count each sample when it is made, not its later occurrences
in descendant lists. Their number is independent of the number of bulk slots.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSampleTier_lt {n : ℕ} (i : MovingSampleIndex n) : movingSampleTier i < n := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
      rcases i with i | ⟨b, i⟩
      · exact Nat.lt_succ_self n
      · exact (ih i).trans (Nat.lt_succ_self n)

theorem card_movingSampleIndex (n : ℕ) : Fintype.card (MovingSampleIndex n) = 2 * n * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card ((TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n)) = _
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
        Fintype.card_fin, card_treeLeafIndex, ih, pow_succ]
      ring

theorem movingCompensationPrior_indexed {A : Type*} (μ : A → ℝ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    movingCompensationPrior μ n a =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      change (∏ j : Fin 4, μ (a j)) = ∏ _t : Unit, ∏ j : Fin 4, μ (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      change movingCompensationPrior μ n a.1 * movingCompensationPrior μ n a.2 =
        ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
          ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type, ih, ih]
      rfl

/-- The tree law is precisely the product of the original coordinate priors.
This identity permits the proved equality-pattern comparison to be applied
without replacing the law by a conditioned or uniform distribution. -/
theorem movingSamplesPrior_coordinates {A : Type*} (μ : ℕ → A → ℝ) (n : ℕ)
    (a : MovingSampleSlots A n) :
    movingSamplesPrior μ a =
      ∏ i : MovingSampleIndex n, μ (movingSampleTier i) (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => rfl
  | @node n u l r hl hr =>
      change movingCompensationPrior (μ n) n u * movingSamplesPrior μ l * movingSamplesPrior μ r =
        ∏ i : (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n), _
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, Fintype.prod_bool,
        movingCompensationPrior_indexed, hl, hr]
      simp only [movingSampleTier, movingSampleCoordinates, Equiv.coe_fn_mk]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompensationWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact compensation factors in the original history weight

Every sampled prime occurs once in the factor `u` at the node where it is
sampled. Its subsequent appearances in descendants do not add factors of `u`.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensationProduct_indexed {A : Type*} (value : A → ℕ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n a)) =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, value (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      simp only [flattenMovingSlots, movingCompensationSlots, MovingSlotReversal.naturalProduct,
        List.map_ofFn, List.prod_ofFn]
      change (∏ j : Fin 4, value (a j)) = ∏ _t : Unit, ∏ j : Fin 4, value (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      simp only [movingCompensationSlots, flattenMovingSlots, movingNaturalProduct_append, ih]
      change _ = ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
        ∏ j : Fin 4, value (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type]
      rfl

theorem movingSampleProduct_coordinates {A : Type*} (value : A → ℕ) {n : ℕ}
    (a : MovingSampleSlots A n) :
    movingSampleProduct value a =
      ∏ i : MovingSampleIndex n, value (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => rfl
  | @node n u l r hl hr =>
      change _ = ∏ i : (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n), _
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, Fintype.prod_bool]
      rw [movingSampleProduct, movingCompensationProduct_indexed, hl, hr]
      simp only [movingSampleCoordinates, Equiv.coe_fn_mk]
      ring

/-- Prior times compensation is precisely the dependent pattern weight
used in the internal-line comparison, before any coincidences are collapsed. -/
theorem movingSamples_compensated_prior {A : Type*} (μ : ℕ → A → ℝ)
    (value : A → ℕ) {n : ℕ} (a : MovingSampleSlots A n) :
    (movingSampleProduct value a : ℝ) * movingSamplesPrior μ a =
      ∏ i : MovingSampleIndex n,
        (value (movingSampleCoordinates A n a i) : ℝ) *
          μ (movingSampleTier i) (movingSampleCoordinates A n a i) := by
  rw [movingSampleProduct_coordinates, movingSamplesPrior_coordinates,
    Nat.cast_prod, Finset.prod_mul_distrib]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_SampleEqualityPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition of finite samples by equality pattern -/

namespace Ostmann
open scoped Classical BigOperators

/-- This equality is a decomposition, so no number-of-samples factor is lost. -/
theorem sum_sample_equality_patterns {I A : Type*} [Fintype I] [Fintype A]
    {M : Type*} [AddCommMonoid M] (f : (I → A) → M) :
    letI := sampleSetoidFintype I
    (∑ x : I → A, f x) =
      ∑ s : Setoid I, ∑ x : {x : Quotient s → A // Function.Injective x},
        f (fun i => x.val (Quotient.mk'' i)) := by
  let _ := sampleSetoidFintype I
  calc
    _ = ∑ p : SampleEqualityPattern I A, f p.evaluate :=
      (Equiv.sum_comp (sampleEqualityPatternEquiv I A) f).symm
    _ = _ := Fintype.sum_sigma _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality patterns of the two actual internal sample trees -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_movingSamplePair {A M : Type*} [Fintype A] [AddCommMonoid M]
    (n : ℕ) (F : MovingSampleSlots A n → MovingSampleSlots A n → M) :
    (∑ l, ∑ r, F l r) = ∑ x : Bool × MovingSampleIndex n → A,
      F ((movingSamplePairCoordinates A n).symm x).1 ((movingSamplePairCoordinates A n).symm x).2 := by
  have hs := Fintype.sum_prod_type (fun a : MovingSampleSlots A n × MovingSampleSlots A n => F a.1 a.2)
  have he := (movingSamplePairCoordinates A n).symm.sum_comp
    (fun a : MovingSampleSlots A n × MovingSampleSlots A n => F a.1 a.2)
  simp only [finite_univ_canonical] at hs he ⊢
  exact hs.symm.trans he.symm

/-- The two histories have exactly `4*n*2^n` independent internal draws,
irrespective of the number of protected bulk positions. -/
theorem card_movingSamplePairIndex (n : ℕ) :
    Fintype.card (Bool × MovingSampleIndex n) = 4 * n * 2 ^ n := by
  rw [Fintype.card_prod, Fintype.card_bool, card_movingSampleIndex]
  ring

theorem movingSamplePair_compensated_prior {A : Type*} (μ : ℕ → A → ℝ)
    (value : A → ℕ) (n : ℕ) (x : Bool × MovingSampleIndex n → A) :
    let a := (movingSamplePairCoordinates A n).symm x
    ((movingSampleProduct value a.1 : ℝ) * movingSamplesPrior μ a.1) *
      ((movingSampleProduct value a.2 : ℝ) * movingSamplesPrior μ a.2) =
        ∏ i : Bool × MovingSampleIndex n, (value (x i) : ℝ) * μ (movingSampleTier i.2) (x i) := by
  dsimp only
  rw [movingSamples_compensated_prior, movingSamples_compensated_prior,
    Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [movingSamplePairCoordinates_left, movingSamplePairCoordinates_right]
  ring

/-- Exact decomposition of the original pair of sample trees by its
equality pattern. No restriction on coincidences between descendants is
inserted, and no factor depending on the bulk length appears. -/
theorem sum_movingSamplePair_patterns {A M : Type*} [Fintype A] [AddCommMonoid M]
    (n : ℕ) (F : MovingSampleSlots A n → MovingSampleSlots A n → M) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    (∑ l, ∑ r, F l r) =
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ x : {x : Quotient s → A // Function.Injective x},
          let a := (movingSamplePairCoordinates A n).symm (fun i => x.val (Quotient.mk'' i))
          F a.1 a.2 := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  have h₁ := sum_movingSamplePair n F
  have h₂ := sum_sample_equality_patterns (I := Bool × MovingSampleIndex n) (A := A) (M := M)
      (fun x => F ((movingSamplePairCoordinates A n).symm x).1
        ((movingSamplePairCoordinates A n).symm x).2)
  simp only [finite_univ_canonical] at h₁ h₂ ⊢
  exact h₁.trans h₂

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePatternBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying representative-prior domination to the literal sampled pair -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPairCompensatedMass_pattern {A C : Type*} (μ : ℕ → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C) (x : C → A) :
    movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm (x ∘ pattern)) =
      internalPatternWeight pattern (fun i => μ (movingSampleTier i.2)) prime x := by
  rw [movingPairCompensatedMass, movingSamplePair_compensated_prior]
  rfl

theorem sampleEqualityPattern_count_le (I : Type*) [Fintype I] :
    let _ := sampleSetoidFintype I
    Fintype.card (Setoid I) ≤ 2 ^ (Fintype.card I) ^ 2 := by
  let _ := sampleSetoidFintype I
  have hi : Function.Injective (fun s : Setoid I => {p : I × I | s p.1 p.2}) := by
    intro s t h
    ext i j
    exact Set.ext_iff.mp h (i, j)
  have h := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_set, Fintype.card_prod, pow_two] using h

/-- A coarse sufficient bound for all patterns at a fixed transfer depth.
In particular no bulk-length variable enters the exponent. -/
theorem movingSamplePair_pattern_count (n : ℕ) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    Fintype.card (Setoid (Bool × MovingSampleIndex n)) ≤ 2 ^ (4 * n * 2 ^ n) ^ 2 := by
  simpa only [card_movingSamplePairIndex] using
    sampleEqualityPattern_count_le (Bool × MovingSampleIndex n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternUniformBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform costs of the actual internal equality patterns -/

namespace Ostmann
open scoped Classical BigOperators

/-- The representative-prior loss is bounded independently of how the
internal slots coincide. -/
theorem movingPattern_loss_le (n r : ℕ) (hr : r ≤ 4 * n * 2 ^ n)
    (E : ℝ) (hE : 0 ≤ E) :
    (2 : ℝ) ^ r * E ^ (4 * n * 2 ^ n - r) ≤
      (max 2 E) ^ (4 * n * 2 ^ n) := by
  have hK : 0 ≤ max (2 : ℝ) E := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  calc
    _ ≤ (max 2 E) ^ r * (max 2 E) ^ (4 * n * 2 ^ n - r) :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) (le_max_left _ _) r)
        (pow_le_pow_left₀ hE (le_max_right _ _) _) (by positivity) (pow_nonneg hK _)
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hr]

theorem movingPattern_quotient_card_le (n : ℕ)
    (s : Setoid (Bool × MovingSampleIndex n)) :
    Fintype.card (Quotient s) ≤ 4 * n * 2 ^ n := by
  have h := Fintype.card_le_of_surjective
    (Quotient.mk'' : Bool × MovingSampleIndex n → Quotient s) Quotient.mk''_surjective
  simpa only [card_movingSamplePairIndex] using h

/-- Summing every original equality pattern introduces only a depth-dependent
factor. The number of protected bulk slots never appears in this cost. -/
theorem movingPattern_error_sum_le (n : ℕ) (E D : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    ∀ R : Setoid (Bool × MovingSampleIndex n) → ℂ,
      (∀ s, ‖R s‖ ≤ D * ((2 : ℝ) ^ Fintype.card (Quotient s) *
        E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s)))) →
      ‖∑ s, R s‖ ≤ (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (D * (max 2 E) ^ (4 * n * 2 ^ n)) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro R hR
  have hp := movingSamplePair_pattern_count n
  dsimp only at hp
  have hcard : (Fintype.card (Setoid (Bool × MovingSampleIndex n)) : ℝ) ≤
      (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) := by exact_mod_cast hp
  calc
    ‖∑ s, R s‖ ≤ ∑ s, ‖R s‖ := norm_sum_le _ _
    _ ≤ ∑ _s : Setoid (Bool × MovingSampleIndex n), D * (max 2 E) ^ (4 * n * 2 ^ n) := by
      apply Finset.sum_le_sum
      intro s _
      exact (hR s).trans (mul_le_mul_of_nonneg_left
        (movingPattern_loss_le n _ (movingPattern_quotient_card_le n s) E hE) hD)
    _ = (Fintype.card (Setoid (Bool × MovingSampleIndex n)) : ℝ) *
        (D * (max 2 E) ^ (4 * n * 2 ^ n)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternCostRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual equality-pattern cost fits the source's error budget -/

namespace Ostmann
open Filter

/-- All equality patterns and representative-prior losses contribute only a
fixed-depth exponential in L when p times its prior is at most exp(C L). -/
theorem movingPattern_total_cost_le_exp (n : ℕ) (C L : ℝ) (hC : 1 ≤ C) (hL : 1 ≤ L) :
    (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (C * L))) ^ (4 * n * 2 ^ n) ≤
      Real.exp ((((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ) : ℝ) * C * L) := by
  let J := 4 * n * 2 ^ n
  have hCL : 1 ≤ C * L := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ C * L := mul_le_mul hC hL (by norm_num) (by linarith)
  have he : (2 : ℝ) ≤ Real.exp (C * L) := by
    have h := Real.add_one_le_exp (C * L)
    linarith
  rw [max_eq_right he]
  calc
    _ ≤ (Real.exp (C * L)) ^ (J ^ 2) * (Real.exp (C * L)) ^ J :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) he _) (by positivity)
    _ = Real.exp (((J ^ 2 + J : ℕ) : ℝ) * C * L) := by
      rw [← pow_add, ← Real.exp_nat_mul]
      congr 1
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticPatternPriorRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A depth-independent cost for all original equality patterns -/

namespace Ostmann
open Filter

/-- The original internal-prior cost has an absolute coefficient of `2^n m`
once the depth is chosen. The fixed pattern count is absorbed only as `L`
tends to infinity; no constant exponential in the depth is charged per slot. -/
theorem movingPattern_prior_cost_rate (k : ℕ) (hk : 0 < k)
    (C ε : ℝ) (hC : 1 ≤ C) (hε : 0 < ε) (hdepth : 8 * C ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, n ≤ k →
      (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
          (max 2 (Real.exp (C * L))) ^ (4 * n * 2 ^ n) ≤
        Real.exp ((2 ^ n : ℕ) * spectatorBulkCount k L + ε * spectatorBulkCount k L) := by
  let J := 4 * k * 2 ^ k
  let A : ℝ := (J ^ 2 : ℕ) * Real.log 2
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hm := (spectatorBulkCount_tendsto k hk).eventually
    (eventually_ge_atTop (A / ε))
  filter_upwards [hm, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (4 / (k : ℝ) ^ 4)] with L hm hL hscale n hn
  have hL0 : 0 ≤ L := by linarith
  have hscale' : 4 ≤ (k : ℝ) ^ 4 * L := by
    simpa only [mul_comm] using
      (div_le_iff₀ (by positivity : 0 < (k : ℝ) ^ 4)).mp hscale
  have hbulk := spectatorBulkCount_half k L hscale'
  have hsmall : A ≤ ε * spectatorBulkCount k L := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hm
  have hJ : 4 * n * 2 ^ n ≤ J := by
    dsimp only [J]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hn) (Nat.pow_le_pow_right (by decide) hn)
  have hcount : (((4 * n * 2 ^ n) ^ 2 : ℕ) : ℝ) * Real.log 2 ≤ A := by
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    exact_mod_cast Nat.pow_le_pow_left hJ 2
  have hkc : 8 * C * (k : ℝ) ≤ (k : ℝ) ^ 4 := by
    calc
      _ ≤ (k : ℝ) ^ 3 * k := mul_le_mul_of_nonneg_right hdepth hkR.le
      _ = _ := by ring
  have hkcL := mul_le_mul_of_nonneg_right hkc hL0
  have hprior : 4 * (n : ℝ) * C * L ≤ (spectatorBulkCount k L : ℝ) := by
    have hnR : (n : ℝ) ≤ k := by exact_mod_cast hn
    have hnk := mul_le_mul_of_nonneg_right hnR (mul_nonneg (by linarith : 0 ≤ C) hL0)
    nlinarith
  have hprior' := mul_le_mul_of_nonneg_left hprior
    (show (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) by positivity)
  have hCL : 1 ≤ C * L := one_le_mul_of_one_le_of_one_le hC hL
  have he : (2 : ℝ) ≤ Real.exp (C * L) := by linarith [Real.add_one_le_exp (C * L)]
  rw [max_eq_right he, ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast at hcount hprior' ⊢
  nlinarith

/-- The retained numerical norm, including all original equality-pattern
weights, has the absolute bulk constant `log 12 + 1`. -/
theorem arithmetic_prime_pattern_budget_rate (ψ : SchwartzMap ℝ ℂ) (n k : ℕ)
    (hk : 0 < k) (hn : n ≤ k) (B Cfreq Cprior ε : ℝ)
    (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior) (hε : 0 < ε)
    (hdepth : 8 * Cprior ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * Cfreq * m) →
          (q.divisors.card : ℝ) ≤ D) ∧
        ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (Cfreq * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
          (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
          ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            B ^ (2 ^ n - 1)) ^ 2 *
            (((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) *
              ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
                (2 * (V : ℝ)) ^ (2 * 2 ^ n)))) * 2 ^ (2 ^ n * m)) ≤
          Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) := by
  filter_upwards [movingPattern_prior_cost_rate k hk Cprior (ε / 4) hCprior
      (by positivity) hdepth,
    arithmetic_prime_fourier_budget_rate ψ n k hk B Cfreq (ε / 4) hCfreq (by positivity),
    (spectatorBulkCount_tendsto k hk).eventually (eventually_ge_atTop (2 / ε))]
    with L hprior hrate hm
  dsimp only
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have hp := hprior n hn
  have hc := hcost N V Δ hN hV
  have htwo : (2 : ℝ) ≤ Real.exp ((ε / 2) * spectatorBulkCount k L) := by
    have hscale := (div_le_iff₀ hε).mp hm
    have he := Real.add_one_le_exp ((ε / 2) * spectatorBulkCount k L)
    nlinarith
  have hprod := mul_le_mul hp hc (by positivity) (Real.exp_nonneg _)
  have hmain := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
  apply le_trans (le_of_eq (by ring)) hmain |>.trans
  apply (mul_le_mul_of_nonneg_right htwo (by positivity)).trans_eq
  simp only [← Real.exp_add]
  congr 1
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FactorialExponential
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary exponential factorial bounds used in arrangement ratios -/

namespace Ostmann

theorem factorial_exp_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.exp ((n : ℝ) * Real.log n - n) ≤ (n.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (show n ≠ 0 by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.two_le_pi])
  calc
    _ ≤ Real.exp (Real.log (n.factorial : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_log (by exact_mod_cast Nat.factorial_pos n)

theorem factorial_exp_upper {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * Real.log n) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  rw [Real.exp_nat_mul, Real.exp_log hn0]
  exact_mod_cast Nat.factorial_le_pow n

/-- Normalization of r independent blocks against all permutations of rm
slots produces the entropy gain -rm log r. -/
theorem block_factorial_ratio {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (m.factorial : ℝ) ^ r / ((r * m).factorial : ℝ) ≤
      Real.exp ((r : ℝ) * m * (1 - Real.log r)) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hr
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hu : (m.factorial : ℝ) ^ r ≤ Real.exp ((r : ℝ) * m * Real.log m) := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ m.factorial by positivity)
      (factorial_exp_upper hm) r
    rw [← Real.exp_nat_mul] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hl := factorial_exp_lower (Nat.mul_pos (by omega : 0 < r) (by omega : 0 < m))
  simp only [Nat.cast_mul, Real.log_mul (ne_of_gt hr0) (ne_of_gt hm0)] at hl
  apply (div_le_iff₀ (show (0 : ℝ) < (r * m).factorial by positivity)).mpr
  calc
    _ ≤ Real.exp ((r : ℝ) * m * Real.log m) := hu
    _ = Real.exp ((r : ℝ) * m * (1 - Real.log r)) *
        Real.exp ((r : ℝ) * m * (Real.log r + Real.log m) - (r : ℝ) * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (Real.exp_nonneg _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionMatching
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting labeled arrangements that respect paired partitions -/

namespace Ostmann

open scoped BigOperators Classical

theorem PartitionMatching.restrict_injective {A B C : Type*}
    {f : A → C} {g : B → C} :
    Function.Injective (fun e : PartitionMatching f g => e.restrict) := by
  intro e e' h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  exact congrArg Subtype.val (Equiv.congr_fun (congrFun h (f a)) ⟨a, rfl⟩)

/-- Each label can be matched independently; an upper bound suffices even
without constructing the inverse assembly map. -/
theorem card_partitionMatching_le {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] (f : A → C) (g : B → C)
    (hcard : ∀ c, Fintype.card {a : A // f a = c} =
      Fintype.card {b : B // g b = c}) :
    Fintype.card (PartitionMatching f g) ≤
      ∏ c, (Fintype.card {a : A // f a = c}).factorial := by
  classical
  calc
    _ ≤ Fintype.card (∀ c, {a : A // f a = c} ≃ {b : B // g b = c}) :=
      Fintype.card_le_of_injective _ PartitionMatching.restrict_injective
    _ = _ := by
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro c _
      exact Fintype.card_equiv (Fintype.equivOfCardEq (hcard c))

theorem card_slotFiber {L C : Type*} [Fintype L]
    (f : L → C) (m : ℕ) (c : C) :
    Fintype.card {x : L × Fin m // f x.1 = c} =
      Fintype.card {l : L // f l = c} * m := by
  classical
  rw [Fintype.card_congr (slotFiberEquiv f m c), Fintype.card_prod, Fintype.card_fin]

/-- Slots and sampled variables remain labeled, so every arrangement is
an actual permutation of all rm positions. -/
theorem card_slotMatching_le {L C : Type*} [Fintype L] [Fintype C]
    (f g : L → C) (m : ℕ)
    (hcard : ∀ c, Fintype.card {l : L // f l = c} =
      Fintype.card {l : L // g l = c}) :
    Fintype.card (PartitionMatching (fun x : L × Fin m => f x.1)
      (fun x : L × Fin m => g x.1)) ≤
      ∏ c, (Fintype.card {l : L // f l = c} * m).factorial := by
  simpa only [card_slotFiber] using
    card_partitionMatching_le (fun x : L × Fin m => f x.1)
      (fun x : L × Fin m => g x.1)
      (fun c => by rw [card_slotFiber, card_slotFiber, hcard c])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ArrangementGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bipartite overlap graph of an actual bulk permutation -/

namespace Ostmann

open scoped Classical

theorem arrangementRight_surjective {L : Type*} {m : ℕ} (hm : 0 < m)
    (e : Equiv.Perm (L × Fin m)) : Function.Surjective (arrangementRight e) := by
  intro c
  obtain ⟨l, rfl⟩ := arrangementLeft_surjective hm e c
  exact ⟨(e (l, ⟨0, hm⟩)).1, arrangement_components_match e (l, ⟨0, hm⟩)⟩

/-- Counting the slots in a component from the two sides gives equal
leaf counts, because every leaf has exactly m slots. -/
theorem arrangement_component_balance {L : Type*} [Fintype L] {m : ℕ}
    (hm : 0 < m) (e : Equiv.Perm (L × Fin m))
    (c : (arrangementGraph m e).ConnectedComponent) :
    Fintype.card {l : L // arrangementLeft e l = c} =
      Fintype.card {l : L // arrangementRight e l = c} := by
  have h := Fintype.card_congr ((arrangementMatching e).restrict c)
  simp only [card_slotFiber] at h
  exact Nat.eq_of_mul_eq_mul_right hm h

theorem arrangement_component_count_le {L : Type*} [Fintype L] {m : ℕ}
    (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) :
    Fintype.card (arrangementGraph m e).ConnectedComponent ≤ Fintype.card L :=
  Fintype.card_le_of_surjective _ (arrangementLeft_surjective hm e)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ComponentFactorial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factorial costs of components in the arrangement graph -/

namespace Ostmann

open scoped BigOperators

/-- Assigning a*m labeled positions to a blocks gives the factorial
inequality used in the count of bad arrangements. -/
theorem component_factorial_le (a m : ℕ) :
    (a * m).factorial ≤ m.factorial ^ a * a ^ (a * m) := by
  classical
  let s : Finset (Fin a) := Finset.univ
  let f : Fin a → ℕ := fun _ => m
  have hmem : f ∈ Finset.piAntidiag s (a * m) := by
    simp [Finset.mem_piAntidiag, s, f]
  have hsum : a ^ (a * m) =
      ∑ k ∈ s.piAntidiag (a * m), Nat.multinomial s k := by
    simpa [s] using
      (Finset.sum_pow_eq_sum_piAntidiag (R := ℕ) s (fun _ => (1 : ℕ)) (a * m))
  have hb := Finset.single_le_sum (fun k (_ : k ∈ Finset.piAntidiag s (a * m)) =>
    Nat.zero_le (Nat.multinomial s k)) hmem
  rw [← hsum] at hb
  have hs := Nat.multinomial_spec s f
  simp only [s, f, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_const, smul_eq_mul] at hs
  rw [← hs]
  exact Nat.mul_le_mul_left _ hb

theorem component_log_cost (a r : ℝ) (ha : 1 ≤ a) (har : a ≤ r) :
    a * Real.log a ≤ (a - 1) * (Real.log r + 1) := by
  have ha0 : 0 < a := by linarith
  have hlog : Real.log a ≤ Real.log r := Real.log_le_log ha0 har
  have hlog' : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
  have hm := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr ha)
  nlinarith

/-- The sum of a-1 is exactly the number of leaves minus the number
of components, so the entropy cost is controlled by this deficit. -/
theorem component_entropy_bound {I : Type*} [Fintype I]
    (a : I → ℕ) (r : ℕ) (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = r) :
    (∑ i, (a i : ℝ) * Real.log (a i)) ≤
      ((r : ℝ) - Fintype.card I) * (Real.log r + 1) := by
  have hle (i : I) : a i ≤ r := by
    rw [← hsum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hcost (i : I) := component_log_cost (a i) r
    (by exact_mod_cast ha i) (by exact_mod_cast hle i)
  calc
    _ ≤ ∑ i, ((a i : ℝ) - 1) * (Real.log r + 1) := Finset.sum_le_sum fun i _ => hcost i
    _ = ((∑ i, (a i : ℝ)) - Fintype.card I) * (Real.log r + 1) := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ = _ := by rw [← Nat.cast_sum, hsum]

/-- Product of the component assignment counts, with the cost expressed
through the deficit in the number of components. -/
theorem component_factorial_product_bound {I : Type*} [Fintype I]
    (a : I → ℕ) (r m : ℕ) (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = r) :
    (∏ i, ((a i * m).factorial : ℝ)) ≤
      (m.factorial : ℝ) ^ r *
        Real.exp ((m : ℝ) * ((r : ℝ) - Fintype.card I) * (Real.log r + 1)) := by
  classical
  have hp (i : I) : (a i : ℝ) ^ (a i * m) =
      Real.exp ((m : ℝ) * ((a i : ℝ) * Real.log (a i))) := by
    have hi : 0 < (a i : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (ha i)
    rw [show (m : ℝ) * ((a i : ℝ) * Real.log (a i)) =
      ((a i * m : ℕ) : ℝ) * Real.log (a i) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hi]
  calc
    _ ≤ ∏ i, (m.factorial : ℝ) ^ a i * (a i : ℝ) ^ (a i * m) := by
      exact_mod_cast (Finset.prod_le_prod' (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
        component_factorial_le (a i) m))
    _ = (m.factorial : ℝ) ^ r * Real.exp ((m : ℝ) * ∑ i, (a i : ℝ) * Real.log (a i)) := by
      simp_rw [hp]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum,
        ← Real.exp_sum, ← Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (component_entropy_bound a r ha hsum) (show 0 ≤ (m : ℝ) by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_BadPartitionCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform counting bound for paired leaf partitions -/

namespace Ostmann

open scoped BigOperators Classical

theorem card_badPartitionPair_le (r t : ℕ) :
    Fintype.card (BadPartitionPair r t) ≤ t ^ (2 * r) := by
  calc
    _ ≤ Fintype.card ((Fin r → Fin t) × (Fin r → Fin t)) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp [Fintype.card_prod, pow_mul, pow_two, mul_pow]

theorem card_badPartitionWitness_le (r : ℕ) :
    Fintype.card (BadPartitionWitness r) ≤ (r + 1) * r ^ (2 * r) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ t : Fin (r + 1), r ^ (2 * r) := by
      apply Finset.sum_le_sum
      intro t _
      exact (card_badPartitionPair_le r t).trans
        (Nat.pow_le_pow_left (Nat.le_of_lt_succ t.isLt) _)
    _ = _ := by simp

theorem badPartitionCost_nonneg (r m : ℕ) : 0 ≤ badPartitionCost r m := by
  unfold badPartitionCost
  positivity

theorem badPartition_matching_bound {r : ℕ} (hr : 1 ≤ r)
    (w : BadPartitionWitness r) (m : ℕ) :
    (Fintype.card (w.Matching m) : ℝ) ≤ badPartitionCost r m := by
  let a : Fin w.1 → ℕ := fun c => Fintype.card {l : Fin r // w.2.1.1 l = c}
  have ha (c : Fin w.1) : 1 ≤ a c := by
    obtain ⟨l, hl⟩ := w.2.2.1 c
    exact Fintype.card_pos_iff.mpr ⟨⟨l, hl⟩⟩
  have hs : ∑ c, a c = r := by
    simpa only [Fintype.card_fin] using sum_card_partition w.2.1.1
  have hc : (Fintype.card (w.Matching m) : ℝ) ≤
      ∏ c, ((a c * m).factorial : ℝ) := by
    have hbal := fun c => w.2.2.2.2.1 c
    have h := card_slotMatching_le w.2.1.1 w.2.1.2 m
      (fun c => by simpa only [Fintype.card_eq_nat_card] using hbal c)
    have hnat : Fintype.card (w.Matching m) ≤ ∏ c, (a c * m).factorial := by
      simpa only [a, Fintype.card_eq_nat_card] using h
    exact_mod_cast hnat
  have ht : (w.1 : ℕ) ≤ r := Nat.le_of_lt_succ w.1.isLt
  have hd : 4 * ((r : ℝ) - (w.1 : ℕ)) ≤ r := by
    have h := w.2.2.2.2.2
    have h' : (4 : ℝ) * ((r - (w.1 : ℕ) : ℕ) : ℝ) ≤ r := by exact_mod_cast h
    simpa only [Nat.cast_sub ht] using h'
  have hl : 0 ≤ Real.log (r : ℝ) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ r by exact_mod_cast hr)
    linarith
  apply hc.trans
  apply (component_factorial_product_bound a r m ha hs).trans
  unfold badPartitionCost
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  simp only [Fintype.card_fin]
  have hh := mul_le_mul_of_nonneg_left hd
    (mul_nonneg (show (0 : ℝ) ≤ m by positivity) hl)
  nlinarith

/-- Sum over every possible pair of component partitions. The prefactor
depends only on r, and not on the number m of slots at a leaf. -/
theorem badPartition_total_bound {r : ℕ} (hr : 1 ≤ r) (m : ℕ) :
    (Fintype.card (Σ w : BadPartitionWitness r, w.Matching m) : ℝ) ≤
      ((r + 1) * r ^ (2 * r) : ℕ) * badPartitionCost r m := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _w : BadPartitionWitness r, badPartitionCost r m :=
      Finset.sum_le_sum fun w _ => badPartition_matching_bound hr w m
    _ = (Fintype.card (BadPartitionWitness r) : ℝ) * badPartitionCost r m := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_badPartitionWitness_le r) (badPartitionCost_nonneg r m)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_BadArrangementCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting bad permutations through their actual overlap components -/

namespace Ostmann

open scoped BigOperators Classical

theorem badBulkArrangement_witness {r m : ℕ} (hm : 0 < m)
    (e : Equiv.Perm (Fin r × Fin m)) (he : BadBulkArrangement e) :
    ∃ w : BadPartitionWitness r,
      ∀ x : Fin r × Fin m, w.2.1.2 (e x).1 = w.2.1.1 x.1 := by
  let C := (arrangementGraph m e).ConnectedComponent
  let t := Fintype.card C
  let E : C ≃ Fin t := Fintype.equivFin C
  let f : Fin r → Fin t := E ∘ arrangementLeft e
  let g : Fin r → Fin t := E ∘ arrangementRight e
  have ht : t ≤ r := by
    simpa only [Fintype.card_fin] using arrangement_component_count_le hm e
  have hf : Function.Surjective f := E.surjective.comp (arrangementLeft_surjective hm e)
  have hg : Function.Surjective g := E.surjective.comp (arrangementRight_surjective hm e)
  have hb (c : Fin t) : Fintype.card {l : Fin r // f l = c} =
      Fintype.card {l : Fin r // g l = c} := by
    have hleft : {l : Fin r // f l = c} ≃
        {l : Fin r // arrangementLeft e l = E.symm c} :=
      Equiv.subtypeEquivRight (fun _ => E.eq_symm_apply.symm)
    have hright : {l : Fin r // g l = c} ≃
        {l : Fin r // arrangementRight e l = E.symm c} :=
      Equiv.subtypeEquivRight (fun _ => E.eq_symm_apply.symm)
    rw [Fintype.card_congr hleft, Fintype.card_congr hright]
    exact arrangement_component_balance hm e _
  have hd : 4 * (r - t) ≤ r := by
    change 3 * r < 4 * t at he
    omega
  refine ⟨⟨⟨t, Nat.lt_succ_of_le ht⟩, ⟨(f, g), hf, hg, hb, hd⟩⟩, ?_⟩
  intro x
  exact congrArg E (arrangement_components_match e x)

theorem card_badBulkArrangement_le {r m : ℕ} (hm : 0 < m) :
    Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} ≤
      Fintype.card (Σ w : BadPartitionWitness r, w.Matching m) := by
  choose w hw using fun e : {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} =>
    badBulkArrangement_witness hm e.1 e.2
  let f : {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} →
      Σ w : BadPartitionWitness r, w.Matching m := fun e => ⟨w e, ⟨e.1, hw e⟩⟩
  apply Fintype.card_le_of_injective f
  intro e e' h
  apply Subtype.ext
  exact congrArg (fun z : Σ w : BadPartitionWitness r, w.Matching m => z.2.1) h

/-- The arrangement count used in Section 9. The prefactor depends only
on the number of leaves r; all m-dependence is explicit. -/
theorem badBulkArrangement_count_bound {r m : ℕ} (hr : 1 ≤ r) (hm : 0 < m) :
    (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) ≤
      ((r + 1) * r ^ (2 * r) : ℕ) * (m.factorial : ℝ) ^ r *
        Real.exp ((m : ℝ) * r * (Real.log r + 1) / 4) := by
  have hc : (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) ≤
      Fintype.card (Σ w : BadPartitionWitness r, w.Matching m) := by
    exact_mod_cast card_badBulkArrangement_le hm
  apply hc.trans
  simpa only [badPartitionCost, mul_assoc] using badPartition_total_bound hr m

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_BadArrangementFraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exponentially small proportion of bad bulk arrangements -/

namespace Ostmann

open scoped Classical

theorem badBulkArrangement_fraction_bound {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) /
        ((r * m).factorial : ℝ) ≤
      ((r + 1) * r ^ (2 * r) : ℕ) *
        Real.exp ((r : ℝ) * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4)) := by
  let C : ℝ := ((r + 1) * r ^ (2 * r) : ℕ)
  let q : ℝ := (m : ℝ) * r * (Real.log r + 1) / 4
  have hc := badBulkArrangement_count_bound hr (show 0 < m by omega)
  change (Fintype.card {e : Equiv.Perm (Fin r × Fin m) // BadBulkArrangement e} : ℝ) ≤
    C * (m.factorial : ℝ) ^ r * Real.exp q at hc
  calc
    _ ≤ C * (m.factorial : ℝ) ^ r * Real.exp q / ((r * m).factorial : ℝ) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = (C * Real.exp q) * ((m.factorial : ℝ) ^ r / ((r * m).factorial : ℝ)) := by ring
    _ ≤ (C * Real.exp q) * Real.exp ((r : ℝ) * m * (1 - Real.log r)) :=
      mul_le_mul_of_nonneg_left (block_factorial_ratio hr hm) (by dsimp [C]; positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [q]
      ring

/-- The total number of labeled arrangements is (rm)!, including when
different slots happen to contain the same prime value. -/
theorem card_bulkPerm (r m : ℕ) :
    Fintype.card (Equiv.Perm (Fin r × Fin m)) = (r * m).factorial := by
  rw [Fintype.card_perm, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SymmetrizedPairBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pair-correlation control of the symmetrized amplitude -/

namespace Ostmann

open scoped BigOperators Classical

theorem finiteFamilyAverage_norm_sq {J X : Type*} [Fintype J]
    (A : J → X → ℂ) (x : X) :
    ‖finiteFamilyAverage A x‖ ^ 2 =
      ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        (∑ i : J, ∑ j : J, A i x * star (A j x)).re := by
  have hs : (∑ i : J, ∑ j : J, A i x * star (A j x)) =
      (∑ i, A i x) * star (∑ j, A j x) := by
    rw [star_sum, Finset.sum_mul_sum]
  rw [hs, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  unfold finiteFamilyAverage
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]

theorem finiteFamilyAverage_energy_le {J X : Type*} [Fintype J] [Fintype X]
    (μ : X → ℝ) (A : J → X → ℂ) :
    (∑ x, μ x * ‖finiteFamilyAverage A x‖ ^ 2) ≤
      ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ∑ i : J, ∑ j : J, ‖∑ x, (μ x : ℂ) * (A i x * star (A j x))‖ := by
  simp_rw [finiteFamilyAverage_norm_sq A]
  have hs :
      (∑ x, μ x * (∑ i : J, ∑ j : J, A i x * star (A j x)).re) =
        ∑ i : J, ∑ j : J, (∑ x, (μ x : ℂ) * (A i x * star (A j x))).re := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  calc
    _ = ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ∑ x, μ x * (∑ i : J, ∑ j : J, A i x * star (A j x)).re := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := congrArg (fun z => ((Fintype.card J : ℝ)⁻¹) ^ 2 * z) hs
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Complex.re_le_norm _)
      (sq_nonneg _)

theorem sum_relative_function {J : Type*} [Group J] [Fintype J]
    (f : J → ℝ) (i : J) : (∑ j, f (i⁻¹ * j)) = ∑ j, f j :=
  (Equiv.mulLeft i⁻¹).bijective.sum_comp f

/-- Bad pairs are counted by a single relative permutation. No invariance
of individual amplitudes or support conditions is required. -/
theorem finiteFamilyAverage_good_bad_bound {J X : Type*} [Group J] [Fintype J]
    [Fintype X] (μ : X → ℝ) (A : J → X → ℂ)
    (bad : J → Prop) (B E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ i j, ‖∑ x, (μ x : ℂ) * (A i x * star (A j x))‖ ≤
      if bad (i⁻¹ * j) then B else E) :
    (∑ x, μ x * ‖finiteFamilyAverage A x‖ ^ 2) ≤
      (Fintype.card {j : J // bad j} : ℝ) / Fintype.card J * B + E := by
  have hc : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc0 : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ j : J, if bad j then B else E) ≤
      (Fintype.card {j : J // bad j} : ℝ) * B + (Fintype.card J : ℝ) * E := by
    calc
      _ ≤ ∑ j : J, ((if bad j then B else 0) + E) := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs <;> linarith
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ, Fintype.card_subtype]
  apply (finiteFamilyAverage_energy_le μ A).trans
  calc
    _ ≤ ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ∑ i : J, ∑ j : J, if bad (i⁻¹ * j) then B else E := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ((Fintype.card J : ℝ) * ∑ j : J, if bad j then B else E) := by
      simp only [sum_relative_function (fun j => if bad j then B else E),
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((Fintype.card J : ℝ)⁻¹) ^ 2 *
        ((Fintype.card J : ℝ) *
          ((Fintype.card {j : J // bad j} : ℝ) * B + (Fintype.card J : ℝ) * E)) := by
      gcongr
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalHistoryCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-depth cost of summing both frequency histories -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem card_frequencyTree (A : Type) [Fintype A] (n : ℕ) :
    Fintype.card (FrequencyTree A n) = (Fintype.card A) ^ (2 ^ (n + 1) - 1) := by
  induction n with
  | zero => simp [FrequencyTree]
  | succ n ih =>
    simp only [FrequencyTree, Fintype.card_prod] at *
    rw [ih, ← pow_add, ← pow_succ']
    congr 1
    have hp : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem frequency_history_pair_card_bound (S : Finset ℤ) (n : ℕ) (C m : ℝ)
    (hS : (S.card : ℝ) ≤ Real.exp (C * m)) :
    ((Fintype.card (FrequencyTree S n) : ℝ) ^ 2) ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * C * m) := by
  rw [card_frequencyTree]
  simp only [Fintype.card_coe]
  push_cast
  rw [← pow_mul]
  have h := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hS ((2 ^ (n + 1) - 1) * 2)
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticPatternErrorRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern and frequency counts preserve the arithmetic error -/

namespace Ostmann
open Filter

theorem pairedFrequencyTree_card (S : Finset ℤ) (n : ℕ) :
    Fintype.card (FrequencyTree (S × S) n) = (Fintype.card (FrequencyTree S n)) ^ 2 := by
  simp only [card_frequencyTree, Fintype.card_prod, pow_two, mul_pow]

theorem movingPattern_frequency_error_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq α β : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq)
    (hα : 0 < α) (hβα : β < α) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (S.card : ℝ) ≤ Real.exp (Cfreq * spectatorBulkCount k L) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        (Fintype.card (FrequencyTree (S × S) n) : ℝ) * Real.exp (-Real.exp (α * L)) ≤
          Real.exp (-Real.exp (β * L)) := by
  let J := 4 * n * 2 ^ n
  let A : ℝ := ((J ^ 2 + J : ℕ) : ℝ) * Cprior
  let B : ℝ := (2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * Cfreq
  let H := A + B * (k : ℝ) ^ 4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  filter_upwards [arithmetic_exponent_absorption 0 α β H 1 0 hα hα hβα (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL S hS
  have hL0 : 0 ≤ L := by linarith
  have hp := movingPattern_total_cost_le_exp n Cprior L hCprior hL
  have hc := frequency_history_pair_card_bound S n Cfreq (spectatorBulkCount k L) hS
  have hc' : (Fintype.card (FrequencyTree (S × S) n) : ℝ) ≤
      Real.exp (B * (k : ℝ) ^ 4 * L) := by
    rw [pairedFrequencyTree_card, Nat.cast_pow]
    apply hc.trans
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left (spectatorBulkCount_upper k L hL0) hB
    exact hm.trans_eq (by ring)
  have hprod := mul_le_mul hp hc' (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hexp : ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
      (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
      (Fintype.card (FrequencyTree (S × S) n) : ℝ) ≤ Real.exp (H * L) := by
    apply hprod.trans_eq
    rw [← Real.exp_add]
    congr 1
    dsimp only [H, A, J]
    ring
  apply (mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero, one_mul] at hrate
  linarith

/-- All three errors in the original-prior norm bound fit the final common
scale after the exact equality-pattern and two-history sums. -/
theorem movingPattern_three_errors_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (S.card : ℝ) ≤ Real.exp (Cfreq * spectatorBulkCount k L) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
          (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) ≤
        3 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [movingPattern_frequency_error_rate n k hk Cprior Cfreq
      (125 / 100000) (12 / 10000) hCprior hCfreq (by norm_num) (by norm_num),
    movingPattern_frequency_error_rate n k hk Cprior Cfreq
      (2 / 1000) (12 / 10000) hCprior hCfreq (by norm_num) (by norm_num)]
    with L hfirst hsecond S hS
  have h := add_le_add (hfirst S hS) (mul_le_mul_of_nonneg_left (hsecond S hS)
    (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith only [h]

/-- The internal-prime comparison contributes one further error of the same
scale. All four errors survive both finite sums with a common saving. -/
theorem movingPattern_four_errors_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (S.card : ℝ) ≤ Real.exp (Cfreq * spectatorBulkCount k L) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
          (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            3 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) ≤
        4 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [movingPattern_three_errors_rate n k hk Cprior Cfreq hCprior hCfreq,
    movingPattern_frequency_error_rate n k hk Cprior Cfreq
      (2 / 1000) (12 / 10000) hCprior hCfreq (by norm_num) (by norm_num)]
    with L hthree hone S hS
  have h := add_le_add (hthree S hS) (hone S hS)
  nlinarith only [h]

/-- The literal giant comparison adds one further error to the two bulk and
one internal comparison errors. All five survive the exact finite sums. -/
theorem movingPattern_five_errors_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℤ,
      (S.card : ℝ) ≤ Real.exp (Cfreq * spectatorBulkCount k L) →
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
        (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
        (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
          (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) ≤
        5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [movingPattern_four_errors_rate n k hk Cprior Cfreq hCprior hCfreq,
    movingPattern_frequency_error_rate n k hk Cprior Cfreq
      (2 / 1000) (12 / 10000) hCprior hCfreq (by norm_num) (by norm_num)]
    with L hfour hone S hS
  have h := add_le_add (hfour S hS) (hone S hS)
  nlinarith only [h]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PatternFrequencyNormSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the arithmetic norm over frequencies and internal patterns -/

namespace Ostmann
open scoped Classical BigOperators

/-- The two-history norm retains every node's reduced-modulus bound. Only
the negligible comparison errors are multiplied by the full history count. -/
theorem paired_frequency_norm_sum_le (S : Finset ℤ) (n N V : ℕ)
    (D K err : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (R : FrequencyTree (S × S) n → ℂ)
    (hR : ∀ t, ‖R t‖ ≤ err + K *
      (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
        ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod)) :
    ‖∑ t, R t‖ ≤ (Fintype.card (FrequencyTree (S × S) n) : ℝ) * err +
      K * ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
        (2 * (V : ℝ)) ^ (2 * 2 ^ n)) := by
  have hsum := arithmetic_frequency_tree_sum_le S N V D hD hS
    (gcd_frequency_divisor_bound S N D hS hdiv) n
  calc
    _ ≤ ∑ t, (err + K * frequencyTreeWeight
        (pairedFrequencyKernel S D) (pairedFrequencyLeaf S V) n t) := by
      apply norm_sum_le_of_le
      intro t _
      simpa only [frequencyTreeWeight_eq_splitList, mul_comm] using hR t
    _ = (Fintype.card (FrequencyTree (S × S) n) : ℝ) * err +
        K * ∑ t, frequencyTreeWeight (pairedFrequencyKernel S D) (pairedFrequencyLeaf S V) n t := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hK)

/-- The same retained frequency sum survives summing every equality pattern
of the original internal prime samples. -/
theorem pattern_frequency_norm_sum_le (S : Finset ℤ) (n N V : ℕ)
    (D E K err : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hK : 0 ≤ K) (herr : 0 ≤ err)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    ∀ R : Setoid (Bool × MovingSampleIndex n) → FrequencyTree (S × S) n → ℂ,
    (∀ s t, ‖R s t‖ ≤
      ((2 : ℝ) ^ Fintype.card (Quotient s) * E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
        (err + K * (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod))) →
    ‖∑ s, ∑ t, R s t‖ ≤
      ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) * (max 2 E) ^ (4 * n * 2 ^ n)) *
        ((Fintype.card (FrequencyTree (S × S) n) : ℝ) * err +
          K * ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) := by
  dsimp only
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro R hR
  let T : ℝ := (Fintype.card (FrequencyTree (S × S) n) : ℝ) * err +
    K * ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
      (2 * (V : ℝ)) ^ (2 * 2 ^ n))
  have hlog := Real.log_natCast_nonneg N
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hs (s : Setoid (Bool × MovingSampleIndex n)) :
      ‖∑ t, R s t‖ ≤ T * ((2 : ℝ) ^ Fintype.card (Quotient s) *
        E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) := by
    let κ : ℝ := (2 : ℝ) ^ Fintype.card (Quotient s) *
      E ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))
    have hκ : 0 ≤ κ := mul_nonneg (by positivity) (pow_nonneg hE _)
    have h := paired_frequency_norm_sum_le S n N V D (κ * K) (κ * err) hD
      (mul_nonneg hκ hK) hS hdiv (R s) (fun t => by
        simpa only [κ, mul_add, mul_assoc] using hR s t)
    exact h.trans_eq (by dsimp only [T]; ring)
  have h := movingPattern_error_sum_le n E T hE hT (fun s => ∑ t, R s t) hs
  exact h.trans_eq (by ring)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticDiagonalPatternNormRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal budget after both giant and bulk comparisons -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The actual pattern sum and paired frequency sum have an absolute bulk
constant. The cutoff includes the constructed bottom reserve `2 sqrt(m)`.
The five comparison errors retain their saving after the full history count. -/
theorem arithmetic_diagonal_pattern_norm_rate (ψ : SchwartzMap ℝ ℂ) (n k : ℕ)
    (hk : 0 < k) (hn : n ≤ k) (B Cfreq Cprior ε : ℝ)
    (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior) (hε : 0 < ε)
    (hdepth : 8 * Cprior ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * Cfreq * m) →
          (q.divisors.card : ℝ) ≤ D) ∧
        ∀ (S : Finset ℤ) (N V : ℕ) (Δ err : ℝ),
        (S.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
        (N : ℝ) ≤ Real.exp (Cfreq * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        0 ≤ err → err ≤ Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) →
        let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
        let K := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            B ^ (2 ^ n - 1)) ^ 2 *
          ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) * 2 ^ (2 ^ n * m)
        ∀ R : Setoid (Bool × MovingSampleIndex n) → FrequencyTree (S × S) n → ℂ,
        (∀ s t, ‖R s t‖ ≤
          ((2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (err + K * (frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
            ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod))) →
        ‖∑ s, ∑ t, R s t‖ ≤
          Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_prime_pattern_budget_rate ψ n k hk hn B Cfreq Cprior ε
      hCfreq hCprior hε hdepth,
    movingPattern_five_errors_rate n k hk Cprior Cfreq hCprior hCfreq]
    with L hbudget herrors
  dsimp only
  obtain ⟨D, hD, hdiv, hbudget⟩ := hbudget
  refine ⟨D, hD, hdiv, ?_⟩
  intro S N V Δ err hcard hS hN hV herr herrbound R hR
  have hdivN : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D := by
    intro q hq hqN
    apply hdiv q hq
    calc
      (q : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hqN
      _ ≤ (Real.exp (Cfreq * spectatorBulkCount k L)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg N) hN 2
      _ = Real.exp (2 * Cfreq * spectatorBulkCount k L) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hsum := pattern_frequency_norm_sum_le S n N V D (Real.exp (Cprior * L))
    (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
      B ^ (2 ^ n - 1)) ^ 2 *
      ((2 : ℝ) ^ (2 ^ n * spectatorBulkCount k L) * 4 * 3 ^ (2 ^ n * spectatorBulkCount k L)) *
        2 ^ (2 ^ n * spectatorBulkCount k L)) err hD (Real.exp_nonneg _) (by positivity)
      herr hS hdivN R hR
  have hcost := hbudget N V Δ hN hV
  have he := (mul_le_mul_of_nonneg_left herrbound
    (show 0 ≤ ((2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
      (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)) *
      (Fintype.card (FrequencyTree (S × S) n) : ℝ) by positivity)).trans (herrors S hcard)
  apply hsum.trans
  nlinarith only [hcost, he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticGoodPatternRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full equality-pattern and frequency sums in the good-matching estimate -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem arithmetic_good_pattern_rate (n k : ℕ) (hk : 0 < k)
    (Cprior Cfreq gain : ℝ) (hCprior : 1 ≤ Cprior) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ S : Finset ℤ, (S.card : ℝ) ≤ Real.exp (Cfreq * m) →
      let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
      ∀ R : Setoid (Bool × MovingSampleIndex n) → FrequencyTree (S × S) n → ℂ,
      (∀ s t, ‖R s t‖ ≤
        ((2 : ℝ) ^ Fintype.card (Quotient s) *
          (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
        (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) +
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) →
      ‖∑ s, ∑ t, R s t‖ ≤ Real.exp (-gain * m) +
        5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [movingPattern_five_errors_rate n k hk Cprior Cfreq hCprior hCfreq,
    eventually_ge_atTop (4 : ℝ)] with L herrors hL
  dsimp only
  intro S hS R hR
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let m := spectatorBulkCount k L
  let A : ℝ := (((4 * n * 2 ^ n) ^ 2 + 4 * n * 2 ^ n : ℕ) : ℝ) * Cprior
  let B : ℝ := (2 * (2 ^ (n + 1) - 1 : ℕ) : ℝ) * Cfreq
  let cost := (2 : ℝ) ^ ((4 * n * 2 ^ n) ^ 2) *
    (max 2 (Real.exp (Cprior * L))) ^ (4 * n * 2 ^ n)
  let err := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
    4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hL0 : 0 ≤ L := by linarith
  have hkpow : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hk)
  have hLL : L ≤ (k : ℝ) ^ 4 * L := by nlinarith only [hkpow, hL0]
  have hhalf := spectatorBulkCount_half k L (show 4 ≤ (k : ℝ) ^ 4 * L by linarith)
  have hLm : L ≤ 2 * (m : ℝ) := by dsimp only [m]; linarith
  have hcost : cost ≤ Real.exp (2 * A * m) := by
    apply (movingPattern_total_cost_le_exp n Cprior L hCprior (by linarith)).trans
    apply Real.exp_le_exp.mpr
    change A * L ≤ 2 * A * m
    nlinarith only [hLm, hA]
  have hcard : (Fintype.card (FrequencyTree (S × S) n) : ℝ) ≤ Real.exp (B * m) := by
    rw [pairedFrequencyTree_card, Nat.cast_pow]
    exact frequency_history_pair_card_bound S n Cfreq m hS
  have hgain : cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
      Real.exp (-goodPatternGain n Cprior Cfreq gain * m) ≤ Real.exp (-gain * m) := by
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul hcost hcard (Nat.cast_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [goodPatternGain, A, B]
    ring
  have hsum : ‖∑ s, ∑ t, R s t‖ ≤
      cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
        (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err) := by
    have hs (s : Setoid (Bool × MovingSampleIndex n)) :
        ‖∑ t, R s t‖ ≤
          ((Fintype.card (FrequencyTree (S × S) n) : ℝ) *
            (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err)) *
          ((2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) := by
      apply (norm_sum_le_of_le _ (fun t _ => hR s t)).trans_eq
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [err]
      ring
    have hh := movingPattern_error_sum_le n (Real.exp (Cprior * L))
      ((Fintype.card (FrequencyTree (S × S) n) : ℝ) *
        (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err))
      (Real.exp_nonneg _) (by dsimp only [err]; positivity) (fun s => ∑ t, R s t) hs
    exact hh.trans_eq (by dsimp only [cost]; ring)
  have he : cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) * err ≤
      5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := herrors S hS
  calc
    _ ≤ _ := hsum
    _ = cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) *
          Real.exp (-goodPatternGain n Cprior Cfreq gain * m) +
        cost * (Fintype.card (FrequencyTree (S × S) n) : ℝ) * err := by ring
    _ ≤ _ := add_le_add hgain he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ConductorDeletion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conductor support after deleting one large prime

For each exceptional conductor choose one prime divisor above the threshold,
if there is one, and exclude that value from the nongiant priors. A conductor
that still divides the arithmetic modulus is then supported on its frequency
block, with full prime-power multiplicity.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem deletedConductorPrime_spec {D T p : ℕ}
    (h : deletedConductorPrime D T = some p) : p.Prime ∧ p ∣ D ∧ T ≤ p := by
  unfold deletedConductorPrime at h
  split at h
  next hex =>
    have hp : hex.choose = p := Option.some.inj h
    exact hp ▸ hex.choose_spec
  next => simp at h

/-- If the chosen large divisor was excluded, any surviving conductor divides
only the small frequency modulus. No squarefree assumption on the conductor
or on either modulus is needed. -/
theorem conductor_dvd_frequency_of_deletion (D Q R T : ℕ)
    (hQ : ∀ p, p.Prime → p ∣ Q → p < T)
    (hR : ∀ p, p.Prime → p ∣ R → T ≤ p)
    (hdeleted : ∀ p, deletedConductorPrime D T = some p → ¬p ∣ R)
    (hD : D ∣ Q * R) : D ∣ Q := by
  by_cases hlarge : ∃ p, p.Prime ∧ p ∣ D ∧ T ≤ p
  · have hsel : deletedConductorPrime D T = some hlarge.choose := by
      simp [deletedConductorPrime, hlarge]
    obtain ⟨hp, hpD, hpT⟩ := hlarge.choose_spec
    have hpQR := dvd_trans hpD hD
    rcases hp.dvd_mul.mp hpQR with hpQ | hpR
    · exact False.elim ((not_lt_of_ge hpT) (hQ _ hp hpQ))
    · exact False.elim (hdeleted _ hsel hpR)
  · have hcop : D.Coprime R := Nat.coprime_of_dvd fun p hp hpD hpR =>
      hlarge ⟨p, hp, hpD, hR p hp hpR⟩
    exact hcop.dvd_of_dvd_mul_left (by simpa only [Nat.mul_comm] using hD)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PageConductorProjection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected Page correction factors through the frequency modulus -/

namespace Ostmann

open Classical

/-- After excluding a selected large conductor prime, the correction on
the full modulus is exactly its correction on the frequency modulus. -/
theorem pageAtModulus_mul_eq (z : Option PrimitiveRealZero) (Q R T : ℕ)
    (hQ : ∀ p, p.Prime → p ∣ Q → p < T)
    (hR : ∀ p, p.Prime → p ∣ R → T ≤ p)
    (hexcluded : ∀ e, z = some e → ∀ p,
      deletedConductorPrime e.modulus T = some p → ¬p ∣ R) :
    pageAtModulus (Q * R) z = pageAtModulus Q z := by
  cases z with
  | none => rfl
  | some e =>
    by_cases hd : e.modulus ∣ Q * R
    · have hf := conductor_dvd_frequency_of_deletion e.modulus Q R T hQ hR
        (hexcluded e rfl) hd
      simp [pageAtModulus, hd, hf]
    · have hf : ¬e.modulus ∣ Q := fun h => hd (dvd_mul_of_dvd_left h R)
      simp [pageAtModulus, hd, hf]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_BulkProgressionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual frequency/spectator modulus fits one progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem bulkResidueModulus_exp_bound (m r : ℕ) (p : Fin m → ℕ) (F V : ℝ)
    (hr : (r : ℝ) ≤ Real.exp (F * m)) (hp : ∀ i, (p i : ℝ) ≤ Real.exp V) :
    ((∏ i, bulkResidueModuli r p i : ℕ) : ℝ) ≤ Real.exp (F * m + (m : ℝ) * V) := by
  have hprod : (∏ i : Fin m, (p i : ℝ)) ≤ Real.exp ((m : ℝ) * V) := by
    calc
      _ ≤ ∏ _i : Fin m, Real.exp V := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hp i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have he : ((∏ i, bulkResidueModuli r p i : ℕ) : ℝ) = (r : ℝ) * ∏ i, (p i : ℝ) := by
    rw [Fintype.prod_sum_type]
    simp only [bulkResidueModuli, Fintype.prod_unique, Nat.cast_mul, Nat.cast_prod]
  rw [he, Real.exp_add]
  exact mul_le_mul hr hprod (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) (Real.exp_nonneg _)

theorem bulkResidueModulus_progression_range (F K : ℝ) (hF : 0 ≤ F) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ (m r : ℕ) (p : Fin m → ℕ),
      (m : ℝ) ≤ K * L → (r : ℝ) ≤ Real.exp (F * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∏ i, bulkResidueModuli r p i) ≤ bulkProgressionCutoff L := by
  filter_upwards [arithmetic_exponent_absorption (1 / 1000) (12 / 10000) 0 ((F + 1) * K) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hrate hL
  intro m r p hm hr hp
  apply Nat.le_floor
  apply (bulkResidueModulus_exp_bound m r p F _ hr hp).trans
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_left hm hF
  have h₂ := mul_le_mul_of_nonneg_right hm (Real.exp_nonneg ((1 / 1000 : ℝ) * L))
  have h₃ : 0 ≤ K * L := mul_nonneg hK hL
  have h₄ : 0 ≤ F * K * L := mul_nonneg (mul_nonneg hF hK) hL
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hrate
  have h₅ := mul_nonneg h₄ (Real.exp_nonneg ((1 / 1000 : ℝ) * L))
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkResidueCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # CRT coprimality for the actual frequency and spectator moduli -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem bulkResidueModuli_pairwise {I : Type*} (r : ℕ) (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hcop : ∀ i, r.Coprime (p i)) :
    Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)) := by
  intro i j hij
  rcases i with u | i <;> rcases j with v | j
  · cases u
    cases v
    exact False.elim (hij rfl)
  · exact hcop j
  · exact (hcop i).symm
  · apply (Nat.coprime_primes (hp i) (hp j)).mpr
    exact fun he => hij (congrArg Sum.inr (hinj he))

theorem bulkResidueModulus_positive {I : Type*} [Fintype I] (r : ℕ) (hr : 0 < r)
    (p : I → ℕ) (hp : ∀ i, 0 < p i) : 0 < ∏ i, bulkResidueModuli r p i := by
  apply Finset.prod_pos
  intro i _
  rcases i with u | i
  · exact hr
  · exact hp i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relabelling repeated sampled slots by their equality-pattern classes -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.naturalProduct_map {σ τ : Type*}
    (f : σ → τ) (value : τ → ℕ) (slots : List σ) :
    naturalProduct value (slots.map f) = naturalProduct (value ∘ f) slots := by
  simp only [naturalProduct, List.map_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pair of sampled trees after fixing an internal pattern -/

namespace Ostmann
open scoped Classical

theorem movingPatternSamples_pair {C : Type*} (n : ℕ)
    (pattern : Bool × MovingSampleIndex n → C) :
    (movingPatternSamples C n pattern false, movingPatternSamples C n pattern true) =
      (movingSamplePairCoordinates C n).symm pattern := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkBudgets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete length and frequency budgets for the original pattern pair -/

namespace Ostmann
open scoped Classical

theorem bulkSlotLeaves_length {A : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    MovingLeafLengthLE n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => simp [bulkSlotLeaves, MovingLeafLengthLE, treeLeafTupleEquiv]
  | succ n ih =>
    change MovingLeafLengthLE n
      (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthLE n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A modulus using only the frequencies of the two fixed histories -/

namespace Ostmann
open scoped Classical

theorem frequencyModelBase_pos (S : Finset ℤ) (n : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) : 0 < frequencyModelBase S n t :=
  Nat.mul_pos (historyFrequencyProduct_pos S hS n _) (historyFrequencyProduct_pos S hS n _)

theorem frequencyModelBase_le (S : Finset ℤ) (n N : ℕ) (t : FrequencyTree (S × S) n)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) :
    frequencyModelBase S n t ≤ N ^ (2 * (2 ^ (n + 1) - 1)) := by
  calc
    _ ≤ N ^ (2 ^ (n + 1) - 1) * N ^ (2 ^ (n + 1) - 1) :=
      Nat.mul_le_mul (historyFrequencyProduct_le S N hN n _) (historyFrequencyProduct_le S N hN n _)
    _ = _ := by rw [← pow_add]; congr 1; omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticBlocks
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete CRT blocks for the original moving-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingArithmeticModuli_product {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) :
    (∏ b, movingArithmeticModuli r q P S b) =
      r * ((∏ p ∈ P, p) ^ 2 * ∏ i ∈ S, q i) := by
  simp only [Fintype.prod_sum_type, movingArithmeticModuli, Fintype.prod_unique,
    Finset.prod_coe_sort, Finset.prod_pow]
  have hp : (∏ x : P, (x : ℕ)) = ∏ p ∈ P, p := Finset.prod_coe_sort P (fun p : ℕ => p)
  rw [hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimePriorDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual harmonic-prime point masses on the separated scales -/

namespace Ostmann

open scoped BigOperators
open Filter

theorem primeSubsetPrior_le_exp (P Q : Finset ℕ) (p : P) (H T : ℝ)
    (hmass : (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hp : Real.exp T ≤ (p : ℝ)) :
    primeSubsetPrior P Q p ≤ Real.exp (H - T) := by
  have hp0 : 0 < (p : ℝ) := (Real.exp_pos T).trans_le hp
  have hi : (p : ℝ)⁻¹ ≤ Real.exp (-T) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hp
  calc
    _ ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ := primeSubsetPrior_atom P Q p
    _ ≤ Real.exp H * Real.exp (-T) :=
      mul_le_mul hmass hi (inv_nonneg.mpr hp0.le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfListWeights
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent cutoff weights in an initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

theorem initialLogSumWeight_nonneg {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) :
    0 ≤ initialLogSumWeight value c x := logCellProfile_nonneg _

theorem initialLogSumWeight_le_one {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) :
    initialLogSumWeight value c x ≤ 1 := logCellProfile_le_one _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveCompensation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting compensation from the actual supported recursion -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSlotCutoff_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E) x s v w =
      (x.compensation value : ℝ) * movingSlotCutoff value childBound pivotBound E x s v w := by
  unfold movingSlotCutoff movingCompensatedExtra
  split_ifs <;> simp only [mul_zero]

theorem MovingSlotState.compensation_rootData {σ : Type*} (value : σ → ℕ)
    (x : MovingSlotState σ) :
    (⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ : MovingSlotState σ).compensation value =
      x.compensation value := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

theorem movingLocalExtra_compensated {σ : Type*} (value : σ → ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingCompensatedExtra value E) =
      movingCompensatedExtra value (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingCompensatedExtra, MovingSlotState.compensation_rootData]

/-- Each node contributes its newly sampled compensation exactly once,
including off-support samples where both sides vanish. -/
theorem movingRecursiveWeight_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t =
        (movingSampleProduct value a : ℂ) *
          recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutc := movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)
  induction a generalizing XL XR with
  | leaf => simp only [movingSampleProduct, Nat.cast_one, one_mul, recursiveTransferWeight]
  | @node n a l r hl hr =>
    let x : MovingSlotState σ :=
      ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
    let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys F cutc n x t P hv,
        recursiveTransferWeight_node sys F cut n x t P hv]
      change (cutc x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.1 *
        star (recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.2) = _
      simp only [ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      rw [hl, hr]
      have hc : cutc x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
          (x.compensation value : ℝ) * cut x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) :=
        movingSlotCutoff_compensated value childBound pivotBound E x _ _ _
      rw [hc]
      simp only [movingSampleProduct, Complex.ofReal_mul, Complex.ofReal_natCast,
        Nat.cast_mul, star_mul, star_natCast]
      change _ = (x.compensation value : ℂ) * _ * _ * _
      simp only [sys, movingSlotSystem, MovingSlotState.child, x, buildMovingSlotData,
        ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      ring
    · have hz₁ : recursiveTransferWeight sys F cutc (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      rw [hz₁, hz₂, mul_zero]

theorem movingSupportedWeight_mul {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (c z : ℂ) :
    movingSupportedWeight value outside T XL XR (c * z) =
      c * movingSupportedWeight value outside T XL XR z := by
  unfold movingSupportedWeight
  split_ifs <;> simp only [mul_zero]

/-- Exact compensated prior times the supported coefficient with node
compensations removed. This is the scalar used by the pattern comparison. -/
theorem movingSampledWeight_compensated_supported {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))
      n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n,
        (((movingSampleProduct value a : ℝ) * movingSamplesPrior μ a : ℝ) : ℂ) *
          movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
            (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
              (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
              ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  rw [movingSampledWeight_supported]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingLocalExtra_compensated, movingRecursiveWeight_compensated,
    movingSupportedWeight_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact paired expansion of the fully supported sampled coefficient

The equality-pattern scalar is the literal original prior times all node
compensations. The remaining coefficient retains every support test.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingCompensatedAverage_pair {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ) (H K : MovingSampleSlots A n → ℂ) :
    movingCompensatedAverage μ value n H * star (movingCompensatedAverage μ value n K) =
      ∑ a, ∑ b, (movingPairCompensatedMass μ value (a, b) : ℂ) * H a * star (K b) := by
  unfold movingCompensatedAverage
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [movingPairCompensatedMass, Complex.ofReal_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- The class assignments are injective, so coincidences are recorded exactly
once; no independence is ascribed to their induced law. -/
theorem movingCompensatedAverage_pair_patterns {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ) (H K : MovingSampleSlots A n → ℂ) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    movingCompensatedAverage μ value n H * star (movingCompensatedAverage μ value n K) =
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ x : {x : Quotient s → A // Function.Injective x},
          let a := (movingSamplePairCoordinates A n).symm (fun i => x.val (Quotient.mk'' i))
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value x.val : ℂ) * H a.1 * star (K a.2) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  rw [movingCompensatedAverage_pair, sum_movingSamplePair_patterns]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  have h := movingPairCompensatedMass_pattern μ value n
    (fun i : Bool × MovingSampleIndex n => (Quotient.mk'' i : Quotient s)) x.val
  dsimp only [Function.comp_def] at h
  rw [h]

theorem movingSupportedSampledWeight_eq {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small bulk XL XR =
      movingCompensatedAverage μ value n
        (movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR) :=
  movingSampledWeight_compensated_supported value outside μ childBound pivotBound F E n t small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalSampleExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original Fourier coefficient under the exact internal sampling law -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalNode_local {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    movingLocalExtra (movingOriginalNode value childBound pivotBound φ G) =
      movingOriginalNode value childBound pivotBound φ G := by
  funext x s v w
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

theorem movingOriginalNode_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G) =
      movingPhiExtra value childBound pivotBound (movingDataExtra (movingCompensationExtra value)) φ G := by
  funext x s v w
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [movingCompensatedExtra, movingOriginalNode, movingPhiExtra,
    movingDataExtra, movingCompensationExtra, MovingSlotState.compensation, Nat.cast_one, one_mul]

/-- The Fourier/window/spectator coefficient is exactly the local sampled
recursion already expanded above. -/
theorem movingOriginalSampleAverage_eq {σ I : Type*} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t small bulk XL XR =
    movingSupportedSampledWeight value outside μ childBound pivotBound
      (movingOriginalLeaf value q F g Dq S ψ X lo hi)
      (movingOriginalNode value childBound pivotBound φ G) n t small bulk XL XR := by
  unfold movingSupportedSampledWeight
  rw [movingSampledWeight_supported, movingLocalExtra_compensated, movingOriginalNode_local,
    movingOriginalNode_compensated]
  rfl

/-- After extracting compensation, the retained term is the original giant
coefficient with unit data at internal nodes. -/
theorem movingSupportedSampleTerm_original {σ I : Type*}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ)
    (a : MovingSampleSlots σ n) :
    movingSupportedSampleTerm value outside childBound pivotBound
      (movingOriginalLeaf value q F g Dq S ψ X lo hi)
      (movingOriginalNode value childBound pivotBound φ G) n t small bulk XL XR a =
    movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
      (movingOriginalGiantWeight q value childBound pivotBound F (fun _ _ _ _ => 1)
        g Dq S ψ X lo hi φ G (buildMovingSlotData n t small bulk a) t XL XR) := by
  unfold movingSupportedSampleTerm
  rw [movingOriginalNode_local]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual sampled coefficient over its internal frequencies -/

namespace Ostmann
open scoped Classical BigOperators

theorem scheduledFrequencyRootEquiv_history (V : ℕ → ℕ) (n : ℕ)
    (t : ScheduledFrequencyIndex V n) :
    scheduledFrequencyHistory V n t =
      movingRootedFrequencyTree V n (scheduledFrequencyRootEquiv V n t).1.val
        (scheduledFrequencyRootEquiv V n t).2 := by
  cases n <;> rfl

/-- Identification with the already proved original prime-pattern expansion.
This links the finite frequency coefficient to the arithmetic comparison. -/
theorem movingFrequencyCoefficient_original {σ I : Type} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk XL XR =
      ∑ t : MovingDescendantFrequencyIndex V n,
        movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
          n (movingRootedFrequencyTree V n s t) small bulk XL XR := by
  simp only [movingFrequencyCoefficient, movingOriginalSampleAverage_eq]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ArrangementReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting actual overlap graphs along a leaf enumeration -/

namespace Ostmann

theorem arrangement_component_count_reindex {L L' : Type*} [Fintype L] [Fintype L']
    (f : L ≃ L') {m : ℕ} (e : Equiv.Perm (L × Fin m)) :
    Fintype.card (arrangementGraph m (reindexArrangement f e)).ConnectedComponent =
      Fintype.card (arrangementGraph m e).ConnectedComponent :=
  (Fintype.card_congr (arrangementGraphReindex f e).connectedComponentEquiv).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkPairedCutoffs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bulk leaf lists and their retained logarithmic cutoffs -/

namespace Ostmann
open scoped Classical BigOperators

theorem treeLeafProduct_eq_prod {A : Type*} [CommMonoid A] (n : ℕ)
    (a : TreeLeafTuple A n) :
    treeLeafProduct n a = ∏ i : TreeLeafIndex n, treeLeafTupleEquiv A n a i := by
  induction n with
  | zero =>
    change A at a
    change a = @Finset.prod Unit A _ Finset.univ (fun _ => a)
    simp
  | succ n ih =>
    change treeLeafProduct n a.1 * treeLeafProduct n a.2 =
      ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n,
        Sum.elim (treeLeafTupleEquiv A n a.1) (treeLeafTupleEquiv A n a.2) i
    rw [Fintype.prod_sum_type, ih, ih]
    rfl

theorem movingBulkPairedCutoffSlots_product {B : Type*} (n : ℕ)
    (bulk : Bool → TreeLeafTuple (List B) n) (f : List B → ℝ) :
    (∏ j, f (movingBulkPairedCutoffSlots n bulk j)) =
      treeLeafProduct n (treeLeafMap f n (bulk false)) *
        treeLeafProduct n (treeLeafMap f n (bulk true)) := by
  simp only [movingBulkPairedCutoffSlots, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    treeLeafProduct_eq_prod, treeLeafTupleEquiv_map]
  exact congrArg₂ (· * ·)
    ((treeLeafEnumeration n).symm.prod_comp (fun i => f (treeLeafTupleEquiv (List B) n (bulk false) i)))
    ((treeLeafEnumeration n).symm.prod_comp (fun i => f (treeLeafTupleEquiv (List B) n (bulk true) i)))

theorem movingBulkPairedCutoffSlots_map {B C : Type*} (n : ℕ)
    (bulk : Bool → TreeLeafTuple (List B) n) (g : B → C) (j : Fin (2 ^ n + 2 ^ n)) :
    movingBulkPairedCutoffSlots n (fun b => treeLeafMap (List.map g) n (bulk b)) j =
      (movingBulkPairedCutoffSlots n bulk j).map g := by
  refine Fin.addCases ?_ ?_ j <;> intro i <;>
    simp only [movingBulkPairedCutoffSlots, Fin.append_left, Fin.append_right, treeLeafTupleEquiv_map]

theorem bulkLogCutoffWeight_map {B C : Type*} (value : C → ℝ)
    (g : B → C) (cb : ℝ) (slots : List B) :
    bulkLogCutoffWeight value cb (slots.map g) =
      bulkLogCutoffWeight (value ∘ g) cb slots := by
  simp only [bulkLogCutoffWeight, realSlotProduct, List.map_map]

theorem treeLeafTuple_list_length {B : Type*} (n : ℕ) (bulk : TreeLeafTuple (List B) n)
    (m : ℕ) (h : MovingLeafLengthLE n bulk m) (j : TreeLeafIndex n) :
    (treeLeafTupleEquiv (List B) n bulk j).length ≤ m := by
  induction n with
  | zero => exact h
  | succ n ih =>
    cases j with
    | inl j => exact ih bulk.1 h.1 j
    | inr j => exact ih bulk.2 h.2 j

theorem movingBulkPairedCutoffSlots_length {B : Type*} (n m : ℕ)
    (bulk : Bool → TreeLeafTuple (List B) n)
    (h : ∀ b, MovingLeafLengthLE n (bulk b) m) (j : Fin (2 ^ n + 2 ^ n)) :
    (movingBulkPairedCutoffSlots n bulk j).length ≤ m := by
  refine Fin.addCases ?_ ?_ j <;> intro i
  · simp only [movingBulkPairedCutoffSlots, Fin.append_left]
    exact treeLeafTuple_list_length n (bulk false) m (h false) _
  · simp only [movingBulkPairedCutoffSlots, Fin.append_right]
    exact treeLeafTuple_list_length n (bulk true) m (h true) _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingScheduledLeafCongruence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only the scheduled bottom frequencies evaluate a leaf multiplier -/
namespace Ostmann
open scoped Classical BigOperators

theorem recursiveTransferWeight_scheduled_leaf_congr {State : Type*}
    (sys : TransferHistorySystem State) (F H : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (V : ℕ → ℕ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (n : ℕ) (x : State) (t : ScheduledFrequencyIndex V n) :
    recursiveTransferWeight sys F cutoff n x (scheduledFrequencyHistory V n t) =
      recursiveTransferWeight sys H cutoff n x (scheduledFrequencyHistory V n t) := by
  induction n generalizing x with
  | zero => exact hF x t.val ((mem_transferFrequencyRange _ _).mp t.property)
  | succ n ih =>
    simp only [scheduledFrequencyHistory, recursiveTransferWeight]
    rw [ih _ t.2.1, ih _ t.2.2]

theorem recursiveTransferWeight_rooted_leaf_congr {State : Type*}
    (sys : TransferHistorySystem State) (F H : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (V : ℕ → ℕ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n) (x : State)
    (t : MovingDescendantFrequencyIndex V n) :
    recursiveTransferWeight sys F cutoff n x (movingRootedFrequencyTree V n s t) =
      recursiveTransferWeight sys H cutoff n x (movingRootedFrequencyTree V n s t) := by
  let root : transferFrequencyRange (V n) := ⟨s, (mem_transferFrequencyRange _ _).mpr hs⟩
  let d := (scheduledFrequencyRootEquiv V n).symm (root, t)
  have he : scheduledFrequencyHistory V n d = movingRootedFrequencyTree V n s t := by
    rw [scheduledFrequencyRootEquiv_history]
    simp only [d, Equiv.apply_symm_apply, root]
  rw [← he]
  exact recursiveTransferWeight_scheduled_leaf_congr sys F H cutoff V hF n x d

theorem movingFrequencyCoefficient_leaf_congr {P : Type} [Fintype P]
    (value : P → ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F H : MovingSlotState P → ℤ → ℂ)
    (hF : ∀ x s, s.natAbs ≤ V 0 → F x s = H x s)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (small bulk : TreeLeafTuple (List P) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small bulk XL XR =
      movingFrequencyCoefficient value outside μ childBound pivotBound V H φ G n s small bulk XL XR := by
  unfold movingFrequencyCoefficient
  apply Finset.sum_congr rfl
  intro t _
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  unfold movingSupportedSampleTerm
  rw [recursiveTransferWeight_rooted_leaf_congr _ F H _ V hF n s hs]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePrimeExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact sample expansion inside the actual giant-prime averages -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexPrimeInterval_sum {I : Type*} (q a : ℕ) (u v : ℝ)
    (S : Finset I) (F : I → ℝ → ℂ) :
    complexPrimeInterval q a u v (fun x => ∑ i ∈ S, F i x) =
      ∑ i ∈ S, complexPrimeInterval q a u v (F i) := by
  unfold complexPrimeInterval
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.Prime ∧ Nat.ModEq q p a
  · simp [h]
  · simp [h]

theorem complexPrimeInterval_const_mul (q a : ℕ) (u v : ℝ) (c : ℂ) (F : ℝ → ℂ) :
    complexPrimeInterval q a u v (fun x => c * F x) =
      c * complexPrimeInterval q a u v F := by
  unfold complexPrimeInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [mul_assoc, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalPrimeExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant-prime mean as a sum of supported pattern means -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalSampleAverage_compensated {σ I : Type*} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t small bulk XL XR =
    movingCompensatedAverage μ value n (fun a =>
      movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
        (movingOriginalGiantWeight q value childBound pivotBound F (fun _ _ _ _ => 1)
          g Dq S ψ X lo hi φ G (buildMovingSlotData n t small bulk a) t XL XR)) := by
  rw [movingOriginalSampleAverage_eq, movingSupportedSampledWeight_eq]
  congr 1
  funext a
  exact movingSupportedSampleTerm_original q value outside childBound pivotBound F g Dq S
    ψ X lo hi φ G n t small bulk XL XR a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyPrimeSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual coefficient square inside the original two prime intervals -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

/-- Enlarging only the shared-root restriction costs no factor. This is used
after the exact original prime-pair expansion of each coefficient square. -/
theorem same_root_scheduled_pair_sum_le (V : ℕ → ℕ) (n : ℕ)
    (F : ScheduledFrequencyIndex V n → ScheduledFrequencyIndex V n → ℝ)
    (hF : ∀ a b, 0 ≤ F a b) :
    (∑ s : transferFrequencyRange (V n), ∑ a : MovingDescendantFrequencyIndex V n,
      ∑ b : MovingDescendantFrequencyIndex V n,
        F ((scheduledFrequencyRootEquiv V n).symm (s, a))
          ((scheduledFrequencyRootEquiv V n).symm (s, b))) ≤
    ∑ a : ScheduledFrequencyIndex V n, ∑ b : ScheduledFrequencyIndex V n, F a b := by
  let e := sameRootScheduledPairEmbedding V n
  have h : (∑ t ∈ Finset.univ.map e, F t.1 t.2) ≤
      ∑ t : ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n, F t.1 t.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ.map e))
    (by intro a _ _; exact hF a.1 a.2)
  rw [Finset.sum_map] at h
  change (∑ a : transferFrequencyRange (V n) ×
    (MovingDescendantFrequencyIndex V n × MovingDescendantFrequencyIndex V n),
    F ((scheduledFrequencyRootEquiv V n).symm (a.1, a.2.1))
      ((scheduledFrequencyRootEquiv V n).symm (a.1, a.2.2))) ≤ _ at h
  simpa only [Fintype.sum_prod_type] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_MovingZeroFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zero frequencies vanish in the original sampled histories -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem recursiveTransferWeight_nonzero_frequencies {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (hleaf : ∀ x, leaf x 0 = 0)
    (n : ℕ) (x : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  induction n generalizing x with
  | zero =>
    intro s hs
    have hst : s = t := by simpa only [allFrequencyList, List.mem_singleton] using hs
    subst s
    intro hz
    subst t
    exact ht (hleaf x)
  | succ n ih =>
    obtain ⟨P, hP, _, _⟩ := recursiveTransferWeight_nonzero_valid sys leaf cutoff _ x t ht
    rw [recursiveTransferWeight_node sys leaf cutoff n x t P hP] at ht
    have hL : recursiveTransferWeight sys leaf cutoff n (sys.leftState x P) t.2.1 ≠ 0 := by
      intro hz
      exact ht (by rw [hz, mul_zero, zero_mul])
    have hR : recursiveTransferWeight sys leaf cutoff n (sys.rightState x P) t.2.2 ≠ 0 := by
      intro hz
      exact ht (by rw [hz, star_zero, mul_zero])
    intro s hs
    simp only [allFrequencyList, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · exact hP.root_ne_zero
    · exact ih _ _ hL s hs
    · exact ih _ _ hR s hs

theorem movingSupportedSampledWeight_zero_frequency {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (hF : ∀ x, F x 0 = 0)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (hz : ¬ ∀ s ∈ allFrequencyList n t, s ≠ 0) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E
      n t small bulk XL XR = 0 := by
  unfold movingSupportedSampledWeight movingSampledWeight
  apply Finset.sum_eq_zero
  intro a _
  suffices h : recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound
        (movingLocalExtra
          (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))))
      n ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t = 0 by
    rw [h, mul_zero]
  by_contra hn
  apply hz
  apply recursiveTransferWeight_nonzero_frequencies _ _ _ _ n _ t hn
  intro x
  simp only [movingGuardedLeaf, hF, ite_self]

theorem movingOriginalSampleAverage_zero_frequency {σ I : Type} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ n (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (hz : ¬ ∀ s ∈ allFrequencyList n t, s ≠ 0) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t small bulk XL XR = 0 := by
  rw [movingOriginalSampleAverage_eq]
  apply movingSupportedSampledWeight_zero_frequency value outside μ childBound pivotBound
    _ _ _ n t small bulk XL XR hz
  intro x
  simp only [movingOriginalLeaf, movingWindowLeaf, movingDataLeaf, hF, ite_self,
    zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small and bulk slots at a moving-giant level -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateSmall_length (n r m : ℕ) :
    MovingLeafLengthLE n (movingTemplateSmall n r m) r := bulkSlotLeaves_length n r _

theorem movingTemplateSmall_not_bulk (n r m : ℕ) :
    ∀ i ∈ flattenMovingSlots n (movingTemplateSmall n r m), i ∉ Set.range (movingTemplateBulk n r m) := by
  intro i hi hbulk
  obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n r _ i).mp hi
  obtain ⟨k, hk⟩ := hbulk
  have hs : (Sum.inr k.2 : Fin r ⊕ Fin m) = .inl j.2 :=
    congrArg (fun z : MovingRegularSlot n r m => z.2) hk
  cases hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternSumCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact passage from injective class assignments to the comparison sum -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_injective_assignments {A C M : Type*} [Fintype A] [Fintype C]
    [AddCommMonoid M] (F : (C → A) → M) :
    (∑ z : {z : C → A // Function.Injective z}, F z.val) =
      ∑ z : C → A, if Function.Injective z then F z else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun z : C → A => Function.Injective z))
    (by simp) F, Finset.sum_filter]

theorem sum_external_injective_pattern {A B C M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M]
    (F : (B → A) → (C → A) → M) :
    (∑ y : B → A, ∑ z : {z : C → A // Function.Injective z}, F y z.val) =
      ∑ x : B ⊕ C → A,
        if Function.Injective (fun c => x (.inr c)) then
          F (fun b => x (.inl b)) (fun c => x (.inr c)) else 0 := by
  simp_rw [sum_injective_assignments]
  have hp := Fintype.sum_prod_type (fun yz : (B → A) × (C → A) =>
    if Function.Injective yz.2 then F yz.1 yz.2 else 0)
  have he := (Equiv.sumArrowEquivProdArrow B C A).sum_comp
    (fun yz : (B → A) × (C → A) => if Function.Injective yz.2 then F yz.1 yz.2 else 0)
  simp only [finite_univ_canonical] at hp he ⊢
  exact hp.symm.trans he.symm

/-- This is an exact zero extension of the original injective class sum;
it is the form to which the independent-prior comparison applies. -/
theorem sum_external_injective_pattern_fin {A B C M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (F : (B → A) → (C → A) → M) :
    (∑ y : B → A, ∑ z : {z : C → A // Function.Injective z}, F y z.val) =
      ∑ x : Fin (N + 1) → A,
        if Function.Injective (fun c => x (e.symm (.inr c))) then
          F (fun b => x (e.symm (.inl b))) (fun c => x (e.symm (.inr c))) else 0 := by
  rw [sum_external_injective_pattern]
  have he := (Equiv.arrowCongr e (Equiv.refl A)).sum_comp
    (fun x : B ⊕ C → A => if Function.Injective (fun c => x (.inr c)) then
      F (fun b => x (.inl b)) (fun c => x (.inr c)) else 0)
  simp only [finite_univ_canonical] at he ⊢
  exact he.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalPatternSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original pattern weights and their exact zero extension -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original dependent pattern coefficient with independent external
priors is exactly the full finite-coordinate sum with this support mask. -/
theorem movingOriginalPattern_sum_fin {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (n : ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) :
    (∑ y : B → A, ∑ z : {z : C → A // Function.Injective z},
      ((∏ b, ν b (y b) : ℝ) : ℂ) *
        (internalPatternWeight pattern (fun i => μ (movingSampleTier i.2)) prime z.val : ℂ) *
        G (fun i => Sum.elim y z.val (e i))) =
    ∑ x : Fin (N + 1) → A, ((∏ b, ν b (x (e.symm (.inl b))) : ℝ) : ℂ) *
      (movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
        (fun i => x (e.symm (.inr (pattern i))))) : ℂ) * movingPatternInjectionGuard e G x := by
  rw [sum_external_injective_pattern_fin e (fun y z =>
    ((∏ b, ν b (y b) : ℝ) : ℂ) *
      (internalPatternWeight pattern (fun i => μ (movingSampleTier i.2)) prime z : ℂ) *
      G (fun i => Sum.elim y z (e i)))]
  apply Finset.sum_congr rfl
  intro x _
  have heval : (fun i => Sum.elim (fun b => x (e.symm (.inl b)))
      (fun c => x (e.symm (.inr c))) (e i)) = x := by
    have h (j : B ⊕ C) : Sum.elim (fun b => x (e.symm (.inl b)))
        (fun c => x (e.symm (.inr c))) j = x (e.symm j) := by cases j <;> rfl
    funext i
    rw [h, Equiv.symm_apply_apply]
  rw [heval]
  have hp := movingPairCompensatedMass_pattern μ prime n pattern
    (fun c => x (e.symm (.inr c)))
  simp only [Function.comp_def] at hp
  rw [hp]
  unfold movingPatternInjectionGuard
  split_ifs <;> simp only [mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLeafAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scalar leaf weights retain the actual frequency cutoff -/

namespace Ostmann
open scoped Classical

theorem frequencyLeafWeight_pair_projection (S : Finset ℤ) (V n : ℕ)
    (t : FrequencyTree (S × S) n) :
    frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t) *
      frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t) =
      frequencyLeafWeight (pairedFrequencyLeaf S V) n t := by
  induction n with
  | zero =>
    change (if (t.1 : ℤ).natAbs ≤ V then (1 : ℝ) else 0) *
      (if (t.2 : ℤ).natAbs ≤ V then 1 else 0) = _
    unfold frequencyLeafWeight pairedFrequencyLeaf
    split_ifs <;> simp_all
  | succ n ih =>
    change
      (frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t.2.1) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n false t.2.2)) *
      (frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t.2.1) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n (frequencyPairProjection S n true t.2.2)) = _ * _
    rw [show ∀ a b c d : ℝ, (a * b) * (c * d) = (a * c) * (b * d) by intros; ring]
    rw [ih t.2.1, ih t.2.2]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledHistoryEmbedding
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the actual varying-cutoff histories without adding bottom frequencies -/

namespace Ostmann
open scoped BigOperators Classical

theorem scheduledHistoryEmbedding_map (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n) :
    frequencyTreeMap Subtype.val n (scheduledHistoryEmbedding V hV n a) =
      scheduledFrequencyHistory V n a.val :=
  frequencyTreeInFinset_map _ _ _ _

theorem scheduledFrequencyHistory_leaf_cutoff (V : ℕ → ℕ) (n : ℕ)
    (a : ScheduledFrequencyIndex V n) :
    frequencyLeafWeight (fun v : ℤ => if v.natAbs ≤ V 0 then (1 : ℝ) else 0)
      n (scheduledFrequencyHistory V n a) = 1 := by
  induction n with
  | zero =>
    exact ite_eq_left (scheduledFrequencyHistory_root_bound V 0 a)
  | succ n ih =>
    change frequencyLeafWeight _ n (scheduledFrequencyHistory V n a.2.1) *
      frequencyLeafWeight _ n (scheduledFrequencyHistory V n a.2.2) = 1
    rw [ih, ih, mul_one]

theorem scheduledHistoryEmbedding_leaf_cutoff (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n) :
    frequencyLeafWeight (singleFrequencyLeaf ((transferFrequencyRange (V n)).erase 0) (V 0))
      n (scheduledHistoryEmbedding V hV n a) = 1 := by
  have h := scheduledFrequencyHistory_leaf_cutoff V n a.val
  rw [← scheduledHistoryEmbedding_map V hV n a, frequencyLeafWeight_map] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PairedScheduledHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original scheduled histories as one paired frequency tree -/

namespace Ostmann
open scoped Classical BigOperators

theorem pairedScheduledHistoryEmbedding_projection (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n) (side : Bool) :
    frequencyTreeMap Subtype.val n
      (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n side
        (pairedScheduledHistoryEmbedding V hV n a)) =
      scheduledFrequencyHistory V n (if side then a.2.val else a.1.val) := by
  change frequencyTreeMap Subtype.val n (frequencyPairProjection _ n side
    (pairFrequencyTrees _ n (scheduledHistoryEmbedding V hV n a.1)
      (scheduledHistoryEmbedding V hV n a.2))) = _
  rw [frequencyPairProjection_pair]
  cases side <;> exact scheduledHistoryEmbedding_map V hV n _

/-- Passing to a common internal cutoff retains the actual bottom cutoff on
both sides of the original square. -/
theorem pairedScheduledHistoryEmbedding_leaf (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n) :
    frequencyLeafWeight (pairedFrequencyLeaf ((transferFrequencyRange (V n)).erase 0) (V 0)) n
      (pairedScheduledHistoryEmbedding V hV n a) = 1 := by
  rw [← frequencyLeafWeight_pair_projection]
  change frequencyLeafWeight _ n
      (frequencyPairProjection _ n false (pairFrequencyTrees _ n (scheduledHistoryEmbedding V hV n a.1)
        (scheduledHistoryEmbedding V hV n a.2))) *
    frequencyLeafWeight _ n
      (frequencyPairProjection _ n true (pairFrequencyTrees _ n (scheduledHistoryEmbedding V hV n a.1)
        (scheduledHistoryEmbedding V hV n a.2))) = 1
  simp only [frequencyPairProjection_pair, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
    scheduledHistoryEmbedding_leaf_cutoff, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PairedScheduledSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending both scheduled frequency sums with their bottom cutoffs intact -/

namespace Ostmann
open scoped Classical BigOperators

theorem paired_scheduled_history_sum_le (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (F : FrequencyTree ℤ n → FrequencyTree ℤ n → ℝ)
    (hF : ∀ a b, 0 ≤ F a b)
    (hzeroL : ∀ a : ScheduledFrequencyIndex V n, ∀ t,
      ¬(∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) →
        F (scheduledFrequencyHistory V n a) t = 0)
    (hzeroR : ∀ t, ∀ a : ScheduledFrequencyIndex V n,
      ¬(∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) →
        F t (scheduledFrequencyHistory V n a) = 0) :
    (∑ a : ScheduledFrequencyIndex V n, ∑ b : ScheduledFrequencyIndex V n,
      F (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b)) ≤
    ∑ t : FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
      ((transferFrequencyRange (V n)).erase 0)) n,
      if frequencyLeafWeight (pairedFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
        (V 0)) n t = 1 then
        F (frequencyTreeMap Subtype.val n
            (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n false t))
          (frequencyTreeMap Subtype.val n
            (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n true t))
      else 0 := by
  let p := fun a : ScheduledFrequencyIndex V n =>
    ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0
  have hr (t : FrequencyTree ℤ n) :
      (∑ b : ScheduledFrequencyIndex V n, F t (scheduledFrequencyHistory V n b)) =
        ∑ b : NonzeroScheduledHistory V n, F t (scheduledFrequencyHistory V n b.val) := by
    have h := Fintype.sum_subtype_add_sum_subtype p (fun b => F t (scheduledFrequencyHistory V n b))
    have hz : (∑ b : {b // ¬p b}, F t (scheduledFrequencyHistory V n b.val)) = 0 :=
      Finset.sum_eq_zero (fun b _ => hzeroR t b.val b.property)
    rw [hz, add_zero] at h
    exact h.symm
  have hl :
      (∑ a : ScheduledFrequencyIndex V n, ∑ b : NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b.val)) =
      ∑ a : NonzeroScheduledHistory V n, ∑ b : NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a.val) (scheduledFrequencyHistory V n b.val) := by
    have h := Fintype.sum_subtype_add_sum_subtype p (fun a =>
      ∑ b : NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b.val))
    have hz : (∑ a : {a // ¬p a}, ∑ b : NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a.val) (scheduledFrequencyHistory V n b.val)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact Finset.sum_eq_zero (fun b _ => hzeroL a.val _ a.property)
    rw [hz, add_zero] at h
    exact h.symm
  let e := pairedScheduledHistoryEmbedding V hV n
  let G := fun t : FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
      ((transferFrequencyRange (V n)).erase 0)) n =>
    if frequencyLeafWeight (pairedFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
      (V 0)) n t = 1 then
      F (frequencyTreeMap Subtype.val n
          (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n false t))
        (frequencyTreeMap Subtype.val n
          (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n true t))
    else 0
  have he (a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n) :
      G (e a) = F (scheduledFrequencyHistory V n a.1.val) (scheduledFrequencyHistory V n a.2.val) := by
    dsimp only [G, e]
    rw [pairedScheduledHistoryEmbedding_leaf, ite_eq_left rfl,
      pairedScheduledHistoryEmbedding_projection, pairedScheduledHistoryEmbedding_projection]
    rfl
  calc
    _ = ∑ a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a.1.val) (scheduledFrequencyHistory V n a.2.val) := by
      simp_rw [hr]
      rw [hl, Fintype.sum_prod_type]
    _ = ∑ a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n, G (e a) := by
      exact Finset.sum_congr rfl (fun a _ => (he a).symm)
    _ ≤ ∑ t, G t := by
      rw [← Finset.sum_map]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro t _ _
        dsimp only [G]
        split_ifs
        · exact hF _ _
        · exact le_rfl)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalPatternMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact equality patterns under the original external prime law -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- Finite reindexing is proved independently of the large prime integrand. -/
theorem moving_external_pattern_mean {σ B : Type} [Fintype σ] [Fintype B]
    (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ) (value : σ → ℕ) (n : ℕ)
    (H : (B → σ) → (MovingSampleSlots σ n × MovingSampleSlots σ n) → ℂ) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    ∀ (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
      (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s),
    (∑ y : B → σ, ((∏ b, ν b (y b) : ℝ) : ℂ) *
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ z : {z : Quotient s → σ // Function.Injective z},
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value z.val : ℂ) *
          H y ((movingSamplePairCoordinates σ n).symm (fun i => z.val (Quotient.mk'' i)))) =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → σ,
      movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
        (fun x => H (fun b => x ((e s).symm (.inl b)))
          ((movingSamplePairCoordinates σ n).symm
            (fun i => x ((e s).symm (.inr (Quotient.mk'' i)))))) x := by
  dsimp only
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  intro N e
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  let obs := fun x : Fin (N s + 1) → σ => H (fun b => x ((e s).symm (.inl b)))
    ((movingSamplePairCoordinates σ n).symm (fun i => x ((e s).symm (.inr (Quotient.mk'' i)))))
  have heq := movingOriginalPattern_sum_fin (e s) μ ν value n (fun i => Quotient.mk'' i) obs
  dsimp only [obs] at heq
  simp only [finite_univ_canonical] at heq ⊢
  unfold movingOriginalPatternWeight
  simp only [finite_univ_canonical] at heq ⊢
  refine Eq.trans ?_ heq
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr, mul_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternFrequencyModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pattern denominator satisfies the frequency-model requirements -/

namespace Ostmann
open scoped Classical

theorem prime_coprime_frequencyModelBase (S : Finset ℤ) (N p n : ℕ)
    (hp : p.Prime) (hpN : N < p) (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (t : FrequencyTree (S × S) n) : p.Coprime (frequencyModelBase S n t) := by
  have h (b : Bool) : p.Coprime (historyFrequencyProduct S n (frequencyPairProjection S n b t)) := by
    have hb := prime_coprime_historyFrequencyModulus S N p hp hpN hS n 0
      (frequencyPairProjection S n b t)
    exact Nat.Coprime.of_dvd_right (dvd_pow_self _ (by decide : (0 + 2 : ℕ) ≠ 0)) hb
  exact (h false).mul_right (h true)

theorem frequencyModelModulus_bound (S : Finset ℤ) (N n : ℕ)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) (t : FrequencyTree (S × S) n) :
    frequencyModelBase S n t ^ (n - 1 + 2) ≤
      N ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) := by
  exact (Nat.pow_le_pow_left (frequencyModelBase_le S n N t hN) _).trans_eq (pow_mul _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPriorRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prior support supplies the level and prime-separation hypotheses -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_internal_prior_nonzero {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    ∀ i, μ (movingSampleTier i.2) (x (e.symm (.inr (pattern i)))) ≠ 0 := by
  have hm : movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
      (fun i => x (e.symm (.inr (pattern i))))) ≠ 0 := by
    intro hz
    apply hx
    simp only [movingOriginalPatternWeight, hz, Complex.ofReal_zero, mul_zero, zero_mul]
  have hp := movingPairCompensatedMass_pattern μ prime n pattern
    (fun c => x (e.symm (.inr c)))
  change movingPairCompensatedMass μ prime ((movingSamplePairCoordinates A n).symm
    (fun i => x (e.symm (.inr (pattern i))))) = _ at hp
  rw [hp] at hm
  intro i
  exact (mul_ne_zero_iff.mp
    (Finset.prod_ne_zero_iff.mp hm i (Finset.mem_univ _))).2

/-- Incompatible level identifications have zero original weight. This
permits retaining all setoids in the exact expansion. -/
theorem movingPattern_tier_consistent_of_nonzero {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (hμ : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    ∀ i, movingSampleTier (rep (pattern i)).val.2 = movingSampleTier i.2 := by
  have hp := movingPattern_internal_prior_nonzero e μ ν prime pattern G x hx
  intro i
  have hi := hμ _ (movingSampleTier_lt i.2) _ (hp i)
  have hr := hμ _ (movingSampleTier_lt (rep (pattern i)).val.2) _ (hp (rep (pattern i)).val)
  rw [(rep (pattern i)).property] at hr
  exact hr.symm.trans hi

theorem movingPattern_zero_of_inconsistent_tiers {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (hμ : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hbad : ¬ ∀ i, movingSampleTier (rep (pattern i)).val.2 = movingSampleTier i.2)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A) :
    movingOriginalPatternWeight e μ ν prime n pattern G x = 0 := by
  by_contra hx
  exact hbad (movingPattern_tier_consistent_of_nonzero e μ ν prime pattern rep tier hμ G x hx)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Range separation and conductor deletion for the actual giant comparison -/

namespace Ostmann
open scoped Classical BigOperators

/-- Deleting the selected large conductor prime confines the actual Page
correction to the history-frequency modulus, including all its powers. -/
theorem frequencyModel_page_projection {I : Type*} [Fintype I]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (P : Finset ℕ) (p : I → ℕ) (z : Option PrimitiveRealZero)
    (hP : ∀ q ∈ P, q.Prime ∧ cutoff ≤ q) (hp : ∀ i, (p i).Prime ∧ cutoff ≤ p i)
    (hdeleteP : ∀ e, z = some e → ∀ q, deletedConductorPrime e.modulus cutoff = some q → q ∉ P)
    (hdeletep : ∀ e, z = some e → ∀ q, deletedConductorPrime e.modulus cutoff = some q → ∀ i, q ≠ p i) :
    pageAtModulus (∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p P Finset.univ b) z = pageAtModulus (frequencyModelBase S n t ^ (n - 1 + 2)) z := by
  let R := frequencyModelBase S n t ^ (n - 1 + 2)
  let C := (∏ q ∈ P, q) ^ 2 * ∏ i, p i
  have heq : (∏ b, movingArithmeticModuli R p P Finset.univ b) = R * C :=
    movingArithmeticModuli_product R p P Finset.univ
  change pageAtModulus (∏ b, movingArithmeticModuli R p P Finset.univ b) z = _
  rw [heq]
  apply pageAtModulus_mul_eq z R C cutoff
  · intro q hq hd
    by_contra hh
    have hVq : V < q := hcut.trans_le (Nat.le_of_not_lt hh)
    have hc := (prime_coprime_frequencyModelBase S V q n hq hVq hS t).pow_right (n - 1 + 2)
    exact (hq.coprime_iff_not_dvd.mp hc) hd
  · intro q hq hd
    rcases hq.dvd_mul.mp hd with hleft | hright
    · obtain ⟨a, ha, hqa⟩ := (hq.prime.dvd_finsetProd_iff (fun a : ℕ => a)).mp
        (hq.dvd_of_dvd_pow hleft)
      have he := (Nat.prime_dvd_prime_iff_eq hq (hP a ha).1).mp hqa
      simpa only [he] using (hP a ha).2
    · obtain ⟨i, _, hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hright
      have he := (Nat.prime_dvd_prime_iff_eq hq (hp i).1).mp hqi
      simpa only [he] using (hp i).2
  · intro e he q hq hd
    have hprime := (deletedConductorPrime_spec hq).1
    rcases hprime.dvd_mul.mp hd with hleft | hright
    · obtain ⟨a, ha, hqa⟩ := (hprime.prime.dvd_finsetProd_iff (fun a : ℕ => a)).mp
        (hprime.dvd_of_dvd_pow hleft)
      have heq := (Nat.prime_dvd_prime_iff_eq hprime (hP a ha).1).mp hqa
      exact hdeleteP e he q hq (heq.symm ▸ ha)
    · obtain ⟨i, _, hqi⟩ := (hprime.prime.dvd_finsetProd_iff p).mp hright
      exact hdeletep e he q hq i ((Nat.prime_dvd_prime_iff_eq hprime (hp i).1).mp hqi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularMultiplierIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal diagonal multiplier is the squared regular Fourier product -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRegularOther_eq_cofactor {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (slots : List σ) (j : Fin slots.length) :
    movingRegularOther value outside slots j =
      ((outside.prod * tupleCofactor (fun i => value (slots.get i)) j : ℕ) : ℤ) := by
  unfold movingRegularOther tupleCofactor
  congr 2
  apply Finset.prod_congr
  · ext i
    simp only [Finset.mem_erase, Finset.mem_univ]
  · intro i _
    rfl

theorem naturalRegularMultiplier_eq_transform_norm {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (active : I → Bool) (s : ℤ)
    (D : ℕ) (g : ∀ i, ZMod (p i) → ℂ) (XL XR : ℕ) :
    naturalRegularMultiplier p active s
      (fun i => ((D * tupleCofactor p i : ℕ) : ZMod (p i))) g XL XR =
      ‖movingRegularTransform p (fun i x => if active i then g i x else 1)
        (D * XL * XR) s‖ ^ 2 := by
  rw [movingRegularTransform, norm_prod, ← Finset.prod_pow]
  unfold naturalRegularMultiplier
  apply Finset.prod_congr rfl
  intro i _
  cases ha : active i
  · simp only [Bool.false_eq_true, ite_false, if_false, norm_one, one_pow]
  · simp only [ite_true, if_true]
    congr 2
    simp only [div_eq_mul_inv, Nat.cast_mul]
    congr 2
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotStateRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the original recursion in finite pattern coordinates -/

namespace Ostmann
open scoped Classical

@[simp] theorem MovingSlotState.leftProduct_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).leftProduct value = x.leftProduct (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.leftProduct, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.rightProduct_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).rightProduct value = x.rightProduct (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.rightProduct, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.compensation_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).compensation value = x.compensation (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.compensation, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.child_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (b : Bool) (x : MovingSlotState σ) (P : ℕ) :
    (x.map f).child value b P = (x.child (value ∘ f) b P).map f := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> cases b <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.child, MovingSlotReversal.naturalProduct_map, Bool.false_eq_true,
    ite_true, if_true, ite_false, if_false] <;> rfl

@[simp] theorem movingSlotSystem_leftState_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ) (P : ℕ) :
    (movingSlotSystem value childBound pivotBound).leftState (x.map f) P =
      ((movingSlotSystem (value ∘ f) childBound pivotBound).leftState x P).map f :=
  MovingSlotState.child_map f value true x P

@[simp] theorem movingSlotSystem_rightState_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ) (P : ℕ) :
    (movingSlotSystem value childBound pivotBound).rightState (x.map f) P =
      ((movingSlotSystem (value ∘ f) childBound pivotBound).rightState x P).map f :=
  MovingSlotState.child_map f value false x P

@[simp] theorem movingHistoryPivot_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ)
    (s v w : ℤ) :
    historyPivot (movingSlotSystem value childBound pivotBound) (x.map f) s v w =
      historyPivot (movingSlotSystem (value ∘ f) childBound pivotBound) x s v w := by
  simp only [historyPivot, movingSlotSystem, MovingSlotState.leftProduct_map,
    MovingSlotState.rightProduct_map]

theorem movingValidTransferNode_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ)
    (s v w : ℤ) (P : ℕ) :
    ValidTransferNode (movingSlotSystem value childBound pivotBound) (x.map f) s v w P ↔
      ValidTransferNode (movingSlotSystem (value ∘ f) childBound pivotBound) x s v w P := by
  constructor <;> intro h
  all_goals refine ⟨h.root_ne_zero, ?_, ?_, h.pivot_pos, h.pivot_bound,
    h.left_bound, h.right_bound, ?_, h.pivot_unit⟩
  all_goals first
    | simpa only [movingSlotSystem, MovingSlotState.rightProduct_map] using h.root_unit
    | simpa only [movingSlotSystem, MovingSlotState.leftProduct_map,
        MovingSlotState.rightProduct_map] using h.relation
    | simpa only [movingSlotSystem, MovingSlotState.rightProduct_map,
        MovingSlotState.map_depth] using h.range_gap

/-- A relabeling evaluates every original pivot and guard, including the
integer division by the sampled compensation product. -/
theorem movingRecursiveWeight_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (leaf : MovingSlotState τ → ℤ → ℂ)
    (cutoff : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (x : MovingSlotState σ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) leaf cutoff n (x.map f) t =
      recursiveTransferWeight (movingSlotSystem (value ∘ f) childBound pivotBound)
        (fun x => leaf (x.map f)) (fun x => cutoff (x.map f)) n x t := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [recursiveTransferWeight, movingHistoryPivot_map, movingValidTransferNode_map]
    split_ifs
    · simp only [movingSlotSystem_leftState_map, movingSlotSystem_rightState_map]
      rw [ih, ih]
    · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalWeightRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant weight commutes with evaluating pattern labels -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

@[simp] theorem movingSlotModulus_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    movingSlotModulus value (x.map f) = movingSlotModulus (value ∘ f) x := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map, movingSlotModulus,
    ← List.map_append, MovingSlotReversal.naturalProduct_map]

theorem movingSlotCutoff_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (extra : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound extra (x.map f) s v w =
      movingSlotCutoff (value ∘ f) childBound pivotBound
        (fun x => extra (x.map f)) x s v w := by
  simp only [movingSlotCutoff, MovingSlotState.compensation_map, movingHistoryPivot_map]

theorem movingPhiExtra_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (extra : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingPhiExtra value childBound pivotBound extra φ G (x.map f) s v w =
      movingPhiExtra (value ∘ f) childBound pivotBound
        (fun x => extra (x.map f)) φ G x s v w := by
  simp only [movingPhiExtra, MovingSlotState.map_depth, movingHistoryPivot_map,
    MovingSlotState.compensation_map]

theorem movingOriginalGiantWeight_map {σ τ I : Type*} (f : σ → τ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : τ → ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData τ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData τ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (XL XR : ℕ) :
    movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G
      (T.map f) t XL XR =
    movingOriginalGiantWeight q (value ∘ f) childBound pivotBound
      (fun T => F (T.map f)) (fun T => E (T.map f)) g Dq S ψ X lo hi φ G T t XL XR := by
  unfold movingOriginalGiantWeight
  change recursiveTransferWeight _ _ _ n
    ((⟨n, T, XL, XR⟩ : MovingSlotState σ).map f) t = _
  rw [movingRecursiveWeight_map]
  congr 1
  · funext x s
    simp only [movingWindowLeaf, movingDataLeaf, movingFourierLeaf,
      spectatorHistoryLeaf, movingSlotModulus_map, MovingSlotState.map_data]
    rfl
  · funext x s v w
    rw [movingSlotCutoff_map]
    congr 1
    funext y a b c
    rw [movingPhiExtra_map]
    rfl

theorem movingLocalGiantUnits_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) :
    movingLocalGiantUnits value outside (T.map f) XL XR ↔
      movingLocalGiantUnits (value ∘ f) outside T XL XR := by
  simp only [movingLocalGiantUnits, MovingSlotData.frequencyProduct_map,
    MovingSlotData.regularSlots_map, MovingSlotReversal.naturalProduct_map]

theorem MovingSlotReversal.naturalPivot_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (s : MovingSlotReversal σ) (XL XR : ℕ) :
    (s.map f).naturalPivot value XL XR = s.naturalPivot (value ∘ f) XL XR := by
  simp only [MovingSlotReversal.naturalPivot, MovingSlotReversal.map,
    MovingSlotReversal.naturalProduct_map]

theorem movingLocalSupport_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) (x : MovingSlotState σ) :
    movingLocalSupport value outside (x.map f) ↔
      movingLocalSupport (value ∘ f) outside x := by
  change (((x.data.map f).currentSlots value x.leftGiant x.rightGiant ++ outside).Pairwise Nat.Coprime ∧
      movingLocalGiantUnits value outside (x.data.map f) x.leftGiant x.rightGiant) ↔ _
  rw [MovingSlotData.currentSlots_map, movingLocalGiantUnits_map]
  rfl

theorem movingFullSupport_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    movingFullSupport value outside (T.map f) XL XR ↔
      movingFullSupport (value ∘ f) outside T XL XR := by
  induction T generalizing XL XR with
  | leaf s regular =>
    change movingLocalSupport value outside
      ((⟨0, .leaf s regular, XL, XR⟩ : MovingSlotState σ).map f) ↔ _
    exact movingLocalSupport_map f value outside _
  | node s CL CR u l r ihL ihR =>
    have hlocal := movingLocalSupport_map f value outside
      (⟨_, .node s CL CR u l r, XL, XR⟩ : MovingSlotState σ)
    change movingLocalSupport value outside
      ⟨_, .node s (CL.map f) (CR.map f) (u.map f) (l.map f) (r.map f), XL, XR⟩ ↔ _ at hlocal
    simp only [MovingSlotData.map, movingFullSupport_node, MovingSlotData.step_map,
      MovingSlotReversal.naturalPivot_map, ihL, ihR, hlocal]

theorem movingSupportedWeight_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (XL XR : ℕ) (z : ℂ) :
    movingSupportedWeight value outside (T.map f) XL XR z =
      movingSupportedWeight (value ∘ f) outside T XL XR z := by
  simp only [movingSupportedWeight, movingFullSupport_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPrimeRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pattern prime integral in the arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingPatternFinData_evaluate {σ B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → σ) (b : Bool) :
    (movingPatternFinData e n t small bulk pattern b).map x =
      buildMovingSlotData n (t b)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (small b))
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (bulk b))
        (movingPatternSamples σ n (fun i => x (e.symm (.inr (pattern i)))) b) := by
  rw [movingPatternFinData_build, buildMovingSlotData_map]
  simp only [movingPatternFiniteSmall, treeLeafMap_list_comp, movingPatternFiniteSamples,
    movingPatternSamples_map]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleDiagonalExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact sample expansion in the mixed prime/integer diagonal -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexIntegerInterval_sum {I : Type*} (q a : ℕ) (u v G : ℝ)
    (S : Finset I) (F : I → ℝ → ℂ) :
    complexIntegerInterval q a u v G (fun x => ∑ i ∈ S, F i x) =
      ∑ i ∈ S, complexIntegerInterval q a u v G (F i) := by
  unfold complexIntegerInterval
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem complexIntegerInterval_const_mul (q a : ℕ) (u v G : ℝ)
    (c : ℂ) (F : ℝ → ℂ) :
    complexIntegerInterval q a u v G (fun x => c * F x) =
      c * complexIntegerInterval q a u v G F := by
  unfold complexIntegerInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact mul_assoc _ _ _

/-- The outer factor may contain the full cutoff weight and the common
regular transform. It depends on the external draws, not the internal pair. -/
theorem movingCompensatedAverage_diagonal_patterns {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ)
    (H K : ℝ → ℝ → MovingSampleSlots A n → ℂ)
    (W : ℝ → ℝ → ℂ) (u v r s center : ℝ) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v center (fun x =>
      (movingCompensatedAverage μ value n (H x y) *
        star (movingCompensatedAverage μ value n (K x y))) * W x y)) =
    ∑ eqp : Setoid (Bool × MovingSampleIndex n),
      ∑ z : {z : Quotient eqp → A // Function.Injective z},
        let a := (movingSamplePairCoordinates A n).symm (fun i => z.val (Quotient.mk'' i))
        (internalPatternWeight (fun i => Quotient.mk'' i)
          (fun i => μ (movingSampleTier i.2)) value z.val : ℂ) *
          complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v center
            (fun x => (H x y a.1 * star (K x y a.2)) * W x y)) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  simp_rw [movingCompensatedAverage_pair_patterns, Finset.sum_mul,
    complexIntegerInterval_sum, complexPrimeInterval_sum]
  apply Finset.sum_congr rfl
  intro eqp _
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [mul_assoc, complexIntegerInterval_const_mul, complexPrimeInterval_const_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalDiagonalEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete original diagonal energy and its pattern expansion -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem frequencyRoot_movingRootedFrequencyTree (V : ℕ → ℕ) (n : ℕ)
    (s : ℤ) (a : MovingDescendantFrequencyIndex V n) :
    frequencyRoot n (movingRootedFrequencyTree V n s a) = s := by
  cases n <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedMatchedMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original matched-history mean and its exact equality patterns -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedMatchedMean_patterns {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    movingWeightedMatchedMean q value outside μ ν childBound pivotBound f g Dq S
      ψ X lo hi φ G n t small bulk W u v r w center =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → σ,
      movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
        (fun x => movingWeightedMatchedKernel q value outside childBound pivotBound f g Dq S
          ψ X lo hi φ G t small bulk W u v r w center
          (fun b => x ((e s).symm (.inl b)))
          ((movingSamplePairCoordinates σ n).symm
            (fun i => x ((e s).symm (.inr (Quotient.mk'' i)))))) x := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  let H := movingWeightedMatchedKernel q value outside childBound pivotBound f g Dq S
    ψ X lo hi φ G t small bulk W u v r w center
  have hpair (y : B → σ) :
      complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
        (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (t false) (treeLeafMap (List.map y) n small)
          (treeLeafMap (List.map y) n (bulk false)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (t true) (treeLeafMap (List.map y) n small)
          (treeLeafMap (List.map y) n (bulk true)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
        W y x z)) =
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ a : {a : Quotient s → σ // Function.Injective a},
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value a.val : ℂ) *
          H y ((movingSamplePairCoordinates σ n).symm (fun i => a.val (Quotient.mk'' i))) := by
    simp_rw [movingOriginalSampleAverage_compensated]
    exact movingCompensatedAverage_diagonal_patterns μ value n _ _ _ u v r w center
  unfold movingWeightedMatchedMean
  simp_rw [hpair]
  exact moving_external_pattern_mean μ ν value n H N e

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedMatchedCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original correlation of two matched bulk assignments -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedMatchedCorrelation_eq {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) :
    movingWeightedMatchedCorrelation q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n small bulk W u v r w center =
    ∑ s : transferFrequencyRange (V n), ∑ a : MovingDescendantFrequencyIndex V n,
      ∑ b : MovingDescendantFrequencyIndex V n,
        movingWeightedMatchedMean q value outside μ ν childBound pivotBound f g Dq S
          ψ X lo hi φ G n (fun side => if side then movingRootedFrequencyTree V n s.val b
            else movingRootedFrequencyTree V n s.val a)
          small bulk (W s.val) u v r w center := by
  unfold movingWeightedMatchedCorrelation
  apply Finset.sum_congr rfl
  intro s _
  have heq (y : B → σ) (x z : ℝ) :
      (movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk false))
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk true))
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) =
      ∑ a : MovingDescendantFrequencyIndex V n, ∑ b : MovingDescendantFrequencyIndex V n,
        movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (movingRootedFrequencyTree V n s.val a)
          (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk false))
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (movingRootedFrequencyTree V n s.val b)
          (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n (bulk true))
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) := by
    simp only [movingFrequencyCoefficient_original, star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [heq, Finset.sum_mul, complexIntegerInterval_sum, complexPrimeInterval_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  rfl

theorem movingWeightedMatchedMean_zero_frequency {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ)
    (side : Bool) (hzero : ¬ ∀ s ∈ allFrequencyList n (t side), s ≠ 0) :
    movingWeightedMatchedMean q value outside μ ν childBound pivotBound f g Dq S
      ψ X lo hi φ G n t small bulk W u v r w center = 0 := by
  have hz := movingOriginalSampleAverage_zero_frequency q value outside μ childBound pivotBound
    (fun _ => f) (fun _ _ => hf) g Dq S ψ X lo hi φ G n (t side)
  unfold movingWeightedMatchedMean
  cases side <;>
    simp_rw [hz _ _ _ _ hzero] <;>
    simp only [star_zero, zero_mul, mul_zero, complexPrimeInterval, complexIntegerInterval,
      Finset.sum_const_zero, ite_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompactLeaf
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact leaf multipliers preserve the scheduled statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingCompactLeaf_zero (V : ℕ) : movingCompactLeaf V 0 = 0 := by
  simp [movingCompactLeaf]

theorem movingCompactLeaf_norm (V : ℕ) (s : ℤ) :
    ‖movingCompactLeaf V s‖ ≤ if s.natAbs ≤ V then 1 else 0 := by
  unfold movingCompactLeaf
  split_ifs <;> simp

theorem movingOriginalLeaf_congr {σ I : Type*}
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (f h : ℤ → ℂ) (s : ℤ) (hs : f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (x : MovingSlotState σ) :
    movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi x s =
      movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi x s := by
  simp only [movingOriginalLeaf, movingWindowLeaf, movingDataLeaf, hs]

theorem movingFrequencyCoefficient_original_leaf_congr {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (f h : ℤ → ℂ) (hf : ∀ s, s.natAbs ≤ V 0 → f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s small bulk XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi) φ G n s small bulk XL XR := by
  apply movingFrequencyCoefficient_leaf_congr value outside μ childBound pivotBound V
    _ _ _ φ G n s hs small bulk XL XR
  intro x z hz
  exact movingOriginalLeaf_congr value q f h z (hf z hz) g Dq S ψ X lo hi x

theorem movingTemplateCoefficient_original_leaf_congr {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (f h : ℤ → ℂ) (hf : ∀ s, s.natAbs ≤ V 0 → f s = h s)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (s : ℤ) (hs : s.natAbs ≤ V n)
    (y : MovingRegularSlot n r m → σ) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n r m s y XL XR =
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => h) g Dq S ψ X lo hi) φ G n r m s y XL XR :=
  movingFrequencyCoefficient_original_leaf_congr value q outside μ childBound pivotBound V
    f h hf g Dq S ψ X lo hi φ G n s hs _ _ XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting only the selected bulk coordinates in the original law -/

namespace Ostmann
open scoped Classical BigOperators

theorem selectedBulkSample_mul {B J A : Type*} (slot : J ↪ B)
    (e f : Equiv.Perm J) (y : B → A) :
    selectedBulkSample slot (e * f) y = selectedBulkSample slot e (selectedBulkSample slot f y) := by
  simp only [selectedBulkSample, selectedBulkPerm_mul]
  rfl

/-- Only the selected coordinates need identical distributions. -/
theorem selectedBulkSample_prior {B J A : Type*} [Fintype B]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k)) (y : B → A) :
    (∏ i, ν i (selectedBulkSample slot e y i)) = ∏ i, ν i (y i) := by
  have hpres (i : B) : ν i = ν ((selectedBulkPerm slot e).symm i) := by
    obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
    cases j with
    | inl j => simpa using hν j (e.symm j)
    | inr i => simp [i.property]
  calc
    _ = ∏ i, ν ((selectedBulkPerm slot e).symm i)
        (y ((selectedBulkPerm slot e).symm i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [hpres i]
      rfl
    _ = _ := (selectedBulkPerm slot e).symm.prod_comp (fun i => ν i (y i))

theorem selectedBulkSample_sum {B J A : Type*} [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k)) (F : (B → A) → ℂ) :
    (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * F (selectedBulkSample slot e y)) =
      ∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * F y := by
  have h := (bulkArrayEquiv (A := A) (selectedBulkPerm slot e)).sum_comp
    (fun y => ((∏ i, ν i (y i) : ℝ) : ℂ) * F y)
  change (∑ y, ((∏ i, ν i (selectedBulkSample slot e y i) : ℝ) : ℂ) *
    F (selectedBulkSample slot e y)) = _ at h
  simpa only [selectedBulkSample_prior slot e ν hν] using h

theorem selectedBulkSample_bulk_leaves {B A : Type*} (n m : ℕ)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → A) :
    treeLeafMap (List.map (selectedBulkSample slot e y)) n (bulkSlotLeaves n m slot) =
      treeLeafMap (List.map y) n (bulkSlotLeaves n m (slot ∘ e.symm)) := by
  simp only [bulkSlotLeaves_map]
  congr 1
  funext j
  exact selectedBulkSample_bulk slot e y j

theorem treeLeafMap_congr_on_slots {B A : Type*} (n : ℕ)
    (small : TreeLeafTuple (List B) n) (x y : B → A)
    (h : ∀ i ∈ flattenMovingSlots n small, x i = y i) :
    treeLeafMap (List.map x) n small = treeLeafMap (List.map y) n small := by
  induction n with
  | zero => exact List.map_congr_left h
  | succ n ih =>
    apply Prod.ext
    · exact ih small.1 (fun i hi => h i (List.mem_append_left _ hi))
    · exact ih small.2 (fun i hi => h i (List.mem_append_right _ hi))

theorem selectedBulkSample_small_leaves {B J A : Type*} (n : ℕ)
    (small : TreeLeafTuple (List B) n) (slot : J ↪ B) (e : Equiv.Perm J) (y : B → A)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    treeLeafMap (List.map (selectedBulkSample slot e y)) n small =
      treeLeafMap (List.map y) n small :=
  treeLeafMap_congr_on_slots n small _ _ (fun i hi => selectedBulkSample_nonbulk slot e y i (hsmall i hi))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original root, prime and integer average as one finite positive law -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalPrior_nonneg {B A : Type*} [Fintype B]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ) (x : MixedExternalPoint B A N u v r w) :
    0 ≤ mixedExternalPrior ν N u v r w center x := by
  unfold mixedExternalPrior
  apply mul_nonneg
  · exact mul_nonneg (Finset.prod_nonneg fun b _ => hν b _) (by split_ifs <;> positivity)
  · exact integerResidueAtom_nonneg 1 0 center _

theorem mixedExternalAverage_finite {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center F =
      ∑ x : MixedExternalPoint B A N u v r w,
        (mixedExternalPrior ν N u v r w center x : ℂ) *
          F x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val) := by
  have hp (F : ℝ → ℂ) : complexPrimeInterval 1 0 r w F =
      ∑ p : Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp w⌋₊,
        if (p.val).Prime then F (Real.log p.val) * ((p.val : ℝ)⁻¹ : ℂ) else 0 := by
    rw [Finset.sum_coe_sort _ (fun p : ℕ =>
      if p.Prime then F (Real.log p) * ((p : ℝ)⁻¹ : ℂ) else 0)]
    simp only [complexPrimeInterval, Nat.modEq_one, and_true]
  have hi (F : ℝ → ℂ) : complexIntegerInterval 1 0 u v center F =
      ∑ q : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        F (Real.log q.val) * (integerResidueAtom 1 0 center q.val : ℂ) := by
    rw [Finset.sum_coe_sort _ (fun q : ℕ =>
      F (Real.log q) * (integerResidueAtom 1 0 center q : ℂ))]
    rfl
  simp only [mixedExternalAverage, hp, hi, MixedExternalPoint,
    Fintype.sum_prod_type, mixedExternalPrior]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hprime : (p.val).Prime
  · simp only [hprime, ite_true, if_true, Complex.ofReal_mul]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    push_cast
    ring
  · simp only [hprime, ite_false, if_false, mul_zero, zero_mul, Complex.ofReal_zero,
      Finset.sum_const_zero]

theorem mixedExternalAverage_star {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center (fun s y x z => star (F s y x z)) =
      star (mixedExternalAverage ν N u v r w center F) := by
  simp [mixedExternalAverage_finite]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalBulkAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original coefficient and common transform under bulk reassignment -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFrequencyCoefficient_bulk_action {σ B : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n m : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → σ) (XL XR : ℕ)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (treeLeafMap (List.map (selectedBulkSample slot e y)) n small)
      (treeLeafMap (List.map (selectedBulkSample slot e y)) n (bulkSlotLeaves n m slot)) XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (treeLeafMap (List.map y) n small)
      (treeLeafMap (List.map y) n (bulkSlotLeaves n m (slot ∘ e.symm))) XL XR := by
  rw [selectedBulkSample_small_leaves n small slot e y hsmall,
    selectedBulkSample_bulk_leaves]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the original mixed external law by its selected bulk coordinates -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_selectedBulkSample {B J A : Type*}
    [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ) (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z => F s (selectedBulkSample slot e y) x z) =
    mixedExternalAverage ν N u v r w center F := by
  unfold mixedExternalAverage
  apply Finset.sum_congr rfl
  intro s _
  exact selectedBulkSample_sum slot e ν hν
    (fun y => complexPrimeInterval 1 0 r w (fun z =>
      complexIntegerInterval 1 0 u v center (fun x => F s.val y x z)))

theorem mixedExternalAverage_relative_pair {B J A : Type*}
    [Fintype B] [Fintype A]
    (slot : J ↪ B) (e f : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hW : ∀ e s y x z, W s (selectedBulkSample slot e y) x z = W s y x z) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z =>
        (F s (selectedBulkSample slot e y) x z *
          star (F s (selectedBulkSample slot f y) x z)) * W s y x z) =
    mixedExternalAverage ν N u v r w center
      (fun s y x z =>
        (F s y x z * star (F s (selectedBulkSample slot (f * e⁻¹) y) x z)) * W s y x z) := by
  rw [← mixedExternalAverage_selectedBulkSample slot e⁻¹ ν hν]
  congr 1
  funext s y x z
  rw [hW, ← selectedBulkSample_mul, ← selectedBulkSample_mul]
  simp only [mul_inv_cancel, selectedBulkSample_one]

theorem mixedExternalAverage_pair_swap {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (F s y x z * star (H s y x z)) * W s y x z)‖ =
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (H s y x z * star (F s y x z)) * W s y x z)‖ := by
  conv_lhs => rw [← norm_star]
  rw [← mixedExternalAverage_star]
  congr 2
  funext s y x z
  simp [mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalGram
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive Gram estimates in the original mixed external measure -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_weighted_correlation_bound {B A : Type*}
    [Fintype B] [Fintype A] (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ s y x z, 0 ≤ W s y x z) (E : ℝ)
    (hF : (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤ E)
    (hH : (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖H s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤ E) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (F s y x z * star (H s y x z)) * W s y x z)‖ ≤ E := by
  let ρ := mixedExternalPrior ν N u v r w center
  let f := fun x : MixedExternalPoint B A N u v r w =>
    F x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  let h := fun x : MixedExternalPoint B A N u v r w =>
    H x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  let vW := fun x : MixedExternalPoint B A N u v r w =>
    W x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  have hρ (x) : 0 ≤ ρ x := mixedExternalPrior_nonneg ν hν N u v r w center x
  have hW' (x) : 0 ≤ vW x := hW _ _ _ _
  have hF' : (∑ x, ρ x * (‖f x‖ ^ 2 * vW x)) ≤ E := by
    simpa only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero] using hF
  have hH' : (∑ x, ρ x * (‖h x‖ ^ 2 * vW x)) ≤ E := by
    simpa only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero] using hH
  rw [mixedExternalAverage_finite]
  calc
    _ ≤ ∑ x, ρ x * (‖f x‖ * ‖h x‖ * vW x) := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro x _
      change ‖(ρ x : ℂ) * ((f x * star (h x)) * (vW x : ℂ))‖ = _
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (hρ x),
        Real.norm_of_nonneg (hW' x)]
    _ ≤ (∑ x, (ρ x * (‖f x‖ ^ 2 * vW x) +
        ρ x * (‖h x‖ ^ 2 * vW x))) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro x _
      have ha : ‖f x‖ * ‖h x‖ ≤ (‖f x‖ ^ 2 + ‖h x‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖f x‖ - ‖h x‖)]
      have hb := mul_le_mul_of_nonneg_left ha (mul_nonneg (hρ x) (hW' x))
      nlinarith
    _ ≤ E := by rw [Finset.sum_add_distrib]; linarith

theorem mixedExternalAverage_family_bound {B A J : Type*}
    [Fintype B] [Fintype A] [Group J] [Fintype J]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : J → ℤ → (B → A) → ℝ → ℝ → ℂ)
    (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (bad : J → Prop) (D E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ i j, ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (F i s y x z * star (F j s y x z)) * W s y x z)‖ ≤
        if bad (i⁻¹ * j) then D else E) :
    (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖finiteFamilyAverage (fun j _ => F j s y x z) ()‖ ^ 2 : ℂ) *
        W s y x z)).re ≤
      (Fintype.card {j : J // bad j} : ℝ) / Fintype.card J * D + E := by
  let ρ := fun x : MixedExternalPoint B A N u v r w =>
    mixedExternalPrior ν N u v r w center x *
      W x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  let f := fun j (x : MixedExternalPoint B A N u v r w) =>
    F j x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  have hp (i j : J) : ‖∑ x, (ρ x : ℂ) * (f i x * star (f j x))‖ ≤
      if bad (i⁻¹ * j) then D else E := by
    convert hpair i j using 1
    all_goals try with_reducible_and_instances rfl
    rw [mixedExternalAverage_finite]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    dsimp [ρ, f]
    push_cast
    ring
  have h := finiteFamilyAverage_good_bad_bound ρ f bad D E hE hp
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [ρ, f, finiteFamilyAverage]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeArrangementFraction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bad-arrangement fractions on the actual recursive leaf index -/

namespace Ostmann
open scoped Classical

theorem badTreeArrangement_fraction_bound (n m : ℕ) (hm : 1 ≤ m) :
    (Fintype.card {e : Equiv.Perm (TreeLeafIndex n × Fin m) // BadTreeArrangement e} : ℝ) /
        (Fintype.card (Equiv.Perm (TreeLeafIndex n × Fin m)) : ℝ) ≤
      ((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) := by
  let f : TreeLeafIndex n ≃ Fin (2 ^ n) :=
    (Fintype.equivFin _).trans (finCongr (card_treeLeafIndex n))
  let E := (f.prodCongr (Equiv.refl (Fin m))).permCongr
  have hbad (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
      BadTreeArrangement e ↔ BadBulkArrangement (E e) := by
    change _ ↔ 3 * 2 ^ n < 4 * Fintype.card (arrangementGraph m (reindexArrangement f e)).ConnectedComponent
    rw [arrangement_component_count_reindex]
    simp only [BadTreeArrangement, card_treeLeafIndex]
  have he := E.subtypeEquiv hbad
  rw [Fintype.card_congr he, Fintype.card_congr E, card_bulkPerm]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    badBulkArrangement_fraction_bound (r := 2 ^ n) (pow_pos (by decide : 0 < (2 : ℕ)) n) hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedBulkSymmetrization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetrization of the original mixed law, with bad pairs paid by energy -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_weighted_square_permute {B J A : Type*}
    [Fintype B] [Fintype A]
    (slot : J ↪ B) (e : Equiv.Perm J) (ν : B → A → ℝ)
    (hν : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ e s y x z, W s (selectedBulkSample slot e y) x z = W s y x z) :
    mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖F s (selectedBulkSample slot e y) x z‖ ^ 2 : ℂ) * W s y x z) =
    mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z) := by
  have h := mixedExternalAverage_selectedBulkSample slot e ν hν N u v r w center
    (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)
  simpa only [hW] using h

/-- The ordinary diagonal energy controls every bad pair. Only good relative
permutations use the signed arithmetic correlation estimate. -/
theorem mixedBulkSymmetrize_energy_bound {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (hm : 1 ≤ m) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ s y x z, 0 ≤ W s y x z)
    (hinv : ∀ e s y x z, W s (selectedBulkSample slot e y) x z = W s y x z)
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤ D)
    (hgood : ∀ e : Equiv.Perm (TreeLeafIndex n × Fin m),
      4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex n) →
      ‖mixedExternalAverage ν N u v r w center
        (fun s y x z => (F s y x z * star (F s (selectedBulkSample slot e y) x z)) *
          W s y x z)‖ ≤ E) :
    (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) * D + E := by
  have hall (e : Equiv.Perm (TreeLeafIndex n × Fin m)) :
      ‖mixedExternalAverage ν N u v r w center
        (fun s y x z => (F s y x z * star (F s (selectedBulkSample slot e y) x z)) *
          W s y x z)‖ ≤ D := by
    apply mixedExternalAverage_weighted_correlation_bound ν hν N u v r w center
      F (fun s y x z => F s (selectedBulkSample slot e y) x z) W hW D hdiag
    rw [mixedExternalAverage_weighted_square_permute slot e ν hidentical N u v r w center F W hinv]
    exact hdiag
  have hpair (e f : Equiv.Perm (TreeLeafIndex n × Fin m)) :
      ‖mixedExternalAverage ν N u v r w center
        (fun s y x z =>
          (F s (selectedBulkSample slot e⁻¹ y) x z *
            star (F s (selectedBulkSample slot f⁻¹ y) x z)) * W s y x z)‖ ≤
        if BadTreeArrangement (e⁻¹ * f) then D else E := by
    rw [mixedExternalAverage_pair_swap]
    rw [mixedExternalAverage_relative_pair slot f⁻¹ e⁻¹ ν hidentical N u v r w center F
      (fun s y x z => (W s y x z : ℂ)) (fun e s y x z => congrArg Complex.ofReal (hinv e s y x z))]
    simp only [inv_inv]
    split_ifs with hbad
    · exact hall _
    · exact hgood _ (by simpa only [BadTreeArrangement, not_lt] using hbad)
  have hb := mixedExternalAverage_family_bound ν N u v r w center
    (fun e s y x z => F s (selectedBulkSample slot e⁻¹ y) x z) W
    BadTreeArrangement D E hE hpair
  apply hb.trans
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_right (badTreeArrangement_fraction_bound n m hm) hD

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary total-mass bounds for the original mixed external law -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_re_nonneg {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hF : ∀ s y x z, 0 ≤ (F s y x z).re) :
    0 ≤ (mixedExternalAverage ν N u v r w center F).re := by
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg
    (mixedExternalPrior_nonneg ν hν N u v r w center x) (hF _ _ _ _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the original pivot, compensation, and surviving slots -/

namespace Ostmann
open scoped Classical BigOperators

/-- Reindexing changes neither the cofactor nor its local transform. -/
theorem movingRegularTransform_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) [∀ j, NeZero (p j)]
    (g : ∀ j, ZMod (p j) → ℂ) (D : ℕ) (s : ℤ) :
    let _ : ∀ i, NeZero (p (e i)) := fun _i => inferInstance
    movingRegularTransform (fun i => p (e i)) (fun i => g (e i)) D s =
      movingRegularTransform p g D s := by
  dsimp only
  unfold movingRegularTransform
  simp_rw [tupleCofactor_equiv e p (fun j => NeZero.ne (p j))]
  exact e.prod_comp (fun j => g j ((s : ZMod (p j)) *
    ((D * tupleCofactor p j : ℕ) : ZMod (p j))⁻¹))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingMaskedMultiplierReindex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the complete masked cofactor multiplier -/

namespace Ostmann
open scoped Classical BigOperators

theorem naturalRegularMultiplier_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, (p j).Prime) (active : J → Bool)
    (g : ∀ q : ℕ, ZMod q → ℂ) (D XL XR : ℕ) (s : ℤ) :
    let _ : ∀ j, Fact (p j).Prime := fun j => ⟨hp j⟩
    let _ : ∀ i, Fact (p (e i)).Prime := fun i => ⟨hp (e i)⟩
    naturalRegularMultiplier (fun i => p (e i)) (fun i => active (e i)) s
      (fun i => ((D * tupleCofactor (fun j => p (e j)) i : ℕ) : ZMod (p (e i))))
      (fun i => g (p (e i))) XL XR =
    naturalRegularMultiplier p active s
      (fun i => ((D * tupleCofactor p i : ℕ) : ZMod (p i)))
      (fun i => g (p i)) XL XR := by
  dsimp only
  let _ : ∀ j, Fact (p j).Prime := fun j => ⟨hp j⟩
  let _ : ∀ i, Fact (p (e i)).Prime := fun i => ⟨hp (e i)⟩
  rw [naturalRegularMultiplier_eq_transform_norm, naturalRegularMultiplier_eq_transform_norm]
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
    (movingRegularTransform_equiv e p (fun j z => if active j then g (p j) z else 1)
      (D * XL * XR) s)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternTemplateEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying arithmetic pattern slots with the full regular template -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternTemplateEquiv_label {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C)
    (i : Fin (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).length) :
    (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).get i = e.symm (.inl (movingPatternTemplateEquiv n r m e i)) := by
  simp only [movingPatternTemplateEquiv, Equiv.trans_apply, movingTemplateListEquiv_apply,
    List.get_eq_getElem, movingPatternTemplateSlots_eq, List.getElem_map, finCongr_apply,
    Fin.val_cast]

/-- The inactive-slot condition used by the arithmetic theorem follows from
activity of the actual bulk slots. -/
theorem movingPatternTemplate_inactive_not_bulk {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C)
    (active : MovingRegularSlot n r m → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n r m j) = true)
    (i : Fin (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).length)
    (hi : active (movingPatternTemplateEquiv n r m e i) = false) :
    (movingPatternRegularSlots e n m (movingTemplateSmall n r m)
      (movingTemplateBulk n r m)).get i ∉
      Set.range (movingPatternBulkEmbedding e (movingTemplateBulk n r m)) := by
  rintro ⟨j, hj⟩
  rw [movingPatternTemplateEquiv_label] at hj
  have he : movingTemplateBulk n r m j = movingPatternTemplateEquiv n r m e i := by
    apply Sum.inl.inj
    apply e.symm.injective
    exact hj
  rw [← he, hactive j] at hi
  cases hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePatternMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact masked multiplier in the finite arithmetic pattern -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplate_pattern_multiplier {C : Type*} {N : ℕ} (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C)
    (value : Fin (N + 1) → ℕ) (hprime : ∀ i, (value i).Prime)
    (active : MovingRegularSlot n r m → Bool) (outside : List ℕ)
    (g : ∀ q : ℕ, ZMod q → ℂ) (XL XR : ℕ) (s : ℤ) :
    let L := movingPatternRegularSlots e n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)
    let p := fun i : Fin L.length => value (L.get i)
    let q := fun i => value (e.symm (.inl i))
    let _ : ∀ i, Fact (p i).Prime := fun _ => ⟨hprime _⟩
    let _ : ∀ i, Fact (q i).Prime := fun _ => ⟨hprime _⟩
    naturalRegularMultiplier p (fun i => active (movingPatternTemplateEquiv n r m e i)) s
      (fun i => (movingRegularOther value outside L i : ZMod (p i)))
      (fun i => g (p i)) XL XR =
    naturalRegularMultiplier q active s
      (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
      (fun i => g (q i)) XL XR := by
  intro L p q ip iq
  simp only [movingRegularOther_eq_cofactor, Int.cast_natCast]
  let E := movingPatternTemplateEquiv n r m e
  have hp : p = fun i => q (E i) := by
    funext i
    exact congrArg value (movingPatternTemplateEquiv_label n r m e i)
  let M (v : Fin L.length → ℕ) : ℝ :=
    ∏ i, if active (E i) then
      ‖g (v i) ((s : ZMod (v i)) *
        (((outside.prod * tupleCofactor v i : ℕ) : ZMod (v i)) *
          (XL : ZMod (v i)) * (XR : ZMod (v i)))⁻¹)‖ ^ 2 else 1
  simp only [naturalRegularMultiplier, div_eq_mul_inv]
  change M p = _
  rw [hp]
  have h := naturalRegularMultiplier_equiv E q (fun i => hprime _) active g outside.prod XL XR s
  simpa only [naturalRegularMultiplier, div_eq_mul_inv, M] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedDiagonalMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equality patterns with a retained external Fourier multiplier -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedDiagonalMean_patterns {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (W : (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    movingWeightedDiagonalMean q value outside μ ν childBound pivotBound f g Dq S
      ψ X lo hi φ G n t small bulk W u v r w center =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → σ,
      movingOriginalPatternWeight (e s) μ ν value n (fun i => Quotient.mk'' i)
        (fun x => movingWeightedDiagonalKernel q value outside childBound pivotBound f g Dq S
          ψ X lo hi φ G t small bulk W u v r w center
          (fun b => x ((e s).symm (.inl b)))
          ((movingSamplePairCoordinates σ n).symm
            (fun i => x ((e s).symm (.inr (Quotient.mk'' i)))))) x := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  let H := movingWeightedDiagonalKernel q value outside childBound pivotBound f g Dq S
    ψ X lo hi φ G t small bulk W u v r w center
  have hpair (y : B → σ) :
      complexPrimeInterval 1 0 r w (fun z => complexIntegerInterval 1 0 u v center (fun x =>
        (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (t false) (treeLeafMap (List.map y) n small)
          (treeLeafMap (List.map y) n bulk) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (t true) (treeLeafMap (List.map y) n small)
          (treeLeafMap (List.map y) n bulk) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
        W y x z)) =
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ a : {a : Quotient s → σ // Function.Injective a},
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value a.val : ℂ) *
          H y ((movingSamplePairCoordinates σ n).symm (fun i => a.val (Quotient.mk'' i))) := by
    simp_rw [movingOriginalSampleAverage_compensated]
    exact movingCompensatedAverage_diagonal_patterns μ value n _ _ _ u v r w center
  unfold movingWeightedDiagonalMean
  simp_rw [hpair]
  exact moving_external_pattern_mean μ ν value n H N e

theorem movingWeightedDiagonalMean_zero_frequency {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (W : (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ)
    (side : Bool) (hzero : ¬ ∀ s ∈ allFrequencyList n (t side), s ≠ 0) :
    movingWeightedDiagonalMean q value outside μ ν childBound pivotBound f g Dq S
      ψ X lo hi φ G n t small bulk W u v r w center = 0 := by
  have hz := movingOriginalSampleAverage_zero_frequency q value outside μ childBound pivotBound
    (fun _ => f) (fun _ _ => hf) g Dq S ψ X lo hi φ G n (t side)
  unfold movingWeightedDiagonalMean
  cases side <;>
    simp_rw [hz _ _ _ _ hzero] <;>
    simp only [star_zero, zero_mul, mul_zero, complexPrimeInterval, complexIntegerInterval,
      Finset.sum_const_zero, ite_self]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedDiagonalRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relabeling the retained exterior multiplier into arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedDiagonalKernel_fin {B C J : Type*} [Fintype J] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (pattern : Bool × MovingSampleIndex n → C)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (reg : J → Fin (N + 1)) (active : J → Bool)
    (other : (Fin (N + 1) → primes) → J → ℤ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (W : (B → primes) → ℝ → ℝ → ℂ)
    (x : Fin (N + 1) → primes)
    (hW : ∀ z y, W (fun j => x (e.symm (.inl j))) z y =
      movingPatternExternalMultiplier primes hprimes reg active other greg sreg φ
        Jleft Jright diagonal x z y) :
    movingWeightedDiagonalKernel p (fun q : primes => (q : ℕ)) outside
      childBound pivotBound f g Dq Finset.univ ψ X lo hi φ G t small
      (bulkSlotLeaves n m slot) W u v a b center
      (fun j => x (e.symm (.inl j)))
      ((movingSamplePairCoordinates primes n).symm
        (fun i => x (e.symm (.inr (pattern i))))) =
    movingOriginalPatternDiagonalObservable e t small slot pattern primes hprimes p g Dq
      reg active sreg other greg f outside childBound pivotBound
      ψ X lo hi φ G Jleft Jright diagonal u v a b center x := by
  have heval (side : Bool) :
      (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern side).map x =
      buildMovingSlotData n (t side)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (bulkSlotLeaves n m slot))
        (movingPatternSamples primes n (fun i => x (e.symm (.inr (pattern i)))) side) := by
    have hbulk : movingPatternBulkLeaves n m slot (Equiv.refl _) =
        fun _ => bulkSlotLeaves n m slot := by
      funext b
      cases b <;> rfl
    rw [movingPatternFinBulkData, hbulk]
    exact movingPatternFinData_evaluate e t (fun _ => small)
      (fun _ => bulkSlotLeaves n m slot) pattern x side
  have hterm (side : Bool) (XL XR : ℕ) :
      let T := buildMovingSlotData n (t side)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (bulkSlotLeaves n m slot))
        (movingPatternSamples primes n (fun i => x (e.symm (.inr (pattern i)))) side)
      movingSupportedWeight (fun q : primes => (q : ℕ)) outside T XL XR
        (movingOriginalGiantWeight p (fun q : primes => (q : ℕ)) childBound pivotBound
          (fun _ => f) (fun _ _ _ _ => 1) g Dq Finset.univ ψ X lo hi φ G T (t side) XL XR) =
      movingSupportedWeight (fun i => (x i : ℕ)) outside
        (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern side) XL XR
        (movingOriginalGiantWeight p (fun i => (x i : ℕ)) childBound pivotBound
          (fun _ => f) (fun _ _ _ _ => 1) g Dq Finset.univ ψ X lo hi φ G
          (movingPatternFinBulkData e n m t (fun _ => small) slot (Equiv.refl _) pattern side)
          (t side) XL XR) := by
    dsimp only
    rw [← heval side, movingOriginalGiantWeight_map, movingSupportedWeight_map]
    rfl
  unfold movingOriginalPatternDiagonalObservable
  unfold movingWeightedDiagonalKernel
  dsimp only
  rw [← movingPatternSamples_pair]
  dsimp only
  apply congrArg (complexPrimeInterval 1 0 a b)
  funext y
  apply congrArg (complexIntegerInterval 1 0 u v center)
  funext z
  simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  rw [hterm false, hterm true]
  rw [hW z y]
  unfold movingPatternExternalMultiplier movingOriginalSupportedOuterPair
  dsimp only
  exact (mul_assoc _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateExternalMultiplier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original exterior multiplier in template and pattern coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateExternalMultiplier_pattern {C : Type*} {N : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (e : Fin (N + 1) ≃ MovingRegularSlot n r m ⊕ C)
    (active : MovingRegularSlot n r m → Bool) (outside : List ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool)
    (x : Fin (N + 1) → P) (z y : ℝ) :
    movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal
      (fun i => x (e.symm (.inl i))) z y =
    movingPatternExternalMultiplier P hP
      (movingPatternRegularSlots e n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)).get
      (fun i => active (movingPatternTemplateEquiv n r m e i))
      (fun x => movingRegularOther (fun j => (x j : ℕ)) outside
        (movingPatternRegularSlots e n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)))
      greg s φ Jleft Jright diagonal x z y := by
  have h := movingTemplate_pattern_multiplier n r m e (fun i => (x i : ℕ))
    (fun i => hP _ (x i).property) active outside greg ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s
  unfold movingTemplateExternalMultiplier movingPatternExternalMultiplier
  dsimp only
  exact congrArg (fun a : ℝ =>
    (giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ) * a) h.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCompactEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency truncation preserves the actual unsymmetrized energy -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem mixedExternalAverage_frequency_congr {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ s, s.natAbs ≤ N → ∀ y x z, F s y x z = H s y x z) :
    mixedExternalAverage ν N u v r w center F =
      mixedExternalAverage ν N u v r w center H := by
  rw [mixedExternalAverage_finite, mixedExternalAverage_finite]
  apply Finset.sum_congr rfl
  intro x _
  rw [h x.1.val ((mem_transferFrequencyRange _ _).mp x.1.property)]

theorem movingTemplate_compact_energy {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (law : MovingRegularSlot n r m → σ → ℝ)
    (W : ℤ → (MovingRegularSlot n r m → σ) → ℝ → ℝ → ℂ)
    (u v a b center : ℝ) :
    mixedExternalAverage law (V n) u v a b center (fun s y x z =>
      (‖movingTemplateCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1)
          g Dq S ψ X lo hi) φ G n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) * W s y x z) =
    mixedExternalAverage law (V n) u v a b center (fun s y x z =>
      (‖movingTemplateCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => movingCompactLeaf (V 0))
          g Dq S ψ X lo hi) φ G n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) * W s y x z) := by
  apply mixedExternalAverage_frequency_congr
  intro s hs y x z
  rw [movingTemplateCoefficient_original_leaf_congr value q outside μ childBound pivotBound V
    (fun s => if s = 0 then 0 else 1) (movingCompactLeaf (V 0))
    (fun s hs => by simp only [movingCompactLeaf, hs, ite_true, if_true])
    g Dq S ψ X lo hi φ G n r m s hs]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyModelPage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bulk Page projection for the actual frequency model -/

namespace Ostmann
open scoped Classical BigOperators

theorem frequencyModel_bulk_page_projection {I : Type*} [Fintype I]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (p : I → ℕ) (z : Option PrimitiveRealZero)
    (hp : ∀ i, (p i).Prime ∧ cutoff ≤ p i)
    (hdelete : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → ∀ i, q ≠ p i) :
    pageAtModulus (∏ i, bulkResidueModuli (frequencyModelBase S n t ^ (n - 1 + 2)) p i) z =
      pageAtModulus (frequencyModelBase S n t ^ (n - 1 + 2)) z := by
  have h := frequencyModel_page_projection S n V cutoff t hS hcut ∅ p z
    (by simp) hp (by simp) hdelete
  rw [movingArithmeticModuli_product] at h
  simpa only [Fintype.prod_sum_type, bulkResidueModuli, Fintype.prod_unique,
    Finset.prod_empty, one_pow, one_mul, mul_one] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternGiantBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete logarithmic bounds for the original giant comparison -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The frequency modulus used by the actual pair of histories has a fixed
polynomial degree in the frequency cutoff. -/
theorem frequencyModelModulus_exp_bound (S : Finset ℤ) (N n : ℕ)
    (t : FrequencyTree (S × S) n) (A : ℝ)
    (hN : ∀ s ∈ S, s.natAbs ≤ N) (hA : (N : ℝ) ≤ Real.exp A) :
    ((frequencyModelBase S n t ^ (n - 1 + 2) : ℕ) : ℝ) ≤
      Real.exp ((2 * (2 ^ (n + 1) - 1) * (n - 1 + 2) : ℕ) * A) := by
  calc
    _ ≤ (N : ℝ) ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) := by
      exact_mod_cast frequencyModelModulus_bound S N n hN t
    _ ≤ (Real.exp A) ^ (2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)) :=
      pow_le_pow_left₀ (Nat.cast_nonneg N) hA _
    _ = _ := (Real.exp_nat_mul _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyModelRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete frequency-model modulus in the bulk progression range -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem movingFrequencyModel_bulk_range (n k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (S : Finset ℤ) (N : ℕ) (t : FrequencyTree (S × S) n) (p : Fin m → ℕ),
      (∀ s ∈ S, s ≠ 0) → (∀ s ∈ S, s.natAbs ≤ N) →
      (N : ℝ) ≤ Real.exp (A * m) →
      (∀ i, (p i).Prime) → Function.Injective p → (∀ i, N < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      let r := frequencyModelBase S n t ^ (n - 1 + 2)
      let M := ∏ i, bulkResidueModuli r p i
      0 < r ∧ 0 < M ∧
      Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)) ∧
      M ≤ bulkProgressionCutoff L := by
  let d : ℕ := 2 * (2 ^ (n + 1) - 1) * (n - 1 + 2)
  filter_upwards [bulkResidueModulus_progression_range ((d : ℝ) * A) ((k : ℝ) ^ 4)
    (by positivity) (by positivity), eventually_ge_atTop (0 : ℝ)] with L hL hL0
  dsimp only
  intro S N t p hS hN hbound hp hinj hNp hupper
  let r := frequencyModelBase S n t ^ (n - 1 + 2)
  have hr : 0 < r := pow_pos (frequencyModelBase_pos S n t hS) _
  have hrbound : (r : ℝ) ≤ Real.exp (((d : ℝ) * A) * spectatorBulkCount k L) := by
    simpa only [d, r, mul_assoc] using frequencyModelModulus_exp_bound S N n t
      (A * spectatorBulkCount k L) hN hbound
  refine ⟨hr, bulkResidueModulus_positive r hr p (fun i => (hp i).pos), ?_,
    hL _ r p (spectatorBulkCount_upper k L hL0) hrbound hupper⟩
  apply bulkResidueModuli_pairwise r p hp hinj
  intro i
  exact ((prime_coprime_frequencyModelBase S N (p i) n (hp i) (hNp i)
    (fun s hs => ⟨hS s hs, hN s hs⟩) t).pow_right _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingMaskedBulkAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compensation mask is invariant under every bulk reassignment -/

namespace Ostmann
open scoped Classical BigOperators

theorem selectedBulkPerm_active {B J : Type*} (slot : J ↪ B)
    (active : B → Bool) (hactive : ∀ j, active (slot j) = true)
    (e : Equiv.Perm J) (i : B) : active (selectedBulkPerm slot e i) = active i := by
  obtain ⟨j, rfl⟩ := (selectedIndexEquiv slot).surjective i
  cases j with
  | inl j => simp only [selectedIndexEquiv_inl, selectedBulkPerm_bulk, hactive]
  | inr j =>
    change active (selectedBulkPerm slot e j.val) = active j.val
    rw [selectedBulkPerm_nonbulk slot e j.val j.property]

theorem movingTemplateExternalMultiplier_bulk_action
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (active : MovingRegularSlot n r m → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n r m j) = true)
    (outside : List ℕ) (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (x : MovingRegularSlot n r m → P) (z y : ℝ) :
    movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal
      (selectedBulkSample (movingTemplateBulk n r m) e x) z y =
    movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal x z y := by
  let E := (selectedBulkPerm (movingTemplateBulk n r m) e).symm
  let q := fun i => (x i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (x i).property⟩
  let _ : ∀ i, Fact (q (E i)).Prime := fun i => ⟨hP _ (x (E i)).property⟩
  have ha : (fun i => active (E i)) = active := by
    funext i
    exact selectedBulkPerm_active (movingTemplateBulk n r m) active hactive e.symm i
  have h := naturalRegularMultiplier_equiv E q (fun i => hP _ (x i).property) active greg
    outside.prod ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s
  dsimp only at h
  rw [ha] at h
  unfold movingTemplateExternalMultiplier
  dsimp only
  exact congrArg (fun a : ℝ =>
    (giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ : ℂ) * a) h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedMatchedRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The masked correlation of two bulk assignments in pattern coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedMatchedKernel_fin {B C J : Type*} [Fintype J] {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (reg : J → Fin (N + 1)) (active : J → Bool)
    (other : (Fin (N + 1) → primes) → J → ℤ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (W : (B → primes) → ℝ → ℝ → ℂ)
    (x : Fin (N + 1) → primes)
    (hW : ∀ z y, W (fun j => x (e.symm (.inl j))) z y =
      movingPatternExternalMultiplier primes hprimes reg active other greg sreg φ
        Jleft Jright diagonal x z y) :
    movingWeightedMatchedKernel p (fun q : primes => (q : ℕ)) outside
      childBound pivotBound f g Dq Finset.univ ψ X lo hi φ G t small
      (movingPatternBulkLeaves n m slot perm) W u v a b center
      (fun j => x (e.symm (.inl j)))
      ((movingSamplePairCoordinates primes n).symm
        (fun i => x (e.symm (.inr (pattern i))))) =
    movingOriginalPatternMatchedObservable e t small slot perm pattern primes hprimes p g Dq
      reg active sreg other greg f outside childBound pivotBound
      ψ X lo hi φ G Jleft Jright diagonal u v a b center x := by
  have heval (side : Bool) :
      (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern side).map x =
      buildMovingSlotData n (t side)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (movingPatternBulkLeaves n m slot perm side))
        (movingPatternSamples primes n (fun i => x (e.symm (.inr (pattern i)))) side) := by
    exact movingPatternFinData_evaluate e t (fun _ => small)
      (movingPatternBulkLeaves n m slot perm) pattern x side
  have hterm (side : Bool) (XL XR : ℕ) :
      let T := buildMovingSlotData n (t side)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (movingPatternBulkLeaves n m slot perm side))
        (movingPatternSamples primes n (fun i => x (e.symm (.inr (pattern i)))) side)
      movingSupportedWeight (fun q : primes => (q : ℕ)) outside T XL XR
        (movingOriginalGiantWeight p (fun q : primes => (q : ℕ)) childBound pivotBound
          (fun _ => f) (fun _ _ _ _ => 1) g Dq Finset.univ ψ X lo hi φ G T (t side) XL XR) =
      movingSupportedWeight (fun i => (x i : ℕ)) outside
        (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern side) XL XR
        (movingOriginalGiantWeight p (fun i => (x i : ℕ)) childBound pivotBound
          (fun _ => f) (fun _ _ _ _ => 1) g Dq Finset.univ ψ X lo hi φ G
          (movingPatternFinBulkData e n m t (fun _ => small) slot perm pattern side)
          (t side) XL XR) := by
    dsimp only
    rw [← heval side, movingOriginalGiantWeight_map, movingSupportedWeight_map]
    rfl
  unfold movingOriginalPatternMatchedObservable
  unfold movingWeightedMatchedKernel
  dsimp only
  rw [← movingPatternSamples_pair]
  dsimp only
  apply congrArg (complexPrimeInterval 1 0 a b)
  funext y
  apply congrArg (complexIntegerInterval 1 0 u v center)
  funext z
  simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  rw [hterm false, hterm true]
  rw [hW z y]
  unfold movingPatternExternalMultiplier movingOriginalSupportedOuterPair
  dsimp only
  exact (mul_assoc _ _ _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingMatchedExteriorWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constants in the original matched-history exterior factor -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedMatchedKernel_mul {σ I B : Type*} {n : ℕ}
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small : TreeLeafTuple (List B) n)
    (bulk : Bool → TreeLeafTuple (List B) n)
    (weight : (B → σ) → ℂ) (W : (B → σ) → ℝ → ℝ → ℂ)
    (u v r w center : ℝ) (y : B → σ)
    (a : MovingSampleSlots σ n × MovingSampleSlots σ n) :
    movingWeightedMatchedKernel q value outside childBound pivotBound f g Dq S ψ X lo hi φ G
      t small bulk (fun y x z => weight y * W y x z) u v r w center y a =
    weight y * movingWeightedMatchedKernel q value outside childBound pivotBound f g Dq S
      ψ X lo hi φ G t small bulk W u v r w center y a := by
  unfold movingWeightedMatchedKernel
  simp_rw [mul_left_comm _ (weight y), complexIntegerInterval_const_mul,
    complexPrimeInterval_const_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedPrimePrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds on the support of the original harmonic prime priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The ambient sample space can include smaller primes in other roles. -/
theorem primeSubsetPrior_le_exp_of_support (P Q : Finset ℕ) (H T : ℝ)
    (hmass : (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hQ : ∀ q ∈ Q, Real.exp T ≤ (q : ℝ)) (p : P) :
    primeSubsetPrior P Q p ≤ Real.exp (H - T) := by
  by_cases hp : primeSubsetPrior P Q p = 0
  · rw [hp]
    exact (Real.exp_pos _).le
  · exact primeSubsetPrior_le_exp P Q p H T hmass
      (hQ _ (primeSubsetPrior_support P Q p hp))

/-- The compensated internal prior pays only its original normalizer. -/
theorem prime_mul_primeSubsetPrior_le (P Q : Finset ℕ) (p : P) :
    (p : ℝ) * primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ := by
  by_cases hp0 : (p : ℕ) = 0
  · simp only [hp0, Nat.cast_zero, zero_mul]
    exact inv_nonneg.mpr (Finset.sum_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))
  · have hp : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
    unfold primeSubsetPrior
    split_ifs
    · rw [div_eq_mul_inv, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
    · simp only [mul_zero]
      exact inv_nonneg.mpr (Finset.sum_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternPriorArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic support under the unchanged representative prior -/

namespace Ostmann
open scoped Classical BigOperators

/-- The literal list of frequencies still lies in the finite source set. -/
theorem allFrequencyList_subtype_mem (S : Finset ℤ) (n : ℕ)
    (t : FrequencyTree S n) (s : ℤ)
    (hs : s ∈ allFrequencyList n (frequencyTreeMap Subtype.val n t)) : s ∈ S := by
  induction n with
  | zero =>
    have heq : s = Subtype.val t := by simpa only [frequencyTreeMap, allFrequencyList, List.mem_singleton] using hs
    simpa only [heq] using (Subtype.property t)
  | succ n ih =>
    simp only [frequencyTreeMap, allFrequencyList, List.mem_cons, List.mem_append] at hs
    rcases hs with heq | hs | hs
    · simpa only [heq] using (Subtype.property t.1)
    · exact ih t.2.1 hs
    · exact ih t.2.2 hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicFamilyBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical bounds for the selected internal and external harmonic laws -/

namespace Ostmann
open scoped Classical BigOperators

/-- The fixed positive cell-mass constant changes the starting threshold,
not the coefficient of L in the normalizer. -/
theorem selected_cell_normalizer (c K L mass : ℝ) (hc : 0 < c)
    (hL : max 1 (-Real.log c) ≤ L)
    (hmass : c / Real.exp (K * L) ≤ mass) :
    0 < mass ∧ mass⁻¹ ≤ Real.exp ((K + 1) * L) := by
  have hm : 0 < mass := lt_of_lt_of_le (div_pos hc (Real.exp_pos _)) hmass
  have hsmall : Real.exp (-L) ≤ c := by
    calc
      _ ≤ Real.exp (Real.log c) :=
        Real.exp_le_exp.mpr (by linarith only [(le_max_right 1 (-Real.log c)).trans hL])
      _ = _ := Real.exp_log hc
  have hci : c⁻¹ ≤ Real.exp L := by
    have hh := inv_anti₀ (Real.exp_pos (-L)) hsmall
    simpa only [Real.exp_neg, inv_inv] using hh
  refine ⟨hm, (inv_anti₀ (div_pos hc (Real.exp_pos _)) hmass).trans ?_⟩
  calc
    (c / Real.exp (K * L))⁻¹ = Real.exp (K * L) * c⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ Real.exp (K * L) * Real.exp L :=
      mul_le_mul_of_nonneg_left hci (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Rich selected cells supply all the probability and atom bounds used in
both original-prime comparisons. Only their actual reciprocal masses and
prime ranges are needed. -/
theorem selected_harmonic_family_bounds (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    let C := K + 1
    1 ≤ C ∧ ∀ (L : ℝ), max 1 (-Real.log c) ≤ L → ∀ (P : Finset ℕ) (B : Type)
      (Qμ : ℕ → Finset ℕ) (Qν : B → Finset ℕ),
      (∀ j, Qμ j ⊆ P) → (∀ j, Qν j ⊆ P) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      let μ := fun j => primeSubsetPrior P (Qμ j)
      let ν := fun j => primeSubsetPrior P (Qν j)
      (∀ j q, 0 ≤ μ j q) ∧ (∀ j q, 0 ≤ ν j q) ∧
      (∀ j, ∑ q, μ j q = 1) ∧ (∀ j, ∑ q, ν j q = 1) ∧
      (∀ j (q : P), (q : ℝ) * μ j q ≤ Real.exp (C * L)) ∧
      (∀ j q, μ j q ≤ Real.exp (C * L - Real.exp ((39 / 10000 : ℝ) * L))) ∧
      (∀ j q, ν j q ≤ Real.exp (C * L - Real.exp ((39 / 10000 : ℝ) * L))) ∧
      (∀ j q, μ j q ≤ Real.exp (C * L - Real.exp ((1 / 100 : ℝ) * L))) ∧
      (∀ j q, μ j q ≠ 0 → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) := by
  dsimp only
  have hC : 1 ≤ K + 1 := by linarith only [hK]
  refine ⟨hC, ?_⟩
  intro L hL P B Qμ Qν hμP hνP hμmass hνmass hμrange hνrange
  have hm (j) := selected_cell_normalizer c K L (∑ q ∈ Qμ j, (q : ℝ)⁻¹) hc hL (hμmass j)
  have hn (j) := selected_cell_normalizer c K L (∑ q ∈ Qν j, (q : ℝ)⁻¹) hc hL (hνmass j)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hlow : Real.exp ((39 / 10000 : ℝ) * L) ≤ Real.exp ((1 / 100 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith only [hL1])
  refine ⟨(fun j q => primeSubsetPrior_nonneg P (Qμ j) q),
    (fun j q => primeSubsetPrior_nonneg P (Qν j) q), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact primeSubsetPrior_mass P (Qμ j) (hμP j) (ne_of_gt (hm j).1)
  · intro j
    exact primeSubsetPrior_mass P (Qν j) (hνP j) (ne_of_gt (hn j).1)
  · intro j q
    exact (prime_mul_primeSubsetPrior_le P (Qμ j) q).trans (hm j).2
  · intro j q
    exact primeSubsetPrior_le_exp_of_support P (Qμ j) _ _ (hm j).2
      (fun q hq => (Real.exp_le_exp.mpr hlow).trans (hμrange j q hq)) q
  · intro j q
    exact primeSubsetPrior_le_exp_of_support P (Qν j) _ _ (hn j).2 (hνrange j) q
  · intro j q
    exact primeSubsetPrior_le_exp_of_support P (Qμ j) _ _ (hm j).2 (hμrange j) q
  · intro j q hq
    exact hμrange j q (primeSubsetPrior_support P (Qμ j) q hq)

/-- A finite ambient prime set requires tier separation only for the
internal tiers which the depth-n sample actually uses. -/
theorem selected_harmonic_family_tiers (P : Finset ℕ) (B : Type) (n : ℕ)
    (Qμ : ℕ → Finset ℕ) (Qν : B → Finset ℕ) (tier : P → ℕ) (tierB : B → ℕ)
    (hμ : ∀ j, j < n → ∀ q : P, (q : ℕ) ∈ Qμ j → tier q = j)
    (hν : ∀ j (q : P), (q : ℕ) ∈ Qν j → tier q = tierB j) :
    (∀ j, j < n → ∀ q, primeSubsetPrior P (Qμ j) q ≠ 0 → tier q = j) ∧
    (∀ j q, primeSubsetPrior P (Qν j) q ≠ 0 → tier q = tierB j) := by
  exact ⟨fun j hj q hq => hμ j hj q (primeSubsetPrior_support P (Qμ j) q hq),
    fun j q hq => hν j q (primeSubsetPrior_support P (Qν j) q hq)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternDiagonalMaskedPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The masked diagonal bound for the original selected harmonic laws -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_diagonal_selected_masked_priors_rate
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ c K : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hc : 0 < c) (hK : 0 ≤ K)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cmass := K + 1
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) n) (Nfreq Vleaf : ℕ) (D : ℝ)
        (small : TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (_rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (f : ℤ → ℂ)
        (outside : List ℕ)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ)
        (Qμ : ℕ → Finset ℕ) (Qν : Bidx → Finset ℕ)
        (active : Fin (movingPatternRegularSlots e n m small slot).length → Bool)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let Eprior := Real.exp (Cmass * L)
      let Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ := fun _ {_} _ => f
      let A₀ := ((2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m)) *
        (frequencyLeafWeight (pairedFrequencyLeaf Sfreq Vleaf) n ft *
          ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots n ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) →
      (∀ b : Bool, MovingLeafLengthLE n ((fun _ => small) b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ b s regular, ‖Fw b (.leaf s regular) s‖ ≤ if s.natAbs ≤ Vleaf then 1 else 0) →
      0 ≤ D → (∀ q : ℕ, q ≠ 0 → q ≤ Nfreq ^ 2 → (q.divisors.card : ℝ) ≤ D) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      S ⊆ primes →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active j = false →
        (movingPatternRegularSlots e n m small slot).get j ∉
          Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      (∀ j, j < n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern
        (movingOriginalPatternDiagonalObservable e t small slot pattern primes _hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq
          (movingPatternRegularSlots e n m small slot).get active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e n m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center) x‖ ≤
        ((2 : ℝ) ^ Fintype.card Cidx *
          Eprior ^ (4 * n * 2 ^ n - Fintype.card Cidx)) *
          (((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
              Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) *
                2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
            Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  have hfamily := selected_harmonic_family_bounds c K hc hK
  let Cmass := K + 1
  have hCmass : 1 ≤ Cmass := hfamily.1
  filter_upwards [P.movingPattern_diagonal_whole_shell_masked_rate C hM ψ n r₀ k
    A Wwin Bφ Dφ Cmass hA hWwin hCmass hBφ hDφ,
    movingFrequencyModel_bulk_range n k A hA,
    eventually_ge_atTop (max 1 (-Real.log c))] with L hrate hmod hL
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ N e tierB t Sfreq ft Nfreq Vleaf D small slot pattern rep
    primes hprimes _ childBound pivotBound f outside p _ Dq sets
    primeLo cutoff tier X j₀ φ G global Qμ Qν active sreg setsReg Jleft Jright diagonal uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter hsmall hB hsmallLen ht hS hN hleaf hD hdiv hm hp
    hsets hsetsp hpupper hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange hactive houtcover hinjp huBig hrBig
    hNfreq hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hsreg hsregN hsetsReg
  let μ := fun j => primeSubsetPrior primes (Qμ j)
  let ν := fun j => primeSubsetPrior primes (Qν j)
  let α := Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L))
  let β := Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L))
  let Vint := Real.exp ((1 / 100 : ℝ) * L)
  let Uall := Real.exp (Real.exp ((11 / 1000 : ℝ) * L))
  obtain ⟨hμ0, hν0, hμsum, hνsum, hμbound, hμα, hνα, hμβ, hμmin⟩ :=
    hfamily.2 L hL primes Bidx Qμ Qν hμP hνP hμmass hνmass hμrange hνrange
  have htiers := selected_harmonic_family_tiers primes Bidx n Qμ Qν tier tierB hμtier hνtier
  have hL0 : 0 ≤ L := le_trans (by norm_num) ((le_max_left _ _).trans hL)
  have hμlo (j) (q : primes) (hq : μ j q ≠ 0) : primeLo < (q : ℕ) := by
    have hr := hμmin j q hq
    have hh : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
        Real.exp (Real.exp ((1 / 100 : ℝ) * L)) :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [hL0]))
    exact_mod_cast (hloReal.trans_le (hh.trans hr))
  have hνlo (j) (q : primes) (hq : ν j q ≠ 0) : primeLo < (q : ℕ) := by
    exact_mod_cast (hloReal.trans_le (hνrange j q (primeSubsetPrior_support primes (Qν j) q hq)))
  have hUlog : Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
    dsimp only [Uall]
    rw [Real.log_exp]
    exact Real.exp_le_exp.mpr (by linarith only [hL0])
  have hUup : Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    exact Real.exp_le_exp.mpr (by simpa only [Uall, Real.log_exp] using hUlog)
  obtain ⟨hrpos, hMpos, hcop, hMQ⟩ := hmod Sfreq Nfreq ft p hS hN hNfreq
    (fun i => Fact.out) hinjp (fun i => hNcut.trans_le (hpband i).1) hpupper
  let : NeZero (frequencyModelBase Sfreq n ft ^ (n - 1 + 2)) := ⟨Nat.ne_of_gt hrpos⟩
  let : NeZero (∏ i, bulkResidueModuli (frequencyModelBase Sfreq n ft ^ (n - 1 + 2)) p i) :=
    ⟨Nat.ne_of_gt hMpos⟩
  by_cases htier : ∀ i, movingSampleTier (rep (pattern i)).val.2 = movingSampleTier i.2
  ·
    exact hrate lo hi hlo hhi hwindow Bidx Cidx N e tierB (fun c => movingSampleTier (rep c).val.2) t Sfreq ft Nfreq Vleaf D
      small slot pattern rep primes hprimes childBound pivotBound f outside p hcop Dq sets
      primeLo cutoff tier X j₀ φ G global μ ν active (Real.exp (Cmass * L)) α β Vint Uall sreg setsReg Jleft Jright diagonal uG vG rG sG center
      huG hrG huvG hrsG hvG hsG hvcenter hsmall hB htier hsmallLen ht hS hN hleaf hD hdiv hm hp
      hsets hsetsp hpupper hMQ hφ hlip hφout hShell hdel hout
      (fun j => congrArg (primeSubsetPrior primes) (hν j))
      hμ0 hν0 hμsum hνsum (Real.one_le_exp_iff.mpr (mul_nonneg (by linarith only [hCmass]) hL0))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _) (Real.one_le_exp_iff.mpr (Real.exp_pos _).le)
      hμbound hμα hνα (fun c => hμβ _) (fun c => hμmin _) hupper hactive houtcover hinjp huBig hrBig
      hNfreq le_rfl le_rfl le_rfl rfl hUlog hUup htiers.1 htiers.2 hNlo hNcut hcutlo hμlo hνlo
      hupper hpband
      (fun z hz q hq j a ha heq => hdeleteμ z hz q hq j
        (heq ▸ primeSubsetPrior_support primes (Qμ j) a ha)) hdeletep
      (fun z hz q hq j a ha heq => hdeleteν z hz q hq j
        (heq ▸ primeSubsetPrior_support primes (Qν j) a ha)) hsreg hsregN hsetsReg
  · have hz (H : (Fin (N + 1) → primes) → ℂ) (x) :
        movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) n pattern H x = 0 :=
      movingPattern_zero_of_inconsistent_tiers e μ ν (fun q : primes => (q : ℕ))
        pattern rep tier htiers.1 htier H x
    dsimp only [μ, ν] at hz
    simp only [hz, Finset.sum_const_zero, norm_zero]
    have hleaf0 := frequencyLeafWeight_nonneg (pairedFrequencyLeaf Sfreq Vleaf)
      (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n ft
    have hprod : 0 ≤ ((frequencySplitList Sfreq n ft).map (pairFrequencySupportBound D)).prod := by
      apply List.prod_nonneg
      intro z hz
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hz
      exact pairFrequencySupportBound_nonneg D f
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete finite enumeration for every equality pattern -/

namespace Ostmann
open scoped Classical

/-- The same ambient coordinate budget covers every quotient pattern. -/
theorem movingPattern_enumeration (B : Type) [Fintype B] (b : B) (n : ℕ) :
    ∃ (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
      (_e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ B ⊕ Quotient s),
      ∀ s, N s + 1 ≤ Fintype.card B + 4 * n * 2 ^ n := by
  let N := fun s : Setoid (Bool × MovingSampleIndex n) => Fintype.card (B ⊕ Quotient s) - 1
  have hpos (s : Setoid (Bool × MovingSampleIndex n)) : 0 < Fintype.card (B ⊕ Quotient s) := by
    let : Nonempty (B ⊕ Quotient s) := ⟨Sum.inl b⟩
    exact Fintype.card_pos
  have heq (s : Setoid (Bool × MovingSampleIndex n)) :
      Fintype.card (B ⊕ Quotient s) = N s + 1 := by
    dsimp only [N]
    have hp := hpos s
    omega
  let e := fun s : Setoid (Bool × MovingSampleIndex n) => (Fintype.equivFinOfCardEq (heq s)).symm
  refine ⟨N, e, ?_⟩
  intro s
  rw [← heq s, Fintype.card_sum]
  apply Nat.add_le_add_left
  simpa only [card_movingSamplePairIndex] using Fintype.card_quotient_le s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternHalfLogGoodMaskedPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original diagonal bound for actual selected harmonic laws -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_half_log_good_selected_masked_priors_rate
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ c K gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hc : 0 < c) (hK : 0 ≤ K)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cmass := K + 1
      ∀ (lo hi : ℝ) (_hlo : 1 ≤ lo) (_hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (Sfreq : Finset ℤ) (ft : FrequencyTree (Sfreq × Sfreq) (n + 2)) (Nfreq : ℕ)
        (small : TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (_rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (f : ℤ → ℂ)
        (outside : List ℕ)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (global : Finset ℕ)
        (Qμ : ℕ → Finset ℕ) (Qν : Bidx → Finset ℕ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ)
        (active : Fin (movingPatternRegularSlots e (n + 2) m small slot).length → Bool)
        (sreg : ℤ) (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let Eprior := Real.exp (Cmass * L)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ b : Bool, ∀ i ∈ flattenMovingSlots (n + 2) ((fun _ => small) b), i ∉ Set.range slot) →
      (∀ i, (n + 2) ≤ tierB i) →
      (∀ b : Bool, MovingLeafLengthLE (n + 2) ((fun _ => small) b) r₀) →
      t = (fun b => frequencyTreeMap Subtype.val (n + 2) (frequencyPairProjection Sfreq (n + 2) b ft)) →
      (∀ s ∈ Sfreq, s ≠ 0) → (∀ s ∈ Sfreq, s.natAbs ≤ Nfreq) →
      (∀ s, ‖f s‖ ≤ 1) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      S ⊆ primes →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active j = false →
        (movingPatternRegularSlots e (n + 2) m small slot).get j ∉
          Set.range (movingPatternBulkEmbedding e slot)) →
      (∀ q ∈ outside, ∃ i, p i = q) →
      Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (Nfreq : ℝ) ≤ Real.exp (A * m) →
      (∀ j, j < (n + 2) → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      Nfreq ≤ primeLo → Nfreq < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q →
        ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      sreg ≠ 0 → sreg.natAbs ≤ Nfreq →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern
        (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ) *
        movingOriginalPatternMatchedObservable e t small slot perm pattern primes _hprimes
          p (fun i => normalizedResidueTransform (sets i)) Dq
          (movingPatternRegularSlots e (n + 2) m small slot).get active sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots e (n + 2) m small slot))
          (normalizedResidueFamily setsReg) f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal uG vG rG sG center x) x‖ ≤
        ((2 : ℝ) ^ Fintype.card Cidx *
          Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
          (Real.exp (-gain * m) +
            Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
            4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  have hfamily := selected_harmonic_family_bounds c K hc hK
  let Cmass := K + 1
  have hCmass : 1 ≤ Cmass := hfamily.1
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hmain⟩ :=
    P.movingPattern_half_log_good_masked_whole_shell_rate C hM ψ n r₀ k A Wwin Bφ Dφ Cmass gain
      hA hWwin hCmass hBφ hDφ Dlog hDlog hloglip tlog htlog
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hmain, movingFrequencyModel_bulk_range (n + 2) k A hA,
    eventually_ge_atTop (max 1 (-Real.log c))] with L hrate hmod hL
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx _ _ N e tierB t Sfreq ft Nfreq small slot perm pattern rep
    primes hprimes _ childBound pivotBound f outside p _ Dq sets β
    primeLo cutoff tier X j₀ φ G global Qμ Qν logSlots cb active sreg setsReg Jleft Jright diagonal uG vG rG sG center
    hslots huG hrG huvG hrsG hvG hsG hvcenter hsmall hB hsmallLen ht hS hN hf hm hp
    hsets hsetsp hpupper hgood hdlo hdhi hβ hbias hφ hlip hφout hShell hdel hout hν
    hμP hνP hμmass hνmass hμrange hνrange hactive houtcover hinjp huBig hrBig
    hNfreq hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsreg hsregN hsetsReg
  let μ := fun j => primeSubsetPrior primes (Qμ j)
  let ν := fun j => primeSubsetPrior primes (Qν j)
  let α := Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L))
  let βint := Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L))
  let Vint := Real.exp ((1 / 100 : ℝ) * L)
  let Uall := Real.exp (Real.exp ((11 / 1000 : ℝ) * L))
  obtain ⟨hμ0, hν0, hμsum, hνsum, hμbound, hμα, hνα, hμβ, hμmin⟩ :=
    hfamily.2 L hL primes Bidx Qμ Qν hμP hνP hμmass hνmass hμrange hνrange
  have htiers := selected_harmonic_family_tiers primes Bidx (n + 2) Qμ Qν tier tierB hμtier hνtier
  have hL0 : 0 ≤ L := le_trans (by norm_num) ((le_max_left _ _).trans hL)
  have hμlo (j) (q : primes) (hq : μ j q ≠ 0) : primeLo < (q : ℕ) := by
    have hr := hμmin j q hq
    have hh : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
        Real.exp (Real.exp ((1 / 100 : ℝ) * L)) :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [hL0]))
    exact_mod_cast (hloReal.trans_le (hh.trans hr))
  have hνlo (j) (q : primes) (hq : ν j q ≠ 0) : primeLo < (q : ℕ) := by
    exact_mod_cast (hloReal.trans_le (hνrange j q (primeSubsetPrior_support primes (Qν j) q hq)))
  have hUlog : Real.log Uall ≤ Real.exp ((12 / 1000 : ℝ) * L) := by
    dsimp only [Uall]
    rw [Real.log_exp]
    exact Real.exp_le_exp.mpr (by linarith only [hL0])
  have hUup : Uall ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    exact Real.exp_le_exp.mpr (by simpa only [Uall, Real.log_exp] using hUlog)
  obtain ⟨hrpos, hMpos, hcop, hMQ⟩ := hmod Sfreq Nfreq ft p hS hN hNfreq
    (fun i => Fact.out) hinjp (fun i => hNcut.trans_le (hpband i).1) hpupper
  let : NeZero (frequencyModelBase Sfreq (n + 2) ft ^ ((n + 2) - 1 + 2)) := ⟨Nat.ne_of_gt hrpos⟩
  let : NeZero (∏ i, bulkResidueModuli (frequencyModelBase Sfreq (n + 2) ft ^ ((n + 2) - 1 + 2)) p i) :=
    ⟨Nat.ne_of_gt hMpos⟩
  have hpage := frequencyModel_bulk_page_projection Sfreq (n + 2) Nfreq cutoff ft
    (fun s hs => ⟨hS s hs, hN s hs⟩) hNcut p (selectedPageZero P (bulkProgressionCutoff L))
    (fun i => ⟨Fact.out, (hpband i).1⟩)
    (fun z hz q hq i => (hdeletebulk z hz q hq i).symm)
  by_cases htier : ∀ i, movingSampleTier (rep (pattern i)).val.2 = movingSampleTier i.2
  ·
    exact hrate lo hi hlo hhi hwindow Bidx Cidx N e tierB (fun c => movingSampleTier (rep c).val.2) t Sfreq ft Nfreq
      small slot perm pattern rep primes hprimes childBound pivotBound f outside p hcop Dq sets β
      primeLo cutoff tier X j₀ φ G global μ ν logSlots cb active (Real.exp (Cmass * L)) α βint Vint Uall sreg setsReg Jleft Jright diagonal uG vG rG sG center
      hslots huG hrG huvG hrsG hvG hsG hvcenter hsmall hB htier hsmallLen ht hS hN hf hm hp
      hsets hsetsp hpupper hgood hdlo hdhi hβ hbias hMQ hpage hφ hlip hφout hShell hdel hout
      (fun j => congrArg (primeSubsetPrior primes) (hν j))
      hμ0 hν0 hμsum hνsum (Real.one_le_exp_iff.mpr (mul_nonneg (by linarith only [hCmass]) hL0))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _) (Real.one_le_exp_iff.mpr (Real.exp_pos _).le)
      hμbound hμα hνα (fun c => hμβ _) (fun c => hμmin _) hupper hactive houtcover hinjp huBig hrBig
      hNfreq le_rfl le_rfl le_rfl rfl hUlog hUup htiers.1 htiers.2 hNlo hNcut hcutlo hμlo hνlo
      hupper hpband
      (fun z hz q hq j a ha heq => hdeleteμ z hz q hq j
        (heq ▸ primeSubsetPrior_support primes (Qμ j) a ha)) hdeletep
      (fun z hz q hq j a ha heq => hdeleteν z hz q hq j
        (heq ▸ primeSubsetPrior_support primes (Qν j) a ha)) hsreg hsregN hsetsReg
  · have hz (H : (Fin (N + 1) → primes) → ℂ) (x) :
        movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern H x = 0 :=
      movingPattern_zero_of_inconsistent_tiers e μ ν (fun q : primes => (q : ℕ))
        pattern rep tier htiers.1 htier H x
    dsimp only [μ, ν] at hz
    simp only [hz, Finset.sum_const_zero, norm_zero]
    positivity

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateDiagonalPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed equality-pattern expansion of the actual masked diagonal -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateWeightedDiagonalMean_patterns
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (t : Bool → FrequencyTree ℤ n) (active : MovingRegularSlot n r m → Bool)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n r m → P → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n),
      Fin (N s + 1) ≃ MovingRegularSlot n r m ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let small := movingTemplateSmall n r m
    let slot := movingTemplateBulk n r m
    let W := movingTemplateExternalMultiplier P hP n r m active outside greg sreg φ
      Jleft Jright diagonal
    movingWeightedDiagonalMean p Subtype.val outside μ ν childBound pivotBound f g Dq Finset.univ
      ψ X lo hi φ G n t small (bulkSlotLeaves n m slot) W u v a b center =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → P,
      movingOriginalPatternWeight (e s) μ ν Subtype.val n (fun i => Quotient.mk'' i)
        (movingOriginalPatternDiagonalObservable (e s) t small slot (fun i => Quotient.mk'' i)
          P hP p g Dq (movingPatternRegularSlots (e s) n m small slot).get
          (fun i => active (movingPatternTemplateEquiv n r m (e s) i)) sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots (e s) n m small slot))
          greg f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal u v a b center) x := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  rw [movingWeightedDiagonalMean_patterns p Subtype.val outside μ ν]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  unfold movingOriginalPatternWeight
  congr 1
  unfold movingPatternInjectionGuard
  split_ifs
  · apply movingWeightedDiagonalKernel_fin (e s) t (movingTemplateSmall n r m)
      (movingTemplateBulk n r m) (fun i => Quotient.mk'' i) P hP p g Dq
      (movingPatternRegularSlots (e s) n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)).get
      (fun i => active (movingPatternTemplateEquiv n r m (e s) i))
      (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
        (movingPatternRegularSlots (e s) n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)))
      greg sreg f outside childBound pivotBound ψ X lo hi φ G Jleft Jright diagonal u v a b center
    intro z y
    exact movingTemplateExternalMultiplier_pattern P hP n r m (e s) active outside greg sreg φ
      Jleft Jright diagonal x z y
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedDiagonalEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact expansion of the coefficient square with its exterior mask retained -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedDiagonalEnergy_eq {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small bulk : TreeLeafTuple (List B) n)
    (W : ℤ → (B → σ) → ℝ → ℝ → ℂ) (u v r w center : ℝ) :
    movingWeightedDiagonalEnergy q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n small bulk W u v r w center =
    ∑ s : transferFrequencyRange (V n), ∑ a : MovingDescendantFrequencyIndex V n,
      ∑ b : MovingDescendantFrequencyIndex V n,
        movingWeightedDiagonalMean q value outside μ ν childBound pivotBound f g Dq S
          ψ X lo hi φ G n (fun side => if side then movingRootedFrequencyTree V n s.val b
            else movingRootedFrequencyTree V n s.val a)
          small bulk (W s.val) u v r w center := by
  unfold movingWeightedDiagonalEnergy
  apply Finset.sum_congr rfl
  intro s _
  have heq (y : B → σ) (x z : ℝ) :
      (‖movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s.val
        (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) =
      ∑ a : MovingDescendantFrequencyIndex V n, ∑ b : MovingDescendantFrequencyIndex V n,
        movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (movingRootedFrequencyTree V n s.val a)
          (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingOriginalSampleAverage q value outside μ childBound pivotBound (fun _ => f)
          g Dq S ψ X lo hi φ G n (movingRootedFrequencyTree V n s.val b)
          (treeLeafMap (List.map y) n small) (treeLeafMap (List.map y) n bulk)
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) := by
    rw [movingFrequencyCoefficient_original, Complex.star_def, ← Complex.mul_conj']
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [heq, Finset.sum_mul, complexIntegerInterval_sum, complexPrimeInterval_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedDiagonalHistories
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original paired frequency histories with the exterior multiplier retained -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedDiagonalEnergy_history_bound {B : Type} [Fintype B]
    (primes : Finset ℕ) (outside : List ℕ)
    (n m : ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (small bulk : TreeLeafTuple (List B) n)
    (W : ℤ → (B → primes) → ℝ → ℝ → ℂ)
    (u v r w center : ℝ) (hV : Monotone V) :
    let Sfreq := (transferFrequencyRange (V n)).erase 0
    let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
      frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    ‖movingWeightedDiagonalEnergy p Subtype.val outside μ ν childBound pivotBound V f g Dq
      Finset.univ ψ X lo hi φ G n small bulk W u v r w center‖ ≤
      ∑ t : FrequencyTree (Sfreq × Sfreq) n,
        ‖movingWeightedDiagonalMean p Subtype.val outside μ ν childBound pivotBound f g Dq
          Finset.univ ψ X lo hi φ G n (trees t) small bulk
          (W (frequencyRoot n (trees t false))) u v r w center‖ := by
  dsimp only
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let M := fun a b : FrequencyTree ℤ n =>
    movingWeightedDiagonalMean p (fun q : primes => (q : ℕ)) outside μ ν childBound pivotBound
      f g Dq Finset.univ ψ X lo hi φ G n (fun side => if side then b else a)
      small bulk (W (frequencyRoot n a)) u v r w center
  have hzL (a : ScheduledFrequencyIndex V n) (t : FrequencyTree ℤ n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M (scheduledFrequencyHistory V n a) t = 0 :=
    movingWeightedDiagonalMean_zero_frequency p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound f hf g Dq Finset.univ ψ X lo hi φ G n _ small
      bulk (W _) u v r w center false ha
  have hzR (t : FrequencyTree ℤ n) (a : ScheduledFrequencyIndex V n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M t (scheduledFrequencyHistory V n a) = 0 :=
    movingWeightedDiagonalMean_zero_frequency p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound f hf g Dq Finset.univ ψ X lo hi φ G n _ small
      bulk (W _) u v r w center true ha
  have hs := same_root_scheduled_pair_sum_le V n
    (fun a b => ‖M (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b)‖)
    (fun _ _ => norm_nonneg _)
  have hh (a : transferFrequencyRange (V n)) (b : MovingDescendantFrequencyIndex V n) :
      scheduledFrequencyHistory V n ((scheduledFrequencyRootEquiv V n).symm (a, b)) =
        movingRootedFrequencyTree V n a.val b := by
    rw [scheduledFrequencyRootEquiv_history, Equiv.apply_symm_apply]
  simp_rw [hh] at hs
  have he := paired_scheduled_history_sum_le V hV n (fun a b => ‖M a b‖)
    (fun _ _ => norm_nonneg _) (fun a t ha => by rw [hzL a t ha, norm_zero])
    (fun t a ha => by rw [hzR t a ha, norm_zero])
  rw [movingWeightedDiagonalEnergy_eq]
  apply le_trans _ (hs.trans (he.trans ?_))
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    have hb := norm_sum_le (Finset.univ : Finset (MovingDescendantFrequencyIndex V n))
      (fun c => movingWeightedDiagonalMean p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound f g Dq Finset.univ ψ X lo hi φ G n
        (fun side => if side then movingRootedFrequencyTree V n a.val c
          else movingRootedFrequencyTree V n a.val b)
        small bulk (W a.val) u v r w center)
    simpa only [M, frequencyRoot_movingRootedFrequencyTree] using hb
  · apply Finset.sum_le_sum
    intro t _
    let trees := fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    have htrees : (fun side => if side then trees true else trees false) = trees := by
      funext side
      cases side <;> rfl
    dsimp only [M]
    rw [htrees]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateEnergyPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual masked energy is bounded by its original signed pattern means -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateDiagonalEnergy_pattern_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ)
    (n r m : ℕ) (active : MovingRegularSlot n r m → Bool)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n r m → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ) (hV : Monotone V)
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n),
      Fin (N s + 1) ≃ MovingRegularSlot n r m ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let Sfreq := (transferFrequencyRange (V n)).erase 0
    let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
      frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    let small := movingTemplateSmall n r m
    let slot := movingTemplateBulk n r m
    let W := fun s => movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal
    let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
      ∑ x : Fin (N s + 1) → P,
        movingOriginalPatternWeight (e s) μ ν Subtype.val n (fun i => Quotient.mk'' i)
          (movingOriginalPatternDiagonalObservable (e s) (trees t) small slot (fun i => Quotient.mk'' i)
            P hP p g Dq (movingPatternRegularSlots (e s) n m small slot).get
            (fun i => active (movingPatternTemplateEquiv n r m (e s) i))
            (frequencyRoot n (trees t false))
            (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
              (movingPatternRegularSlots (e s) n m small slot))
            greg f outside childBound pivotBound ψ X lo hi φ G
            Jleft Jright diagonal u v a b center) x
    ‖movingWeightedDiagonalEnergy p Subtype.val outside μ ν childBound pivotBound V f g Dq
      Finset.univ ψ X lo hi φ G n small (bulkSlotLeaves n m slot) W u v a b center‖ ≤
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ∑ s : Setoid (Bool × MovingSampleIndex n), ‖term t s‖ := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  apply (movingWeightedDiagonalEnergy_history_bound P outside n m p μ ν childBound pivotBound V
    f hf g Dq ψ X lo hi φ G (movingTemplateSmall n r m)
    (bulkSlotLeaves n m (movingTemplateBulk n r m))
    (fun s => movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal) u v a b center hV).trans
  apply Finset.sum_le_sum
  intro t _
  rw [movingTemplateWeightedDiagonalMean_patterns P hP n r m _ active p μ ν g Dq greg _
    f outside childBound pivotBound ψ X lo hi φ G Jleft Jright diagonal u v a b center N e]
  exact norm_sum_le _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateDiagonalRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the numerical pattern budget to the original masked energy -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateDiagonalEnergy_pattern_rate
    (ψ : 𝓢(ℝ, ℂ)) (n k : ℕ) (hk : 0 < k) (hn : n ≤ k)
    (Bwindow Cfreq Cprior ε : ℝ) (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior)
    (hε : 0 < ε) (hdepth : 8 * Cprior ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∃ D : ℝ, 0 ≤ D ∧
        (∀ d : ℕ, d ≠ 0 → (d : ℝ) ≤ Real.exp (2 * Cfreq * m) →
          (d.divisors.card : ℝ) ≤ D) ∧
        ∀ (r₀ : ℕ)
          (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
          (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
          (μ : ℕ → primes → ℝ) (ν : MovingRegularSlot n r₀ m → primes → ℝ)
          (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
          (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
          (X Δ hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
          (active : MovingRegularSlot n r₀ m → Bool)
          (greg : ∀ q : ℕ, ZMod q → ℂ) (outside : List ℕ)
          (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ)
          (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
          (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ MovingRegularSlot n r₀ m ⊕ Quotient s),
        let small := movingTemplateSmall n r₀ m
        let slot := movingTemplateBulk n r₀ m
        let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
        let Sfreq := (transferFrequencyRange (V n)).erase 0
        let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
          frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
        let K := ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            Bwindow ^ (2 ^ n - 1)) ^ 2 *
          ((2 : ℝ) ^ (2 ^ n * m) * 4 * 3 ^ (2 ^ n * m)) * 2 ^ (2 ^ n * m)
        let err := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
        let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
          ∑ x : Fin (N s + 1) → primes,
            movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n
              (fun i => Quotient.mk'' i)
              (movingOriginalPatternDiagonalObservable (e s) (trees t) small slot
                (fun i => Quotient.mk'' i) primes hprimes p g Dq
                (movingPatternRegularSlots (e s) n m small slot).get (fun i => active (movingPatternTemplateEquiv n r₀ m (e s) i))
                (frequencyRoot n (trees t false))
                (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
                  (movingPatternRegularSlots (e s) n m small slot)) greg f outside
                childBound pivotBound ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center) x
        Monotone V → f 0 = 0 →
        (Sfreq.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (V n : ℝ) ≤ Real.exp (Cfreq * m) →
        (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
        (∀ s t, ‖term t s‖ ≤
          ((2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (err + K * (frequencyLeafWeight (pairedFrequencyLeaf Sfreq (V 0)) n t *
            ((frequencySplitList Sfreq n t).map (pairFrequencySupportBound D)).prod))) →
        ‖movingWeightedDiagonalEnergy p (fun q : primes => (q : ℕ)) outside μ ν
          childBound pivotBound V f g Dq Finset.univ ψ X (Real.exp Δ) hi φ G n small
          (bulkSlotLeaves n m slot)
          (fun s => movingTemplateExternalMultiplier primes hprimes n r₀ m active outside greg s φ
            Jleft Jright diagonal) u v r w center‖ ≤
          Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_diagonal_pattern_norm_rate ψ n k hk hn
    Bwindow Cfreq Cprior ε hCfreq hCprior hε hdepth] with L hrate
  dsimp only at hrate ⊢
  obtain ⟨D, hD, hdiv, hrate⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro r₀ primes hprimes p _ μ ν childBound pivotBound V f g Dq X Δ hi φ G
    active greg outside Jleft Jright diagonal u v r w center N e
  let m := spectatorBulkCount k L
  let small := movingTemplateSmall n r₀ m
  let slot := movingTemplateBulk n r₀ m
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
    frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
  let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
    ∑ x : Fin (N s + 1) → primes,
      movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n (fun i => Quotient.mk'' i)
        (movingOriginalPatternDiagonalObservable (e s) (trees t) small slot (fun i => Quotient.mk'' i)
          primes hprimes p g Dq (movingPatternRegularSlots (e s) n m small slot).get (fun i => active (movingPatternTemplateEquiv n r₀ m (e s) i))
          (frequencyRoot n (trees t false))
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots (e s) n m small slot)) greg f outside childBound pivotBound
          ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center) x
  intro hV hf hcard hVn hV0 hterm
  have hS : ∀ s ∈ Sfreq, s ≠ 0 ∧ s.natAbs ≤ V n := by
    intro s hs
    exact ⟨(Finset.mem_erase.mp hs).1,
      (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp hs).2⟩
  have hsum := hrate Sfreq (V n) (V 0) Δ
    (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
      4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) hcard hS hVn hV0 (by positivity) le_rfl
    (fun s t => (‖term t s‖ : ℂ)) (by
      intro s t
      rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      exact hterm s t)
  have hnonneg : 0 ≤ ∑ s : Setoid (Bool × MovingSampleIndex n),
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ‖term t s‖ := by positivity
  simp only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hnonneg] at hsum
  have hactual := movingTemplateDiagonalEnergy_pattern_bound primes hprimes outside n r₀
    (spectatorBulkCount k L) active p μ ν childBound pivotBound V f hf g Dq ψ X (Real.exp Δ)
    hi φ G greg Jleft Jright diagonal u v r w center hV N e
  apply hactual.trans
  rw [Finset.sum_comm]
  exact hsum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedTemplateEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual mixed diagonal energy under selected harmonic prime laws -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The mixed diagonal energy estimate with its original arithmetic premise
fully supplied by the published progression estimate and the concrete cells. -/
theorem PublishedProgressionInput.moving_selected_template_diagonal_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n ≤ k)
    (A Wwin Bφ Dφ c K ε : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot n r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (active : MovingRegularSlot n r₀ m → Bool)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot n r₀ m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let small := movingTemplateSmall n r₀ m
      let slot := movingTemplateBulk n r₀ m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V n)).erase 0
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ V 0 then 1 else 0) →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V n : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i, n ≤ tierB i) →
      0 < m → (∀ i, 3 ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot n r₀ m) + 4 * n * 2 ^ n) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active (slot j) = true) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j, j < n → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V n ≤ primeLo → V n < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingWeightedDiagonalEnergy p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ
        ψ X (Real.exp Δ) hi φ G n small (bulkSlotLeaves n m slot)
        (fun s => movingTemplateExternalMultiplier primes _hprimes n r₀ m active outside
          (normalizedResidueFamily setsReg) s φ Jleft Jright diagonal) uG vG rG sG center‖ ≤
        Real.exp ((2 ^ n : ℕ) * Δ + (Real.log 12 + 1) * (2 ^ n : ℕ) * m + ε * m) +
          5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hCprior : 1 ≤ K + 1 := (selected_harmonic_family_bounds c K hc hK).1
  filter_upwards [P.movingPattern_diagonal_selected_masked_priors_rate C hM ψ n r₀ k
    A Wwin Bφ Dφ c K hA hWwin hc hK hBφ hDφ,
    movingTemplateDiagonalEnergy_pattern_rate ψ n k hk hn Bφ A (K + 1) ε
      hA hCprior hε hdepth] with L hprime henergy
  dsimp only
  dsimp only at henergy
  obtain ⟨D, hD, hdiv, henergy⟩ := henergy
  intro tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
    hm hp hsets hsetsp hpupper hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg
  let B := MovingRegularSlot n r₀ (spectatorBulkCount k L)
  let small := movingTemplateSmall n r₀ (spectatorBulkCount k L)
  let slot := movingTemplateBulk n r₀ (spectatorBulkCount k L)
  have hsmall := movingTemplateSmall_not_bulk n r₀ (spectatorBulkCount k L)
  have hsmallLen := movingTemplateSmall_length n r₀ (spectatorBulkCount k L)
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let j₀ : TreeLeafIndex n × Fin (spectatorBulkCount k L) :=
    ⟨Classical.choice inferInstance, ⟨0, hm⟩⟩
  obtain ⟨N, e, hNcard⟩ := movingPattern_enumeration B (slot j₀) n
  have hdel' (s) : ((global.card + (N s + 1) + outside.length : ℕ) : ℝ) ≤
      Real.exp ((K + 1) * L) := by
    exact (Nat.cast_le.mpr (Nat.add_le_add_right
      (Nat.add_le_add_left (hNcard s) global.card) outside.length)).trans hdel
  apply henergy r₀ primes hprimes p
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j => primeSubsetPrior primes (Qν j))
    childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq
    X Δ hi φ G active (normalizedResidueFamily setsReg) outside Jleft Jright diagonal
    uG vG rG sG center N e hV hf0 hcard hVn hV0
  intro s t
  let rep : ∀ c : Quotient s, {i : Bool × MovingSampleIndex n // Quotient.mk'' i = c} :=
    fun c => ⟨c.out, Quotient.out_eq' c⟩
  have hS : ∀ a ∈ Sfreq, a ≠ 0 := fun a ha => (Finset.mem_erase.mp ha).1
  have hN : ∀ a ∈ Sfreq, a.natAbs ≤ V n := by
    intro a ha
    exact (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp ha).2
  have hdiv' (q : ℕ) (hq : q ≠ 0) (hsize : q ≤ (V n) ^ 2) : (q.divisors.card : ℝ) ≤ D := by
    apply hdiv q hq
    calc
      (q : ℝ) ≤ ((V n : ℕ) : ℝ) ^ 2 := by exact_mod_cast hsize
      _ ≤ (Real.exp (A * spectatorBulkCount k L)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hVn 2
      _ = Real.exp (2 * A * spectatorBulkCount k L) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hh := hprime (Real.exp Δ) hi (Real.one_le_exp_iff.mpr hΔ) hhi hwindow
    B (Quotient s) (N s) (e s) tierB
    (fun b => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n b t))
    Sfreq t (V n) (V 0) D small slot (fun i => Quotient.mk'' i) rep primes hprimes
    childBound pivotBound f outside p Dq sets primeLo cutoff tier X j₀ φ G global Qμ Qν
    (fun i => active (movingPatternTemplateEquiv n r₀ (spectatorBulkCount k L) (e s) i))
    (frequencyRoot n (frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n false t)))
    setsReg Jleft Jright diagonal uG vG rG sG center
    huG hrG huvG hrsG hvG hsG hvcenter (fun _ => hsmall) hB (fun _ => hsmallLen)
    rfl hS hN (fun _ a _ => hf a) hD hdiv' hm hp hsets hsetsp hpupper
    hφ hlip hφout hShell (hdel' s) hout hν hμP hνP hμmass hνmass hμrange hνrange
    (fun i hi => movingPatternTemplate_inactive_not_bulk n r₀ (spectatorBulkCount k L)
      (e s) active hactive i hi) houtcover hinjp huBig hrBig hVn hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband
    hdeleteμ hdeletep hdeleteν
    (hS _ (allFrequencyList_subtype_mem Sfreq n (frequencyPairProjection Sfreq n false t) _
      (frequencyRoot_mem_allFrequencyList n _)))
    (hN _ (allFrequencyList_subtype_mem Sfreq n (frequencyPairProjection Sfreq n false t) _
      (frequencyRoot_mem_allFrequencyList n _))) hsetsReg
  calc
    _ ≤ _ := hh
    _ ≤ _ := by
      rw [Fintype.card_prod, card_treeLeafIndex, Fintype.card_fin]
      have hw : 0 ≤ frequencyLeafWeight (pairedFrequencyLeaf Sfreq (V 0)) n t *
          ((frequencySplitList Sfreq n t).map (pairFrequencySupportBound D)).prod := by
        apply mul_nonneg
        · exact frequencyLeafWeight_nonneg _ (fun _ => by
            unfold pairedFrequencyLeaf
            split_ifs <;> norm_num) n t
        · apply List.prod_nonneg
          intro a ha
          obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
          exact pairFrequencySupportBound_nonneg D a
      have hκ : 0 ≤ (2 : ℝ) ^ Fintype.card (Quotient s) *
          (Real.exp ((K + 1) * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s)) := by positivity
      have hreserve : 0 ≤
          (((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
            Bφ ^ (2 ^ n - 1)) ^ 2) *
          ((2 : ℝ) ^ (2 ^ n * spectatorBulkCount k L) * 3 ^ (2 ^ n * spectatorBulkCount k L)) *
          (frequencyLeafWeight (pairedFrequencyLeaf Sfreq (V 0)) n t *
            ((frequencySplitList Sfreq n t).map (pairFrequencySupportBound D)).prod) *
          2 ^ (2 ^ n * spectatorBulkCount k L) := by positivity
      nlinarith only [mul_nonneg hκ hreserve]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLogFamilyPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed equality-pattern expansion of the actual masked diagonal -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateLogFamilyWeightedMatchedMean_patterns
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (t : Bool → FrequencyTree ℤ n) (active : MovingRegularSlot n r m → Bool)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n r m → P → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (sreg : ℤ)
    (f : ℤ → ℂ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center cb : ℝ)
    (tlog : ℕ) (logSlots : Fin tlog → List (MovingRegularSlot n r m))
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n),
      Fin (N s + 1) ≃ MovingRegularSlot n r m ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let small := movingTemplateSmall n r m
    let slot := movingTemplateBulk n r m
    let wgt := fun (y : MovingRegularSlot n r m → P) =>
      ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
    let W := movingTemplateExternalMultiplier P hP n r m active outside greg sreg φ
      Jleft Jright diagonal
    movingWeightedMatchedMean p Subtype.val outside μ ν childBound pivotBound f g Dq Finset.univ
      ψ X lo hi φ G n t small (movingPatternBulkLeaves n m slot perm) (fun y x z => wgt y * W y x z) u v a b center =
    ∑ s : Setoid (Bool × MovingSampleIndex n), ∑ x : Fin (N s + 1) → P,
      movingOriginalPatternWeight (e s) μ ν Subtype.val n (fun i => Quotient.mk'' i)
        (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb
          ((logSlots j).map (fun i => (e s).symm (.inl i))) : ℝ) : ℂ) *
        movingOriginalPatternMatchedObservable (e s) t small slot perm (fun i => Quotient.mk'' i)
          P hP p g Dq (movingPatternRegularSlots (e s) n m small slot).get
          (fun i => active (movingPatternTemplateEquiv n r m (e s) i)) sreg
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots (e s) n m small slot))
          greg f outside childBound pivotBound ψ X lo hi φ G
          Jleft Jright diagonal u v a b center x) x := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  rw [movingWeightedMatchedMean_patterns p Subtype.val outside μ ν]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  unfold movingOriginalPatternWeight
  congr 1
  unfold movingPatternInjectionGuard
  split_ifs
  · dsimp only
    rw [movingWeightedMatchedKernel_mul]
    have hw (x : Fin (N s + 1) → P) :
        (∏ j, bulkLogCutoffWeight
          (fun i => ((x ((e s).symm (.inl i)) : ℕ) : ℝ)) cb
          (logSlots j)) =
        ∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb
          ((logSlots j).map
            (fun i => (e s).symm (.inl i))) := by
      simp only [bulkLogCutoffWeight_map, Function.comp_def]
    rw [hw x]
    congr 1
    apply movingWeightedMatchedKernel_fin (e s) t (movingTemplateSmall n r m)
      (movingTemplateBulk n r m) perm (fun i => Quotient.mk'' i) P hP p g Dq
      (movingPatternRegularSlots (e s) n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)).get
      (fun i => active (movingPatternTemplateEquiv n r m (e s) i))
      (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
        (movingPatternRegularSlots (e s) n m (movingTemplateSmall n r m) (movingTemplateBulk n r m)))
      greg sreg f outside childBound pivotBound ψ X lo hi φ G Jleft Jright diagonal u v a b center
    intro z y
    exact movingTemplateExternalMultiplier_pattern P hP n r m (e s) active outside greg sreg φ
      Jleft Jright diagonal x z y
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingWeightedMatchedHistories
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original paired frequency histories with the exterior multiplier retained -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingWeightedMatchedCorrelation_history_bound {B : Type} [Fintype B]
    (primes : Finset ℕ) (outside : List ℕ)
    (n m : ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → primes → ℝ) (ν : B → primes → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (small : TreeLeafTuple (List B) n) (bulk : Bool → TreeLeafTuple (List B) n)
    (W : ℤ → (B → primes) → ℝ → ℝ → ℂ)
    (u v r w center : ℝ) (hV : Monotone V) :
    let Sfreq := (transferFrequencyRange (V n)).erase 0
    let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
      frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    ‖movingWeightedMatchedCorrelation p Subtype.val outside μ ν childBound pivotBound V f g Dq
      Finset.univ ψ X lo hi φ G n small bulk W u v r w center‖ ≤
      ∑ t : FrequencyTree (Sfreq × Sfreq) n,
        ‖movingWeightedMatchedMean p Subtype.val outside μ ν childBound pivotBound f g Dq
          Finset.univ ψ X lo hi φ G n (trees t) small bulk
          (W (frequencyRoot n (trees t false))) u v r w center‖ := by
  dsimp only
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let M := fun a b : FrequencyTree ℤ n =>
    movingWeightedMatchedMean p (fun q : primes => (q : ℕ)) outside μ ν childBound pivotBound
      f g Dq Finset.univ ψ X lo hi φ G n (fun side => if side then b else a)
      small bulk (W (frequencyRoot n a)) u v r w center
  have hzL (a : ScheduledFrequencyIndex V n) (t : FrequencyTree ℤ n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M (scheduledFrequencyHistory V n a) t = 0 :=
    movingWeightedMatchedMean_zero_frequency p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound f hf g Dq Finset.univ ψ X lo hi φ G n _ small
      bulk (W _) u v r w center false ha
  have hzR (t : FrequencyTree ℤ n) (a : ScheduledFrequencyIndex V n)
      (ha : ¬ ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) :
      M t (scheduledFrequencyHistory V n a) = 0 :=
    movingWeightedMatchedMean_zero_frequency p (fun q : primes => (q : ℕ)) outside μ ν
      childBound pivotBound f hf g Dq Finset.univ ψ X lo hi φ G n _ small
      bulk (W _) u v r w center true ha
  have hs := same_root_scheduled_pair_sum_le V n
    (fun a b => ‖M (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b)‖)
    (fun _ _ => norm_nonneg _)
  have hh (a : transferFrequencyRange (V n)) (b : MovingDescendantFrequencyIndex V n) :
      scheduledFrequencyHistory V n ((scheduledFrequencyRootEquiv V n).symm (a, b)) =
        movingRootedFrequencyTree V n a.val b := by
    rw [scheduledFrequencyRootEquiv_history, Equiv.apply_symm_apply]
  simp_rw [hh] at hs
  have he := paired_scheduled_history_sum_le V hV n (fun a b => ‖M a b‖)
    (fun _ _ => norm_nonneg _) (fun a t ha => by rw [hzL a t ha, norm_zero])
    (fun t a ha => by rw [hzR t a ha, norm_zero])
  rw [movingWeightedMatchedCorrelation_eq]
  apply le_trans _ (hs.trans (he.trans ?_))
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    have hb := norm_sum_le (Finset.univ : Finset (MovingDescendantFrequencyIndex V n))
      (fun c => movingWeightedMatchedMean p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound f g Dq Finset.univ ψ X lo hi φ G n
        (fun side => if side then movingRootedFrequencyTree V n a.val c
          else movingRootedFrequencyTree V n a.val b)
        small bulk (W a.val) u v r w center)
    simpa only [M, frequencyRoot_movingRootedFrequencyTree] using hb
  · apply Finset.sum_le_sum
    intro t _
    let trees := fun side => frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    have htrees : (fun side => if side then trees true else trees false) = trees := by
      funext side
      cases side <;> rfl
    dsimp only [M]
    rw [htrees]
    split_ifs
    · exact le_rfl
    · exact norm_nonneg _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLogFamilyBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual masked energy is bounded by its original signed pattern means -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateLogFamilyMatchedCorrelation_pattern_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ)
    (n r m : ℕ) (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (active : MovingRegularSlot n r m → Bool)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n r m → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ) (hf : f 0 = 0)
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center cb : ℝ) (hV : Monotone V)
    (tlog : ℕ) (logSlots : Fin tlog → List (MovingRegularSlot n r m))
    (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
    (e : ∀ s : Setoid (Bool × MovingSampleIndex n),
      Fin (N s + 1) ≃ MovingRegularSlot n r m ⊕ Quotient s) :
    let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let Sfreq := (transferFrequencyRange (V n)).erase 0
    let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
      frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
    let small := movingTemplateSmall n r m
    let slot := movingTemplateBulk n r m
    let wgt := fun (y : MovingRegularSlot n r m → P) =>
      ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
    let W := fun s => movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal
    let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
      ∑ x : Fin (N s + 1) → P,
        movingOriginalPatternWeight (e s) μ ν Subtype.val n (fun i => Quotient.mk'' i)
          (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb
            ((logSlots j).map (fun i => (e s).symm (.inl i))) : ℝ) : ℂ) *
          movingOriginalPatternMatchedObservable (e s) (trees t) small slot perm (fun i => Quotient.mk'' i)
            P hP p g Dq (movingPatternRegularSlots (e s) n m small slot).get
            (fun i => active (movingPatternTemplateEquiv n r m (e s) i))
            (frequencyRoot n (trees t false))
            (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
              (movingPatternRegularSlots (e s) n m small slot))
            greg f outside childBound pivotBound ψ X lo hi φ G
            Jleft Jright diagonal u v a b center x) x
    ‖movingWeightedMatchedCorrelation p Subtype.val outside μ ν childBound pivotBound V f g Dq
      Finset.univ ψ X lo hi φ G n small (movingPatternBulkLeaves n m slot perm) (fun s y x z => wgt y * W s y x z) u v a b center‖ ≤
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ∑ s : Setoid (Bool × MovingSampleIndex n), ‖term t s‖ := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  apply (movingWeightedMatchedCorrelation_history_bound P outside n m p μ ν childBound pivotBound V
    f hf g Dq ψ X lo hi φ G (movingTemplateSmall n r m)
    (movingPatternBulkLeaves n m (movingTemplateBulk n r m) perm)
    (fun s y x z =>
      ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb
        (logSlots j) : ℝ) : ℂ) *
      movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal y x z) u v a b center hV).trans
  apply Finset.sum_le_sum
  intro t _
  rw [movingTemplateLogFamilyWeightedMatchedMean_patterns P hP n r m perm _ active p μ ν g Dq greg _
    f outside childBound pivotBound ψ X lo hi φ G Jleft Jright diagonal u v a b center cb tlog logSlots N e]
  exact norm_sum_le _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLogFamilyRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full original matched correlation from the signed pattern budget -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateLogFamilyMatchedCorrelation_pattern_rate
    (ψ : 𝓢(ℝ, ℂ)) (n k : ℕ) (hk : 0 < k)
    (Cfreq Cprior gain : ℝ) (hCfreq : 0 ≤ Cfreq) (hCprior : 1 ≤ Cprior) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
        ∀ (r₀ : ℕ)
          (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
          (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
          (μ : ℕ → primes → ℝ) (ν : MovingRegularSlot n r₀ m → primes → ℝ)
          (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
          (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
          (X Δ hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
          (active : MovingRegularSlot n r₀ m → Bool)
          (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
          (greg : ∀ q : ℕ, ZMod q → ℂ) (outside : List ℕ)
          (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center cb : ℝ)
          (tlog : ℕ) (logSlots : Fin tlog → List (MovingRegularSlot n r₀ m))
          (N : Setoid (Bool × MovingSampleIndex n) → ℕ)
          (e : ∀ s : Setoid (Bool × MovingSampleIndex n), Fin (N s + 1) ≃ MovingRegularSlot n r₀ m ⊕ Quotient s),
        let small := movingTemplateSmall n r₀ m
        let slot := movingTemplateBulk n r₀ m
        let wgt := fun (y : MovingRegularSlot n r₀ m → primes) =>
          ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
        let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
        let Sfreq := (transferFrequencyRange (V n)).erase 0
        let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
          frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
        let err := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
        let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
          ∑ x : Fin (N s + 1) → primes,
            movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n
              (fun i => Quotient.mk'' i)
              (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb
                ((logSlots j).map (fun i => (e s).symm (.inl i))) : ℝ) : ℂ) *
              movingOriginalPatternMatchedObservable (e s) (trees t) small slot perm
                (fun i => Quotient.mk'' i) primes hprimes p g Dq
                (movingPatternRegularSlots (e s) n m small slot).get (fun i => active (movingPatternTemplateEquiv n r₀ m (e s) i))
                (frequencyRoot n (trees t false))
                (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
                  (movingPatternRegularSlots (e s) n m small slot)) greg f outside
                childBound pivotBound ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center x) x
        Monotone V → f 0 = 0 →
        (Sfreq.card : ℝ) ≤ Real.exp (Cfreq * m) →
        (∀ s t, ‖term t s‖ ≤
          ((2 : ℝ) ^ Fintype.card (Quotient s) *
            (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - Fintype.card (Quotient s))) *
          (Real.exp (-goodPatternGain n Cprior Cfreq gain * m) + err)) →
        ‖movingWeightedMatchedCorrelation p (fun q : primes => (q : ℕ)) outside μ ν
          childBound pivotBound V f g Dq Finset.univ ψ X (Real.exp Δ) hi φ G n small
          (movingPatternBulkLeaves n m slot perm)
          (fun s y x z => wgt y * movingTemplateExternalMultiplier primes hprimes n r₀ m active outside greg s
            φ Jleft Jright diagonal y x z) u v r w center‖ ≤
          Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  filter_upwards [arithmetic_good_pattern_rate n k hk Cprior Cfreq gain hCprior hCfreq] with L hrate
  dsimp only at hrate ⊢
  intro r₀ primes hprimes p _ μ ν childBound pivotBound V f g Dq X Δ hi φ G
    active perm greg outside Jleft Jright diagonal u v r w center cb tlog logSlots N e
  let m := spectatorBulkCount k L
  let small := movingTemplateSmall n r₀ m
  let slot := movingTemplateBulk n r₀ m
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  let Sfreq := (transferFrequencyRange (V n)).erase 0
  let trees := fun (t : FrequencyTree (Sfreq × Sfreq) n) side =>
    frequencyTreeMap Subtype.val n (frequencyPairProjection Sfreq n side t)
  let term := fun (t : FrequencyTree (Sfreq × Sfreq) n) (s : Setoid (Bool × MovingSampleIndex n)) =>
    ∑ x : Fin (N s + 1) → primes,
      movingOriginalPatternWeight (e s) μ ν (fun q : primes => (q : ℕ)) n (fun i => Quotient.mk'' i)
        (fun x => ((∏ j, bulkLogCutoffWeight (fun i => ((x i : ℕ) : ℝ)) cb
                ((logSlots j).map (fun i => (e s).symm (.inl i))) : ℝ) : ℂ) *
              movingOriginalPatternMatchedObservable (e s) (trees t) small slot perm (fun i => Quotient.mk'' i)
          primes hprimes p g Dq (movingPatternRegularSlots (e s) n m small slot).get (fun i => active (movingPatternTemplateEquiv n r₀ m (e s) i))
          (frequencyRoot n (trees t false))
          (fun x => movingRegularOther (fun i => (x i : ℕ)) outside
            (movingPatternRegularSlots (e s) n m small slot)) greg f outside childBound pivotBound
          ψ X (Real.exp Δ) hi φ G Jleft Jright diagonal u v r w center x) x
  intro hV hf hcard hterm
  have hsum := hrate Sfreq hcard (fun s t => (‖term t s‖ : ℂ)) (by
    intro s t
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [add_assoc] using hterm s t)
  have hnonneg : 0 ≤ ∑ s : Setoid (Bool × MovingSampleIndex n),
      ∑ t : FrequencyTree (Sfreq × Sfreq) n, ‖term t s‖ := by positivity
  simp only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hnonneg] at hsum
  have hactual := movingTemplateLogFamilyMatchedCorrelation_pattern_bound primes hprimes outside n r₀
    (spectatorBulkCount k L) perm active p μ ν childBound pivotBound V f hf g Dq ψ X (Real.exp Δ)
    hi φ G greg Jleft Jright diagonal u v r w center cb hV tlog logSlots N e
  apply hactual.trans
  rw [Finset.sum_comm]
  exact hsum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedTemplateHalfLogGood
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete good-matching correlation under original selected harmonic priors -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_template_half_log_good_correlation
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k)
    (A Wwin Bφ Dφ c K gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (active : MovingRegularSlot (n + 2) r₀ m → Bool)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r₀ m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center cb : ℝ)
        (logSlots : Fin tlog → List (MovingRegularSlot (n + 2) r₀ m)),
      let small := movingTemplateSmall (n + 2) r₀ m
      let slot := movingTemplateBulk (n + 2) r₀ m
      let wgt := fun (y : MovingRegularSlot (n + 2) r₀ m → primes) =>
        ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      (∀ j, (logSlots j).length ≤ m) →
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ 1) →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) r₀ m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active (slot j) = true) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j, j < (n + 2) → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingWeightedMatchedCorrelation p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ
        ψ X (Real.exp Δ) hi φ G (n + 2) small (movingPatternBulkLeaves (n + 2) m slot perm)
        (fun s y x z => wgt y * movingTemplateExternalMultiplier primes _hprimes (n + 2) r₀ m active outside
          (normalizedResidueFamily setsReg) s φ Jleft Jright diagonal y x z) uG vG rG sG center‖ ≤
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hCprior : 1 ≤ K + 1 := (selected_harmonic_family_bounds c K hc hK).1
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hprime⟩ :=
    P.movingPattern_half_log_good_selected_masked_priors_rate C hM ψ n r₀ k A Wwin Bφ Dφ c K
      (goodPatternGain (n + 2) (K + 1) A gain) hA hWwin hc hK hBφ hDφ
      Dlog hDlog hloglip tlog htlog
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hprime, movingTemplateLogFamilyMatchedCorrelation_pattern_rate ψ (n + 2) k hk
    A (K + 1) gain hA hCprior] with L hprime hcorr
  dsimp only at hcorr ⊢
  intro tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G active perm global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center cb logSlots
    hslots hV hf0 hf hcard hVn hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
    hm hp hsets hsetsp hpupper hgood hdlo hdhi hβ hbias hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  let m := spectatorBulkCount k L
  let B := MovingRegularSlot (n + 2) r₀ m
  let small := movingTemplateSmall (n + 2) r₀ m
  let slot := movingTemplateBulk (n + 2) r₀ m
  have hsmall := movingTemplateSmall_not_bulk (n + 2) r₀ m
  have hsmallLen := bulkSlotLeaves_length (n + 2) r₀ (fun j : TreeLeafIndex (n + 2) × Fin r₀ => ((j.1, Sum.inl j.2) : B))
  let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex (n + 2))
  let j₀ : TreeLeafIndex (n + 2) × Fin (spectatorBulkCount k L) :=
    ⟨Classical.choice inferInstance, ⟨0, by omega⟩⟩
  obtain ⟨N, e, hNcard⟩ := movingPattern_enumeration B (slot j₀) (n + 2)
  have hdel' (s) : ((global.card + (N s + 1) + outside.length : ℕ) : ℝ) ≤
      Real.exp ((K + 1) * L) := by
    exact (Nat.cast_le.mpr (Nat.add_le_add_right
      (Nat.add_le_add_left (hNcard s) global.card) outside.length)).trans hdel
  apply hcorr r₀ primes hprimes p
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j => primeSubsetPrior primes (Qν j))
    childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq
    X Δ hi φ G active perm (normalizedResidueFamily setsReg) outside Jleft Jright diagonal
    uG vG rG sG center cb tlog logSlots N e hV hf0 hcard
  intro s t
  let rep : ∀ c : Quotient s, {i : Bool × MovingSampleIndex (n + 2) // Quotient.mk'' i = c} :=
    fun c => ⟨c.out, Quotient.out_eq' c⟩
  have hS : ∀ a ∈ Sfreq, a ≠ 0 := fun a ha => (Finset.mem_erase.mp ha).1
  have hN : ∀ a ∈ Sfreq, a.natAbs ≤ V (n + 2) := by
    intro a ha
    exact (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp ha).2
  have hh := hprime (Real.exp Δ) hi (Real.one_le_exp_iff.mpr hΔ) hhi hwindow
    B (Quotient s) (N s) (e s) tierB
    (fun b => frequencyTreeMap Subtype.val (n + 2) (frequencyPairProjection Sfreq (n + 2) b t))
    Sfreq t (V (n + 2)) small slot perm (fun i => Quotient.mk'' i) rep primes hprimes
    childBound pivotBound f outside p Dq sets β primeLo cutoff tier X j₀ φ G global Qμ Qν
    (fun j => (logSlots j).map
      (fun i => (e s).symm (.inl i))) cb
    (fun i => active (movingPatternTemplateEquiv (n + 2) r₀ m (e s) i))
    (frequencyRoot (n + 2) (frequencyTreeMap Subtype.val (n + 2) (frequencyPairProjection Sfreq (n + 2) false t)))
    setsReg Jleft Jright diagonal uG vG rG sG center
    (fun j => by
      rw [List.length_map]
      exact (hslots j).trans (by nlinarith only [Nat.one_le_pow (n + 2) 2 (by omega)]))
    huG hrG huvG hrsG hvG hsG hvcenter (fun _ => hsmall) hB (fun _ => hsmallLen)
    rfl hS hN hf hm hp hsets hsetsp hpupper hgood hdlo hdhi hβ hbias
    hφ hlip hφout hShell (hdel' s) hout hν hμP hνP hμmass hνmass hμrange hνrange
    (fun i hi => movingPatternTemplate_inactive_not_bulk (n + 2) r₀ m (e s) active hactive i hi)
    houtcover hinjp huBig hrBig hVn hμtier hνtier hNlo hNcut hcutlo hloReal hupper hpband
    hdeleteμ hdeletep hdeleteν hdeletebulk
    (hS _ (allFrequencyList_subtype_mem Sfreq (n + 2) (frequencyPairProjection Sfreq (n + 2) false t) _
      (frequencyRoot_mem_allFrequencyList (n + 2) _)))
    (hN _ (allFrequencyList_subtype_mem Sfreq (n + 2) (frequencyPairProjection Sfreq (n + 2) false t) _
      (frequencyRoot_mem_allFrequencyList (n + 2) _))) hsetsReg
  simpa only [add_assoc] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateMaskedSymmetrization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetrization with the actual compensation mask and original leaf coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateExternalMultiplier_nonneg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m : ℕ)
    (active : MovingRegularSlot n r m → Bool) (outside : List ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Jleft Jright : ℝ) (diagonal : Bool) (y : MovingRegularSlot n r m → P) (x z : ℝ) :
    0 ≤ (movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal y x z).re ∧
    ((movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal y x z).re : ℂ) =
      movingTemplateExternalMultiplier P hP n r m active outside greg s φ
        Jleft Jright diagonal y x z := by
  have hc (J t : ℝ) : 0 ≤ positiveLogCutoff φ J t := by
    unfold positiveLogCutoff
    split_ifs
    · exact hφ _
    · exact le_rfl
  let q := fun i => (y i : ℕ)
  let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (y i).property⟩
  let M := naturalRegularMultiplier q active s
    (fun i => ((outside.prod * tupleCofactor q i : ℕ) : ZMod (q i)))
    (fun i => greg (q i)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  have hM : 0 ≤ M := by
    dsimp only [M, naturalRegularMultiplier]
    apply Finset.prod_nonneg
    intro i _
    split_ifs <;> positivity
  let a := positiveLogCutoff φ Jleft (⌊Real.exp x⌋₊ : ℝ)
  let b := positiveLogCutoff φ Jright (⌊Real.exp z⌋₊ : ℝ)
  let d : ℝ := if diagonal then Real.exp Jright / (⌊Real.exp z⌋₊ : ℝ) else 1
  have hd : 0 ≤ d := by dsimp [d]; split_ifs <;> positivity
  have heq : movingTemplateExternalMultiplier P hP n r m active outside greg s φ
      Jleft Jright diagonal y x z = ((a * b * d * M : ℝ) : ℂ) := by
    unfold movingTemplateExternalMultiplier giantOuterWeight
    dsimp only [a, b, d, M, q]
    cases diagonal <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;> push_cast <;> rfl
  rw [heq]
  simpa only [Complex.ofReal_re] using
    And.intro (mul_nonneg (mul_nonneg (mul_nonneg (hc _ _) (hc _ _)) hd) hM)
      (Eq.refl ((a * b * d * M : ℝ) : ℂ))

theorem movingTemplateMaskedSymmetrizedEnergy_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ) (n r m : ℕ) (hm : 1 ≤ m)
    (ν : MovingRegularSlot n r m → P → ℝ) (hν : ∀ j a, 0 ≤ ν j a)
    (hidentical : ∀ j k, ν (movingTemplateBulk n r m j) = ν (movingTemplateBulk n r m k))
    (active : MovingRegularSlot n r m → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n r m j) = true)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v a b center D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : (mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
      (‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s y
        ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal y x z)).re ≤ D)
    (hgood : ∀ e : Equiv.Perm (TreeLeafIndex n × Fin m),
      4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤ 3 * Fintype.card (TreeLeafIndex n) →
      ‖mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
        (movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s y
          ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ *
        star (movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s
          (selectedBulkSample (movingTemplateBulk n r m) e y) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)) *
        movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal y x z)‖ ≤ E) :
    (movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G n r m
      ν active greg Jleft Jright diagonal u v a b center).re ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) * D + E := by
  let C := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
    n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  let W := fun s y x z => movingTemplateExternalMultiplier P hP n r m active outside greg s φ
    Jleft Jright diagonal y x z
  have hwcast (s : ℤ) (y : MovingRegularSlot n r m → P) (x z : ℝ) :
      ((W s y x z).re : ℂ) = W s y x z :=
    (movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ
      hφ Jleft Jright diagonal y x z).2
  have hd : (mixedExternalAverage ν (V n) u v a b center
      (fun s y x z => (‖C s y x z‖ ^ 2 : ℂ) * (W s y x z).re)).re ≤ D := by
    simp_rw [hwcast]
    exact hdiag
  have hg (e : Equiv.Perm (TreeLeafIndex n × Fin m))
      (he : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤ 3 * Fintype.card (TreeLeafIndex n)) :
      ‖mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
        (C s y x z * star (C s (selectedBulkSample (movingTemplateBulk n r m) e y) x z)) *
          (W s y x z).re)‖ ≤ E := by
    simp_rw [hwcast]
    exact hgood e he
  have h := mixedBulkSymmetrize_energy_bound n m hm (movingTemplateBulk n r m) ν hν hidentical
    (V n) u v a b center C (fun s y x z => (W s y x z).re)
    (fun s y x z => (movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ
      hφ Jleft Jright diagonal y x z).1)
    (fun e s y x z => congrArg Complex.re (movingTemplateExternalMultiplier_bulk_action P hP
      n r m active hactive outside greg s φ Jleft Jright diagonal e y x z)) D E hD hE hd hg
  change (mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
    (‖mixedBulkSymmetrize n m (movingTemplateBulk n r m) C s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤ _
  simpa only [hwcast] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateSymmetrizedNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The masked symmetrized energy is a nonnegative real number -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_norm_eq_re {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ j a, 0 ≤ ν j a) (N : ℕ) (u v a b center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hreal : ∀ s y x z, (F s y x z).im = 0)
    (hpos : ∀ s y x z, 0 ≤ (F s y x z).re) :
    ‖mixedExternalAverage ν N u v a b center F‖ =
      (mixedExternalAverage ν N u v a b center F).re := by
  have hi : (mixedExternalAverage ν N u v a b center F).im = 0 := by
    simp only [mixedExternalAverage_finite, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hreal, mul_zero,
      Finset.sum_const_zero]
  have hr : (((mixedExternalAverage ν N u v a b center F).re : ℝ) : ℂ) =
      mixedExternalAverage ν N u v a b center F := by
    apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im, hi]
  rw [← hr, Complex.norm_real, Real.norm_of_nonneg
    (mixedExternalAverage_re_nonneg ν hν N u v a b center F hpos)]
  rfl

theorem movingTemplateMaskedSymmetrizedEnergy_norm_eq_re
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (hν : ∀ j a, 0 ≤ ν j a)
    (active : MovingRegularSlot n r m → Bool) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ) :
    ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G n r m
      ν active greg Jleft Jright diagonal u v a b center‖ =
    (movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G n r m
      ν active greg Jleft Jright diagonal u v a b center).re := by
  unfold movingTemplateMaskedSymmetrizedEnergy
  apply mixedExternalAverage_norm_eq_re ν hν
  · intro s y x z
    have h := (movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ
      hφ Jleft Jright diagonal y x z).2
    rw [← h]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  · intro s y x z
    have h := movingTemplateExternalMultiplier_nonneg P hP n r m active outside greg s φ
      hφ Jleft Jright diagonal y x z
    rw [← h.2]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (sq_nonneg _) h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateLogCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained log weights in the original masked coefficient correlation -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem mixedExternalAverage_support_const_mul {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v a b center : ℝ) (c : ℂ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ y, (∏ j, ν j (y j)) ≠ 0 → ∀ s x z, F s y x z = c * H s y x z) :
    mixedExternalAverage ν N u v a b center F =
      c * mixedExternalAverage ν N u v a b center H := by
  unfold mixedExternalAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : (∏ j, ν j (y j)) = 0
  · simp only [hy, Complex.ofReal_zero, zero_mul, mul_zero]
  · simp_rw [h y hy, complexIntegerInterval_const_mul, complexPrimeInterval_const_mul]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original cutoff weight as a function of the actual leaf data -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem initialRegularFromList_mapped {P : Type*} (b r : ℕ) (fallback : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    initialRegularFromList b r fallback ((movingTemplateSlotList 0 (r + r) (b + b)).map y) = y := by
  funext i
  unfold initialRegularFromList
  rw [List.getD_eq_getElem _ _ (by
    simpa only [List.length_map] using ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i).isLt)]
  rw [List.getElem_map]
  change y ((movingTemplateSlotList 0 (r + r) (b + b)).get
    ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i)) = y i
  rw [← movingTemplateListEquiv_apply, Equiv.apply_symm_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds retained by the two original half-list cutoffs -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialMovingCutoffWeight_norm_le_one {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    ‖initialMovingCutoffWeight value b d r cb cd sl sr y‖ ≤ 1 := by
  have h (x : Fin b → P) (s : Fin d → P) :
      ‖((initialLogSumWeight value cb x * initialLogSumWeight value cd s : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg
      (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))]
    exact (mul_le_mul (initialLogSumWeight_le_one _ _ _) (initialLogSumWeight_le_one _ _ _)
      (initialLogSumWeight_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)
  unfold initialMovingCutoffWeight
  rw [norm_mul]
  exact (mul_le_mul (h _ _) (h _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTreeWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original half-list weights through the complete moving tree -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialMovingRealWeight_cast {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (initialMovingRealWeight value b d r cb cd sl sr y : ℂ) =
      initialMovingCutoffWeight value b d r cb cd sl sr y := by
  exact Complex.ofReal_mul _ _

theorem initialMovingRealWeight_bounds {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    0 ≤ initialMovingRealWeight value b d r cb cd sl sr y ∧
      initialMovingRealWeight value b d r cb cd sl sr y ≤ 1 := by
  have h0 : 0 ≤ initialMovingRealWeight value b d r cb cd sl sr y := by
    unfold initialMovingRealWeight
    exact mul_nonneg (mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))
      (mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))
  refine ⟨h0, ?_⟩
  have h := initialMovingCutoffWeight_norm_le_one value b d r cb cd sl sr y
  rw [← initialMovingRealWeight_cast, Complex.norm_real, Real.norm_of_nonneg h0] at h
  exact h

theorem initialMovingDataCutoff_factor {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    {n : ℕ} (T : MovingSlotData P n) (s : ℤ) :
    initialMovingDataCutoff value b d r cb cd sl sr fallback T s =
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback T.regularSlots) : ℂ) *
        (if s = 0 then 0 else 1) := by
  rw [initialMovingRealWeight_cast]
  unfold initialMovingDataCutoff
  split_ifs <;> simp only [mul_zero, mul_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkLists
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual half-bulk cutoffs are independent of restored small slots -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialRegularFromList_bulk {P : Type*} (b r : ℕ) (fallback : P)
    (small : List P) (hsmall : small.length = r + r)
    (bulk : Fin (b + b) → P) (i : Fin (b + b)) :
    initialRegularFromList b r fallback (small ++ List.ofFn bulk) ((), .inr i) = bulk i := by
  let y : MovingRegularSlot 0 (r + r) (b + b) → P :=
    fun j => Sum.elim (fun z => small.get (Fin.cast hsmall.symm z)) bulk j.2
  have hlist : (movingTemplateSlotList 0 (r + r) (b + b)).map y =
      small ++ List.ofFn bulk := by
    simp only [movingTemplateSlotList, movingTemplateSmall, bulkSlotLeaves,
      treeLeafTupleEquiv, Equiv.coe_fn_symm_mk, flattenMovingSlots, List.map_append,
      List.map_ofFn, Function.comp_def, y, movingTemplateBulk, Sum.elim_inl,
      ]
    congr 1
    exact (List.ofFn_congr hsmall small.get).symm.trans (List.ofFn_get small)
  have h := congrFun (initialRegularFromList_mapped b r fallback y) ((), .inr i)
  simpa only [hlist, y, Sum.elim_inr] using h

theorem initialMovingRealWeight_list {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (small : List P) (hsmall : small.length = r + r) (bulk : Fin (b + b) → P) :
    initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback (small ++ List.ofFn bulk)) =
      initialHalfBulkWeight value b d cb cd sl sr bulk := by
  unfold initialMovingRealWeight initialHalfBulkWeight
  simp only [initialRegularFromList_bulk b r fallback small hsmall bulk]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two half-bulk weights through every moving branch -/
namespace Ostmann
open scoped Classical BigOperators

theorem moving_append_length_eq {P : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List P) n) (a b : ℕ)
    (hx : MovingLeafLengthEq n x a) (hy : MovingLeafLengthEq n y b) :
    MovingLeafLengthEq n (appendMovingSlotLeaves n x y) (a + b) := by
  induction n with
  | zero => exact (List.length_append).trans (congrArg₂ (· + ·) hx hy)
  | succ n ih => exact ⟨ih x.1 y.1 hx.1 hy.1, ih x.2 y.2 hx.2 hy.2⟩

theorem moving_compensation_length_eq {P : Type*} (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → P) n) :
    MovingLeafLengthEq n (movingCompensationSlots n samples) 4 := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih => exact ⟨ih samples.1, ih samples.2⟩

theorem initialMovingTreeWeight_sample {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P) (a : MovingSampleSlots P n)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r) :
    initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small (bulkSlotLeaves n (b + b) slot) a) =
      initialHalfBulkProduct value b d cb cd sl sr n slot := by
  induction a generalizing s with
  | leaf =>
    change initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback ((show List P from small) ++ List.ofFn (fun i => slot ((), i)))) = _
    exact initialMovingRealWeight_list value b d r cb cd sl sr fallback small
      (hsmall.trans (by omega)) _
  | @node n samples left right ihL ihR =>
    have hl : 4 + s + 4 * n = r + r := by omega
    change initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.1
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inl j.1, j.2))) left) *
      initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.2
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inr j.1, j.2))) right) = _
    rw [ihL _ _ _ _ (moving_append_length_eq n _ _ 4 s
      (moving_compensation_length_eq n samples) hsmall.1) hl,
      ihR _ _ _ _ (moving_append_length_eq n _ _ 4 s
        (moving_compensation_length_eq n samples) hsmall.2) hl]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfLogSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact two half-bulk cutoffs as a finite family of log weights -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfBulkProduct_eq_prod {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (n : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → P) :
    initialHalfBulkProduct value b d cb cd sl sr n slot =
      ∏ j : TreeLeafIndex n, initialHalfBulkWeight value b d cb cd sl sr (fun i => slot (j, i)) := by
  induction n with
  | zero =>
    change _ = ∏ j : Unit, initialHalfBulkWeight value b d cb cd sl sr (fun i => slot (j, i))
    simp only [Fintype.prod_unique, initialHalfBulkProduct]
  | succ n ih =>
    change initialHalfBulkProduct value b d cb cd sl sr n (fun j => slot (.inl j.1, j.2)) *
      initialHalfBulkProduct value b d cb cd sl sr n (fun j => slot (.inr j.1, j.2)) =
      ∏ j : TreeLeafIndex n ⊕ TreeLeafIndex n,
        initialHalfBulkWeight value b d cb cd sl sr (fun i => slot (j, i))
    rw [Fintype.prod_sum_type, ih, ih]

theorem initialLogSumWeight_eq_cutoff {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b : ℕ) (cb : ℝ) (x : Fin b → P) :
    initialLogSumWeight value cb x =
      bulkLogCutoffWeight (fun p => (value p : ℝ)) cb (List.ofFn x) := by
  have hp : 0 < ∏ i, (value (x i) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hvalue (x i))
  unfold bulkLogCutoffWeight realSlotProduct
  rw [List.map_ofFn, List.prod_ofFn]
  unfold positiveLogCutoff
  simp only [Function.comp_def]
  rw [ite_eq_left hp, Real.log_prod (fun i _ => by exact_mod_cast (hvalue (x i)).ne')]
  rfl

theorem initialHalfLogSlots_length {B : Type*} (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) (j : Fin (2 ^ n + 2 ^ n)) :
    (initialHalfLogSlots n b slot j).length ≤ b :=
  movingBulkPairedCutoffSlots_length n b _ (fun _ => bulkSlotLeaves_length n b _) j

theorem initialHalfBulkProduct_log_slots {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (n : ℕ) (slot : TreeLeafIndex n × Fin (b + b) → P) :
    initialHalfBulkProduct value b d cb cd sl sr n slot =
      (initialLogSumWeight value cd sl * initialLogSumWeight value cd sr) ^ (2 ^ n) *
      ∏ j, bulkLogCutoffWeight (fun p => (value p : ℝ)) cb (initialHalfLogSlots n b slot j) := by
  rw [initialHalfBulkProduct_eq_prod]
  unfold initialHalfLogSlots
  rw [movingBulkPairedCutoffSlots_product]
  simp only [initialHalfBulkLeaves, treeLeafProduct_eq_prod, treeLeafTupleEquiv_map,
    bulkSlotLeaves, Equiv.apply_symm_apply, Bool.false_eq_true, ↓reduceIte]
  simp_rw [← initialLogSumWeight_eq_cutoff value hvalue]
  simp only [initialHalfBulkWeight, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, card_treeLeafIndex, mul_pow]
  ring

theorem initialPairedHalfLogSlots_length {B : Type*} (n b : ℕ)
    (slot : Bool → TreeLeafIndex n × Fin (b + b) → B)
    (j : Fin ((2 ^ n + 2 ^ n) + (2 ^ n + 2 ^ n))) :
    (initialPairedHalfLogSlots n b slot j).length ≤ b := by
  refine Fin.addCases ?_ ?_ j <;> intro i
  · simpa only [initialPairedHalfLogSlots, Fin.append_left] using
      initialHalfLogSlots_length n b (slot false) i
  · simpa only [initialPairedHalfLogSlots, Fin.append_right] using
      initialHalfLogSlots_length n b (slot true) i

theorem initialHalfBulkProduct_pair_log_slots {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (n : ℕ) (slot : Bool → TreeLeafIndex n × Fin (b + b) → P) :
    (initialHalfBulkProduct value b d cb cd sl sr n (slot false) : ℂ) *
      star (initialHalfBulkProduct value b d cb cd sl sr n (slot true) : ℂ) =
    ((initialLogSumWeight value cd sl * initialLogSumWeight value cd sr) ^
      (2 ^ n + 2 ^ n) : ℝ) *
      ((∏ j, bulkLogCutoffWeight (fun p => (value p : ℝ)) cb
        (initialPairedHalfLogSlots n b slot j) : ℝ) : ℂ) := by
  rw [initialHalfBulkProduct_log_slots value hvalue b d cb cd sl sr n (slot false),
    initialHalfBulkProduct_log_slots value hvalue b d cb cd sl sr n (slot true)]
  simp only [initialPairedHalfLogSlots, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    Complex.ofReal_mul, Complex.star_def, map_mul, Complex.conj_ofReal, pow_add]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialHalfLogMap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the original half-cutoff lists without changing their weights -/
namespace Ostmann
open scoped Classical

theorem initialHalfBulkLeaves_map {B C : Type*} (g : B → C) (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) (side : Bool) :
    initialHalfBulkLeaves n b (g ∘ slot) side =
      treeLeafMap (List.map g) n (initialHalfBulkLeaves n b slot side) := by
  unfold initialHalfBulkLeaves
  rw [bulkSlotLeaves_map]
  rfl

theorem initialHalfLogSlots_map {B C : Type*} (g : B → C) (n b : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → B) (j : Fin (2 ^ n + 2 ^ n)) :
    initialHalfLogSlots n b (g ∘ slot) j = (initialHalfLogSlots n b slot j).map g := by
  unfold initialHalfLogSlots
  have he : initialHalfBulkLeaves n b (g ∘ slot) =
      fun side => treeLeafMap (List.map g) n (initialHalfBulkLeaves n b slot side) := by
    funext side
    exact initialHalfBulkLeaves_map g n b slot side
  rw [he]
  exact movingBulkPairedCutoffSlots_map n (initialHalfBulkLeaves n b slot) g j

theorem initialPairedHalfLogSlots_map {B C : Type*} (g : B → C) (n b : ℕ)
    (slot : Bool → TreeLeafIndex n × Fin (b + b) → B)
    (j : Fin ((2 ^ n + 2 ^ n) + (2 ^ n + 2 ^ n))) :
    initialPairedHalfLogSlots n b (fun side => g ∘ slot side) j =
      (initialPairedHalfLogSlots n b slot j).map g := by
  refine Fin.addCases ?_ ?_ j <;> intro i
  · simpa only [initialPairedHalfLogSlots, Fin.append_left] using
      initialHalfLogSlots_map g n b (slot false) i
  · simpa only [initialPairedHalfLogSlots, Fin.append_right] using
      initialHalfLogSlots_map g n b (slot true) i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingRecursiveWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring terminal bulk weights from the original recursion -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The logarithmic bulk cutoffs are independent of every reconstructed
pivot and survive the right-branch conjugations unchanged. -/
theorem movingSlotWeight_initial_halves {σ : Type*} (value : σ → ℕ) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → σ) (fallback : σ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (cutoff : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
          (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
        cutoff n ⟨n, T, XL, XR⟩ t =
      (initialMovingTreeWeight value b d r cb cd sl sr fallback T : ℂ) *
        recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
          F cutoff n ⟨n, T, XL, XR⟩ t := by
  induction T generalizing XL XR with
  | leaf => rfl
  | @node n s CL CR U left right ihL ihR =>
    simp only [recursiveTransferWeight]
    split_ifs
    · simp only [movingSlotSystem, MovingSlotState.child, ite_true, if_true,
        Bool.false_eq_true, ite_false, if_false] at ihL ihR ⊢
      rw [ihL, ihR]
      simp only [initialMovingTreeWeight,
        Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    · exact (mul_zero _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingCoefficientFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact half-bulk factorization under the unchanged compensation law -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampleTerm_initial_halves {P : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List P) n)
    (XL XR : ℕ) (a : MovingSampleSlots P n) :
    movingSupportedSampleTerm value outside childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small bulk XL XR a =
    (initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small bulk a) : ℂ) *
      movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR a := by
  unfold movingSupportedSampleTerm
  rw [movingSlotWeight_initial_halves]
  unfold movingSupportedWeight
  split_ifs
  · rfl
  · exact (mul_zero _).symm

theorem movingSupportedSampledWeight_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedSampleTerm_initial_halves,
    initialMovingTreeWeight_sample value b d r cb cd sl sr fallback n s t small slot a hsmall hlen]
  ring

theorem movingFrequencyCoefficient_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n a : ℕ) (s : ℤ) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r)
    (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  unfold movingFrequencyCoefficient
  simp only [movingSupportedSampledWeight_initial_halves value b d r cb cd sl sr fallback
    outside μ childBound pivotBound F _ n a _ small slot hsmall hlen XL XR, Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingOriginalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring the genuine half-list weights in the original Fourier coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalLeaf_initial_halves {P I : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (x : MovingSlotState P) (s : ℤ) :
    movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi x s =
    (initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  dsimp only
  rw [initialMovingDataCutoff_factor]
  split_ifs <;> ring

theorem movingFrequencyCoefficient_original_initial_halves {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR := by
  have he : movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi = fun x s =>
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
    funext x s
    exact movingOriginalLeaf_initial_halves value b d r cb cd sl sr fallback q g Dq S ψ X lo hi x s
  rw [he]
  exact movingFrequencyCoefficient_initial_halves value b d r cb cd sl sr fallback outside μ
    childBound pivotBound V _ φ G n a s small slot hsmall hlen XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingCoefficientPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact retained half-bulk factors in a pair of Fourier coefficients -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalCoefficientPair_initial_halves {P J : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : Bool → TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    let plain := fun side => movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
      φ G n s small (bulkSlotLeaves n (b + b) (slot side)) XL XR
    let weighted := fun side => movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) (slot side)) XL XR
    weighted false * star (weighted true) =
      ((initialLogSumWeight value cd sl * initialLogSumWeight value cd sr) ^
        (2 ^ n + 2 ^ n) : ℝ) *
      ((∏ j, bulkLogCutoffWeight (fun p => (value p : ℝ)) cb
        (initialPairedHalfLogSlots n b slot j) : ℝ) : ℂ) *
      (plain false * star (plain true)) := by
  dsimp only
  rw [movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s small (slot false) hsmall hlen XL XR,
    movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s small (slot true) hsmall hlen XL XR,
    star_mul]
  have hp := initialHalfBulkProduct_pair_log_slots value hvalue b d cb cd sl sr n slot
  let C := fun side => movingFrequencyCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
    φ G n s small (bulkSlotLeaves n (b + b) (slot side)) XL XR
  calc
    _ = ((initialHalfBulkProduct value b d cb cd sl sr n (slot false) : ℂ) *
        star (initialHalfBulkProduct value b d cb cd sl sr n (slot true) : ℂ)) *
        (C false * star (C true)) := by dsimp only [C]; ring
    _ = _ := by rw [hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTemplateProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic product bounds from the literal two-half initial weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingLeafLengthEq_map {P Q : Type*} (f : P → Q) (n : ℕ)
    (x : TreeLeafTuple (List P) n) (a : ℕ) (hx : MovingLeafLengthEq n x a) :
    MovingLeafLengthEq n (treeLeafMap (List.map f) n x) a := by
  induction n with
  | zero => simpa only [MovingLeafLengthEq, treeLeafMap, List.length_map] using hx
  | succ n ih => exact ⟨ih x.1 hx.1, ih x.2 hx.2⟩

theorem bulkSlotLeaves_length_eq {P : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → P) :
    MovingLeafLengthEq n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih =>
    change MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingLogCorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal half-cutoff correlation under the original regular law -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplate_initial_log_correlation_eq
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n a b d r : ℕ)
    (hlen : a + 4 * n = r + r) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n a (b + b) → P → ℝ)
    (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ)
    (childBound pivotBound V : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (active : MovingRegularSlot n a (b + b) → Bool)
    (greg : ∀ p : ℕ, ZMod p → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v w z center : ℝ) (perm : Equiv.Perm (TreeLeafIndex n × Fin (b + b))) :
    let slot := movingTemplateBulk n a (b + b)
    let bulk := movingPatternBulkLeaves n (b + b) slot perm
    let slots := fun side => if side then slot ∘ perm.symm else (slot : _ → _)
    let logSlots := initialPairedHalfLogSlots n b slots
    let leaf := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback) g Dq Finset.univ ψ X lo hi
    let coeff := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      leaf φ G n a (b + b) s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    let W := fun s => movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
      Jleft Jright diagonal
    let wgt := fun (y : MovingRegularSlot n a (b + b) → P) =>
      ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
    mixedExternalAverage ν (V n) u v w z center (fun s y x z =>
      (coeff s y x z * star (coeff s (selectedBulkSample slot perm y) x z)) * W s y x z) =
    ((initialLogSumWeight Subtype.val cd sl * initialLogSumWeight Subtype.val cd sr) ^
      (2 ^ n + 2 ^ n) : ℝ) *
      movingWeightedMatchedCorrelation q Subtype.val outside μ ν childBound pivotBound V
        (fun s => if s = 0 then 0 else 1) g Dq Finset.univ ψ X lo hi φ G n
        (movingTemplateSmall n a (b + b)) bulk (fun s y x z => wgt y * W s y x z) u v w z center := by
  intro slot bulk slots logSlots leaf coeff W wgt
  let plain := fun side (s : ℤ) (y : MovingRegularSlot n a (b + b) → P) (x z : ℝ) =>
    movingFrequencyCoefficient Subtype.val outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q (fun _ s => if s = 0 then 0 else 1)
        g Dq Finset.univ ψ X lo hi) φ G n s
      (treeLeafMap (List.map y) n (movingTemplateSmall n a (b + b)))
      (treeLeafMap (List.map y) n (bulk side)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  change mixedExternalAverage ν (V n) u v w z center _ = _ *
    mixedExternalAverage ν (V n) u v w z center
      (fun s y x z => (plain false s y x z * star (plain true s y x z)) * (wgt y * W s y x z))
  apply mixedExternalAverage_support_const_mul
  intro y _ s x z
  have hp := movingOriginalCoefficientPair_initial_halves Subtype.val
    (fun p : P => (hP _ p.property).pos) b d r cb cd sl sr fallback q g Dq Finset.univ
    ψ X lo hi outside μ childBound pivotBound V φ G n a s
    (treeLeafMap (List.map y) n (movingTemplateSmall n a (b + b)))
    (fun side => y ∘ slots side)
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  dsimp only [coeff, leaf, plain, W, wgt, slot, bulk]
  unfold movingTemplateCoefficient
  rw [movingFrequencyCoefficient_bulk_action Subtype.val outside μ childBound pivotBound V _ φ G
    n (b + b) s (movingTemplateSmall n a (b + b)) (movingTemplateBulk n a (b + b)) perm y
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ (movingTemplateSmall_not_bulk n a (b + b))]
  simp only [movingPatternBulkLeaves, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, bulkSlotLeaves_map]
  have hlogs (j) : initialPairedHalfLogSlots n b (fun side => y ∘ slots side) j =
      (logSlots j).map y := initialPairedHalfLogSlots_map y n b slots j
  dsimp only [slots, slot] at hp hlogs
  simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] at hp
  rw [hp]
  simp_rw [hlogs]
  simp only [bulkLogCutoffWeight_map, Function.comp_def]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalSupportedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing energies on the support of the original external law -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_square_mono_support {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ j a, 0 ≤ ν j a) (N : ℕ) (u v a b center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ s y x z, 0 ≤ W s y x z)
    (hFH : ∀ y, (∏ j, ν j (y j)) ≠ 0 → ∀ s x z, ‖F s y x z‖ ≤ ‖H s y x z‖) :
    (mixedExternalAverage ν N u v a b center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤
    (mixedExternalAverage ν N u v a b center
      (fun s y x z => (‖H s y x z‖ ^ 2 : ℂ) * W s y x z)).re := by
  simp only [mixedExternalAverage_finite, ← Complex.ofReal_pow, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : (∏ j, ν j (x.2.1 j)) = 0
  · simp only [mixedExternalPrior, hx, zero_mul, le_refl]
  · apply mul_le_mul_of_nonneg_left _ (mixedExternalPrior_nonneg ν hν N u v a b center x)
    apply mul_le_mul_of_nonneg_right _ (hW _ _ _ _)
    exact pow_le_pow_left₀ (norm_nonneg _) (hFH x.2.1 hx _ _ _) 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing only the nonnegative diagonal's actual half-cutoff weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem initialHalfBulkWeight_bounds {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (bulk : Fin (b + b) → P) :
    0 ≤ initialHalfBulkWeight value b d cb cd sl sr bulk ∧
      initialHalfBulkWeight value b d cb cd sl sr bulk ≤ 1 := by
  exact initialMovingRealWeight_bounds value b d 0 cb cd sl sr
    (fun j => Sum.elim Fin.elim0 bulk j.2)

theorem initialHalfBulkProduct_bounds {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (n : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → P) :
    0 ≤ initialHalfBulkProduct value b d cb cd sl sr n slot ∧
      initialHalfBulkProduct value b d cb cd sl sr n slot ≤ 1 := by
  induction n with
  | zero => exact initialHalfBulkWeight_bounds value b d cb cd sl sr _
  | succ n ih =>
    obtain ⟨hl, hl1⟩ := ih (fun j => slot (.inl j.1, j.2))
    obtain ⟨hr, hr1⟩ := ih (fun j => slot (.inr j.1, j.2))
    exact ⟨mul_nonneg hl hr, (mul_le_mul hl1 hr1 hr zero_le_one).trans_eq (one_mul 1)⟩

theorem movingTemplateCoefficient_original_initial_norm_le {P J : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (y : MovingRegularSlot n a (b + b) → P) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    ‖movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s y XL XR‖ ≤
    ‖movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n a (b + b) s y XL XR‖ := by
  unfold movingTemplateCoefficient
  rw [bulkSlotLeaves_map]
  rw [movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s
    (treeLeafMap (List.map y) n (movingTemplateSmall n a (b + b)))
    (y ∘ movingTemplateBulk n a (b + b))
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen XL XR,
    norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (initialHalfBulkProduct_bounds value b d cb cd sl sr n _).1]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (initialHalfBulkProduct_bounds value b d cb cd sl sr n _).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingSymmetrizedEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetrized energy with both original half-cutoffs retained -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplate_initial_symmetrized_energy_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n a b d r : ℕ)
    (hm : 1 ≤ b + b) (hlen : a + 4 * n = r + r)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) (outside : List ℕ)
    (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n a (b + b) → P → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p)
    (hidentical : ∀ j l, ν (movingTemplateBulk n a (b + b) j) =
      ν (movingTemplateBulk n a (b + b) l))
    (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ)
    (childBound pivotBound V : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (active : MovingRegularSlot n a (b + b) → Bool)
    (hactive : ∀ j, active (movingTemplateBulk n a (b + b) j) = true)
    (greg : ∀ p : ℕ, ZMod p → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v w z center D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : ‖mixedExternalAverage ν (V n) u v w z center (fun s y x z =>
      (‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val q (fun _ s => if s = 0 then 0 else 1)
          g Dq Finset.univ ψ X lo hi) φ G n a (b + b) s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
        Jleft Jright diagonal y x z)‖ ≤ D)
    (hgood : ∀ perm : Equiv.Perm (TreeLeafIndex n × Fin (b + b)),
      4 * Fintype.card (arrangementGraph (b + b) perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex n) →
      let slot := movingTemplateBulk n a (b + b)
      let bulk := movingPatternBulkLeaves n (b + b) slot perm
      let slots := fun side => if side then slot ∘ perm.symm else (slot : _ → _)
      let logSlots := initialPairedHalfLogSlots n b slots
      let wgt := fun (y : MovingRegularSlot n a (b + b) → P) =>
        ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
      ‖movingWeightedMatchedCorrelation q Subtype.val outside μ ν childBound pivotBound V
        (fun s => if s = 0 then 0 else 1) g Dq Finset.univ ψ X lo hi φ G n
        (movingTemplateSmall n a (b + b)) bulk (fun s y x z => wgt y *
          movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
            Jleft Jright diagonal y x z) u v w z center‖ ≤ E) :
    ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
        g Dq Finset.univ ψ X lo hi) φ G n a (b + b) ν active greg
      Jleft Jright diagonal u v w z center‖ ≤
    (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
      Real.exp ((2 ^ n : ℝ) * ((b + b : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) * D + E := by
  let F : MovingSlotState P → ℤ → ℂ := movingOriginalLeaf Subtype.val q (fun _ s => if s = 0 then 0 else 1)
    g Dq Finset.univ ψ X lo hi
  let Fw : MovingSlotState P → ℤ → ℂ := movingOriginalLeaf Subtype.val q
    (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback) g Dq Finset.univ ψ X lo hi
  rw [movingTemplateMaskedSymmetrizedEnergy_norm_eq_re P hP outside μ childBound pivotBound V
    Fw φ hφ G n a (b + b) ν hν active greg Jleft Jright diagonal u v w z center]
  apply movingTemplateMaskedSymmetrizedEnergy_bound P hP outside μ childBound pivotBound V Fw
    φ hφ G n a (b + b) hm ν hν hidentical active hactive greg
    Jleft Jright diagonal u v w z center D E hD hE
  · have hw (s : ℤ) (y : MovingRegularSlot n a (b + b) → P) (x z : ℝ) :
        ((movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
          Jleft Jright diagonal y x z).re : ℂ) =
        movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
          Jleft Jright diagonal y x z :=
      (movingTemplateExternalMultiplier_nonneg P hP n a (b + b) active outside greg s φ hφ
        Jleft Jright diagonal y x z).2
    have h := mixedExternalAverage_square_mono_support ν hν (V n) u v w z center
      (fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V Fw
        φ G n a (b + b) s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)
      (fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F
        φ G n a (b + b) s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)
      (fun s y x z => (movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
        Jleft Jright diagonal y x z).re)
      (fun s y x z => (movingTemplateExternalMultiplier_nonneg P hP n a (b + b) active outside greg s φ hφ
        Jleft Jright diagonal y x z).1)
      (fun y _ s x z => movingTemplateCoefficient_original_initial_norm_le Subtype.val b d r cb cd
        sl sr fallback q g Dq Finset.univ ψ X lo hi outside μ childBound pivotBound V φ G n a s y
        hlen ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)
    simp only [hw] at h
    exact h.trans ((Complex.re_le_norm _).trans hdiag)
  · intro perm hperm
    have he := movingTemplate_initial_log_correlation_eq P hP n a b d r hlen cb cd sl sr fallback
      outside μ ν q g Dq childBound pivotBound V ψ X lo hi φ G active greg Jleft Jright diagonal
      u v w z center perm
    rw [he, norm_mul]
    have h0 := mul_nonneg (initialLogSumWeight_nonneg Subtype.val cd sl)
      (initialLogSumWeight_nonneg Subtype.val cd sr)
    have h1 : initialLogSumWeight Subtype.val cd sl * initialLogSumWeight Subtype.val cd sr ≤ 1 :=
      (mul_le_mul (initialLogSumWeight_le_one Subtype.val cd sl)
        (initialLogSumWeight_le_one Subtype.val cd sr)
        (initialLogSumWeight_nonneg Subtype.val cd sr) zero_le_one).trans_eq (one_mul 1)
    have hfac : ‖((initialLogSumWeight Subtype.val cd sl * initialLogSumWeight Subtype.val cd sr) ^
        (2 ^ n + 2 ^ n) : ℝ)‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (pow_nonneg h0 _)]
      exact pow_le_one₀ h0 h1
    rw [Complex.norm_real]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfac).trans (hgood perm hperm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSelectedInitialSymmetrization
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full bulk symmetrization under the actual selected harmonic priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_symmetrized_energy_oai
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (active : MovingRegularSlot (n + 2) r₀ m → Bool)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r₀ m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center cb cd : ℝ),
      let slot := movingTemplateBulk (n + 2) r₀ m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      r₀ + 4 * (n + 2) = r + r →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i, (n + 2) ≤ tierB i) →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) r₀ m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active (slot j) = true) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j, j < n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      ‖movingTemplateMaskedSymmetrizedEnergy primes _hprimes outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r₀ m ν active (normalizedResidueFamily setsReg)
        Jleft Jright diagonal uG vG rG sG center‖ ≤
      (((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hgood⟩ :=
    P.moving_selected_template_half_log_good_correlation C hM ψ n r₀ k hk A Wwin Bφ Dφ c K gain
      hA hWwin hBφ hDφ hc hK Dlog hDlog hloglip
      ((2 ^ (n + 2) + 2 ^ (n + 2)) + (2 ^ (n + 2) + 2 ^ (n + 2))) (by omega)
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hgood, P.moving_selected_template_diagonal_energy C hM ψ (n + 2) r₀ k hk hn
    A Wwin Bφ Dφ c K εdiag hA hWwin hBφ hDφ hc hK hεdiag hdepth] with L hg hd
  intro b hsize
  rw [hsize] at hg hd
  dsimp only at hg hd ⊢
  intro tierB primes hprimes _ d r sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center cb cd
    hlen hV hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  let m := b + b
  let μ := fun j => primeSubsetPrior primes (Qμ j)
  let ν := fun j => primeSubsetPrior primes (Qν j)
  have hlocal := hμtier
  let f : ℤ → ℂ := fun s => if s = 0 then 0 else 1
  have hf0 : f 0 = 0 := by simp [f]
  have hfnorm (s : ℤ) : ‖f s‖ ≤ 1 := by simp only [f]; split_ifs <;> simp
  have hdiagonal := hd tierB primes hprimes childBound pivotBound V (movingCompactLeaf (V 0)) outside p Dq sets
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
    hV (movingCompactLeaf_zero _) (movingCompactLeaf_norm _) hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
    (by omega) (fun i => hpc.trans (hp i)) hsets hsetsp hpupper hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp huBig hrBig hlocal hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg
  change ‖mixedExternalAverage ν (V (n + 2)) uG vG rG sG center
    (fun s y x z =>
      (‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p (fun _ => movingCompactLeaf (V 0))
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r₀ m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
        movingTemplateExternalMultiplier primes hprimes (n + 2) r₀ m active outside
          (normalizedResidueFamily setsReg) s φ Jleft Jright diagonal y x z)‖ ≤ _ at hdiagonal
  rw [← movingTemplate_compact_energy Subtype.val p outside μ childBound pivotBound V
    (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi φ G
    (n + 2) r₀ m ν
    (fun s y x z => movingTemplateExternalMultiplier primes hprimes (n + 2) r₀ m active outside
      (normalizedResidueFamily setsReg) s φ Jleft Jright diagonal y x z)
    uG vG rG sG center] at hdiagonal
  let slot := movingTemplateBulk (n + 2) r₀ m
  let slots (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m)) (side : Bool) :=
    if side then slot ∘ perm.symm else (slot : _ → _)
  have hpairs (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
      (hperm : 4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2))) :=
    hg tierB primes hprimes childBound pivotBound V f outside p Dq sets β
      primeLo cutoff tier X Δ hi φ G active perm global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center cb (initialPairedHalfLogSlots (n + 2) b (slots perm))
      (fun j => (initialPairedHalfLogSlots_length _ _ _ j).trans (by omega)) hV hf0 hfnorm hcard hVn hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
      hm hp hsets hsetsp hpupper hperm hdlo hdhi hβ hbias hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
      hμrange hνrange hactive houtcover hinjp huBig hrBig hlocal hνtier hNlo hNcut hcutlo hloReal
      hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have h := movingTemplate_initial_symmetrized_energy_bound primes hprimes (n + 2) r₀ b d r hm hlen
    cb cd sl sr fallback outside μ ν (fun j q => primeSubsetPrior_nonneg primes (Qν j) q)
    (fun j l => by dsimp only [ν]; rw [hν j, hν l])
    p (fun i => normalizedResidueTransform (sets i)) Dq childBound pivotBound V ψ X (Real.exp Δ) hi
    φ hφpos G active hactive (normalizedResidueFamily setsReg) Jleft Jright diagonal uG vG rG sG center _ _
    (by positivity) (by positivity) hdiagonal hpairs
  simpa only [add_assoc] using h

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy_oai := @OAI.Ostmann.PublishedProgressionInput.moving_selected_initial_symmetrized_energy_oai
