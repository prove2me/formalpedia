-- Prove2me | solution 1 for OAI.TwoPointCorrelations.minor_arc_bilinear_fourth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:39:07.54369+00:00
-- url     : https://prove2.me/submissions/c9f3fd6f-eac2-4c62-9958-a415cffaee47

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical








lemma additiveCharacter_nat_add (α : ℝ) (m n : ℕ) :
    additiveCharacter α (m + n) = additiveCharacter α m * additiveCharacter α n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_additiveCharacter (α : ℝ) (n : ℕ) : ‖additiveCharacter α n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcGeometric
namespace OAI

/-! Literal interval exponential sums used in the minor-arc fourth moment. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

lemma additiveCharacter_pow (α : ℝ) (n : ℕ) :
    additiveCharacter α n = additiveCharacter α 1 ^ n := by
  induction n with
  | zero => simp [additiveCharacter]
  | succ n ih => rw [additiveCharacter_nat_add, ih, pow_succ]

lemma minor_arc_unit_geometric {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  by_cases hab : a ≤ b
  · have he := congrArg norm (geom_sum_Ico_mul z hab)
    rw [norm_mul] at he
    have hnorm : ‖z ^ b - z ^ a‖ ≤ 2 := by
      simpa only [norm_pow, hz, one_pow, one_add_one_eq_two] using norm_sub_le (z ^ b) (z ^ a)
    exact (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz1))).mpr (he.trans_le hnorm)
  · simp [Ico_eq_empty_of_le (le_of_not_ge hab)]
    positivity


lemma minor_arc_geometric_bound (α : ℝ) (a b : ℕ) :
    ‖∑ n ∈ Ico a b, additiveCharacter α n‖ ≤
      minorArcGeometricBound ((b - a : ℕ) : ℝ) α := by
  have htriv : ‖∑ n ∈ Ico a b, additiveCharacter α n‖ ≤ ((b - a : ℕ) : ℝ) := by
    apply (norm_sum_le _ _).trans
    simp only [norm_additiveCharacter, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    exact le_rfl
  unfold minorArcGeometricBound
  split_ifs with hz
  · exact htriv
  · apply le_min htriv
    have h := minor_arc_unit_geometric (norm_additiveCharacter α 1) hz a b
    have he : (∑ n ∈ Ico a b, additiveCharacter α n) =
        ∑ n ∈ Ico a b, additiveCharacter α 1 ^ n :=
      sum_congr rfl (fun n _ => additiveCharacter_pow α n)
    rw [← he] at h
    exact h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcFourthExpansion
namespace OAI

/-! Exact finite fourth-moment expansion, before any sieve or rational
approximation is used. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.ComplexConjugate

lemma minor_arc_fourth_power (z : ℂ) :
    ‖z‖ ^ 4 = (z * z * conj z * conj z).re := by
  rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma minor_arc_fourth_sum {ι : Type*} (P : Finset ι) (f : ι → ℂ) :
    ‖∑ p ∈ P, f p‖ ^ 4 =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        (f p₁ * f p₂ * conj (f p₃) * conj (f p₄)).re := by
  have h₂ : (∑ p ∈ P, f p) * (∑ p ∈ P, f p) =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, f p₁ * f p₂ := sum_mul_sum _ _ _ _
  have h₃ : (∑ p ∈ P, f p) * (∑ p ∈ P, f p) * conj (∑ p ∈ P, f p) =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, f p₁ * f p₂ * conj (f p₃) := by
    rw [h₂, map_sum]
    simp only [sum_mul]
    simp only [mul_sum]
  rw [minor_arc_fourth_power, h₃, map_sum]
  simp only [sum_mul]
  simp only [mul_sum, Complex.re_sum]

lemma minor_arc_fourth_moment_expansion {ι : Type*} (P : Finset ι)
    (S : Finset ℕ) (f : ι → ℕ → ℂ) :
    (∑ m ∈ S, ‖∑ p ∈ P, f p m‖ ^ 4) =
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        (∑ m ∈ S, f p₁ m * f p₂ m * conj (f p₃ m) * conj (f p₄ m)).re := by
  simp_rw [minor_arc_fourth_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p₁ _
  rw [sum_comm]
  apply sum_congr rfl
  intro p₂ _
  rw [sum_comm]
  apply sum_congr rfl
  intro p₃ _
  rw [sum_comm]
  apply sum_congr rfl
  intro p₄ _
  rw [Complex.re_sum]

lemma minor_arc_fourth_moment_bound {ι : Type*} (P : Finset ι)
    (S : Finset ℕ) (f : ι → ℕ → ℂ) :
    (∑ m ∈ S, ‖∑ p ∈ P, f p m‖ ^ 4) ≤
      ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        ‖∑ m ∈ S, f p₁ m * f p₂ m * conj (f p₃ m) * conj (f p₄ m)‖ := by
  rw [minor_arc_fourth_moment_expansion]
  repeat' apply sum_le_sum fun _ _ => ?_
  exact Complex.re_le_norm _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcKernelSymmetry
namespace OAI

/-! Positivity and reflection symmetry of the resonant-safe geometric kernel. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.ComplexConjugate

lemma minor_arc_geometric_nonneg {L : ℝ} (hL : 0 ≤ L) (α : ℝ) :
    0 ≤ minorArcGeometricBound L α := by
  unfold minorArcGeometricBound
  split_ifs
  · exact hL
  · exact le_min hL (by positivity)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcOriginGeometry
namespace OAI

/-! Discrete interval origins: simultaneous prime windows occupy only a
bounded number of origins once the first origin is fixed. -/

namespace TwoPointCorrelations

open _root_.Finset

/-- For factors in a dyadic block, all other origins lie within three
interval lengths of the scaled first origin. This also applies to factors
`d*p`, so the same geometry survives the multiplicative correction. -/
lemma minor_arc_origin_bounds (A B H k l m : ℕ) (hA : 0 < A)
    (hB : B ≤ 2 * A) (hk : k < A * m ∧ A * m ≤ k + H)
    (hl : l < B * m ∧ B * m ≤ l + H) :
    (B * k) / A - H ≤ l ∧ l ≤ (B * k) / A + 2 * H := by
  let c := (B * k) / A
  have hlo : A * c ≤ B * k := Nat.mul_div_le _ _
  have hhi : B * k < A * (c + 1) := Nat.lt_mul_div_succ _ hA
  have hlow : c ≤ B * m := by
    by_cases hB0 : B = 0
    · simp [c, hB0]
    · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      have hmul : A * c < A * (B * m) := by nlinarith [hk.1]
      exact (Nat.le_of_lt ((Nat.mul_lt_mul_left hA).mp hmul))
  constructor
  · change c - H ≤ l
    omega
  · change l ≤ c + 2 * H
    have hmul₁ : A * l < A * (B * m) := Nat.mul_lt_mul_of_pos_left hl.1 hA
    have hmul₂ : A * (B * m) ≤ B * k + B * H := by
      nlinarith [hk.2]
    have hmul₃ : B * H ≤ 2 * A * H := Nat.mul_le_mul_right H hB
    have hmul : A * l < A * (c + 2 * H + 1) := by nlinarith
    have := (Nat.mul_lt_mul_left hA).mp hmul
    omega


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcOriginCount
namespace OAI

/-! The support of four simultaneous short windows has size `O(X H³)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_origin_interval_card (c H : ℕ) :
    (Icc (c - H) (c + 2 * H)).card ≤ 3 * H + 1 := by
  rw [Nat.card_Icc]
  omega

/-- Only the first origin costs `X`; each of the other three origins
costs at most `3H+1`, independently of the prime quadruple. -/
theorem minor_arc_origin_quadruples (X H A B C D : ℕ) (hA : 0 < A)
    (hB : B ≤ 2 * A) (hC : C ≤ 2 * A) (hD : D ≤ 2 * A)
    (T : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hT : ∀ v ∈ T, v.1.1 < X ∧ ∃ m : ℕ,
      (v.1.1 < A * m ∧ A * m ≤ v.1.1 + H) ∧
      (v.1.2 < B * m ∧ B * m ≤ v.1.2 + H) ∧
      (v.2.1 < C * m ∧ C * m ≤ v.2.1 + H) ∧
      (v.2.2 < D * m ∧ D * m ≤ v.2.2 + H)) :
    T.card ≤ X * (3 * H + 1) ^ 3 := by
  let box := fun k =>
    ({k} ×ˢ Icc ((B * k) / A - H) ((B * k) / A + 2 * H)) ×ˢ
      (Icc ((C * k) / A - H) ((C * k) / A + 2 * H) ×ˢ
        Icc ((D * k) / A - H) ((D * k) / A + 2 * H))
  have hsub : T ⊆ (range X).biUnion box := by
    rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩ hv
    obtain ⟨hkX, m, hk, hl, hr, hs⟩ := hT _ hv
    apply mem_biUnion.mpr
    refine ⟨k, mem_range.mpr hkX, ?_⟩
    dsimp [box]
    simp only [mem_product, mem_singleton, mem_Icc]
    exact ⟨⟨True.intro, minor_arc_origin_bounds A B H k l m hA hB hk hl⟩,
      minor_arc_origin_bounds A C H k r m hA hC hk hr,
      minor_arc_origin_bounds A D H k s m hA hD hk hs⟩
  have hbox (k : ℕ) : (box k).card ≤ (3 * H + 1) ^ 3 := by
    dsimp [box]
    simp only [card_product, card_singleton, one_mul]
    have h₁ := minor_arc_origin_interval_card ((B * k) / A) H
    have h₂ := minor_arc_origin_interval_card ((C * k) / A) H
    have h₃ := minor_arc_origin_interval_card ((D * k) / A) H
    calc
      _ ≤ (3 * H + 1) * ((3 * H + 1) * (3 * H + 1)) :=
        Nat.mul_le_mul h₁ (Nat.mul_le_mul h₂ h₃)
      _ = _ := by ring
  calc
    T.card ≤ ((range X).biUnion box).card := card_le_card hsub
    _ ≤ ∑ k ∈ range X, (box k).card := card_biUnion_le
    _ ≤ ∑ _k ∈ range X, (3 * H + 1) ^ 3 := sum_le_sum (fun k _ => hbox k)
    _ = X * (3 * H + 1) ^ 3 := by simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcPrimeFourth
namespace OAI

/-! The prime fourth moment is controlled by the rational geometric kernel
at the additive differences p₁+p₂-p₃-p₄. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.ComplexConjugate

lemma minor_arc_phase_four (α x₁ x₂ x₃ x₄ : ℝ) (m : ℕ) :
    additiveCharacter (α * x₁) m * additiveCharacter (α * x₂) m *
      conj (additiveCharacter (α * x₃) m) * conj (additiveCharacter (α * x₄) m) =
      additiveCharacter (α * (x₁ + x₂ - x₃ - x₄)) m := by
  simp only [additiveCharacter, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcWindowInterval
namespace OAI

/-! Exact finite cofactor intervals for discrete short-sum origins. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma mem_minorArcWindowInterval (M A k H m : ℕ) (hA : 0 < A) :
    m ∈ minorArcWindowInterval M A k H ↔
      m < M ∧ k < A * m ∧ A * m ≤ k + H := by
  unfold minorArcWindowInterval
  rw [mem_Ico, lt_min_iff]
  have hlow : k / A < m ↔ k < A * m := by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hA : k / A < m ↔ k < m * A)
  have hhigh : m ≤ (k + H) / A ↔ A * m ≤ k + H := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hA : m ≤ (k + H) / A ↔ m * A ≤ k + H)
  omega

lemma minor_arc_interval_length (A k H a b : ℕ) (hA : 0 < A)
    (hwindow : ∀ m ∈ Ico a b, k < A * m ∧ A * m ≤ k + H) :
    ((b - a : ℕ) : ℝ) ≤ (H : ℝ) / A + 1 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  by_cases hab : a < b
  · have ha := (hwindow a (mem_Ico.mpr ⟨le_rfl, hab⟩)).1
    have hb := (hwindow (b - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)).2
    have haR : (k : ℝ) < (A : ℝ) * a := by exact_mod_cast ha
    have hbR : (A : ℝ) * (b - 1 : ℕ) ≤ (k : ℝ) + H := by exact_mod_cast hb
    rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one] at hbR
    rw [Nat.cast_sub (by omega : a ≤ b)]
    rw [show (H : ℝ) / A + 1 = ((H : ℝ) + A) / A by field_simp [hA0.ne']]
    apply (le_div_iff₀ hA0).mpr
    nlinarith
  · rw [Nat.sub_eq_zero_of_le (by omega : b ≤ a), Nat.cast_zero]
    positivity

lemma minor_arc_geometric_mono {L V : ℝ} (h : L ≤ V) (α : ℝ) :
    minorArcGeometricBound L α ≤ minorArcGeometricBound V α := by
  unfold minorArcGeometricBound
  split_ifs
  · exact h
  · exact min_le_min h le_rfl

lemma minor_arc_geometric_window (A k H a b : ℕ) (hA : 0 < A)
    (hwindow : ∀ m ∈ Ico a b, k < A * m ∧ A * m ≤ k + H) (α : ℝ) :
    ‖∑ m ∈ Ico a b, additiveCharacter α m‖ ≤
      minorArcGeometricBound ((H : ℝ) / A + 1) α :=
  (minor_arc_geometric_bound α a b).trans
    (minor_arc_geometric_mono (minor_arc_interval_length A k H a b hA hwindow) α)

/-- The intersection of four origin windows is again one interval; its
length is controlled by the first prime, regardless of the other origins. -/
lemma minor_arc_four_window_kernel (M A B C D k l r s H : ℕ)
    (hA : 0 < A) (α : ℝ) :
    ‖∑ m ∈ (minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
        (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H),
      additiveCharacter α m‖ ≤ minorArcGeometricBound ((H : ℝ) / A + 1) α := by
  unfold minorArcWindowInterval
  rw [Ico_inter_Ico, Ico_inter_Ico, Ico_inter_Ico]
  apply minor_arc_geometric_window A k H _ _ hA
  intro m hm
  have hm' := mem_Ico.mp hm
  have hlow : k / A + 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm'.1
  have hhigh : m < (k + H) / A + 1 :=
    lt_of_lt_of_le hm'.2 (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hmlow : k < A * m := by
    have hh : k / A < m := by omega
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hA).mp hh
  have hmhigh : A * m ≤ k + H := by
    have hh : m ≤ (k + H) / A := by omega
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hA).mp hh
  exact ⟨hmlow, hmhigh⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcWindowProduct
namespace OAI

/-! One term of the fourth expansion of a weighted short-window sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate


lemma minor_arc_window_product (M A B C D k l r s H : ℕ)
    (hA : 0 < A) (z₁ z₂ z₃ z₄ : ℂ) (β₁ β₂ β₃ β₄ : ℝ) :
    (∑ m ∈ range M,
      minorArcWindowTerm M A k H z₁ β₁ m * minorArcWindowTerm M B l H z₂ β₂ m *
        conj (minorArcWindowTerm M C r H z₃ β₃ m) *
        conj (minorArcWindowTerm M D s H z₄ β₄ m)) =
      (z₁ * z₂ * conj z₃ * conj z₄) *
        ∑ m ∈ (minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
          (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H),
          additiveCharacter (β₁ + β₂ - β₃ - β₄) m := by
  let S := (minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
    (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H)
  let z := z₁ * z₂ * conj z₃ * conj z₄
  have hphase (m : ℕ) :
      additiveCharacter β₁ m * additiveCharacter β₂ m *
        conj (additiveCharacter β₃ m) * conj (additiveCharacter β₄ m) =
      additiveCharacter (β₁ + β₂ - β₃ - β₄) m := by
    simpa only [one_mul] using minor_arc_phase_four 1 β₁ β₂ β₃ β₄ m
  have he (m : ℕ) :
      minorArcWindowTerm M A k H z₁ β₁ m * minorArcWindowTerm M B l H z₂ β₂ m *
        conj (minorArcWindowTerm M C r H z₃ β₃ m) *
        conj (minorArcWindowTerm M D s H z₄ β₄ m) =
      if m ∈ S then z * additiveCharacter (β₁ + β₂ - β₃ - β₄) m else 0 := by
    by_cases ha : m ∈ minorArcWindowInterval M A k H
    · by_cases hb : m ∈ minorArcWindowInterval M B l H
      · by_cases hc : m ∈ minorArcWindowInterval M C r H
        · by_cases hd : m ∈ minorArcWindowInterval M D s H
          · simp only [minorArcWindowTerm, ha, hb, hc, hd, ite_true, S, mem_inter,
              and_self, map_mul, z]
            rw [← hphase]
            ring
          · simp [minorArcWindowTerm, S, ha, hb, hc, hd]
        · simp [minorArcWindowTerm, S, ha, hb, hc]
      · simp [minorArcWindowTerm, S, ha, hb]
    · simp [minorArcWindowTerm, S, ha]
  have hsub : S ⊆ range M := by
    intro m hm
    exact mem_range.mpr ((mem_minorArcWindowInterval M A k H m hA).mp
      (mem_inter.mp (mem_inter.mp hm).1).1).1
  have hfilt : (range M).filter (fun m => m ∈ S) = S := by
    ext m
    simp only [mem_filter]
    exact ⟨And.right, fun hm => ⟨hsub hm, hm⟩⟩
  simp_rw [he]
  rw [← sum_filter, hfilt, mul_sum]

lemma minor_arc_window_product_bound (M A B C D k l r s H : ℕ)
    (hA : 0 < A) (z₁ z₂ z₃ z₄ : ℂ) (β₁ β₂ β₃ β₄ V : ℝ)
    (hz : ‖z₁ * z₂ * conj z₃ * conj z₄‖ ≤ 1)
    (hV : (H : ℝ) / A + 1 ≤ V) :
    ‖∑ m ∈ range M,
      minorArcWindowTerm M A k H z₁ β₁ m * minorArcWindowTerm M B l H z₂ β₂ m *
        conj (minorArcWindowTerm M C r H z₃ β₃ m) *
        conj (minorArcWindowTerm M D s H z₄ β₄ m)‖ ≤
      minorArcGeometricBound V (β₁ + β₂ - β₃ - β₄) := by
  rw [minor_arc_window_product M A B C D k l r s H hA, norm_mul]
  calc
    _ ≤ 1 * ‖∑ m ∈ (minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
        (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H),
        additiveCharacter (β₁ + β₂ - β₃ - β₄) m‖ :=
      mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact (minor_arc_four_window_kernel M A B C D k l r s H hA _).trans
        (minor_arc_geometric_mono hV _)

lemma minor_arc_window_product_support (M A B C D k l r s H : ℕ)
    (hA : 0 < A) (z₁ z₂ z₃ z₄ : ℂ) (β₁ β₂ β₃ β₄ V : ℝ)
    (hz : ‖z₁ * z₂ * conj z₃ * conj z₄‖ ≤ 1)
    (hV : (H : ℝ) / A + 1 ≤ V) :
    ‖∑ m ∈ range M,
      minorArcWindowTerm M A k H z₁ β₁ m * minorArcWindowTerm M B l H z₂ β₂ m *
        conj (minorArcWindowTerm M C r H z₃ β₃ m) *
        conj (minorArcWindowTerm M D s H z₄ β₄ m)‖ ≤
      if ((minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
          (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H)).Nonempty
      then minorArcGeometricBound V (β₁ + β₂ - β₃ - β₄) else 0 := by
  split_ifs with hs
  · exact minor_arc_window_product_bound M A B C D k l r s H hA
      z₁ z₂ z₃ z₄ β₁ β₂ β₃ β₄ V hz hV
  · have hempty := not_nonempty_iff_eq_empty.mp hs
    rw [minor_arc_window_product M A B C D k l r s H hA, hempty]
    simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcOriginSum
namespace OAI

/-! Summing a fixed prime quadruple over its possible interval origins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

lemma minor_arc_origin_kernel_sum (X M A B C D H : ℕ) (hA : 0 < A)
    (hB0 : 0 < B) (hC0 : 0 < C) (hD0 : 0 < D)
    (hB : B ≤ 2 * A) (hC : C ≤ 2 * A) (hD : D ≤ 2 * A)
    (z₁ z₂ z₃ z₄ : ℕ → ℂ) (hz₁ : ∀ k, ‖z₁ k‖ ≤ 1) (hz₂ : ∀ k, ‖z₂ k‖ ≤ 1)
    (hz₃ : ∀ k, ‖z₃ k‖ ≤ 1) (hz₄ : ∀ k, ‖z₄ k‖ ≤ 1)
    (β₁ β₂ β₃ β₄ V : ℝ) (hV : (H : ℝ) / A + 1 ≤ V) :
    (∑ k ∈ range X, ∑ l ∈ range X, ∑ r ∈ range X, ∑ s ∈ range X,
      ‖∑ m ∈ range M,
        minorArcWindowTerm M A k H (z₁ k) β₁ m * minorArcWindowTerm M B l H (z₂ l) β₂ m *
          conj (minorArcWindowTerm M C r H (z₃ r) β₃ m) *
          conj (minorArcWindowTerm M D s H (z₄ s) β₄ m)‖) ≤
      (X * (3 * H + 1) ^ 3 : ℕ) * minorArcGeometricBound V (β₁ + β₂ - β₃ - β₄) := by
  let Q := ((range X) ×ˢ (range X)) ×ˢ ((range X) ×ˢ (range X))
  let S := fun v : (ℕ × ℕ) × (ℕ × ℕ) =>
    (minorArcWindowInterval M A v.1.1 H ∩ minorArcWindowInterval M B v.1.2 H) ∩
      (minorArcWindowInterval M C v.2.1 H ∩ minorArcWindowInterval M D v.2.2 H)
  let T := Q.filter (fun v => (S v).Nonempty)
  let K := minorArcGeometricBound V (β₁ + β₂ - β₃ - β₄)
  have hV0 : 0 ≤ V := by
    have h : 0 ≤ (H : ℝ) / A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  have hK : 0 ≤ K := minor_arc_geometric_nonneg hV0 _
  have hcard : T.card ≤ X * (3 * H + 1) ^ 3 := by
    apply minor_arc_origin_quadruples X H A B C D hA hB hC hD T
    rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩ hv
    obtain ⟨hvQ, m, hm⟩ := mem_filter.mp hv
    have hkX := (mem_product.mp (mem_product.mp hvQ).1).1
    obtain ⟨hm₁, hm₂⟩ := mem_inter.mp hm
    obtain ⟨hmA, hmB⟩ := mem_inter.mp hm₁
    obtain ⟨hmC, hmD⟩ := mem_inter.mp hm₂
    exact ⟨mem_range.mp hkX, m,
      ((mem_minorArcWindowInterval M A k H m hA).mp hmA).2,
      ((mem_minorArcWindowInterval M B l H m hB0).mp hmB).2,
      ((mem_minorArcWindowInterval M C r H m hC0).mp hmC).2,
      ((mem_minorArcWindowInterval M D s H m hD0).mp hmD).2⟩
  have hz (k l r s : ℕ) : ‖z₁ k * z₂ l * conj (z₃ r) * conj (z₄ s)‖ ≤ 1 := by
    simp only [norm_mul, Complex.norm_conj]
    calc
      ‖z₁ k‖ * ‖z₂ l‖ * ‖z₃ r‖ * ‖z₄ s‖ ≤ 1 * 1 * 1 * 1 := by
        gcongr <;> first | exact hz₁ _ | exact hz₂ _ | exact hz₃ _ | exact hz₄ _
      _ = 1 := by norm_num
  calc
    _ ≤ ∑ k ∈ range X, ∑ l ∈ range X, ∑ r ∈ range X, ∑ s ∈ range X,
        if (S ((k, l), (r, s))).Nonempty then K else 0 := by
      repeat' apply sum_le_sum fun _ _ => ?_
      exact minor_arc_window_product_support M A B C D _ _ _ _ H hA _ _ _ _
        β₁ β₂ β₃ β₄ V (hz _ _ _ _) hV
    _ = ∑ v ∈ Q, if (S v).Nonempty then K else 0 := by
      simp only [Q, sum_product]
    _ = (T.card : ℝ) * K := by
      rw [← sum_filter]
      simp only [T, sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hcard) hK

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcWindowFourth
namespace OAI

/-! The discrete weighted-window fourth moment in MRT's minor-arc argument. -/

namespace TwoPointCorrelations

open _root_.Finset

/-- A prime block contributes only `X (3H+1)^3` possible origin quadruples.
The remaining cancellation is exactly the four-prime geometric kernel. -/
theorem minor_arc_window_fourth (P : Finset ℕ) (X M H d : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P, 0 < p ∧ ∀ q ∈ P, q ≤ 2 * p)
    (c θ : ℕ → ℂ) (hc : ∀ p ∈ P, ‖c p‖ ≤ 1) (hθ : ∀ k, ‖θ k‖ ≤ 1)
    (α V : ℝ) (hV : ∀ p ∈ P, (H : ℝ) / (d * p : ℕ) + 1 ≤ V) :
    (∑ m ∈ range M, ‖∑ p ∈ P, ∑ k ∈ range X,
      minorArcWindowTerm M (d * p) k H (c p * θ k) (α * p) m‖ ^ 4) ≤
      (X * (3 * H + 1) ^ 3 : ℕ) *
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
          minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) := by
  classical
  let f := fun v : ℕ × ℕ =>
    minorArcWindowTerm M (d * v.1) v.2 H (c v.1 * θ v.2) (α * v.1)
  have he := minor_arc_fourth_moment_bound (P ×ˢ range X) (range M) f
  dsimp [f] at he
  simp only [sum_product] at he
  simp_rw [sum_comm (s := range X) (t := P)] at he
  apply he.trans
  simp only [mul_sum]
  apply sum_le_sum
  intro p₁ hp₁
  apply sum_le_sum
  intro p₂ hp₂
  apply sum_le_sum
  intro p₃ hp₃
  apply sum_le_sum
  intro p₄ hp₄
  have hcoef (p : ℕ) (hp : p ∈ P) (k : ℕ) : ‖c p * θ k‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (hc p hp) (hθ k) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h := minor_arc_origin_kernel_sum X M (d * p₁) (d * p₂) (d * p₃) (d * p₄) H
    (Nat.mul_pos hd (hP p₁ hp₁).1)
    (Nat.mul_pos hd (hP p₂ hp₂).1)
    (Nat.mul_pos hd (hP p₃ hp₃).1)
    (Nat.mul_pos hd (hP p₄ hp₄).1)
    (by nlinarith [(hP p₁ hp₁).2 p₂ hp₂])
    (by nlinarith [(hP p₁ hp₁).2 p₃ hp₃])
    (by nlinarith [(hP p₁ hp₁).2 p₄ hp₄])
    (fun k => c p₁ * θ k) (fun k => c p₂ * θ k)
    (fun k => c p₃ * θ k) (fun k => c p₄ * θ k)
    (hcoef p₁ hp₁) (hcoef p₂ hp₂) (hcoef p₃ hp₃) (hcoef p₄ hp₄)
    (α * p₁) (α * p₂) (α * p₃) (α * p₄) V (hV p₁ hp₁)
  have hphase : α * (p₁ : ℝ) + α * p₂ - α * p₃ - α * p₄ =
      α * ((p₁ : ℝ) + p₂ - p₃ - p₄) := by ring
  rw [hphase] at h
  exact h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcHolder
namespace OAI

/-! The finite fourth-power Hölder step for the minor-arc cofactor sum. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma minor_arc_sum_fourth {ι : Type*} (S : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ S, a i) ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ S, a i ^ 4 := by
  have h₁ := sq_sum_le_card_mul_sum_sq (s := S) (f := a)
  have h₂ := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => a i ^ 2)
  calc
    _ = ((∑ i ∈ S, a i) ^ 2) ^ 2 := by ring
    _ ≤ ((S.card : ℝ) * ∑ i ∈ S, a i ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = (S.card : ℝ) ^ 2 * (∑ i ∈ S, a i ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ (S.card : ℝ) ^ 2 * ((S.card : ℝ) * ∑ i ∈ S, (a i ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by simp only [← pow_mul]; ring

lemma minor_arc_weighted_fourth {ι : Type*} (S : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) :
    ‖∑ i ∈ S, a i * b i‖ ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ S, ‖b i‖ ^ 4 := by
  have hn : ‖∑ i ∈ S, a i * b i‖ ≤ ∑ i ∈ S, ‖b i‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i hi
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha i hi) (norm_nonneg (b i))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 4).trans (minor_arc_sum_fourth S (fun i => ‖b i‖))

/-- Polarizing the finite origin sum produces a coefficient of norm one
at every origin, including origins where the short sum vanishes. -/
lemma minor_arc_norm_sum_duality (S : Finset ℕ) (f : ℕ → ℂ) :
    ∃ θ : ℕ → ℂ, (∀ k, ‖θ k‖ = 1) ∧
      (∑ k ∈ S, ‖f k‖) = ‖∑ k ∈ S, θ k * f k‖ := by
  classical
  choose θ hθnorm hθmul using (fun k => Complex.exists_norm_eq_mul_self (f k))
  refine ⟨θ, hθnorm, ?_⟩
  have he : (∑ k ∈ S, θ k * f k) = ((∑ k ∈ S, ‖f k‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact sum_congr rfl (fun k _ => (hθmul k).symm)
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sum_nonneg (fun k _ => norm_nonneg (f k)))]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcBilinearWindow
namespace OAI

/-! A literal finite bilinear short-window bound, before substituting the
Ramaré cofactor coefficient or the sieve kernel estimate. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma minor_arc_window_scalar (M A k H : ℕ) (z w : ℂ) (β : ℝ) (m : ℕ) :
    w * minorArcWindowTerm M A k H z β m =
      minorArcWindowTerm M A k H (z * w) β m := by
  unfold minorArcWindowTerm
  split_ifs <;> ring

lemma minor_arc_bilinear_dual (P : Finset ℕ) (X M H d : ℕ)
    (a c θ : ℕ → ℂ) (α : ℝ) :
    (∑ k ∈ range X, θ k * minorArcBilinearWindow P M H d a c α k) =
      ∑ m ∈ range M, a m * ∑ p ∈ P, ∑ k ∈ range X,
        minorArcWindowTerm M (d * p) k H (c p * θ k) (α * p) m := by
  unfold minorArcBilinearWindow
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro k _
  rw [← minor_arc_window_scalar]
  ring

/-- The full finite minor-arc inequality obtained by polarization,
Hölder, geometric summation and the four-origin support estimate. -/
theorem minor_arc_bilinear_fourth (P : Finset ℕ) (X M H d : ℕ) (hd : 0 < d)
    (hP : ∀ p ∈ P, 0 < p ∧ ∀ q ∈ P, q ≤ 2 * p)
    (a c : ℕ → ℂ) (ha : ∀ m ∈ range M, ‖a m‖ ≤ 1) (hc : ∀ p ∈ P, ‖c p‖ ≤ 1)
    (α V : ℝ) (hV : ∀ p ∈ P, (H : ℝ) / (d * p : ℕ) + 1 ≤ V) :
    (∑ k ∈ range X, ‖minorArcBilinearWindow P M H d a c α k‖) ^ 4 ≤
      (M : ℝ) ^ 3 * (X * (3 * H + 1) ^ 3 : ℕ) *
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
          minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄)) := by
  obtain ⟨θ, hθ, hdual⟩ := minor_arc_norm_sum_duality (range X)
    (minorArcBilinearWindow P M H d a c α)
  rw [hdual, minor_arc_bilinear_dual]
  have hholder := minor_arc_weighted_fourth (range M) a
    (fun m => ∑ p ∈ P, ∑ k ∈ range X,
      minorArcWindowTerm M (d * p) k H (c p * θ k) (α * p) m) ha
  simp only [card_range] at hholder
  apply hholder.trans
  have hfour := minor_arc_window_fourth P X M H d hd hP c θ hc
    (fun k => (hθ k).le) α V hV
  have hh := mul_le_mul_of_nonneg_left hfour (by positivity : 0 ≤ (M : ℝ) ^ 3)
  simpa only [mul_assoc] using hh

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.minor_arc_bilinear_fourth := @OAI.TwoPointCorrelations.minor_arc_bilinear_fourth
