-- Prove2me | solution 1 for OAI.TwoPointCorrelations.minor_arc_bilinear_parameter_saving
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:14:13.51572+00:00
-- url     : https://prove2.me/submissions/4809565a-d25d-4eb3-aed6-7dc404b9663f

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_minor_arc_bilinear_fourth
import Theorems.Thm_OAI_TwoPointCorrelations_sieve_prime_additive_energy

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds
namespace OAI
noncomputable section

open scoped _root_.BigOperators

namespace Problem337


instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩







end Problem337

end

end OAI

end

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcShiftedFiber
namespace OAI

/-! A shifted additive fiber is bounded by the unshifted additive energy. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma minor_arc_value_support {α : Type*} {S : Finset α} {f : α → ℤ} {n : ℤ}
    (hn : minorArcValueCount S f n ≠ 0) : n ∈ S.image f := by
  obtain ⟨a, ha⟩ := card_ne_zero.mp hn
  obtain ⟨haS, han⟩ := mem_filter.mp ha
  exact mem_image.mpr ⟨a, haS, han⟩

lemma minor_arc_pair_fiber {α : Type*} (S : Finset α) (f : α → ℤ) (h : ℤ) :
    ((S ×ˢ S).filter (fun v => f v.1 - f v.2 = h)).card =
      ∑ n ∈ S.image f, minorArcValueCount S f n * minorArcValueCount S f (n - h) := by
  have hfirst : ((S ×ˢ S).filter (fun v => f v.1 - f v.2 = h)).card =
      ∑ a ∈ S, minorArcValueCount S f (f a - h) := by
    simp only [card_eq_sum_ones, sum_filter, sum_product, minorArcValueCount]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    have hi : f a - f b = h ↔ f b = f a - h := by omega
    by_cases hab : f a - f b = h
    · simp only [if_pos hab, if_pos (hi.mp hab)]
    · simp only [if_neg hab, if_neg ((not_congr hi).mp hab)]
  rw [hfirst, ← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem f ha)
    (fun a => minorArcValueCount S f (f a - h))]
  apply sum_congr rfl
  intro n _
  calc
    _ = ∑ _a ∈ S.filter (fun a => f a = n), minorArcValueCount S f (n - h) := by
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id, minorArcValueCount]

lemma minor_arc_shifted_value_squares {α : Type*} (S : Finset α) (f : α → ℤ) (h : ℤ) :
    (∑ n ∈ S.image f, minorArcValueCount S f (n - h) ^ 2) ≤
      ∑ n ∈ S.image f, minorArcValueCount S f n ^ 2 := by
  have hi : Set.InjOn (fun n : ℤ => n - h) (↑(S.image f) : Set ℤ) := by
    intro a _ b _ hab
    change a - h = b - h at hab
    omega
  rw [← sum_image (f := fun n : ℤ => minorArcValueCount S f n ^ 2) hi]
  apply sum_le_sum_of_ne_zero
  intro n _ hn
  apply minor_arc_value_support
  intro hz
  simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
  exact hn rfl

lemma minor_arc_shifted_pair_card {α : Type*} (S : Finset α) (f : α → ℤ) (h : ℤ) :
    ((S ×ˢ S).filter (fun v => f v.1 - f v.2 = h)).card ≤
      ((S ×ˢ S).filter (fun v => f v.1 - f v.2 = 0)).card := by
  rw [minor_arc_pair_fiber, minor_arc_pair_fiber]
  simp only [sub_zero, ← pow_two]
  have he : 2 * (∑ n ∈ S.image f, minorArcValueCount S f n * minorArcValueCount S f (n - h)) ≤
      (∑ n ∈ S.image f, minorArcValueCount S f n ^ 2) +
        ∑ n ∈ S.image f, minorArcValueCount S f (n - h) ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro n _
    have he : (2 : ℤ) * minorArcValueCount S f n * minorArcValueCount S f (n - h) ≤
        (minorArcValueCount S f n : ℤ) ^ 2 + (minorArcValueCount S f (n - h) : ℤ) ^ 2 := by
      nlinarith [sq_nonneg ((minorArcValueCount S f n : ℤ) - minorArcValueCount S f (n - h))]
    simpa only [mul_assoc] using (show
      2 * minorArcValueCount S f n * minorArcValueCount S f (n - h) ≤
        minorArcValueCount S f n ^ 2 + minorArcValueCount S f (n - h) ^ 2 by exact_mod_cast he)
  have hs := minor_arc_shifted_value_squares S f h
  omega

/-- Every difference-of-prime-sums fiber has size at most the zero fiber. -/
theorem minor_arc_prime_shifted_fiber (P : Finset ℕ) (h : ℤ) :
    (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter
      (fun v => ((v.1.1 : ℤ) + v.1.2) - ((v.2.1 : ℤ) + v.2.2) = h)).card ≤
      Finset.addEnergy P P := by
  have he := minor_arc_shifted_pair_card (P ×ˢ P)
    (fun v => (v.1 : ℤ) + v.2) h
  have hz : (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter
      (fun v => ((v.1.1 : ℤ) + v.1.2) - ((v.2.1 : ℤ) + v.2.2) = 0)).card =
      Finset.addEnergy P P := by
    rw [Finset.addEnergy_eq_card_filter]
    apply congrArg Finset.card
    apply filter_congr
    intro v _
    omega
  exact hz ▸ he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcCircleKernel
namespace OAI

/-! Convert the exact geometric denominator to distance from the nearest
integer. This is the kernel used in the rational-spacing estimate. -/

namespace TwoPointCorrelations

open _root_.Complex

lemma minor_arc_phase_gap (α : ℝ) :
    4 * ‖(α : UnitAddCircle)‖ ≤ ‖additiveCharacter α 1 - 1‖ := by
  let δ := α - (round α : ℝ)
  have hδ : |δ| ≤ 1 / 2 := by
    simpa only [UnitAddCircle.norm_eq, abs_one] using
      (AddCircle.norm_le_half_period (1 : ℝ) (by norm_num) (x := (α : UnitAddCircle)))
  have hsin := Real.mul_abs_le_abs_sin (x := Real.pi * δ) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  have hs : |Real.sin (Real.pi * δ)| = |Real.sin (Real.pi * α)| := by
    rw [show Real.pi * δ = Real.pi * α - (round α : ℝ) * Real.pi by dsimp [δ]; ring,
      Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
    norm_num
  have hn : ‖additiveCharacter α 1 - 1‖ = 2 * |Real.sin (Real.pi * α)| := by
    have he : additiveCharacter α 1 = Complex.exp (Complex.I * ((2 * Real.pi * α : ℝ) : ℂ)) := by
      simp only [additiveCharacter, Nat.cast_one, mul_one]
      rw [mul_comm]
    rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
      show 2 * Real.pi * α / 2 = Real.pi * α by ring,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hn, ← hs, UnitAddCircle.norm_eq]
  have hδπ : |Real.pi * δ| = Real.pi * |δ| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [hδπ] at hsin
  have he : (2 / Real.pi) * (Real.pi * |δ|) = 2 * |δ| := by field_simp
  rw [he] at hsin
  change 4 * |δ| ≤ 2 * |Real.sin (Real.pi * δ)|
  linarith

lemma minor_arc_geometric_circle {α L : ℝ} (hα : 0 < ‖(α : UnitAddCircle)‖) :
    minorArcGeometricBound L α ≤ min L (1 / (2 * ‖(α : UnitAddCircle)‖)) := by
  have hgap := minor_arc_phase_gap α
  have hn : 0 < ‖additiveCharacter α 1 - 1‖ := by linarith
  have hz : additiveCharacter α 1 ≠ 1 := by
    intro he
    simp only [he, sub_self, norm_zero] at hn
    linarith
  unfold minorArcGeometricBound
  rw [if_neg hz]
  apply min_le_min_left
  apply (div_le_div_iff₀ hn (by positivity : 0 < 2 * ‖(α : UnitAddCircle)‖)).mpr
  nlinarith

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

lemma minor_arc_character_neg (α : ℝ) (n : ℕ) :
    additiveCharacter (-α) n = conj (additiveCharacter α n) := by
  simp only [additiveCharacter, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma minor_arc_geometric_neg (L α : ℝ) :
    minorArcGeometricBound L (-α) = minorArcGeometricBound L α := by
  have hc : conj (additiveCharacter α 1) = 1 ↔ additiveCharacter α 1 = 1 := by
    constructor
    · intro h
      have he := congrArg conj h
      simpa only [map_one, conj_conj] using he
    · intro h
      rw [h, map_one]
  unfold minorArcGeometricBound
  rw [minor_arc_character_neg]
  by_cases h : additiveCharacter α 1 = 1
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg ((not_congr hc).mpr h), if_neg h]
    have he : conj (additiveCharacter α 1) - 1 = conj (additiveCharacter α 1 - 1) := by
      rw [map_sub, map_one]
    rw [he, norm_conj]

lemma minor_arc_geometric_natAbs (L α : ℝ) (n : ℤ) :
    minorArcGeometricBound L ((n.natAbs : ℝ) * α) =
      minorArcGeometricBound L ((n : ℝ) * α) := by
  have he : (n.natAbs : ℝ) = |(n : ℝ)| := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs n)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  rw [he]
  by_cases hn : (0 : ℝ) ≤ n
  · rw [abs_of_nonneg hn]
  · rw [abs_of_neg (lt_of_not_ge hn), neg_mul, minor_arc_geometric_neg]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcEnergyKernel
namespace OAI

/-! Regrouping the prime fourth moment by its integer additive difference. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_fiber_sum {α β : Type*} (S : Finset α) (T : Finset β)
    (f : α → β) (w : β → ℝ) (B : ℝ)
    (hmap : ∀ a ∈ S, f a ∈ T) (hw : ∀ b ∈ T, 0 ≤ w b)
    (hcard : ∀ b ∈ T, ((S.filter (fun a => f a = b)).card : ℝ) ≤ B) :
    (∑ a ∈ S, w (f a)) ≤ B * (∑ b ∈ T, w b) := by
  rw [← sum_fiberwise_of_maps_to hmap (fun a => w (f a)), mul_sum]
  apply sum_le_sum
  intro b hb
  calc
    _ = ((S.filter (fun a => f a = b)).card : ℝ) * w b := by
      rw [sum_congr rfl (fun a ha => congrArg w (mem_filter.mp ha).2)]
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard b hb) (hw b hb)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcRationalSpacing
namespace OAI

/-! Separation of a nonintegral rational point, and stability under the
small perturbation used in the minor-arc rational approximation. -/

namespace TwoPointCorrelations

lemma minor_arc_circle_norm_le (x : ℝ) : ‖(x : UnitAddCircle)‖ ≤ |x| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le x (0 : ℤ)

lemma minor_arc_rational_norm {a q : ℤ} (hq : 0 < q) (hqa : ¬q ∣ a) :
    1 / (q : ℝ) ≤ ‖(((a : ℝ) / (q : ℝ)) : UnitAddCircle)‖ := by
  let j := round ((a : ℝ) / (q : ℝ))
  have hz : a - j * q ≠ 0 := by
    intro he
    apply hqa
    refine ⟨j, ?_⟩
    have hh : a = j * q := sub_eq_zero.mp he
    simpa only [mul_comm] using hh
  have hb : (1 : ℝ) ≤ |(a : ℝ) - (j : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hz
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  rw [UnitAddCircle.norm_eq]
  have he : |(a : ℝ) / (q : ℝ) - (j : ℝ)| = |(a : ℝ) - (j : ℝ) * q| / (q : ℝ) := by
    calc
      _ = |((a : ℝ) - (j : ℝ) * q) / (q : ℝ)| := by congr 1; field_simp
      _ = _ := by rw [abs_div, abs_of_pos hqr]
  change 1 / (q : ℝ) ≤ |(a : ℝ) / (q : ℝ) - (j : ℝ)|
  rw [he]
  exact div_le_div_of_nonneg_right hb hqr.le

lemma minor_arc_perturbed_rational {a q : ℤ} {x : ℝ} (hq : 0 < q) (hqa : ¬q ∣ a)
    (hx : |x - (a : ℝ) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ))) :
    1 / (2 * (q : ℝ)) ≤ ‖(x : UnitAddCircle)‖ := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hrat := minor_arc_rational_norm hq hqa
  have herr := (minor_arc_circle_norm_le (x - (a : ℝ) / (q : ℝ))).trans hx
  rw [AddCircle.coe_sub] at herr
  have ht := norm_le_norm_add_norm_sub (x : UnitAddCircle) (((a : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)
  have he : 1 / (q : ℝ) = 2 * (1 / (2 * (q : ℝ))) := by field_simp
  rw [he] at hrat
  linarith

lemma minor_arc_multiple_spacing {α : ℝ} {a q k : ℤ} (hq : 0 < q)
    (hqak : ¬q ∣ a * k) (hk : |(k : ℝ)| ≤ (q : ℝ) / 2)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    1 / (2 * (q : ℝ)) ≤ ‖(((k : ℝ) * α : ℝ) : UnitAddCircle)‖ := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  apply minor_arc_perturbed_rational hq hqak
  calc
    |(k : ℝ) * α - ((a * k : ℤ) : ℝ) / (q : ℝ)| =
        |(k : ℝ)| * |α - (a : ℝ) / (q : ℝ)| := by
      rw [← abs_mul]
      congr 1
      push_cast
      ring
    _ ≤ ((q : ℝ) / 2) * (1 / (q : ℝ) ^ 2) :=
      mul_le_mul hk happrox (abs_nonneg _) (by positivity)
    _ = 1 / (2 * (q : ℝ)) := by field_simp

lemma minor_arc_pair_spacing {α : ℝ} {a q m n : ℤ} (hq : 0 < q)
    (hcop : IsCoprime q a) (hmn : m ≠ n)
    (hshort : |((m - n : ℤ) : ℝ)| ≤ (q : ℝ) / 2)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    1 / (2 * (q : ℝ)) ≤ dist (((m : ℝ) * α : ℝ) : UnitAddCircle)
      (((n : ℝ) * α : ℝ) : UnitAddCircle) := by
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hmn
  have hnot : ¬q ∣ a * (m - n) := by
    intro hh
    have hd := hcop.dvd_of_dvd_mul_left hh
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hle := Int.natAbs_le_of_dvd_ne_zero hd hk
    have hlei : |q| ≤ |m - n| := by
      rw [← Int.natCast_natAbs q, ← Int.natCast_natAbs (m - n)]
      exact_mod_cast hle
    rw [abs_of_pos hq] at hlei
    have hler : (q : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast hlei
    linarith
  have h := minor_arc_multiple_spacing hq hnot hshort happrox
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  convert (preTransparency := .instances) h using 1
  congr 2
  push_cast
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcPacking
namespace OAI

/-! Elementary interval packing for separated phase representatives. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_interval_packing {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (δ b : ℝ) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|) :
    (S.filter (fun i => b ≤ x i ∧ x i < b + δ)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiS, hix⟩ := mem_filter.mp hi
  obtain ⟨hjS, hjx⟩ := mem_filter.mp hj
  by_contra hij
  have hh := hsep i hiS j hjS hij
  have habs : |x i - x j| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

lemma minor_arc_absolute_band_packing {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (δ b : ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|) :
    (S.filter (fun i => b ≤ |x i| ∧ |x i| < b + δ)).card ≤ 2 := by
  let P := S.filter (fun i => b ≤ x i ∧ x i < b + δ)
  let Q := S.filter (fun i => b ≤ -x i ∧ -x i < b + δ)
  have hP : P.card ≤ 1 := minor_arc_interval_packing S x δ b hsep
  have hQ : Q.card ≤ 1 := by
    apply minor_arc_interval_packing S (fun i => -x i) δ b
    intro i hi j hj hij
    simpa only [neg_sub_neg, abs_sub_comm] using hsep i hi j hj hij
  have hsub : S.filter (fun i => b ≤ |x i| ∧ |x i| < b + δ) ⊆ P ∪ Q := by
    intro i hi
    obtain ⟨hiS, hix⟩ := mem_filter.mp hi
    by_cases hx : 0 ≤ x i
    · apply mem_union_left
      exact mem_filter.mpr ⟨hiS, by simpa only [abs_of_nonneg hx] using hix⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨hiS, by simpa only [abs_of_neg (lt_of_not_ge hx)] using hix⟩
  have hu := (card_le_card hsub).trans (card_union_le P Q)
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcPackingSum
namespace OAI

/-! Summing a truncated reciprocal over separated real representatives. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem minor_arc_packing_sum {ι : Type*} (S : Finset ι) (x w : ι → ℝ)
    (δ V R : ℝ) (hδ : 0 < δ) (hV : 0 ≤ V)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |x i - x j|)
    (hx : ∀ i ∈ S, |x i| ≤ R) (hw : ∀ i ∈ S, w i ≤ V)
    (hwinv : ∀ i ∈ S, 0 < |x i| → w i ≤ 1 / |x i|) :
    (∑ i ∈ S, w i) ≤ 2 * V + (2 / δ) * (1 + Real.log (⌈R / δ⌉₊ : ℝ)) := by
  let L := ⌈R / δ⌉₊
  let b := fun i => ⌊|x i| / δ⌋₊
  let F := fun j : ℕ => S.filter (fun i => b i = j)
  have hindex (i : ι) (hi : i ∈ S) : b i ≤ L := by
    apply Nat.floor_le_of_le
    exact (div_le_div_of_nonneg_right (hx i hi) hδ.le).trans (Nat.le_ceil _)
  have hband (j : ℕ) (i : ι) (hi : i ∈ F j) :
      (j : ℝ) * δ ≤ |x i| ∧ |x i| < (j : ℝ) * δ + δ := by
    have he : b i = j := (mem_filter.mp hi).2
    have hl := Nat.floor_le (div_nonneg (abs_nonneg (x i)) hδ.le)
    have hu := Nat.lt_floor_add_one (|x i| / δ)
    change ((b i : ℕ) : ℝ) ≤ |x i| / δ at hl
    change |x i| / δ < (b i : ℝ) + 1 at hu
    rw [he] at hl hu
    constructor
    · exact (le_div_iff₀ hδ).mp hl
    · have hh := (div_lt_iff₀ hδ).mp hu
      nlinarith
  have hcard (j : ℕ) : (F j).card ≤ 2 := by
    refine (card_le_card (s := F j) (t := S.filter (fun i =>
      (j : ℝ) * δ ≤ |x i| ∧ |x i| < (j : ℝ) * δ + δ)) ?_).trans
      (minor_arc_absolute_band_packing S x δ ((j : ℝ) * δ) hsep)
    intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1, hband j i hi⟩
  have hzero : (∑ i ∈ F 0, w i) ≤ 2 * V := by
    calc
      _ ≤ ∑ _i ∈ F 0, V := sum_le_sum (fun i hi => hw i (mem_filter.mp hi).1)
      _ = ((F 0).card : ℝ) * V := by simp
      _ ≤ 2 * V := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard 0) hV
  have hpiece (j : ℕ) (hj : j ∈ Icc 1 L) : (∑ i ∈ F j, w i) ≤ 2 / (δ * j) := by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    have hbound (i : ι) (hi : i ∈ F j) : w i ≤ 1 / (δ * j) := by
      have hlo := (hband j i hi).1
      have hpos : 0 < |x i| := (mul_pos hj0 hδ).trans_le hlo
      apply (hwinv i (mem_filter.mp hi).1 hpos).trans
      exact one_div_le_one_div_of_le (mul_pos hδ hj0) (by nlinarith)
    calc
      _ ≤ ∑ _i ∈ F j, 1 / (δ * j) := sum_le_sum hbound
      _ = ((F j).card : ℝ) * (1 / (δ * j)) := by simp
      _ ≤ 2 * (1 / (δ * j)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard j) (by positivity)
      _ = _ := by ring
  have hpartition : (∑ i ∈ S, w i) = ∑ j ∈ Icc 0 L, ∑ i ∈ F j, w i := by
    symm
    exact sum_fiberwise_of_maps_to (fun i hi => mem_Icc.mpr ⟨Nat.zero_le _, hindex i hi⟩) _
  have hsplit : (∑ j ∈ Icc 0 L, ∑ i ∈ F j, w i) =
      (∑ i ∈ F 0, w i) + ∑ j ∈ Icc 1 L, ∑ i ∈ F j, w i := by
    have he : Icc 0 L = insert 0 (Icc 1 L) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [he, sum_insert (by simp)]
  have hharm : (∑ j ∈ Icc 1 L, 2 / (δ * j)) ≤
      (2 / δ) * (1 + Real.log (L : ℝ)) := by
    calc
      _ = (2 / δ) * (harmonic L : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log L) (by positivity)
  rw [hpartition, hsplit]
  exact add_le_add hzero ((sum_le_sum hpiece).trans hharm)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcPhaseRepresentatives
namespace OAI

/-! Centered representatives preserve the rational separation on the circle. -/

namespace TwoPointCorrelations

lemma minor_arc_integer_zero (z : ℤ) : ((z : ℝ) : UnitAddCircle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨z, by simp⟩

lemma minor_arc_centered_coe (x : ℝ) :
    ((x - (round x : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [AddCircle.coe_sub, minor_arc_integer_zero, sub_zero]

lemma minor_arc_centered_difference (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤
      |(x - (round x : ℝ)) - (y - (round y : ℝ))| := by
  have h := minor_arc_circle_norm_le ((x - (round x : ℝ)) - (y - (round y : ℝ)))
  rw [AddCircle.coe_sub, minor_arc_centered_coe, minor_arc_centered_coe] at h
  simpa only [dist_eq_norm] using h

lemma minor_arc_centered_small (x : ℝ) : |x - (round x : ℝ)| ≤ 1 / 2 := by
  simpa only [UnitAddCircle.norm_eq, abs_one] using
    (AddCircle.norm_le_half_period (1 : ℝ) (by norm_num) (x := (x : UnitAddCircle)))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcSeparatedKernel
namespace OAI

/-! A finite Vinogradov kernel bound on a separated set of phases. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma minor_arc_kernel_le (L α : ℝ) : minorArcGeometricBound L α ≤ L := by
  unfold minorArcGeometricBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem minor_arc_separated_kernel {ι : Type*} (S : Finset ι) (θ : ι → ℝ)
    (δ V : ℝ) (hδ : 0 < δ) (hV : 0 ≤ V)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (θ i : UnitAddCircle) (θ j : UnitAddCircle)) :
    (∑ i ∈ S, minorArcGeometricBound V (θ i)) ≤
      2 * V + (2 / δ) * (1 + Real.log (⌈(1 / 2 : ℝ) / δ⌉₊ : ℝ)) := by
  let x := fun i => θ i - (round (θ i) : ℝ)
  apply minor_arc_packing_sum S x (fun i => minorArcGeometricBound V (θ i))
    δ V (1 / 2) hδ hV
  · intro i hi j hj hij
    exact (hsep i hi j hj hij).trans (minor_arc_centered_difference (θ i) (θ j))
  · intro i _
    exact minor_arc_centered_small (θ i)
  · intro i _
    exact minor_arc_kernel_le V (θ i)
  · intro i _ hxi
    have hnorm : ‖(θ i : UnitAddCircle)‖ = |x i| := UnitAddCircle.norm_eq
    have hb := minor_arc_geometric_circle (L := V) (hnorm.symm ▸ hxi)
    apply (hb.trans (min_le_right _ _)).trans
    rw [hnorm]
    exact one_div_le_one_div_of_le hxi (by linarith)

theorem minor_arc_rational_block (S : Finset ℤ) (α : ℝ) (a q : ℤ)
    (hq : 0 < q) (hcop : IsCoprime q a) (V : ℝ) (hV : 0 ≤ V)
    (hwidth : ∀ m ∈ S, ∀ n ∈ S, |((m - n : ℤ) : ℝ)| ≤ (q : ℝ) / 2)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ S, minorArcGeometricBound V ((n : ℝ) * α)) ≤
      2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hb := minor_arc_separated_kernel S (fun n => (n : ℝ) * α)
    (1 / (2 * (q : ℝ))) V (by positivity) hV
    (fun m hm n hn hmn => minor_arc_pair_spacing hq hcop hmn (hwidth m hm n hn) happrox)
  have hceil : ⌈(1 / 2 : ℝ) / (1 / (2 * (q : ℝ)))⌉₊ = q.toNat := by
    rw [show (1 / 2 : ℝ) / (1 / (2 * (q : ℝ))) = (q : ℝ) by field_simp]
    exact Nat.ceil_intCast q
  have hcast : (q.toNat : ℝ) = q := by exact_mod_cast Int.toNat_of_nonneg hq.le
  rw [hceil, hcast] at hb
  have he : 2 / (1 / (2 * (q : ℝ))) = 4 * (q : ℝ) := by field_simp; norm_num
  rw [he] at hb
  exact hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcVinogradov
namespace OAI

/-! The finite Vinogradov bound obtained by partitioning an integer range
into blocks shorter than half the rational denominator. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_nat_rational_block (S : Finset ℕ) (α : ℝ) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a) (V : ℝ) (hV : 0 ≤ V)
    (hwidth : ∀ m ∈ S, ∀ n ∈ S, |(m : ℝ) - n| ≤ (q : ℝ) / 2)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ S, minorArcGeometricBound V ((n : ℝ) * α)) ≤
      2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  let e : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
  have hb := minor_arc_rational_block (S.map e) α a (q : ℤ)
    (by exact_mod_cast hq) hcop V hV ?_ (by simpa using happrox)
  · simpa only [sum_map, e, Function.Embedding.coeFn_mk, Int.cast_natCast] using hb
  · intro m hm n hn
    obtain ⟨m', hm', rfl⟩ := mem_map.mp hm
    obtain ⟨n', hn', rfl⟩ := mem_map.mp hn
    simpa only [e, Function.Embedding.coeFn_mk, Int.cast_sub, Int.cast_natCast] using
      hwidth m' hm' n' hn'

theorem minor_arc_vinogradov (N q : ℕ) (α V : ℝ) (a : ℤ)
    (hq : 2 ≤ q) (hV : 0 ≤ V) (hcop : IsCoprime (q : ℤ) a)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ range N, minorArcGeometricBound V ((n : ℝ) * α)) ≤
      (3 * (N : ℝ) / q + 1) * (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) := by
  let L := q / 2
  let J := N / L + 1
  let S := fun j : ℕ => (range N).filter (fun n => n / L = j)
  have hL : 0 < L := Nat.div_pos hq (by norm_num)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hLq : (L : ℝ) ≤ (q : ℝ) / 2 := by
    exact Nat.cast_div_le
  have hblock (j : ℕ) : (∑ n ∈ S j, minorArcGeometricBound V ((n : ℝ) * α)) ≤
      2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
    apply minor_arc_nat_rational_block (S j) α a q (by omega) hcop V hV ?_ happrox
    intro m hm n hn
    have hmj : m / L = j := (mem_filter.mp hm).2
    have hnj : n / L = j := (mem_filter.mp hn).2
    have hmlo : j * L ≤ m := by simpa only [hmj] using Nat.div_mul_le_self m L
    have hnlo : j * L ≤ n := by simpa only [hnj] using Nat.div_mul_le_self n L
    have hmhi : m < L * (j + 1) := by simpa only [hmj] using Nat.lt_mul_div_succ m hL
    have hnhi : n < L * (j + 1) := by simpa only [hnj] using Nat.lt_mul_div_succ n hL
    have hmi : (j : ℝ) * L ≤ m := by exact_mod_cast hmlo
    have hni : (j : ℝ) * L ≤ n := by exact_mod_cast hnlo
    have hma : (m : ℝ) < L * ((j : ℝ) + 1) := by exact_mod_cast hmhi
    have hna : (n : ℝ) < L * ((j : ℝ) + 1) := by exact_mod_cast hnhi
    apply (le_of_lt (abs_lt.mpr ⟨?_, ?_⟩)).trans hLq <;> nlinarith
  have hpart : (∑ n ∈ range N, minorArcGeometricBound V ((n : ℝ) * α)) =
      ∑ j ∈ range J, ∑ n ∈ S j, minorArcGeometricBound V ((n : ℝ) * α) := by
    symm
    apply sum_fiberwise_of_maps_to
    intro n hn
    apply mem_range.mpr
    have hle : n / L ≤ N / L := Nat.div_le_div_right (mem_range.mp hn).le
    omega
  have hqL : (q : ℝ) ≤ 3 * (L : ℝ) := by
    have hmod := Nat.mod_lt q (by norm_num : 0 < 2)
    have hid := Nat.mod_add_div q 2
    have hqq : q ≤ 3 * L := by dsimp [L] at *; omega
    exact_mod_cast hqq
  have hJ : (J : ℝ) ≤ 3 * (N : ℝ) / q + 1 := by
    have hquot : (N : ℝ) / L ≤ 3 * (N : ℝ) / q := by
      apply (div_le_div_iff₀ hLr hqr).mpr
      nlinarith [mul_le_mul_of_nonneg_left hqL (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    calc
      _ = ((N / L : ℕ) : ℝ) + 1 := by simp [J]
      _ ≤ (N : ℝ) / L + 1 := add_le_add Nat.cast_div_le le_rfl
      _ ≤ _ := by linarith
  have hconstant : 0 ≤ 2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    positivity
  rw [hpart]
  calc
    _ ≤ ∑ _j ∈ range J, (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) :=
      sum_le_sum (fun j _ => hblock j)
    _ = (J : ℝ) * (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) := by
      simp only [sum_const, card_range, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hJ hconstant

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcSignedKernel
namespace OAI

/-! The rational geometric-kernel bound on a symmetric integer range. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_natAbs_fiber (S : Finset ℤ) (k : ℕ) :
    (S.filter (fun n => n.natAbs = k)).card ≤ 2 := by
  have hs : S.filter (fun n => n.natAbs = k) ⊆ {(k : ℤ), -(k : ℤ)} := by
    intro n hn
    have ha : |n| = (k : ℤ) := by
      rw [← Int.natCast_natAbs, (mem_filter.mp hn).2]
    have he : |n| = |(k : ℤ)| := by simpa only [abs_of_nonneg (Int.natCast_nonneg k)] using ha
    rcases abs_eq_abs.mp he with he | he
    · simp only [mem_insert, mem_singleton]
      exact Or.inl he
    · simp only [mem_insert, mem_singleton]
      exact Or.inr he
  exact (card_le_card hs).trans card_le_two

theorem minor_arc_signed_kernel (N q : ℕ) (α V : ℝ) (a : ℤ)
    (hq : 2 ≤ q) (hV : 0 ≤ V) (hcop : IsCoprime (q : ℤ) a)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), minorArcGeometricBound V ((n : ℝ) * α)) ≤
      2 * (3 * ((N : ℝ) + 1) / q + 1) *
        (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) := by
  let S := Icc (-(N : ℤ)) (N : ℤ)
  have hmap : ∀ n ∈ S, n.natAbs ∈ range (N + 1) := by
    intro n hn
    have hb : (n.natAbs : ℤ) ≤ (N : ℤ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr (mem_Icc.mp hn)
    have hbN : n.natAbs ≤ N := by exact_mod_cast hb
    exact mem_range.mpr (by omega)
  have he := minor_arc_fiber_sum S (range (N + 1)) Int.natAbs
    (fun n => minorArcGeometricBound V ((n : ℝ) * α)) 2 hmap
    (fun n _ => minor_arc_geometric_nonneg hV _)
    (fun n _ => by
      convert (preTransparency := .instances) (Nat.cast_le (α := ℝ)).mpr (minor_arc_natAbs_fiber S n) using 1
      apply congrArg (fun T : Finset ℤ => (T.card : ℝ))
      ext z
      simp only [mem_filter])
  have hs : (∑ n ∈ S, minorArcGeometricBound V ((n.natAbs : ℝ) * α)) =
      ∑ n ∈ S, minorArcGeometricBound V ((n : ℝ) * α) :=
    sum_congr rfl (fun n _ => minor_arc_geometric_natAbs V α n)
  rw [hs] at he
  have hv := minor_arc_vinogradov (N + 1) q α V a hq hV hcop happrox
  have htwice := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Nat.cast_add, Nat.cast_one] at htwice
  exact he.trans (by nlinarith [htwice])

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcPrimeKernel
namespace OAI

/-! The four-prime kernel in MRT (3.3), including arbitrary window lengths. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem minor_arc_prime_difference_kernel (P : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, p ≤ N) (α V : ℝ) (hV : 0 ≤ V) :
    (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
      minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄))) ≤
      (Finset.addEnergy P P : ℝ) *
        ∑ n ∈ Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
          minorArcGeometricBound V (α * (n : ℝ)) := by
  let S := (P ×ˢ P) ×ˢ (P ×ˢ P)
  let f : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun v =>
    ((v.1.1 : ℤ) + v.1.2) - ((v.2.1 : ℤ) + v.2.2)
  have hmap : ∀ v ∈ S, f v ∈ Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)) := by
    rintro ⟨⟨p, q⟩, ⟨r, s⟩⟩ hv
    obtain ⟨hpq, hrs⟩ := mem_product.mp hv
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    obtain ⟨hr, hs⟩ := mem_product.mp hrs
    have := hP p hp
    have := hP q hq
    have := hP r hr
    have := hP s hs
    apply mem_Icc.mpr
    dsimp [f]
    omega
  have he := minor_arc_fiber_sum S (Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))) f
    (fun n => minorArcGeometricBound V (α * (n : ℝ)))
    (Finset.addEnergy P P : ℝ) hmap
    (fun n _ => minor_arc_geometric_nonneg hV _)
    (fun n _ => by
      have hh := (Nat.cast_le (α := ℝ)).mpr (minor_arc_prime_shifted_fiber P n)
      simpa only [S, f] using hh)
  convert (preTransparency := .instances) he using 1
  dsimp [S, f]
  simp only [sum_product]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro s hs
  congr 1
  push_cast
  ring

theorem minor_arc_prime_kernel_rational (P : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ P, p ≤ N) (α V : ℝ) (hV : 0 ≤ V)
    (a : ℤ) (q : ℕ) (hq : 2 ≤ q) (hcop : IsCoprime (q : ℤ) a)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
      minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄))) ≤
      (Finset.addEnergy P P : ℝ) *
        (2 * (3 * (2 * (N : ℝ) + 1) / q + 1) *
          (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)))) := by
  have he := minor_arc_prime_difference_kernel P N hP α V hV
  have hk := minor_arc_signed_kernel (2 * N) q α V a hq hV hcop happrox
  have hs : (∑ n ∈ Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
      minorArcGeometricBound V (α * (n : ℝ))) =
      ∑ n ∈ Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ),
        minorArcGeometricBound V ((n : ℝ) * α) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_comm α]
  rw [hs] at he
  apply he.trans
  have hm := mul_le_mul_of_nonneg_left hk
    (Nat.cast_nonneg (Finset.addEnergy P P) : (0 : ℝ) ≤ _)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcParameters
namespace OAI

/-! The explicit minor-arc parameter saving for the four-prime kernel. -/

namespace TwoPointCorrelations

lemma minor_arc_parameter_bound (R H W q V : ℝ)
    (hR : 1 ≤ R) (hW : 1 ≤ W) (hWR : W ≤ R)
    (hWq : W ≤ q) (hqH : q ≤ H / W) (hRH : R ≤ H / W)
    (hV : 0 ≤ V) (hVR : V ≤ H / R) :
    2 * (3 * (4 * R + 1) / q + 1) * (2 * V + 4 * q * (1 + Real.log q)) ≤
      192 * H * (1 + Real.log H) / W := by
  have hR0 : 0 < R := by linarith
  have hW0 : 0 < W := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le hW0 hWq
  have hH1 : 1 ≤ H := by
    have hwq : W * q ≤ H := by nlinarith [(le_div_iff₀ hW0).mp hqH]
    nlinarith
  have hH0 : 0 < H := by linarith
  have hqH' : q ≤ H := by
    have hmul := (le_div_iff₀ hW0).mp hqH
    nlinarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (hW.trans hWq)
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hlog : Real.log q ≤ Real.log H := Real.log_le_log hq0 hqH'
  have hA : 4 * R + 1 ≤ 5 * R := by linarith
  have h₁ : 12 * (4 * R + 1) * V / q ≤ 60 * H / W := by
    calc
      _ ≤ 12 * (5 * R) * (H / R) / q := by gcongr
      _ = 60 * H / q := by field_simp; ring
      _ ≤ _ := by gcongr
  have h₂ : 24 * (4 * R + 1) * (1 + Real.log q) ≤
      120 * (H / W) * (1 + Real.log H) := by
    calc
      _ ≤ 24 * (5 * R) * (1 + Real.log H) := by gcongr
      _ = 120 * R * (1 + Real.log H) := by ring
      _ ≤ _ := by gcongr
  have h₃ : 4 * V ≤ 4 * H / W := by
    calc
      _ ≤ 4 * (H / R) := mul_le_mul_of_nonneg_left hVR (by norm_num)
      _ = 4 * H / R := by ring
      _ ≤ _ := by gcongr
  have h₄ : 8 * q * (1 + Real.log q) ≤ 8 * (H / W) * (1 + Real.log H) := by
    gcongr
  have hsmall : 64 * H / W ≤ 64 * (H / W) * (1 + Real.log H) := by
    have hnonneg : 0 ≤ 64 * (H / W) := by positivity
    calc
      64 * H / W = (64 * (H / W)) * 1 := by ring
      _ ≤ (64 * (H / W)) * (1 + Real.log H) :=
        mul_le_mul_of_nonneg_left (by linarith) hnonneg
  have he : 2 * (3 * (4 * R + 1) / q + 1) * (2 * V + 4 * q * (1 + Real.log q)) =
      12 * (4 * R + 1) * V / q + 24 * (4 * R + 1) * (1 + Real.log q) +
        4 * V + 8 * q * (1 + Real.log q) := by field_simp; ring
  rw [he]
  calc
    _ ≤ (60 * H / W + 120 * (H / W) * (1 + Real.log H)) +
        4 * H / W + 8 * (H / W) * (1 + Real.log H) :=
      add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = 64 * H / W + 128 * (H / W) * (1 + Real.log H) := by ring
    _ ≤ 64 * (H / W) * (1 + Real.log H) +
        128 * (H / W) * (1 + Real.log H) := add_le_add hsmall le_rfl
    _ = 192 * H * (1 + Real.log H) / W := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicSummation
namespace OAI

/-! Summing the reciprocal logarithmic saving over dyadic prime blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma minor_arc_dyadic_prime_bounds {p j : ℕ} (hp : 0 < p) (hj : Nat.log 2 p = j) :
    2 ^ j ≤ p ∧ p ≤ 2 * 2 ^ j := by
  have hl := Nat.pow_log_le_self 2 hp.ne'
  have hu := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rw [hj] at hl hu
  rw [pow_succ] at hu
  exact ⟨hl, by omega⟩


lemma minor_arc_dyadic_log_sum (J : Finset ℕ) (N : ℕ)
    (hJ : J ⊆ Icc 1 N) :
    (∑ j ∈ J, 1 / Real.log ((2 : ℝ) ^ j)) ≤
      (1 + Real.log (N : ℝ)) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfull : (∑ j ∈ Icc 1 N, 1 / Real.log ((2 : ℝ) ^ j)) =
      (harmonic N : ℝ) / Real.log 2 := by
    simp only [Real.log_pow]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, sum_div]
    apply sum_congr rfl
    intro j _
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  calc
    _ ≤ ∑ j ∈ Icc 1 N, 1 / Real.log ((2 : ℝ) ^ j) := by
      apply sum_le_sum_of_subset_of_nonneg hJ
      intro j hj _
      rw [Real.log_pow]
      positivity
    _ = (harmonic N : ℝ) / Real.log 2 := hfull
    _ ≤ _ := div_le_div_of_nonneg_right (harmonic_le_one_add_log N) hlog2.le

lemma minor_arc_weighted_dyadic_log_sum (J : Finset ℕ) (N : ℕ)
    (hJ : J ⊆ Icc 1 N) (K : ℝ) (hK : 0 ≤ K) (S : ℕ → ℝ)
    (hS : ∀ j ∈ J, S j ≤ K / Real.log ((2 : ℝ) ^ j)) :
    (∑ j ∈ J, S j) ≤ K * (1 + Real.log (N : ℝ)) / Real.log 2 := by
  calc
    _ ≤ ∑ j ∈ J, K / Real.log ((2 : ℝ) ^ j) := sum_le_sum hS
    _ = K * ∑ j ∈ J, 1 / Real.log ((2 : ℝ) ^ j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ K * ((1 + Real.log (N : ℝ)) / Real.log 2) :=
      mul_le_mul_of_nonneg_left (minor_arc_dyadic_log_sum J N hJ) hK
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcRamareWindow
namespace OAI

/-! Exact change of variables from the Ramaré coefficient to the finite
bilinear short-window sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma minor_arc_window_weighted_sum (M p k H : ℕ) (a : ℕ → ℂ) (c : ℂ) (β : ℝ) :
    (∑ m ∈ range M, a m * minorArcWindowTerm M p k H c β m) =
      ∑ m ∈ minorArcWindowInterval M p k H, a m * (c * additiveCharacter β m) := by
  let W := minorArcWindowInterval M p k H
  have hsub : W ⊆ range M := by
    intro m hm
    exact mem_range.mpr ((mem_Ico.mp hm).2.trans_le (min_le_left _ _))
  have hf : (range M).filter (fun m => m ∈ W) = W := by
    ext m
    simp only [mem_filter]
    exact ⟨And.right, fun hm => ⟨hsub hm, hm⟩⟩
  change (∑ m ∈ range M, a m * minorArcWindowTerm M p k H c β m) =
    ∑ m ∈ W, a m * (c * additiveCharacter β m)
  rw [← hf, sum_filter]
  apply sum_congr rfl
  intro m _
  change a m * (if m ∈ W then c * additiveCharacter β m else 0) =
    if m ∈ W then a m * (c * additiveCharacter β m) else 0
  split_ifs <;> simp

lemma minor_arc_window_interval_eq_of_cutoff (M A k H : ℕ)
    (hM : (k + H) / A < M) :
    minorArcWindowInterval M A k H = Ico (k / A + 1) ((k + H) / A + 1) := by
  unfold minorArcWindowInterval
  rw [min_eq_right (by omega : (k + H) / A + 1 ≤ M)]

lemma minor_arc_bilinear_cutoff_eq (P : Finset ℕ) (M N H d k : ℕ)
    (hM : ∀ p ∈ P, (k + H) / (d * p) < M)
    (hN : ∀ p ∈ P, (k + H) / (d * p) < N)
    (a c : ℕ → ℂ) (α : ℝ) :
    minorArcBilinearWindow P M H d a c α k =
      minorArcBilinearWindow P N H d a c α k := by
  unfold minorArcBilinearWindow
  simp only [mul_sum]
  rw [sum_comm, sum_comm (s := range N) (t := P)]
  apply sum_congr rfl
  intro p hp
  rw [minor_arc_window_weighted_sum, minor_arc_window_weighted_sum,
    minor_arc_window_interval_eq_of_cutoff M (d * p) k H (hM p hp),
    minor_arc_window_interval_eq_of_cutoff N (d * p) k H (hN p hp)]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicWindows
namespace OAI

/-! Splitting only the prime index into dyadic blocks. The cofactor
coefficient, including its full-prime-set denominator, stays fixed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma minor_arc_dyadic_primes_bounds (P : Finset ℕ) (j p : ℕ)
    (hp : p ∈ minorArcDyadicPrimes P j) (hp0 : 0 < p) :
    2 ^ j ≤ p ∧ p ≤ 2 * 2 ^ j :=
  minor_arc_dyadic_prime_bounds hp0 (mem_filter.mp hp).2

lemma minor_arc_bilinear_dyadic_partition (J P : Finset ℕ)
    (hJ : ∀ p ∈ P, Nat.log 2 p ∈ J) (M H d k : ℕ)
    (a c : ℕ → ℂ) (α : ℝ) :
    minorArcBilinearWindow P M H d a c α k =
      ∑ j ∈ J, minorArcBilinearWindow (minorArcDyadicPrimes P j) M H d a c α k := by
  unfold minorArcBilinearWindow
  have hp (m : ℕ) : (∑ j ∈ J, ∑ p ∈ minorArcDyadicPrimes P j,
      minorArcWindowTerm M (d * p) k H (c p) (α * p) m) =
      ∑ p ∈ P, minorArcWindowTerm M (d * p) k H (c p) (α * p) m :=
    sum_fiberwise_of_maps_to hJ _
  rw [sum_comm (s := J) (t := range M)]
  apply sum_congr rfl
  intro m _
  rw [← mul_sum, hp]

lemma minor_arc_bilinear_dyadic_cutoffs (J P : Finset ℕ)
    (hJ : ∀ p ∈ P, Nat.log 2 p ∈ J) (M H d k : ℕ) (N : ℕ → ℕ)
    (hM : ∀ p ∈ P, (k + H) / (d * p) < M)
    (hN : ∀ j ∈ J, ∀ p ∈ minorArcDyadicPrimes P j, (k + H) / (d * p) < N j)
    (a c : ℕ → ℂ) (α : ℝ) :
    minorArcBilinearWindow P M H d a c α k =
      ∑ j ∈ J, minorArcBilinearWindow (minorArcDyadicPrimes P j) (N j) H d a c α k := by
  rw [minor_arc_bilinear_dyadic_partition J P hJ]
  apply sum_congr rfl
  intro j hj
  exact minor_arc_bilinear_cutoff_eq (minorArcDyadicPrimes P j) M (N j) H d k
    (fun p hp => hM p (mem_filter.mp hp).1) (hN j hj) a c α

lemma minor_arc_bilinear_dyadic_sum_le (J P : Finset ℕ)
    (hJ : ∀ p ∈ P, Nat.log 2 p ∈ J) (X M H d : ℕ) (N : ℕ → ℕ)
    (hM : ∀ k ∈ range X, ∀ p ∈ P, (k + H) / (d * p) < M)
    (hN : ∀ j ∈ J, ∀ k ∈ range X, ∀ p ∈ minorArcDyadicPrimes P j,
      (k + H) / (d * p) < N j)
    (a c : ℕ → ℂ) (α : ℝ) :
    (∑ k ∈ range X, ‖minorArcBilinearWindow P M H d a c α k‖) ≤
      ∑ j ∈ J, ∑ k ∈ range X,
        ‖minorArcBilinearWindow (minorArcDyadicPrimes P j) (N j) H d a c α k‖ := by
  calc
    _ ≤ ∑ k ∈ range X, ∑ j ∈ J,
        ‖minorArcBilinearWindow (minorArcDyadicPrimes P j) (N j) H d a c α k‖ := by
      apply sum_le_sum
      intro k hk
      rw [minor_arc_bilinear_dyadic_cutoffs J P hJ M H d k N
        (hM k hk) (fun j hj => hN j hj k hk)]
      exact norm_sum_le _ _
    _ = _ := sum_comm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcSieveSaving
namespace OAI

/-! The four-prime estimate in corrected MRT, equation (3.3). -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

/-- The additive-energy sieve and rational kernel give the required uniform
four-prime saving. The prime set may be any subset of the dyadic prime block. -/
theorem minor_arc_sieve_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (P : Finset ℕ) (N : ℕ),
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ p ≤ N) → (N : ℝ) ≤ 2 * R →
      ∀ H W V : ℝ, 1 ≤ W → W ≤ R →
      ∀ (a : ℤ) (q : ℕ), 2 ≤ q → W ≤ (q : ℝ) → (q : ℝ) ≤ H / W →
      R ≤ H / W → 0 ≤ V → V ≤ H / R →
      ∀ α : ℝ, IsCoprime (q : ℤ) a →
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄))) ≤
          C * H * R ^ 3 * (1 + Real.log H) / (W * Real.log R ^ 4) := by
  obtain ⟨C, hC, henergy⟩ := sieve_prime_additive_energy
  refine ⟨192 * C, by positivity, ?_⟩
  filter_upwards [henergy, eventually_ge_atTop (1 : ℝ)] with R henergy hR
  intro P N hP hN H W V hW hWR a q hq hWq hqH hRH hV hVR α hcop happ
  have hE := henergy P (fun p hp =>
    ⟨(hP p hp).1, (hP p hp).2.1,
      (show (p : ℝ) ≤ N by exact_mod_cast (hP p hp).2.2).trans hN⟩)
  have hkernel := minor_arc_prime_kernel_rational P N (fun p hp => (hP p hp).2.2)
    α V hV a q hq hcop happ
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hparam := minor_arc_parameter_bound R H W (q : ℝ) V hR hW hWR hWq hqH hRH hV hVR
  have hmon :
      2 * (3 * (2 * (N : ℝ) + 1) / q + 1) *
        (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) ≤
      2 * (3 * (4 * R + 1) / q + 1) *
        (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) := by
    have hnum : 3 * (2 * (N : ℝ) + 1) ≤ 3 * (4 * R + 1) := by linarith
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (div_le_div_of_nonneg_right hnum hqpos.le) le_rfl
  have hparam0 : 0 ≤ 192 * H * (1 + Real.log H) / W :=
    (by positivity : 0 ≤
      2 * (3 * (2 * (N : ℝ) + 1) / q + 1) *
        (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)))) |>.trans (hmon.trans hparam)
  calc
    _ ≤ (Finset.addEnergy P P : ℝ) *
        (192 * H * (1 + Real.log H) / W) :=
      hkernel.trans (mul_le_mul_of_nonneg_left (hmon.trans hparam) (Nat.cast_nonneg _))
    _ ≤ (C * R ^ 3 / Real.log R ^ 4) *
        (192 * H * (1 + Real.log H) / W) := mul_le_mul_of_nonneg_right hE hparam0
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcBilinearSieve
namespace OAI

/-! The prime sieve saving for the actual finite bilinear short-window sum. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem minor_arc_bilinear_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (P : Finset ℕ) (N X M H d : ℕ), 0 < d →
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ R ≤ (p : ℝ) ∧ p ≤ N) → (N : ℝ) ≤ 2 * R →
      ∀ (a c : ℕ → ℂ), (∀ m ∈ range M, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ W : ℝ, 1 ≤ W → W ≤ R → R ≤ (H : ℝ) / W →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q → W ≤ (q : ℝ) → (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P M H d a c α k‖) ^ 4 ≤
        C * (M : ℝ) ^ 3 * (X * (3 * H + 1) ^ 3 : ℕ) * H * R ^ 3 *
          (1 + Real.log (2 * (H : ℝ))) / (W * Real.log R ^ 4) := by
  obtain ⟨C, hC, hk⟩ := minor_arc_sieve_saving
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hk, eventually_ge_atTop (1 : ℝ)] with R hk hR
  intro P N X M H d hd hP hN a c ha hc W hW hWR hRH r q hq hWq hqH α hcop happ
  have hW0 : 0 < W := by linarith
  have hR0 : 0 < R := by linarith
  have hHR : R ≤ (H : ℝ) := by
    exact (le_mul_of_one_le_right hR0.le hW).trans ((le_div_iff₀ hW0).mp hRH)
  have hH0 : 0 ≤ (H : ℝ) := Nat.cast_nonneg H
  have hdouble : ∀ p ∈ P, 0 < p ∧ ∀ s ∈ P, s ≤ 2 * p := by
    intro p hp
    have hpR := (hP p hp).2.2.1
    constructor
    · have hp1 : (1 : ℝ) ≤ p := hR.trans hpR
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp1)
    · intro s hs
      have hsN : (s : ℝ) ≤ N := by exact_mod_cast (hP s hs).2.2.2
      have hsp : (s : ℝ) ≤ 2 * (p : ℝ) := by linarith
      exact_mod_cast hsp
  have hV : ∀ p ∈ P, (H : ℝ) / (d * p : ℕ) + 1 ≤ 2 * (H : ℝ) / R := by
    intro p hp
    have hpR := (hP p hp).2.2.1
    have hd1 : 1 ≤ d := hd
    have hdp : R ≤ ((d * p : ℕ) : ℝ) := by
      have hpdp : p ≤ d * p := by nlinarith
      exact hpR.trans (by exact_mod_cast hpdp)
    have hdiv : (H : ℝ) / (d * p : ℕ) ≤ (H : ℝ) / R :=
      div_le_div_of_nonneg_left hH0 hR0 hdp
    have hone : 1 ≤ (H : ℝ) / R := (le_div_iff₀ hR0).mpr (by simpa using hHR)
    calc
      _ ≤ (H : ℝ) / R + (H : ℝ) / R := add_le_add hdiv hone
      _ = _ := by ring
  have hbilinear := minor_arc_bilinear_fourth P X M H d hd hdouble a c ha hc α
    (2 * (H : ℝ) / R) hV
  have hHdiv : (H : ℝ) / W ≤ (2 * (H : ℝ)) / W := by gcongr; linarith
  have hkernel := hk P N (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.2⟩)
    hN (2 * (H : ℝ)) W (2 * (H : ℝ) / R) hW hWR r q hq hWq
    (hqH.trans hHdiv) (hRH.trans hHdiv) (by positivity) (le_refl _) α hcop happ
  have hfactor : 0 ≤ (M : ℝ) ^ 3 * (X * (3 * H + 1) ^ 3 : ℕ) := by positivity
  apply hbilinear.trans
  convert (preTransparency := .instances) mul_le_mul_of_nonneg_left hkernel hfactor using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcCofactorCutoff
namespace OAI

/-! The finite cofactor cutoff needed by the literal short-window sum. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma minor_arc_cofactor_cutoff (X H R p k : ℕ) (hR : 0 < R)
    (hRp : R ≤ p) (hk : k < X) :
    (k + H) / p < (X + H) / R + 1 := by
  have h₁ : (k + H) / p ≤ (k + H) / R := Nat.div_le_div_left hRp hR
  have h₂ : (k + H) / R ≤ (X + H) / R := Nat.div_le_div_right (by omega)
  omega

lemma minor_arc_cofactor_cutoff_bound (X H R : ℕ) (hR : 0 < R)
    (hRX : R ≤ X) (hHX : H ≤ X) :
    (((X + H) / R + 1 : ℕ) : ℝ) ≤ 3 * (X : ℝ) / R := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hHX' : (H : ℝ) ≤ X := by exact_mod_cast hHX
  have hRX' : (R : ℝ) ≤ X := by exact_mod_cast hRX
  have hdiv : (((X + H) / R : ℕ) : ℝ) ≤ ((X : ℝ) + H) / R := by
    simpa only [Nat.cast_add] using (Nat.cast_div_le (m := X + H) (n := R) (α := ℝ))
  push_cast
  calc
    _ ≤ ((X : ℝ) + H) / R + 1 := add_le_add hdiv le_rfl
    _ ≤ 3 * (X : ℝ) / R := by
      apply (le_div_iff₀ hR0).mpr
      rw [add_mul, div_mul_cancel₀ _ hR0.ne', one_mul]
      linarith

lemma minor_arc_origin_factor_bound (X H : ℕ) (hH : 1 ≤ H) :
    (X * (3 * H + 1) ^ 3 : ℕ) ≤ 64 * (X : ℝ) * (H : ℝ) ^ 3 := by
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hbase : 3 * (H : ℝ) + 1 ≤ 4 * H := by linarith
  have hc := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * (H : ℝ) + 1) hbase 3
  push_cast
  calc
    _ ≤ (X : ℝ) * (4 * H) ^ 3 := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg X)
    _ = _ := by ring

lemma minor_arc_cofactor_total_bound (X H R : ℕ) (hR : 0 < R)
    (hRX : R ≤ X) (hHX : H ≤ X) (hH : 1 ≤ H) :
    ((((X + H) / R + 1 : ℕ) : ℝ) ^ 3 *
        (X * (3 * H + 1) ^ 3 : ℕ) * H * (R : ℝ) ^ 3) ≤
      1728 * (X : ℝ) ^ 4 * (H : ℝ) ^ 4 := by
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hM := minor_arc_cofactor_cutoff_bound X H R hR hRX hHX
  have hO := minor_arc_origin_factor_bound X H hH
  calc
    ((((X + H) / R + 1 : ℕ) : ℝ) ^ 3 *
        (X * (3 * H + 1) ^ 3 : ℕ) * H * (R : ℝ) ^ 3) ≤
        (3 * (X : ℝ) / R) ^ 3 * (64 * (X : ℝ) * (H : ℝ) ^ 3) * H * (R : ℝ) ^ 3 := by
      gcongr
    _ = _ := by field_simp [hR0]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicSieve
namespace OAI

/-! Cancellation of the dyadic cofactor scale in the fourth moment. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem minor_arc_dyadic_bilinear_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
      ∀ (P : Finset ℕ) (X H : ℕ), 1 ≤ H → H ≤ X → R ≤ X →
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ R ≤ p ∧ p ≤ 2 * R) →
      ∀ (a c : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ W : ℝ, 1 ≤ W → W ≤ (R : ℝ) → (R : ℝ) ≤ (H : ℝ) / W →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q → W ≤ (q : ℝ) → (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P ((X + H) / R + 1) H 1 a c α k‖) ^ 4 ≤
        C * (X : ℝ) ^ 4 * (H : ℝ) ^ 4 * (1 + Real.log (2 * (H : ℝ))) /
          (W * Real.log (R : ℝ) ^ 4) := by
  obtain ⟨C, hC, hbound⟩ := minor_arc_bilinear_sieve
  refine ⟨1728 * C, by positivity, ?_⟩
  have hb : ∀ᶠ R : ℕ in atTop, _ :=
    tendsto_natCast_atTop_atTop.eventually hbound
  filter_upwards [hb, eventually_ge_atTop 2] with R hbound hR
  intro P X H hH hHX hRX hP a c ha hc W hW hWR hRH r q hq hWq hqH α hcop happ
  have hR0 : 0 < R := by omega
  have hp : ∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ (R : ℝ) ≤ p ∧ p ≤ 2 * R := by
    intro p hp
    exact ⟨(hP p hp).1, (hP p hp).2.1, by exact_mod_cast (hP p hp).2.2.1,
      (hP p hp).2.2.2⟩
  have hbil := hbound P (2 * R) X ((X + H) / R + 1) H 1 (by norm_num) hp
    (by simp) a c (fun m _ => ha m) hc W hW hWR hRH
    r q hq hWq hqH α hcop happ
  have hlog : 0 ≤ 1 + Real.log (2 * (H : ℝ)) := by
    have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hh : 1 ≤ 2 * (H : ℝ) := by linarith
    linarith [Real.log_nonneg hh]
  have hK : 0 ≤ (1 + Real.log (2 * (H : ℝ))) / (W * Real.log (R : ℝ) ^ 4) :=
    div_nonneg hlog (mul_nonneg (by linarith) (by positivity))
  have hcore := mul_le_mul_of_nonneg_left
    (minor_arc_cofactor_total_bound X H R hR0 hRX hHX hH) hC.le
  have hfinal := mul_le_mul_of_nonneg_right hcore hK
  apply hbil.trans
  convert (preTransparency := .instances) hfinal using 1 <;> ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcParameterSaving
namespace OAI

/-! The minor-arc fourth-root estimate retains the freely chosen
Diophantine parameter. This permits a common parameter in both arcs. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

lemma minor_arc_parameter_fourth_root (D S X H R W : ℝ)
    (hD : 0 ≤ D) (hX : 0 ≤ X) (hH : 0 < H)
    (hlogH : 1 ≤ Real.log H) (hlogR : 0 < Real.log R) (hW : 0 < W)
    (hbound : S^4 ≤ D*X^4*H^4*(1+Real.log (2*H))/(W*Real.log R^4)) :
    S ≤ (3*D+1)*X*H*(Real.log H/W)^(1/4:ℝ)/Real.log R := by
  have hlog : 1+Real.log (2*H) ≤ 3*Real.log H := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hH.ne']
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hK : 1 ≤ 3*D+1 := by linarith
  have hKpow : 3*D ≤ (3*D+1)^4 := by
    have hh := pow_le_pow_right₀ hK (by omega : 1 ≤ 4)
    simp only [pow_one] at hh
    linarith
  have hroot : ((Real.log H/W)^(1/4:ℝ))^4=Real.log H/W := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ Real.log H/W)]
    norm_num
  have hs : S^4 ≤ 3*D*(X*H*(Real.log H/W)^(1/4:ℝ)/Real.log R)^4 := by
    calc
      _ ≤ D*X^4*H^4*(1+Real.log (2*H))/(W*Real.log R^4) := hbound
      _ ≤ D*X^4*H^4*(3*Real.log H)/(W*Real.log R^4) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
      _ = _ := by
        rw [div_pow,mul_pow,mul_pow,hroot]
        field_simp
  apply le_of_pow_le_pow_left₀ (by norm_num : (4:ℕ) ≠ 0) (by positivity)
  calc
    _ ≤ 3*D*(X*H*(Real.log H/W)^(1/4:ℝ)/Real.log R)^4 := hs
    _ ≤ (3*D+1)^4*(X*H*(Real.log H/W)^(1/4:ℝ)/Real.log R)^4 :=
      mul_le_mul_of_nonneg_right hKpow (by positivity)
    _ = _ := by ring

theorem minor_arc_dyadic_parameter_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℕ in atTop,
      ∀ (P : Finset ℕ) (X H : ℕ), 1 ≤ H → H ≤ X → R ≤ X →
      1 ≤ Real.log (H:ℝ) →
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ R ≤ p ∧ p ≤ 2*R) →
      ∀ (a c : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ W : ℝ, 1 ≤ W → W ≤ (R:ℝ) → (R:ℝ) ≤ (H:ℝ)/W →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q → W ≤ (q:ℝ) → (q:ℝ) ≤ (H:ℝ)/W →
      ∀ α : ℝ, IsCoprime (q:ℤ) r → |α-(r:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P ((X+H)/R+1) H 1 a c α k‖) ≤
        C*(X:ℝ)*H*(Real.log (H:ℝ)/W)^(1/4:ℝ)/Real.log (R:ℝ) := by
  obtain ⟨D,hD,hbound⟩ := minor_arc_dyadic_bilinear_sieve
  refine ⟨3*D+1,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with R hbound hR
  intro P X H hH hHX hRX hlogH hP a c ha hc W hW hWR hRH r q hq hWq hqH α hcop happ
  have hH0 : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hlogR : 0 < Real.log (R:ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  exact minor_arc_parameter_fourth_root D _ X H R W hD.le (Nat.cast_nonneg X)
    hH0 hlogH hlogR (by linarith)
    (hbound P X H hH hHX hRX hP a c ha hc W hW hWR hRH r q hq hWq hqH α hcop happ)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcParameterIntegral
namespace OAI

/-! Summing the minor-arc estimate over the actual dyadic prime blocks. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem minor_arc_bilinear_parameter_saving_oai :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ (P J : Finset ℕ) (X H N : ℕ), 1 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → J ⊆ Icc 1 N →
      (∀ p ∈ P, Nat.log 2 p ∈ J) → (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
      (∀ j ∈ J, R₀ ≤ 2 ^ j ∧ 2 ^ j ≤ X) →
      ∀ W : ℝ, 1 ≤ W →
      (∀ j ∈ J, W ≤ (2 : ℝ) ^ j ∧
        (2 : ℝ) ^ j ≤ (H : ℝ) / W) →
      ∀ (a c : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      W ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P (X + H + 1) H 1 a c α k‖) ≤
        C * (X : ℝ) * H * (1 + Real.log (N : ℝ)) * (Real.log (H : ℝ)/W)^(1/4:ℝ) := by
  obtain ⟨D, hD, hbound⟩ := minor_arc_dyadic_parameter_saving
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hbound
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨D / Real.log 2, div_pos hD hlog2, R₀, ?_⟩
  intro P J X H N hH hHX hlogH hJN hPJ hP hR W hW hgeom a c ha hc r q hq hWq hqH α hcop happ
  let M : ℕ → ℕ := fun j => (X + H) / 2 ^ j + 1
  have hcut : ∀ k ∈ range X, ∀ p ∈ P, (k + H) / (1 * p) < X + H + 1 := by
    intro k hk p _
    have hkX := mem_range.mp hk
    have hd := Nat.div_le_self (k + H) (1 * p)
    omega
  have hcuts : ∀ j ∈ J, ∀ k ∈ range X, ∀ p ∈ minorArcDyadicPrimes P j,
      (k + H) / (1 * p) < M j := by
    intro j hj k hk p hp
    simp only [one_mul]
    exact minor_arc_cofactor_cutoff X H (2 ^ j) p k (by positivity)
      (minor_arc_dyadic_primes_bounds P j p hp (hP p (mem_filter.mp hp).1).1.pos).1
      (mem_range.mp hk)
  let K : ℝ := D * (X : ℝ) * H * (Real.log (H : ℝ)/W)^(1/4:ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hblock : ∀ j ∈ J,
      (∑ k ∈ range X, ‖minorArcBilinearWindow (minorArcDyadicPrimes P j) (M j) H 1 a c α k‖) ≤
        K / Real.log ((2 : ℝ) ^ j) := by
    intro j hj
    have hprime : ∀ p ∈ minorArcDyadicPrimes P j,
        p.Prime ∧ p ≠ 2 ∧ 2 ^ j ≤ p ∧ p ≤ 2 * 2 ^ j := by
      intro p hp
      have hpP := (mem_filter.mp hp).1
      exact ⟨(hP p hpP).1, (hP p hpP).2,
        minor_arc_dyadic_primes_bounds P j p hp (hP p hpP).1.pos⟩
    have hh := hR₀ (2 ^ j) (hR j hj).1 (minorArcDyadicPrimes P j) X H
      hH hHX (hR j hj).2 hlogH hprime a c ha
      (fun p hp => hc p (mem_filter.mp hp).1)
      W hW (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using (hgeom j hj).1)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using (hgeom j hj).2)
      r q hq hWq hqH α hcop happ
    dsimp [M, K]
    convert (preTransparency := .instances) hh using 1
    push_cast
    ring
  calc
    _ ≤ ∑ j ∈ J, ∑ k ∈ range X,
        ‖minorArcBilinearWindow (minorArcDyadicPrimes P j) (M j) H 1 a c α k‖ :=
      minor_arc_bilinear_dyadic_sum_le J P hPJ X (X + H + 1) H 1 M hcut hcuts a c α
    _ ≤ K * (1 + Real.log (N : ℝ)) / Real.log 2 :=
      minor_arc_weighted_dyadic_log_sum J N hJN K hK _ hblock
    _ = _ := by dsimp [K]; ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.minor_arc_bilinear_parameter_saving_oai := @OAI.TwoPointCorrelations.minor_arc_bilinear_parameter_saving_oai
