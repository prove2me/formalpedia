-- Prove2me | solution 1 for OAI.Erdos3.smoothSource_pair_kernel_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:19:22.642913+00:00
-- url     : https://prove2.me/submissions/3f9a0ca1-ad9c-47db-b4a8-2ef2d5ee34bd

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B089

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_finite_sum {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (y : Y) :
    (p.map F y).toReal = ∑ x ∈ S, (p x).toReal * (if F x = y then 1 else 0) := by
  rw [pmf_map_toReal_indicator]
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_image_finite_real_mean {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T) (φ : Y → ℝ) :
    (∑' x, (p x).toReal * φ (F x)) = ∑ y ∈ T, (p.map F y).toReal * φ y := by
  have hs : (∑' x, (p x).toReal * φ (F x)) = ∑ x ∈ S, (p x).toReal * φ (F x) :=
    (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq
  rw [hs]
  simp_rw [pmf_map_finite_sum p S hp F, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (F x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact (hn (hT x hx)).elim

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

open MeasureTheory
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem affinePairMatrix_mulVec {J : Type*} [Fintype J] (t u : J → ℤ)
    (w : Option J → ℤ) :
    affinePairMatrix t u *ᵥ w =
      ![w none + ∑ j, t j * w (some j), w none + ∑ j, u j * w (some j)] := by
  ext i
  fin_cases i <;> simp [affinePairMatrix, Matrix.mulVec, dotProduct, Fintype.sum_option]

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix Classical

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CellResidueCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_fiber_mean_square {Ω R : Type*} [Fintype Ω] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) (r : R) :
    (p.mean (fun x => if F x = r then e x else 0)) ^ 2 ≤
      p.eventProbability (fun x => F x = r) *
        p.mean (fun x => if F x = r then e x ^ 2 else 0) := by
  have h := p.mean_mul_sq_le (fun x => if F x = r then (1 : ℝ) else 0)
    (fun x => if F x = r then e x else 0)
  have h1 : (fun x => (if F x = r then (1 : ℝ) else 0) *
      (if F x = r then e x else 0)) = (fun x => if F x = r then e x else 0) := by
    funext x; split_ifs <;> simp
  have h2 : (fun x => (if F x = r then (1 : ℝ) else 0) ^ 2) =
      (fun x => if F x = r then (1 : ℝ) else 0) := by
    funext x; split_ifs <;> norm_num
  have h3 : (fun x => (if F x = r then e x else 0) ^ 2) =
      (fun x => if F x = r then e x ^ 2 else 0) := by
    funext x; split_ifs <;> norm_num
  rw [h1, h2, h3] at h
  have hmass : p.mean (fun x => if F x = r then (1 : ℝ) else 0) =
      p.eventProbability (fun x => F x = r) := by
    unfold FiniteProbabilityWeights.eventProbability
    apply congrArg p.mean
    funext x
    split_ifs <;> rfl
  rw [hmass] at h
  exact h

theorem finite_fiber_energy_sum {Ω R : Type*} [Fintype Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) :
    (∑ r, p.mean (fun x => if F x = r then e x ^ 2 else 0)) =
      p.mean (fun x => e x ^ 2) := by
  rw [← p.mean_sum]
  congr 1
  funext x
  simp

theorem finite_fiber_square_sum_le {Ω R : Type*}
    [Fintype Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) {c : ℝ}
    (hmass : ∀ r, p.eventProbability (fun x => F x = r) ≤ c) :
    (∑ r, (p.mean (fun x => if F x = r then e x else 0)) ^ 2) ≤
      c * p.mean (fun x => e x ^ 2) := by
  calc
    _ ≤ ∑ r, c * p.mean (fun x => if F x = r then e x ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro r _
      apply (finite_fiber_mean_square p F e r).trans
      exact mul_le_mul_of_nonneg_right (hmass r)
        (p.mean_nonneg (fun x => by split_ifs; exact sq_nonneg _; exact le_rfl))
    _ = _ := by rw [← Finset.mul_sum, finite_fiber_energy_sum]

theorem finite_residue_energy_bound {Ω R : Type*}
    [Fintype Ω] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) {K : ℝ}
    (hmass : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R) :
    (Fintype.card R : ℝ) *
        (∑ r, (p.mean (fun x => if F x = r then |e x| else 0)) ^ 2) ≤
      K * p.mean (fun x => e x ^ 2) := by
  have hcard : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have h := finite_fiber_square_sum_le p F (fun x => |e x|) hmass
  simp only [sq_abs] at h
  calc
    _ ≤ (Fintype.card R : ℝ) * ((K / Fintype.card R) * p.mean (fun x => e x ^ 2)) :=
      mul_le_mul_of_nonneg_left h hcard.le
    _ = _ := by field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_matching_residue_mean {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) :
    p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) =
      ∑ r, p.mean (fun x => if F x = r then |e x| else 0) *
        q.mean (fun y => if G y = r then |d y| else 0) := by
  have hpoint (x : X) (y : Y) :
      (if F x = G y then |e x| * |d y| else 0) =
        ∑ r, (if F x = r then |e x| else 0) * (if G y = r then |d y| else 0) := by
    symm
    rw [Finset.sum_eq_single (F x)]
    · by_cases h : F x = G y <;> simp [h, eq_comm]
    · intro r _ hr
      simp [Ne.symm hr]
    · simp
  simp_rw [hpoint, q.mean_sum, p.mean_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [q.mean_const_mul, p.mean_mul_const]

theorem finite_matching_residue_energy {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) {K : ℝ}
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R) :
    (Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) ≤
      K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2)) := by
  rw [finite_matching_residue_mean]
  have he := finite_residue_energy_bound p F e hp
  have hd := finite_residue_energy_bound q G d hq
  have hs : 2 * (∑ r, p.mean (fun x => if F x = r then |e x| else 0) *
      q.mean (fun y => if G y = r then |d y| else 0)) ≤
      (∑ r, (p.mean (fun x => if F x = r then |e x| else 0)) ^ 2) +
      (∑ r, (q.mean (fun y => if G y = r then |d y| else 0)) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    nlinarith [sq_nonneg (p.mean (fun x => if F x = r then |e x| else 0) -
      q.mean (fun y => if G y = r then |d y| else 0))]
  have hscaled := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) (Fintype.card R))
  nlinarith only [hscaled, he, hd]

theorem finite_matching_kernel_error {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) (k : X → Y → ℝ)
    {K epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (hk : ∀ x y, F x = G y → |k x y| ≤ epsilon) :
    (Fintype.card R : ℝ) *
        |p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      epsilon * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have ha : |p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      epsilon * p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) := by
    apply (p.abs_mean_le_mean_abs _).trans
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    apply (q.abs_mean_le_mean_abs _).trans
    rw [← q.mean_const_mul]
    apply q.mean_mono
    intro y
    by_cases h : F x = G y
    · simp only [h, ite_true, abs_mul]
      calc
        _ = |k x y| * (|e x| * |d y|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hk x y h) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · simp [h]
  calc
    _ ≤ (Fintype.card R : ℝ) * (epsilon *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0))) :=
      mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
    _ = epsilon * ((Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_matching_residue_energy p q F G e d hp hq) hepsilon

theorem finite_matching_kernel_approximation {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) (k l : X → Y → ℝ)
    {K epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (hk : ∀ x y, F x = G y → |k x y - l x y| ≤ epsilon) :
    |(Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      (Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then l x y * e x * d y else 0))| ≤
      epsilon * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have hid : p.mean (fun x => q.mean (fun y =>
      if F x = G y then (k x y - l x y) * e x * d y else 0)) =
      p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      p.mean (fun x => q.mean (fun y => if F x = G y then l x y * e x * d y else 0)) := by
    rw [← p.mean_sub]
    apply congrArg p.mean
    funext x
    rw [← q.mean_sub]
    apply congrArg q.mean
    funext y
    split_ifs <;> ring
  rw [← mul_sub, ← hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact finite_matching_kernel_error p q F G e d (fun x y => k x y - l x y) hepsilon hp hq hk

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_residue_kernel_expand {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : A → B → R → ℝ) :
    p.mean (fun x => q.mean (fun y => if F x = G y then k (C x) (D y) (F x) * e x * d y else 0)) =
      ∑ r, ∑ a, ∑ b, k a b r * finiteCellResidueMean p C F e a r * finiteCellResidueMean q D G d b r := by
  have hpoint (x : X) (y : Y) :
      (if F x = G y then k (C x) (D y) (F x) * e x * d y else 0) =
      ∑ r, ∑ a, ∑ b, k a b r * (if C x = a ∧ F x = r then e x else 0) *
        (if D y = b ∧ G y = r then d y else 0) := by
    symm
    rw [Finset.sum_eq_single (F x)]
    · rw [Finset.sum_eq_single (C x)]
      · rw [Finset.sum_eq_single (D y)]
        · by_cases h : F x = G y <;> simp [h, eq_comm]
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · simp
    · intro r _ hr
      simp [Ne.symm hr]
    · simp
  simp_rw [hpoint, q.mean_sum, p.mean_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [finiteCellResidueMean, q.mean_const_mul, p.mean_mul_const, p.mean_const_mul]

theorem weighted_cell_residue_cancellation {A B R : Type*}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    (p : FiniteProbabilityWeights A) (q : FiniteProbabilityWeights B)
    (e : A → R → ℝ) (d : B → R → ℝ) (k : A → B → R → ℝ)
    {delta gamma L : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (he : ∀ a r, |e a r| ≤ p.weight a * delta / Fintype.card R)
    (hd : ∀ b r, |d b r| ≤ q.weight b * gamma / Fintype.card R)
    (hk : ∀ a b r, |k a b r| ≤ L) :
    |(Fintype.card R : ℝ) * ∑ r, ∑ a, ∑ b, k a b r * e a r * d b r| ≤ L * delta * gamma := by
  let N : ℝ := Fintype.card R
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast Fintype.card_pos
  have hterm (a : A) (b : B) (r : R) :
      |k a b r * e a r * d b r| ≤ (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b) := by
    rw [abs_mul, abs_mul]
    have h := mul_le_mul (mul_le_mul (hk a b r) (he a r) (abs_nonneg _) hL)
      (hd b r) (abs_nonneg _) (mul_nonneg hL (div_nonneg (mul_nonneg (p.nonneg a) hdelta) hN.le))
    apply h.trans_eq
    dsimp only [N]
    ring
  have hs : |∑ r, ∑ a, ∑ b, k a b r * e a r * d b r| ≤
      ∑ _r : R, ∑ a, ∑ b, (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro r _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun b _ => hterm a b r)
  have hsum : (∑ _r : R, ∑ a, ∑ b, (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b)) =
      N * (L * delta * gamma / N ^ 2) := by
    simp only [← mul_assoc, ← Finset.mul_sum, q.total, p.total, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
  change |N * _| ≤ _
  rw [abs_mul, abs_of_pos hN]
  calc
    _ ≤ N * (N * (L * delta * gamma / N ^ 2)) :=
      mul_le_mul_of_nonneg_left (hs.trans_eq hsum) hN.le
    _ = _ := by field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_kernel_cancellation {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : A → B → R → ℝ)
    {delta gamma L : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (he : ∀ a r, |finiteCellResidueMean p C F e a r| ≤
      (finiteCellWeights p C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean q D G d b r| ≤
      (finiteCellWeights q D).weight b * gamma / Fintype.card R)
    (hk : ∀ a b r, |k a b r| ≤ L) :
    |(Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k (C x) (D y) (F x) * e x * d y else 0))| ≤
      L * delta * gamma := by
  rw [finite_cell_residue_kernel_expand]
  exact weighted_cell_residue_cancellation (finiteCellWeights p C) (finiteCellWeights q D)
    (finiteCellResidueMean p C F e) (finiteCellResidueMean q D G d) k hdelta hL he hd hk

theorem finite_cell_kernel_correlation {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : X → Y → ℝ) (cell : A → B → R → ℝ)
    {delta gamma L K zeta : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (he : ∀ a r, |finiteCellResidueMean p C F e a r| ≤
      (finiteCellWeights p C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean q D G d b r| ≤
      (finiteCellWeights q D).weight b * gamma / Fintype.card R)
    (hcell : ∀ a b r, |cell a b r| ≤ L)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |(Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      L * delta * gamma + zeta * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have herror := finite_matching_kernel_approximation p q F G e d k
    (fun x y => cell (C x) (D y) (F x)) hzeta hp hq hgrid
  have hmain := finite_cell_kernel_cancellation p q C D F G e d cell hdelta hL he hd hcell
  have htriangle := abs_add_le
    ((Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      (Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then cell (C x) (D y) (F x) * e x * d y else 0)))
    ((Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then cell (C x) (D y) (F x) * e x * d y else 0)))
  rw [sub_add_cancel] at htriangle
  exact (htriangle.trans (add_le_add herror hmain)).trans_eq (add_comm _ _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PMFSupportedMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem pmf_image_supported_real_mean {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (f : Y → ℝ) (hf : ∀ y ∉ T, f y = 0) :
    (∑' x, (p x).toReal * f (F x)) = ∑ y ∈ T, (p.map F y).toReal * f y := by
  let U := T ∪ S.image F
  have hU : ∀ x ∈ S, F x ∈ U :=
    fun x hx => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [pmf_image_finite_real_mean p S hp F U hU f]
  symm
  apply Finset.sum_subset Finset.subset_union_left
  intro y _ hy
  rw [hf y hy, mul_zero]

theorem pmf_pair_supported_real_mean {X Y Z : Type*} [DecidableEq Y] [DecidableEq Z]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (G : X → Z) (T : Finset Y) (U : Finset Z)
    (e : Y → ℝ) (d : Z → ℝ) (he : ∀ y ∉ T, e y = 0) (hd : ∀ z ∉ U, d z = 0) :
    (∑' x, (p x).toReal * (e (F x) * d (G x))) =
      ∑ y ∈ T, ∑ z ∈ U, (p.map (fun x => (F x, G x)) (y, z)).toReal * (e y * d z) := by
  have hoff (yz : Y × Z) (h : yz ∉ T ×ˢ U) : e yz.1 * d yz.2 = 0 := by
    by_cases hy : yz.1 ∈ T
    · have hz : yz.2 ∉ U := fun hz => h (Finset.mem_product.mpr ⟨hy, hz⟩)
      rw [hd _ hz, mul_zero]
    · rw [he _ hy, zero_mul]
  rw [pmf_image_supported_real_mean p S hp (fun x => (F x, G x)) (T ×ˢ U)
    (fun yz => e yz.1 * d yz.2) hoff, Finset.sum_product]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem smoothAffinePairRows_apply {K I : Type*} [Fintype K]
    (t u : K → ℤ) (z : Option K × I → ℤ) (i : I) :
    smoothAffinePairRows t u z i = ![smoothAffineSample t z i, smoothAffineSample u z i] := by
  rw [smoothAffinePairRows, affinePairMatrix_mulVec]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothWindowChange
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSourceFiniteWeights_mean {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (J → ℤ) → ℝ) :
    (smoothSourceFiniteWeights a S hS hZ).mean (fun z => f z.val) =
      ∑' z, (shiftedSmoothProductPMF a S hS hZ z).toReal * f z := by
  unfold FiniteProbabilityWeights.mean
  change (∑ z : rectangularWeightIndices a S 1,
    (shiftedSmoothProductPMF a S hS hZ z.val).toReal * f z.val) = _
  rw [Finset.sum_coe_sort (rectangularWeightIndices a S 1)
    (fun z => (shiftedSmoothProductPMF a S hS hZ z).toReal * f z)]
  exact (hasSum_sum_of_ne_finset_zero (fun z hz => by
    rw [shiftedSmoothProductPMF_toReal_zero_off a S hS hZ z hz, zero_mul])).tsum_eq.symm

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem affinePairLocations_rows {I : Type*} (xy : (I → ℤ) × (I → ℤ)) :
    affinePairLocations (affinePairRowsOfLocations xy) = xy := rfl

theorem affinePairRows_locations {I : Type*} (v : I → Fin 2 → ℤ) :
    affinePairRowsOfLocations (affinePairLocations v) = v := by
  funext i j
  fin_cases j <;> rfl

theorem affinePairLocations_injective {I : Type*} :
    Function.Injective (affinePairLocations (I := I)) := by
  intro x y h
  have he := congrArg affinePairRowsOfLocations h
  simpa only [affinePairRows_locations] using he

theorem smoothAffinePairRows_locations {J I : Type*} [Fintype J]
    (t u : J → ℤ) (z : Option J × I → ℤ) :
    affinePairLocations (smoothAffinePairRows t u z) = (smoothAffineSample t z, smoothAffineSample u z) := by
  apply Prod.ext
  · funext i
    change smoothAffinePairRows t u z i 0 = _
    rw [smoothAffinePairRows_apply]
    rfl
  · funext i
    change smoothAffinePairRows t u z i 1 = _
    rw [smoothAffinePairRows_apply]
    rfl

theorem affinePair_joint_probability {J I : Type*} [Fintype J]
    (p : PMF (Option J × I → ℤ)) (t u : J → ℤ) (x y : I → ℤ) :
    p.map (fun z => (smoothAffineSample t z, smoothAffineSample u z)) (x, y) =
      p.map (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y)) := by
  have he : (p.map (smoothAffinePairRows t u)).map affinePairLocations =
      p.map (fun z => (smoothAffineSample t z, smoothAffineSample u z)) := by
    rw [PMF.map_comp]
    congr 1
    funext z
    exact smoothAffinePairRows_locations t u z
  rw [← he]
  have h := pmf_map_injective_at (p.map (smoothAffinePairRows t u)) affinePairLocations
    affinePairLocations_injective (affinePairRowsOfLocations (x, y))
  simpa only [affinePairLocations_rows] using h

theorem smoothSource_pair_correlation {J I : Type*} [Fintype J] [Fintype I]
    (a S : Option J × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (t u : J → ℤ) (T U : Finset (I → ℤ)) (e d : (I → ℤ) → ℝ)
    (he : ∀ x ∉ T, e x = 0) (hd : ∀ y ∉ U, d y = 0) :
    (smoothSourceFiniteWeights a S hS hZ).mean
        (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val)) =
      ∑ x ∈ T, ∑ y ∈ U,
        ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
          (affinePairRowsOfLocations (x, y))).toReal * (e x * d y) := by
  classical
  rw [smoothSourceFiniteWeights_mean a S hS hZ
    (fun z => e (smoothAffineSample t z) * d (smoothAffineSample u z))]
  rw [pmf_pair_supported_real_mean (shiftedSmoothProductPMF a S hS hZ)
    (rectangularWeightIndices a S 1) (shiftedSmoothProductPMF_toReal_zero_off a S hS hZ)
    (smoothAffineSample t) (smoothAffineSample u) T U e d he hd]
  simp_rw [affinePair_joint_probability]

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniform_pair_sum {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → ℝ) :
    (Fintype.card X : ℝ) * Fintype.card Y *
        (FiniteProbabilityWeights.uniform X).mean
          (fun x => (FiniteProbabilityWeights.uniform Y).mean (f x)) = ∑ x, ∑ y, f x y := by
  simp_rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card, ← Finset.sum_div]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hX, hY]

theorem uniform_joint_residual_bound {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (joint k : X → Y → ℝ) (cell : A → B → R → ℝ)
    {V delta gamma L K epsilon zeta : ℝ} (hV : 0 < V)
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hepsilon : 0 ≤ epsilon) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform X).eventProbability (fun x => F x = r) ≤
      K / Fintype.card R)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform Y).eventProbability (fun y => G y = r) ≤
      K / Fintype.card R)
    (he : ∀ a r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform Y) D G d b r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform Y) D).weight b * gamma / Fintype.card R)
    (hcell : ∀ a b r, |cell a b r| ≤ L)
    (hoff : ∀ x y, F x ≠ G y → joint x y = 0)
    (hpoint : ∀ x y, F x = G y →
      |V * joint x y - (Fintype.card R : ℝ) * k x y| ≤ Fintype.card R * epsilon)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |∑ x, ∑ y, joint x y * e x * d y| ≤
      ((Fintype.card X : ℝ) * Fintype.card Y / V) *
        (L * delta * gamma + (epsilon + zeta) * (K / 2 *
          ((FiniteProbabilityWeights.uniform X).mean (fun x => e x ^ 2) +
           (FiniteProbabilityWeights.uniform Y).mean (fun y => d y ^ 2)))) := by
  let p := FiniteProbabilityWeights.uniform X
  let q := FiniteProbabilityWeights.uniform Y
  let N : ℝ := Fintype.card R
  let a : X → Y → ℝ := fun x y => V * joint x y / N
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast Fintype.card_pos
  have hnear (x : X) (y : Y) (h : F x = G y) : |a x y - k x y| ≤ epsilon := by
    have hid : a x y - k x y = (V * joint x y - N * k x y) / N := by
      dsimp only [a]
      field_simp [hN.ne']
    rw [hid, abs_div, abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    exact (hpoint x y h).trans_eq (mul_comm _ _)
  have happrox (x : X) (y : Y) (h : F x = G y) :
      |a x y - cell (C x) (D y) (F x)| ≤ epsilon + zeta :=
    (abs_sub_le (a x y) (k x y) (cell (C x) (D y) (F x))).trans
      (add_le_add (hnear x y h) (hgrid x y h))
  have hmain := finite_cell_kernel_correlation p q C D F G e d a cell
    hdelta hL (add_nonneg hepsilon hzeta) hp hq he hd hcell happrox
  have hpoint' (x : X) (y : Y) :
      N * (if F x = G y then a x y * e x * d y else 0) = V * (joint x y * e x * d y) := by
    by_cases h : F x = G y
    · simp only [h, ite_true, a]
      field_simp
    · simp [h, hoff x y h]
  have hscaled : N * p.mean (fun x => q.mean (fun y => if F x = G y then a x y * e x * d y else 0)) =
      V * p.mean (fun x => q.mean (fun y => joint x y * e x * d y)) := by
    calc
      _ = p.mean (fun x => q.mean (fun y => N *
          (if F x = G y then a x y * e x * d y else 0))) := by
        simp only [q.mean_const_mul, p.mean_const_mul]
      _ = _ := by simp only [hpoint', q.mean_const_mul, p.mean_const_mul]
  have hsum := uniform_pair_sum (fun x y => joint x y * e x * d y)
  have hid : (∑ x, ∑ y, joint x y * e x * d y) =
      ((Fintype.card X : ℝ) * Fintype.card Y / V) *
        (N * p.mean (fun x => q.mean (fun y => if F x = G y then a x y * e x * d y else 0))) := by
    rw [hscaled]
    change _ = _ * (V * (FiniteProbabilityWeights.uniform X).mean
      (fun x => (FiniteProbabilityWeights.uniform Y).mean (fun y => joint x y * e x * d y)))
    rw [← mul_assoc, div_mul_cancel₀ _ hV.ne']
    exact hsum.symm
  rw [hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card X : ℝ) * Fintype.card Y / V)]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSource_pair_kernel_reduction {J I A B R : Type*}
    [Fintype J] [Fintype I] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (a S : Option J × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (t u : J → ℤ) (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (C : T → A) (D : U → B) (F : T → R) (G : U → R)
    (k : T → U → ℝ) (cell : A → B → R → ℝ)
    {V delta gamma L K epsilon zeta : ℝ} (hV : 0 < V)
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hepsilon : 0 ≤ epsilon) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform T).eventProbability (fun x => F x = r) ≤
      K / Fintype.card R)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform U).eventProbability (fun y => G y = r) ≤
      K / Fintype.card R)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) C F (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) C).weight c * delta / Fintype.card R)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) D G (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) D).weight c * gamma / Fintype.card R)
    (hcell : ∀ c c' r, |cell c c' r| ≤ L)
    (hoff : ∀ x : T, ∀ y : U, F x ≠ G y →
      ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
        (affinePairRowsOfLocations (x.val, y.val))).toReal = 0)
    (hpoint : ∀ x : T, ∀ y : U, F x = G y →
      |V * ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
        (affinePairRowsOfLocations (x.val, y.val))).toReal -
          (Fintype.card R : ℝ) * k x y| ≤ Fintype.card R * epsilon)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |(smoothSourceFiniteWeights a S hS hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / V) *
        (L * delta * gamma + (epsilon + zeta) * (K / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  rw [smoothSource_pair_correlation a S hS hZ t u T U e d heoff hdoff]
  have h := uniform_joint_residual_bound C D F G (fun x => e x.val) (fun y => d y.val)
    (fun x y => ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
      (affinePairRowsOfLocations (x.val, y.val))).toReal) k cell
    hV hdelta hL hepsilon hzeta hp hq he hd hcell hoff hpoint hgrid
  have hsum (f : (I → ℤ) → (I → ℤ) → ℝ) :
      (∑ x : T, ∑ y : U, f x.val y.val) = ∑ x ∈ T, ∑ y ∈ U, f x y := by
    have hi (x : I → ℤ) : (∑ y : U, f x y.val) = ∑ y ∈ U, f x y :=
      Finset.sum_coe_sort U (f x)
    simp_rw [hi]
    exact Finset.sum_coe_sort T (fun x => ∑ y ∈ U, f x y)
  rw [hsum (fun x y => ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
    (affinePairRowsOfLocations (x, y))).toReal * e x * d y)] at h
  simpa only [Fintype.card_coe, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.smoothSource_pair_kernel_reduction.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.smoothSource_pair_kernel_reduction.{u_1, u_2, u_3, u_4, u_5}
