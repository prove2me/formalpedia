-- Prove2me | solution 1 for OAI.Erdos3.jointAffineBooleanGoodWeight_derivative_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:49:08.707339+00:00
-- url     : https://prove2.me/submissions/ab5d03ee-95c0-4268-a9b1-7d3f369e871b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B109

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CutoffImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem cutoff_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : Integrable w μ := by
  apply (integrable_const (1 : ℝ)).mono' hw.aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (hbound a).1]
  exact (hbound a).2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ProductCutoffBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem product_cutoff_range {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) : (∏ i, f i) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg (fun i _ => (hf i).1),
    Finset.prod_le_one (fun i _ => (hf i).1) (fun i _ => (hf i).2)⟩

theorem product_cutoff_tsupport_subset {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (f : ι → E → ℝ) (i : ι) : tsupport (fun x => ∏ j, f j x) ⊆ tsupport (f i) := by
  classical
  apply closure_mono
  intro x hx
  change f i x ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem product_cutoff_fderiv_norm_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E → ℝ) (x : E) (hf : ∀ i, DifferentiableAt ℝ (f i) x)
    (hrange : ∀ i, f i x ∈ Set.Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (fun y => ∏ i, f i y) x‖ ≤ ∑ i, ‖fderiv ℝ (f i) x‖ := by
  classical
  rw [fderiv_finsetProd (fun i _ => hf i)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hp0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j x :=
    Finset.prod_nonneg (fun j _ => (hrange j).1)
  have hp1 : (∏ j ∈ Finset.univ.erase i, f j x) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (hrange j).1) (fun j _ => (hrange j).2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp0]
  exact mul_le_of_le_one_left (norm_nonneg _) hp1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pderiv_prod_zero {α ι : Type*} (j : α) (s : Finset ι)
    (p : ι → MvPolynomial α ℝ) (hp : ∀ i ∈ s, MvPolynomial.pderiv j (p i) = 0) :
    MvPolynomial.pderiv j (∏ i ∈ s, p i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, hp i (Finset.mem_insert_self i s),
      ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))]
    simp

theorem pderiv_prod_one_active {α ι : Type*} [DecidableEq ι] (j : α) (s : Finset ι)
    (p : ι → MvPolynomial α ℝ) (i : ι) (hi : i ∈ s)
    (hp : ∀ k ∈ s.erase i, MvPolynomial.pderiv j (p k) = 0) :
    MvPolynomial.pderiv j (∏ k ∈ s, p k) =
      MvPolynomial.pderiv j (p i) * ∏ k ∈ s.erase i, p k := by
  rw [← Finset.mul_prod_erase s p hi, MvPolynomial.pderiv_mul, pderiv_prod_zero j _ p hp]
  simp

theorem pderiv_booleanCoefficient {α ι : Type*} [DecidableEq α]
    (j : ι) (f : Finset α → MvPolynomial ι ℝ) (s : Finset α) :
    MvPolynomial.pderiv j (booleanCoefficient f s) =
      booleanCoefficient (fun t => MvPolynomial.pderiv j (f t)) s := by
  classical
  unfold booleanCoefficient
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hc : (-1 : MvPolynomial ι ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [hc, MvPolynomial.pderiv_C_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffinePolynomial_eval {B F α : Type*} [Fintype α] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) :
    MvPolynomial.eval a (booleanAffinePolynomial b v t) =
      ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, v, r) := by
  simp only [booleanAffinePolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem booleanAffinePolynomial_pderiv {B F α : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq B] [DecidableEq F]
    (b b₀ : B) (v v₀ : F) (r : Option α) (t : Finset α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanAffinePolynomial b v t) =
      if b = b₀ ∧ v = v₀ then MvPolynomial.C (booleanFeature r t : ℝ) else 0 := by
  classical
  simp only [booleanAffinePolynomial, map_sum, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
    Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  by_cases hb : b = b₀ <;> by_cases hv : v = v₀
  · subst b
    subst v
    simp
  · simp [hb, hv]
  · simp [hb, hv]
  · simp [hb, hv]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_prod_pderiv_eval_abs_le {I K : Type*} (s : Finset K)
    (p : K → MvPolynomial I ℝ) (j : I) (a : I → ℝ) {L : ℝ} (hL : 1 ≤ L)
    (hp : ∀ k ∈ s, |MvPolynomial.eval a (p k)| ≤ L)
    (hd : ∀ k ∈ s, |MvPolynomial.eval a (MvPolynomial.pderiv j (p k))| ≤ 1) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (∏ k ∈ s, p k))| ≤ s.card * L ^ s.card := by
  have h := mvPolynomial_prod_pderiv_eval_abs_le_of_bound s p j a hL zero_le_one hp hd
  simpa only [mul_one] using h

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BooleanProductSampler
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

omit [Fintype B] in
theorem booleanBlockPolynomial_pderiv (b b₀ : B) (v₀ : F) (r : Option α) (t : Finset α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanBlockPolynomial (F := F) b t) =
      if b = b₀ then MvPolynomial.C (booleanFeature r t : ℝ) *
        ∏ k ∈ Finset.univ.erase v₀, booleanAffinePolynomial b k t else 0 := by
  by_cases hb : b = b₀
  · subst b
    rw [if_pos rfl, booleanBlockPolynomial, pderiv_prod_one_active
      (b₀, v₀, r) Finset.univ (fun k => booleanAffinePolynomial b₀ k t) v₀ (Finset.mem_univ _)]
    · simp only [booleanAffinePolynomial_pderiv, and_self, ite_true]
    · intro k hk
      simp only [booleanAffinePolynomial_pderiv, true_and]
      exact if_neg (Finset.ne_of_mem_erase hk)
  · rw [if_neg hb, booleanBlockPolynomial]
    apply pderiv_prod_zero
    intro k _
    simp only [booleanAffinePolynomial_pderiv, hb, false_and, ite_false]

theorem booleanSamplerPolynomial_pderiv (c : B → ℝ) (s : Finset α) (b₀ : B) (v₀ : F) (r : Option α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanSamplerPolynomial (F := F) c s) =
      booleanSelectedColumn c b₀ v₀ r s := by
  rw [booleanSamplerPolynomial, pderiv_booleanCoefficient]
  have hinner (t : Finset α) :
      MvPolynomial.pderiv (b₀, v₀, r)
        (∑ b : B, MvPolynomial.C (c b) * booleanBlockPolynomial (F := F) b t) =
      MvPolynomial.C (c b₀) * (MvPolynomial.C (booleanFeature r t : ℝ) *
        ∏ k ∈ Finset.univ.erase v₀, booleanAffinePolynomial b₀ k t) := by
    simp only [map_sum, MvPolynomial.pderiv_C_mul, booleanBlockPolynomial_pderiv, mul_ite, mul_zero]
    simp
  simp_rw [hinner]
  rw [booleanCoefficient_const_mul]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanFeature_abs_le_one {α : Type*} [DecidableEq α]
    (r : Option α) (t : Finset α) : |(booleanFeature r t : ℝ)| ≤ 1 := by
  cases r with
  | none => norm_num [booleanFeature]
  | some a => simp only [booleanFeature]; split_ifs <;> norm_num

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

theorem booleanAffinePolynomial_eval_abs_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) {R : ℝ}
    (ha : ∀ j, |a j| ≤ R) :
    |MvPolynomial.eval a (booleanAffinePolynomial b v t)| ≤ ((Fintype.card α : ℝ) + 1) * R := by
  rw [booleanAffinePolynomial_eval]
  calc
    _ ≤ ∑ r : Option α, |(booleanFeature r t : ℝ) * a (b, v, r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Option α, R := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (booleanFeature_abs_le_one r t)
        (ha (b, v, r)) (abs_nonneg _) zero_le_one
    _ = _ := by simp

theorem booleanSelectedColumn_eval_abs_le {B F α : Type*}
    [Fintype F] [Fintype α] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α)
    (a : BlockParameter B F α → ℝ) {R : ℝ} (ha : ∀ j, |a j| ≤ R) :
    |MvPolynomial.eval a (booleanSelectedColumn c b v r s)| ≤
      |c b| * ((2 : ℝ) ^ s.card *
        (((Fintype.card α : ℝ) + 1) * R) ^ (Fintype.card F - 1)) := by
  rw [booleanSelectedColumn, map_mul, MvPolynomial.eval_C, abs_mul, booleanCoefficient_map]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply booleanCoefficient_abs_le
  intro t _
  simp only [map_mul, MvPolynomial.eval_C, map_prod, abs_mul, Finset.abs_prod]
  calc
    _ ≤ 1 * ∏ _k ∈ Finset.univ.erase v, (((Fintype.card α : ℝ) + 1) * R) := by
      apply mul_le_mul (booleanFeature_abs_le_one r t)
      · exact Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun k _ => booleanAffinePolynomial_eval_abs_le a b k t ha)
      · exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)
      · exact zero_le_one
    _ = _ := by simp

theorem productMinorEntryBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorEntryBound q h C R := by
  unfold productMinorEntryBound
  positivity

theorem booleanSelectedMinor_entry_bound {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R) (row col : O) :
    |MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col)| ≤
      productMinorEntryBound (Fintype.card α) h C R := by
  unfold booleanSelectedMinor
  rw [booleanSamplerPolynomial_pderiv]
  have hcol := booleanSelectedColumn_eval_abs_le c (block col) v (r col) (sets row) a ha
  simp only [Fintype.card_fin] at hcol
  have htwo : (2 : ℝ) ^ (sets row).card ≤ 2 ^ h :=
    pow_le_pow_right₀ (by norm_num) (hcard row)
  have hpower : 0 ≤ (((Fintype.card α : ℝ) + 1) * R) ^ (h - 1) := by positivity
  exact hcol.trans (mul_le_mul (hc col) (mul_le_mul_of_nonneg_right htwo hpower)
    (mul_nonneg (by positivity) hpower) hC)

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

open scoped BigOperators

theorem booleanAffinePolynomial_pderiv_eval_abs_le {B F α : Type*}
    [Fintype α] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α)
    (j : BlockParameter B F α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanAffinePolynomial b v t))| ≤ 1 := by
  rcases j with ⟨b₀, v₀, r⟩
  rw [booleanAffinePolynomial_pderiv]
  split_ifs
  · simpa only [MvPolynomial.eval_C] using booleanFeature_abs_le_one r t
  · simp

theorem booleanSelectedColumn_pderiv_eval_abs_le {B F α : Type*}
    [Fintype F] [Fintype α] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α)
    (a : BlockParameter B F α → ℝ) {R : ℝ} (hR : 1 ≤ R) (ha : ∀ j, |a j| ≤ R)
    (j : BlockParameter B F α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanSelectedColumn c b v r s))| ≤
      |c b| * ((2 : ℝ) ^ s.card *
        (Fintype.card F * (((Fintype.card α : ℝ) + 1) * R) ^ Fintype.card F)) := by
  let L : ℝ := ((Fintype.card α : ℝ) + 1) * R
  have hL : 1 ≤ L := by
    dsimp [L]
    have hq : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hq (zero_le_one.trans hR)]
  rw [booleanSelectedColumn, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C,
    abs_mul, pderiv_booleanCoefficient, booleanCoefficient_map]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply booleanCoefficient_abs_le
  intro t _
  rw [MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.eval_C, abs_mul]
  have hd := mvPolynomial_prod_pderiv_eval_abs_le (Finset.univ.erase v)
    (fun k => booleanAffinePolynomial b k t) j a hL
    (fun k _ => booleanAffinePolynomial_eval_abs_le a b k t ha)
    (fun k _ => booleanAffinePolynomial_pderiv_eval_abs_le a b k t j)
  have hn : (Finset.univ.erase v).card ≤ Fintype.card F :=
    (Finset.card_erase_le).trans_eq (Finset.card_univ)
  have hpow := pow_le_pow_right₀ hL hn
  calc
    _ ≤ 1 * ((Finset.univ.erase v).card * L ^ (Finset.univ.erase v).card) :=
      mul_le_mul (booleanFeature_abs_le_one r t) hd (abs_nonneg _) zero_le_one
    _ ≤ Fintype.card F * L ^ Fintype.card F := by
      rw [one_mul]
      exact mul_le_mul (Nat.cast_le.mpr hn) hpow (pow_nonneg (zero_le_one.trans hL) _) (by positivity)

theorem productMinorPartialBound_nonneg (q h : ℕ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorPartialBound q h C R := by
  unfold productMinorPartialBound
  positivity

theorem booleanSelectedMinor_partial_bound {B O α : Type*}
    [Fintype B] [Fintype α] [DecidableEq B] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R)
    (row col : O) (j : BlockParameter B (Fin h) α) :
    |MvPolynomial.eval a (MvPolynomial.pderiv j (booleanSelectedMinor c sets block v r row col))| ≤
      productMinorPartialBound (Fintype.card α) h C R := by
  unfold booleanSelectedMinor
  rw [booleanSamplerPolynomial_pderiv]
  have hd := booleanSelectedColumn_pderiv_eval_abs_le c (block col) v (r col) (sets row) a hR ha j
  simp only [Fintype.card_fin] at hd
  have htwo : (2 : ℝ) ^ (sets row).card ≤ 2 ^ h :=
    pow_le_pow_right₀ (by norm_num) (hcard row)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hpos : 0 ≤ (h : ℝ) * (((Fintype.card α : ℝ) + 1) * R) ^ h := by positivity
  exact hd.trans (mul_le_mul (hc col) (mul_le_mul_of_nonneg_right htwo hpos)
    (mul_nonneg (by positivity) hpos) hC)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

theorem booleanMinorDeterminant_contDiff {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α) :
    ContDiff ℝ ∞ (booleanMinorDeterminant c sets block v r) := by
  change ContDiff ℝ ∞ (fun a => ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det)
  rw [polynomial_det_eval_function]
  exact mvPolynomial_contDiff_eval _

theorem productMinorDeterminantDerivativeBound_nonneg (n j q h : ℕ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ productMinorDeterminantDerivativeBound n j q h C R := by
  have he := productMinorEntryBound_nonneg q h hC hR
  have hd := productMinorPartialBound_nonneg q h hC hR
  unfold productMinorDeterminantDerivativeBound
  positivity

theorem booleanMinorDeterminant_fderiv_norm_le {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R) :
    ‖fderiv ℝ (booleanMinorDeterminant c sets block v r) a‖ ≤
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C R := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have he := productMinorEntryBound_nonneg (Fintype.card α) h hC hR0
  have hL : 1 ≤ 1 + productMinorEntryBound (Fintype.card α) h C R := by linarith
  have hentry (row col : O) :
      |MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col)| ≤
        1 + productMinorEntryBound (Fintype.card α) h C R := by
    have hbound := booleanSelectedMinor_entry_bound c sets block v r hcard a hC hR0 hc ha row col
    linarith
  exact polynomial_det_fderiv_norm_le (booleanSelectedMinor c sets block v r) a hL
    (productMinorPartialBound_nonneg _ _ hC hR0) hentry
    (booleanSelectedMinor_partial_bound c sets block v r hcard a hC hR hc ha)

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

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSliceC2Difference
namespace OAI

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem affineSlice_fderiv (F : X → Y) (c : X) (J : E →L[ℝ] X) (x : E)
    (hF : DifferentiableAt ℝ F (c + J x)) :
    fderiv ℝ (fun y => F (c + J y)) x = (fderiv ℝ F (c + J x)).comp J := by
  exact (hF.hasFDerivAt.comp x (J.hasFDerivAt.const_add c)).fderiv

end Erdos3

end

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothHalfspaceCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem halfspaceCutoff_range {E : Type*} (r : ℝ) (d : E → ℝ) (x : E) :
    halfspaceCutoff r d x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem halfspaceCutoff_eq_zero {E : Type*} {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : d x ≤ r) : halfspaceCutoff r d x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact sub_nonpos.mpr ((div_le_one hr).mpr hx)

theorem halfspaceCutoff_tsupport_subset {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) (hd : Continuous d) :
    tsupport (halfspaceCutoff r d) ⊆ {x | r ≤ d x} := by
  apply closure_minimal _ (isClosed_le continuous_const hd)
  intro x hx
  change r ≤ d x
  by_contra! h
  exact hx (halfspaceCutoff_eq_zero hr d h.le)

theorem contDiff_halfspaceCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (d : E → ℝ) (hd : ContDiff ℝ ∞ d) : ContDiff ℝ ∞ (halfspaceCutoff r d) :=
  Real.smoothTransition.contDiff.comp ((hd.div_const r).sub contDiff_const)

theorem halfspaceCutoff_fderiv_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) {x : E} (hd : DifferentiableAt ℝ d x) :
    ‖fderiv ℝ (halfspaceCutoff r d) x‖ ≤ (A : ℝ) / r * ‖fderiv ℝ d x‖ := by
  have ht : DifferentiableAt ℝ Real.smoothTransition (r⁻¹ • d x - 1) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable one_ne_zero).differentiableAt
  have heq : halfspaceCutoff r d = Real.smoothTransition ∘ (fun y => r⁻¹ • d y - 1) := by
    funext y
    simp only [halfspaceCutoff, Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  change ‖fderiv ℝ (Real.smoothTransition ∘ (fun y => (r⁻¹ • d) y - 1)) x‖ ≤ _
  rw [fderiv_comp x ht ((hd.const_smul r⁻¹).sub_const 1),
    fderiv_sub_const, fderiv_const_smul hd]
  calc
    _ ≤ ‖fderiv ℝ Real.smoothTransition (r⁻¹ • d x - 1)‖ * ‖r⁻¹ • fderiv ℝ d x‖ :=
      (fderiv ℝ Real.smoothTransition _).opNorm_comp_le _
    _ ≤ (A : ℝ) * ‖r⁻¹ • fderiv ℝ d x‖ :=
      mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

theorem inequalityBoundaryCutoff_range {I E : Type*} [Fintype I]
    (r : I → ℝ) (d : I → E → ℝ) (x : E) :
    inequalityBoundaryCutoff r d x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => halfspaceCutoff_range (r i) (d i) x)

theorem inequalityBoundaryCutoff_smooth {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (r : I → ℝ) (d : I → E → ℝ)
    (hd : ∀ i, ContDiff ℝ ∞ (d i)) : ContDiff ℝ ∞ (inequalityBoundaryCutoff r d) :=
  contDiff_prod (fun i _ => contDiff_halfspaceCutoff (r i) (d i) (hd i))

theorem inequalityBoundaryCutoff_tsupport_subset {I E : Type*} [Fintype I]
    [TopologicalSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) :
    tsupport (inequalityBoundaryCutoff r d) ⊆ {x | ∀ i, r i ≤ d i x} := by
  intro x hx i
  exact halfspaceCutoff_tsupport_subset (hr i) (d i) (hd i)
    (product_cutoff_tsupport_subset (fun j => halfspaceCutoff (r j) (d j)) i hx)

theorem inequalityBoundaryCutoff_tsupport_domain {I E : Type*} [Fintype I]
    [TopologicalSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) :
    tsupport (inequalityBoundaryCutoff r d) ⊆ positiveInequalityDomain d := by
  intro x hx i
  exact (hr i).trans_le (inequalityBoundaryCutoff_tsupport_subset r hr d hd hx i)

theorem inequalityBoundaryCutoff_compact {I E : Type*} [Fintype I]
    [MetricSpace E] [ProperSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i))
    (hbounded : Bornology.IsBounded (positiveInequalityDomain d)) :
    HasCompactSupport (inequalityBoundaryCutoff r d) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
  exact hbounded.subset (inequalityBoundaryCutoff_tsupport_domain r hr d hd)

theorem inequalityBoundaryCutoff_fderiv_norm_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (d : I → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (x : E) :
    ‖fderiv ℝ (inequalityBoundaryCutoff r d) x‖ ≤
      ∑ i, ((A : ℝ) / r i) * ‖fderiv ℝ (d i) x‖ := by
  apply (product_cutoff_fderiv_norm_le (fun i => halfspaceCutoff (r i) (d i)) x
    (fun i => ((contDiff_halfspaceCutoff (r i) (d i) (hd i)).differentiable (by norm_num)).differentiableAt)
    (fun i => halfspaceCutoff_range (r i) (d i) x)).trans
  exact Finset.sum_le_sum (fun i _ => halfspaceCutoff_fderiv_norm_le A hLip (hr i) (d i)
    (((hd i).differentiable (by norm_num)).differentiableAt))

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

open scoped BigOperators ContDiff

theorem scalarCubeFace_card (α : Type*) [Fintype α] :
    Fintype.card (Bool × Finset α) = 2 * 2 ^ Fintype.card α := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff

theorem sublevelCutoff_range {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) (d : E → ℝ) (x : E) :
    sublevelCutoff ψ r d x ∈ Set.Icc (0 : ℝ) 1 := hψ _

theorem sublevelCutoff_eq_zero {E : Type*} (ψ : ℝ → ℝ)
    (hψ : ∀ t, |t| ≤ 1 → ψ t = 0) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : |d x| ≤ r) : sublevelCutoff ψ r d x = 0 := by
  apply hψ
  rw [abs_div, abs_of_pos hr]
  exact (div_le_one hr).mpr hx

theorem sublevelCutoff_tsupport_subset {E : Type*} [TopologicalSpace E]
    (ψ : ℝ → ℝ) (hψ : ∀ t, |t| ≤ 1 → ψ t = 0) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) (hd : Continuous d) :
    tsupport (sublevelCutoff ψ r d) ⊆ {x | r ≤ |d x|} := by
  apply closure_minimal _ (isClosed_le continuous_const hd.abs)
  intro x hx
  change r ≤ |d x|
  by_contra! h
  exact hx (sublevelCutoff_eq_zero ψ hψ hr d h.le)

theorem contDiff_sublevelCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) (d : E → ℝ)
    (hd : ContDiff ℝ ∞ d) : ContDiff ℝ ∞ (sublevelCutoff ψ r d) :=
  hψ.comp (hd.div_const r)

theorem sublevelCutoff_fderiv_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (A : ℝ≥0) (hLip : LipschitzWith A ψ)
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) {x : E} (hd : DifferentiableAt ℝ d x) :
    ‖fderiv ℝ (sublevelCutoff ψ r d) x‖ ≤ (A : ℝ) / r * ‖fderiv ℝ d x‖ := by
  have hψd : DifferentiableAt ℝ ψ (r⁻¹ • d x) := hψ.differentiable (by norm_num) |>.differentiableAt
  have heq : sublevelCutoff ψ r d = ψ ∘ (fun y => r⁻¹ • d y) := by
    ext y
    simp only [sublevelCutoff, Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  change ‖fderiv ℝ (ψ ∘ (r⁻¹ • d)) x‖ ≤ _
  rw [fderiv_comp x hψd (hd.const_smul r⁻¹), fderiv_const_smul hd]
  calc
    _ ≤ ‖fderiv ℝ ψ (r⁻¹ • d x)‖ * ‖r⁻¹ • fderiv ℝ d x‖ :=
      (fderiv ℝ ψ (r⁻¹ • d x)).opNorm_comp_le _
    _ ≤ (A : ℝ) * ‖r⁻¹ • fderiv ℝ d x‖ :=
      mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedInequalityGoodCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem goodDomainCutoff_tsupport_subset {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (ψ : ℝ → ℝ) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (d : ι → E → ℝ) (hd : ∀ i, Continuous (d i))
    (b : E → ℝ) :
    tsupport (goodDomainCutoff ψ r d b) ⊆ tsupport b ∩ {x | ∀ i, r i ≤ |d i x|} := by
  intro x hx
  refine ⟨tsupport_mul_subset_left hx, ?_⟩
  intro i
  exact sublevelCutoff_tsupport_subset ψ hzero (hr i) (d i) (hd i)
    (product_cutoff_tsupport_subset (fun j => sublevelCutoff ψ (r j) (d j)) i
      (tsupport_mul_subset_right hx))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem sublevelCutoffProduct_range {J E : Type*} [Fintype J]
    (ψ : ℝ → ℝ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (κ : J → ℝ) (d : J → E → ℝ) (x : E) :
    sublevelCutoffProduct ψ κ d x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => sublevelCutoff_range ψ hrange (κ i) (d i) x)

theorem sublevelCutoffProduct_smooth {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (κ : J → ℝ)
    (d : J → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    ContDiff ℝ ∞ (sublevelCutoffProduct ψ κ d) :=
  contDiff_prod (fun i _ => contDiff_sublevelCutoff ψ hψ (κ i) (d i) (hd i))

theorem sublevelCutoffProduct_fderiv_norm_le {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (A : ℝ≥0) (hLip : LipschitzWith A ψ) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (x : E) :
    ‖fderiv ℝ (sublevelCutoffProduct ψ κ d) x‖ ≤
      ∑ i, ((A : ℝ) / κ i) * ‖fderiv ℝ (d i) x‖ := by
  have h := product_cutoff_fderiv_norm_le (fun i => sublevelCutoff ψ (κ i) (d i)) x
    (fun i => ((contDiff_sublevelCutoff ψ hψ (κ i) (d i) (hd i)).differentiable
      (by norm_num)).differentiableAt)
    (fun i => sublevelCutoff_range ψ hrange (κ i) (d i) x)
  exact h.trans (Finset.sum_le_sum (fun i _ => sublevelCutoff_fderiv_norm_le ψ hψ A hLip
    (hκ i) (d i) ((hd i).differentiable (by norm_num)).differentiableAt))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Topology

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

theorem sigmaAxisCoordinates_symm_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I).symm volume volume := by
  refine ⟨(sigmaAxisCoordinates I).symm.continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (sigmaAxisCoordinates I).symm.continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : (sigmaAxisCoordinates I).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i : I d => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_sigma]

theorem sigmaAxisCoordinates_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I) volume volume :=
  (sigmaAxisCoordinates_symm_measurePreserving I).symm
    (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensorCutoffWeight_tsupport {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) :
    tsupport (tensorCutoffWeight w) ⊆ {x | ∀ i, x i ∈ tsupport (w i)} := by
  have hc : IsClosed {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} := by
    have he : {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} =
        ⋂ i, (fun x : ∀ i, E i => x i) ⁻¹' tsupport (w i) := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i => (isClosed_tsupport _).preimage (continuous_apply i))
  apply closure_minimal _ hc
  intro x hx i
  apply subset_closure
  change w i (x i) ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem tensorCutoffWeight_compact {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, HasCompactSupport (w i)) :
    HasCompactSupport (tensorCutoffWeight w) :=
  (isCompact_pi_infinite hw).of_isClosed_subset (isClosed_tsupport _)
    (tensorCutoffWeight_tsupport w)

theorem tensorCutoffWeight_contDiff {ι : Type*} {E : ι → Type*} [Fintype ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, ContDiff ℝ 1 (w i)) :
    ContDiff ℝ 1 (tensorCutoffWeight w) :=
  contDiff_prod (fun i _ => (hw i).comp
    (ContinuousLinearMap.proj i : (∀ j, E j) →L[ℝ] E i).contDiff)

theorem tensorCutoffWeight_abs_mass {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ) :
    (∫ x, |tensorCutoffWeight w x|) = ∏ i, ∫ y, |w i y| := by
  simp only [tensorCutoffWeight, Finset.abs_prod]
  exact integral_fintype_prod_volume_eq_prod (fun i y => |w i y|)

theorem tensorCutoffWeight_abs_mass_le_one {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))] (w : ∀ i, E i → ℝ)
    (hw : ∀ i, (∫ y, |w i y|) ≤ 1) : (∫ x, |tensorCutoffWeight w x|) ≤ 1 := by
  rw [tensorCutoffWeight_abs_mass]
  exact Finset.prod_le_one (fun i _ => integral_nonneg (fun y => abs_nonneg _)) (fun i _ => hw i)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensorCutoffWeight_update {ι : Type*} {E : ι → Type*} [Fintype ι] [DecidableEq ι]
    (w : ∀ i, E i → ℝ) (i : ι) (g : E i → ℝ) (x : ∀ i, E i) :
    tensorCutoffWeight (Function.update w i g) x =
      g (x i) * ∏ j ∈ Finset.univ.erase i, w j (x j) := by
  unfold tensorCutoffWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem tensorCutoffWeight_fderiv_single {ι : Type*} {E : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ j, ContDiff ℝ 1 (w j)) (x : ∀ i, E i) (i : ι) (v : E i) :
    fderiv ℝ (tensorCutoffWeight w) x (Pi.single i v) =
      (∏ j ∈ Finset.univ.erase i, w j (x j)) * fderiv ℝ (w i) (x i) v := by
  have hd (j : ι) : HasFDerivAt (fun y : ∀ i, E i => w j (y j))
      ((fderiv ℝ (w j) (x j)).comp (ContinuousLinearMap.proj j)) x :=
    ((hw j).differentiable one_ne_zero (x j)).hasFDerivAt.comp x (hasFDerivAt_apply j x)
  have h := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hd j)
  change fderiv ℝ (fun y : ∀ i, E i => ∏ j, w j (y j)) x (Pi.single i v) = _
  rw [h.fderiv, sum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Pi.single_eq_same, smul_eq_mul]
  · intro j _ hji
    simp [smul_apply, ContinuousLinearMap.comp_apply, hji]
  · simp

theorem tensorCutoffWeight_derivative_integral {ι : Type*} {E : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))]
    (w : ∀ i, E i → ℝ) (hw : ∀ j, ContDiff ℝ 1 (w j)) (i : ι) (v : E i) :
    (∫ x, |fderiv ℝ (tensorCutoffWeight w) x (Pi.single i v)|) =
      (∫ y, |fderiv ℝ (w i) y v|) * ∏ j ∈ Finset.univ.erase i, ∫ y, |w j y| := by
  let a : ∀ i, E i → ℝ := fun j y => |w j y|
  let g : E i → ℝ := fun y => |fderiv ℝ (w i) y v|
  have he (x : ∀ i, E i) :
      |fderiv ℝ (tensorCutoffWeight w) x (Pi.single i v)| =
        tensorCutoffWeight (Function.update a i g) x := by
    rw [tensorCutoffWeight_fderiv_single w hw, tensorCutoffWeight_update,
      abs_mul, Finset.abs_prod]
    exact mul_comm _ _
  simp_rw [he]
  rw [tensorCutoffWeight_integral, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem tensorCutoffWeight_derivative_le {ι : Type*} {E : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasureSpace (E i)]
    [∀ i, SigmaFinite (volume : Measure (E i))]
    (w : ∀ i, E i → ℝ) (hw : ∀ j, ContDiff ℝ 1 (w j))
    (hm : ∀ j, (∫ y, |w j y|) ≤ 1) (i : ι) (v : E i) :
    (∫ x, |fderiv ℝ (tensorCutoffWeight w) x (Pi.single i v)|) ≤
      ∫ y, |fderiv ℝ (w i) y v| := by
  rw [tensorCutoffWeight_derivative_integral w hw]
  exact mul_le_of_le_one_right (integral_nonneg (fun _ => abs_nonneg _))
    (Finset.prod_le_one (fun j _ => integral_nonneg (fun y => abs_nonneg _)) (fun j _ => hm j))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomainDensity_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeDomainDensity α := inv_pos.mpr (scalarCubeDomain_volumeReal_pos α)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeBoundaryCost
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem scalarCubeLinearMap_apply {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (a : Option α → ℝ) : scalarCubeLinearMap t a = scalarCubeValue a t := by
  simp only [scalarCubeLinearMap, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, scalarCubeValue]

theorem scalarCubeLinearMap_single {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (r : Option α) :
    scalarCubeLinearMap t (Pi.single r 1) = (booleanFeature r t : ℝ) := by
  rw [scalarCubeLinearMap_apply]
  simp [scalarCubeValue, Pi.single_apply, mul_ite]

theorem scalarCubeLinearMap_norm_le {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    ‖scalarCubeLinearMap t‖ ≤ (Fintype.card α : ℝ) + 1 := by
  have h := clm_norm_le_card_mul_of_basis (scalarCubeLinearMap t) zero_le_one (fun r => by
    rw [scalarCubeLinearMap_single, Real.norm_eq_abs]
    exact booleanFeature_abs_le_one r t)
  simpa only [Fintype.card_option, Nat.cast_add, Nat.cast_one, mul_one] using h

theorem scalarCubeValue_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (a : Option α → ℝ) :
    ‖fderiv ℝ (fun x => scalarCubeValue x t) a‖ ≤ (Fintype.card α : ℝ) + 1 := by
  have heq : (fun x => scalarCubeValue x t) = scalarCubeLinearMap t :=
    funext (fun x => (scalarCubeLinearMap_apply t x).symm)
  rw [heq, ContinuousLinearMap.fderiv]
  exact scalarCubeLinearMap_norm_le t

theorem scalarCubeFace_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (a : Option α → ℝ) :
    ‖fderiv ℝ (scalarCubeFace i) a‖ ≤ (Fintype.card α : ℝ) + 1 := by
  rcases i with ⟨b, t⟩
  cases b with
  | false => exact scalarCubeValue_fderiv_norm_le t a
  | true =>
    change ‖fderiv ℝ (fun x => 1 - scalarCubeValue x t) a‖ ≤ _
    rw [fderiv_const_sub, norm_neg]
    exact scalarCubeValue_fderiv_norm_le t a

theorem scalarCubeBoundaryCutoff_compact (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) := by
  apply inequalityBoundaryCutoff_compact _ (fun _ => hr) _ (fun i => (scalarCubeFace_contDiff i).continuous)
  rw [positiveInequalityDomain_scalarCubeFace]
  exact scalarCubeDomain_isBounded α

theorem scalarCubeBoundaryCutoff_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r)
    (a : Option α → ℝ) :
    ‖fderiv ℝ (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) a‖ ≤
      ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((A : ℝ) / r * ((Fintype.card α : ℝ) + 1)) := by
  apply (inequalityBoundaryCutoff_fderiv_norm_le A hLip _ (fun _ => hr)
    scalarCubeFace scalarCubeFace_contDiff a).trans
  calc
    _ ≤ ∑ _i : Bool × Finset α, (A : ℝ) / r * ((Fintype.card α : ℝ) + 1) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (scalarCubeFace_fderiv_norm_le i a)
        (div_nonneg A.coe_nonneg hr.le))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, scalarCubeFace_card, nsmul_eq_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeMeasure_integral {α : Type*} [Fintype α] [DecidableEq α]
    (f : (Option α → ℝ) → ℝ) :
    (∫ a, f a ∂scalarCubeMeasure α) = scalarCubeDomainDensity α * ∫ a in scalarCubeDomain α, f a := by
  rw [scalarCubeMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rfl

theorem scalarCubeMeasure_ae_domain (α : Type*) [Fintype α] [DecidableEq α] :
    ∀ᵐ a ∂scalarCubeMeasure α, a ∈ scalarCubeDomain α := by
  apply ae_iff.mpr
  change scalarCubeMeasure α (scalarCubeDomain α)ᶜ = 0
  simp [scalarCubeMeasure, Measure.smul_apply,
    Measure.restrict_apply (scalarCubeDomain_isOpen α).measurableSet.compl]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

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

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

theorem scalarCubeCutoffWeight_contDiff {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (scalarCubeCutoffWeight b) := contDiff_const.mul hb

theorem scalarCubeCutoffWeight_compact {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : HasCompactSupport b) :
    HasCompactSupport (scalarCubeCutoffWeight b) := hb.mul_left

theorem scalarCubeCutoffWeight_tsupport_subset {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) : tsupport (scalarCubeCutoffWeight b) ⊆ tsupport b :=
  tsupport_mul_subset_right

theorem scalarCubeCutoffWeight_integral {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : tsupport b ⊆ scalarCubeDomain α) :
    (∫ a, scalarCubeCutoffWeight b a) = ∫ a, b a ∂scalarCubeMeasure α := by
  rw [scalarCubeMeasure_integral]
  change (∫ a, scalarCubeDomainDensity α * b a) = _
  rw [integral_const_mul]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro a ha
  exact image_eq_zero_of_notMem_tsupport (fun h => ha (hb h))

theorem scalarCubeCutoffWeight_abs_mass_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : Measurable b) (hs : tsupport b ⊆ scalarCubeDomain α)
    (hrange : ∀ a, b a ∈ Set.Icc (0 : ℝ) 1) :
    (∫ a, |scalarCubeCutoffWeight b a|) ≤ 1 := by
  have heq : (fun a => |scalarCubeCutoffWeight b a|) = scalarCubeCutoffWeight b := by
    funext a
    exact abs_of_nonneg (mul_nonneg (scalarCubeDomainDensity_pos α).le (hrange a).1)
  rw [heq, scalarCubeCutoffWeight_integral b hs]
  have h := integral_mono (cutoff_integrable (scalarCubeMeasure α) b hb hrange)
    (integrable_const (1 : ℝ)) (fun a => (hrange a).2)
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem scalarCubeCutoffWeight_derivative_integral {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) (hs : tsupport b ⊆ scalarCubeDomain α)
    (v : Option α → ℝ) :
    (∫ a, |fderiv ℝ (scalarCubeCutoffWeight b) a v|) =
      ∫ a, |fderiv ℝ b a v| ∂scalarCubeMeasure α := by
  have heq (a : Option α → ℝ) :
      |fderiv ℝ (scalarCubeCutoffWeight b) a v| =
        scalarCubeDomainDensity α * |fderiv ℝ b a v| := by
    change |fderiv ℝ (fun x => scalarCubeDomainDensity α * b x) a v| = _
    rw [fderiv_const_mul (hb.differentiable one_ne_zero a), smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (scalarCubeDomainDensity_pos α)]
  simp_rw [heq]
  rw [integral_const_mul, scalarCubeMeasure_integral]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro a ha
  rw [fderiv_of_notMem_tsupport ℝ (fun h => ha (hs h)), zero_apply, abs_zero]

theorem scalarCubeMean_derivative_le {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) {L : ℝ} (hL : 0 ≤ L)
    (hder : ∀ a ∈ scalarCubeDomain α, ‖fderiv ℝ b a‖ ≤ L) (v : Option α → ℝ) :
    (∫ a, |fderiv ℝ b a v| ∂scalarCubeMeasure α) ≤ L * ‖v‖ := by
  have hbound : ∀ᵐ a ∂scalarCubeMeasure α, |fderiv ℝ b a v| ≤ L * ‖v‖ := by
    filter_upwards [scalarCubeMeasure_ae_domain α] with a ha
    have h := ((fderiv ℝ b a).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hder a ha) (norm_nonneg v))
    simpa only [Real.norm_eq_abs] using h
  have hm : Measurable (fun a => |fderiv ℝ b a v|) :=
    ((hb.continuous_fderiv one_ne_zero).clm_apply continuous_const).abs.measurable
  have hi : Integrable (fun a => |fderiv ℝ b a v|) (scalarCubeMeasure α) :=
    (integrable_const (L * ‖v‖)).mono hm.aestronglyMeasurable (by
      filter_upwards [hbound] with a ha
      simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg (mul_nonneg hL (norm_nonneg v))] using ha)
  have h := integral_mono_ae hi (integrable_const (L * ‖v‖)) hbound
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem scalarCubeCutoffWeight_derivative_le {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) (hs : tsupport b ⊆ scalarCubeDomain α)
    {L : ℝ} (hL : 0 ≤ L) (hder : ∀ a ∈ scalarCubeDomain α, ‖fderiv ℝ b a‖ ≤ L)
    (v : Option α → ℝ) : (∫ a, |fderiv ℝ (scalarCubeCutoffWeight b) a v|) ≤ L * ‖v‖ := by
  rw [scalarCubeCutoffWeight_derivative_integral b hb hs]
  exact scalarCubeMean_derivative_le b hb hL hder v

theorem scalarCubeCutoffWeight_coordinate_sum_le {α : Type*} [Fintype α] [DecidableEq α]
    (b : (Option α → ℝ) → ℝ) (hb : ContDiff ℝ 1 b) (hs : tsupport b ⊆ scalarCubeDomain α)
    {L : ℝ} (hL : 0 ≤ L) (hder : ∀ a ∈ scalarCubeDomain α, ‖fderiv ℝ b a‖ ≤ L) :
    (∑ j : Option α, ∫ a, |fderiv ℝ (scalarCubeCutoffWeight b) a (Pi.single j 1)|) ≤
      ((Fintype.card α : ℝ) + 1) * L := by
  calc
    _ ≤ ∑ _j : Option α, L := Finset.sum_le_sum (fun j _ => by
      have h := scalarCubeCutoffWeight_derivative_le b hb hs hL hder (Pi.single j 1)
      simpa only [Pi.norm_single, norm_one, mul_one] using h)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeBoundaryCutoff_tsupport_domain (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    tsupport (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) ⊆
      scalarCubeDomain α := by
  rw [← positiveInequalityDomain_scalarCubeFace α]
  exact inequalityBoundaryCutoff_tsupport_domain _ (fun _ => hr) _
    (fun i => (scalarCubeFace_contDiff i).continuous)

theorem scalarCubeBoundaryWeight_spec (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ 1 (scalarCubeBoundaryWeight α r) ∧ HasCompactSupport (scalarCubeBoundaryWeight α r) ∧
      tsupport (scalarCubeBoundaryWeight α r) ⊆ scalarCubeDomain α ∧
      (∀ a, 0 ≤ scalarCubeBoundaryWeight α r a) ∧ (∫ a, |scalarCubeBoundaryWeight α r a|) ≤ 1 := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace
  have hb : ContDiff ℝ 1 b :=
    (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).of_le (by norm_num)
  have hs : tsupport b ⊆ scalarCubeDomain α := scalarCubeBoundaryCutoff_tsupport_domain α hr
  refine ⟨scalarCubeCutoffWeight_contDiff b hb,
    scalarCubeCutoffWeight_compact b (scalarCubeBoundaryCutoff_compact α hr),
    (scalarCubeCutoffWeight_tsupport_subset b).trans hs, ?_, ?_⟩
  · intro a
    exact mul_nonneg (scalarCubeDomainDensity_pos α).le (inequalityBoundaryCutoff_range _ _ a).1
  · exact scalarCubeCutoffWeight_abs_mass_le_one b hb.continuous.measurable hs
      (inequalityBoundaryCutoff_range _ _)

theorem scalarCubeBoundaryWeight_derivative_budget {α : Type*} [Fintype α] [DecidableEq α]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) :
    (∑ j : Option α, ∫ a, |fderiv ℝ (scalarCubeBoundaryWeight α r) a (Pi.single j 1)|) ≤
      ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A / r := by
  let b := inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace
  have hb : ContDiff ℝ 1 b :=
    (inequalityBoundaryCutoff_smooth _ _ scalarCubeFace_contDiff).of_le (by norm_num)
  have hs : tsupport b ⊆ scalarCubeDomain α := scalarCubeBoundaryCutoff_tsupport_domain α hr
  have h := scalarCubeCutoffWeight_coordinate_sum_le b hb hs (by positivity)
    (fun a _ => scalarCubeBoundaryCutoff_fderiv_norm_le A hLip hr a)
  exact h.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem scalarCubeProductWeight_spec {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ContDiff ℝ 1 (scalarCubeProductWeight α r) ∧
      HasCompactSupport (scalarCubeProductWeight α r) ∧
      tsupport (scalarCubeProductWeight α r) ⊆ scalarCubeProductDomain ι α ∧
      (∀ x, 0 ≤ scalarCubeProductWeight α r x) ∧
      (∫ x, |scalarCubeProductWeight α r x|) ≤ 1 := by
  have h := fun i => scalarCubeBoundaryWeight_spec α (hr i)
  refine ⟨tensorCutoffWeight_contDiff _ (fun i => (h i).1),
    tensorCutoffWeight_compact _ (fun i => (h i).2.1), ?_,
    tensorCutoffWeight_nonneg _ (fun i => (h i).2.2.2.1),
    tensorCutoffWeight_abs_mass_le_one _ (fun i => (h i).2.2.2.2)⟩
  intro x hx i _
  exact (h i).2.2.1 (tensorCutoffWeight_tsupport _ hx i)

theorem scalarCubeProductWeight_derivative_budget {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition) :
    (∑ i, ∑ j : Option α, ∫ x,
      |fderiv ℝ (scalarCubeProductWeight α r) x (Pi.single i (Pi.single j 1))|) ≤
      ∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * A / r i := by
  have h := fun i => scalarCubeBoundaryWeight_spec α (hr i)
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ∑ j : Option α, ∫ y, |fderiv ℝ (scalarCubeBoundaryWeight α (r i)) y (Pi.single j 1)| :=
      Finset.sum_le_sum (fun j _ => tensorCutoffWeight_derivative_le _
        (fun i => (h i).1) (fun i => (h i).2.2.2.2) i (Pi.single j 1))
    _ ≤ _ := scalarCubeBoundaryWeight_derivative_budget A hLip (hr i)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BlockCubeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem blockCubeFlatten_symm_apply {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (a : BlockParameter B F α → ℝ) (bf : B × F) (r : Option α) :
    (blockCubeFlatten B F α).symm a bf r = a (bf.1, bf.2, r) := rfl

theorem blockCubeFlatten_norm_le_one (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    ‖(blockCubeFlatten B F α).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro z
  exact (norm_le_pi_norm (x (z.1, z.2.1)) z.2.2).trans (norm_le_pi_norm x (z.1, z.2.1))

theorem blockCubeFlatten_measurePreserving (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] :
    MeasurePreserving (blockCubeFlatten B F α) volume volume := by
  refine ⟨(blockCubeFlatten B F α).continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (blockCubeFlatten B F α).continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : blockCubeFlatten B F α ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun bf : B × F => Set.univ.pi (fun r => s (bf.1, bf.2, r))) := by
    ext x
    constructor
    · intro hx bf _ r _
      exact hx (bf.1, bf.2, r) (Set.mem_univ _)
    · intro hx z _
      exact hx (z.1, z.2.1) (Set.mem_univ _) z.2.2 (Set.mem_univ _)
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_prod_type]

theorem blockCubeFlatten_symm_measurePreserving (B F α : Type*) [Fintype B] [Fintype F]
    [Fintype α] : MeasurePreserving (blockCubeFlatten B F α).symm volume volume :=
  (blockCubeFlatten_measurePreserving B F α).symm
    (blockCubeFlatten B F α).toHomeomorph.toMeasurableEquiv

theorem blockCubeFlatten_symm_single {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (b : B) (f : F) (r : Option α) :
    (blockCubeFlatten B F α).symm (Pi.single (b, f, r) (1 : ℝ)) =
      Pi.single (b, f) (Pi.single r 1) := by
  ext bf r'
  rcases bf with ⟨b', f'⟩
  by_cases hb : b' = b <;> by_cases hf : f' = f <;> by_cases hr : r' = r <;>
    simp [blockCubeFlatten_symm_apply, hb, hf, hr]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weightedCutoff_derivative_pointwise (w θ : E → ℝ)
    (hw : ContDiff ℝ 1 w) (hθ : ContDiff ℝ 1 θ)
    (hrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) {L : ℝ} (hL : 0 ≤ L)
    (hder : ∀ x ∈ tsupport w, ‖fderiv ℝ θ x‖ ≤ L) (x v : E) :
    |fderiv ℝ (fun y => w y * θ y) x v| ≤
      |fderiv ℝ w x v| + (L * ‖v‖) * |w x| := by
  by_cases hx : x ∈ tsupport w
  · have hd : |fderiv ℝ θ x v| ≤ L * ‖v‖ := by
      have h := ((fderiv ℝ θ x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hder x hx) (norm_nonneg v))
      simpa only [Real.norm_eq_abs] using h
    rw [fderiv_fun_mul (hw.differentiable one_ne_zero x) (hθ.differentiable one_ne_zero x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have ha := abs_add_le (w x * fderiv ℝ θ x v) (θ x * fderiv ℝ w x v)
    simp only [abs_mul, abs_of_nonneg (hrange x).1] at ha
    have hb := mul_le_mul_of_nonneg_left hd (abs_nonneg (w x))
    have hc := mul_le_of_le_one_left (abs_nonneg (fderiv ℝ w x v)) (hrange x).2
    nlinarith
  · have hs : x ∉ tsupport (fun y => w y * θ y) :=
      fun h => hx (tsupport_mul_subset_left h)
    rw [fderiv_of_notMem_tsupport ℝ hs, zero_apply, abs_zero]
    positivity

theorem compact_weight_directional_integrable [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (w : E → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (v : E) :
    Integrable (fun x => |fderiv ℝ w x v|) μ := by
  have hi : Integrable (fun x => fderiv ℝ w x v) μ :=
    ((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  simpa only [Real.norm_eq_abs] using hi.norm

theorem weightedCutoff_derivative_integral_le [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (w θ : E → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hθ : ContDiff ℝ 1 θ) (hrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1)
    {L : ℝ} (hL : 0 ≤ L) (hder : ∀ x ∈ tsupport w, ‖fderiv ℝ θ x‖ ≤ L) (v : E) :
    (∫ x, |fderiv ℝ (fun y => w y * θ y) x v| ∂μ) ≤
      (∫ x, |fderiv ℝ w x v| ∂μ) + (L * ‖v‖) * ∫ x, |w x| ∂μ := by
  have hdi := compact_weight_directional_integrable μ w hw hs v
  have hwi : Integrable (fun x => |w x|) μ := by
    simpa only [Real.norm_eq_abs] using (hw.continuous.integrable_of_hasCompactSupport hs (μ := μ)).norm
  have hleft := compact_weight_directional_integrable μ (fun y => w y * θ y)
    (hw.mul hθ) hs.mul_right v
  have h := integral_mono hleft (hdi.add (hwi.const_mul (L * ‖v‖)))
    (fun x => weightedCutoff_derivative_pointwise w θ hw hθ hrange hL hder x v)
  simp only [Pi.add_apply] at h
  rw [integral_add hdi (hwi.const_mul (L * ‖v‖)), integral_const_mul] at h
  exact h

theorem weightedCutoff_abs_mass_le [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (w θ : E → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hθ : ContDiff ℝ 1 θ) (hrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, |w x * θ x| ∂μ) ≤ ∫ x, |w x| ∂μ := by
  have hwθ : Integrable (fun x => w x * θ x) μ :=
    (hw.mul hθ).continuous.integrable_of_hasCompactSupport hs.mul_right
  have hwi : Integrable w μ := hw.continuous.integrable_of_hasCompactSupport hs
  have hleft : Integrable (fun x => |w x * θ x|) μ := by
    simpa only [Real.norm_eq_abs] using hwθ.norm
  have hright : Integrable (fun x => |w x|) μ := by
    simpa only [Real.norm_eq_abs] using hwi.norm
  apply integral_mono hleft hright
  intro x
  change |w x * θ x| ≤ |w x|
  rw [abs_mul, abs_of_nonneg (hrange x).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (hrange x).2

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem blockCubeWeight_contDiff {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) :
    ContDiff ℝ 1 (blockCubeWeight w) := hw.comp (blockCubeFlatten B F α).symm.contDiff

theorem blockCubeWeight_compact {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : HasCompactSupport w) :
    HasCompactSupport (blockCubeWeight w) :=
  hw.comp_homeomorph (blockCubeFlatten B F α).symm.toHomeomorph

theorem blockCubeWeight_tsupport {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    tsupport (blockCubeWeight w) = (blockCubeFlatten B F α).symm ⁻¹' tsupport w :=
  tsupport_comp_eq_preimage w (blockCubeFlatten B F α).symm.toHomeomorph

theorem blockCubeWeight_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    (∫ a, blockCubeWeight w a) = ∫ x, w x :=
  (blockCubeFlatten_symm_measurePreserving B F α).integral_comp
    (blockCubeFlatten B F α).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding w

theorem blockCubeWeight_abs_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    (∫ a, |blockCubeWeight w a|) = ∫ x, |w x| :=
  blockCubeWeight_integral (fun x => |w x|)

theorem blockCubeWeight_coordinate_fderiv {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (a : BlockParameter B F α → ℝ) (b : B) (f : F) (r : Option α) :
    fderiv ℝ (blockCubeWeight w) a (Pi.single (b, f, r) 1) =
      fderiv ℝ w ((blockCubeFlatten B F α).symm a) (Pi.single (b, f) (Pi.single r 1)) := by
  have hd := (hw.differentiable one_ne_zero ((blockCubeFlatten B F α).symm a)).hasFDerivAt.comp a
    (blockCubeFlatten B F α).symm.toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ (w ∘ (blockCubeFlatten B F α).symm) a (Pi.single (b, f, r) 1) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ w ((blockCubeFlatten B F α).symm a)) (blockCubeFlatten_symm_single b f r)

theorem blockCubeWeight_coordinate_integral {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (b : B) (f : F) (r : Option α) :
    (∫ a, |fderiv ℝ (blockCubeWeight w) a (Pi.single (b, f, r) 1)|) =
      ∫ x, |fderiv ℝ w x (Pi.single (b, f) (Pi.single r 1))| := by
  simp_rw [blockCubeWeight_coordinate_fderiv w hw]
  exact blockCubeWeight_integral (fun x => |fderiv ℝ w x (Pi.single (b, f) (Pi.single r 1))|)

theorem blockCubeWeight_derivative_sum {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) :
    (∑ z : BlockParameter B F α, ∫ a, |fderiv ℝ (blockCubeWeight w) a (Pi.single z 1)|) =
      ∑ bf : B × F, ∑ r : Option α, ∫ x, |fderiv ℝ w x (Pi.single bf (Pi.single r 1))| := by
  simp only [Fintype.sum_prod_type, blockCubeWeight_coordinate_integral w hw]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem blockCubeFlatten_box {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] {x : (B × F) → Option α → ℝ} (hx : x ∈ scalarCubeProductDomain (B × F) α)
    (z : BlockParameter B F α) : |blockCubeFlatten B F α x z| ≤ 1 :=
  (scalarCubeDomain_coordinate_abs_lt_one (hx (z.1, z.2.1) (Set.mem_univ _)) z.2.2).le

theorem blockCubeWeight_box {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] (w : ((B × F) → Option α → ℝ) → ℝ)
    (hs : tsupport w ⊆ scalarCubeProductDomain (B × F) α)
    {a : BlockParameter B F α → ℝ} (ha : a ∈ tsupport (blockCubeWeight w))
    (z : BlockParameter B F α) : |a z| ≤ 1 := by
  rw [blockCubeWeight_tsupport] at ha
  have hx := blockCubeFlatten_box (hs ha) z
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

theorem scalarCubeGoodWeight_spec {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    ContDiff ℝ 1 (scalarCubeGoodWeight α ψ r κ d) ∧
      HasCompactSupport (scalarCubeGoodWeight α ψ r κ d) ∧
      tsupport (scalarCubeGoodWeight α ψ r κ d) ⊆
        scalarCubeProductDomain I α ∩ {x | ∀ i, κ i ≤ |d i x|} ∧
      (∀ x, 0 ≤ scalarCubeGoodWeight α ψ r κ d x) ∧
      (∫ x, |scalarCubeGoodWeight α ψ r κ d x|) ≤ 1 := by
  have hb := scalarCubeProductWeight_spec (α := α) r hr
  have hθ : ContDiff ℝ 1 (sublevelCutoffProduct ψ κ d) :=
    (sublevelCutoffProduct_smooth ψ hψ κ d hd).of_le (by norm_num)
  refine ⟨hb.1.mul hθ, hb.2.1.mul_right, ?_, ?_, ?_⟩
  · intro x hx
    have h := goodDomainCutoff_tsupport_subset ψ hzero κ hκ d
      (fun i => (hd i).continuous) (scalarCubeProductWeight α r) hx
    exact ⟨hb.2.2.1 h.1, h.2⟩
  · intro x
    exact mul_nonneg (hb.2.2.2.1 x) (sublevelCutoffProduct_range ψ hrange κ d x).1
  · exact (weightedCutoff_abs_mass_le volume _ _ hb.1 hb.2.1 hθ
      (sublevelCutoffProduct_range ψ hrange κ d)).trans hb.2.2.2.2

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem scalarCubeGoodWeight_directional_le {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (A : ℝ≥0) (hLip : LipschitzWith A ψ)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (L : J → ℝ≥0)
    (hder : ∀ i x, x ∈ scalarCubeProductDomain I α → ‖fderiv ℝ (d i) x‖ ≤ L i)
    (v : I → Option α → ℝ) :
    (∫ x, |fderiv ℝ (scalarCubeGoodWeight α ψ r κ d) x v|) ≤
      (∫ x, |fderiv ℝ (scalarCubeProductWeight α r) x v|) +
        (∑ i, (A : ℝ) / κ i * L i) * ‖v‖ := by
  have hb := scalarCubeProductWeight_spec (α := α) r hr
  have hθ : ContDiff ℝ 1 (sublevelCutoffProduct ψ κ d) :=
    (sublevelCutoffProduct_smooth ψ hψ κ d hd).of_le (by norm_num)
  have hS : 0 ≤ ∑ i, (A : ℝ) / κ i * L i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (div_nonneg A.coe_nonneg (hκ i).le) (L i).coe_nonneg)
  have hθbound (x) (hx : x ∈ tsupport (scalarCubeProductWeight α r)) :
      ‖fderiv ℝ (sublevelCutoffProduct ψ κ d) x‖ ≤ ∑ i, (A : ℝ) / κ i * L i :=
    (sublevelCutoffProduct_fderiv_norm_le ψ hψ hrange A hLip κ hκ d hd x).trans
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hder i x (hb.2.2.1 hx)) (div_nonneg A.coe_nonneg (hκ i).le)))
  have h := weightedCutoff_derivative_integral_le volume _ _ hb.1 hb.2.1 hθ
    (sublevelCutoffProduct_range ψ hrange κ d) hS hθbound v
  exact h.trans (add_le_add le_rfl
    (mul_le_of_le_one_right (mul_nonneg hS (norm_nonneg v)) hb.2.2.2.2))

theorem scalarCubeGoodWeight_derivative_budget {I J α : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (A T : ℝ≥0)
    (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (L : J → ℝ≥0)
    (hder : ∀ i x, x ∈ scalarCubeProductDomain I α → ‖fderiv ℝ (d i) x‖ ≤ L i) :
    (∑ i, ∑ j : Option α, ∫ x,
      |fderiv ℝ (scalarCubeGoodWeight α ψ r κ d) x (Pi.single i (Pi.single j 1))|) ≤
      (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
        (Fintype.card I : ℝ) * ((Fintype.card α : ℝ) + 1) *
          (∑ i, (A : ℝ) / κ i * L i) := by
  let S := ∑ i, (A : ℝ) / κ i * L i
  have hcoord (i : I) (j : Option α) :
      (∫ x, |fderiv ℝ (scalarCubeGoodWeight α ψ r κ d) x (Pi.single i (Pi.single j 1))|) ≤
        (∫ x, |fderiv ℝ (scalarCubeProductWeight α r) x (Pi.single i (Pi.single j 1))|) + S := by
    have h := scalarCubeGoodWeight_directional_le ψ hψ hrange A hLip r hr κ hκ d hd L hder
      (Pi.single i (Pi.single j 1))
    simpa only [Pi.norm_single, norm_one, mul_one] using h
  calc
    _ ≤ ∑ i, ∑ j : Option α,
        ((∫ x, |fderiv ℝ (scalarCubeProductWeight α r) x (Pi.single i (Pi.single j 1))|) + S) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcoord i j))
    _ = (∑ i, ∑ j : Option α,
        ∫ x, |fderiv ℝ (scalarCubeProductWeight α r) x (Pi.single i (Pi.single j 1))|) +
        (Fintype.card I : ℝ) * ((Fintype.card α : ℝ) + 1) * S := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Fintype.card_option, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ _ := add_le_add (scalarCubeProductWeight_derivative_budget (α := α) r hr T hTransition) le_rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaWeightDerivative
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] [DecidableEq D] {I : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)]

omit [Fintype D] [∀ d, Fintype (I d)] in
theorem sigmaAxisCoordinates_single (d : D) (i : I d) :
    sigmaAxisCoordinates I (Pi.single ⟨d, i⟩ (1 : ℝ)) = Pi.single d (Pi.single i 1) := by
  ext e j
  by_cases he : e = d
  · subst e
    simp [sigmaAxisCoordinates, Pi.single_apply]
  · have hs : (⟨e, j⟩ : Σ d, I d) ≠ ⟨d, i⟩ := fun h => he (congrArg Sigma.fst h)
    simp [sigmaAxisCoordinates, Pi.single_eq_of_ne he, Pi.single_eq_of_ne hs]

theorem sigmaAxisWeight_coordinate_fderiv (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) (x : (Σ d, I d) → ℝ) (d : D) (i : I d) :
    fderiv ℝ (sigmaAxisWeight w) x (Pi.single ⟨d, i⟩ 1) =
      fderiv ℝ (tensorCutoffWeight w) (sigmaAxisCoordinates I x) (Pi.single d (Pi.single i 1)) := by
  have hd := ((tensorCutoffWeight_contDiff w hw).differentiable one_ne_zero
    (sigmaAxisCoordinates I x)).hasFDerivAt.comp x (sigmaAxisCoordinates I).toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ (tensorCutoffWeight w ∘ sigmaAxisCoordinates I) x (Pi.single ⟨d, i⟩ 1) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ (tensorCutoffWeight w) (sigmaAxisCoordinates I x))
    (sigmaAxisCoordinates_single d i)

theorem sigmaAxisWeight_coordinate_integral (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) (d : D) (i : I d) :
    (∫ x, |fderiv ℝ (sigmaAxisWeight w) x (Pi.single ⟨d, i⟩ 1)|) =
      (∫ y, |fderiv ℝ (w d) y (Pi.single i 1)|) * ∏ e ∈ Finset.univ.erase d, ∫ y, |w e y| := by
  simp_rw [sigmaAxisWeight_coordinate_fderiv w hw]
  rw [(sigmaAxisCoordinates_measurePreserving I).integral_comp
    (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y => |fderiv ℝ (tensorCutoffWeight w) y (Pi.single d (Pi.single i 1))|)]
  exact tensorCutoffWeight_derivative_integral w hw d (Pi.single i 1)

theorem sigmaAxisWeight_coordinate_integral_le (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) (hm : ∀ d, (∫ y, |w d y|) ≤ 1) (d : D) (i : I d) :
    (∫ x, |fderiv ℝ (sigmaAxisWeight w) x (Pi.single ⟨d, i⟩ 1)|) ≤
      ∫ y, |fderiv ℝ (w d) y (Pi.single i 1)| := by
  rw [sigmaAxisWeight_coordinate_integral w hw]
  exact mul_le_of_le_one_right (integral_nonneg (fun _ => abs_nonneg _))
    (Finset.prod_le_one (fun e _ => integral_nonneg (fun _ => abs_nonneg _)) (fun e _ => hm e))

theorem sigmaAxisWeight_derivative_sum_le (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) (hm : ∀ d, (∫ y, |w d y|) ≤ 1) :
    (∑ s : Σ d, I d, ∫ x, |fderiv ℝ (sigmaAxisWeight w) x (Pi.single s 1)|) ≤
      ∑ d, ∑ i : I d, ∫ y, |fderiv ℝ (w d) y (Pi.single i 1)| := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun i _ =>
    sigmaAxisWeight_coordinate_integral_le w hw hm d i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I : Type*} [Fintype I]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

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

open MeasureTheory
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
open scoped ContDiff BigOperators

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

theorem affineBooleanCubeDeterminant_contDiff
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (v : Fin h) (sel : O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) :
    ContDiff ℝ ∞ (affineBooleanCubeDeterminant c sets block v sel L b) :=
  (booleanMinorDeterminant_contDiff c sets block v sel).comp
    (contDiff_const.add (L.contDiff.comp (blockCubeFlatten B (Fin h) α).contDiff))

variable (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
  (v : Fin h) (sel : J → O → Option α)
  (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
  (b : BlockParameter B (Fin h) α → ℝ)
  (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ)

theorem affineBooleanCubeGoodWeight_spec
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ i, 0 < r i) (hκ : ∀ j, 0 < κ j) :
    let w := affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ
    ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ (∀ a, 0 ≤ w a) ∧ (∫ a, |w a|) ≤ 1 ∧
      ∀ a ∈ tsupport w, (∀ z, |a z| ≤ 1) ∧
        ∀ j, κ j ≤ |booleanMinorDeterminant (c j) sets (block j) v (sel j) (b + L a)| := by
  let d := fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b
  have hs := scalarCubeGoodWeight_spec ψ hψ hrange hzero r hr κ hκ d
    (fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b)
  refine ⟨blockCubeWeight_contDiff _ hs.1, blockCubeWeight_compact _ hs.2.1,
    fun a => hs.2.2.2.1 _, ?_, ?_⟩
  · change (∫ a, |blockCubeWeight (scalarCubeGoodWeight α ψ r κ d) a|) ≤ 1
    rw [blockCubeWeight_abs_integral]
    exact hs.2.2.2.2
  · intro a ha
    refine ⟨blockCubeWeight_box _ (fun x hx => (hs.2.2.1 hx).1) ha, ?_⟩
    change a ∈ tsupport (blockCubeWeight (scalarCubeGoodWeight α ψ r κ d)) at ha
    rw [blockCubeWeight_tsupport] at ha
    intro j
    simpa only [d, affineBooleanCubeDeterminant, ContinuousLinearEquiv.apply_symm_apply] using
      (hs.2.2.1 ha).2 j

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators NNReal

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

theorem affineBooleanCubeDeterminant_fderiv_norm_le
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (v : Fin h) (sel : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) (hL : ‖L‖ ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ o, |c (block o)| ≤ C)
    (x : (B × Fin h) → Option α → ℝ)
    (hx : ∀ z, |(b + L (blockCubeFlatten B (Fin h) α x)) z| ≤ 1) :
    ‖fderiv ℝ (affineBooleanCubeDeterminant c sets block v sel L b) x‖ ≤
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C 1 := by
  let e := (blockCubeFlatten B (Fin h) α).toContinuousLinearMap
  have hLe : ‖L.comp e‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le L e).trans
    exact (mul_le_mul hL (blockCubeFlatten_norm_le_one B (Fin h) α)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hF := (booleanMinorDeterminant_contDiff c sets block v sel).differentiable (by norm_num)
  have hd := affineSlice_fderiv (booleanMinorDeterminant c sets block v sel) b (L.comp e) x
    (hF (b + (L.comp e) x))
  change fderiv ℝ (affineBooleanCubeDeterminant c sets block v sel L b) x = _ at hd
  rw [hd]
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hLe)).trans
      (booleanMinorDeterminant_fderiv_norm_le c sets block v sel hcard _ hC le_rfl hc hx)

theorem affineBooleanCubeGoodWeight_derivative_budget
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (v : Fin h) (sel : J → O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) (hL : ‖L‖ ≤ 1)
    (hbox : ∀ x ∈ scalarCubeProductDomain (B × Fin h) α,
      ∀ z, |(b + L (blockCubeFlatten B (Fin h) α x)) z| ≤ 1)
    (C : J → ℝ) (hC : ∀ j, 0 ≤ C j) (hc : ∀ j o, |c j (block j o)| ≤ C j)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ j, 0 < κ j) :
    (∑ z : BlockParameter B (Fin h) α, ∫ a,
      |fderiv ℝ (affineBooleanCubeGoodWeight c sets block v sel L b ψ r κ) a (Pi.single z 1)|) ≤
      (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
        (Fintype.card (B × Fin h) : ℝ) * ((Fintype.card α : ℝ) + 1) *
          (∑ j, (A : ℝ) / κ j * productMinorDeterminantDerivativeBound
            (Fintype.card (BlockParameter B (Fin h) α)) (Fintype.card O) (Fintype.card α) h (C j) 1) := by
  let d := fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b
  have hd := fun j => affineBooleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j) L b
  have hw : ContDiff ℝ 1 (scalarCubeGoodWeight α ψ r κ d) :=
    (scalarCubeProductWeight_spec (α := α) r hr).1.mul
      ((sublevelCutoffProduct_smooth ψ hψ κ d hd).of_le (by norm_num))
  unfold affineBooleanCubeGoodWeight
  rw [blockCubeWeight_derivative_sum _ hw]
  let D : J → ℝ≥0 := fun j => ⟨productMinorDeterminantDerivativeBound
    (Fintype.card (BlockParameter B (Fin h) α)) (Fintype.card O) (Fintype.card α) h (C j) 1,
      productMinorDeterminantDerivativeBound_nonneg _ _ _ _ (hC j) zero_le_one⟩
  exact scalarCubeGoodWeight_derivative_budget ψ hψ hrange A T hLip hTransition r hr κ hκ d hd D
    (fun j x hx => affineBooleanCubeDeterminant_fderiv_norm_le (c j) sets (block j) v (sel j)
      hcard L b hL (hC j) (hc j) x (hbox x hx))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanSource
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
  (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
  (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
  (ψ : ℝ → ℝ) (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointAffineBooleanGoodWeight_derivative_budget {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hL : ∀ d, ‖L d‖ ≤ 1)
    (hbox : ∀ d x, x ∈ scalarCubeProductDomain (B d × Fin (h d)) α →
      ∀ z, |(b d + L d (blockCubeFlatten (B d) (Fin (h d)) α x)) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) :
    (∑ s : JointBlockParameter B h α, ∫ x,
      |fderiv ℝ (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) x (Pi.single s 1)|) ≤
      jointBooleanWeightBudget (O := O) (α := α) h C A T r κ := by
  have hs (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
    hψ hrange hzero (hr d) (fun _ => hκ d)
  apply (sigmaAxisWeight_derivative_sum_le _ (fun d => (hs d).1)
    (fun d => (hs d).2.2.2.1)).trans
  unfold jointBooleanWeightBudget
  apply Finset.sum_le_sum
  intro d _
  have hb := affineBooleanCubeGoodWeight_derivative_budget (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (hcard d) (L d) (b d) (hL d) (hbox d)
    (fun _ => C d) (fun _ => hC d) (fun _ => hc d) ψ hψ hrange A T hLip hTransition
    (r d) (hr d) (fun _ => κ d) (fun _ => hκ d)
  simpa only [Fintype.sum_unique, BlockParameter, Fintype.card_prod, Fintype.card_option,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [Fintype α] [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.jointAffineBooleanGoodWeight_derivative_budget.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.jointAffineBooleanGoodWeight_derivative_budget.{u_1, u_2, u_3, u_4}
