-- Prove2me | solution 1 for OAI.SquareRootDegree.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:51:01.475654+00:00
-- url     : https://prove2.me/submissions/29f0cfee-669f-4ce1-b8af-893503e105a2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Main.lean:L19-L21
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.SquareRootDegree.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_SquareRootDegree_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_CellDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Grouping
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Amplification
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_ReadoutCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Readout
import Theorems.Thm_OAI_SquareRootDegree_GaussianGain_tail_integral_bound
import Theorems.Thm_OAI_SquareRootDegree_Observations_exists_amplification
import Theorems.Thm_OAI_SquareRootDegree_Observations_grouped_score
import Theorems.Thm_OAI_SquareRootDegree_Observations_singletonSum_eq_average
import Theorems.Thm_OAI_SquareRootDegree_ReadoutCLT_exists_abs_gain
import Theorems.Thm_OAI_SquareRootDegree_SmoothGaussian_beta_lower
import Theorems.Thm_OAI_SquareRootDegree_SmoothGaussian_weighted_interval_bounds
import Theorems.Thm_OAI_SquareRootDegree_SmoothSelector_hat_local
import Theorems.Thm_OAI_SquareRootDegree_TableRounding_event_indicator
import Theorems.Thm_OAI_SquareRootDegree_cell_tuple
import Theorems.Thm_OAI_SquareRootDegree_fourierDegree_comp_coordinates_le
import Theorems.Thm_OAI_SquareRootDegree_fourierDegree_mul_le
import Theorems.Thm_OAI_SquareRootDegree_fourier_inversion

-- ---- from OAI.Combinatorics.BooleanFunctions.Walsh ----
namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Finite Walsh calculus -/

theorem sign_ne_zero (b : Bool) : sign b ≠ 0 := by
  cases b <;> norm_num [sign]

theorem average_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_sum {α κ : Type*} [Fintype α] (s : Finset κ) (f : κ → α → ℝ) :
    average (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem character_ne_zero {ι : Type*} (s : Finset ι) (x : Cube ι) :
    character s x ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun i _ => sign_ne_zero (x i)

theorem fourierDegree_reflection {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) (a : Cube ι) :
    fourierDegree (fun x => f (reflection a x)) = fourierDegree f := by
  classical
  simp [fourierDegree, fourierCoeff_reflection, character_ne_zero]

theorem fourierCoeff_positive_reflection {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) (i : ι) :
    fourierCoeff (fun x => f (reflection (positiveMask f) x)) {i} =
      |fourierCoeff f {i}| := by
  classical
  rw [fourierCoeff_reflection, character_singleton]
  by_cases h : fourierCoeff f {i} < 0
  · simp [positiveMask, sign, h, abs_of_neg h]
  · simp [positiveMask, sign, h, abs_of_nonneg (le_of_not_gt h)]

theorem singletonSum_positive_reflection {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) :
    singletonSum (fun x => f (reflection (positiveMask f) x)) = absoluteSingletonSum f := by
  simp [singletonSum, absoluteSingletonSum, fourierCoeff_positive_reflection]

theorem isBoolean_reflection {ι : Type*} (f : Cube ι → ℝ) (a : Cube ι)
    (hf : IsBoolean f) : IsBoolean (fun x => f (reflection a x)) := fun x => hf (reflection a x)

theorem nonconstant_reflection {ι : Type*} (f : Cube ι → ℝ) (a : Cube ι)
    (hf : Nonconstant f) : Nonconstant (fun x => f (reflection a x)) := by
  obtain ⟨x, y, h⟩ := hf
  exact ⟨reflection a x, reflection a y, by simpa using h⟩

theorem singletonSum_le_absoluteSingletonSum {ι : Type*} [Fintype ι]
    (f : Cube ι → ℝ) : singletonSum f ≤ absoluteSingletonSum f :=
  Finset.sum_le_sum fun i _ => le_abs_self (fourierCoeff f {i})

theorem positive_degree_of_nonconstant {ι : Type*} [Fintype ι] (f : Cube ι → ℝ)
    (hf : Nonconstant f) : 0 < fourierDegree f := by
  classical
  by_contra h
  have hd : fourierDegree f = 0 := Nat.eq_zero_of_not_pos h
  have hc (x : Cube ι) : f x = fourierCoeff f ∅ := by
    rw [fourier_inversion f x]
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro s _ hs
      have hpos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      rw [fourierCoeff_eq_zero_of_degree_lt f (by simpa [hd] using hpos), zero_mul]
    · simp
  obtain ⟨x, y, hxy⟩ := hf
  exact hxy ((hc x).trans (hc y).symm)

/-- Coordinate reflection exactly identifies the signed and absolute linear sums,
without changing the ordinary real Fourier degree or Boolean/nonconstant status. -/
theorem coordinate_reflection {ι : Type*} [Fintype ι] (f : Cube ι → ℝ)
    (hf : IsBoolean f) (hn : Nonconstant f) :
    ∃ g : Cube ι → ℝ, IsBoolean g ∧ Nonconstant g ∧
      fourierDegree g = fourierDegree f ∧ singletonSum g = absoluteSingletonSum f := by
  exact ⟨fun x => f (reflection (positiveMask f) x), isBoolean_reflection _ _ hf,
    nonconstant_reflection _ _ hn, fourierDegree_reflection _ _,
    singletonSum_positive_reflection _⟩

theorem absolute_unbounded_of_signed (h : SignedViolations) : ¬ BddAbove AbsoluteRatios := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, f, hf, hnon, hlt⟩ := h (max M 0 + 1) (by positivity)
  obtain ⟨g, hgb, hgn, hdeg, hsum⟩ := coordinate_reflection f hf hnon
  have hd := positive_degree_of_nonconstant g hgn
  have hs : 0 < Real.sqrt (fourierDegree g : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hm : absoluteSingletonSum g / Real.sqrt (fourierDegree g) ≤ M :=
    hM ⟨n, hn, g, hgb, hd, rfl⟩
  have hcompare : singletonSum f ≤ absoluteSingletonSum g :=
    calc singletonSum f ≤ absoluteSingletonSum f := singletonSum_le_absoluteSingletonSum f
      _ = singletonSum g := hsum.symm
      _ ≤ absoluteSingletonSum g := singletonSum_le_absoluteSingletonSum g
  have hlt' : max M 0 + 1 < absoluteSingletonSum g / Real.sqrt (fourierDegree g) := by
    apply (lt_div_iff₀ hs).mpr
    rw [hdeg]
    exact hlt.trans_le hcompare
  have := le_max_left M 0
  linarith

/-! ### Degree calculus for finite observations -/

theorem fourierCoeff_const_mul {ι : Type*} [Fintype ι]
    (c : ℝ) (f : Cube ι → ℝ) (s : Finset ι) :
    fourierCoeff (fun x => c * f x) s = c * fourierCoeff f s := by
  simp only [fourierCoeff, mul_assoc, average_const_mul]

theorem fourierCoeff_sum {ι κ : Type*} [Fintype ι]
    (t : Finset κ) (f : κ → Cube ι → ℝ) (s : Finset ι) :
    fourierCoeff (fun x => ∑ j ∈ t, f j x) s = ∑ j ∈ t, fourierCoeff (f j) s := by
  simp only [fourierCoeff, Finset.sum_mul, average_sum]

theorem fourierDegree_sum_le {ι κ : Type*} [Fintype ι]
    (t : Finset κ) (f : κ → Cube ι → ℝ) (d : ℕ)
    (h : ∀ j ∈ t, fourierDegree (f j) ≤ d) :
    fourierDegree (fun x => ∑ j ∈ t, f j x) ≤ d := by
  rw [fourierDegree_le_iff]
  intro s hs
  rw [fourierCoeff_sum]
  exact Finset.sum_eq_zero fun j hj =>
    fourierCoeff_eq_zero_of_degree_lt _ (lt_of_le_of_lt (h j hj) hs)

theorem fourierDegree_const_mul_le {ι : Type*} [Fintype ι]
    (c : ℝ) (f : Cube ι → ℝ) : fourierDegree (fun x => c * f x) ≤ fourierDegree f := by
  rw [fourierDegree_le_iff]
  intro s hs
  rw [fourierCoeff_const_mul, fourierCoeff_eq_zero_of_degree_lt _ hs, mul_zero]

theorem fourierDegree_const {ι : Type*} [Fintype ι] (c : ℝ) :
    fourierDegree (fun _ : Cube ι => c) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact fourierDegree_le_card_of_dependsOn (t := ∅) (by intro x y _; rfl)

theorem fourierDegree_prod_le {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (f : κ → Cube ι → ℝ) :
    fourierDegree (fun x => ∏ j ∈ s, f j x) ≤ ∑ j ∈ s, fourierDegree (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fourierDegree_const]
  | @insert j s hj ih =>
    simp only [Finset.prod_insert hj, Finset.sum_insert hj]
    exact (fourierDegree_mul_le _ _).trans (Nat.add_le_add_left ih _)

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Conditioning ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Uniform finite conditioning, without measure-theoretic assumptions -/

theorem cellMoment_eq_zero_of_mass_eq_zero {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) (h : cellMass F b = 0) :
    cellMoment F g b = 0 := by
  classical
  have hc : ∀ x, cell F b x = 0 := by
    intro x
    have hs : ∑ x, cell F b x = 0 := by
      unfold cellMass average at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by unfold cell; split <;> norm_num)).mp hs x (Finset.mem_univ x)
  simp [cellMoment, hc]

theorem mass_mul_conditionalValue {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) :
    cellMass F b * conditionalValue F g b = cellMoment F g b := by
  by_cases h : cellMass F b = 0
  · simp [h, cellMoment_eq_zero_of_mass_eq_zero F g b h]
  · simp [conditionalValue, field]

theorem average_mul_comp_eq_sum {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β) (g : α → ℝ) (h : β → ℝ) :
    average (fun x => h (F x) * g x) = ∑ b, h b * cellMoment F g b := by
  classical
  simp only [cellMoment, ← average_const_mul, ← average_sum]
  congr 1
  funext x
  simp [cell]

theorem cellMoment_conditionalAverage {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) :
    cellMoment F (conditionalAverage F g) b = cellMoment F g b := by
  have he : (fun x => cell F b x * conditionalAverage F g x) =
      (fun x => cell F b x * conditionalValue F g b) := by
    funext x
    unfold cell conditionalAverage
    split_ifs with h
    · rw [h]
    · simp
  rw [cellMoment, he, average_mul_const]
  exact mass_mul_conditionalValue F g b

theorem conditionalAverage_projection {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) (h : β → ℝ) :
    average (fun x => h (F x) * conditionalAverage F g x) =
      average (fun x => h (F x) * g x) := by
  rw [average_mul_comp_eq_sum, average_mul_comp_eq_sum]
  simp only [cellMoment_conditionalAverage]

theorem average_conditionalAverage {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) : average (conditionalAverage F g) = average g := by
  simpa using conditionalAverage_projection F g (fun _ => 1)

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Blocks ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Disjoint blocks and finite observation degree calculus -/

attribute [local instance] Classical.propDecidable

theorem average_pi_prod {κ α : Type*} [Fintype κ] [Fintype α] (f : κ → α → ℝ) :
    average (fun x : κ → α => ∏ i, f i (x i)) = ∏ i, average (f i) := by
  simp only [average, Fintype.card_fun, Nat.cast_pow, inv_pow, ← Fintype.prod_sum,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem average_pi_eval {κ α : Type*} [Fintype κ] [Fintype α] [Nonempty α]
    (j : κ) (f : α → ℝ) : average (fun x : κ → α => f (x j)) = average f := by
  have he := average_pi_prod (fun i a => if i = j then f a else 1)
  have hif (i : κ) : average (fun a : α => if i = j then f a else 1) =
      if i = j then average f else 1 := by
    split_ifs <;> simp_all [average_const]
  simpa [Finset.prod_ite_eq, hif] using he

theorem fourierDegree_comp_observation_le {ι α : Type*} [Fintype ι] [Fintype α]
    (F : Cube ι → α) (D : ℕ) (hF : ∀ a, fourierDegree (cell F a) ≤ D) (g : α → ℝ) :
    fourierDegree (fun x => g (F x)) ≤ D := by
  have he : (fun x => g (F x)) = fun x => ∑ a, g a * cell F a x := by
    funext x
    simp [cell]
  rw [he]
  apply fourierDegree_sum_le
  intro a _
  exact (fourierDegree_const_mul_le _ _).trans (hF a)

theorem fourierDegree_comp_tuple_le {ι α κ : Type*}
    [Fintype ι] [Fintype α] [Fintype κ]
    (F : κ → Cube ι → α) (D : κ → ℕ)
    (hF : ∀ i a, fourierDegree (cell (F i) a) ≤ D i) (g : (κ → α) → ℝ) :
    fourierDegree (fun x => g (fun i => F i x)) ≤ ∑ i, D i := by
  apply fourierDegree_comp_observation_le
  intro a
  have he : cell (fun x i => F i x) a = fun x => ∏ i, cell (F i) (a i) x := by
    funext x
    exact cell_tuple F a x
  rw [he]
  apply (fourierDegree_prod_le _ _).trans
  exact Finset.sum_le_sum (fun i _ => hF i (a i))

theorem fourierDegree_block_cell_le {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (F : Cube ι → α) (D : ℕ) (hF : ∀ a, fourierDegree (cell F a) ≤ D) (j : κ) (a : α) :
    fourierDegree (cell (fun x : Cube (κ × ι) => F (blockCurry κ ι Bool x j)) a) ≤ D := by
  exact (fourierDegree_comp_coordinates_le (cell F a) (fun i => (j,i))).trans (hF a)

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Observations ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable

variable {γ β κ : Type*} [Fintype γ] [Fintype β] [Fintype κ]
  [DecidableEq γ] [DecidableEq κ]

omit [Fintype β] [Fintype κ] in
theorem cubeSum_zero : average (cubeSum (γ := γ)) = 0 := by
  unfold cubeSum
  rw [average_sum]
  have hz : average sign = 0 := by norm_num [average,sign,Fintype.sum_bool]
  have hi (i : γ) : average (fun x : Cube γ => sign (x i)) = 0 := by
    calc _ = average sign := by
           convert average_pi_eval i sign using 1
           congr 1
           exact Subsingleton.elim _ _
      _ = 0 := hz
  simp only [hi,Finset.sum_const_zero]

omit [Fintype κ] in
theorem score_zero (F : Cube γ → β) : average (score F) = 0 := by
  rw [score,average_conditionalAverage]
  exact cubeSum_zero

omit [DecidableEq γ] [DecidableEq κ] in
theorem grouped_degree (F : Cube γ → β) (D : ℕ)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) (b : κ → β) :
    fourierDegree (cell (grouped F) b) ≤ Fintype.card κ*D := by
  have h := fourierDegree_comp_tuple_le (fun j x => F (fun i => x (j,i))) (fun _ : κ => D)
      (fun j a => fourierDegree_block_cell_le F D hF j a) (cell id b)
  have he : (fun x : Cube (κ × γ) => cell id b (fun j => F (fun i => x (j,i)))) =
      cell (grouped F) b := by
    funext x
    unfold cell grouped
    rfl
  rw [he] at h
  simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using h

omit [Fintype κ] [DecidableEq κ] in
theorem standard_zero (F : Cube γ → β) : average (standard F) = 0 := by
  change average (fun x => (Real.sqrt (variance F))⁻¹*score F x) = 0
  rw [average_const_mul,score_zero,mul_zero]

omit [Fintype β] [Fintype κ] [DecidableEq κ] in
theorem standard_sq (F : Cube γ → β) (hv : 0 < variance F) :
    average (fun x => (standard F x)^2) = 1 := by
  change average (fun x => ((Real.sqrt (variance F))⁻¹*score F x)^2) = 1
  simp only [mul_pow,average_const_mul,inv_pow]
  rw [Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

end Observations
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothGaussian ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothGaussian

theorem tent_nonneg (a h x : ℝ) : 0 ≤ tent a h x := le_max_left _ _

theorem tent_eq_zero {a h x : ℝ} (hh : 0 < h) (hx : h ≤ |x-a|) :
    tent a h x = 0 := by
  unfold tent
  apply max_eq_left
  have : 1 ≤ |x-a|/h := (one_le_div hh).mpr hx
  linarith

theorem tent_ne_zero_iff {a h x : ℝ} (hh : 0 < h) :
    tent a h x ≠ 0 ↔ |x-a| < h := by
  constructor
  · intro hn
    exact lt_of_not_ge (fun hx => hn (tent_eq_zero hh hx))
  · intro hx
    apply ne_of_gt
    apply lt_of_lt_of_le _ (le_max_right _ _)
    have := (div_lt_one hh).mpr hx
    linarith

theorem tent_support {a h : ℝ} (hh : 0 < h) :
    Function.support (tent a h) ⊆ Set.Icc (a-h) (a+h) := by
  intro x hx
  have he := (tent_ne_zero_iff hh).mp hx
  rw [abs_lt] at he
  constructor <;> linarith

theorem tent_compactSupport {a h : ℝ} (hh : 0 < h) : HasCompactSupport (tent a h) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := a-h) (b := a+h))
  intro x hx
  by_contra hn
  exact hx (tent_support hh hn)

theorem integrable_tent_mul {a h : ℝ} (hh : 0 < h) (p : ℝ → ℝ) (hp : Continuous p)
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] :
    Integrable (fun x => tent a h x * p x) μ := by
  apply ((continuous_tent a h).mul hp).integrable_of_hasCompactSupport
  exact (tent_compactSupport hh).mul_right

theorem tent_mass_pos {a h : ℝ} (hh : 0 < h) :
    0 < mass (gaussianReal 0 1) (tent a h) := by
  apply lt_of_lt_of_le _ (beta_lower hh)
  positivity

theorem tent_moments {a h : ℝ} (hh : 0 < h) :
    |mean (gaussianReal 0 1) (tent a h)-a| ≤ h ∧
    0 ≤ variance (gaussianReal 0 1) (tent a h) ∧
    variance (gaussianReal 0 1) (tent a h) ≤ h^2 := by
  apply weighted_interval_bounds (gaussianReal 0 1) (tent a h) hh.le (tent_nonneg a h)
  · intro x hx
    exact le_of_lt ((tent_ne_zero_iff hh).mp hx)
  · simpa using integrable_tent_mul (a := a) hh (fun _ => 1) continuous_const (gaussianReal 0 1)
  · exact integrable_tent_mul hh id continuous_id (gaussianReal 0 1)
  · exact integrable_tent_mul hh (fun x => x^2) (by fun_prop) (gaussianReal 0 1)
  · exact tent_mass_pos hh

end SmoothGaussian
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.SmoothSelector ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace SmoothSelector

theorem clip_nonneg (x : ℝ) : 0 ≤ clip x := le_max_left _ _
theorem clip_le_one (x : ℝ) : clip x ≤ 1 := max_le zero_le_one (min_le_left _ _)
theorem clip_mono : Monotone clip := fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)
theorem hat_nonneg (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    0 ≤ hat N δ i t := by
  unfold hat
  exact sub_nonneg.mpr (clip_mono (by linarith))

theorem hats_sum (N : ℕ) (δ t : ℝ) :
    ∑ i : Fin (2*N+1), hat N δ i t = clip (t/δ+N+1)-clip (t/δ-N) := by
  unfold hat
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    clip (t/δ+N-i+1)-clip (t/δ+N-i)) (2*N+1)]
  have he (i : ℕ) : clip (t/δ+N-i+1)-clip (t/δ+N-i) =
      clip (t/δ+N-i+1)-clip (t/δ+N-(i+1:ℕ)+1) := by push_cast; ring_nf
  simp_rw [he]
  rw [Finset.sum_range_sub']
  push_cast
  congr 1 <;> congr 1 <;> ring

theorem hats_sum_le_one (N : ℕ) (δ t : ℝ) :
    ∑ i : Fin (2*N+1), hat N δ i t ≤ 1 := by
  rw [hats_sum]
  linarith [clip_le_one (t/δ+N+1),clip_nonneg (t/δ-N)]

theorem weight_nonneg (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    0 ≤ weight N δ i t := by
  unfold weight
  split_ifs <;> linarith [hat_nonneg N δ i t, hats_sum_le_one N δ t]

theorem hat_support {N : ℕ} {δ t : ℝ} {i : Fin (2*N+1)} (hδ : 0 < δ)
    (hi : hat N δ i t ≠ 0) : |t| ≤ (N+1)*δ := by
  have hh := abs_lt.mp (hat_local hδ hi)
  have hi0 : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have hiN : (i:ℝ) ≤ 2*N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have h1 := mul_nonneg hδ.le hi0
  have h2 := mul_nonneg hδ.le (sub_nonneg.mpr hiN)
  rw [abs_le]
  dsimp [center] at hh
  constructor <;> nlinarith

theorem hat_compactSupport {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (i : Fin (2*N+1)) :
    HasCompactSupport (hat N δ i) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(N+1)*δ) (b := (N+1)*δ))
  intro x hx
  by_contra hn
  have hh := abs_le.mp (hat_support hδ hn)
  exact hx ⟨by linarith [hh.1],hh.2⟩

end SmoothSelector
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.GaussianGain ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace GaussianGain
open SmoothGaussian SmoothSelector

theorem gaussian_sq_integrable (v : ℝ≥0) : Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) := by
  simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

theorem density_div_mass_bound {a h δ R t : ℝ} (hh : 0 < h)
    (hδh : δ+h ≤ 1) (ha : |a-(1+t)| ≤ δ) (ht : |t| ≤ R+1) :
    gaussianPDFReal 0 1 t / mass (gaussianReal 0 1) (tent a h) ≤
      2/h * Real.exp (2*R+4) := by
  have hb := tent_mass_pos (a := a) hh
  have hA : |a|+h ≤ |t|+2 := by
    have he : |a| ≤ |a-(1+t)|+|1+t| := by
      simpa using abs_add_le (a-(1+t)) (1+t)
    have he' : |1+t| ≤ 1+|t| := by simpa using abs_add_le (1:ℝ) t
    linarith
  have hsq : (|a|+h)^2 ≤ (|t|+2)^2 := by
    nlinarith [abs_nonneg a, abs_nonneg t]
  have he : Real.exp (-t^2/2) ≤ Real.exp (-((|a|+h)^2)/2) * Real.exp (2*R+4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_abs t]
  apply (div_le_iff₀ hb).mpr
  have hl := beta_lower (a := a) hh
  have hp : 0 ≤ 2/h * Real.exp (2*R+4) := by positivity
  calc
    gaussianPDFReal 0 1 t ≤ (Real.sqrt (2*Real.pi))⁻¹ *
        (Real.exp (-((|a|+h)^2)/2) * Real.exp (2*R+4)) := by
      simpa only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] using
        mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (2/h * Real.exp (2*R+4)) *
      (h/2 * ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-((|a|+h)^2)/2))) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hp

theorem centralKernel_support {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (μ v β : Fin (2*N+1) → ℝ) {t : ℝ} (ht : (N+1)*δ < |t|) :
    centralKernel N δ μ v β t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : hat N δ i t = 0 := by
    by_contra hn
    exact (not_le_of_gt ht) (hat_support hδ hn)
  simp [hi]

theorem centralKernel_compactSupport {N : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (μ v β : Fin (2*N+1) → ℝ) : HasCompactSupport (centralKernel N δ μ v β) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(N+1)*δ) (b := (N+1)*δ))
  intro t ht
  apply centralKernel_support hδ
  by_contra hn
  have hh := abs_le.mp (le_of_not_gt hn)
  apply ht
  constructor <;> linarith [hh.1,hh.2]

theorem central_density_bound {N : ℕ} {δ h R M : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hsmall : δ+h ≤ 1) (hR : N*δ = R)
    (μ v : Fin (2*N+1) → ℝ)
    (hμ : ∀ i, |μ i-center N δ i| ≤ h) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ M)
    (t : ℝ) :
    gaussianPDFReal 0 1 t *
      centralKernel N δ μ v (fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)) t ≤
        (2/h * Real.exp (2*R+4)) * ((δ+h)^2+M) := by
  let K := 2/h * Real.exp (2*R+4)
  let B := (δ+h)^2+M
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := (hv0 ⟨0,by omega⟩).trans (hv _)
  have hB : 0 ≤ B := add_nonneg (sq_nonneg _) hM
  unfold centralKernel
  rw [Finset.mul_sum]
  calc
    ∑ i, gaussianPDFReal 0 1 t *
        (hat N δ i t * ((1+t-μ i)^2+v i) /
          mass (gaussianReal 0 1) (tent (center N δ i) h)) ≤
        ∑ i, hat N δ i t * (K*B) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : hat N δ i t = 0
      · simp [hi]
      have ha := hat_local hδ hi
      have ht := hat_support hδ hi
      have ht' : |t| ≤ R+1 := by rw [add_mul, hR] at ht; nlinarith
      have he := density_div_mass_bound hh hsmall ha.le ht'
      have herr : |1+t-μ i| ≤ δ+h := by
        have hx : |1+t-μ i| ≤ |center N δ i-(1+t)|+|μ i-center N δ i| := by
          have := abs_add_le (center N δ i-(1+t)) (μ i-center N δ i)
          simpa only [show center N δ i-(1+t)+(μ i-center N δ i) = -(1+t-μ i) by ring_nf,
            abs_neg] using this
        linarith [hμ i]
      have hnum : (1+t-μ i)^2+v i ≤ B := by
        dsimp [B]
        nlinarith [sq_abs (1+t-μ i), abs_nonneg (1+t-μ i), hv i]
      have hnum0 : 0 ≤ (1+t-μ i)^2+v i := add_nonneg (sq_nonneg _) (hv0 i)
      calc
        _ = hat N δ i t *
          ((gaussianPDFReal 0 1 t / mass (gaussianReal 0 1) (tent (center N δ i) h)) *
            ((1+t-μ i)^2+v i)) := by ring_nf
        _ ≤ hat N δ i t * (K*B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul he hnum hnum0 hK) (hat_nonneg ..)
    _ = (∑ i, hat N δ i t) * (K*B) := (Finset.sum_mul ..).symm
    _ ≤ K*B := by nlinarith [hats_sum_le_one N δ t, mul_nonneg hK hB]

theorem central_integral_bound {N : ℕ} {δ h R M : ℝ} (hδ : 0 < δ)
    (hh : 0 < h) (hsmall : δ+h ≤ 1) (hR : N*δ = R)
    (μ v : Fin (2*N+1) → ℝ)
    (hμ : ∀ i, |μ i-center N δ i| ≤ h) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ M) :
    (∫ t, centralKernel N δ μ v
       (fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)) t ∂gaussianReal 0 1) ≤
      4*(R+δ)/h * Real.exp (2*R+4) * ((δ+h)^2+M) := by
  let β := fun i => mass (gaussianReal 0 1) (tent (center N δ i) h)
  let f := fun t => gaussianPDFReal 0 1 t * centralKernel N δ μ v β t
  have hf : Integrable f volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [f]; unfold gaussianPDFReal; fun_prop
    · exact (centralKernel_compactSupport hδ μ v β).mul_left
  have he : ∫ t in Set.Icc (-(R+δ)) (R+δ), f t = ∫ t, f t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    dsimp [f]
    rw [centralKernel_support hδ μ v β]
    · exact mul_zero _
    · by_contra hn
      have hab := abs_le.mp (le_of_not_gt hn)
      rw [add_mul, hR, one_mul] at hab
      exact ht ⟨by linarith [hab.1],hab.2⟩
  have hbound := integral_mono_ae hf.integrableOn (integrable_const
    ((2/h * Real.exp (2*R+4))*((δ+h)^2+M)))
    (ae_of_all (volume.restrict (Set.Icc (-(R+δ)) (R+δ)))
      (central_density_bound hδ hh hsmall hR μ v hμ hv0 hv))
  rw [he] at hbound
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  change (∫ t, f t) ≤ _
  apply hbound.trans
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, smul_eq_mul]
  have hn : 0 ≤ R+δ-(-(R+δ)) := by
    have : 0 ≤ (N:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    rw [hR] at this
    linarith
  rw [ENNReal.toReal_ofReal hn]
  ring_nf

  exact le_rfl

theorem quadratic_integrable (c v : ℝ) (σ : ℝ≥0) :
    Integrable (fun t : ℝ => (1+t-c)^2+v) (gaussianReal 0 σ) := by
  have h0 : Integrable (fun _ : ℝ => (1-c)^2+v) (gaussianReal 0 σ) := integrable_const _
  have h1 : Integrable (fun t : ℝ => t) (gaussianReal 0 σ) :=
    (memLp_id_gaussianReal (μ := 0) (v := σ) 1).integrable (by norm_num)
  have h2 := gaussian_sq_integrable σ
  convert! (h2.add (h1.const_mul (2*(1-c)))).add h0 using 1
  funext t; simp only [Pi.add_apply]; ring_nf

theorem residual_quadratic_integrable {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (c v : ℝ) :
    Integrable (fun t => residual N δ t *((1+t-c)^2+v)) (gaussianReal 0 1) := by
  have hi (i : Fin (2*N+1)) : Integrable (fun t => hat N δ i t *((1+t-c)^2+v)) (gaussianReal 0 1) :=
    (by fun_prop : Continuous (fun t => hat N δ i t *((1+t-c)^2+v))).integrable_of_hasCompactSupport
      ((hat_compactSupport hδ i).mul_right)
  convert! (quadratic_integrable c v 1).sub (integrable_finsetSum _ (fun i _ => hi i)) using 1
  funext t
  simp only [Pi.sub_apply]
  dsimp [residual]
  rw [sub_mul,one_mul,Finset.sum_mul]

theorem gridN_pos : 0 < gridN := by norm_num [gridN]
theorem width_pos : 0 < width := by unfold width; positivity
theorem step_pos : 0 < step := by
  exact div_pos (by norm_num [radius]) (by exact_mod_cast gridN_pos)
theorem step_small : step+width ≤ 1 := by norm_num [step,radius,gridN,width]
theorem width_le_one : width ≤ 1 := by linarith [step_small,step_pos]
theorem grid_radius : (gridN:ℝ)*step = radius := by
  unfold step; field_simp [show (gridN:ℝ)≠0 by exact_mod_cast gridN_pos.ne']
theorem variance_numeric : (2*gridN+1:ℝ)*width^2 < 1/4 := by
  norm_num [gridN,width]

theorem central_numeric :
    4*(radius+step)/width * Real.exp (2*radius+4) *
      ((step+width)^2+(2*gridN+1:ℝ)*width^2) < 1/4 := by
  have he : Real.exp 196 < (3:ℝ)^196 := by
    calc Real.exp 196 = (Real.exp 1)^196 := by rw [← Real.exp_nat_mul]; norm_num
      _ < 3^196 := pow_lt_pow_left₀ (lt_trans Real.exp_one_lt_d9 (by norm_num))
        (Real.exp_pos _).le (by norm_num)
  have hp : 0 < 4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2) := by
    dsimp [radius,step,width,gridN]; positivity
  calc _ = Real.exp 196 * (4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2)) := by
           norm_num [radius]; ring_nf
    _ < 3^196 * (4*(radius+step)/width*((step+width)^2+(2*gridN+1:ℝ)*width^2)) :=
      mul_lt_mul_of_pos_right he hp
    _ < 1/4 := by norm_num [radius,step,width,gridN]

theorem tail_numeric : 972/width*Real.exp (-(radius^2/4)) < 1/4 := by
  have he : (2:ℝ)^2304 < Real.exp 2304 := by
    calc (2:ℝ)^2304 < (Real.exp 1)^2304 :=
           pow_lt_pow_left₀ (lt_trans (by norm_num) Real.exp_one_gt_d9) (by norm_num) (by norm_num)
      _ = Real.exp 2304 := by rw [← Real.exp_nat_mul]; norm_num
  have hi : Real.exp (-2304) < ((2:ℝ)^2304)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_lt_inv₀ (Real.exp_pos _) (by positivity)).mpr he
  calc _ = 972/width*Real.exp (-2304) := by norm_num [radius]
    _ < 972/width*((2:ℝ)^2304)⁻¹ := mul_lt_mul_of_pos_left hi (by unfold width; positivity)
    _ < 1/4 := by
      rw [show (2:ℝ)^2304 = ((2:ℝ)^128)^18 by rw [← pow_mul]]
      norm_num [width]

theorem beta_pos (i : Leaves) : 0 < beta i := tent_mass_pos width_pos
theorem mu_close (i : Leaves) : |mu i-center gridN step i| ≤ width :=
  (tent_moments width_pos).1
theorem sigma_nonneg (i : Leaves) : 0 ≤ sigma i := (tent_moments width_pos).2.1
theorem sigma_bound (i : Leaves) : sigma i ≤ width^2 := (tent_moments width_pos).2.2
theorem otherVariance_nonneg (i : Leaves) : 0 ≤ otherVariance i :=
  Finset.sum_nonneg (fun _ _ => sigma_nonneg _)
theorem otherVariance_bound (i : Leaves) : otherVariance i ≤ (2*gridN+1:ℝ)*width^2 := by
  calc otherVariance i ≤ ∑ j : Leaves, sigma j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => sigma_nonneg j)
    _ ≤ ∑ _ : Leaves, width^2 := Finset.sum_le_sum (fun j _ => sigma_bound j)
    _ = _ := by simp [Leaves]
theorem otherVariance_le_one (i : Leaves) : otherVariance i ≤ 1 :=
  (otherVariance_bound i).trans (le_trans variance_numeric.le (by norm_num))

theorem kernel_split_general (N : ℕ) (δ : ℝ) (μ v β : Fin (2*N+1) → ℝ) (t : ℝ) :
    (∑ i, weight N δ i t *((1+t-μ i)^2+v i)/β i) = centralKernel N δ μ v β t +
    residual N δ t *((1+t-μ (middle N))^2+v (middle N))/β (middle N) := by
  unfold weight centralKernel residual
  simp only [add_mul,add_div,Finset.sum_add_distrib]
  congr 1
  simp only [ite_mul,zero_mul,ite_div,zero_div,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem kernel_split (t : ℝ) : kernel t = centralKernel gridN step mu otherVariance beta t +
    residual gridN step t *((1+t-mu (middle gridN))^2+otherVariance (middle gridN))/beta (middle gridN) :=
  kernel_split_general gridN step mu otherVariance beta t

theorem J_lt_half : J < 1/2 := by
  have hc := central_integral_bound step_pos width_pos step_small grid_radius mu otherVariance
    mu_close otherVariance_nonneg otherVariance_bound
  have ht := tail_integral_bound step_pos width_pos width_le_one grid_radius
    (show |mu (middle gridN)-1| ≤ width by simpa using mu_close (middle gridN))
    (otherVariance_nonneg (middle gridN)) (otherVariance_le_one (middle gridN))
  have hb : beta (middle gridN) = mass (gaussianReal 0 1) (tent 1 width) := by
    simp [beta,leafTest]
  unfold J
  simp_rw [kernel_split]
  rw [integral_add ((centralKernel_continuous ..).integrable_of_hasCompactSupport
    (centralKernel_compactSupport step_pos ..))
      ((residual_quadratic_integrable step_pos _ _).div_const _), hb]
  change (∫ t, centralKernel gridN step mu otherVariance beta t ∂gaussianReal 0 1) + _ < _
  change (∫ t, centralKernel gridN step mu otherVariance beta t ∂gaussianReal 0 1) ≤ _ at hc
  linarith [central_numeric,tail_numeric]

theorem positive_gaussian_deficit :
    0 < (∏ i : Leaves, beta i) * (1+totalVariance-J) := by
  have hp : 0 < ∏ i : Leaves, beta i := Finset.prod_pos (fun _ _ => beta_pos _)
  have hs : 0 ≤ totalVariance := Finset.sum_nonneg (fun _ _ => sigma_nonneg _)
  exact mul_pos hp (by linarith [J_lt_half])

end GaussianGain
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.MomentTransfer ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace MomentTransfer
open SmoothGaussian SmoothSelector GaussianGain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussian_pow_integrable (k : Fin 3) :
    Integrable (fun x : ℝ => x^(k:ℕ)) (gaussianReal 0 1) := by
  fin_cases k
  · simp only [pow_zero]; exact integrable_const _
  · change Integrable (fun x : ℝ => x^1) (gaussianReal 0 1)
    simp only [pow_one]
    exact (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  · exact gaussian_sq_integrable 1

theorem weight_le_one (N : ℕ) (δ : ℝ) (i : Fin (2*N+1)) (t : ℝ) :
    weight N δ i t ≤ 1 := by
  calc weight N δ i t ≤ ∑ j, weight N δ j t :=
      Finset.single_le_sum (fun j _ => weight_nonneg N δ j t) (Finset.mem_univ i)
    _ = 1 := weight_sum ..

theorem gaussian_selector_integrable (k : Fin 3) (i : Leaves) :
    Integrable (fun x : ℝ => selectorTest i x*x^(k:ℕ)) (gaussianReal 0 1) := by
  apply (gaussian_pow_integrable k).norm.mono' (by dsimp [selectorTest]; fun_prop)
  filter_upwards [] with x
  change |weight gridN step i x*x^(k:ℕ)| ≤ |x^(k:ℕ)|
  rw [abs_mul,abs_of_nonneg (weight_nonneg ..)]
  exact mul_le_of_le_one_left (abs_nonneg _) (weight_le_one ..)

theorem quadratic_moment_formula {P : Measure ℝ} (w : ℝ → ℝ)
    (h0 : Integrable w P) (h1 : Integrable (fun x => w x*x) P)
    (h2 : Integrable (fun x => w x*x^2) P) (a v : ℝ) :
    (∫ x, w x*((1+x-a)^2+v) ∂P) = (∫ x, w x*x^2 ∂P) +
      2*(1-a)*(∫ x, w x*x ∂P) + ((1-a)^2+v)*(∫ x, w x ∂P) := by
  have he : (fun x => w x*((1+x-a)^2+v)) = fun x =>
      w x*x^2 + (2*(1-a))*(w x*x) + ((1-a)^2+v)*w x := by funext x; ring
  rw [he,integral_add (f := fun x => w x*x^2+(2*(1-a))*(w x*x))
    (g := fun x => ((1-a)^2+v)*w x) (h2.add (h1.const_mul _)) (h0.const_mul _),
    integral_add h2 (h1.const_mul _), integral_const_mul,integral_const_mul]

theorem gaussianGain_eq : gain gaussianLeafMoments gaussianSelectorMoments =
    (∏ i : Leaves, GaussianGain.beta i) * (1+totalVariance-J) := by
  have hi0 (i) : Integrable (selectorTest i) (gaussianReal 0 1) := by
    simpa only [Fin.val_zero,pow_zero,mul_one] using gaussian_selector_integrable 0 i
  have hi1 (i) : Integrable (fun x => selectorTest i x*x) (gaussianReal 0 1) := by
    simpa only [Fin.val_one,pow_one] using gaussian_selector_integrable 1 i
  have hi2 (i) : Integrable (fun x => selectorTest i x*x^2) (gaussianReal 0 1) :=
    gaussian_selector_integrable 2 i
  have hik (i) : Integrable (fun x => selectorTest i x*((1+x-mu i)^2+otherVariance i)/GaussianGain.beta i)
      (gaussianReal 0 1) := by
    have he : (fun x => selectorTest i x*((1+x-mu i)^2+otherVariance i)) = fun x =>
        selectorTest i x*x^2 + (2*(1-mu i))*(selectorTest i x*x) +
          ((1-mu i)^2+otherVariance i)*selectorTest i x := by funext x; ring
    apply Integrable.div_const
    rw [he]
    exact ((hi2 i).add ((hi1 i).const_mul _)).add ((hi0 i).const_mul _)
  have hJ : J = ∑ i, (gaussianSelectorMoments 2 i + 2*(1-mu i)*gaussianSelectorMoments 1 i +
      ((1-mu i)^2+otherVariance i)*gaussianSelectorMoments 0 i) / GaussianGain.beta i := by
    change (∫ t, ∑ i, selectorTest i t*((1+t-mu i)^2+otherVariance i)/GaussianGain.beta i
      ∂gaussianReal 0 1) = _
    rw [integral_finsetSum Finset.univ (fun i _ => hik i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_div,quadratic_moment_formula _ (hi0 i) (hi1 i) (hi2 i)]
    simp only [gaussianSelectorMoments,moments,Fin.val_zero,Fin.val_one,pow_zero,pow_one,mul_one,id_eq]
    rfl
  simp only [gain,gaussianLeaf_zero,gaussianLeaf_mean,gaussianLeaf_var,totalVariance,hJ,otherVariance]

theorem gaussianGain_pos : 0 < gain gaussianLeafMoments gaussianSelectorMoments := by
  rw [gaussianGain_eq]
  exact positive_gaussian_deficit

theorem eta_pos : 0 < eta := div_pos gaussianGain_pos (by norm_num)

end MomentTransfer
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.CellDegree ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace CellDegree
attribute [local instance] Classical.propDecidable
variable {γ β ι : Type*} [Fintype γ] [Fintype β] [Fintype ι]

omit [Fintype β] [Fintype ι] in
theorem sub_le (f g : Cube γ → ℝ) (d : ℕ)
    (hf : fourierDegree f ≤ d) (hg : fourierDegree g ≤ d) :
    fourierDegree (fun x => f x-g x) ≤ d := by
  rw [fourierDegree_le_iff]
  intro s hs
  simp only [fourierCoeff,sub_mul,average_sub]
  change fourierCoeff f s-fourierCoeff g s = 0
  rw [fourierCoeff_eq_zero_of_degree_lt f (lt_of_le_of_lt hf hs),
    fourierCoeff_eq_zero_of_degree_lt g (lt_of_le_of_lt hg hs),sub_self]

theorem event_degree (F₀ : Cube γ → β) (F : ι → Cube γ → β)
    (S : β → ι) (L : ι → β → Bool) (D : ℕ)
    (hF₀ : ∀ b, fourierDegree (cell F₀ b) ≤ D)
    (hF : ∀ i b, fourierDegree (cell (F i) b) ≤ D) :
    fourierDegree (fun x => if TableRounding.tableEvent S L (F₀ x,fun i => F i x) then 1 else 0) ≤
      Fintype.card ι*D := by
  have he : (fun x : Cube γ => if TableRounding.tableEvent S L (F₀ x,fun i => F i x) then (1:ℝ) else 0) =
      fun x => (∑ i, (if S (F₀ x) = i then (1:ℝ) else 0)*
        ∏ j ∈ Finset.univ.erase i, TableRounding.bit (L j (F j x))) -
      ∏ j, TableRounding.bit (L j (F j x)) := by
    funext x
    exact TableRounding.event_indicator S L (F₀ x,fun i => F i x)
  have hl (j : ι) : fourierDegree (fun x => TableRounding.bit (L j (F j x))) ≤ D :=
    fourierDegree_comp_observation_le (F j) D (hF j) (fun b => TableRounding.bit (L j b))
  have hp (I : Finset ι) : fourierDegree (fun x => ∏ j ∈ I, TableRounding.bit (L j (F j x))) ≤ I.card*D := by
    apply (fourierDegree_prod_le I _).trans
    calc ∑ j ∈ I, fourierDegree (fun x => TableRounding.bit (L j (F j x))) ≤ ∑ _j ∈ I, D :=
          Finset.sum_le_sum (fun j _ => hl j)
      _ = I.card*D := by simp
  rw [he]
  apply sub_le
  · apply fourierDegree_sum_le
    intro i _
    have hs : fourierDegree (fun x => if S (F₀ x) = i then (1:ℝ) else 0) ≤ D :=
      fourierDegree_comp_observation_le F₀ D hF₀ (fun b => if S b = i then 1 else 0)
    apply (fourierDegree_mul_le _ _).trans
    apply (Nat.add_le_add hs (hp _)).trans
    have hi : (Finset.univ.erase i : Finset ι).card+1 = Fintype.card ι :=
      Finset.card_erase_add_one (Finset.mem_univ i)
    calc D+(Finset.univ.erase i : Finset ι).card*D =
          ((Finset.univ.erase i : Finset ι).card+1)*D := by ring
      _ = Fintype.card ι*D := by rw [hi]
      _ ≤ Fintype.card ι*D := le_rfl
  · simpa only [Finset.card_univ] using hp Finset.univ

omit [Fintype γ] [Fintype β] in
theorem tuple_cell (F₀ : Cube γ → β) (F : ι → Cube γ → β) (a : β × (ι → β)) :
    cell (labelTuple F₀ F) a = fun x => cell F₀ a.1 x*∏ i, cell (F i) (a.2 i) x := by
  funext x
  rw [← cell_tuple F a.2 x]
  rcases a with ⟨a₀,a⟩
  simp only [cell,labelTuple,Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype β] in
theorem tuple_degree (F₀ : Cube γ → β) (F : ι → Cube γ → β) (D : ℕ)
    (hF₀ : ∀ b, fourierDegree (cell F₀ b) ≤ D)
    (hF : ∀ i b, fourierDegree (cell (F i) b) ≤ D) (a) :
    fourierDegree (cell (labelTuple F₀ F) a) ≤ (Fintype.card ι+1)*D := by
  rw [tuple_cell]
  apply (fourierDegree_mul_le _ _).trans
  have hp : fourierDegree (fun x => ∏ i, cell (F i) (a.2 i) x) ≤ Fintype.card ι*D := by
    apply (fourierDegree_prod_le _ _).trans
    calc ∑ i, fourierDegree (cell (F i) (a.2 i)) ≤ ∑ _i : ι, D :=
          Finset.sum_le_sum (fun i _ => hF i (a.2 i))
      _ = Fintype.card ι*D := by simp
  exact (Nat.add_le_add (hF₀ _) hp).trans (by simp only [Nat.add_mul,one_mul]; omega)

theorem observation_degree (F₀ Fw : Cube γ → β) (F : ι → Cube γ → β)
    (S : β → ι) (L : ι → β → Bool) (D : ℕ)
    (hF₀ : ∀ b, fourierDegree (cell F₀ b) ≤ D)
    (hFw : ∀ b, fourierDegree (cell Fw b) ≤ D)
    (hF : ∀ i b, fourierDegree (cell (F i) b) ≤ D) (a) :
    fourierDegree (cell (observationOn F₀ Fw F S L) a) ≤ (Fintype.card ι+1)*D := by
  cases a with
  | inl a =>
    have he : cell (observationOn F₀ Fw F S L) (Sum.inl a) =
        if TableRounding.tableEvent S L a then (fun _ => 0) else cell (labelTuple F₀ F) a := by
      funext x
      unfold cell observationOn
      by_cases h : labelTuple F₀ F x = a
      · by_cases ha : TableRounding.tableEvent S L a <;> simp [h,ha]
      · split_ifs <;> simp_all
    rw [he]
    split_ifs
    · simp [fourierDegree_const]
    · exact tuple_degree F₀ F D hF₀ hF a
  | inr a =>
    have he : cell (observationOn F₀ Fw F S L) (Sum.inr a) = fun x =>
        (if TableRounding.tableEvent S L (labelTuple F₀ F x) then (1:ℝ) else 0)*cell Fw a x := by
      funext x
      unfold cell observationOn
      split_ifs <;> simp_all
    rw [he]
    apply (fourierDegree_mul_le _ _).trans
    exact (Nat.add_le_add (event_degree F₀ F S L D hF₀ hF) (hFw a)).trans (by simp only [Nat.add_mul,one_mul]; omega)

end CellDegree
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
open Switching
attribute [local instance] Classical.propDecidable
variable {γ β ι : Type*} [Fintype γ] [Fintype β] [Fintype ι]
  [DecidableEq γ] [DecidableEq ι]

omit [DecidableEq γ] [DecidableEq ι] in
theorem switched_degree (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool) (D : ℕ)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) (a) :
    fourierDegree (cell (switched F S L) a) ≤ (Fintype.card ι+1)*D := by
  have he : switched F S L = CellDegree.observationOn
      (fun x => F (fun i => x (some none,i))) (fun x => F (fun i => x (none,i)))
      (fun j x => F (fun i => x (some (some j),i))) S L := rfl
  rw [he]
  apply CellDegree.observation_degree
  · exact fun a => fourierDegree_block_cell_le F D hF (some none) a
  · exact fun a => fourierDegree_block_cell_le F D hF none a
  · exact fun j a => fourierDegree_block_cell_le F D hF (some (some j)) a

end Observations
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Grouping ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
open Switching FiniteCLT UniformFinite GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable

variable {α δ ι : Type*} [Fintype α] [Fintype δ] [Fintype ι]

variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem grouped_score_scaled (F : Cube γ → β) (hv : 0 < variance F) {n : ℕ} (hn : 0 < n) :
    score (grouped (κ := Fin n) F) = fun x => groupScale F n * groupStandard F n x := by
  rw [grouped_score]
  funext x
  simp only [groupScale,groupStandard,normalizedSum,Function.comp_apply,blockCurry,Equiv.coe_fn_mk,
    standard,standardValue,← Finset.mul_sum]
  have hv' := (Real.sqrt_pos.mpr hv).ne'
  have hn' := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  unfold score conditionalAverage
  field_simp

end Observations
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Amplification ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Amplification
open Observations Switching GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable

attribute [instance] Observation.coordFintype Observation.coordDecidableEq Observation.labelFintype

theorem costFactor_eq : Fintype.card Leaves+1 = costFactor := by
  simp only [Leaves,Fintype.card_fin,costFactor]

theorem costFactor_pos : 0 < costFactor := by
  unfold costFactor
  omega

theorem factor_gt_one : 1 < factor := by
  unfold factor
  have : 0 < eta/(costFactor:ℝ) := div_pos eta_pos (Nat.cast_pos.mpr costFactor_pos)
  linarith

theorem ratio_improvement {q n D : ℕ} (hq : 0 < q) (hn : 0 < n) (hD : 0 < D)
    {v v' η : ℝ} (hv : (n:ℝ)*v*((q:ℝ)+η) < v') :
    (1+η/q)*(v/D) < v'/(q*(n*D):ℕ) := by
  rw [lt_div_iff₀ (Nat.cast_pos.mpr (Nat.mul_pos hq (Nat.mul_pos hn hD)))]
  calc (1+η/q)*(v/D)*(q*(n*D):ℕ) = (n:ℝ)*v*((q:ℝ)+η) := by
        have hD' : (D:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
        have hq' : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
        simp only [Nat.cast_mul]
        field_simp
    _ < _ := hv

theorem exists_step (F : Observation) : ∃ G : Observation, factor*ratio F < ratio G := by
  obtain ⟨n,hn,S,L,hv⟩ := exists_amplification F.map F.variance_pos
  have he : (Fintype.card Leaves:ℝ)+1 = (costFactor:ℝ) := by
    rw [← costFactor_eq,Nat.cast_add,Nat.cast_one]
  rw [he] at hv
  let G : Observation := {
    Coord := Slots Leaves × (Fin n × F.Coord)
    Label := EventSpace (Fin n → F.Label) Leaves ⊕ (Fin n → F.Label)
    map := switched (grouped (κ := Fin n) F.map) S L
    cost := costFactor*(n*F.cost)
    cost_pos := Nat.mul_pos costFactor_pos (Nat.mul_pos hn F.cost_pos)
    cell_le := fun b => by
      rw [← costFactor_eq]
      exact switched_degree _ _ _ _
        (fun a => by simpa only [Fintype.card_fin] using grouped_degree F.map F.cost F.cell_le a) b
    variance_pos := lt_trans (mul_pos (mul_pos (Nat.cast_pos.mpr hn) F.variance_pos)
      (add_pos (Nat.cast_pos.mpr costFactor_pos) eta_pos)) hv }
  refine ⟨G,?_⟩
  exact ratio_improvement costFactor_pos hn F.cost_pos hv

theorem base_ratio : ratio base = 1 := by
  unfold ratio base
  rw [identity_variance]
  norm_num

theorem exists_iterate (k : ℕ) : ∃ F : Observation, factor^k ≤ ratio F := by
  induction k with
  | zero => exact ⟨base,by simp [base_ratio]⟩
  | succ k ih =>
    obtain ⟨F,hF⟩ := ih
    obtain ⟨G,hG⟩ := exists_step F
    refine ⟨G,?_⟩
    calc factor^(k+1) = factor*factor^k := pow_succ' factor k
      _ ≤ factor*ratio F := mul_le_mul_of_nonneg_left hF (le_trans zero_le_one factor_gt_one.le)
      _ ≤ ratio G := hG.le

theorem exists_large_ratio (R : ℝ) : ∃ F : Observation, R < ratio F := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt R factor_gt_one
  obtain ⟨F,hF⟩ := exists_iterate k
  exact ⟨F,hk.trans_le hF⟩

end Amplification
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.ReadoutCLT ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace ReadoutCLT
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem constant_pos : 0 < constant := by
  have h := SmoothGaussian.tent_mass_pos (a := (1:ℝ)) (h := (1/2:ℝ)) (by norm_num)
  unfold constant test
  rw [integral_const_mul]
  positivity

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

end ReadoutCLT
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Readout ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable
variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

theorem readSign_boolean (z : ℝ) : readSign z = -1 ∨ readSign z = 1 := by
  unfold readSign
  split_ifs <;> simp

theorem readSign_mul (z : ℝ) : readSign z*z = |z| := by
  unfold readSign
  split_ifs with h
  · rw [one_mul,abs_of_nonneg h]
  · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]

omit [Fintype β] in
theorem readout_boolean (F : Cube γ → β) : IsBoolean (readout F) :=
  fun _ => readSign_boolean _

theorem readout_degree (F : Cube γ → β) (D : ℕ)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) :
    fourierDegree (readout F) ≤ D := by
  exact fourierDegree_comp_observation_le F D hF
    (fun b => readSign (conditionalValue F cubeSum b))

theorem readout_sum (F : Cube γ → β) :
    singletonSum (readout F) = average (fun x => |score F x|) := by
  rw [singletonSum_eq_average]
  have hp := conditionalAverage_projection F cubeSum
    (fun b => readSign (conditionalValue F cubeSum b))
  change average (fun x => readSign (conditionalValue F cubeSum (F x))*cubeSum x) = _
  exact hp.symm.trans (by
    change average (fun x => readSign (score F x)*score F x) = _
    simp only [readSign_mul])

theorem exists_readout (F : Cube γ → β) (hv : 0 < variance F) (D : ℕ)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n × γ) → ℝ,
      IsBoolean f ∧ fourierDegree f ≤ n*D ∧
      ReadoutCLT.constant*groupScale F n < singletonSum f := by
  let : MeasurableSpace (Cube γ) := ⊤
  obtain ⟨n,hn,hg⟩ := ReadoutCLT.exists_abs_gain (standard F) (standard_zero F) (standard_sq F hv)
  refine ⟨n,hn,readout (grouped (κ := Fin n) F),readout_boolean _,?_,?_⟩
  · apply readout_degree
    intro b
    simpa only [Fintype.card_fin] using grouped_degree F D hF b
  · rw [readout_sum,grouped_score_scaled F hv hn]
    have hk : 0 < groupScale F n := mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)) (Real.sqrt_pos.mpr hv)
    simp only [abs_mul,abs_of_pos hk,average_const_mul]
    have he := average_equiv (blockCurry (Fin n) γ Bool)
      (fun x => |FiniteCLT.normalizedSum (standard F) n x|)
    change _ < groupScale F n*average (fun x => |groupStandard F n x|)
    rw [show average (fun x => |groupStandard F n x|) =
      average (fun x => |FiniteCLT.normalizedSum (standard F) n x|) from he]
    rw [mul_comm ReadoutCLT.constant]
    exact mul_lt_mul_of_pos_left hg hk

end Observations
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable
variable {γ δ : Type*} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]

omit [DecidableEq γ] [DecidableEq δ] in
theorem cubeSum_reindex (e : γ ≃ δ) (x : Cube δ) :
    cubeSum (cubeReindex e x) = cubeSum x := by
  exact e.sum_comp (fun j => sign (x j))

theorem singletonSum_reindex (e : γ ≃ δ) (f : Cube γ → ℝ) :
    singletonSum (f ∘ cubeReindex e) = singletonSum f := by
  rw [singletonSum_eq_average,singletonSum_eq_average]
  have he : (fun x => (f ∘ cubeReindex e) x*cubeSum x) =
      (fun x => f x*cubeSum x) ∘ cubeReindex e := by
    funext x
    simp only [Function.comp_apply,cubeSum_reindex]
  rw [he]
  convert average_equiv (cubeReindex e) (fun x => f x*cubeSum x) using 1
  congr 1

omit [Fintype δ] [DecidableEq δ] in
theorem nonconstant_of_singletonSum_pos (f : Cube γ → ℝ) (hf : 0 < singletonSum f) :
    Nonconstant f := by
  by_contra h
  have hc : ∀ x y, f x = f y := by simpa only [Nonconstant,not_exists,not_not] using h
  have he : f = fun _ => f (fun _ => false) := funext fun x => hc x _
  rw [he,singletonSum_eq_average,average_const_mul,cubeSum_zero,mul_zero] at hf
  exact (lt_irrefl 0) hf

omit [Fintype δ] [DecidableEq δ] [DecidableEq γ] in
theorem positive_card_of_nonconstant (f : Cube γ → ℝ) (hf : Nonconstant f) :
    0 < Fintype.card γ := by
  by_contra h
  have hc : Fintype.card γ = 0 := Nat.eq_zero_of_not_pos h
  have : IsEmpty γ := Fintype.card_eq_zero_iff.mp hc
  obtain ⟨x,y,hxy⟩ := hf
  exact hxy (congrArg f (Subsingleton.elim x y))

omit [Fintype δ] [DecidableEq δ] in
theorem reindex_violation (f : Cube γ → ℝ) (C : ℝ) (hC : 0 < C)
    (hb : IsBoolean f) (hf : C*Real.sqrt (fourierDegree f) < singletonSum f) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : Cube (Fin n) → ℝ,
      IsBoolean g ∧ Nonconstant g ∧ C*Real.sqrt (fourierDegree g) < singletonSum g := by
  let e := Fintype.equivFin γ
  let g := f ∘ cubeReindex e
  have hp : 0 < singletonSum f := lt_of_le_of_lt (mul_nonneg hC.le (Real.sqrt_nonneg _)) hf
  have hn := nonconstant_of_singletonSum_pos f hp
  have hg : singletonSum g = singletonSum f := singletonSum_reindex e f
  refine ⟨Fintype.card γ,positive_card_of_nonconstant f hn,g,(fun x => hb _),?_,?_⟩
  · exact nonconstant_of_singletonSum_pos g (hg.symm ▸ hp)
  · rw [hg]
    have hd : fourierDegree g ≤ fourierDegree f := fourierDegree_comp_coordinates_le f e
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hd)) hC.le).trans_lt hf

end Observations
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable

theorem sqrt_ratio_bound {C c v : ℝ} {D n : ℕ}
    (hC : 0 < C) (hc : 0 < c) (hv : 0 ≤ v) (hD : 0 < D) (hn : 0 < n)
    (hq : (C/c)^2 < v/D) :
    C*Real.sqrt (n*D:ℕ) < c*(Real.sqrt n*Real.sqrt v) := by
  have hd : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hq' := (lt_div_iff₀ hd).mp hq
  have hm := mul_lt_mul_of_pos_left hq' (sq_pos_of_pos hc)
  have he : c^2*((C/c)^2*(D:ℝ)) = C^2*(D:ℝ) := by
    field_simp
  rw [he] at hm
  have hs : C*Real.sqrt D < c*Real.sqrt v := by
    apply (sq_lt_sq₀ (mul_nonneg hC.le (Real.sqrt_nonneg _))
      (mul_nonneg hc.le (Real.sqrt_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt hd.le,Real.sq_sqrt hv] using hm
  rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg n)]
  have hn' : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  calc C*(Real.sqrt n*Real.sqrt D) = Real.sqrt n*(C*Real.sqrt D) := by ring
    _ < Real.sqrt n*(c*Real.sqrt v) := mul_lt_mul_of_pos_left hs hn'
    _ = c*(Real.sqrt n*Real.sqrt v) := by ring

variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

theorem violation_of_observation (F : Cube γ → β) (D : ℕ) (hD : 0 < D)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) (hv : 0 < variance F)
    (C : ℝ) (hC : 0 < C) (hq : (C/ReadoutCLT.constant)^2 < variance F/D) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
      IsBoolean f ∧ Nonconstant f ∧ C*Real.sqrt (fourierDegree f) < singletonSum f := by
  obtain ⟨n,hn,f,hb,hd,hs⟩ := exists_readout F hv D hF
  apply reindex_violation f C hC hb
  have ht := sqrt_ratio_bound hC ReadoutCLT.constant_pos hv.le hD hn hq
  have hb' : C*Real.sqrt (fourierDegree f) ≤ C*Real.sqrt (n*D:ℕ) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hd)) hC.le
  exact hb'.trans_lt (ht.trans hs)

end Observations
end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Main ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-- Every stage and the final sign readout use finitely many actual Boolean inputs. -/
theorem signed_violations : SignedViolations := by
  intro C hC
  obtain ⟨F,hF⟩ := Amplification.exists_large_ratio ((C/ReadoutCLT.constant)^2)
  exact Observations.violation_of_observation F.map F.cost F.cost_pos F.cell_le
    F.variance_pos C hC hF

/-- Unbounded violations for ordinary real Fourier degree and uniform cube averages. -/
theorem main : SignedViolations ∧ ¬ BddAbove AbsoluteRatios := by
  exact ⟨signed_violations,absolute_unbounded_of_signed signed_violations⟩

end SquareRootDegree

end

end OAI

-- ---- mission target ----
open OAI OAI.SquareRootDegree
open scoped BigOperators

theorem solution : SignedViolations ∧ ¬ BddAbove AbsoluteRatios := by
  first
    | exact OAI.SquareRootDegree.main
    | (apply OAI.SquareRootDegree.main <;> assumption)
    | (intros; apply OAI.SquareRootDegree.main <;> assumption)
