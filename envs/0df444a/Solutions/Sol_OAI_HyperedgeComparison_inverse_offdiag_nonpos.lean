-- Prove2me | solution 1 for OAI.HyperedgeComparison.inverse_offdiag_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:09:35.139824+00:00
-- url     : https://prove2.me/submissions/2584aa69-7b76-4ef3-ace0-995de13208a3

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L1298-L1327
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.inverse_offdiag_nonpos. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Theorems.Thm_OAI_HyperedgeComparison_baseMatrix_diag_pos
import Theorems.Thm_OAI_HyperedgeComparison_coeff_nonneg

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

section FiniteLaw
variable [Fintype E]

omit [Fintype E] in
/-- Closing every hyperedge isolates every node, in every deletion graph. -/
theorem cluster_all_closed (H : Hypergraph V E) (D : Set V) (s : V) :
    cluster H (fun _ => false) D s = {s} := by
  ext y
  constructor
  · intro hy
    change y = s
    induction hy with
    | refl => rfl
    | tail _ h _ => obtain ⟨e, he, _⟩ := h; simp at he
  · rintro rfl
    exact .refl

/-- Probability mass of the all-closed finite configuration. -/
theorem all_closed_mass (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).real {fun _ => false} = ∏ e, (1 - (p e : ℝ)) := by
  classical
  rw [Measure.real_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {false} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton false)]
  simp [unitInterval.coe_symm_eq]

theorem all_closed_mass_pos (p : E → Set.Icc (0 : ℝ) 1)
    (hp : ∀ e, (p e : ℝ) < 1) : 0 < (law p).real {fun _ => false} := by
  rw [all_closed_mass]
  exact Finset.prod_pos (fun e _ => sub_pos.mpr (hp e))

theorem baseMatrix_lowerTriangular {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : (baseMatrix H p x).IsLowerTriangular := by
  intro i j hij
  have hf (ω : E → Bool) : ¬firstRoot H x ω ∅ j i := by
    intro hf
    exact Set.disjoint_left.mp hf.1 hf.2 ⟨i, hij, rfl⟩
  simp [baseMatrix, column, hf]

theorem baseMatrix_det_ne_zero {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (baseMatrix_lowerTriangular H p x)]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => ne_of_gt (baseMatrix_diag_pos H p hp x hx k))

theorem column_const {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (c : ℝ) :
    column H p x k (fun _ => c) = c • column H p x k (fun _ => 1) := by
  funext i
  unfold column
  change (∫ ω, if firstRoot H x ω ∅ k i then c else 0 ∂law p) =
    c * ∫ ω, if firstRoot H x ω ∅ k i then 1 else 0 ∂law p
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i <;> simp [hf]

theorem coeff_const {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k i : Fin n) (c : ℝ) :
    coeff H p x k (fun _ => c) i = if i = k then c else 0 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  have hinv : coeff H p x k (fun _ => 1) i = if i = k then 1 else 0 := by
    change ((baseMatrix H p x)⁻¹ * baseMatrix H p x) i k = _
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
  unfold coeff
  rw [column_const, Matrix.mulVec_smul]
  change c * coeff H p x k (fun _ => 1) i = _
  rw [hinv]
  split_ifs <;> simp

omit [Fintype E] in
theorem isolated_firstRoot {n : ℕ} {H : Hypergraph V E} {x : Fin n → V}
    {k : Fin n} {ω : E → Bool}
    (h : ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j)) : firstRoot H x ω ∅ k k := by
  refine ⟨Set.disjoint_left.mpr ?_, .refl⟩
  rintro y hy ⟨j, hj, rfl⟩
  exact h j (ne_of_lt hj) hy

theorem isolatedMass_pos {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < isolatedMass H p x k := by
  have hi : (∫ ω : E → Bool, if ω = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  apply (all_closed_mass_pos p hp).trans_le
  rw [← hi]
  unfold isolatedMass
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hc : ω = (fun _ => false)
  · subst ω
    have hf : ∀ j, j ≠ k → ¬Connected H (fun _ => false) ∅ (x k) (x j) := by
      intro j hj hc
      have : x j ∈ cluster H (fun _ => false) ∅ (x k) := hc
      rw [cluster_all_closed] at this
      exact hj (hx this)
    dsimp only
    rw [ite_eq_left hf]
    simp
  · simp only [hc, ite_false]
    split_ifs <;> norm_num

theorem column_hitsOther {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) :
    column H p x k (hitsOther x k) = column H p x k (fun _ => 1) -
      Pi.single k (isolatedMass H p x k) := by
  classical
  funext i
  change column H p x k (hitsOther x k) i = column H p x k (fun _ => 1) i - _
  by_cases hik : i = k
  · subst i
    simp only [Pi.single_eq_same]
    unfold column isolatedMass
    rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    by_cases ho : ∃ j, j ≠ k ∧ x j ∈ cluster H ω ∅ (x k)
    · have hn : ¬∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) := by
        obtain ⟨j, hj, hc⟩ := ho
        exact fun h => h j hj hc
      simp [hitsOther, ho, hn]
    · have hy : ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) := by
        intro j hj hc
        exact ho ⟨j, hj, hc⟩
      simp only [hitsOther, ite_eq_right ho, ite_eq_left hy, ite_eq_left (isolated_firstRoot hy)]
      norm_num
  · simp only [Pi.single_eq_of_ne hik, sub_zero]
    unfold column
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hf : firstRoot H x ω ∅ k i
    · simp [hf, hitsOther, show ∃ j, j ≠ k ∧ x j ∈ cluster H ω ∅ (x k) from ⟨i, hik, hf.2⟩]
    · simp [hf]

/-- The inverse cluster matrix has nonpositive off-diagonal entries. -/
theorem inverse_offdiag_nonpos [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) {k i : Fin n} (hik : i ≠ k) :
    (baseMatrix H p x)⁻¹ i k ≤ 0 := by
  have hF0 : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ hitsOther x k U := by
    intro U _
    unfold hitsOther
    split_ifs <;> norm_num
  have hFm : MonotoneOn (hitsOther x k) (ClusterDomain (x k) (earlier x k)) := by
    intro U _ U' _ hUU
    unfold hitsOther
    split_ifs with h h'
    · rfl
    · obtain ⟨j, hj, hc⟩ := h
      exact (h' ⟨j, hj, hUU hc⟩).elim
    · norm_num
    · rfl
  have hc := coeff_nonneg H p hp x hx k (hitsOther x k) hF0 hFm i
  have heq : coeff H p x k (hitsOther x k) i =
      -(baseMatrix H p x)⁻¹ i k * isolatedMass H p x k := by
    unfold coeff
    rw [column_hitsOther, Matrix.mulVec_sub]
    change coeff H p x k (fun _ => 1) i - _ = _
    rw [coeff_const H p hp x hx, ite_eq_right hik]
    rw [Matrix.mulVec_single]
    simp
  rw [heq] at hc
  have ha := isolatedMass_pos H p hp x hx k
  nlinarith

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.inverse_offdiag_nonpos.{uE,uV} := @_root_.OAI.HyperedgeComparison.inverse_offdiag_nonpos.{uE,uV}
