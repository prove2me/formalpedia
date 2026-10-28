-- Prove2me | solution 1 for OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:22:31.807389+00:00
-- url     : https://prove2.me/submissions/cf667e5c-7978-4911-93de-c09ed9b408f4

import Mathlib
import Definitions.Def_Brenier
import Definitions.Def_OAIQ5T2000

section
-- module Solutions.OAIQ5_T2.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_AffineTies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!+# Generic lines avoid affine subspaces of codimension at least two

This is the general-position step used in the cell-connectivity argument.
It does not assert that a nonempty cell intersection has positive surface measure.
-/

section

open scoped RealInnerProductSpace

namespace Problem358.TripleCell

/-- Three functions, each strictly largest somewhere, cannot have proportional differences. -/
theorem no_proportional_differences {X : Type*} {f g h : X → ℝ}
    (hf : ∃ x, g x < f x ∧ h x < f x)
    (hg : ∃ x, f x < g x ∧ h x < g x)
    (hh : ∃ x, f x < h x ∧ g x < h x) :
    ¬ ∃ r : ℝ, ∀ x, f x - h x = r * (f x - g x) := by
  rintro ⟨r, hr⟩
  obtain ⟨x0, h0g, h0h⟩ := hf
  obtain ⟨x1, h1f, h1h⟩ := hg
  obtain ⟨x2, h2f, h2g⟩ := hh
  have hpos : 0 < r := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (le_of_lt (sub_pos.mpr h0g))
    nlinarith [hr x0]
  have hlt : r < 1 := by
    by_contra hn
    have hm := mul_le_mul_of_nonpos_right (le_of_not_gt hn) (le_of_lt (sub_neg.mpr h1f))
    nlinarith [hr x1]
  have hneg : f x2 - g x2 < 0 := by
    by_contra hn
    have hm := mul_nonneg hpos.le (le_of_not_gt hn)
    nlinarith [hr x2]
  have hm := mul_lt_mul_of_neg_right hlt hneg
  nlinarith [hr x2]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- At a common tie point, strict activity of all three branches excludes
proportional slope differences. -/
theorem no_proportional_slopes_of_tie {y0 y1 y2 z : V} {c0 c1 c2 : ℝ}
    (hf : ∃ x, score y1 c1 x < score y0 c0 x ∧ score y2 c2 x < score y0 c0 x)
    (hg : ∃ x, score y0 c0 x < score y1 c1 x ∧ score y2 c2 x < score y1 c1 x)
    (hh : ∃ x, score y0 c0 x < score y2 c2 x ∧ score y1 c1 x < score y2 c2 x)
    (h01 : score y0 c0 z = score y1 c1 z)
    (h02 : score y0 c0 z = score y2 c2 z) :
    ∀ r : ℝ, r • (y0 - y1) ≠ y0 - y2 := by
  intro r hr
  apply no_proportional_differences hf hg hh
  refine ⟨r, ?_⟩
  have hv (x : V) : ⟪x, y0⟫ - ⟪x, y2⟫ =
      r * (⟪x, y0⟫ - ⟪x, y1⟫) := by
    have he := congrArg (fun v : V => ⟪x, v⟫) hr
    simpa only [inner_smul_right, inner_sub_right] using he.symm
  have hc : c0 - c2 = r * (c0 - c1) := by
    unfold score at h01 h02
    have hm := congrArg (fun a : ℝ => r * a) h01
    nlinarith [hv z]
  intro x
  unfold score
  nlinarith [hv x]

/-- The two tie-plane normals at a triple tie are linearly independent whenever
all three affine branches are strictly active somewhere. -/
theorem linearIndependent_slopes_of_tie {y0 y1 y2 z : V} {c0 c1 c2 : ℝ}
    (hf : ∃ x, score y1 c1 x < score y0 c0 x ∧ score y2 c2 x < score y0 c0 x)
    (hg : ∃ x, score y0 c0 x < score y1 c1 x ∧ score y2 c2 x < score y1 c1 x)
    (hh : ∃ x, score y0 c0 x < score y2 c2 x ∧ score y1 c1 x < score y2 c2 x)
    (h01 : score y0 c0 z = score y1 c1 z)
    (h02 : score y0 c0 z = score y2 c2 z) :
    LinearIndependent ℝ ![y0 - y1, y0 - y2] := by
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro hzero
    have hy : y0 = y2 := sub_eq_zero.mp hzero
    obtain ⟨x, _, hstrict⟩ := hf
    unfold score at h02 hstrict
    rw [hy] at h02 hstrict
    linarith
  · apply no_proportional_slopes_of_tie
      (hf.imp fun x hx => hx.symm) hh hg h02 h01

/-- A vector outside a line is detected by some vector tangent to its orthogonal plane. -/
theorem exists_tangent_inner_ne_zero {u v : V}
    (h : ∀ r : ℝ, r • u ≠ v) :
    ∃ w : (ℝ ∙ u)ᗮ, ⟪(w : V), v⟫ ≠ 0 := by
  by_contra! hn
  have hv : v ∈ ((ℝ ∙ u)ᗮ)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    exact hn ⟨w, hw⟩
  rw [Submodule.orthogonal_orthogonal] at hv
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hv
  exact h r hr

/-- The second independent tie normal cuts out a null set for Haar measure on
 the first tie plane's tangent vector space. -/
theorem tangent_inner_zero_null [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {u v : V}
    (h : ∀ r : ℝ, r • u ≠ v)
    (μ : MeasureTheory.Measure ((ℝ ∙ u)ᗮ)) [μ.IsAddHaarMeasure] :
    μ {w : (ℝ ∙ u)ᗮ | ⟪(w : V), v⟫ = 0} = 0 := by
  let L : ((ℝ ∙ u)ᗮ) →ₗ[ℝ] ℝ := (innerₗ V v).comp ((ℝ ∙ u)ᗮ).subtype
  have hker : L.ker ≠ ⊤ := by
    obtain ⟨w, hw⟩ := exists_tangent_inner_ne_zero h
    intro heq
    have hm : w ∈ L.ker := by rw [heq]; trivial
    apply hw
    simpa [L, real_inner_comm] using hm
  have heq : {w : (ℝ ∙ u)ᗮ | ⟪(w : V), v⟫ = 0} = (L.ker : Set ((ℝ ∙ u)ᗮ)) := by
    ext w
    simp [L, real_inner_comm]
  rw [heq]
  exact MeasureTheory.Measure.addHaar_submodule μ L.ker hker

/-- Every affine level of the second independent normal is surface-null. -/
theorem tangent_inner_level_null [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {u v : V}
    (h : ∀ r : ℝ, r • u ≠ v)
    (μ : MeasureTheory.Measure ((ℝ ∙ u)ᗮ)) [μ.IsAddHaarMeasure] (t : ℝ) :
    μ {w : (ℝ ∙ u)ᗮ | ⟪(w : V), v⟫ = t} = 0 := by
  let S : Set ((ℝ ∙ u)ᗮ) := {w | ⟪(w : V), v⟫ = t}
  change μ S = 0
  by_cases hs : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hs
    have heq : (fun w => w0 + w) ⁻¹' S =
        {w : (ℝ ∙ u)ᗮ | ⟪(w : V), v⟫ = 0} := by
      ext w
      change ⟪((w0 + w : (ℝ ∙ u)ᗮ) : V), v⟫ = t ↔ ⟪(w : V), v⟫ = 0
      change ⟪(w0 : V) + (w : V), v⟫ = t ↔ ⟪(w : V), v⟫ = 0
      rw [inner_add_left, show ⟪(w0 : V), v⟫ = t from hw0]
      simp
    rw [← MeasureTheory.measure_preimage_add μ w0 S, heq]
    exact tangent_inner_zero_null h μ
  · rw [Set.not_nonempty_iff_eq_empty.mp hs]
    exact MeasureTheory.measure_empty

/-- The triple tie locus is surface-null when the first tie hyperplane is
parametrized at any of its points; no triple tie need be specified in advance. -/
theorem triple_tie_surface_null_of_first_tie [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {y0 y1 y2 z : V} {c0 c1 c2 : ℝ}
    (hf : ∃ x, score y1 c1 x < score y0 c0 x ∧ score y2 c2 x < score y0 c0 x)
    (hg : ∃ x, score y0 c0 x < score y1 c1 x ∧ score y2 c2 x < score y1 c1 x)
    (hh : ∃ x, score y0 c0 x < score y2 c2 x ∧ score y1 c1 x < score y2 c2 x)
    (h01 : score y0 c0 z = score y1 c1 z)
    (μ : MeasureTheory.Measure ((ℝ ∙ (y0 - y1))ᗮ)) [μ.IsAddHaarMeasure] :
    μ {w : (ℝ ∙ (y0 - y1))ᗮ |
      score y0 c0 (z + (w : V)) = score y2 c2 (z + (w : V))} = 0 := by
  let S := {w : (ℝ ∙ (y0 - y1))ᗮ |
      score y0 c0 (z + (w : V)) = score y2 c2 (z + (w : V))}
  change μ S = 0
  by_cases hs : S.Nonempty
  · obtain ⟨w0, hw0⟩ := hs
    have horth : ⟪(w0 : V), y0 - y1⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp w0.property
    have h01' : score y0 c0 (z + (w0 : V)) = score y1 c1 (z + (w0 : V)) := by
      unfold score at h01 ⊢
      rw [inner_sub_right] at horth
      simp only [inner_add_left]
      linarith
    have hnonprop := no_proportional_slopes_of_tie hf hg hh h01' hw0
    have heq : S = {w : (ℝ ∙ (y0 - y1))ᗮ |
        ⟪(w : V), y0 - y2⟫ = c2 - c0 - (⟪z, y0⟫ - ⟪z, y2⟫)} := by
      ext w
      simp only [S, Set.mem_ofPred_eq, score, inner_add_left, inner_sub_right]
      constructor <;> intro hw <;> linarith
    rw [heq]
    exact tangent_inner_level_null hnonprop μ _
  · rw [Set.not_nonempty_iff_eq_empty.mp hs]
    exact MeasureTheory.measure_empty

/-- On a fixed interface of a finite strictly-active affine family, almost every
surface point avoids every other tie hyperplane. -/
theorem ae_no_other_ties_on_interface {ι : Type*} [Fintype ι]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (y : ι → V) (c : ι → ℝ)
    (hactive : ∀ i, ∃ x, ∀ j, j ≠ i → score (y j) (c j) x < score (y i) (c i) x)
    {i j : ι} (hij : i ≠ j) {z : V}
    (htie : score (y i) (c i) z = score (y j) (c j) z)
    (μ : MeasureTheory.Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ, ∀ k, k ≠ i → k ≠ j →
      score (y i) (c i) (z + (w : V)) ≠ score (y k) (c k) (z + (w : V)) := by
  apply (MeasureTheory.ae_all_iff).mpr
  intro k
  by_cases hki : k = i
  · subst k
    exact Filter.Eventually.of_forall (fun _ h => (h rfl).elim)
  by_cases hkj : k = j
  · subst k
    exact Filter.Eventually.of_forall (fun _ _ h => (h rfl).elim)
  have hnull : μ {w : (ℝ ∙ (y i - y j))ᗮ |
      score (y i) (c i) (z + (w : V)) = score (y k) (c k) (z + (w : V))} = 0 := by
    apply triple_tie_surface_null_of_first_tie (z := z) (μ := μ) ?_ ?_ ?_ htie
    · obtain ⟨x, hx⟩ := hactive i
      exact ⟨x, hx j hij.symm, hx k hki⟩
    · obtain ⟨x, hx⟩ := hactive j
      exact ⟨x, hx i hij, hx k hkj⟩
    · obtain ⟨x, hx⟩ := hactive k
      exact ⟨x, hx i (Ne.symm hki), hx j (Ne.symm hkj)⟩
  have hae : ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      score (y i) (c i) (z + (w : V)) ≠ score (y k) (c k) (z + (w : V)) := by
    simpa only [MeasureTheory.ae_iff, not_not] using hnull
  exact hae.mono (fun _ hw _ _ => hw)

end Problem358.TripleCell

end

namespace Problem358.GenericSegment

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma affineScore_combination (v p q : V) (c a b : ℝ) (hab : a + b = 1) :
    affineScore v c (a • p + b • q) =
      a * affineScore v c p + b * affineScore v c q := by
  simp only [affineScore, inner_add_right, inner_smul_right]
  linear_combination -c * hab

/-- A nonzero endpoint determinant excludes a simultaneous affine zero on
the entire segment, including its endpoints. -/
theorem segment_avoids_common_zero_of_det_ne_zero
    {v w p q : V} {c d : ℝ}
    (hdet : affineScore v c p * affineScore w d q -
      affineScore w d p * affineScore v c q ≠ 0) :
    ∀ x ∈ segment ℝ p q,
      ¬ (affineScore v c x = 0 ∧ affineScore w d x = 0) := by
  rintro x ⟨a, b, _, _, hab, rfl⟩ ⟨hf, hg⟩
  rw [affineScore_combination v p q c a b hab] at hf
  rw [affineScore_combination w p q d a b hab] at hg
  by_cases hb : b = 0
  · have ha : a = 1 := by linarith
    simp only [ha, hb, one_mul, zero_mul, add_zero] at hf hg
    exact hdet (by simp [hf, hg])
  · have hzero : b * (affineScore v c p * affineScore w d q -
        affineScore w d p * affineScore v c q) = 0 := by
      linear_combination (affineScore v c p) * hg - (affineScore w d p) * hf
    exact hdet ((mul_eq_zero.mp hzero).resolve_left hb)

/-- For independent normals, the endpoint determinant is a nonconstant
affine function of the second endpoint, provided the first endpoint avoids
the first hyperplane. -/
theorem determinant_normal_ne_zero {v w p : V} {c d : ℝ}
    (hvw : LinearIndependent ℝ ![v, w]) (hp : affineScore v c p ≠ 0) :
    affineScore v c p • w - affineScore w d p • v ≠ 0 := by
  intro hzero
  have heq : affineScore w d p • v = affineScore v c p • w :=
    (sub_eq_zero.mp hzero).symm
  exact hp (hvw.eq_zero_of_pair' heq).2

lemma determinant_eq_affine (v w p q : V) (c d : ℝ) :
    affineScore v c p * affineScore w d q -
      affineScore w d p * affineScore v c q =
    inner ℝ (affineScore v c p • w - affineScore w d p • v) q +
      (affineScore v c p * d - affineScore w d p * c) := by
  simp [affineScore, inner_sub_left, inner_smul_left]
  ring

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (μ : Measure V) [IsAddHaarMeasure μ]
include μ

/-- The exceptional second endpoints for a fixed independent pair lie on a
single Haar-null affine hyperplane. -/
theorem ae_endpoint_determinant_ne_zero {v w p : V} {c d : ℝ}
    (hvw : LinearIndependent ℝ ![v, w]) (hp : affineScore v c p ≠ 0) :
    ∀ᵐ q ∂μ, affineScore v c p * affineScore w d q -
      affineScore w d p * affineScore v c q ≠ 0 := by
  rw [ae_iff]
  have hnormal := determinant_normal_ne_zero (d := d) hvw hp
  have hnull := haar_inner_level_null μ hnormal
    (-(affineScore v c p * d - affineScore w d p * c))
  convert hnull using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext q
  simp only [Set.mem_ofPred_eq, not_not, determinant_eq_affine]
  constructor <;> intro h <;> linarith

/-- A generic segment from a fixed endpoint avoids every member of a
countable family of codimension-two affine intersections. -/
theorem ae_segment_avoids_common_zeros {ι : Type*} [Countable ι]
    (v w : ι → V) (c d : ι → ℝ) {p : V}
    (hvw : ∀ i, LinearIndependent ℝ ![v i, w i])
    (hp : ∀ i, affineScore (v i) (c i) p ≠ 0) :
    ∀ᵐ q ∂μ, ∀ i, ∀ x ∈ segment ℝ p q,
      ¬ (affineScore (v i) (c i) x = 0 ∧
        affineScore (w i) (d i) x = 0) := by
  have hdet : ∀ᵐ q ∂μ, ∀ i,
      affineScore (v i) (c i) p * affineScore (w i) (d i) q -
      affineScore (w i) (d i) p * affineScore (v i) (c i) q ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact ae_endpoint_determinant_ne_zero μ (hvw i) (hp i)
  filter_upwards [hdet] with q hq i
  exact segment_avoids_common_zero_of_det_ne_zero (hq i)

/-- In particular one can choose the second endpoint in any prescribed
nonempty open region, as needed when connecting strict cell interiors. -/
theorem exists_endpoint_in_open_avoiding_common_zeros {ι : Type*} [Countable ι]
    (v w : ι → V) (c d : ι → ℝ) {p : V} {U : Set V}
    (hvw : ∀ i, LinearIndependent ℝ ![v i, w i])
    (hp : ∀ i, affineScore (v i) (c i) p ≠ 0)
    (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ i, ∀ x ∈ segment ℝ p q,
      ¬ (affineScore (v i) (c i) x = 0 ∧
        affineScore (w i) (d i) x = 0) := by
  apply Measure.exists_mem_of_measure_ne_zero_of_ae (hU.measure_ne_zero μ hUne)
  exact ae_restrict_of_ae (ae_segment_avoids_common_zeros μ v w c d hvw hp)

end Problem358.GenericSegment

/-! General-position segments for finite strictly active affine families. -/

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Uniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.UniformSource

variable {d : ℕ} {K : Set (E d)}

theorem integrable_norm (hK : IsCompact K) :
    Integrable (fun x : E d => ‖x‖) (uniformMeasure K) :=
  integrable_continuousOn hK continuous_norm.continuousOn

end Problem358.UniformSource

end

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Problem358

/-- Every uniform source is absolutely continuous with respect to ambient volume,
without any measurability, finiteness, or nondegeneracy assumptions on its set. -/
theorem uniformMeasure_absolutelyContinuous {d : ℕ} (K : Set (E d)) :
    uniformMeasure K ≪ volume := by
  exact Measure.smul_absolutelyContinuous.trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- A volume-null exceptional set is null for any uniform source. -/
theorem uniformMeasure_null_of_volume_null {d : ℕ} (K : Set (E d))
    {N : Set (E d)} (hN : volume N = 0) : uniformMeasure K N = 0 :=
  uniformMeasure_absolutelyContinuous K hN

/-- A hyperplane with nonzero normal is a proper affine subspace. -/
theorem innerLevelSubspace_ne_top {d : ℕ} {a : E d} (ha : a ≠ 0) (b : ℝ) :
    innerLevelSubspace a b ≠ ⊤ := by
  intro h
  have hz : (0 : E d) ∈ innerLevelSubspace a b := by rw [h]; trivial
  have haa : a ∈ innerLevelSubspace a b := by rw [h]; trivial
  change inner ℝ a 0 = b at hz
  change inner ℝ a a = b at haa
  apply ha
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simpa only [inner_zero_right] using haa.trans hz.symm

/-- Every nontrivial real scalar-product level set is volume-null. -/
theorem volume_inner_level {d : ℕ} {a : E d} (ha : a ≠ 0) (b : ℝ) :
    volume {x : E d | inner ℝ a x = b} = 0 := by
  exact Measure.addHaar_affineSubspace volume (innerLevelSubspace a b)
    (innerLevelSubspace_ne_top ha b)

/-- Every nontrivial real scalar-product level set is uniform-source-null. -/
theorem uniformMeasure_inner_level {d : ℕ} (K : Set (E d))
    {a : E d} (ha : a ≠ 0) (b : ℝ) :
    uniformMeasure K {x : E d | inner ℝ a x = b} = 0 :=
  uniformMeasure_null_of_volume_null K (volume_inner_level ha b)

/-- The tie set of two affine functions with distinct slopes is null. -/
theorem uniformMeasure_affine_tie {d : ℕ} (K : Set (E d))
    {y z : E d} (hyz : y ≠ z) (c e : ℝ) :
    uniformMeasure K {x : E d | inner ℝ y x + c = inner ℝ z x + e} = 0 := by
  have hsets : {x : E d | inner ℝ y x + c = inner ℝ z x + e} =
      {x : E d | inner ℝ (y - z) x = e - c} := by
    ext x
    simp only [Set.mem_ofPred_eq, inner_sub_left]
    constructor <;> intro hx <;> linarith
  rw [hsets]
  exact uniformMeasure_inner_level K (sub_ne_zero.mpr hyz) (e - c)

/-- Outside a null set, equal values of two affine functions mean equal slopes. -/
theorem ae_affine_eq_imp_slope_eq {d : ℕ} (K : Set (E d))
    (y z : E d) (c e : ℝ) :
    ∀ᵐ x ∂uniformMeasure K, inner ℝ y x + c = inner ℝ z x + e → y = z := by
  by_cases hyz : y = z
  · exact Filter.Eventually.of_forall (fun _ _ => hyz)
  · have hne : ∀ᵐ x ∂uniformMeasure K, inner ℝ y x + c ≠ inner ℝ z x + e := by
      rw [ae_iff]
      simpa only [not_not] using uniformMeasure_affine_tie K hyz c e
    filter_upwards [hne] with x hx h
    exact (hx h).elim

/-- A countable family of affine functions has no ties between distinct slopes
at almost every source point. In particular this applies to finite maxima. -/
theorem ae_all_affine_eq_imp_slope_eq {d : ℕ} {ι : Type*} [Countable ι]
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) :
    ∀ᵐ x ∂uniformMeasure K, ∀ i j,
      inner ℝ (y i) x + c i = inner ℝ (y j) x + c j → y i = y j := by
  simp only [ae_all_iff]
  intro i j
  exact ae_affine_eq_imp_slope_eq K (y i) (y j) (c i) (c j)

/-- Normalization always has total mass at most one, even for degenerate sets. -/
theorem uniformMeasure_univ_le_one {d : ℕ} (K : Set (E d)) :
    uniformMeasure K Set.univ ≤ 1 := by
  simp only [uniformMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_le_one (volume K)

/-- Every normalized restriction is a finite measure, including zero/infinite-volume sets. -/
theorem uniformMeasure_finite {d : ℕ} (K : Set (E d)) :
    IsFiniteMeasure (uniformMeasure K) :=
  ⟨lt_of_le_of_lt (uniformMeasure_univ_le_one K) ENNReal.one_lt_top⟩

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace Problem358
namespace CellGeometry

variable {d : ℕ} {ι : Type*}

theorem closedCell_subset (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) :
    closedCell K y c i ⊆ K := fun _ h => h.1

theorem isClosed_closedCell {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) : IsClosed (closedCell K y c i) := by
  have heq : closedCell K y c i = K ∩ ⋂ j,
      {x | inner ℝ x (y j) + c j ≤ inner ℝ x (y i) + c i} := by
    ext x
    simp [closedCell]
  rw [heq]
  exact hK.inter (isClosed_iInter fun j =>
    isClosed_le ((continuous_id.inner continuous_const).add continuous_const)
      ((continuous_id.inner continuous_const).add continuous_const))

theorem isCompact_closedCell {K : Set (E d)} (hK : IsCompact K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) : IsCompact (closedCell K y c i) :=
  hK.of_isClosed_subset (isClosed_closedCell hK.isClosed y c i)
    (closedCell_subset K y c i)

theorem convex_closedCell {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) : Convex ℝ (closedCell K y c i) := by
  intro x hx z hz a b ha hb hab
  refine ⟨hK hx.1 hz.1 ha hb hab, ?_⟩
  intro j
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  have h1 := mul_le_mul_of_nonneg_left (hx.2 j) ha
  have h2 := mul_le_mul_of_nonneg_left (hz.2 j) hb
  nlinarith [congrArg (fun t : ℝ => t * c i) hab,
    congrArg (fun t : ℝ => t * c j) hab]

theorem exists_mem_closedCell [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (y : ι → E d) (c : ι → ℝ) {x : E d} (hx : x ∈ K) :
    ∃ i, x ∈ closedCell K y c i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j => inner ℝ x (y j) + c j) Finset.univ_nonempty
  exact ⟨i, hx, fun j => hi j (Finset.mem_univ j)⟩

theorem iUnion_closedCell [Fintype ι] [Nonempty ι]
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) :
    (⋃ i, closedCell K y c i) = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hi.1
  · intro hx
    obtain ⟨i, hi⟩ := exists_mem_closedCell y c hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Positive-volume cells have strictly active points in the interior, once affine ties
have been removed as a null set. -/
theorem exists_strict_active_interior {K : Set (E d)}
    (hconv : Convex ℝ K) (y : ι → E d) (c : ι → ℝ) (i : ι)
    (hpos : volume (closedCell K y c i) ≠ 0)
    (hties : ∀ᵐ x ∂volume, ∀ j, j ≠ i →
      inner ℝ x (y j) + c j ≠ inner ℝ x (y i) + c i) :
    ∃ x ∈ interior K, ∀ j, j ≠ i →
      inner ℝ x (y j) + c j < inner ℝ x (y i) + c i := by
  have hboundary : ∀ᵐ x ∂(volume : Measure (E d)), x ∉ frontier K := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hconv.addHaar_frontier volume
  have hgood : ∀ᵐ x ∂volume.restrict (closedCell K y c i),
      x ∉ frontier K ∧ ∀ j, j ≠ i →
        inner ℝ x (y j) + c j ≠ inner ℝ x (y i) + c i :=
    ae_restrict_of_ae (hboundary.and hties)
  obtain ⟨x, hx, hxb, hxt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos hgood
  refine ⟨x, ?_, fun j hj => lt_of_le_of_ne (hx.2 j) (hxt j hj)⟩
  by_contra hn
  exact hxb ⟨subset_closure hx.1, hn⟩

/-- Convex interpolation of the intercepts and source points remains in the same cell. -/
theorem combo_mem_closedCell {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c e : ι → ℝ) (i : ι) {x z : E d}
    (hx : x ∈ closedCell K y c i) (hz : z ∈ closedCell K y e i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • z ∈ closedCell K y (fun j => a * c j + b * e j) i := by
  refine ⟨hK hx.1 hz.1 ha hb hab, ?_⟩
  intro j
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  have h1 := mul_le_mul_of_nonneg_left (hx.2 j) ha
  have h2 := mul_le_mul_of_nonneg_left (hz.2 j) hb
  nlinarith

/-- The opposite-intercept midpoint inclusion used in the moment estimate. -/
theorem midpoint_mem_closedCell {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c q : ι → ℝ) (i : ι) (s : ℝ) {x z : E d}
    (hx : x ∈ closedCell K y (fun j => c j - s * q j) i)
    (hz : z ∈ closedCell K y (fun j => c j + s * q j) i) :
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z ∈ closedCell K y c i := by
  have h := combo_mem_closedCell hK y _ _ i hx hz
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have heq : (fun j => (1 / 2 : ℝ) * (c j - s * q j) +
      (1 / 2 : ℝ) * (c j + s * q j)) = c := by
    funext j
    ring
  rwa [heq] at h

/-- An affine equality plane separating two strictly active interior points meets
 the interior of the convex source. -/
theorem exists_affine_equality_interior {K : Set (E d)} (hK : Convex ℝ K)
    {y z : E d} {c e : ℝ} {p q : E d}
    (hp : p ∈ interior K) (hq : q ∈ interior K)
    (hp_lt : inner ℝ p y + c < inner ℝ p z + e)
    (hq_lt : inner ℝ q z + e < inner ℝ q y + c) :
    ∃ x ∈ interior K, inner ℝ x y + c = inner ℝ x z + e := by
  let f : E d → ℝ := fun x => (inner ℝ x y + c) - (inner ℝ x z + e)
  have hf : Continuous f :=
    ((continuous_id.inner continuous_const).add continuous_const).sub
      ((continuous_id.inner continuous_const).add continuous_const)
  have hzero : (0 : ℝ) ∈ Set.Icc (f p) (f q) := by
    constructor <;> dsimp [f] <;> linarith
  obtain ⟨x, hx, heq⟩ := hK.interior.isPreconnected.intermediate_value
    hp hq hf.continuousOn hzero
  exact ⟨x, hx, sub_eq_zero.mp heq⟩

end CellGeometry
end Problem358

end

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace Problem358
namespace CellGeometry

variable {d : ℕ} {ι : Type*}

/-- Distinct-site closed cells overlap only along null affine tie planes. -/
theorem pairwise_aedisjoint_closedCell {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) :
    Pairwise (fun i j => AEDisjoint ρ (closedCell K y c i) (closedCell K y c j)) := by
  intro i j hij
  change ρ (closedCell K y c i ∩ closedCell K y c j) = 0
  apply hρ
  apply measure_mono_null (t := {x | inner ℝ x (y i) + c i = inner ℝ x (y j) + c j})
  · intro x hx
    exact le_antisymm (hx.2.2 i) (hx.1.2 j)
  · exact haar_affine_tie_null volume (hy.ne hij) (c i) (c j)

/-- Integrable functions can be summed cellwise despite the shared boundary faces. -/
theorem sum_integral_closedCell [Fintype ι] [Nonempty ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume) {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    {f : E d → V} (hf : IntegrableOn f K ρ) :
    (∑ i, ∫ x in closedCell K y c i, f x ∂ρ) = ∫ x in K, f x ∂ρ := by
  have hi : IntegrableOn f (⋃ i, closedCell K y c i) ρ := by
    simpa only [iUnion_closedCell] using hf
  have h := integral_iUnion_ae
    (fun i => (isClosed_closedCell hK y c i).measurableSet.nullMeasurableSet)
    (pairwise_aedisjoint_closedCell hρ K y c hy) hi
  simpa only [iUnion_closedCell, tsum_fintype] using h.symm

/-- Real-valued cell masses also add to the total source mass. -/
theorem sum_real_measure_closedCell [Fintype ι] [Nonempty ι]
    {ρ : Measure (E d)} [IsFiniteMeasure ρ] (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) :
    (∑ i, ρ.real (closedCell K y c i)) = ρ.real K := by
  have h := sum_integral_closedCell hρ hK y c hy
    (f := fun _ => (1 : ℝ)) (integrable_const 1)
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one] using h

/-- Injective sites discharge the null-tie premise in strict activation. -/
theorem exists_strict_active_interior_of_injective [Countable ι]
    {K : Set (E d)} (hK : Convex ℝ K) (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (i : ι) (hpos : volume (closedCell K y c i) ≠ 0) :
    ∃ x ∈ interior K, ∀ j, j ≠ i →
      inner ℝ x (y j) + c j < inner ℝ x (y i) + c i := by
  apply exists_strict_active_interior hK y c i hpos
  filter_upwards [ae_affine_tie_implies_slopes_eq volume y c] with x hx
  intro j hji heq
  exact hji (hy (hx j i heq))

/-- Positive cell mass for an absolutely continuous source already guarantees a
strictly active interior point. -/
theorem exists_strict_active_interior_of_mass [Countable ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume) {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (i : ι) (hpos : ρ (closedCell K y c i) ≠ 0) :
    ∃ x ∈ interior K, ∀ j, j ≠ i →
      inner ℝ x (y j) + c j < inner ℝ x (y i) + c i := by
  apply exists_strict_active_interior_of_injective hK y c hy i
  exact fun hnull => hpos (hρ hnull)

/-- Every equality plane between positive-mass cells cuts the interior of the source. -/
theorem exists_equality_interior_of_positive_cells [Countable ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume) {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    {i j : ι} (hij : i ≠ j)
    (hi : ρ (closedCell K y c i) ≠ 0) (hj : ρ (closedCell K y c j) ≠ 0) :
    ∃ x ∈ interior K, inner ℝ x (y i) + c i = inner ℝ x (y j) + c j := by
  obtain ⟨p, hp, hpi⟩ := exists_strict_active_interior_of_mass hρ hK y c hy i hi
  obtain ⟨q, hq, hqj⟩ := exists_strict_active_interior_of_mass hρ hK y c hy j hj
  exact exists_affine_equality_interior hK hq hp (hqj i hij) (hpi j hij.symm)

end CellGeometry
end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace Problem358

theorem measurableSet_scoreCell {d : ℕ} {ι : Type*} [Countable ι]
    (y : ι → E d) (c : ι → ℝ) (i : ι) : MeasurableSet (scoreCell y c i) := by
  simp only [scoreCell, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (by fun_prop) (by fun_prop)

/-- A strict limiting comparison has an eventually constant truth value. -/
theorem eventually_le_iff_of_tendsto_ne {β : Type*} {l : Filter β}
    {f g : β → ℝ} {a b : ℝ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hab : a ≠ b) :
    ∀ᶠ n in l, f n ≤ g n ↔ a ≤ b := by
  rcases lt_or_gt_of_ne hab with h | h
  · filter_upwards [hf.eventually_lt hg h] with n hn
    simp only [le_of_lt hn, le_of_lt h]
  · filter_upwards [hg.eventually_lt hf h] with n hn
    simp only [not_le_of_gt hn, not_le_of_gt h]

/-- Away from limiting ties, membership in a finite affine cell stabilizes. -/
theorem eventually_mem_scoreCell_iff {d : ℕ} {ι β : Type*} [Finite ι]
    {l : Filter β} {ys : β → ι → E d} {cs : β → ι → ℝ}
    {y : ι → E d} {c : ι → ℝ} (i : ι) (x : E d)
    (hy : ∀ j, Tendsto (fun n => ys n j) l (𝓝 (y j)))
    (hc : ∀ j, Tendsto (fun n => cs n j) l (𝓝 (c j)))
    (htie : ∀ j, j ≠ i → inner ℝ (y j) x + c j ≠ inner ℝ (y i) x + c i) :
    ∀ᶠ n in l, x ∈ scoreCell (ys n) (cs n) i ↔ x ∈ scoreCell y c i := by
  have hcomp : ∀ j, ∀ᶠ n in l,
      (inner ℝ (ys n j) x + cs n j ≤ inner ℝ (ys n i) x + cs n i) ↔
        inner ℝ (y j) x + c j ≤ inner ℝ (y i) x + c i := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · exact eventually_le_iff_of_tendsto_ne
        (((hy j).inner tendsto_const_nhds).add (hc j))
        (((hy i).inner tendsto_const_nhds).add (hc i)) (htie j hji)
  filter_upwards [Filter.eventually_all.mpr hcomp] with n hn
  exact forall_congr' hn

/-- Distinct limiting slopes make affine-cell membership stabilize almost everywhere. -/
theorem ae_eventually_mem_scoreCell_iff {d : ℕ} {ι β : Type*} [Finite ι]
    (K : Set (E d)) {l : Filter β} {ys : β → ι → E d} {cs : β → ι → ℝ}
    {y : ι → E d} {c : ι → ℝ} (i : ι) (hinj : Function.Injective y)
    (hy : ∀ j, Tendsto (fun n => ys n j) l (𝓝 (y j)))
    (hc : ∀ j, Tendsto (fun n => cs n j) l (𝓝 (c j))) :
    ∀ᵐ x ∂uniformMeasure K, ∀ᶠ n in l,
      x ∈ scoreCell (ys n) (cs n) i ↔ x ∈ scoreCell y c i := by
  filter_upwards [ae_all_affine_eq_imp_slope_eq K y c] with x hx
  apply eventually_mem_scoreCell_iff i x hy hc
  intro j hji heq
  exact hji (hinj (hx j i heq))

/-- Cell masses converge under convergence of sites and intercepts, provided only
that the limiting sites are distinct and the uniform source is finite. -/
theorem tendsto_uniformMeasure_scoreCell {d : ℕ} {ι β : Type*} [Finite ι]
    (K : Set (E d))
    {l : Filter β} [l.IsCountablyGenerated]
    {ys : β → ι → E d} {cs : β → ι → ℝ} {y : ι → E d} {c : ι → ℝ}
    (i : ι) (hinj : Function.Injective y)
    (hy : ∀ j, Tendsto (fun n => ys n j) l (𝓝 (y j)))
    (hc : ∀ j, Tendsto (fun n => cs n j) l (𝓝 (c j))) :
    Tendsto (fun n => uniformMeasure K (scoreCell (ys n) (cs n) i)) l
      (𝓝 (uniformMeasure K (scoreCell y c i))) := by
  let := uniformMeasure_finite K
  exact tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure l
    (measurableSet_scoreCell y c i) (fun n => measurableSet_scoreCell (ys n) (cs n) i)
    (ae_eventually_mem_scoreCell_iff K i hinj hy hc)

/-- Joint continuity in all affine coefficients at configurations with distinct sites. -/
theorem continuousAt_uniformMeasure_scoreCell {d : ℕ} {ι : Type*} [Finite ι]
    (K : Set (E d))
    (y : ι → E d) (c : ι → ℝ) (i : ι) (hinj : Function.Injective y) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      uniformMeasure K (scoreCell p.1 p.2 i)) (y, c) := by
  apply tendsto_uniformMeasure_scoreCell K i hinj
  · intro j
    exact ((continuous_apply j).comp continuous_fst).continuousAt
  · intro j
    exact ((continuous_apply j).comp continuous_snd).continuousAt

/-- Distinctness of a finite family of sites persists locally. -/
theorem eventually_injective_sites {d : ℕ} {ι : Type*} [Finite ι]
    (y : ι → E d) (c : ι → ℝ) (hinj : Function.Injective y) :
    ∀ᶠ p : (ι → E d) × (ι → ℝ) in 𝓝 (y, c), Function.Injective p.1 := by
  have hp : ∀ i j, ∀ᶠ p : (ι → E d) × (ι → ℝ) in 𝓝 (y, c),
      i ≠ j → p.1 i ≠ p.1 j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hopen : IsOpen {p : (ι → E d) × (ι → ℝ) | p.1 i ≠ p.1 j} :=
        isOpen_ne_fun (by fun_prop) (by fun_prop)
      filter_upwards [hopen.mem_nhds (hinj.ne hij)] with p hp
      exact fun _ => hp
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hp i))]
    with p hp
  intro i j hij
  by_contra hne
  exact hp i j hne hij

end Problem358

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- The geometric closed cell is the score cell restricted to the source body. -/
theorem closedCell_eq_inter_scoreCell
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) :
    closedCell K y c i = K ∩ scoreCell y c i := by
  ext x
  simp only [closedCell, scoreCell, mem_ofPred_eq, mem_inter_iff]
  simp only [real_inner_comm x]

/-- The two cell conventions agree almost everywhere for the uniform source. -/
theorem closedCell_ae_eq_scoreCell {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) :
    closedCell K y c i =ᵐ[uniformMeasure K] scoreCell y c i := by
  filter_upwards [UniformSource.ae_mem hK] with x hx
  apply propext
  simp only [closedCell_eq_inter_scoreCell, mem_inter_iff, hx, true_and]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- Closed-cell masses are exactly the score-cell masses. -/
theorem uniformMeasure_closedCell_eq_scoreCell {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) :
    uniformMeasure K (closedCell K y c i) = uniformMeasure K (scoreCell y c i) :=
  measure_congr (closedCell_ae_eq_scoreCell hK y c i)

/-- Joint continuity of the actual geometric closed-cell mass at distinct sites. -/
theorem continuousAt_uniformMeasure_closedCell [Finite ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) (hinj : Function.Injective y) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      uniformMeasure K (closedCell K p.1 p.2 i)) (y, c) := by
  simpa only [uniformMeasure_closedCell_eq_scoreCell hK] using
    continuousAt_uniformMeasure_scoreCell K y c i hinj

/-- Real-valued closed-cell masses are jointly continuous at distinct sites. -/
theorem continuousAt_real_closedCell [Finite ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) (hinj : Function.Injective y) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      (uniformMeasure K).real (closedCell K p.1 p.2 i)) (y, c) := by
  let := uniformMeasure_finite K
  change ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
    (uniformMeasure K (closedCell K p.1 p.2 i)).toReal) (y, c)
  exact (ENNReal.tendsto_toReal
    (measure_ne_top (uniformMeasure K) (closedCell K y c i))).comp
    (continuousAt_uniformMeasure_closedCell hK y c i hinj)

/-- The admissible locus used by geometric cell calculus is open, in the real-mass
convention of the normalized implicit-function construction. -/
theorem isOpen_distinct_positive_real_closedCell [Finite ι]
    {K : Set (E d)} (hK : MeasurableSet K) :
    IsOpen {p : (ι → E d) × (ι → ℝ) |
      Function.Injective p.1 ∧ ∀ i, 0 < (uniformMeasure K).real (closedCell K p.1 p.2 i)} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨y, c⟩ ⟨hinj, hpos⟩
  have hp : ∀ i, ∀ᶠ p : (ι → E d) × (ι → ℝ) in 𝓝 (y, c),
      0 < (uniformMeasure K).real (closedCell K p.1 p.2 i) := by
    intro i
    exact (continuousAt_real_closedCell hK y c i hinj).eventually
      (lt_mem_nhds (hpos i))
  filter_upwards [_root_.OAI.Problem358.eventually_injective_sites y c hinj, Filter.eventually_all.mpr hp]
    with p hi hm
  exact ⟨hi, hm⟩

end Problem358.CellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.NormalizedCell

variable {X : Type*} [MeasurableSpace X]

variable {ρ : Measure X} {P : Set X}

/-- Normalizing a cell removes any positive finite scalar prefactor in the source. -/
theorem measure_smul (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    measure (c • ρ) P = measure ρ P := by
  unfold measure
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_smul, smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), mul_right_comm,
    ENNReal.inv_mul_cancel hc0 hctop, one_mul]

/-- Restricting the source to a larger set does not change the normalized cell law. -/
theorem measure_restrict {K : Set X} (hP : MeasurableSet P) (hPK : P ⊆ K) :
    measure (ρ.restrict K) P = measure ρ P := by
  unfold measure
  rw [Measure.restrict_apply hP, Set.inter_eq_left.mpr hPK,
    Measure.restrict_restrict_of_subset hPK]

end Problem358.NormalizedCell

namespace Problem358

/-- The normalized restriction of a uniform source to a cell is exactly the
uniform law of that cell; this identifies the laws used by midpoint couplings. -/
theorem normalizedCell_uniformMeasure {d : ℕ} {K P : Set (E d)}
    (hKpos : 0 < volume K) (hKfinite : volume K ≠ ∞)
    (hP : MeasurableSet P) (hPK : P ⊆ K) :
    NormalizedCell.measure (uniformMeasure K) P = uniformMeasure P := by
  rw [uniformMeasure, NormalizedCell.measure_smul _
    (ENNReal.inv_ne_zero.mpr hKfinite) (ENNReal.inv_ne_top.mpr hKpos.ne'),
    NormalizedCell.measure_restrict hP hPK]
  rfl

/-- Cell mass for a uniform source is the ratio of cell and source volume. -/
theorem uniformMeasure_real_cell {d : ℕ} {K P : Set (E d)}
    (hP : MeasurableSet P) (hPK : P ⊆ K) :
    (uniformMeasure K).real P = (volume P).toReal / (volume K).toReal := by
  unfold Measure.real uniformMeasure
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hP,
    Set.inter_eq_left.mpr hPK, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- A closed-cell mass is the normalized scalar volume integral used by the
moving-cut calculus. No positivity or distinct-site hypothesis is needed. -/
theorem uniformMass_eq_normalized_integral_one
    {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) :
    (uniformMeasure K).real (closedCell K y c i) =
      (volume K).toReal⁻¹ * ∫ _x in closedCell K y c i, (1 : ℝ) := by
  rw [uniformMeasure_real_cell (isClosed_closedCell hK y c i).measurableSet
    (closedCell_subset K y c i)]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one]
  ring

/-- A scalar moving-volume derivative immediately gives the actual normalized
real cell-mass derivative. -/
theorem hasDerivAt_uniformMass_of_integral_one
    {K : Set (E d)} (hK : IsClosed K)
    (y : ℝ → ι → E d) (c : ℝ → ι → ℝ) (i : ι) {t D : ℝ}
    (hD : HasDerivAt (fun s => ∫ _x in closedCell K (y s) (c s) i, (1 : ℝ)) D t) :
    HasDerivAt (fun s => (uniformMeasure K).real (closedCell K (y s) (c s) i))
      ((volume K).toReal⁻¹ * D) t := by
  have h := hD.const_mul (volume K).toReal⁻¹
  simpa only [uniformMass_eq_normalized_integral_one hK] using h

end Problem358.CellGeometry

end

/-! Coordinate assembly and source normalization for genuine vector cell moments.
The scalar moving-cell calculus is an explicit input; no differentiability of a
cell or of its coefficients is assumed implicitly. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Problem358.CellVectorDerivative

variable {d : ℕ}

/-- A coordinate of a Bochner integral in the problem's Euclidean space. -/
theorem integral_coordinate {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → E d} (hf : Integrable f μ) (k : Fin d) :
    (∫ x, f x ∂μ) k = ∫ x, f x k ∂μ :=
  eval_integral_piLp (fun k => hf.eval_piLp k) k

/-- Assemble scalar coordinate derivatives in the Euclidean, rather than sup, norm. -/
theorem hasDerivAt_of_coordinates {f : ℝ → E d} {b : E d} {t : ℝ}
    (h : ∀ k : Fin d, HasDerivAt (fun s => f s k) (b k) t) :
    HasDerivAt f b t := by
  have hp : HasDerivAt (fun s k => f s k) (fun k => b k) t := hasDerivAt_pi.mpr h
  have hh := (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t hp
  convert hh using 1 <;> first | rfl | simp [Function.comp_def]

/-- Restriction to a subset of the source removes the extra source indicator.
This identity is valid even in the zero-volume degenerate case. -/
theorem setIntegral_uniformMeasure {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {K P : Set (E d)} (hPK : P ⊆ K) (f : E d → V) :
    (∫ x in P, f x ∂uniformMeasure K) =
      (volume K).toReal⁻¹ • ∫ x in P, f x ∂volume := by
  rw [uniformMeasure, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset hPK, integral_smul_measure, ENNReal.toReal_inv]

/-- Scalar volume derivatives of the coordinate weights give the actual
uniform-source vector-moment derivative, with the source normalization explicit. -/
theorem hasDerivAt_uniform_cellMoment_of_coordinates
    {ι : Type*} {K : Set (E d)} (hK : IsCompact K)
    (y : ℝ → ι → E d) (c : ℝ → ι → ℝ) (i : ι) {t : ℝ} {b : E d}
    (h : ∀ k : Fin d, HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K (y s) (c s) i, x k ∂volume)
      (b k) t) :
    HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K (y s) (c s) i, x ∂uniformMeasure K)
      ((volume K).toReal⁻¹ • b) t := by
  have hi (s : ℝ) : IntegrableOn (fun x : E d => x)
      (CellGeometry.closedCell K (y s) (c s) i) volume :=
    ContinuousOn.integrableOn_compact
      (CellGeometry.isCompact_closedCell hK (y s) (c s) i) continuousOn_id
  have hv : HasDerivAt
      (fun s => ∫ x in CellGeometry.closedCell K (y s) (c s) i, x ∂volume) b t := by
    apply hasDerivAt_of_coordinates
    intro k
    simpa only [integral_coordinate (hi _) k] using h k
  have hn := hv.const_smul (volume K).toReal⁻¹
  apply hn.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s =>
    setIntegral_uniformMeasure (CellGeometry.closedCell_subset K (y s) (c s) i) id

end Problem358.CellVectorDerivative

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_HalfspaceKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem358

/-- Joint measurability is preserved by integrating between measurable endpoints. -/
theorem stronglyMeasurable_intervalIntegral_endpoints
    {X : Type*} [MeasurableSpace X] {f : X → ℝ → ℝ} {a b : X → ℝ}
    (hf : Measurable (Function.uncurry f)) (ha : Measurable a) (hb : Measurable b) :
    StronglyMeasurable (fun x => ∫ t in a x..b x, f x t) := by
  let S : Set (X × ℝ) := {p | a p.1 < p.2 ∧ p.2 ≤ b p.1}
  let T : Set (X × ℝ) := {p | b p.1 < p.2 ∧ p.2 ≤ a p.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hb.comp measurable_fst))
  have hT : MeasurableSet T :=
    (measurableSet_lt (hb.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (ha.comp measurable_fst))
  have hleft : StronglyMeasurable (fun x => ∫ t : ℝ,
      S.indicator (Function.uncurry f) (x, t)) :=
    StronglyMeasurable.integral_prod_right (f := fun x t =>
      S.indicator (Function.uncurry f) (x, t)) (by
        convert (hf.indicator hS).stronglyMeasurable using 1
        all_goals try with_reducible_and_instances rfl
        funext p
        rcases p with ⟨x, t⟩
        rfl)
  have hright : StronglyMeasurable (fun x => ∫ t : ℝ,
      T.indicator (Function.uncurry f) (x, t)) :=
    StronglyMeasurable.integral_prod_right (f := fun x t =>
      T.indicator (Function.uncurry f) (x, t)) (by
        convert (hf.indicator hT).stronglyMeasurable using 1
        all_goals try with_reducible_and_instances rfl
        funext p
        rcases p with ⟨x, t⟩
        rfl)
  convert hleft.sub hright using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  change (∫ t in a x..b x, f x t) =
    (∫ t, (Set.Ioc (a x) (b x)).indicator (f x) t) -
      (∫ t, (Set.Ioc (b x) (a x)).indicator (f x) t)
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rfl

/-- A moving-boundary derivative remains valid for a changing integrand. The
scaled pointwise limit is exactly what remains after removing the principal
moving halfspace in a telescoping product of cell indicators. -/
theorem hasDerivAt_integral_moving_boundary_varying
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℝ → ℝ} {b B : X → ℝ} {trace : X → ℝ}
    (hf : ∀ h, Measurable (Function.uncurry (f h))) (hb : Measurable b)
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (h * u)) (nhds 0) (nhds (trace x)))
    (hbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => |b x| * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t in (0 : ℝ)..h * b x, f h x t) ∂μ)
      (∫ x, b x * trace x ∂μ) 0 := by
  let G : ℝ → X → ℝ := fun h x => ∫ u in (0 : ℝ)..b x, f h x (h * u)
  have hGmeas : ∀ h, StronglyMeasurable (G h) := by
    intro h
    apply stronglyMeasurable_intervalIntegral_endpoints _ measurable_const hb
    exact (hf h).comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hGbound : ∀ h, ∀ᵐ x ∂μ, ‖G h x‖ ≤ |b x| * B x := by
    intro h
    filter_upwards [hbound] with x hx
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := b x) (fun u _ => hx h (h * u))
    simpa [G, mul_comm] using hi
  have hGlim : ∀ᵐ x ∂μ, Tendsto (fun h => G h x) (nhds 0)
      (nhds (b x * trace x)) := by
    filter_upwards [hlim, hbound] with x hx hxbound
    have hi := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := (0 : ℝ)) (b := b x) (μ := volume) (l := nhds (0 : ℝ))
      (F := fun h u => f h x (h * u)) (f := fun _ => trace x)
      (fun _ => B x)
      (Eventually.of_forall fun h =>
        ((hf h).comp (measurable_const.prodMk
          (measurable_const.mul measurable_id))).aestronglyMeasurable)
      (Eventually.of_forall fun h => Eventually.of_forall fun u _ => hxbound h (h * u))
      intervalIntegrable_const
      (Eventually.of_forall fun u _ => hx u)
    simpa [G] using hi
  have hHlim : Tendsto (fun h => ∫ x, G h x ∂μ) (nhds 0)
      (nhds (∫ x, b x * trace x ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence (fun x => |b x| * B x)
      (Eventually.of_forall fun h => (hGmeas h).aestronglyMeasurable)
      (Eventually.of_forall hGbound) hdom hGlim
  have hscale : ∀ h : ℝ,
      (∫ x, (∫ t in (0 : ℝ)..h * b x, f h x t) ∂μ) =
        h * ∫ x, G h x ∂μ := by
    intro h
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simpa only [G, smul_eq_mul, mul_zero] using
        (intervalIntegral.smul_integral_comp_mul_left (f h x) (a := (0 : ℝ))
          (b := b x) h).symm
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply (hHlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa using hh
  simp [hscale, hh0, smul_eq_mul]

/-- A varying boundary velocity is allowed as well. In moving-plane coordinates,
this covers the denominator introduced when the normal direction is perturbed. -/
theorem hasDerivAt_integral_moving_boundary_varying_speed
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℝ → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    (hf : ∀ h, Measurable (Function.uncurry (f h)))
    (hspeed : ∀ h, Measurable (speed h))
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (h * speed h x * u)) (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h : ℝ, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t in (0 : ℝ)..h * speed h x, f h x t) ∂μ)
      (∫ x, slope x * trace x ∂μ) 0 := by
  let G : ℝ → X → ℝ → ℝ := fun h x t => speed h x * f h x (speed h x * t)
  have hGmeas : ∀ h, Measurable (Function.uncurry (G h)) := by
    intro h
    exact ((hspeed h).comp measurable_fst).mul
      ((hf h).comp (measurable_fst.prodMk
        (((hspeed h).comp measurable_fst).mul measurable_snd)))
  have hGlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => G h x (h * u)) (nhds 0)
        (nhds (slope x * trace x)) := by
    filter_upwards [hspeedlim, hlim] with x hx hy
    intro u
    simpa [G, mul_assoc, mul_comm, mul_left_comm] using hx.mul (hy u)
  have hGbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖G h x t‖ ≤ A x * B x := by
    filter_upwards [hspeedbound, hbound] with x hx hy
    intro h t
    have hB : 0 ≤ B x := (norm_nonneg _).trans (hy 0 0)
    calc
      ‖G h x t‖ = |speed h x| * ‖f h x (speed h x * t)‖ := by
        simp [G, norm_mul, Real.norm_eq_abs]
      _ ≤ A x * B x := mul_le_mul (hx h) (hy h (speed h x * t))
        (norm_nonneg _) ((abs_nonneg _).trans (hx h))
  have hg := hasDerivAt_integral_moving_boundary_varying
    (f := G) (b := fun _ => (1 : ℝ)) (B := fun x => A x * B x)
    hGmeas measurable_const hGlim hGbound (by simpa using hdom)
  simp only [mul_one, one_mul] at hg
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∫ t in (0 : ℝ)..h * speed h x, f h x t) =
      (∫ t in (0 : ℝ)..h, G h x t)
    rw [show (∫ t in (0 : ℝ)..h, G h x t) =
      speed h x * ∫ t in (0 : ℝ)..h, f h x (speed h x * t) by
        exact intervalIntegral.integral_const_mul _ _]
    simpa only [smul_eq_mul, mul_zero, mul_comm] using
      (intervalIntegral.smul_integral_comp_mul_left (f h x)
        (a := (0 : ℝ)) (b := h) (speed h x)).symm

end Problem358

namespace Problem358

/-- The signed change of a threshold halfline is exactly its boundary strip. -/
theorem integral_threshold_difference (f : ℝ → ℝ) (c : ℝ) :
    (∫ t : ℝ, f t * ((if c ≤ t then (1 : ℝ) else 0) -
      (if 0 ≤ t then (1 : ℝ) else 0))) = ∫ t in c..0, f t := by
  classical
  by_cases hc : c ≤ 0
  · have hid : (fun t : ℝ => f t * ((if c ≤ t then (1 : ℝ) else 0) -
        (if 0 ≤ t then (1 : ℝ) else 0))) = (Set.Ico c 0).indicator f := by
      funext t
      simp only [Set.indicator, Set.mem_Ico]
      split_ifs <;> simp_all <;> linarith
    rw [hid, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      intervalIntegral.integral_of_le hc]
  · have hc' : 0 ≤ c := le_of_lt (lt_of_not_ge hc)
    have hid : (fun t : ℝ => f t * ((if c ≤ t then (1 : ℝ) else 0) -
        (if 0 ≤ t then (1 : ℝ) else 0))) =
        fun t => -((Set.Ico 0 c).indicator f t) := by
      funext t
      simp only [Set.indicator, Set.mem_Ico]
      split_ifs <;> simp_all <;> linarith
    rw [hid, integral_neg, integral_indicator measurableSet_Ico,
      integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_ge hc']

/-- The derivative of one varying halfspace factor, with all other varying
factors included in `f`. This is stated as an iterated integral so that an
orthogonal-coordinate/Fubini argument can apply it directly. -/
theorem hasDerivAt_integral_halfspace_difference
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℝ → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    (hf : ∀ h, Measurable (Function.uncurry (f h)))
    (hspeed : ∀ h, Measurable (speed h))
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (-(h * speed h x * u))) (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h : ℝ, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t : ℝ,
      f h x t * ((if -(h * speed h x) ≤ t then (1 : ℝ) else 0) -
        (if 0 ≤ t then (1 : ℝ) else 0))) ∂μ)
      (∫ x, slope x * trace x ∂μ) 0 := by
  have hg := hasDerivAt_integral_moving_boundary_varying_speed
    (f := fun h x t => f h x (-t)) (speed := speed)
    (A := A) (B := B) (slope := slope) (trace := trace)
    (fun h => (hf h).comp (measurable_fst.prodMk measurable_snd.neg))
    hspeed hspeedlim hlim hspeedbound
    (hbound.mono fun x hx h t => hx h (-t)) hdom
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [integral_threshold_difference, intervalIntegral.integral_comp_neg]
    simp

/-- Local-in-parameter version of the halfspace derivative. In particular,
velocity denominators need only stay away from zero near the base configuration. -/
theorem hasDerivAt_integral_halfspace_difference_local
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℝ → X → ℝ → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    {s : Set ℝ} (hs : s ∈ nhds 0)
    (hf : ∀ h, Measurable (Function.uncurry (f h)))
    (hspeed : ∀ h, Measurable (speed h))
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (-(h * speed h x * u))) (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h ∈ s, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h ∈ s, ∀ t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ) :
    HasDerivAt (fun h : ℝ => ∫ x, (∫ t : ℝ,
      f h x t * ((if -(h * speed h x) ≤ t then (1 : ℝ) else 0) -
        (if 0 ≤ t then (1 : ℝ) else 0))) ∂μ)
      (∫ x, slope x * trace x ∂μ) 0 := by
  classical
  let ff : ℝ → X → ℝ → ℝ := fun h x t => if h ∈ s then f h x t else 0
  let vv : ℝ → X → ℝ := fun h x => if h ∈ s then speed h x else 0
  have hzero : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  have hff : ∀ h, Measurable (Function.uncurry (ff h)) := by
    intro h
    by_cases hh : h ∈ s
    · simpa [ff, hh, Function.uncurry] using hf h
    · convert (measurable_const : Measurable (fun _ : X × ℝ => (0 : ℝ))) using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      rcases p with ⟨x, t⟩
      simp [ff, hh]
  have hvv : ∀ h, Measurable (vv h) := by
    intro h
    by_cases hh : h ∈ s
    · simpa [vv, hh] using hspeed h
    · simp [vv, hh]
  have hvlim : ∀ᵐ x ∂μ, Tendsto (fun h => vv h x) (nhds 0) (nhds (slope x)) := by
    filter_upwards [hspeedlim] with x hx
    apply hx.congr'
    filter_upwards [hs] with h hh
    simp [vv, hh]
  have hflim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => ff h x (-(h * vv h x * u))) (nhds 0) (nhds (trace x)) := by
    filter_upwards [hlim] with x hx
    intro u
    apply (hx u).congr'
    filter_upwards [hs] with h hh
    simp [ff, vv, hh]
  have hvbound : ∀ᵐ x ∂μ, ∀ h : ℝ, |vv h x| ≤ A x := by
    filter_upwards [hspeedbound] with x hx
    have hA : 0 ≤ A x := (abs_nonneg _).trans (hx 0 hzero)
    intro h
    by_cases hh : h ∈ s
    · simpa [vv, hh] using hx h hh
    · simpa [vv, hh] using hA
  have hfbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖ff h x t‖ ≤ B x := by
    filter_upwards [hbound] with x hx
    have hB : 0 ≤ B x := (norm_nonneg _).trans (hx 0 hzero 0)
    intro h t
    by_cases hh : h ∈ s
    · simpa [ff, hh] using hx h hh t
    · simpa [ff, hh] using hB
  have hd := hasDerivAt_integral_halfspace_difference hff hvv hvlim hflim hvbound hfbound hdom
  apply hd.congr_of_eventuallyEq
  filter_upwards [hs] with h hh
  simp [ff, vv, hh]

/-- Multiplication by the signed difference of two threshold indicators
preserves ambient integrability. -/
theorem integrable_threshold_difference
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X × ℝ → ℝ} {c : X → ℝ}
    (hf : Integrable f (μ.prod volume)) (hc : Measurable c) :
    Integrable (fun p : X × ℝ => f p *
      ((if c p.1 ≤ p.2 then (1 : ℝ) else 0) -
        (if 0 ≤ p.2 then (1 : ℝ) else 0))) (μ.prod volume) := by
  have hfirst : Measurable (fun p : X × ℝ =>
      if c p.1 ≤ p.2 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (hc.comp measurable_fst) measurable_snd)
      measurable_const measurable_const
  have hsecond : Measurable (fun p : X × ℝ =>
      if 0 ≤ p.2 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const measurable_snd)
      measurable_const measurable_const
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul
    (hfirst.sub hsecond).aestronglyMeasurable)
  exact Eventually.of_forall fun p => by
    have hcut : ‖(if c p.1 ≤ p.2 then (1 : ℝ) else 0) -
        (if 0 ≤ p.2 then (1 : ℝ) else 0)‖ ≤ 1 := by
      split_ifs <;> norm_num
    simp only [Pi.mul_apply, Pi.sub_apply]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hcut (norm_nonneg _)).trans_eq (mul_one _)

/-- Product-measure version of the local moving-face derivative. Ambient
integrability is enough to discharge the Fubini step, while slice domination
controls the derivative independently of the parameter. -/
theorem hasDerivAt_prod_integral_halfspace_difference_local
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {f : ℝ → X → ℝ → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    {s : Set ℝ} (hs : s ∈ nhds 0)
    (hf : ∀ h, Measurable (Function.uncurry (f h)))
    (hspeed : ∀ h, Measurable (speed h))
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h x (-(h * speed h x * u))) (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h ∈ s, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h ∈ s, ∀ t : ℝ, ‖f h x t‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ)
    (hInt : ∀ᶠ h in nhds 0, Integrable (Function.uncurry (f h)) (μ.prod volume)) :
    HasDerivAt (fun h : ℝ => ∫ p : X × ℝ,
      f h p.1 p.2 * ((if -(h * speed h p.1) ≤ p.2 then (1 : ℝ) else 0) -
        (if 0 ≤ p.2 then (1 : ℝ) else 0)) ∂μ.prod volume)
      (∫ x, slope x * trace x ∂μ) 0 := by
  have hd := hasDerivAt_integral_halfspace_difference_local hs hf hspeed
    hspeedlim hlim hspeedbound hbound hdom
  apply hd.congr_of_eventuallyEq
  filter_upwards [hInt] with h hh
  exact integral_prod _ (integrable_threshold_difference hh
    (measurable_const.mul (hspeed h)).neg)

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CutVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem358

/-- Transport the moving-halfspace derivative through a measure-preserving
coordinate chart. The affine geometry enters only through the exact threshold
identity, while the derivative and all integration steps are proved here. -/
theorem hasDerivAt_integral_cut_difference_of_chart
    {X V : Type*} [MeasurableSpace X] [MeasurableSpace V]
    {μ : Measure X} [SFinite μ] {ρ : Measure V}
    {chart : X × ℝ → V} (hchart : MeasurePreserving chart (μ.prod volume) ρ)
    {f ell : ℝ → V → ℝ} {speed : ℝ → X → ℝ} {A B slope trace : X → ℝ}
    {s : Set ℝ} (hs : s ∈ nhds 0)
    (hf : ∀ h, Measurable (f h)) (hell : ∀ h, Measurable (ell h))
    (hspeed : ∀ h, Measurable (speed h))
    (hlevel : ∀ h ∈ s, ∀ p : X × ℝ,
      0 ≤ ell h (chart p) ↔ -(h * speed h p.1) ≤ p.2)
    (hspeedlim : ∀ᵐ x ∂μ, Tendsto (fun h => speed h x) (nhds 0) (nhds (slope x)))
    (hlim : ∀ᵐ x ∂μ, ∀ u : ℝ,
      Tendsto (fun h : ℝ => f h (chart (x, -(h * speed h x * u))))
        (nhds 0) (nhds (trace x)))
    (hspeedbound : ∀ᵐ x ∂μ, ∀ h ∈ s, |speed h x| ≤ A x)
    (hbound : ∀ᵐ x ∂μ, ∀ h ∈ s, ∀ t : ℝ, ‖f h (chart (x, t))‖ ≤ B x)
    (hdom : Integrable (fun x => A x * B x) μ)
    (hInt : ∀ᶠ h in nhds 0, Integrable (f h) ρ) :
    HasDerivAt (fun h : ℝ => ∫ v,
      f h v * ((if 0 ≤ ell h v then (1 : ℝ) else 0) -
        (if 0 ≤ ell 0 v then (1 : ℝ) else 0)) ∂ρ)
      (∫ x, slope x * trace x ∂μ) 0 := by
  let F : ℝ → X → ℝ → ℝ := fun h => Function.curry (f h ∘ chart)
  have hF : ∀ h, Measurable (Function.uncurry (F h)) := by
    intro h
    simpa only [F, Function.uncurry_curry] using (hf h).comp hchart.measurable
  have hFI : ∀ᶠ h in nhds 0, Integrable (Function.uncurry (F h)) (μ.prod volume) := by
    filter_upwards [hInt] with h hh
    simpa only [F, Function.uncurry_curry] using hchart.integrable_comp_of_integrable hh
  have hd := hasDerivAt_prod_integral_halfspace_difference_local
    (f := F) hs hF hspeed hspeedlim hlim hspeedbound hbound hdom hFI
  apply hd.congr_of_eventuallyEq
  filter_upwards [hs] with h hh
  have hraw : Measurable (fun v => f h v *
      ((if 0 ≤ ell h v then (1 : ℝ) else 0) -
        (if 0 ≤ ell 0 v then (1 : ℝ) else 0))) :=
    (hf h).mul ((Measurable.ite (measurableSet_le measurable_const (hell h))
      measurable_const measurable_const).sub
      (Measurable.ite (measurableSet_le measurable_const (hell 0))
        measurable_const measurable_const))
  rw [← hchart.map_eq, integral_map hchart.measurable.aemeasurable hraw.aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    have hz := hlevel 0 (mem_of_mem_nhds hs) p
    simp only [zero_mul, neg_zero] at hz
    simp only [F, Function.curry, Function.comp_apply, hlevel h hh p, hz]

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MovingTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology RealInnerProductSpace

namespace Problem358.MovingCellTrace

lemma continuousAt_cutIndicator {r : ℝ} (hr : r ≠ 0) :
    ContinuousAt cutIndicator r := by
  apply ContinuousOn.continuousAt_indicator continuousOn_const
  simpa only [frontier_Ici, Set.mem_singleton_iff] using hr

/-- A finite family of cuts is stable whenever every limiting score is nonzero. -/
lemma tendsto_cut_product {α ι : Type*} {l : Filter α}
    (J : Finset ι) {s : α → ι → ℝ} {b : ι → ℝ}
    (hs : ∀ i ∈ J, Tendsto (fun a => s a i) l (𝓝 (b i)))
    (hb : ∀ i ∈ J, b i ≠ 0) :
    Tendsto (fun a => ∏ i ∈ J, cutIndicator (s a i)) l
      (𝓝 (∏ i ∈ J, cutIndicator (b i))) := by
  exact tendsto_finsetProd J fun i hi =>
    (continuousAt_cutIndicator (hb i hi)).tendsto.comp (hs i hi)

/-- Generic scaled-trace convergence for the unchanged source constraint and all
nonselected moving cuts. The selected face is deliberately absent from `J`. -/
lemma tendsto_remainder_trace {α ι X : Type*} [TopologicalSpace X]
    {l : Filter α} (J : Finset ι) {K : Set X} {w : X → ℝ}
    {x : α → X} {z : X} {s : α → ι → ℝ} {b : ι → ℝ}
    (hx : Tendsto x l (𝓝 z)) (hz : z ∉ frontier K)
    (hw : ContinuousOn w (interior K))
    (hs : ∀ i ∈ J, Tendsto (fun a => s a i) l (𝓝 (b i)))
    (hb : ∀ i ∈ J, b i ≠ 0) :
    Tendsto (fun a => K.indicator w (x a) * ∏ i ∈ J, cutIndicator (s a i)) l
      (𝓝 (K.indicator w z * ∏ i ∈ J, cutIndicator (b i))) := by
  exact ((hw.continuousAt_indicator hz).tendsto.comp hx).mul
    (tendsto_cut_product J hs hb)

end Problem358.MovingCellTrace

end

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Problem358.MovingCellTrace

lemma measurable_cutIndicator : Measurable cutIndicator :=
  measurable_const.indicator measurableSet_Ici

lemma norm_cutIndicator_le_one (r : ℝ) : ‖cutIndicator r‖ ≤ 1 := by
  by_cases hr : 0 ≤ r <;> simp [cutIndicator, Set.indicator, hr]

lemma norm_cut_product_le_one {ι : Type*} (J : Finset ι) (s : ι → ℝ) :
    ‖∏ i ∈ J, cutIndicator (s i)‖ ≤ 1 := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_cutIndicator_le_one _)).trans ih

lemma measurable_cut_product {ι X : Type*} [MeasurableSpace X]
    (J : Finset ι) {s : X → ι → ℝ} (hs : ∀ i ∈ J, Measurable (fun x => s x i)) :
    Measurable (fun x => ∏ i ∈ J, cutIndicator (s x i)) :=
  J.measurable_prod (fun i hi => measurable_cutIndicator.comp (hs i hi))

lemma measurable_remainder {ι X : Type*} [MeasurableSpace X]
    (J : Finset ι) {K : Set X} (hK : MeasurableSet K)
    {w : X → ℝ} (hw : Measurable w) {s : X → ι → ℝ}
    (hs : ∀ i ∈ J, Measurable (fun x => s x i)) :
    Measurable (fun x => K.indicator w x * ∏ i ∈ J, cutIndicator (s x i)) :=
  (hw.indicator hK).mul (measurable_cut_product J hs)

/-- Removing finitely many halfspace constraints never enlarges the absolute weight. -/
lemma norm_remainder_le {ι X : Type*} (J : Finset ι) (K : Set X)
    (w : X → ℝ) (s : X → ι → ℝ) (x : X) :
    ‖K.indicator w x * ∏ i ∈ J, cutIndicator (s x i)‖ ≤ ‖K.indicator w x‖ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_cut_product_le_one J (s x))
    (norm_nonneg _)).trans_eq (mul_one _)

lemma integrable_remainder {ι X : Type*} [MeasurableSpace X]
    {μ : Measure X} (J : Finset ι) {K : Set X} (hK : MeasurableSet K)
    {w : X → ℝ} (hw : IntegrableOn w K μ) {s : X → ι → ℝ}
    (hs : ∀ i ∈ J, Measurable (fun x => s x i)) :
    Integrable (fun x => K.indicator w x * ∏ i ∈ J, cutIndicator (s x i)) μ := by
  have hwi := hw.integrable_indicator hK
  apply hwi.norm.mono' (hwi.aestronglyMeasurable.mul
    (measurable_cut_product J hs).aestronglyMeasurable)
  exact Eventually.of_forall (norm_remainder_le J K w s)

/-- The transverse support of every cut remainder is inside the projection of the
fixed compact source. No bound on the normal coordinate is needed. -/
lemma norm_remainder_chart_le {ι X V : Type*}
    (J : Finset ι) (K : Set V) (P : V → X) (chart : X × ℝ → V)
    (hP : ∀ z t, P (chart (z, t)) = z)
    (w : V → ℝ) (s : V → ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ x ∈ K, ‖w x‖ ≤ C) (z : X) (t : ℝ) :
    ‖K.indicator w (chart (z, t)) * ∏ i ∈ J,
      cutIndicator (s (chart (z, t)) i)‖ ≤ (P '' K).indicator (fun _ => C) z := by
  classical
  by_cases hx : chart (z, t) ∈ K
  · have hz : z ∈ P '' K := ⟨chart (z, t), hx, hP z t⟩
    rw [Set.indicator_of_mem hz]
    exact (norm_remainder_le J K w s (chart (z, t))).trans (by
      simpa only [Set.indicator_of_mem hx] using hw (chart (z, t)) hx)
  · simp only [Set.indicator_of_notMem hx, zero_mul, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hC) z

/-- Any continuous speed envelope is integrable against a compact transverse
support bound. This is the domination premise in the moving-face kernel. -/
lemma integrable_compact_projection_bound
    {X V : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] [TopologicalSpace V]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set V} (hK : IsCompact K) {P : V → X} (hP : Continuous P)
    {A : X → ℝ} (hA : Continuous A) (C : ℝ) :
    Integrable (fun z => A z * (P '' K).indicator (fun _ => C) z) μ := by
  have hcompact : IsCompact (P '' K) := hK.image hP
  have hint : Integrable ((P '' K).indicator (fun z => A z * C)) μ :=
    ((hA.mul continuous_const).continuousOn.integrableOn_compact hcompact).integrable_indicator
      hcompact.measurableSet
  convert hint using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  by_cases hz : z ∈ P '' K <;> simp [Set.indicator, hz]

/-- Compactness discharges a uniform transverse dominating function for every
configuration of additional halfspace cuts, at once. -/
theorem exists_compact_projection_domination
    {ι Θ X V : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] [TopologicalSpace V]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (J : Finset ι) {K : Set V} (hK : IsCompact K)
    {P : V → X} (hP : Continuous P) (chart : X × ℝ → V)
    (hchart : ∀ z t, P (chart (z, t)) = z)
    {w : V → ℝ} (hw : ContinuousOn w K)
    (s : Θ → V → ι → ℝ) {A : X → ℝ} (hA : Continuous A) :
    ∃ B : X → ℝ, (∀ z, 0 ≤ B z) ∧ Integrable (fun z => A z * B z) μ ∧
      ∀ a z t, ‖K.indicator w (chart (z, t)) * ∏ i ∈ J,
        cutIndicator (s a (chart (z, t)) i)‖ ≤ B z := by
  obtain ⟨C, hC, hbound⟩ := (hK.image_of_continuousOn hw).isBounded.exists_pos_norm_le
  refine ⟨(P '' K).indicator (fun _ => C), ?_,
    integrable_compact_projection_bound hK hP hA C, ?_⟩
  · exact fun z => Set.indicator_nonneg (fun _ _ => hC.le) z
  · intro a z t
    exact norm_remainder_chart_le J K P chart hchart w (s a) hC.le
      (fun x hx => hbound (w x) ⟨x, hx, rfl⟩) z t

end Problem358.MovingCellTrace

namespace Problem358.MovingCellTrace

/-- Continuity of finite-cut face integrals in a fixed transverse projection.
All integrability and domination are consequences of the compact source and
continuous test weight. The varying charts need not be measure preserving: the
measure here stays on the fixed reference plane. -/
theorem tendsto_integral_remainder_of_compact_projection
    {ι α X V : Type*} {l : Filter α} [l.IsCountablyGenerated]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] [T2Space V]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (J : Finset ι) {K : Set V} (hK : IsCompact K)
    {P : V → X} (hP : Continuous P)
    {chart : α → X → V} {base : X → V}
    (hproject : ∀ q x, P (chart q x) = x)
    (hchartmeas : ∀ q, Measurable (chart q))
    (hchartlim : ∀ᵐ x ∂μ, Tendsto (fun q => chart q x) l (𝓝 (base x)))
    {w : V → ℝ} (hwmeas : Measurable w) (hwcont : ContinuousOn w K)
    {s : α → V → ι → ℝ} {b : X → ι → ℝ}
    (hsmeas : ∀ q k, k ∈ J → Measurable (fun v => s q v k))
    (hslim : ∀ᵐ x ∂μ, ∀ k ∈ J,
      Tendsto (fun q => s q (chart q x) k) l (𝓝 (b x k)))
    (hregular : ∀ᵐ x ∂μ, base x ∉ frontier K ∧ ∀ k ∈ J, b x k ≠ 0) :
    Tendsto (fun q => ∫ x, K.indicator w (chart q x) * ∏ k ∈ J,
      cutIndicator (s q (chart q x) k) ∂μ) l
      (𝓝 (∫ x, K.indicator w (base x) * ∏ k ∈ J, cutIndicator (b x k) ∂μ)) := by
  obtain ⟨C, hC, hCbound⟩ := (hK.image_of_continuousOn hwcont).isBounded.exists_pos_norm_le
  let B : X → ℝ := (P '' K).indicator (fun _ => C)
  have hBint : Integrable B μ := by
    simpa only [one_mul] using
      (integrable_compact_projection_bound hK hP continuous_const C :
        Integrable (fun x => (1 : ℝ) * (P '' K).indicator (fun _ => C) x) μ)
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hBint ?_
  · exact Eventually.of_forall fun q =>
      ((measurable_remainder J hK.measurableSet hwmeas (hsmeas q)).comp
        (hchartmeas q)).aestronglyMeasurable
  · exact Eventually.of_forall fun q => Eventually.of_forall fun x =>
      norm_remainder_chart_le J K P (fun p : X × ℝ => chart q p.1)
        (fun z _ => hproject q z) w (s q) hC.le
        (fun v hv => hCbound (w v) ⟨v, hv, rfl⟩) x 0
  · filter_upwards [hchartlim, hslim, hregular] with x hx hs hr
    exact tendsto_remainder_trace J hx hr.1
      (hwcont.mono interior_subset) hs hr.2

end Problem358.MovingCellTrace

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CutDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace Problem358.AffineHalfspaceSpeed

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem perturbed_affine_eq (n u v x : V) (c r h t : ℝ)
    (hface : ⟪n, x⟫_ℝ + c = 0) :
    ⟪n + h • v, x + t • u⟫_ℝ + (c + h * r) =
      t * (⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) + h * (r + ⟪v, x⟫_ℝ) := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  nlinarith

/-- A tilted affine inequality is an exact moving scalar threshold. -/
theorem perturbed_nonneg_iff (n u v x : V) (c r h t : ℝ)
    (hface : ⟪n, x⟫_ℝ + c = 0)
    (hden : 0 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) :
    0 ≤ ⟪n + h • v, x + t • u⟫_ℝ + (c + h * r) ↔
      -h * speed n u v r h x ≤ t := by
  rw [perturbed_affine_eq n u v x c r h t hface]
  unfold speed
  rw [← mul_div_assoc, div_le_iff₀ hden]
  constructor <;> intro hi <;> nlinarith

/-- The transverse denominator stays uniformly above half its initial value. -/
theorem eventually_denominator_half (n u v : V) (htrans : 0 < ⟪n, u⟫_ℝ) :
    ∀ᶠ h : ℝ in 𝓝 0, ⟪n, u⟫_ℝ / 2 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ := by
  have ht : Tendsto (fun h : ℝ => ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ)
      (𝓝 0) (𝓝 ⟪n, u⟫_ℝ) := by
    have hc : ContinuousAt (fun h : ℝ => ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) 0 := by fun_prop
    simpa using hc.tendsto
  exact ht.eventually_const_lt (by linarith)

theorem continuousAt_speed (n u v : V) (r : ℝ) (x : V)
    (htrans : ⟪n, u⟫_ℝ ≠ 0) : ContinuousAt (fun h => speed n u v r h x) 0 := by
  unfold speed
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · simpa using htrans

theorem tendsto_speed (n u v : V) (r : ℝ) (x : V)
    (htrans : ⟪n, u⟫_ℝ ≠ 0) :
    Tendsto (fun h => speed n u v r h x) (𝓝 0)
      (𝓝 ((r + ⟪v, x⟫_ℝ) / ⟪n, u⟫_ℝ)) := by
  simpa [speed] using (continuousAt_speed n u v r x htrans).tendsto

/-- A uniform speed bound on a bounded subset of the reference face. -/
theorem abs_speed_le (n u v : V) (r h R : ℝ) (x : V)
    (htrans : 0 < ⟪n, u⟫_ℝ)
    (hden : ⟪n, u⟫_ℝ / 2 ≤ ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ)
    (hx : ‖x‖ ≤ R) :
    |speed n u v r h x| ≤ 2 * (|r| + ‖v‖ * R) / ⟪n, u⟫_ℝ := by
  have hdenpos : 0 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ := by linarith
  have hnum : |r + ⟪v, x⟫_ℝ| ≤ |r| + ‖v‖ * R := by
    calc
      |r + ⟪v, x⟫_ℝ| ≤ |r| + |⟪v, x⟫_ℝ| := abs_add_le _ _
      _ ≤ |r| + ‖v‖ * ‖x‖ := add_le_add (le_refl _) (abs_real_inner_le_norm v x)
      _ ≤ |r| + ‖v‖ * R := by gcongr
  have hnumpos : 0 ≤ |r| + ‖v‖ * R := le_trans (abs_nonneg _) hnum
  rw [speed, abs_div, abs_of_pos hdenpos]
  calc
    |r + ⟪v, x⟫_ℝ| / (⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) ≤
        (|r| + ‖v‖ * R) / (⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
    _ ≤ (|r| + ‖v‖ * R) / (⟪n, u⟫_ℝ / 2) :=
      div_le_div_of_nonneg_left hnumpos (by positivity) hden
    _ = 2 * (|r| + ‖v‖ * R) / ⟪n, u⟫_ℝ := by ring

/-- Points in the rescaled moving strip converge to their reference-face point. -/
theorem tendsto_scaled_point (n u v x : V) (r a : ℝ)
    (htrans : ⟪n, u⟫_ℝ ≠ 0) :
    Tendsto (fun h : ℝ => x + (-h * speed n u v r h x * a) • u)
      (𝓝 0) (𝓝 x) := by
  have hs := tendsto_speed n u v r x htrans
  have hh : Tendsto (fun h : ℝ => -h * speed n u v r h x * a) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.neg.mul hs).mul_const a
  have hu : Tendsto (fun h : ℝ => (-h * speed n u v r h x * a) • u)
      (𝓝 0) (𝓝 (0 : V)) := by
    simpa using hh.smul_const u
  simpa using (tendsto_const_nhds (x := x)).add hu

variable [MeasurableSpace V] [BorelSpace V]

/-- Joint measurability remains valid even where the totalized denominator vanishes. -/
theorem measurable_speed (n u v : V) (r : ℝ) :
    Measurable (fun p : ℝ × V => speed n u v r p.1 p.2) := by
  unfold speed
  fun_prop

end Problem358.AffineHalfspaceSpeed

end

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Problem358

/-- Differentiation of an actual moving affine cut in a fixed transverse chart.
The affine threshold identity, local denominator bounds, velocity limit, and
velocity measurability are all consequences, not extra hypotheses. -/
theorem hasDerivAt_integral_affine_cut_difference
    {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure X} [SFinite μ] {ρ : Measure V}
    (base : X → V) (hbase : Measurable base) (n u v : V) (c r : ℝ)
    (hchart : MeasurePreserving
      (fun p : X × ℝ => base p.1 + p.2 • u) (μ.prod volume) ρ)
    (hface : ∀ x, ⟪n, base x⟫_ℝ + c = 0)
    (htrans : 0 < ⟪n, u⟫_ℝ)
    {f : ℝ → V → ℝ} (hf : ∀ h, Measurable (f h))
    (B trace : X → ℝ)
    (hlim : ∀ᵐ x ∂μ, ∀ a : ℝ,
      Tendsto (fun h : ℝ => f h
        (base x + (-h * AffineHalfspaceSpeed.speed n u v r h (base x) * a) • u))
        (nhds 0) (nhds (trace x)))
    (hbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖f h (base x + t • u)‖ ≤ B x)
    (hdom : Integrable
      (fun x => (2 * (|r| + ‖v‖ * ‖base x‖) / ⟪n, u⟫_ℝ) * B x) μ)
    (hInt : ∀ᶠ h in nhds 0, Integrable (f h) ρ) :
    HasDerivAt (fun h : ℝ => ∫ y,
      f h y *
        ((if 0 ≤ ⟪n + h • v, y⟫_ℝ + (c + h * r) then (1 : ℝ) else 0) -
          (if 0 ≤ ⟪n, y⟫_ℝ + c then (1 : ℝ) else 0)) ∂ρ)
      (∫ x, ((r + ⟪v, base x⟫_ℝ) / ⟪n, u⟫_ℝ) * trace x ∂μ) 0 := by
  let speed : ℝ → X → ℝ := fun h x => AffineHalfspaceSpeed.speed n u v r h (base x)
  let s : Set ℝ := {h | ⟪n, u⟫_ℝ / 2 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ}
  have hs : s ∈ nhds 0 := AffineHalfspaceSpeed.eventually_denominator_half n u v htrans
  have hspeed : ∀ h, Measurable (speed h) := by
    intro h
    exact (AffineHalfspaceSpeed.measurable_speed n u v r).comp
      (measurable_const.prodMk hbase)
  have hlevel : ∀ h ∈ s, ∀ p : X × ℝ,
      0 ≤ ⟪n + h • v, base p.1 + p.2 • u⟫_ℝ + (c + h * r) ↔
        -(h * speed h p.1) ≤ p.2 := by
    intro h hh p
    have hpos : 0 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ := by
      change ⟪n, u⟫_ℝ / 2 < _ at hh
      linarith
    simpa only [speed, neg_mul] using
      AffineHalfspaceSpeed.perturbed_nonneg_iff n u v (base p.1) c r h p.2
        (hface p.1) hpos
  have hspeedlim : ∀ᵐ x ∂μ,
      Tendsto (fun h => speed h x) (nhds 0)
        (nhds ((r + ⟪v, base x⟫_ℝ) / ⟪n, u⟫_ℝ)) :=
    Eventually.of_forall fun x =>
      AffineHalfspaceSpeed.tendsto_speed n u v r (base x) (ne_of_gt htrans)
  have hspeedbound : ∀ᵐ x ∂μ, ∀ h ∈ s,
      |speed h x| ≤ 2 * (|r| + ‖v‖ * ‖base x‖) / ⟪n, u⟫_ℝ := by
    apply Eventually.of_forall
    intro x h hh
    exact AffineHalfspaceSpeed.abs_speed_le n u v r h ‖base x‖ (base x)
      htrans (le_of_lt hh) le_rfl
  have hlim' : ∀ᵐ x ∂μ, ∀ a : ℝ,
      Tendsto (fun h : ℝ => f h (base x + (-(h * speed h x * a)) • u))
        (nhds 0) (nhds (trace x)) := by
    simpa only [speed, neg_mul] using hlim
  have hd := hasDerivAt_integral_cut_difference_of_chart hchart hs hf
    (ell := fun h y => ⟪n + h • v, y⟫_ℝ + (c + h * r))
    (fun _ => by fun_prop) hspeed hlevel hspeedlim hlim' hspeedbound
    (hbound.mono fun x hx h _ t => hx h t) hdom hInt
  simpa only [zero_smul, add_zero, zero_mul] using hd

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators

namespace Problem358

/-- A compact source and an almost-everywhere regular reference face suffice to
differentiate a moving cut with all other moving cut indicators attached. In
particular, the trace limit, compact domination, ambient integrability, affine
velocity, and exact threshold identity are all proved internally. -/
theorem hasDerivAt_compact_affine_cut_remainder
    {ι X V : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure X} [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    {ρ : Measure V} [IsFiniteMeasureOnCompacts ρ]
    {K : Set V} (hK : IsCompact K) (w : V → ℝ) (hw : Continuous w)
    (base : X → V) (hbase : Continuous base) (n u v : V) (c r : ℝ)
    (hchart : MeasurePreserving
      (fun p : X × ℝ => base p.1 + p.2 • u) (μ.prod volume) ρ)
    (P : V → X) (hP : Continuous P)
    (hprojection : ∀ (z : X) (t : ℝ), P (base z + t • u) = z)
    (hface : ∀ x, ⟪n, base x⟫_ℝ + c = 0)
    (htrans : 0 < ⟪n, u⟫_ℝ)
    (J : Finset ι) (ell : ℝ → ι → V → ℝ)
    (hell : ∀ i ∈ J, Continuous (fun p : ℝ × V => ell p.1 i p.2))
    (hregular : ∀ᵐ x ∂μ, base x ∉ frontier K ∧
      ∀ i ∈ J, ell 0 i (base x) ≠ 0) :
    HasDerivAt (fun h : ℝ => ∫ y,
      (K.indicator w y * ∏ i ∈ J, MovingCellTrace.cutIndicator (ell h i y)) *
        ((if 0 ≤ ⟪n + h • v, y⟫_ℝ + (c + h * r) then (1 : ℝ) else 0) -
          (if 0 ≤ ⟪n, y⟫_ℝ + c then (1 : ℝ) else 0)) ∂ρ)
      (∫ x, ((r + ⟪v, base x⟫_ℝ) / ⟪n, u⟫_ℝ) *
        (K.indicator w (base x) *
          ∏ i ∈ J, MovingCellTrace.cutIndicator (ell 0 i (base x))) ∂μ) 0 := by
  let f : ℝ → V → ℝ := fun h y =>
    K.indicator w y * ∏ i ∈ J, MovingCellTrace.cutIndicator (ell h i y)
  have hellM (h : ℝ) (i : ι) (hi : i ∈ J) : Measurable (ell h i) :=
    ((hell i hi).comp (continuous_const.prodMk continuous_id)).measurable
  have hf : ∀ h, Measurable (f h) := by
    intro h
    exact MovingCellTrace.measurable_remainder J hK.measurableSet hw.measurable
      (hellM h)
  have hInt : ∀ᶠ h in nhds 0, Integrable (f h) ρ := by
    apply Eventually.of_forall
    intro h
    exact MovingCellTrace.integrable_remainder J hK.measurableSet
      (hw.continuousOn.integrableOn_compact hK) (hellM h)
  have hA : Continuous
      (fun x => 2 * (|r| + ‖v‖ * ‖base x‖) / ⟪n, u⟫_ℝ) := by fun_prop
  obtain ⟨B, _, hdom, hbound⟩ :=
    MovingCellTrace.exists_compact_projection_domination
      (μ := μ) J hK hP (fun p : X × ℝ => base p.1 + p.2 • u)
      hprojection hw.continuousOn (fun h y i => ell h i y) hA
  have hlim : ∀ᵐ x ∂μ, ∀ a : ℝ,
      Tendsto (fun h : ℝ => f h
        (base x + (-h * AffineHalfspaceSpeed.speed n u v r h (base x) * a) • u))
        (nhds 0) (nhds (K.indicator w (base x) *
          ∏ i ∈ J, MovingCellTrace.cutIndicator (ell 0 i (base x)))) := by
    filter_upwards [hregular] with x hx
    intro a
    have hp := AffineHalfspaceSpeed.tendsto_scaled_point n u v (base x) r a
      (ne_of_gt htrans)
    apply MovingCellTrace.tendsto_remainder_trace J hp hx.1 hw.continuousOn _ hx.2
    intro i hi
    exact (hell i hi).continuousAt.tendsto.comp (tendsto_id.prodMk_nhds hp)
  exact hasDerivAt_integral_affine_cut_difference base hbase.measurable n u v c r
    hchart hface htrans hf B _ hlim
    (Eventually.of_forall fun x h t => hbound h x t) hdom hInt

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Interfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Positive-mass affine cells have regular interfaces: the source boundary and
all third-branch ties are negligible for surface Haar measure. -/
theorem ae_regular_interface {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : inner ℝ z (y i) + c i = inner ℝ z (y j) + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      z + (w : E d) ∉ frontier K ∧ ∀ k, k ≠ i → k ≠ j →
      inner ℝ (z + (w : E d)) (y i) + c i ≠
        inner ℝ (z + (w : E d)) (y k) + c k := by
  let W := (ℝ ∙ (y i - y j))ᗮ
  let f : W →ᵃ[ℝ] E d := AffineMap.const ℝ W z + W.subtype.toAffineMap
  have hmeet : (f ⁻¹' interior K).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [f] using hz
  have hboundary : ∀ᵐ w : W ∂μ, z + (w : E d) ∉ frontier K := by
    have hn := Problem358.haar_affine_preimage_frontier_null μ f hclosed hconv hmeet
    change μ {w : W | z + (w : E d) ∈ frontier K} = 0 at hn
    simpa only [ae_iff, not_not] using hn
  have hactive : ∀ k, ∃ x, ∀ l, l ≠ k →
      TripleCell.score (y l) (c l) x < TripleCell.score (y k) (c k) x := by
    intro k
    obtain ⟨x, _, hx⟩ := exists_strict_active_interior_of_mass hρ hconv y c hy k (hpos k)
    exact ⟨x, hx⟩
  exact hboundary.and (TripleCell.ae_no_other_ties_on_interface y c hactive hij htie μ)

end Problem358.CellGeometry

namespace Problem358.CellGeometry

/-- The regular-interface theorem for an arbitrary point on the equality plane.
Positive cell masses supply an interior crossing, so the chosen affine-chart base
need not itself belong to the convex source. -/
theorem ae_regular_interface_of_tie
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d}
    (htie : inner ℝ z (y i) + c i = inner ℝ z (y j) + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      z + (w : E d) ∉ frontier K ∧ ∀ k, k ≠ i → k ≠ j →
      inner ℝ (z + (w : E d)) (y i) + c i ≠
        inner ℝ (z + (w : E d)) (y k) + c k := by
  let W := (ℝ ∙ (y i - y j))ᗮ
  let f : W →ᵃ[ℝ] E d := AffineMap.const ℝ W z + W.subtype.toAffineMap
  obtain ⟨x, hx, hxtie⟩ := exists_equality_interior_of_positive_cells
    hρ hconv y c hy hij (hpos i) (hpos j)
  have hxz : x - z ∈ W := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    simp only [inner_sub_left, inner_sub_right]
    linarith
  have hmeet : (f ⁻¹' interior K).Nonempty := by
    refine ⟨⟨x - z, hxz⟩, ?_⟩
    change z + (x - z) ∈ interior K
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    abel
  have hboundary : ∀ᵐ w : W ∂μ, z + (w : E d) ∉ frontier K := by
    have hn := Problem358.haar_affine_preimage_frontier_null μ f hclosed hconv hmeet
    change μ {w : W | z + (w : E d) ∈ frontier K} = 0 at hn
    simpa only [ae_iff, not_not] using hn
  have hactive : ∀ k, ∃ x, ∀ l, l ≠ k →
      TripleCell.score (y l) (c l) x < TripleCell.score (y k) (c k) x := by
    intro k
    obtain ⟨x, _, hx⟩ := exists_strict_active_interior_of_mass hρ hconv y c hy k (hpos k)
    exact ⟨x, hx⟩
  exact hboundary.and (TripleCell.ae_no_other_ties_on_interface y c hactive hij htie μ)

end Problem358.CellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_SurfaceCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Topology

namespace Problem358.TangentNormalCoordinates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Canonical product volume is transported to ambient volume by normal coordinates. -/
theorem measurePreserving_normalMap (n : V) (hn : n ≠ 0) :
    MeasurePreserving (normalMap n) (volume.prod volume) volume := by
  have h := (normalEquiv n hn).measurePreserving.comp
    (WithLp.volume_preserving_toLp ℝ (Tangent n))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

theorem measurePreserving_affineMap (n : V) (hn : n ≠ 0) (base : V) :
    MeasurePreserving (affineMap n base) (volume.prod volume) volume := by
  exact (measurePreserving_add_left volume base).comp (measurePreserving_normalMap n hn)

theorem measurePreserving_tangentMap (n : V) (hn : n ≠ 0) (base : V) :
    MeasurePreserving (tangentMap n base) (volume.prod volume) volume :=
  (measurePreserving_affineMap n hn base).comp Measure.measurePreserving_swap

end Problem358.TangentNormalCoordinates

end

noncomputable section

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace Problem358.AffinePlaneGraph

variable {X V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem graph_eq_base (base : X → V) (u n : V) (c : ℝ)
    (hface : ∀ x, ⟪n, base x⟫ + c = 0) (x : X) :
    graph base u n c x = base x := by
  simp [graph, hface x]

theorem inner_graph_add (base : X → V) (u n : V) (c : ℝ)
    (htrans : ⟪n, u⟫ ≠ 0) (x : X) :
    ⟪n, graph base u n c x⟫ + c = 0 := by
  simp only [graph, inner_sub_right, inner_smul_right]
  field_simp
  ring

theorem projection_graph (base : X → V) (u n : V) (c : ℝ)
    (P : V → X) (hP : ∀ (x : X) (t : ℝ), P (base x + t • u) = x) (x : X) :
    P (graph base u n c x) = x := by
  simpa only [graph, sub_eq_add_neg, neg_smul] using
    hP x (-((⟪n, base x⟫ + c) / ⟪n, u⟫))

section Topology

theorem tendsto_graph {α : Type*} {l : Filter α}
    {base : X → V} (u : V) {n : α → V} {c : α → ℝ} {n₀ : V} {c₀ : ℝ}
    (hn : Tendsto n l (𝓝 n₀)) (hc : Tendsto c l (𝓝 c₀))
    (htrans : ⟪n₀, u⟫ ≠ 0) (x : X) :
    Tendsto (fun q => graph base u (n q) (c q) x) l
      (𝓝 (graph base u n₀ c₀ x)) := by
  unfold graph
  exact tendsto_const_nhds.sub
    (((hn.inner tendsto_const_nhds).add hc).div
      (hn.inner tendsto_const_nhds) htrans |>.smul tendsto_const_nhds)

theorem tendsto_graph_base {α : Type*} {l : Filter α}
    {base : X → V} (u : V) {n : α → V} {c : α → ℝ} {n₀ : V} {c₀ : ℝ}
    (hn : Tendsto n l (𝓝 n₀)) (hc : Tendsto c l (𝓝 c₀))
    (htrans : ⟪n₀, u⟫ ≠ 0) (hface : ∀ x, ⟪n₀, base x⟫ + c₀ = 0) (x : X) :
    Tendsto (fun q => graph base u (n q) (c q) x) l (𝓝 (base x)) := by
  simpa only [graph_eq_base base u n₀ c₀ hface] using
    tendsto_graph (base := base) u hn hc htrans x

end Topology

variable [MeasurableSpace X] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

theorem measurable_graph (base : X → V) (hbase : Measurable base)
    (u n : V) (c : ℝ) : Measurable (graph base u n c) := by
  unfold graph
  fun_prop

/-- Replacing the base plane by any transverse graph preserves the full
product disintegration. This is a fiberwise translation, so no surface
Jacobian calculation is needed. -/
theorem measurePreserving_graph_chart
    {μ : Measure X} [SFinite μ] {ρ : Measure V}
    (base : X → V) (hbase : Measurable base) (u n : V) (c : ℝ)
    (hchart : MeasurePreserving
      (fun p : X × ℝ => base p.1 + p.2 • u) (μ.prod volume) ρ) :
    MeasurePreserving
      (fun p : X × ℝ => graph base u n c p.1 + p.2 • u) (μ.prod volume) ρ := by
  let a : X → ℝ := fun x => (⟪n, base x⟫ + c) / ⟪n, u⟫
  have ha : Measurable a := by fun_prop
  have hshift : MeasurePreserving (fun p : X × ℝ => (p.1, p.2 - a p.1))
      (μ.prod volume) (μ.prod volume) := by
    apply (MeasurePreserving.id μ).skew_product
      (g := fun x t => t - a x) (μc := volume) (μd := volume)
    · exact measurable_snd.sub (ha.comp measurable_fst)
    · exact Eventually.of_forall fun x =>
        (measurePreserving_sub_right volume (a x)).map_eq
  convert hchart.comp hshift using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [Function.comp_apply, graph, a, sub_smul]
  abel

end Problem358.AffinePlaneGraph

end

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Topology

namespace Problem358.TangentNormalCoordinates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem inner_unitNormal_pos (n : V) (hn : n ≠ 0) :
    0 < ⟪n, (‖n‖⁻¹ : ℝ) • n⟫_ℝ := by
  rw [inner_unitNormal n hn]
  exact norm_pos_iff.mpr hn

end Problem358.TangentNormalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators

namespace Problem358

open TangentNormalCoordinates

/-- The signed variation of one interface of a positive-mass affine cell.
Compactness, convexity, injectivity, and positive cell masses now discharge
all analytic bounds and all exceptional-face hypotheses. Other cuts may move
independently, as required by the finite-intersection telescoping formula. -/
theorem hasDerivAt_positive_cell_cut_remainder
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : ⟪z, y i⟫_ℝ + c i = ⟪z, y j⟫_ℝ + c j)
    (w : E d → ℝ) (hw : Continuous w) (v : E d) (r : ℝ)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    (ell : ℝ → ι → E d → ℝ)
    (hell : ∀ k ∈ J, Continuous (fun p : ℝ × E d => ell p.1 k p.2))
    (hell0 : ∀ k ∈ J, ∀ x, ell 0 k x = (⟪x, y i⟫_ℝ + c i) - (⟪x, y k⟫_ℝ + c k)) :
    HasDerivAt (fun h : ℝ => ∫ x,
      (K.indicator w x * ∏ k ∈ J, MovingCellTrace.cutIndicator (ell h k x)) *
        ((if 0 ≤ ⟪y i - y j + h • v, x⟫_ℝ + (c i - c j + h * r)
          then (1 : ℝ) else 0) -
          (if 0 ≤ ⟪y i - y j, x⟫_ℝ + (c i - c j) then (1 : ℝ) else 0)))
      (∫ a : Tangent (y i - y j),
        ((r + ⟪v, z + (a : E d)⟫_ℝ) / ‖y i - y j‖) *
          (K.indicator w (z + (a : E d)) *
            ∏ k ∈ J, MovingCellTrace.cutIndicator (ell 0 k (z + (a : E d))))) 0 := by
  let n := y i - y j
  have hn : n ≠ 0 := sub_ne_zero.mpr (hy.ne hij)
  let u : E d := (‖n‖⁻¹ : ℝ) • n
  let base : Tangent n → E d := fun a => z + (a : E d)
  let P : E d → Tangent n := fun x =>
    (WithLp.ofLp ((normalEquiv n hn).symm (x - z))).2
  have hbase : Continuous base := by fun_prop
  have hP : Continuous P := by
    unfold P
    fun_prop
  have hprojection : ∀ (a : Tangent n) (t : ℝ), P (base a + t • u) = a := by
    intro a t
    have heq : base a + t • u - z = normalMap n (t, a) := by
      simp only [base, u, normalMap]
      abel
    change (WithLp.ofLp ((normalEquiv n hn).symm (base a + t • u - z))).2 = a
    rw [heq, ← normalEquiv_apply n hn, LinearIsometryEquiv.symm_apply_apply]
  have hchart : MeasurePreserving
      (fun p : Tangent n × ℝ => base p.1 + p.2 • u) (volume.prod volume) volume := by
    convert measurePreserving_tangentMap n hn z using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp [base, u, TangentNormalCoordinates.tangentMap, affineMap, normalMap,
      add_assoc, add_comm]
  have hface : ∀ a : Tangent n, ⟪n, base a⟫_ℝ + (c i - c j) = 0 := by
    intro a
    have ha : ⟪n, (a : E d)⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp a.property
    rw [show base a = z + (a : E d) from rfl, inner_add_right, ha, add_zero]
    dsimp [n]
    rw [inner_sub_left]
    have htie' : ⟪y i, z⟫_ℝ + c i = ⟪y j, z⟫_ℝ + c j := by
      simpa only [real_inner_comm] using htie
    linarith
  have hregular : ∀ᵐ a : Tangent n,
      base a ∉ frontier K ∧ ∀ k ∈ J, ell 0 k (base a) ≠ 0 := by
    filter_upwards [CellGeometry.ae_regular_interface hρ hK.isClosed hconv
      y c hy hpos hij hz htie volume] with a ha
    refine ⟨ha.1, ?_⟩
    intro k hk
    rw [hell0 k hk]
    exact sub_ne_zero.mpr (ha.2 k (hJ k hk).1 (hJ k hk).2)
  have hd := hasDerivAt_compact_affine_cut_remainder hK w hw base hbase
    n u v (c i - c j) r hchart P hP hprojection hface
    (inner_unitNormal_pos n hn) J ell hell hregular
  simpa only [n, u, base, inner_unitNormal _ hn] using hd

end Problem358

end

noncomputable section

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace BigOperators

namespace Problem358.PositiveCellFullDerivative

open TangentNormalCoordinates MovingCellTrace

lemma prod_sub_prod_ordered {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (a b : ι → ℝ) :
    (∏ k ∈ s, a k) - (∏ k ∈ s, b k) =
      ∑ j ∈ s, (a j - b j) *
        ∏ k ∈ s.erase j, if k < j then a k else b k := by
  classical
  have h := Finset.prod_add_ordered s b (fun k => a k - b k)
  simp only [add_sub_cancel] at h
  rw [sub_eq_iff_eq_add]
  rw [h, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.prod_ite]
  have hleft : {k ∈ s.erase j | k < j} = {k ∈ s | k < j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hk⟩, hkj⟩
      exact ⟨hk, hkj⟩
    · rintro ⟨hk, hkj⟩
      exact ⟨⟨ne_of_lt hkj, hk⟩, hkj⟩
  have hright : {k ∈ s.erase j | ¬ k < j} = {k ∈ s | j < k} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, hk⟩, hkj⟩
      exact ⟨hk, lt_of_le_of_ne (le_of_not_gt hkj) (Ne.symm hne)⟩
    · rintro ⟨hk, hjk⟩
      exact ⟨⟨ne_of_gt hjk, hk⟩, not_lt_of_ge hjk.le⟩
  rw [hleft, hright]
  ring

lemma cutIndicator_eq_ite (r : ℝ) :
    cutIndicator r = if 0 ≤ r then 1 else 0 := by
  simp only [cutIndicator, Set.indicator_apply, Set.mem_Ici]

lemma norm_cutIndicator_sub_le_one (a b : ℝ) :
    ‖cutIndicator a - cutIndicator b‖ ≤ 1 := by
  rw [cutIndicator_eq_ite, cutIndicator_eq_ite]
  split_ifs <;> norm_num

/-- Ordered single-cut derivatives reassemble into the actual product integral.
The order is used only for the proof, not in the resulting derivative. -/
theorem hasDerivAt_cut_product_integral
    {ι X : Type*} [LinearOrder ι] [MeasurableSpace X]
    {μ : Measure X} (s : Finset ι) (ell : ℝ → ι → X → ℝ)
    (hell : ∀ t j, Measurable (ell t j))
    {w : X → ℝ} (hw : Integrable w μ) (D : ι → ℝ)
    (hd : ∀ j ∈ s, HasDerivAt (fun t : ℝ => ∫ x,
      (w x * ∏ k ∈ s.erase j,
        cutIndicator (if k < j then ell t k x else ell 0 k x)) *
          (cutIndicator (ell t j x) - cutIndicator (ell 0 j x)) ∂μ) (D j) 0) :
    HasDerivAt (fun t : ℝ => ∫ x,
      w x * ∏ j ∈ s, cutIndicator (ell t j x) ∂μ) (∑ j ∈ s, D j) 0 := by
  classical
  let term : ℝ → ι → X → ℝ := fun t j x =>
    (w x * ∏ k ∈ s.erase j,
      cutIndicator (if k < j then ell t k x else ell 0 k x)) *
        (cutIndicator (ell t j x) - cutIndicator (ell 0 j x))
  have hrem (t : ℝ) (j : ι) : Measurable (fun x =>
      ∏ k ∈ s.erase j, cutIndicator (if k < j then ell t k x else ell 0 k x)) := by
    apply measurable_cut_product
    intro k _
    split_ifs <;> exact hell _ _
  have hterm (t : ℝ) (j : ι) : Integrable (term t j) μ := by
    apply (hw.mul_bdd (hrem t j).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_cut_product_le_one _ _)).mul_bdd
      ((measurable_cutIndicator.comp (hell t j)).sub
        (measurable_cutIndicator.comp (hell 0 j))).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_cutIndicator_sub_le_one _ _)
  have hint (t : ℝ) : Integrable (fun x =>
      w x * ∏ j ∈ s, cutIndicator (ell t j x)) μ :=
    hw.mul_bdd (measurable_cut_product s (fun j _ => hell t j)).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_cut_product_le_one _ _)
  have heq (t : ℝ) :
      (∫ x, w x * ∏ j ∈ s, cutIndicator (ell t j x) ∂μ) -
        (∫ x, w x * ∏ j ∈ s, cutIndicator (ell 0 j x) ∂μ) =
      ∑ j ∈ s, ∫ x, term t j x ∂μ := by
    rw [← integral_sub (hint t) (hint 0), ← integral_finsetSum _ (fun j _ => hterm t j)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [← mul_sub, prod_sub_prod_ordered, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [term]
    simp only [apply_ite]
    ring
  have hs : HasDerivAt (fun t : ℝ => ∑ j ∈ s, ∫ x, term t j x ∂μ)
      (∑ j ∈ s, D j) 0 := HasDerivAt.fun_sum hd
  have hs' := hs.const_add (∫ x, w x * ∏ j ∈ s, cutIndicator (ell 0 j x) ∂μ)
  apply hs'.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro t
  dsimp only
  linarith [heq t]

lemma prod_cutIndicator_eq_indicator {ι X : Type*} (s : Finset ι)
    (ell : ι → X → ℝ) (x : X) :
    (∏ j ∈ s, cutIndicator (ell j x)) =
      {x | ∀ j ∈ s, 0 ≤ ell j x}.indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : ∀ j ∈ s, 0 ≤ ell j x
  · rw [Set.indicator_of_mem (s := {x | ∀ j ∈ s, 0 ≤ ell j x}) hx]
    apply Finset.prod_eq_one
    intro j hj
    simp [cutIndicator_eq_ite, hx j hj]
  · rw [Set.indicator_of_notMem (s := {x | ∀ j ∈ s, 0 ≤ ell j x}) hx]
    push Not at hx
    obtain ⟨j, hj, hneg⟩ := hx
    apply Finset.prod_eq_zero hj
    simp [cutIndicator_eq_ite, not_le_of_gt hneg]

/-- Full scalar weighted-cell derivative. Only actual compact convex positive-cell
geometry is assumed: all trace, domination, and signed-cut limits are proved. -/
theorem hasDerivAt_closedCell_integral
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y v : ι → E d) (c r : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    (w : E d → ℝ) (hw : Continuous w) (i : ι) (z : ι → E d)
    (hz : ∀ j, j ≠ i → z j ∈ interior K)
    (htie : ∀ j, j ≠ i → ⟪z j, y i⟫_ℝ + c i = ⟪z j, y j⟫_ℝ + c j) :
    HasDerivAt (fun t : ℝ => ∫ x in
      CellGeometry.closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i,
      w x)
      (∑ j ∈ Finset.univ.erase i, faceVariation K y v c r w i j (z j)) 0 := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let s : Finset ι := Finset.univ.erase i
  let ell : ℝ → ι → E d → ℝ := fun t j x =>
    ⟪y i - y j + t • (v i - v j), x⟫_ℝ + (c i - c j + t * (r i - r j))
  have hell (t : ℝ) (j : ι) : Measurable (ell t j) := by
    dsimp [ell]
    fun_prop
  have hell0 (j : ι) (x : E d) : ell 0 j x =
      (⟪x, y i⟫_ℝ + c i) - (⟪x, y j⟫_ℝ + c j) := by
    simp only [ell, zero_smul, add_zero, zero_mul, inner_sub_right, real_inner_comm]
    ring
  have hwK : Integrable (K.indicator w) (volume : Measure (E d)) :=
    (hw.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hd : HasDerivAt (fun t : ℝ => ∫ x,
      K.indicator w x * ∏ j ∈ s, cutIndicator (ell t j x))
      (∑ j ∈ s, faceVariation K y v c r w i j (z j)) 0 := by
    apply hasDerivAt_cut_product_integral s ell hell hwK
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    let mixed : ℝ → ι → E d → ℝ := fun t k x =>
      if k < j then ell t k x else ell 0 k x
    have hJ : ∀ k ∈ s.erase j, k ≠ i ∧ k ≠ j := by
      intro k hk
      exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,
        (Finset.mem_erase.mp hk).1⟩
    have hmix : ∀ k ∈ s.erase j, Continuous (fun p : ℝ × E d => mixed p.1 k p.2) := by
      intro k _
      dsimp [mixed]
      split_ifs <;> dsimp [ell] <;> fun_prop
    have hmix0 : ∀ k ∈ s.erase j, ∀ x, mixed 0 k x =
        (⟪x, y i⟫_ℝ + c i) - (⟪x, y k⟫_ℝ + c k) := by
      intro k _ x
      simp only [mixed, ite_self, hell0]
    have hsingle := hasDerivAt_positive_cell_cut_remainder hρ hK hconv y c hy hpos
      hji.symm (hz j hji) (htie j hji) w hw (v i - v j) (r i - r j)
      (s.erase j) hJ mixed hmix hmix0
    have hface : (∫ a : Tangent (y i - y j),
        ((r i - r j + ⟪v i - v j, z j + (a : E d)⟫_ℝ) / ‖y i - y j‖) *
          (K.indicator w (z j + (a : E d)) *
            ∏ k ∈ s.erase j, cutIndicator (mixed 0 k (z j + (a : E d))))) =
        faceVariation K y v c r w i j (z j) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro a
      dsimp only [faceVariation]
      congr 2
      apply Finset.prod_congr rfl
      intro k hk
      rw [hmix0 k hk]
    rw [hface] at hsingle
    apply hsingle.congr_of_eventuallyEq
    apply Eventually.of_forall
    intro t
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    simp only [mixed, ell, cutIndicator_eq_ite, zero_smul, zero_mul, add_zero]
    congr 2
    apply Finset.prod_congr
    · ext k; simp
    · intro k _; rfl
  have heq (t : ℝ) : (∫ x in
      CellGeometry.closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i,
      w x) = ∫ x, K.indicator w x * ∏ j ∈ s, cutIndicator (ell t j x) := by
    rw [← integral_indicator (CellGeometry.isClosed_closedCell hK.isClosed _ _ i).measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [prod_cutIndicator_eq_indicator]
    have hmem : x ∈ CellGeometry.closedCell K
        (fun j => y j + t • v j) (fun j => c j + t * r j) i ↔
        x ∈ K ∧ ∀ j ∈ s, 0 ≤ ell t j x := by
      constructor
      · rintro ⟨hxK, hx⟩
        refine ⟨hxK, ?_⟩
        intro j _
        have hj := hx j
        simp only [ell, inner_add_left, inner_smul_left, inner_sub_left,
          inner_add_right, inner_smul_right, real_inner_comm, starRingEnd_apply, star_trivial] at hj ⊢
        nlinarith
      · rintro ⟨hxK, hx⟩
        refine ⟨hxK, ?_⟩
        intro j
        by_cases hji : j = i
        · subst j; exact le_rfl
        have hj := hx j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
        simp only [ell, inner_add_left, inner_smul_left, inner_sub_left,
          inner_add_right, inner_smul_right, real_inner_comm, starRingEnd_apply, star_trivial] at hj ⊢
        nlinarith
    by_cases hxK : x ∈ K <;> by_cases hx : ∀ j ∈ s, 0 ≤ ell t j x <;>
      simp [Set.indicator_apply, hmem, hxK, hx]
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall heq

end Problem358.PositiveCellFullDerivative

end

/-! Actual vector moment and real mass differentials for positive affine cells.
This specializes the proved scalar moving-cell formula, not an assumed derivative. -/

noncomputable section
open MeasureTheory Set
open scoped Topology InnerProductSpace BigOperators

namespace Problem358.PositiveCellFullDerivative

/-- The genuine vector first-moment derivative, written in coordinates of the
signed intrinsic face integrals. All scalar differentiation hypotheses are
discharged by the full-cell calculus. -/
theorem hasDerivAt_uniform_closedCell_moment
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y v : ι → E d) (c r : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    (i : ι) (z : ι → E d)
    (hz : ∀ j, j ≠ i → z j ∈ interior K)
    (htie : ∀ j, j ≠ i → ⟪z j, y i⟫_ℝ + c i = ⟪z j, y j⟫_ℝ + c j) :
    HasDerivAt (fun t : ℝ => ∫ x in
      CellGeometry.closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i,
      x ∂uniformMeasure K)
      ((volume K).toReal⁻¹ • (WithLp.toLp 2 fun k : Fin d =>
        ∑ j ∈ Finset.univ.erase i, faceVariation K y v c r (fun x => x k) i j (z j))) 0 := by
  apply CellVectorDerivative.hasDerivAt_uniform_cellMoment_of_coordinates hK
    (fun t j => y j + t • v j) (fun t j => c j + t * r j) i
  intro k
  exact hasDerivAt_closedCell_integral hρ hK hconv y v c r hy hpos
    (fun x => x k) (by fun_prop) i z hz htie

end Problem358.PositiveCellFullDerivative

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_SurfaceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic affine-plane measure and orientation invariance

Surface measure is defined by translating canonical volume on a linear subspace.
The resulting ambient measure does not depend on the chosen basepoint in the
affine plane. In particular reversing a hyperplane equation preserves its measure.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped RealInnerProductSpace

namespace Problem358.IntrinsicSurface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem planeChart_isClosedEmbedding (W : Submodule ℝ E) (base : E) :
    Topology.IsClosedEmbedding (fun w : W => base + (w : E)) :=
  (Homeomorph.addLeft base).isClosedEmbedding.comp
    W.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal

theorem planeMeasure_apply_all (W : Submodule ℝ E) (base : E) (s : Set E) :
    planeMeasure W base s = volume {w : W | base + (w : E) ∈ s} :=
  (planeChart_isClosedEmbedding W base).measurableEmbedding.map_apply volume s

instance planeMeasure_finiteOnCompacts (W : Submodule ℝ E) (base : E) :
    IsFiniteMeasureOnCompacts (planeMeasure W base) where
  lt_top_of_isCompact {_} hK := by
    rw [planeMeasure_apply_all]
    exact ((planeChart_isClosedEmbedding W base).isCompact_preimage hK).measure_lt_top

theorem planeMeasure_setIntegral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : Submodule ℝ E) (base : E) (s : Set E) (f : E → F) :
    (∫ x in s, f x ∂planeMeasure W base) =
      ∫ w : W in {w : W | base + (w : E) ∈ s}, f (base + (w : E)) :=
  (planeChart_isClosedEmbedding W base).measurableEmbedding.setIntegral_map f s

/-- Translation of the basepoint within the plane does not change its intrinsic
measure. The equality is of ambient measures, not just of total face areas. -/
theorem planeMeasure_eq_of_sub_mem (W : Submodule ℝ E) {p q : E}
    (hpq : q - p ∈ W) : planeMeasure W q = planeMeasure W p := by
  let δ : W := ⟨q - p, hpq⟩
  have hcomp : (fun w : W => q + (w : E)) =
      (fun w : W => p + (w : E)) ∘ (fun w : W => δ + w) := by
    funext w
    change q + (w : E) = p + ((q - p) + (w : E))
    abel
  unfold planeMeasure
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    IsAddLeftInvariant.map_add_left_eq_self]

theorem planeMeasure_apply (W : Submodule ℝ E) (base : E)
    {s : Set E} (hs : MeasurableSet s) :
    planeMeasure W base s = volume {w : W | base + (w : E) ∈ s} := by
  rw [planeMeasure, Measure.map_apply (by fun_prop) hs]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_normalBase {n : E} (hn : n ≠ 0) (c : ℝ) :
    ⟪n, normalBase n c⟫ = -c := by
  rw [normalBase, inner_smul_right, real_inner_self_eq_norm_sq]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem orthogonal_span_neg (n : E) : (ℝ ∙ (-n))ᗮ = (ℝ ∙ n)ᗮ := by
  congr 1
  simpa only [Set.neg_singleton] using Submodule.span_neg (R := ℝ) ({n} : Set E)

/-- Reversing the equation of a hyperplane does not change surface measure. -/
@[simp] theorem hyperplaneMeasure_neg (n : E) (c : ℝ) :
    hyperplaneMeasure (-n) (-c) = hyperplaneMeasure n c := by
  simp only [hyperplaneMeasure, orthogonal_span_neg, normalBase_neg]

/-- The canonical hyperplane measure agrees with any parametrization based at
a point of its affine equation. -/
theorem hyperplaneMeasure_eq_planeMeasure {n base : E} {c : ℝ}
    (hn : n ≠ 0) (hbase : ⟪n, base⟫ + c = 0) :
    hyperplaneMeasure n c = planeMeasure (ℝ ∙ n)ᗮ base := by
  symm
  apply planeMeasure_eq_of_sub_mem
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  rw [inner_sub_right, inner_normalBase hn]
  linarith

/-- The intrinsic measure attached to a cell interface is symmetric in its labels. -/
theorem interfaceMeasure_swap (y z : E) (a b : ℝ) :
    interfaceMeasure z y b a = interfaceMeasure y z a b := by
  simpa only [interfaceMeasure, neg_sub] using hyperplaneMeasure_neg (y - z) (a - b)

/-- A concrete tie-plane chart computes the canonical interface measure. -/
theorem interfaceMeasure_eq_planeMeasure {y z base : E} {a b : ℝ}
    (hyz : y ≠ z) (htie : ⟪y, base⟫ + a = ⟪z, base⟫ + b) :
    interfaceMeasure y z a b = planeMeasure (ℝ ∙ (y - z))ᗮ base := by
  apply hyperplaneMeasure_eq_planeMeasure (sub_ne_zero.mpr hyz)
  rw [inner_sub_left]
  linarith

theorem interfaceMeasure_apply_of_tie {y z base : E} {a b : ℝ}
    (hyz : y ≠ z) (htie : ⟪y, base⟫ + a = ⟪z, base⟫ + b)
    {s : Set E} (hs : MeasurableSet s) :
    interfaceMeasure y z a b s =
      volume {w : (ℝ ∙ (y - z))ᗮ | base + (w : E) ∈ s} := by
  rw [interfaceMeasure_eq_planeMeasure hyz htie, planeMeasure_apply _ _ hs]

theorem interfaceMeasure_setIntegral_of_tie
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {y z base : E} {a b : ℝ} (hyz : y ≠ z)
    (htie : ⟪y, base⟫ + a = ⟪z, base⟫ + b) (s : Set E) (f : E → F) :
    (∫ x in s, f x ∂interfaceMeasure y z a b) =
      ∫ w : (ℝ ∙ (y - z))ᗮ in {w : (ℝ ∙ (y - z))ᗮ | base + (w : E) ∈ s}, f (base + (w : E)) := by
  rw [interfaceMeasure_eq_planeMeasure hyz htie, planeMeasure_setIntegral]

instance interfaceMeasure_finiteOnCompacts (y z : E) (a b : ℝ) :
    IsFiniteMeasureOnCompacts (interfaceMeasure y z a b) :=
  planeMeasure_finiteOnCompacts _ _

/-- Continuous scalar/vector/tensor weights on compact faces are integrable. -/
theorem integrableOn_interfaceMeasure
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (y z : E) (a b : ℝ) {s : Set E} (hs : IsCompact s)
    {f : E → F} (hf : ContinuousOn f s) :
    IntegrableOn f s (interfaceMeasure y z a b) := hf.integrableOn_compact hs

/-- This is the symmetry needed for both mass and moment face coefficients,
including the source-volume and normal-length normalization. -/
theorem normalized_face_integral_swap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (y z : E) (a b M : ℝ) (s t : Set E) (f : E → F) :
    (M * ‖z - y‖)⁻¹ • (∫ x in t ∩ s, f x ∂interfaceMeasure z y b a) =
      (M * ‖y - z‖)⁻¹ • (∫ x in s ∩ t, f x ∂interfaceMeasure y z a b) := by
  rw [interfaceMeasure_swap, inter_comm t s, norm_sub_rev z y]

theorem normalized_face_area_swap (y z : E) (a b M : ℝ) (s t : Set E) :
    (interfaceMeasure z y b a (t ∩ s)).toReal / (M * ‖z - y‖) =
      (interfaceMeasure y z a b (s ∩ t)).toReal / (M * ‖y - z‖) := by
  rw [interfaceMeasure_swap, inter_comm t s, norm_sub_rev z y]

/-- Intrinsic hyperplane measure is concentrated on its defining affine equation. -/
theorem ae_hyperplane_equation {n : E} (hn : n ≠ 0) (c : ℝ) :
    ∀ᵐ x ∂hyperplaneMeasure n c, ⟪n, x⟫ + c = 0 := by
  change ∀ᵐ x ∂Measure.map (fun w : (ℝ ∙ n)ᗮ => normalBase n c + (w : E)) volume,
    ⟪n, x⟫ + c = 0
  rw [(planeChart_isClosedEmbedding (ℝ ∙ n)ᗮ (normalBase n c)).measurableEmbedding.ae_map_iff]
  exact Filter.Eventually.of_forall fun w => by
    rw [inner_add_right, inner_normalBase hn,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property]
    ring

/-- Almost every point for a genuine interface measure satisfies the affine tie. -/
theorem ae_interface_tie {y z : E} (hyz : y ≠ z) (a b : ℝ) :
    ∀ᵐ x ∂interfaceMeasure y z a b, ⟪x, y⟫ + a = ⟪x, z⟫ + b := by
  filter_upwards [ae_hyperplane_equation (sub_ne_zero.mpr hyz) (a - b)] with x hx
  rw [inner_sub_left] at hx
  linarith [real_inner_comm x y, real_inner_comm x z]

end Problem358.IntrinsicSurface

end

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace Problem358.TransverseSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma height_add_transverse {n u b : V} {c : ℝ}
    (ha : ⟪n, u⟫ ≠ 0) (hb : ⟪n, b⟫ + c = 0) (t : ℝ) :
    height n u c (b + t • u) = t := by
  unfold height
  rw [inner_add_right, inner_smul_right]
  apply (div_eq_iff ha).mpr
  linarith

lemma retract_add_transverse {n u b : V} {c : ℝ}
    (ha : ⟪n, u⟫ ≠ 0) (hb : ⟪n, b⟫ + c = 0) (t : ℝ) :
    retract n u c (b + t • u) = b := by
  rw [retract, height_add_transverse ha hb]
  simp

variable [MeasurableSpace V] [BorelSpace V]

/-- A full product disintegration determines its plane measure by applying the
common retraction and height. No surface Jacobian theorem is assumed. -/
theorem map_retract_height_eq_prod
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {ρ : Measure V} {n u : V} {c : ℝ} (ha : ⟪n, u⟫ ≠ 0)
    (base : X → V) (hbase : Measurable base)
    (hplane : ∀ x, ⟪n, base x⟫ + c = 0)
    (hchart : MeasurePreserving (fun p : X × ℝ => base p.1 + p.2 • u)
      (μ.prod volume) ρ) :
    Measure.map (fun x => (retract n u c x, height n u c x)) ρ =
      (Measure.map base μ).prod volume := by
  have hm : Measurable (fun x => (retract n u c x, height n u c x)) := by
    unfold retract height
    fun_prop
  rw [← hchart.map_eq, Measure.map_map hm hchart.measurable]
  have he : (fun x => (retract n u c x, height n u c x)) ∘
      (fun p : X × ℝ => base p.1 + p.2 • u) = Prod.map base id := by
    funext p
    exact Prod.ext (retract_add_transverse ha (hplane p.1) p.2)
      (height_add_transverse ha (hplane p.1) p.2)
  rw [he, ← Measure.map_prod_map μ volume hbase measurable_id, Measure.map_id]

/-- Two volume disintegrations along the same transverse direction have exactly
the same base measure. The proof cancels the real factor on a unit interval. -/
theorem map_base_eq_of_charts
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {ρ : Measure V} {n u : V} {c : ℝ} (ha : ⟪n, u⟫ ≠ 0)
    (base : X → V) (other : Y → V)
    (hb : Measurable base) (ho : Measurable other)
    (hbp : ∀ x, ⟪n, base x⟫ + c = 0)
    (hop : ∀ y, ⟪n, other y⟫ + c = 0)
    (hbc : MeasurePreserving (fun p : X × ℝ => base p.1 + p.2 • u)
      (μ.prod volume) ρ)
    (hoc : MeasurePreserving (fun p : Y × ℝ => other p.1 + p.2 • u)
      (ν.prod volume) ρ) :
    Measure.map base μ = Measure.map other ν := by
  have hp := (map_retract_height_eq_prod ha base hb hbp hbc).symm.trans
    (map_retract_height_eq_prod ha other ho hop hoc)
  ext s hs
  have h := congrArg (fun m : Measure (V × ℝ) => m (s ×ˢ Ioc (0 : ℝ) 1)) hp
  simpa only [Measure.prod_prod, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one,
    mul_one] using h

variable [FiniteDimensional ℝ V]

private theorem measurePreserving_tangent_shear (n : V)
    (w : TangentNormalCoordinates.Tangent n) (a : ℝ) :
    MeasurePreserving
      (fun p : TangentNormalCoordinates.Tangent n × ℝ =>
        (p.1 + (p.2 / a) • w, p.2))
      (volume.prod volume) (volume.prod volume) := by
  have hs : MeasurePreserving
      (fun p : ℝ × TangentNormalCoordinates.Tangent n =>
        (p.1, p.2 + (p.1 / a) • w))
      (volume.prod volume) (volume.prod volume) := by
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun t y => y + (t / a) • w)
    · fun_prop
    · exact Filter.Eventually.of_forall fun t =>
        (measurePreserving_add_right volume ((t / a) • w)).map_eq
  exact Measure.measurePreserving_swap.comp (hs.comp Measure.measurePreserving_swap)

/-- Intrinsic tangent volume, multiplied by the transverse cosine, gives the
full ambient-volume disintegration along an arbitrary non-tangential vector.
This is proved by a tangential shear and one-dimensional scaling only. -/
theorem measurePreserving_oblique_chart (n u b : V)
    (hn : n ≠ 0) (hu : ⟪n, u⟫ ≠ 0) :
    MeasurePreserving
      (fun p : TangentNormalCoordinates.Tangent n × ℝ => b + (p.1 : V) + p.2 • u)
      ((ENNReal.ofReal |⟪n, u⟫ / ‖n‖| • volume).prod volume) volume := by
  let a : ℝ := ⟪n, u⟫ / ‖n‖
  let v : V := (‖n‖⁻¹ : ℝ) • n
  have hn' : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have ha : a ≠ 0 := div_ne_zero hu hn'
  have hv : ⟪n, v⟫ = ‖n‖ := by
    dsimp [v]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hw : u - a • v ∈ TangentNormalCoordinates.Tangent n := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right, inner_smul_right, hv]
    dsimp [a]
    rw [div_mul_cancel₀ _ hn', sub_self]
  let w : TangentNormalCoordinates.Tangent n := ⟨u - a • v, hw⟩
  have hscale : MeasurePreserving (fun t : ℝ => a * t)
      (ENNReal.ofReal |a| • volume) volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_smul]
    exact Real.smul_map_volume_mul_left ha
  have hp := (MeasurePreserving.id
    (volume : Measure (TangentNormalCoordinates.Tangent n))).prod hscale
  have hcomp := (TangentNormalCoordinates.measurePreserving_tangentMap n hn b).comp
    ((measurePreserving_tangent_shear n w a).comp hp)
  have he : (TangentNormalCoordinates.tangentMap n b) ∘
      (fun p : TangentNormalCoordinates.Tangent n × ℝ =>
        (p.1 + (p.2 / a) • w, p.2)) ∘ Prod.map id (fun t : ℝ => a * t) =
      (fun p : TangentNormalCoordinates.Tangent n × ℝ => b + (p.1 : V) + p.2 • u) := by
    funext p
    simp only [Function.comp_apply,
      TangentNormalCoordinates.tangentMap, TangentNormalCoordinates.affineMap,
      TangentNormalCoordinates.normalMap, Submodule.coe_add, Submodule.coe_smul]
    change b + ((a * p.2) • v + ((p.1 : V) + ((a * p.2) / a) • (u - a • v))) = _
    rw [mul_div_cancel_left₀ p.2 ha]
    module
  rw [he] at hcomp
  simpa only [Measure.prod_smul_left, Measure.prod_smul_right, a] using hcomp

/-- Exact intrinsic surface Jacobian for any product-preserving transverse
chart. This holds for arbitrary measurable base parameterizations. -/
theorem map_base_eq_smul_hyperplaneMeasure
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {n u : V} {c : ℝ} (hn : n ≠ 0) (hu : ⟪n, u⟫ ≠ 0)
    (base : X → V) (hb : Measurable base)
    (hplane : ∀ x, ⟪n, base x⟫ + c = 0)
    (hchart : MeasurePreserving (fun p : X × ℝ => base p.1 + p.2 • u)
      (μ.prod volume) volume) :
    Measure.map base μ = ENNReal.ofReal |⟪n, u⟫ / ‖n‖| •
      IntrinsicSurface.hyperplaneMeasure n c := by
  let b : V := IntrinsicSurface.normalBase n c
  have hbplane : ⟪n, b⟫ + c = 0 := by
    rw [IntrinsicSurface.inner_normalBase hn]
    ring
  have hp := map_base_eq_of_charts (ρ := volume) hu base
    (fun w : TangentNormalCoordinates.Tangent n => b + (w : V)) hb (by fun_prop)
    hplane (fun w => by
      rw [inner_add_right,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property]
      simpa using hbplane)
    hchart (measurePreserving_oblique_chart n u b hn hu)
  rw [Measure.map_smul] at hp
  exact hp

/-- Equality of positively oriented normalized face integrals. The theorem
includes vector-valued weights and needs neither compact cells nor positivity
of their volumes. -/
theorem normalized_integral_eq_intrinsic
    {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} [SFinite μ] {n u : V} {c : ℝ}
    (hn : n ≠ 0) (hu : 0 < ⟪n, u⟫)
    (base : X → V) (hb : Measurable base)
    (hplane : ∀ x, ⟪n, base x⟫ + c = 0)
    (hchart : MeasurePreserving (fun p : X × ℝ => base p.1 + p.2 • u)
      (μ.prod volume) volume)
    (f : V → F) (hf : StronglyMeasurable f) :
    ⟪n, u⟫⁻¹ • (∫ x, f (base x) ∂μ) =
      ‖n‖⁻¹ • (∫ x, f x ∂IntrinsicSurface.hyperplaneMeasure n c) := by
  rw [← integral_map hb.aemeasurable hf.aestronglyMeasurable,
    map_base_eq_smul_hyperplaneMeasure hn hu.ne' base hb hplane hchart,
    integral_smul_measure]
  rw [ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (div_pos hu (norm_pos_iff.mpr hn)), smul_smul]
  congr 1
  field_simp

end Problem358.TransverseSurface

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical first-moment coefficients of common affine-cell faces. -/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- A common cell face is exactly one closed cell restricted to the tie plane. -/
theorem mem_commonFace_iff (K : Set (E d)) (y : ι → E d) (c : ι → ℝ)
    (i j : ι) (x : E d) :
    x ∈ closedCell K y c i ∩ closedCell K y c j ↔
      x ∈ closedCell K y c i ∧ ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j := by
  constructor
  · intro hx
    exact ⟨hx.1, le_antisymm (hx.2.2 i) (hx.1.2 j)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, hx.1, fun k => heq ▸ hx.2 k⟩

/-- On the tie plane only the other branches constrain the common face. -/
theorem mem_commonFace_iff_of_tie (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i j : ι) {x : E d}
    (htie : ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j) :
    x ∈ closedCell K y c i ∩ closedCell K y c j ↔
      x ∈ K ∧ ∀ k, k ≠ i → k ≠ j → ⟪x, y k⟫ + c k ≤ ⟪x, y i⟫ + c i := by
  rw [mem_commonFace_iff]
  constructor
  · rintro ⟨hx, _⟩
    exact ⟨hx.1, fun k _ _ => hx.2 k⟩
  · rintro ⟨hx, hother⟩
    refine ⟨⟨hx, fun k => ?_⟩, htie⟩
    by_cases hki : k = i
    · subst k
      exact le_rfl
    by_cases hkj : k = j
    · subst k
      exact htie.ge
    exact hother k hki hkj

theorem faceMoment_symm (K : Set (E d)) (y : ι → E d) (c : ι → ℝ)
    (i j : ι) : faceMoment K y c i j = faceMoment K y c j i := by
  exact (IntrinsicSurface.normalized_face_integral_swap (y i) (y j)
    (c i) (c j) (volume K).toReal (closedCell K y c i)
    (closedCell K y c j) (fun x => x)).symm

end Problem358.CellGeometry

end

/-! Identification of the cut-product trace with the genuine common cell face. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- On an equality plane the remaining cut indicators describe exactly the
common face, including its boundary. -/
theorem commonFace_indicator_eq_cut_product (K : Set (E d))
    (y : ι → E d) (c : ι → ℝ) (i j : ι) (J : Finset ι)
    (hJ : ∀ k, k ∈ J ↔ k ≠ i ∧ k ≠ j) (f : E d → ℝ) {x : E d}
    (htie : ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j) :
    (closedCell K y c i ∩ closedCell K y c j).indicator f x =
      K.indicator f x * ∏ k ∈ J,
        MovingCellTrace.cutIndicator (⟪x, y i - y k⟫ + (c i - c k)) := by
  classical
  have hcut (k : ι) :
      MovingCellTrace.cutIndicator (⟪x, y i - y k⟫ + (c i - c k)) =
        if ⟪x, y k⟫ + c k ≤ ⟪x, y i⟫ + c i then 1 else 0 := by
    have hle : 0 ≤ ⟪x, y i - y k⟫ + (c i - c k) ↔
        ⟪x, y k⟫ + c k ≤ ⟪x, y i⟫ + c i := by
      rw [inner_sub_right]
      constructor <;> intro h <;> linarith
    simp only [MovingCellTrace.cutIndicator, Set.indicator_apply, Set.mem_Ici, hle]
  by_cases hx : x ∈ closedCell K y c i ∩ closedCell K y c j
  · have hp : (∏ k ∈ J,
        MovingCellTrace.cutIndicator (⟪x, y i - y k⟫ + (c i - c k))) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      rw [hcut, ite_eq_left (hx.1.2 k)]
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx.1.1, hp, mul_one]
  · rw [Set.indicator_of_notMem hx]
    by_cases hxK : x ∈ K
    · have hnot : ¬ ∀ k ∈ J, ⟪x, y k⟫ + c k ≤ ⟪x, y i⟫ + c i := by
        intro hall
        apply hx
        apply (mem_commonFace_iff_of_tie K y c i j htie).2
        exact ⟨hxK, fun k hki hkj => hall k ((hJ k).2 ⟨hki, hkj⟩)⟩
      push Not at hnot
      obtain ⟨k, hk, hbad⟩ := hnot
      have hp : (∏ k ∈ J,
          MovingCellTrace.cutIndicator (⟪x, y i - y k⟫ + (c i - c k))) = 0 := by
        apply Finset.prod_eq_zero hk
        rw [hcut, ite_eq_right (not_le_of_gt hbad)]
      rw [hp, mul_zero]
    · rw [Set.indicator_of_notMem hxK, zero_mul]

/-- Translating a tangent vector preserves the affine equality. -/
theorem tie_on_tangent_chart (y : ι → E d) (c : ι → ℝ) (i j : ι)
    {z : E d} (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (w : (ℝ ∙ (y i - y j))ᗮ) :
    ⟪z + (w : E d), y i⟫ + c i = ⟪z + (w : E d), y j⟫ + c j := by
  have hw : ⟪y i - y j, (w : E d)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  have hw' : ⟪(w : E d), y i⟫ - ⟪(w : E d), y j⟫ = 0 := by
    rw [← inner_sub_right, real_inner_comm]
    exact hw
  simp only [inner_add_left]
  linarith

/-- The scalar face integral in a moving-cut formula is the canonical intrinsic
integral over the common cell face. No boundary or third-tie exception is needed
for this exact identification. -/
theorem interface_integral_eq_cut_trace {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) {i j : ι} (hy : y i ≠ y j)
    (J : Finset ι) (hJ : ∀ k, k ∈ J ↔ k ≠ i ∧ k ≠ j)
    (f : E d → ℝ) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j) :
    (∫ x in closedCell K y c i ∩ closedCell K y c j, f x
      ∂IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)) =
      ∫ w : (ℝ ∙ (y i - y j))ᗮ,
        K.indicator f (z + (w : E d)) * ∏ k ∈ J,
          MovingCellTrace.cutIndicator
            (⟪z + (w : E d), y i - y k⟫ + (c i - c k)) := by
  classical
  rw [IntrinsicSurface.interfaceMeasure_setIntegral_of_tie hy
    (by simpa only [real_inner_comm] using htie)]
  have hmeas : MeasurableSet {w : (ℝ ∙ (y i - y j))ᗮ |
      z + (w : E d) ∈ closedCell K y c i ∩ closedCell K y c j} := by
    apply ((isClosed_closedCell hK y c i).inter
      (isClosed_closedCell hK y c j)).measurableSet.preimage
    fun_prop
  rw [← integral_indicator hmeas]
  apply integral_congr_ae
  filter_upwards [] with w
  have h := commonFace_indicator_eq_cut_product K y c i j J hJ f
    (tie_on_tangent_chart y c i j htie w)
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h

end Problem358.CellGeometry

/-! The actual moving-cut derivative expressed by canonical intrinsic faces. -/

namespace Problem358.PositiveCellFullDerivative

open CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cut derivative is intrinsically defined and independent of the chosen
tie-plane basepoint. This identity holds for every scalar weight. -/
theorem faceVariation_eq_intrinsic {K : Set (E d)} (hK : IsClosed K)
    (y v : ι → E d) (c r : ι → ℝ) (w : E d → ℝ)
    {i j : ι} (hy : y i ≠ y j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j) :
    faceVariation K y v c r w i j z =
      ∫ x in closedCell K y c i ∩ closedCell K y c j,
        ((r i - r j + ⟪v i - v j, x⟫) / ‖y i - y j‖) * w x
        ∂IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j) := by
  rw [interface_integral_eq_cut_trace hK y c hy ((Finset.univ.erase i).erase j)
    (by intro k; simp only [Finset.mem_erase, Finset.mem_univ, and_true]; tauto)
    _ htie]
  unfold faceVariation
  apply integral_congr_ae
  filter_upwards [] with a
  have hscore (k : ι) :
      ⟪z + (a : E d), y i - y k⟫ + (c i - c k) =
        (⟪z + (a : E d), y i⟫ + c i) -
          (⟪z + (a : E d), y k⟫ + c k) := by
    rw [inner_sub_right]
    ring
  simp_rw [hscore]
  by_cases ha : z + (a : E d) ∈ K
  · simp only [Set.indicator_of_mem ha]
    ring
  · simp only [Set.indicator_of_notMem ha, zero_mul, mul_zero]

/-- The mass face contribution equals the scalar and first-moment coefficients
with the exact source-volume normalization. No positive-volume cancellation is
needed in this algebraic identity. -/
theorem normalized_faceVariation_one {K : Set (E d)} (hK : IsCompact K)
    (y v : ι → E d) (c r : ι → ℝ) {i j : ι} (hy : y i ≠ y j)
    {z : E d} (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j) :
    (volume K).toReal⁻¹ * faceVariation K y v c r (fun _ => 1) i j z =
      (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
        (closedCell K y c i ∩ closedCell K y c j)).toReal /
          ((volume K).toReal * ‖y i - y j‖) * (r i - r j) +
        ⟪faceMoment K y c i j, v i - v j⟫ := by
  let S := closedCell K y c i ∩ closedCell K y c j
  let μ := IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
  have hS : IsCompact S := (isCompact_closedCell hK y c i).inter
    (isCompact_closedCell hK y c j)
  have hid : IntegrableOn (fun x : E d => x) S μ :=
    IntrinsicSurface.integrableOn_interfaceMeasure _ _ _ _ hS continuous_id.continuousOn
  have hc : IntegrableOn (fun _ : E d => r i - r j) S μ :=
    IntrinsicSurface.integrableOn_interfaceMeasure _ _ _ _ hS continuous_const.continuousOn
  rw [faceVariation_eq_intrinsic hK.isClosed y v c r (fun _ => 1) hy htie]
  simp only [mul_one]
  change (volume K).toReal⁻¹ *
      (∫ x in S, (r i - r j + ⟪v i - v j, x⟫) / ‖y i - y j‖ ∂μ) = _
  rw [integral_div, integral_add hc (hid.const_inner (v i - v j)),
    integral_const, integral_inner hid]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  unfold faceMoment
  rw [inner_smul_left, real_inner_comm (v i - v j)]
  simp only [starRingEnd_apply, star_trivial]
  dsimp only [S, μ]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

end Problem358.PositiveCellFullDerivative

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_FaceContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.AffinePlaneGraph

variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma inner_unitNormal (n : E d) (hn : n ≠ 0) :
    ⟪n, unitNormal n⟫ = ‖n‖ := by
  rw [unitNormal, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

lemma continuous_tangentProjection (n z : E d) :
    Continuous (tangentProjection n z) :=
  (ℝ ∙ n)ᗮ.orthogonalProjectionOnto.continuous.comp (continuous_id.sub continuous_const)

lemma tangentProjection_add (n z : E d) (x : (ℝ ∙ n)ᗮ) (t : ℝ) :
    tangentProjection n z (z + (x : E d) + t • unitNormal n) = x := by
  have he : z + (x : E d) + t • unitNormal n - z =
      (x : E d) + t • unitNormal n := by abel
  unfold tangentProjection
  rw [he]
  simp only [map_add, map_smul,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, unitNormal,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    smul_zero, add_zero]

end Problem358.AffinePlaneGraph

end

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace Problem358.MovingCellTrace

/-- Weighted face coefficients vary continuously for positive affine cells,
expressed in any nearby-plane chart preserving a fixed transverse projection.
The compact source supplies domination; positivity supplies all surface nullity. -/
theorem tendsto_positive_cell_face_integral_of_tie
    {d : ℕ} {ι α : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure]
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {P : E d → (ℝ ∙ (y i - y j))ᗮ} (hP : Continuous P)
    {chart : α → ((ℝ ∙ (y i - y j))ᗮ) → E d}
    (hproject : ∀ q p, P (chart q p) = p)
    (hchartmeas : ∀ q, Measurable (chart q))
    (hchartlim : ∀ᵐ p : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      Tendsto (fun q => chart q p) l (𝓝 (z + (p : E d))))
    {w : E d → ℝ} (hwmeas : Measurable w) (hwcont : ContinuousOn w K)
    {a : α → ι → E d} {b : α → ι → ℝ}
    (ha : ∀ k ∈ J, Tendsto (fun q => a q k) l (𝓝 (y i - y k)))
    (hb : ∀ k ∈ J, Tendsto (fun q => b q k) l (𝓝 (c i - c k))) :
    Tendsto (fun q => ∫ p, K.indicator w (chart q p) * ∏ k ∈ J,
      cutIndicator (⟪chart q p, a q k⟫ + b q k) ∂μ) l
      (𝓝 (∫ p, K.indicator w (z + (p : E d)) * ∏ k ∈ J,
        cutIndicator (⟪z + (p : E d), y i - y k⟫ + (c i - c k)) ∂μ)) := by
  refine tendsto_integral_remainder_of_compact_projection
    (α := α) (X := (ℝ ∙ (y i - y j))ᗮ) (V := E d) (l := l) (μ := μ)
    (s := fun q v k => ⟪v, a q k⟫ + b q k)
    (b := fun p k => ⟪z + (p : E d), y i - y k⟫ + (c i - c k))
    J hK hP hproject hchartmeas hchartlim hwmeas hwcont ?_ ?_ ?_
  · intro q k _
    exact (continuous_id.inner continuous_const).measurable.add measurable_const
  · filter_upwards [hchartlim] with p hp
    intro k hk
    exact (hp.inner (ha k hk)).add (hb k hk)
  · filter_upwards [CellGeometry.ae_regular_interface_of_tie hρ hK.isClosed hconv y c hy
      hpos hij htie μ] with p hp
    refine ⟨hp.1, ?_⟩
    intro k hk heq
    apply hp.2 k (hJ k hk).1 (hJ k hk).2
    rw [inner_sub_right] at heq
    linarith

end Problem358.MovingCellTrace

namespace Problem358.AffinePlaneGraph

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Continuity of actual weighted positive-cell face coefficients, with the
nearby charts, compact domination, and surface nullity all furnished internally.
Only the reference configuration needs positive cells. -/
theorem tendsto_faceCoefficient_of_tie
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : Continuous w)
    {a : α → ι → E d} {b : α → ι → ℝ}
    (ha : ∀ k, Tendsto (fun q => a q k) l (𝓝 (y k)))
    (hb : ∀ k, Tendsto (fun q => b q k) l (𝓝 (c k))) :
    Tendsto (fun q => faceCoefficient K (y i - y j) z J i j w (a q, b q)) l
      (𝓝 (faceCoefficient K (y i - y j) z J i j w (y, c))) := by
  let n₀ := y i - y j
  let base : (ℝ ∙ n₀)ᗮ → E d := fun x => z + (x : E d)
  have hn : n₀ ≠ 0 := sub_ne_zero.mpr (hy.ne hij)
  have htrans : ⟪n₀, unitNormal n₀⟫ ≠ 0 := by
    rw [inner_unitNormal n₀ hn]
    exact norm_ne_zero_iff.mpr hn
  have hface : ∀ x : (ℝ ∙ n₀)ᗮ, ⟪n₀, base x⟫ + (c i - c j) = 0 := by
    intro x
    have hx : ⟪n₀, (x : E d)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
    simp only [base, inner_add_right, hx, add_zero, n₀, inner_sub_left]
    rw [real_inner_comm z (y i), real_inner_comm z (y j)]
    linarith
  have hlim : ∀ᵐ x : (ℝ ∙ n₀)ᗮ ∂volume,
      Tendsto (fun q => interfaceGraph n₀ z (a q) (b q) i j x) l (𝓝 (base x)) := by
    exact Eventually.of_forall fun x =>
      tendsto_graph_base (unitNormal n₀) ((ha i).sub (ha j))
        ((hb i).sub (hb j)) htrans hface x
  have hi := MovingCellTrace.tendsto_positive_cell_face_integral_of_tie
    hρ hK hconv y c hy hpos hij htie volume J hJ
    (continuous_tangentProjection n₀ z)
    (fun q x => projection_graph base (unitNormal n₀) (a q i - a q j)
      (b q i - b q j) (tangentProjection n₀ z) (tangentProjection_add n₀ z) x)
    (fun q => measurable_graph base (by fun_prop) (unitNormal n₀)
      (a q i - a q j) (b q i - b q j))
    hlim hw.measurable hw.continuousOn
    (fun k _ => (ha i).sub (ha k)) (fun k _ => (hb i).sub (hb k))
  have hden : Tendsto (fun q => ⟪a q i - a q j, unitNormal n₀⟫) l
      (𝓝 ⟪n₀, unitNormal n₀⟫) :=
    ((ha i).sub (ha j)).inner tendsto_const_nhds
  have heq : ∀ x, interfaceGraph n₀ z y c i j x = base x :=
    graph_eq_base base (unitNormal n₀) n₀ (c i - c j) hface
  change Tendsto (fun q => faceCoefficient K n₀ z J i j w (a q, b q)) l
    (𝓝 (faceCoefficient K n₀ z J i j w (y, c)))
  simp only [faceCoefficient, heq]
  exact hi.div hden htrans

/-- Local continuity on the full joint site/intercept parameter space. -/
theorem continuousAt_faceCoefficient_of_tie
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d}
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : Continuous w) :
    ContinuousAt (faceCoefficient K (y i - y j) z J i j w) (y, c) := by
  exact tendsto_faceCoefficient_of_tie hρ hK hconv y c hy hpos hij htie J hJ hw
    (fun k => (continuous_apply k |>.comp continuous_fst).tendsto (y, c))
    (fun k => (continuous_apply k |>.comp continuous_snd).tendsto (y, c))

end Problem358.AffinePlaneGraph

end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.AffinePlaneGraph

variable {d : ℕ} {ι : Type*}

/-- The fixed transverse coefficient equals the intrinsic coefficient throughout
the neighborhood where the transverse orientation stays positive. -/
theorem faceCoefficient_eq_intrinsicCutCoefficient
    {K : Set (E d)} (hK : MeasurableSet K) (n₀ z : E d) (hn₀ : n₀ ≠ 0)
    (J : Finset ι) (i j : ι) (w : E d → ℝ) (hw : Measurable w)
    (p : (ι → E d) × (ι → ℝ))
    (htrans : 0 < ⟪p.1 i - p.1 j, unitNormal n₀⟫) :
    faceCoefficient K n₀ z J i j w p = intrinsicCutCoefficient K J i j w p := by
  let n := p.1 i - p.1 j
  let c := p.2 i - p.2 j
  let base : (ℝ ∙ n₀)ᗮ → E d := fun x => z + (x : E d)
  have hn : n ≠ 0 := by
    intro he
    have he' : ⟪n, unitNormal n₀⟫ = 0 := by rw [he, inner_zero_left]
    exact (ne_of_gt htrans) he'
  have hbase : Measurable base := by fun_prop
  have hchart₀ : MeasurePreserving
      (fun q : (ℝ ∙ n₀)ᗮ × ℝ => base q.1 + q.2 • unitNormal n₀)
      (volume.prod volume) volume := by
    convert TangentNormalCoordinates.measurePreserving_tangentMap n₀ hn₀ z using 1
    all_goals try with_reducible_and_instances rfl
    funext q
    simp only [base, unitNormal, TangentNormalCoordinates.tangentMap,
      TangentNormalCoordinates.affineMap, TangentNormalCoordinates.normalMap]
    abel
  have hchart := measurePreserving_graph_chart base hbase (unitNormal n₀) n c hchart₀
  let f : E d → ℝ := fun x => K.indicator w x * ∏ k ∈ J,
    MovingCellTrace.cutIndicator (⟪x, p.1 i - p.1 k⟫ + (p.2 i - p.2 k))
  have hf : Measurable f := MovingCellTrace.measurable_remainder J hK hw
    (fun _ _ => by fun_prop)
  have he := TransverseSurface.normalized_integral_eq_intrinsic hn htrans
    (graph base (unitNormal n₀) n c) (measurable_graph base hbase _ _ _)
    (inner_graph_add base (unitNormal n₀) n c htrans.ne') hchart f hf.stronglyMeasurable
  change (∫ x : (ℝ ∙ n₀)ᗮ, f (graph base (unitNormal n₀) n c x)) /
      ⟪n, unitNormal n₀⟫ =
    (∫ x, f x ∂IntrinsicSurface.hyperplaneMeasure n c) / ‖n‖
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using he

/-- Actual intrinsic face coefficients are continuous in all sites and
intercepts at each positive-cell configuration. No choice of a moving frame,
Jacobian, exceptional set, or local derivative field is left as a hypothesis. -/
theorem continuousAt_intrinsicCutCoefficient [Fintype ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j)
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : Continuous w) :
    ContinuousAt (intrinsicCutCoefficient K J i j w) (y, c) := by
  let n₀ := y i - y j
  let z := IntrinsicSurface.normalBase n₀ (c i - c j)
  have hn : n₀ ≠ 0 := sub_ne_zero.mpr (hy.ne hij)
  have htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j := by
    have he := IntrinsicSurface.inner_normalBase hn (c i - c j)
    change ⟪n₀, z⟫ = -(c i - c j) at he
    dsimp [n₀] at he
    rw [inner_sub_left, real_inner_comm z (y i), real_inner_comm z (y j)] at he
    linarith
  have hc := continuousAt_faceCoefficient_of_tie hρ hK hconv y c hy hpos hij
    htie J hJ hw
  have hden : ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      ⟪p.1 i - p.1 j, unitNormal n₀⟫) (y, c) := by fun_prop
  have htrans : 0 < ⟪n₀, unitNormal n₀⟫ := by
    rw [inner_unitNormal n₀ hn]
    exact norm_pos_iff.mpr hn
  apply hc.congr_of_eventuallyEq
  filter_upwards [hden.eventually (eventually_gt_nhds htrans)] with p hp
  exact (faceCoefficient_eq_intrinsicCutCoefficient hK.measurableSet n₀ z hn
    J i j w hw.measurable p hp).symm

end Problem358.AffinePlaneGraph

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_FacetConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connectivity of finite closed covers and active-cell intersection graphs. -/

noncomputable section
open Set

namespace Problem358

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

/-- Any two nonempty members of a finite closed cover of a preconnected set
are joined by a chain of nonempty intersections. Empty cover members are harmless. -/
theorem closedCoverGraph_reachable (s : ι → Set X)
    (hclosed : ∀ i, IsClosed (s i)) (hconn : IsPreconnected (⋃ i, s i))
    (i j : ι) (hi : (s i).Nonempty) (hj : (s j).Nonempty) :
    (closedCoverGraph s).Reachable i j := by
  classical
  let G := closedCoverGraph s
  by_contra hij
  let U : Set X := ⋃ k : {k : ι // G.Reachable i k}, s k
  let V : Set X := ⋃ k : {k : ι // ¬ G.Reachable i k}, s k
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun k => hclosed k)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun k => hclosed k)
  have hcover : (⋃ k, s k) ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hik : G.Reachable i k
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k, hik⟩, hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hik⟩, hk⟩)
  have hUne : ((⋃ k, s k) ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := hi
    exact ⟨x, mem_iUnion.mpr ⟨i, hx⟩,
      mem_iUnion.mpr ⟨⟨i, SimpleGraph.Reachable.refl i⟩, hx⟩⟩
  have hVne : ((⋃ k, s k) ∩ V).Nonempty := by
    obtain ⟨x, hx⟩ := hj
    exact ⟨x, mem_iUnion.mpr ⟨j, hx⟩, mem_iUnion.mpr ⟨⟨j, hij⟩, hx⟩⟩
  obtain ⟨x, _, hxU, hxV⟩ :=
    isPreconnected_closed_iff.mp hconn U V hU hV hcover hUne hVne
  obtain ⟨⟨k, hk⟩, hxk⟩ := mem_iUnion.mp hxU
  obtain ⟨⟨l, hl⟩, hxl⟩ := mem_iUnion.mp hxV
  apply hl
  by_cases hkl : k = l
  · exact hkl ▸ hk
  · have hedge : G.Adj k l := ⟨hkl, ⟨x, hxk, hxl⟩⟩
    exact hk.trans hedge.reachable

namespace ClosedCoverConnectivity

omit [Finite ι] in
lemma maximalCell_isClosed (K : Set X) (hK : IsClosed K)
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (i : ι) :
    IsClosed (maximalCell K f i) := by
  have heq : maximalCell K f i = K ∩ ⋂ j, {x | f j x ≤ f i x} := by
    ext x
    simp [maximalCell]
  rw [heq]
  exact hK.inter (isClosed_iInter (fun j => isClosed_le (hf j) (hf i)))

omit [TopologicalSpace X] in
lemma iUnion_maximalCell [Nonempty ι] (K : Set X) (f : ι → X → ℝ) :
    (⋃ i, maximalCell K f i) = K := by
  classical
  let := Fintype.ofFinite ι
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hi.1
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => f i x)
      Finset.univ_nonempty
    exact mem_iUnion.mpr ⟨i, hx, fun j => hi j (Finset.mem_univ j)⟩

end ClosedCoverConnectivity

end Problem358

end

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Problem358

/-- A persistent tie which strictly dominates every other score is a positive
measure face whenever the parameter point maps into the interior of the source.
Only topology and positivity of nonempty open sets are needed. -/
theorem measure_face_pos_of_strict_tie
    {X W ι : Type*} [TopologicalSpace X] [TopologicalSpace W]
    [MeasurableSpace W] [Finite ι]
    (μ : Measure W) [Measure.IsOpenPosMeasure μ]
    (φ : W → X) (hφ : Continuous φ) (score : ι → X → ℝ)
    (hs : ∀ k, Continuous (score k)) (K : Set X) (z : W) (i j : ι)
    (hz : φ z ∈ interior K)
    (htie : ∀ w, score i (φ w) = score j (φ w))
    (hstrict : ∀ k, k ≠ i → k ≠ j → score k (φ z) < score i (φ z)) :
    0 < μ {w | φ w ∈ K ∧ score i (φ w) = score j (φ w) ∧
      ∀ k, score k (φ w) ≤ score i (φ w)} := by
  classical
  apply μ.measure_pos_of_mem_nhds (x := z)
  have hK : ∀ᶠ w in 𝓝 z, φ w ∈ K :=
    hφ.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hz)
  have hall : ∀ᶠ w in 𝓝 z,
      ∀ k, k ≠ i → k ≠ j → score k (φ w) < score i (φ w) := by
    apply Filter.eventually_all.mpr
    intro k
    by_cases hki : k = i
    · exact Filter.Eventually.of_forall fun w hk _ => (hk hki).elim
    by_cases hkj : k = j
    · exact Filter.Eventually.of_forall fun w _ hk => (hk hkj).elim
    have hklt : ∀ᶠ w in 𝓝 z, score k (φ w) < score i (φ w) :=
      (isOpen_lt ((hs k).comp hφ) ((hs i).comp hφ)).mem_nhds (hstrict k hki hkj)
    exact hklt.mono fun w hw _ _ => hw
  filter_upwards [hK, hall] with w hw hws
  refine ⟨hw, htie w, fun k => ?_⟩
  by_cases hki : k = i
  · subst k
    exact le_rfl
  by_cases hkj : k = j
  · subst k
    exact (htie w).symm.le
  exact (hws k hki hkj).le

end Problem358

end

/-! Connectivity through strict two-cell interfaces. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Problem358.PositiveFacet

variable {V W ι : Type*} [TopologicalSpace V] [TopologicalSpace W] [Finite ι]

/-- A connected closed parameter domain without triple ties generates a chain
of strict two-cell interfaces between any two active endpoint labels. Empty
cells on this particular path do not cause an obstruction. -/
theorem strictTieGraph_reachable_of_parametric
    (K : Set V) (f : ι → V → ℝ) (hf : ∀ i, Continuous (f i))
    (s : Set W) (hs : IsClosed s) (hconn : IsPreconnected s)
    (a : W → V) (ha : Continuous a)
    (hK : ∀ t ∈ s, a t ∈ interior K)
    (htriple : ∀ t ∈ s, ∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      f i (a t) = f j (a t) → f i (a t) ≠ f k (a t))
    (i j : ι) (ti tj : W) (hti : ti ∈ s) (htj : tj ∈ s)
    (hi : ∀ k, f k (a ti) ≤ f i (a ti))
    (hj : ∀ k, f k (a tj) ≤ f j (a tj)) :
    (strictTieGraph K f).Reachable i j := by
  let : Nonempty ι := ⟨i⟩
  let cells := ClosedCoverConnectivity.maximalCell s (fun k => f k ∘ a)
  have hclosed : ∀ k, IsClosed (cells k) := fun k =>
    ClosedCoverConnectivity.maximalCell_isClosed s hs _ (fun k => (hf k).comp ha) k
  have hcover : (⋃ k, cells k) = s :=
    ClosedCoverConnectivity.iUnion_maximalCell s _
  have hpath : (closedCoverGraph cells).Reachable i j :=
    closedCoverGraph_reachable cells hclosed (hcover ▸ hconn) i j
      ⟨ti, hti, hi⟩ ⟨tj, htj, hj⟩
  apply SimpleGraph.Reachable.mono (Guv := hpath)
  rintro k l ⟨hkl, t, htk, htl⟩
  have heq : f k (a t) = f l (a t) := le_antisymm (htl.2 k) (htk.2 l)
  refine ⟨hkl, a t, hK t htk.1, heq, ?_⟩
  intro m hmk hml
  exact lt_of_le_of_ne (htk.2 m) (Ne.symm (htriple t htk.1 k l m hkl hmk hml heq))

end Problem358.PositiveFacet

end

/-! Connectivity of the strict-facet graph of an active affine partition. -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology InnerProductSpace

namespace Problem358.PositiveFacet

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Finite ι] [Nonempty ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Finite ι] [Nonempty ι] in
private lemma score_difference (y : ι → E) (c : ι → ℝ) (i j : ι) (x : E) :
    GenericSegment.affineScore (y i - y j) (c i - c j) x =
      TripleCell.score (y i) (c i) x - TripleCell.score (y j) (c j) x := by
  simp only [GenericSegment.affineScore, TripleCell.score, inner_sub_left,
    real_inner_comm (y i) x, real_inner_comm (y j) x]
  ring

/-- Every strictly active affine label is connected to every other by interior
two-cell ties. The proof chooses an actual generic segment avoiding all triple
ties, then applies finite closed-cover connectivity along that segment. -/
theorem affine_strictTieGraph_connected
    (μ : Measure E) [IsAddHaarMeasure μ]
    (K : Set E) (hK : Convex ℝ K) (y : ι → E) (c : ι → ℝ)
    (hactive : ∀ i, ∃ x ∈ interior K, ∀ j, j ≠ i →
      TripleCell.score (y j) (c j) x < TripleCell.score (y i) (c i) x) :
    (strictTieGraph K (fun i => TripleCell.score (y i) (c i))).Connected := by
  classical
  let f : ι → E → ℝ := fun i => TripleCell.score (y i) (c i)
  have hf : ∀ i, Continuous (f i) := by
    intro i
    exact (continuous_id.inner continuous_const).add continuous_const
  have hy : Function.Injective y := by
    intro i j heq
    by_contra hij
    obtain ⟨x, _, hx⟩ := hactive i
    obtain ⟨z, _, hz⟩ := hactive j
    have hxi := hx j (fun h => hij h.symm)
    have hzj := hz i hij
    simp only [TripleCell.score, heq] at hxi hzj
    linarith
  let U : ι → Set E := fun i => {x | x ∈ interior K ∧ ∀ j, j ≠ i → f j x < f i x}
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    simp only [U, ofPred_and, ofPred_forall]
    exact isOpen_interior.inter (isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (hf j) (hf i))
  have hUne : ∀ i, (U i).Nonempty := hactive
  have hae : ∀ᵐ x ∂μ, ∀ i j, i ≠ j → f i x ≠ f j x := by
    filter_upwards [ae_affine_tie_implies_slopes_eq μ y c] with x hx i j hij heq
    exact hij (hy (hx i j heq))
  let T := {t : ι × ι × ι //
    LinearIndependent ℝ ![y t.1 - y t.2.1, y t.1 - y t.2.2]}
  let v : T → E := fun t => y t.1.1 - y t.1.2.1
  let w : T → E := fun t => y t.1.1 - y t.1.2.2
  let a : T → ℝ := fun t => c t.1.1 - c t.1.2.1
  let b : T → ℝ := fun t => c t.1.1 - c t.1.2.2
  refine ⟨fun i j => ?_⟩
  obtain ⟨p, hpU, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    ((hU i).measure_ne_zero μ (hUne i)) (ae_restrict_of_ae hae)
  have hnormal : ∀ t : T, LinearIndependent ℝ ![v t, w t] := fun t => t.2
  have hpfirst : ∀ t : T, GenericSegment.affineScore (v t) (a t) p ≠ 0 := by
    intro t
    have ht : t.1.1 ≠ t.1.2.1 := by
      intro heq
      have hn := t.2.ne_zero (0 : Fin 2)
      simp [heq] at hn
    rw [score_difference]
    exact sub_ne_zero.mpr (hp _ _ ht)
  obtain ⟨q, hqU, hq⟩ := GenericSegment.exists_endpoint_in_open_avoiding_common_zeros
    μ v w a b hnormal hpfirst (hU j) (hUne j)
  have hsegment : segment ℝ p q ⊆ interior K :=
    hK.interior.segment_subset hpU.1 hqU.1
  have htriple : ∀ x ∈ segment ℝ p q, ∀ l m n,
      l ≠ m → n ≠ l → n ≠ m → f l x = f m x → f l x ≠ f n x := by
    intro x hx l m n hlm hnl hnm hlmEq hlnEq
    have hind : LinearIndependent ℝ ![y l - y m, y l - y n] := by
      apply TripleCell.linearIndependent_slopes_of_tie ?_ ?_ ?_ hlmEq hlnEq
      · obtain ⟨z, _, hz⟩ := hactive l
        exact ⟨z, hz m hlm.symm, hz n hnl⟩
      · obtain ⟨z, _, hz⟩ := hactive m
        exact ⟨z, hz l hlm, hz n hnm⟩
      · obtain ⟨z, _, hz⟩ := hactive n
        exact ⟨z, hz l hnl.symm, hz m hnm.symm⟩
    let t : T := ⟨(l, m, n), hind⟩
    apply hq t x hx
    constructor
    · change GenericSegment.affineScore (y l - y m) (c l - c m) x = 0
      rw [score_difference]
      exact sub_eq_zero.mpr hlmEq
    · change GenericSegment.affineScore (y l - y n) (c l - c n) x = 0
      rw [score_difference]
      exact sub_eq_zero.mpr hlnEq
  have hcompact : IsCompact (segment ℝ p q) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  apply strictTieGraph_reachable_of_parametric K f hf
    (segment ℝ p q) hcompact.isClosed (convex_segment p q : Convex ℝ _).isPreconnected
    id continuous_id (fun t ht => hsegment ht) htriple i j p q
    (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  · intro k
    by_cases hki : k = i
    · subst k
      exact le_rfl
    exact (hpU.2 k hki).le
  · intro k
    by_cases hkj : k = j
    · subst k
      exact le_rfl
    exact (hqU.2 k hkj).le

end Problem358.PositiveFacet

end

/-! Positive surface measures on every edge of the connected strict-facet graph. -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped Topology InnerProductSpace

namespace Problem358.PositiveFacet

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Finite ι]

omit [BorelSpace E] in
/-- Strict-facet edges have positive surface measure in a parametrization at
any point of their tie plane. This transfers the local strict-face theorem to
the fixed bases used when defining geometric graph coefficients. -/
theorem strictTieGraph_adj_surfaceFace_pos
    (K : Set E) (y : ι → E) (c : ι → ℝ) {i j : ι}
    (hedge : (strictTieGraph K (fun k => TripleCell.score (y k) (c k))).Adj i j)
    (base : E)
    (hbase : TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [IsOpenPosMeasure μ] :
    0 < μ (surfaceFace K y c i j base) := by
  obtain ⟨_, x, hx, htie, hstrict⟩ := hedge
  have horth : x - base ∈ (ℝ ∙ (y i - y j))ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    simp only [inner_sub_left, inner_sub_right]
    unfold TripleCell.score at htie hbase
    linarith
  let w0 : (ℝ ∙ (y i - y j))ᗮ := ⟨x - base, horth⟩
  have hw0 : base + (w0 : E) = x := by
    change base + (x - base) = x
    abel
  apply measure_face_pos_of_strict_tie μ (fun w => base + (w : E))
    (by fun_prop) (fun k => TripleCell.score (y k) (c k))
    (by intro k; exact (continuous_id.inner continuous_const).add continuous_const)
    K w0 i j
  · simpa only [hw0] using hx
  · intro w
    have hw : ⟪(w : E), y i - y j⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.property
    simp only [inner_sub_right] at hw
    unfold TripleCell.score at hbase ⊢
    simp only [inner_add_left]
    linarith
  · simpa only [hw0] using hstrict

end Problem358.PositiveFacet

end

/-! Positive-mass convex affine partitions have a connected positive-facet graph. -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

namespace Problem358.PositiveFacet

variable {d : ℕ} {ι : Type*} [Finite ι]

omit [Finite ι] in
/-- The intrinsic face domain is exactly the pullback of the intersection of
the two canonical closed cells. -/
theorem surfaceFace_eq_preimage_closedCells
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i j : ι) (base : E d) :
    surfaceFace K y c i j base =
      (fun w : (ℝ ∙ (y i - y j))ᗮ => base + (w : E d)) ⁻¹'
        (CellGeometry.closedCell K y c i ∩ CellGeometry.closedCell K y c j) := by
  ext w
  simp only [surfaceFace, CellGeometry.closedCell, TripleCell.score,
    mem_ofPred_eq, mem_preimage, mem_inter_iff]
  constructor
  · rintro ⟨hK, hij, hi⟩
    exact ⟨⟨hK, hi⟩, hK, fun k => (hi k).trans_eq hij⟩
  · rintro ⟨⟨hK, hi⟩, _, hj⟩
    exact ⟨hK, le_antisymm (hj i) (hi j), hi⟩

omit [Finite ι] in
/-- Compact source cells give compact surface domains in every translated
tangent-plane parametrization. -/
theorem isCompact_surfaceFace
    (K : Set (E d)) (hK : IsCompact K) (y : ι → E d) (c : ι → ℝ)
    (i j : ι) (base : E d) : IsCompact (surfaceFace K y c i j base) := by
  rw [surfaceFace_eq_preimage_closedCells]
  have he : Topology.IsClosedEmbedding
      (fun w : (ℝ ∙ (y i - y j))ᗮ => base + (w : E d)) :=
    (Homeomorph.addLeft base).isClosedEmbedding.comp
      (Submodule.isClosedEmbedding_subtype _ (Submodule.isClosed_orthogonal _))
  exact he.isCompact_preimage
    ((CellGeometry.isCompact_closedCell hK y c i).inter_right
      (CellGeometry.isClosed_closedCell hK.isClosed y c j))

/-- Positivity remains genuine after `ENNReal.toReal`: compactness excludes
an infinite surface measure from being silently converted to zero. -/
theorem strictTieGraph_adj_surfaceFace_real_pos
    (K : Set (E d)) (hK : IsCompact K) (y : ι → E d) (c : ι → ℝ) {i j : ι}
    (hedge : (strictTieGraph K (fun k => TripleCell.score (y k) (c k))).Adj i j)
    (base : E d)
    (hbase : TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ))
    [IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ] :
    0 < (μ (surfaceFace K y c i j base)).toReal := by
  exact ENNReal.toReal_pos (strictTieGraph_adj_surfaceFace_pos K y c hedge base hbase μ).ne'
    (isCompact_surfaceFace K hK y c i j base).measure_ne_top

/-- The coefficient used in the cell Laplacian is positive on every strict
facet edge. Both the source-volume and surface-area `toReal` conversions are
justified by compactness. -/
theorem strictTieGraph_adj_normalized_surface_pos
    (K : Set (E d)) (hK : IsCompact K) (hvol : volume K ≠ 0)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) {i j : ι}
    (hedge : (strictTieGraph K (fun k => TripleCell.score (y k) (c k))).Adj i j)
    (base : E d)
    (hbase : TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ))
    [IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ] :
    0 < (μ (surfaceFace K y c i j base)).toReal /
      ((volume K).toReal * ‖y i - y j‖) := by
  apply div_pos (strictTieGraph_adj_surfaceFace_real_pos K hK y c hedge base hbase μ)
  exact mul_pos (ENNReal.toReal_pos hvol hK.measure_ne_top)
    (norm_pos_iff.mpr (sub_ne_zero.mpr (hy.ne hedge.1)))

/-- No generic-position, no facet positivity, and no strict-activation premise
is left in this connectivity statement: all are consequences of positive cell
masses and absolute continuity of the source. -/
theorem strictTieGraph_connected_of_positive_cells [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0) :
    (strictTieGraph K (fun i => TripleCell.score (y i) (c i))).Connected := by
  apply affine_strictTieGraph_connected volume K hK y c
  intro i
  exact CellGeometry.exists_strict_active_interior_of_mass hρ hK y c hy i (hpos i)

end Problem358.PositiveFacet

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Laplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic facts about the weighted cell-adjacency Laplacian. -/

/-! Implicit-function glue for normalized prescribed cell masses. -/

noncomputable section
open scoped Topology BigOperators ContDiff
open Filter

namespace Problem358

section UniqueImplicit
variable {P Q R : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]

/-- A uniquely specified solution agrees locally with the implicit branch, and so inherits
its regularity. No prior continuity of the selected solution is required. -/
theorem contDiffAt_unique_implicit_solution
    {n : ℕ∞ω} {F : P × Q → R} {s : P → Q} {p : P}
    (hn : n ≠ 0) (hF : ContDiffAt ℝ n F (p, s p))
    (hpartial : (fderiv ℝ F (p, s p) ∘L ContinuousLinearMap.inr ℝ P Q).IsInvertible)
    (hzero : F (p, s p) = 0)
    (hunique : ∀ᶠ x in 𝓝 p, ∀ q, F (x, q) = 0 → q = s x) :
    ContDiffAt ℝ n s p := by
  let ψ := hF.implicitFunction hn hpartial
  have heq : s =ᶠ[𝓝 p] ψ := by
    filter_upwards [hF.eventually_apply_implicitFunction hn hpartial, hunique] with x hx hu
    exact (hu _ (hx.trans hzero)).symm
  exact (hF.contDiffAt_implicitFunction hn hpartial).congr_of_eventuallyEq heq

end UniqueImplicit

namespace CellLaplacian
variable {ι P : Type*} [Fintype ι]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- Invertibility of the intercept partial derivative follows from the connected cell graph. -/
theorem partial_isInvertible_of_laplacian [CompleteSpace P]
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (A : P × normalizedSpace m →L[ℝ] normalizedSpace (fun _ : ι => 1))
    (hA : A ∘L ContinuousLinearMap.inr ℝ P (normalizedSpace m) =
      (normalizedEquiv g hsym hnonneg G hG hpos m hm).toContinuousLinearMap) :
    (A ∘L ContinuousLinearMap.inr ℝ P (normalizedSpace m)).IsInvertible := by
  rw [hA]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The analytic hypothesis on the mass map and the algebraic cell graph together imply
smooth dependence of its uniquely normalized solution on the sites. -/
theorem contDiffAt_normalized_solution
    {n : ℕ∞ω} (hn : n ≠ 0)
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (F : P × normalizedSpace m → normalizedSpace (fun _ : ι => 1))
    (s : P → normalizedSpace m) (p : P)
    (hF : ContDiffAt ℝ n F (p, s p))
    (hA : fderiv ℝ F (p, s p) ∘L ContinuousLinearMap.inr ℝ P (normalizedSpace m) =
      (normalizedEquiv g hsym hnonneg G hG hpos m hm).toContinuousLinearMap)
    (hzero : F (p, s p) = 0)
    (hunique : ∀ᶠ x in 𝓝 p, ∀ q, F (x, q) = 0 → q = s x) :
    ContDiffAt ℝ n s p := by
  exact contDiffAt_unique_implicit_solution hn hF
    (partial_isInvertible_of_laplacian g hsym hnonneg G hG hpos m hm _ hA) hzero hunique

end CellLaplacian
end Problem358

end

noncomputable section
open scoped BigOperators Topology ContDiff

namespace Problem358.CellLaplacian
variable {ι : Type*} [Fintype ι]

/-- The projection fixes all genuine mass variations. -/
theorem zeroSumProjection_eq (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (z : ι → ℝ) (hz : ∑ i, z i = 0) :
    (zeroSumProjection m hm z : ι → ℝ) = z := by
  funext i
  simp [hz]

/-- On probability mass vectors the projected residual is exactly the physical residual. -/
theorem massResidual_coe {P : Type*} (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (M : P × normalizedSpace m → (ι → ℝ)) (x : P × normalizedSpace m)
    (hM : ∑ i, M x i = 1) :
    (massResidual m hm M x : ι → ℝ) = M x - m := by
  apply zeroSumProjection_eq
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, hM, hm, sub_self]

theorem massResidual_eq_zero_iff {P : Type*} (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (M : P × normalizedSpace m → (ι → ℝ)) (x : P × normalizedSpace m)
    (hM : ∑ i, M x i = 1) : massResidual m hm M x = 0 ↔ M x = m := by
  rw [← Subtype.coe_inj, massResidual_coe m hm M x hM]
  change M x - m = 0 ↔ _
  exact sub_eq_zero

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem contDiffAt_massResidual {n : ℕ∞ω} (m : ι → ℝ) (hm : ∑ i, m i = 1)
    {M : P × normalizedSpace m → (ι → ℝ)} {x : P × normalizedSpace m}
    (hM : ContDiffAt ℝ n M x) : ContDiffAt ℝ n (massResidual m hm M) x := by
  exact (zeroSumProjection m hm).contDiff.contDiffAt.comp x (hM.sub contDiffAt_const)

theorem hasFDerivAt_massResidual (m : ι → ℝ) (hm : ∑ i, m i = 1)
    {M : P × normalizedSpace m → (ι → ℝ)} {x : P × normalizedSpace m}
    {A : P × normalizedSpace m →L[ℝ] (ι → ℝ)} (hM : HasFDerivAt M A x) :
    HasFDerivAt (massResidual m hm M) ((zeroSumProjection m hm) ∘L A) x := by
  exact (zeroSumProjection m hm).hasFDerivAt.comp x (hM.sub_const m)

/-- An ordinary coordinate derivative with Laplacian intercept part induces precisely
the normalized continuous linear equivalence used by the implicit function theorem. -/
theorem massResidual_partial_eq
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (A : P × normalizedSpace m →L[ℝ] (ι → ℝ))
    (hA : ∀ q : normalizedSpace m, A (0, q) = apply g q) :
    ((zeroSumProjection m hm) ∘L A) ∘L
        ContinuousLinearMap.inr ℝ P (normalizedSpace m) =
      (normalizedEquiv g hsym hnonneg G hG hpos m hm).toContinuousLinearMap := by
  ext q i
  change (zeroSumProjection m hm (A (0, q)) : ι → ℝ) i = apply g q i
  rw [hA]
  exact congrFun (zeroSumProjection_eq m hm _ (sum_apply g hsym q)) i

end Problem358.CellLaplacian

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CanonicalLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized cell Laplacian with its actual intrinsic geometric weights.

All graph hypotheses in the algebraic inverse theorem are discharged here for
positive-mass convex affine cells. No analytic differentiability assertion is
made: the resulting equivalence is ready to identify with the mass Jacobian.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace BigOperators

namespace Problem358.PositiveFacet

variable {d : ℕ} {ι : Type*}

theorem canonicalFaceWeight_symm (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i j : ι) :
    canonicalFaceWeight K y c i j = canonicalFaceWeight K y c j i := by
  exact (IntrinsicSurface.normalized_face_area_swap (y i) (y j) (c i) (c j)
    (volume K).toReal (CellGeometry.closedCell K y c i)
    (CellGeometry.closedCell K y c j)).symm

theorem canonicalFaceWeight_nonneg (K : Set (E d)) (y : ι → E d)
    (c : ι → ℝ) (i j : ι) : 0 ≤ canonicalFaceWeight K y c i j :=
  div_nonneg ENNReal.toReal_nonneg (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _))

/-- An arbitrary tie-plane chart computes the canonical coefficient. -/
theorem canonicalFaceWeight_eq_chart [Finite ι]
    (K : Set (E d)) (hK : IsCompact K) (y : ι → E d) (c : ι → ℝ)
    {i j : ι} (hy : y i ≠ y j) (base : E d)
    (hbase : TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base) :
    canonicalFaceWeight K y c i j =
      (volume (surfaceFace K y c i j base)).toReal /
        ((volume K).toReal * ‖y i - y j‖) := by
  have hb : ⟪y i, base⟫_ℝ + c i = ⟪y j, base⟫_ℝ + c j := by
    rw [real_inner_comm base (y i), real_inner_comm base (y j)]
    exact hbase
  have hs : MeasurableSet
      (CellGeometry.closedCell K y c i ∩ CellGeometry.closedCell K y c j) :=
    ((CellGeometry.isClosed_closedCell hK.isClosed y c i).inter
      (CellGeometry.isClosed_closedCell hK.isClosed y c j)).measurableSet
  unfold canonicalFaceWeight
  rw [IntrinsicSurface.interfaceMeasure_apply_of_tie hy hb hs,
    surfaceFace_eq_preimage_closedCells]
  rfl

/-- Every strict geometric facet has genuinely positive canonical weight. -/
theorem strictTieGraph_adj_canonicalFaceWeight_pos [Finite ι]
    (K : Set (E d)) (hK : IsCompact K) (hvol : volume K ≠ 0)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) {i j : ι}
    (hedge : (strictTieGraph K (fun k => TripleCell.score (y k) (c k))).Adj i j) :
    0 < canonicalFaceWeight K y c i j := by
  obtain ⟨base, _, hb, _⟩ := hedge.2
  rw [canonicalFaceWeight_eq_chart K hK y c (hy.ne hedge.1) base hb]
  exact strictTieGraph_adj_normalized_surface_pos K hK hvol y c hy hedge base hb volume

/-- Positive cell masses supply all conditions required by the abstract
connected weighted-graph Laplacian API. -/
theorem canonicalFaceWeight_connected [Finite ι] [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0) :
    ∃ G : SimpleGraph ι, G.Connected ∧
      ∀ i j, G.Adj i j → 0 < canonicalFaceWeight K y c i j := by
  have hvol : volume K ≠ 0 := by
    intro hz
    let i : ι := Classical.choice inferInstance
    exact hpos i (hρ (measure_mono_null (CellGeometry.closedCell_subset K y c i) hz))
  exact ⟨strictTieGraph K (fun i => TripleCell.score (y i) (c i)),
    strictTieGraph_connected_of_positive_cells ρ hρ K hconv y c hy hpos,
    fun _ _ hij => strictTieGraph_adj_canonicalFaceWeight_pos K hK hvol y c hy hij⟩

end Problem358.PositiveFacet

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The global intrinsic cut integral is the actual common-face integral. -/
theorem intrinsicCutCoefficient_eq_faceIntegral
    {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) {i j : ι} (hy : y i ≠ y j)
    (w : E d → ℝ) :
    AffinePlaneGraph.intrinsicCutCoefficient K ((Finset.univ.erase i).erase j) i j w
      (y, c) =
      (∫ x in closedCell K y c i ∩ closedCell K y c j, w x
        ∂IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)) / ‖y i - y j‖ := by
  unfold AffinePlaneGraph.intrinsicCutCoefficient
  congr 1
  rw [← integral_indicator ((isClosed_closedCell hK y c i).inter
    (isClosed_closedCell hK y c j)).measurableSet]
  apply integral_congr_ae
  filter_upwards [IntrinsicSurface.ae_interface_tie hy (c i) (c j)] with x hx
  exact (commonFace_indicator_eq_cut_product K y c i j
    ((Finset.univ.erase i).erase j) (by
      intro k
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact and_comm) w hx).symm

/-- Continuity of an arbitrary continuous scalar common-face integral, with the
actual source and normal normalization. -/
theorem continuousAt_normalizedFaceIntegral
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {w : E d → ℝ} (hw : Continuous w) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      (∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, w x
        ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j)) /
          ((volume K).toReal * ‖p.1 i - p.1 j‖)) (y, c) := by
  have hc := (AffinePlaneGraph.continuousAt_intrinsicCutCoefficient hρ hK hconv
    y c hy hpos hij ((Finset.univ.erase i).erase j)
    (by
      intro k hk
      exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,
        (Finset.mem_erase.mp hk).1⟩) hw).div_const (volume K).toReal
  apply hc.congr_of_eventuallyEq
  filter_upwards [_root_.OAI.Problem358.eventually_injective_sites y c hy] with p hp
  rw [intrinsicCutCoefficient_eq_faceIntegral hK.isClosed p.1 p.2 (hp.ne hij) w]
  ring

/-- Canonical normalized face areas vary continuously at positive cells. -/
theorem continuousAt_canonicalFaceWeight
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i j : ι) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      PositiveFacet.canonicalFaceWeight K p.1 p.2 i j) (y, c) := by
  by_cases hij : i = j
  · subst j
    simpa using (continuousAt_const : ContinuousAt (fun _ :
      (ι → E d) × (ι → ℝ) => (0 : ℝ)) (y, c))
  have hc := continuousAt_normalizedFaceIntegral hρ hK hconv y c hy hpos hij
    (w := fun _ => (1 : ℝ)) continuous_const
  simpa only [PositiveFacet.canonicalFaceWeight, integral_const, Measure.real,
    Measure.restrict_apply_univ, smul_eq_mul, mul_one] using hc

/-- Canonical normalized first face moments also vary continuously. -/
theorem continuousAt_faceMoment
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i j : ι) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) => faceMoment K p.1 p.2 i j) (y, c) := by
  by_cases hij : i = j
  · subst j
    simpa using (continuousAt_const : ContinuousAt (fun _ :
      (ι → E d) × (ι → ℝ) => (0 : E d)) (y, c))
  have heq (p : (ι → E d) × (ι → ℝ)) (k : Fin d) :
      faceMoment K p.1 p.2 i j k =
      (∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, x k
        ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j)) /
          ((volume K).toReal * ‖p.1 i - p.1 j‖) := by
    have hi := IntrinsicSurface.integrableOn_interfaceMeasure
      (p.1 i) (p.1 j) (p.2 i) (p.2 j)
      ((isCompact_closedCell hK p.1 p.2 i).inter
        (isCompact_closedCell hK p.1 p.2 j)) continuous_id.continuousOn
    have hp := ((EuclideanSpace.proj k).integral_comp_comm hi).symm
    change ((volume K).toReal * ‖p.1 i - p.1 j‖)⁻¹ *
      (∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, x
        ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j)) k = _
    rw [show (∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, x
      ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j)) k =
      ∫ x in closedCell K p.1 p.2 i ∩ closedCell K p.1 p.2 j, x k
      ∂IntrinsicSurface.interfaceMeasure (p.1 i) (p.1 j) (p.2 i) (p.2 j) by simpa using hp]
    ring
  have hc : ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      fun k : Fin d => faceMoment K p.1 p.2 i j k) (y, c) := by
    apply continuousAt_pi.mpr
    intro k
    simpa only [heq] using continuousAt_normalizedFaceIntegral hρ hK hconv y c hy hpos
      hij (w := fun x => x k) (by fun_prop)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).continuousAt.comp hc

end Problem358.CellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MapDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ : Measure (E d)} {T S U : E d → E d}

@[simp] theorem mapL2Dist_self (ρ : Measure (E d)) (T : E d → E d) :
    mapL2Dist ρ T T = 0 := by
  simp [mapL2Dist]

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Minimizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
variable (ρ : Measure V) [IsProbabilityMeasure ρ]

/-- The actual finite-potential objective attains its normalized minimum. -/
theorem exists_minimum_objective (y : ι → V) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ) :
    ∃ c : ι → ℝ, (∑ i, m i * c i) = 0 ∧
      ∀ b : ι → ℝ, (∑ i, m i * b i) = 0 →
        objective ρ y m c ≤ objective ρ y m b := by
  apply exists_minimum_on_normalized_intercepts m hm hsum (objective ρ y m)
    (continuous_objective ρ y m L hy hρ) ((L : ℝ) * ∫ x, ‖x‖ ∂ρ)
  intro c hc i
  have hi := intercept_le_integral_potential ρ y c L hy hρ i
  simp only [objective, hc, sub_zero]
  linarith

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]

/-- A normalized potential minimizer has an explicit uniform coordinate upper bound. -/
theorem minimizer_upper_bound (ρ : Measure V) [IsProbabilityMeasure ρ]
    (y : ι → V) (c : ι → ℝ) (L : NNReal) (hy : ∀ i, ‖y i‖ ≤ L)
    (hρ : Integrable (fun x : V => ‖x‖) ρ)
    (hmin : (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y 0 x ∂ρ) :
    ∀ i, c i ≤ 2 * (L : ℝ) * ∫ x, ‖x‖ ∂ρ := by
  have hzero : (∫ x, potential y 0 x ∂ρ) ≤ (L : ℝ) * ∫ x, ‖x‖ ∂ρ := by
    have hpoint : ∀ x : V, potential y 0 x ≤ (L : ℝ) * ‖x‖ := by
      intro x
      have hn := norm_potential_le y 0 L hy x
      have hle : potential y 0 x ≤ ‖potential y 0 x‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (potential y 0 x)
      simpa only [norm_zero, add_zero] using hle.trans hn
    have hi := integral_mono (integrable_potential ρ y 0 L hy hρ)
      (hρ.const_mul (L : ℝ)) hpoint
    simpa only [integral_const_mul] using hi
  intro i
  have hc := intercept_le_integral_potential ρ y c L hy hρ i
  linarith

/-- The positive weighted normalization turns the preceding upper bound into a compact box. -/
theorem minimizer_mem_box (ρ : Measure V) [IsProbabilityMeasure ρ]
    (y : ι → V) (c m : ι → ℝ) (L : NNReal) (hy : ∀ i, ‖y i‖ ≤ L)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) (hc : ∑ i, m i * c i = 0)
    (hρ : Integrable (fun x : V => ‖x‖) ρ)
    (hmin : (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y 0 x ∂ρ) :
    c ∈ Set.Icc (fun i => -(2 * (L : ℝ) * ∫ x, ‖x‖ ∂ρ) / m i)
      (fun _ => 2 * (L : ℝ) * ∫ x, ‖x‖ ∂ρ) := by
  have hupper := minimizer_upper_bound ρ y c L hy hρ hmin
  refine ⟨?_, hupper⟩
  intro i
  apply normalized_intercept_lower_bound m c hm hsum hc _ hupper i
  positivity

end Problem358.MaxPotential

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_PrescribedCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- For distinct sites and positive normalized weights the normalized uniform-source
variational objective has at most one minimizer. All geometric hypotheses are concrete. -/
theorem uniform_normalized_minimizer_unique {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (y : ι → E d) (hy : Function.Injective y) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (c b : ι → ℝ) (hc0 : ∑ i, m i * c i = 0) (hb0 : ∑ i, m i * b i = 0)
    (hcmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y c x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K)
    (hbmin : ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
      (∫ x, potential y b x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K) :
    c = b := by
  classical
  let : MeasurableSpace ι := ⊤
  let := UniformSource.probability hK hne
  have htie : ∀ a : ι → ℝ, ∀ᵐ x ∂uniformMeasure K, ∀ i j, i ≠ j →
      ⟪x, y i⟫ + a i ≠ ⟪x, y j⟫ + a j := by
    intro a
    filter_upwards [uniform_ae_affine_tie_implies_slopes_eq K y a] with x hx
    intro i j hij heq
    exact hij (hy (hx i j heq))
  obtain ⟨a, k, ha0, hk, hmax, hmass⟩ := exists_prescribed_cell_masses
    (uniformMeasure K) y m hm hsum ‖y‖₊ (fun i => norm_le_pi_norm y i)
    (UniformSource.integrable_norm hK) htie
  have hfib : ∀ i, MeasurableSet {x | k x = i} := by
    intro i
    exact hk (measurableSet_singleton i)
  have hint : ∀ a' : ι → ℝ, Integrable (potential y a') (uniformMeasure K) :=
    fun a' => UniformSource.integrable_continuousOn hK (continuous_potential y a').continuousOn
  have hamin := isMin_of_cell_masses (uniformMeasure K) y a m k ha0 hfib
    (Filter.Eventually.of_forall hmax) hmass hint
  have hstrict : ∀ᵐ x ∂uniformMeasure K, ∀ j, j ≠ k x →
      ⟪x, y j⟫ + a j < ⟪x, y (k x)⟫ + a (k x) := by
    filter_upwards [htie a] with x hx
    intro j hj
    exact lt_of_le_of_ne (hmax x j) (hx j (k x) hj)
  have hpos : ∀ i, (uniformMeasure K) {x | k x = i} ≠ 0 := by
    intro i hz
    have hz' : (uniformMeasure K).real {x | k x = i} = 0 := by simp [measureReal_def, hz]
    rw [hmass i] at hz'
    exact (ne_of_gt (hm i)) hz'
  have huniq (z : ι → ℝ) (hz0 : ∑ i, m i * z i = 0)
      (hzmin : ∀ a' : ι → ℝ, (∑ i, m i * a' i) = 0 →
        (∫ x, potential y z x ∂uniformMeasure K) ≤ ∫ x, potential y a' x ∂uniformMeasure K) :
      a = z :=
    normalized_minimizer_unique (uniformMeasure K) hconv.isPreconnected
      (UniformSource.subset_support hK hconv hne) (UniformSource.ae_mem hK.measurableSet)
      y a z m k hsum ha0 hz0 hint hamin hzmin hstrict hpos
  exact (huniq c hc0 hcmin).symm.trans (huniq b hb0 hbmin)

end Problem358.MaxPotential

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_FixedMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ContDiff

namespace Problem358.FixedMassIntercepts

variable {d : ℕ} {ι : Type*} [Fintype ι]

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem intercepts_spec {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y) :
    masses K y (intercepts hK hconv hne m hm hsum y) = m := by
  simp only [intercepts, dite_eq_left hy]
  exact (existsUnique_normalized hK hconv hne m hm hsum y hy).choose_spec.1

theorem eq_intercepts {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y)
    (c : CellLaplacian.normalizedSpace m) (hc : masses K y c = m) :
    c = intercepts hK hconv hne m hm hsum y := by
  exact (existsUnique_normalized hK hconv hne m hm hsum y hy).unique hc
    (intercepts_spec hK hconv hne m hm hsum y hy)

end Problem358.FixedMassIntercepts

end

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Distinctness of finitely many sites persists on a neighborhood. -/
theorem eventually_injective_sites {y : ι → E d} (hy : Function.Injective y) :
    ∀ᶠ z in 𝓝 y, Function.Injective z := by
  classical
  simp only [Function.Injective, Filter.eventually_all]
  intro i j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ _ => hij)
  · have hn : ∀ᶠ z in 𝓝 y, z i ≠ z j :=
      (isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl.mem_nhds (hy.ne hij)
    exact hn.mono (fun z hz heq => (hz heq).elim)

/-- The coordinate mass map takes values in probability vectors whenever the
sites are distinct. This is derived from the actual closed-cell partition. -/
theorem sum_normalizedMassMap [Nonempty ι] {K : Set (E d)} (hK : IsCompact K)
    (hne : (interior K).Nonempty) (m : ι → ℝ)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m)
    (hy : Function.Injective p.1) :
    ∑ i, normalizedMassMap K m p i = 1 := by
  let := UniformSource.probability hK hne
  have hρ : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hmass : uniformMeasure K K = 1 := by
    calc
      uniformMeasure K K = uniformMeasure K Set.univ := by
        apply measure_congr
        filter_upwards [UniformSource.ae_mem hK.measurableSet] with x hx
        exact propext ⟨fun _ => Set.mem_univ x, fun _ => hx⟩
      _ = 1 := measure_univ
  have h := sum_real_measure_closedCell hρ hK.isClosed p.1 p.2 hy
  simpa only [normalizedMassMap, Measure.real, hmass, ENNReal.toReal_one] using h

/-- The normalized mass residual vanishes exactly at the prescribed physical
closed-cell masses, without a selector or residual-range assumption. -/
theorem normalizedMassResidual_eq_zero_iff [Nonempty ι] {K : Set (E d)} (hK : IsCompact K)
    (hne : (interior K).Nonempty) (m : ι → ℝ) (hm : ∑ i, m i = 1)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m)
    (hy : Function.Injective p.1) :
    CellLaplacian.massResidual m hm (normalizedMassMap K m) p = 0 ↔
      ∀ i, (uniformMeasure K).real (closedCell K p.1 p.2 i) = m i := by
  rw [CellLaplacian.massResidual_eq_zero_iff m hm _ p
    (sum_normalizedMassMap hK hne m p hy)]
  exact funext_iff

/-- Restrict geometric C¹ regularity on ordinary site/intercept coordinates to
the weighted normalization hyperplane used by the implicit function theorem. -/
theorem contDiffAt_normalizedMassMap_of_raw {K : Set (E d)} (m : ι → ℝ)
    (p : (ι → E d) × CellLaplacian.normalizedSpace m)
    (hM : ContDiffAt ℝ 1
      (fun z : (ι → E d) × (ι → ℝ) => fun i =>
        (uniformMeasure K).real (closedCell K z.1 z.2 i))
      (p.1, (p.2 : ι → ℝ))) :
    ContDiffAt ℝ 1 (normalizedMassMap K m) p :=
  hM.comp p (normalizedConfigInclusion m).contDiff.contDiffAt

end Problem358.CellGeometry

end

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace Problem358.FixedMassIntercepts

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The actual canonical prescribed-mass intercepts are C¹ at each distinct-site
configuration where the geometric mass map is C¹ with its connected cell Laplacian
as intercept derivative.  Neither continuity nor uniqueness of a chosen branch is
assumed: both are supplied by the geometric closed-cell construction. -/
theorem contDiffAt_intercepts_of_massDifferential {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y)
    (g : ι → ι → ℝ) (hsym : ∀ i j, g i j = g j i)
    (hnonneg : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hM : ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m)
      (y, intercepts hK hconv hne m hm hsum y))
    (hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A
      (y, intercepts hK hconv hne m hm hsum y))
    (hA : ∀ q : CellLaplacian.normalizedSpace m, A (0, q) = CellLaplacian.apply g q) :
    ContDiffAt ℝ 1 (intercepts hK hconv hne m hm hsum) y := by
  let s := intercepts hK hconv hne m hm hsum
  let F := CellLaplacian.massResidual m hsum (CellGeometry.normalizedMassMap K m)
  have hF : ContDiffAt ℝ 1 F (y, s y) :=
    CellLaplacian.contDiffAt_massResidual m hsum hM
  have hDF := CellLaplacian.hasFDerivAt_massResidual m hsum hD
  have hpartial : fderiv ℝ F (y, s y) ∘L
      ContinuousLinearMap.inr ℝ (ι → E d) (CellLaplacian.normalizedSpace m) =
      (CellLaplacian.normalizedEquiv g hsym hnonneg G hG hpos m hsum).toContinuousLinearMap := by
    rw [show fderiv ℝ F (y, s y) = (CellLaplacian.zeroSumProjection m hsum) ∘L A from hDF.fderiv]
    exact CellLaplacian.massResidual_partial_eq g hsym hnonneg G hG hpos m hsum A hA
  have hzero : F (y, s y) = 0 := by
    apply (CellGeometry.normalizedMassResidual_eq_zero_iff hK hne m hsum (y, s y) hy).mpr
    exact fun i => congrFun (intercepts_spec hK hconv hne m hm hsum y hy) i
  have hunique : ∀ᶠ z in 𝓝 y, ∀ c, F (z, c) = 0 → c = s z := by
    filter_upwards [CellGeometry.eventually_injective_sites hy] with z hz
    intro c hc
    apply eq_intercepts hK hconv hne m hm hsum z hz c
    exact funext ((CellGeometry.normalizedMassResidual_eq_zero_iff hK hne m hsum (z, c) hz).mp hc)
  exact CellLaplacian.contDiffAt_normalized_solution (by norm_num) g hsym hnonneg G hG hpos
    m hsum F s y hF hpartial hzero hunique

/-- Along a differentiable site path, the actual canonical intercept derivative
satisfies the differentiated fixed-mass constraint. Its weighted mean vanishes
because it belongs to the normalization subspace. -/
theorem hasDerivAt_intercepts_comp_and_mass_constraint {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (Y : ℝ → (ι → E d)) (v : ι → E d) (t : ℝ)
    (hY : HasDerivAt Y v t) (hy : Function.Injective (Y t))
    (hs : DifferentiableAt ℝ (intercepts hK hconv hne m hm hsum) (Y t))
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A
      (Y t, intercepts hK hconv hne m hm hsum (Y t))) :
    let c := fun q => intercepts hK hconv hne m hm hsum (Y q)
    HasDerivAt c (deriv c t) t ∧ A (v, deriv c t) = 0 ∧
      ∑ i, m i * (↑(deriv c t : CellLaplacian.normalizedSpace m) : ι → ℝ) i = 0 := by
  let c := fun q => intercepts hK hconv hne m hm hsum (Y q)
  have hdc : HasDerivAt c (deriv c t) t :=
    (hs.comp t hY.differentiableAt).hasDerivAt
  refine ⟨hdc, ?_, (deriv c t).property⟩
  have hcomp := hD.comp_hasDerivAt t (hY.prodMk hdc)
  have heq : (fun q => CellGeometry.normalizedMassMap K m (Y q, c q)) =ᶠ[𝓝 t]
      (fun _ => m) := by
    filter_upwards [hY.continuousAt.eventually (CellGeometry.eventually_injective_sites hy)] with q hq
    exact intercepts_spec hK hconv hne m hm hsum (Y q) hq
  exact hcomp.unique ((hasDerivAt_const t m).congr_of_eventuallyEq heq)

end Problem358.FixedMassIntercepts

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_InterceptContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness and uniqueness imply continuous dependence of minimizers.
No differentiability or inverse-function theorem is used. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Problem358.CompactArgmin

variable {P C I : Type*} [TopologicalSpace P] [TopologicalSpace C]

/-- A compactly constrained family of minimizers converges to the unique minimizer
of the limiting continuous objective. The feasible set may be noncompact. -/
theorem tendsto_of_unique_minimizer {l : Filter I} {p : I → P} {p₀ : P}
    {c : I → C} {c₀ : C} {S K : Set C} {F : P × C → ℝ}
    (hK : IsCompact K) (hS : IsClosed S) (hF : Continuous F)
    (hp : Tendsto p l (𝓝 p₀)) (hbounded : ∀ᶠ i in l, c i ∈ K)
    (hfeasible : ∀ᶠ i in l, c i ∈ S)
    (hmin : ∀ᶠ i in l, ∀ z ∈ S, F (p i, c i) ≤ F (p i, z))
    (hunique : ∀ z ∈ S, IsMinOn (fun w => F (p₀, w)) S z → z = c₀) :
    Tendsto c l (𝓝 c₀) := by
  apply hK.tendsto_nhds_of_unique_mapClusterPt hbounded
  intro z _ hz
  obtain ⟨U, hUl, hUz⟩ := mapClusterPt_iff_ultrafilter.mp hz
  have hzS : z ∈ S := hS.mem_of_tendsto hUz (hUl hfeasible)
  apply hunique z hzS
  intro w hw
  have hleft : Tendsto (fun i => F (p i, c i)) (U : Filter I) (𝓝 (F (p₀, z))) :=
    hF.continuousAt.tendsto.comp ((hp.mono_left hUl).prodMk_nhds hUz)
  have hright : Tendsto (fun i => F (p i, w)) (U : Filter I) (𝓝 (F (p₀, w))) :=
    hF.continuousAt.tendsto.comp ((hp.mono_left hUl).prodMk_nhds tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hUl hmin] with i hi
  exact hi w hw

/-- Local compact bounds and uniqueness give continuity of an arbitrary selected minimizer. -/
theorem continuousAt_unique_minimizer {c : P → C} {p : P}
    {S K : Set C} {F : P × C → ℝ}
    (hK : IsCompact K) (hS : IsClosed S) (hF : Continuous F)
    (hbounded : ∀ᶠ q in 𝓝 p, c q ∈ K)
    (hfeasible : ∀ᶠ q in 𝓝 p, c q ∈ S)
    (hmin : ∀ᶠ q in 𝓝 p, ∀ z ∈ S, F (q, c q) ≤ F (q, z))
    (hunique : ∀ z ∈ S, IsMinOn (fun w => F (p, w)) S z → z = c p) :
    ContinuousAt c p :=
  tendsto_of_unique_minimizer hK hS hF tendsto_id hbounded hfeasible hmin hunique

end Problem358.CompactArgmin

end

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Problem358.MaxPotential

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Finite affine maxima depend jointly continuously on sites, intercepts, and source points. -/
theorem continuous_joint_potential {d : ℕ} :
    Continuous (fun p : ((ι → E d) × (ι → ℝ)) × E d =>
      potential p.1.1 p.1.2 p.2) := by
  have h : Continuous (Finset.univ.sup' Finset.univ_nonempty
      (fun i (p : ((ι → E d) × (ι → ℝ)) × E d) => ⟪p.2, p.1.1 i⟫ + p.1.2 i)) := by
    apply Continuous.finset_sup'
    intro i _
    fun_prop
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [potential, Finset.sup'_apply]

/-- The integrated finite affine objective is jointly continuous in all sites and intercepts. -/
theorem continuous_uniform_integral_potential {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hne : (interior K).Nonempty) :
    Continuous (fun p : (ι → E d) × (ι → ℝ) =>
      ∫ x, potential p.1 p.2 x ∂uniformMeasure K) := by
  let := UniformSource.probability hK hne
  have h := continuous_parametric_integral_of_continuous
    (μ := uniformMeasure K)
    (f := fun (p : (ι → E d) × (ι → ℝ)) (x : E d) => potential p.1 p.2 x)
    (continuous_joint_potential (ι := ι) (d := d)) hK
  rwa [Measure.restrict_eq_self_of_ae_mem (UniformSource.ae_mem hK.measurableSet)] at h

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace BigOperators Topology

namespace Problem358.MaxPotential

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Any normalized minimizing intercept selection depends continuously on the sites
at every injective configuration. This needs neither moving-cell derivatives nor IFT. -/
theorem continuousAt_uniform_intercept_selection {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (c : (ι → E d) → ι → ℝ)
    (hc0 : ∀ y, ∑ i, m i * c y i = 0)
    (hcmin : ∀ y (a : ι → ℝ), (∑ i, m i * a i) = 0 →
      (∫ x, potential y (c y) x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K)
    (y : ι → E d) (hy : Function.Injective y) : ContinuousAt c y := by
  let := UniformSource.probability hK hne
  let L : NNReal := ⟨‖y‖ + 1, by positivity⟩
  let B : ℝ := 2 * (L : ℝ) * ∫ x, ‖x‖ ∂uniformMeasure K
  let S : Set (ι → ℝ) := {a | ∑ i, m i * a i = 0}
  let J : Set (ι → ℝ) := Set.Icc (fun i => -B / m i) (fun _ => B)
  have hS : IsClosed S := isClosed_eq (by fun_prop) continuous_const
  have hJ : IsCompact J := isCompact_Icc
  have hnorm : ∀ᶠ z : ι → E d in 𝓝 y, ‖z‖ < (L : ℝ) := by
    exact continuous_norm.continuousAt.eventually_lt continuousAt_const (by change ‖y‖ < ‖y‖ + 1; linarith)
  have hbounded : ∀ᶠ z in 𝓝 y, c z ∈ J := by
    filter_upwards [hnorm] with z hz
    apply minimizer_mem_box (uniformMeasure K) z (c z) m L
      (fun i => (norm_le_pi_norm z i).trans hz.le) hm hsum (hc0 z)
      (UniformSource.integrable_norm hK)
    exact hcmin z 0 (by simp)
  apply CompactArgmin.continuousAt_unique_minimizer hJ hS
    (continuous_uniform_integral_potential (ι := ι) hK hne) hbounded
    (Filter.Eventually.of_forall hc0) (Filter.Eventually.of_forall hcmin)
  intro a ha hamin
  exact uniform_normalized_minimizer_unique hK hconv hne y hy m hm hsum
    a (c y) ha (hc0 y) hamin (hcmin y)

/-- A globally defined normalized minimizer selection exists, and is continuous
on the open set of pairwise distinct sites. -/
theorem exists_continuous_uniform_intercept_selection {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    ∃ c : (ι → E d) → ι → ℝ,
      (∀ y, ∑ i, m i * c y i = 0) ∧
      (∀ y (a : ι → ℝ), (∑ i, m i * a i) = 0 →
        (∫ x, potential y (c y) x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K) ∧
      ContinuousOn c {y | Function.Injective y} := by
  classical
  let := UniformSource.probability hK hne
  have hex : ∀ y : ι → E d, ∃ c : ι → ℝ,
      (∑ i, m i * c i) = 0 ∧
      ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
        (∫ x, potential y c x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K := by
    intro y
    obtain ⟨c, hc0, hcmin⟩ := exists_minimum_objective (uniformMeasure K) y m hm hsum
      ‖y‖₊ (fun i => norm_le_pi_norm y i) (UniformSource.integrable_norm hK)
    refine ⟨c, hc0, ?_⟩
    intro a ha
    simpa only [objective, hc0, ha, sub_zero] using hcmin a ha
  choose c hc0 hcmin using hex
  refine ⟨c, hc0, hcmin, ?_⟩
  intro y hy
  exact (continuousAt_uniform_intercept_selection hK hconv hne m hm hsum c hc0 hcmin y hy).continuousWithinAt

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology

namespace Problem358.FixedMassIntercepts

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Distinct finite site configurations form an open subset of the ambient coordinate space. -/
theorem isOpen_injective_sites : IsOpen {y : ι → E d | Function.Injective y} := by
  have heq : {y : ι → E d | Function.Injective y} =
      ⋂ i : ι, ⋂ j : ι, {y | i ≠ j → y i ≠ y j} := by
    ext y
    simp only [mem_ofPred_eq, mem_iInter]
    exact Function.injective_iff_pairwise_ne
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp [hij]
  · have hset : {y : ι → E d | i ≠ j → y i ≠ y j} =
        {y : ι → E d | y i = y j}ᶜ := by
      ext y
      simp [hij]
    rw [hset]
    exact (isClosed_eq (show Continuous (fun y : ι → E d => y i) from continuous_apply i)
      (show Continuous (fun y : ι → E d => y j) from continuous_apply j)).isOpen_compl

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The actual prescribed intercepts minimize the integrated affine potential. -/
theorem intercepts_minimize {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y) (a : ι → ℝ)
    (ha : ∑ i, m i * a i = 0) :
    (∫ x, MaxPotential.potential y (intercepts hK hconv hne m hm hsum y) x
      ∂uniformMeasure K) ≤ ∫ x, MaxPotential.potential y a x ∂uniformMeasure K := by
  let := UniformSource.probability hK hne
  let c := intercepts hK hconv hne m hm hsum y
  obtain ⟨k, hk, _, hmax⟩ := exists_measurable_argmax
    (fun i (x : E d) => ⟪x, y i⟫ + (c : ι → ℝ) i)
    (fun i => ((continuous_id.inner continuous_const).add continuous_const).measurable)
  apply MaxPotential.isMin_of_cell_masses (uniformMeasure K) y c m k c.property
    (fun i => hk (measurableSet_singleton i)) (Eventually.of_forall hmax)
    _ _ a ha
  · intro i
    exact (masses_eq_selector hK.measurableSet y hy c k hmax i).symm.trans
      (congrFun (intercepts_spec hK hconv hne m hm hsum y hy) i)
  · intro b
    exact UniformSource.integrable_continuousOn hK
      (MaxPotential.continuous_potential y b).continuousOn

/-- Canonical closed-cell intercepts are continuous at every distinct-site configuration.
This compactness argument is independent of the moving-boundary C1 theorem. -/
theorem continuousAt_intercepts_coe {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y) :
    ContinuousAt (fun z => (intercepts hK hconv hne m hm hsum z : ι → ℝ)) y := by
  obtain ⟨b, hb0, hbmin, hbcont⟩ :=
    MaxPotential.exists_continuous_uniform_intercept_selection hK hconv hne m hm hsum
  have heq : ∀ z : ι → E d, Function.Injective z →
      (intercepts hK hconv hne m hm hsum z : ι → ℝ) = b z := by
    intro z hz
    apply MaxPotential.uniform_normalized_minimizer_unique hK hconv hne z hz m hm hsum
      _ _ (intercepts hK hconv hne m hm hsum z).property (hb0 z)
    · exact intercepts_minimize hK hconv hne m hm hsum z hz
    · exact hbmin z
  have h_nhds : {z : ι → E d | Function.Injective z} ∈ 𝓝 y :=
    isOpen_injective_sites.mem_nhds hy
  apply (hbcont.continuousAt h_nhds).congr_of_eventuallyEq
  filter_upwards [h_nhds] with z hz
  exact heq z hz

/-- On repeated-site configurations the chosen extension is exactly zero. -/
theorem intercepts_eq_zero_of_not_injective {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : ¬Function.Injective y) :
    intercepts hK hconv hne m hm hsum y = 0 := by
  simp only [intercepts, dite_eq_right hy]

/-- The actual normalized intercept choice is globally Borel measurable, including
at repeated-site configurations, where its value was explicitly set to zero. -/
theorem measurable_intercepts_coe {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    Measurable (fun y => (intercepts hK hconv hne m hm hsum y : ι → ℝ)) := by
  classical
  let c : (ι → E d) → ι → ℝ := fun y => intercepts hK hconv hne m hm hsum y
  have hc : ContinuousOn c {y | Function.Injective y} := fun y hy =>
    (continuousAt_intercepts_coe hK hconv hne m hm hsum y hy).continuousWithinAt
  have hmeas := hc.measurable_piecewise (continuous_const.continuousOn :
    ContinuousOn (fun _ : ι → E d => (0 : ι → ℝ)) {y | Function.Injective y}ᶜ)
    isOpen_injective_sites.measurableSet
  have heq : ({y : ι → E d | Function.Injective y}.piecewise c (fun _ => 0)) = c := by
    funext y
    by_cases hy : Function.Injective y
    · simp only [piecewise, mem_ofPred_eq, ite_eq_left hy]
    · simp only [piecewise, mem_ofPred_eq, ite_eq_right hy]
      symm
      exact congrArg Subtype.val (intercepts_eq_zero_of_not_injective hK hconv hne m hm hsum y hy)
  rwa [heq] at hmeas

end Problem358.FixedMassIntercepts

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Flux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted finite-dimensional estimates for moving affine cells

These lemmas isolate the algebraic part of the moment and intercept-speed
estimates. They make no assertion about existence or differentiability of cells.
-/

noncomputable section

open scoped BigOperators

namespace Problem358

section WeightedCauchySchwarz

variable {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Weighted Cauchy--Schwarz, in the form needed by the cell moment estimate. -/
theorem weighted_inner_sum_sq_le (s : Finset ι) (m : ι → ℝ)
    (v B : ι → F) (hm : ∀ i ∈ s, 0 < m i) :
    (∑ i ∈ s, inner ℝ (v i) (B i)) ^ 2 ≤
      (∑ i ∈ s, m i * ‖v i‖ ^ 2) *
        (∑ i ∈ s, ‖B i‖ ^ 2 / m i) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi
    exact mul_nonneg (hm i hi).le (sq_nonneg _)
  · intro i hi
    exact div_nonneg (sq_nonneg _) (hm i hi).le
  · intro i hi
    have h := abs_real_inner_le_norm (v i) (B i)
    have hsq := (sq_le_sq₀ (abs_nonneg (inner ℝ (v i) (B i)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
    rw [sq_abs, mul_pow] at hsq
    convert hsq using 1
    all_goals try with_reducible_and_instances rfl
    field_simp [(hm i hi).ne']

/-- The energy cancellation step, including the zero-energy case. -/
theorem energy_le_of_sq_le_mul {energy bound : ℝ} (he : 0 ≤ energy) (hb : 0 ≤ bound)
    (h : energy ^ 2 ≤ bound * energy) : energy ≤ bound := by
  rcases he.eq_or_lt with he | he
  · subst energy
    exact hb
  · nlinarith

/-- Algebraic intercept-energy estimate from a moment estimate and cell duality.
The geometric work supplies `hdual` and `hmoment`; no inverse bound on a
Laplacian is used here. -/
theorem intercept_energy_le (s : Finset ι) (m r : ι → ℝ) (v B : ι → F)
    {k w : ℝ} (hm : ∀ i ∈ s, 0 < m i) (hk : 0 ≤ k)
    (hspeed : (∑ i ∈ s, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hdual : (∑ i ∈ s, m i * r i ^ 2) =
      -(∑ i ∈ s, inner ℝ (v i) (B i)))
    (hmoment : (∑ i ∈ s, ‖B i‖ ^ 2 / m i) ≤
      k * (∑ i ∈ s, m i * r i ^ 2)) :
    (∑ i ∈ s, m i * r i ^ 2) ≤ k * w ^ 2 := by
  have he : 0 ≤ ∑ i ∈ s, m i * r i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hm i hi).le (sq_nonneg _)
  have hb : 0 ≤ ∑ i ∈ s, ‖B i‖ ^ 2 / m i :=
    Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hm i hi).le
  apply energy_le_of_sq_le_mul he (mul_nonneg hk (sq_nonneg w))
  calc
    (∑ i ∈ s, m i * r i ^ 2) ^ 2 =
        (∑ i ∈ s, inner ℝ (v i) (B i)) ^ 2 := by rw [hdual, neg_sq]
    _ ≤ (∑ i ∈ s, m i * ‖v i‖ ^ 2) *
        (∑ i ∈ s, ‖B i‖ ^ 2 / m i) := weighted_inner_sum_sq_le s m v B hm
    _ ≤ w ^ 2 * (∑ i ∈ s, ‖B i‖ ^ 2 / m i) :=
      mul_le_mul_of_nonneg_right hspeed hb
    _ ≤ w ^ 2 * (k * (∑ i ∈ s, m i * r i ^ 2)) :=
      mul_le_mul_of_nonneg_left hmoment (sq_nonneg w)
    _ = (k * w ^ 2) * (∑ i ∈ s, m i * r i ^ 2) := by ring

/-- Symmetry of the vector-valued face coefficients identifies the adjoint
of site motion with the stationary-site moment derivative. -/
theorem symmetric_flux_pairing [Fintype ι] (q : ι → ℝ) (v : ι → F)
    (b : ι → ι → F) (hb : ∀ i j, b i j = b j i) :
    (∑ i, q i * ∑ j, inner ℝ (b i j) (v i - v j)) =
      ∑ i, inner ℝ (v i) (∑ j, (q i - q j) • b i j) := by
  classical
  have hswap : (∑ i, ∑ j, q i * inner ℝ (b i j) (v j)) =
      ∑ i, ∑ j, q j * inner ℝ (b i j) (v i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hb j i]
  simp only [inner_sub_right, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib,
    inner_sum, inner_smul_right, sub_mul]
  rw [hswap]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;>
    rw [real_inner_comm]

/-- Symmetry of scalar face coefficients gives the mass pairing identity. -/
theorem symmetric_mass_pairing [Fintype ι] (q r : ι → ℝ)
    (g : ι → ι → ℝ) (hg : ∀ i j, g i j = g j i) :
    (∑ i, q i * ∑ j, g i j * (r i - r j)) =
      ∑ i, r i * ∑ j, g i j * (q i - q j) := by
  simpa [mul_comm] using
    symmetric_flux_pairing q r g hg

/-- The finite-cell duality identity follows solely from symmetric face
coefficients and the differentiated fixed-mass constraints. -/
theorem fixed_mass_flux_duality [Fintype ι] (q r : ι → ℝ) (v : ι → F)
    (g : ι → ι → ℝ) (b : ι → ι → F)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hfixed : ∀ i, (∑ j, g i j * (r i - r j)) +
      (∑ j, inner ℝ (b i j) (v i - v j)) = 0) :
    (∑ i, r i * ∑ j, g i j * (q i - q j)) =
      -(∑ i, inner ℝ (v i) (∑ j, (q i - q j) • b i j)) := by
  have hz : (∑ i, q i * ((∑ j, g i j * (r i - r j)) +
      (∑ j, inner ℝ (b i j) (v i - v j)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hfixed i, mul_zero]
  simp only [mul_add, Finset.sum_add_distrib] at hz
  rw [symmetric_mass_pairing q r g hg, symmetric_flux_pairing q v b hb] at hz
  linarith

end WeightedCauchySchwarz

/-- Weighted Cauchy--Schwarz for the mass-displacement mixed term. -/
theorem weighted_abs_sqrt_sum_le {ι : Type*} (s : Finset ι)
    (δ γ D : ι → ℝ) (hγ : ∀ i ∈ s, 0 < γ i)
    (hD : ∀ i ∈ s, 0 ≤ D i) :
    (∑ i ∈ s, |δ i| * Real.sqrt (D i)) ≤
      Real.sqrt ((∑ i ∈ s, δ i ^ 2 / γ i) * (∑ i ∈ s, γ i * D i)) := by
  apply Real.le_sqrt_of_sq_le
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi
    exact div_nonneg (sq_nonneg _) (hγ i hi).le
  · intro i hi
    exact mul_nonneg (hγ i hi).le (hD i hi)
  · intro i hi
    rw [mul_pow, sq_abs, Real.sq_sqrt (hD i hi)]
    apply le_of_eq
    field_simp [(hγ i hi).ne']

/-- Young's inequality absorbs the mixed square-root term in the stationary
cell displacement estimate. -/
theorem midpoint_displacement_energy_le {A B R : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (h : A / 4 ≤ R ^ 2 * B / 8 + R / 2 * Real.sqrt (A * B)) :
    A ≤ 5 * R ^ 2 * B := by
  have ha := Real.sq_sqrt hA
  have hb := Real.sq_sqrt hB
  rw [Real.sqrt_mul hA] at h
  have hy : R / 2 * (Real.sqrt A * Real.sqrt B) ≤ A / 8 + R ^ 2 * B / 2 := by
    nlinarith [sq_nonneg (Real.sqrt A - 2 * R * Real.sqrt B)]
  linarith

/-- Elementary arithmetic/geometric mean gap bound without square-root
normalization: the positive geometric mean can be supplied by its square. -/
theorem geometric_mean_gap_bounds {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hγ : 0 < γ) (hγsq : γ ^ 2 = α * β) :
    0 ≤ (α + β) / 2 - γ ∧
      (α + β) / 2 - γ ≤ (α - β) ^ 2 / (8 * γ) := by
  constructor
  · nlinarith [sq_nonneg (α - β)]
  · apply (le_div_iff₀ (by positivity : 0 < 8 * γ)).2
    nlinarith [sq_nonneg (α + β - 2 * γ)]

/-- The contribution of one cell to the aggregate midpoint energy balance. -/
theorem midpoint_cell_energy_balance {α β γ Am Ap D R : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ) (hγsq : γ ^ 2 = α * β)
    (hAm : Am ≤ R ^ 2) (hAp : Ap ≤ R ^ 2)
    (hdiff : |Am - Ap| ≤ 2 * R * Real.sqrt D) :
    (α * Am + β * Ap) / 2 - γ * ((Am + Ap) / 2) ≤
      R ^ 2 * ((α - β) ^ 2 / γ) / 8 +
        R / 2 * (|α - β| * Real.sqrt D) := by
  obtain ⟨hgap0, hgap⟩ := geometric_mean_gap_bounds hα hβ hγ hγsq
  have hmean : (Am + Ap) / 2 ≤ R ^ 2 := by linarith
  have hfirst := mul_le_mul_of_nonneg_left hmean hgap0
  have hsecond := mul_le_mul_of_nonneg_right hgap (sq_nonneg R)
  have hprod : (α - β) * (Am - Ap) ≤ |α - β| * |Am - Ap| := by
    simpa only [abs_mul] using le_abs_self ((α - β) * (Am - Ap))
  have hprod' := mul_le_mul_of_nonneg_left hdiff (abs_nonneg (α - β))
  have hterm : (α - β) / 4 * (Am - Ap) ≤
      R / 2 * (|α - β| * Real.sqrt D) := by nlinarith
  have hfirst' : ((α + β) / 2 - γ) * ((Am + Ap) / 2) ≤
      R ^ 2 * ((α - β) ^ 2 / γ) / 8 := by
    calc
      _ ≤ ((α + β) / 2 - γ) * R ^ 2 := hfirst
      _ ≤ ((α - β) ^ 2 / (8 * γ)) * R ^ 2 := hsecond
      _ = _ := by ring
  calc
    _ = ((α + β) / 2 - γ) * ((Am + Ap) / 2) +
        (α - β) / 4 * (Am - Ap) := by ring
    _ ≤ _ := add_le_add hfirst' hterm

/-- Aggregate midpoint domination and cellwise moment-control bounds imply
the transport-energy estimate used in the uniform `162` moment bound. -/
theorem midpoint_aggregate_transport {ι : Type*} (s : Finset ι)
    (α β γ D Am Ap : ι → ℝ) {R : ℝ}
    (hα : ∀ i ∈ s, 0 ≤ α i) (hβ : ∀ i ∈ s, 0 ≤ β i)
    (hγ : ∀ i ∈ s, 0 < γ i) (hγsq : ∀ i ∈ s, γ i ^ 2 = α i * β i)
    (hD : ∀ i ∈ s, 0 ≤ D i) (hR : 0 ≤ R)
    (hAm : ∀ i ∈ s, Am i ≤ R ^ 2) (hAp : ∀ i ∈ s, Ap i ≤ R ^ 2)
    (hdiff : ∀ i ∈ s, |Am i - Ap i| ≤ 2 * R * Real.sqrt (D i))
    (hdom : (∑ i ∈ s, γ i * ((Am i + Ap i) / 2 + D i / 4)) ≤
      ∑ i ∈ s, (α i * Am i + β i * Ap i) / 2) :
    (∑ i ∈ s, γ i * D i) ≤
      5 * R ^ 2 * ∑ i ∈ s, (α i - β i) ^ 2 / γ i := by
  have hA : 0 ≤ ∑ i ∈ s, γ i * D i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hγ i hi).le (hD i hi)
  have hB : 0 ≤ ∑ i ∈ s, (α i - β i) ^ 2 / γ i :=
    Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hγ i hi).le
  apply midpoint_displacement_energy_le hA hB
  have hsplit : (∑ i ∈ s, γ i * ((Am i + Ap i) / 2 + D i / 4)) =
      (∑ i ∈ s, γ i * ((Am i + Ap i) / 2)) +
        (∑ i ∈ s, γ i * D i) / 4 := by
    simp only [mul_add, mul_div_assoc, Finset.sum_add_distrib, Finset.sum_div]
  rw [hsplit] at hdom
  have hdom' : (∑ i ∈ s, γ i * D i) / 4 ≤
      ∑ i ∈ s, ((α i * Am i + β i * Ap i) / 2 -
        γ i * ((Am i + Ap i) / 2)) := by
    rw [Finset.sum_sub_distrib]
    linarith
  calc
    (∑ i ∈ s, γ i * D i) / 4 ≤
        ∑ i ∈ s, ((α i * Am i + β i * Ap i) / 2 -
          γ i * ((Am i + Ap i) / 2)) := hdom'
    _ ≤ ∑ i ∈ s, (R ^ 2 * ((α i - β i) ^ 2 / γ i) / 8 +
        R / 2 * (|α i - β i| * Real.sqrt (D i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact midpoint_cell_energy_balance (hα i hi) (hβ i hi) (hγ i hi)
        (hγsq i hi) (hAm i hi) (hAp i hi) (hdiff i hi)
    _ = R ^ 2 * (∑ i ∈ s, (α i - β i) ^ 2 / γ i) / 8 +
        R / 2 * (∑ i ∈ s, |α i - β i| * Real.sqrt (D i)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    _ ≤ R ^ 2 * (∑ i ∈ s, (α i - β i) ^ 2 / γ i) / 8 +
        R / 2 * Real.sqrt ((∑ i ∈ s, γ i * D i) *
          (∑ i ∈ s, (α i - β i) ^ 2 / γ i)) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hR (by norm_num))
      rw [mul_comm]
      exact weighted_abs_sqrt_sum_le s (fun i => α i - β i) γ D hγ hD

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem358

variable {ι F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The connected mass Jacobian and the stationary moment estimate control the
intercept velocity.  The auxiliary solution of the mass equation is constructed
here; in particular no quantitative inverse-Jacobian bound is assumed. -/
theorem fixed_mass_intercept_energy_le
    (g : ι → ι → ℝ) (b : ι → ι → F)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m r : ι → ℝ) (v : ι → F) {k w : ℝ}
    (hm : ∀ i, 0 < m i) (hk : 0 ≤ k)
    (hmean : ∑ i, m i * r i = 0)
    (hfixed : ∀ i, CellLaplacian.apply g r i +
      (∑ j, inner ℝ (b i j) (v i - v j)) = 0)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hmoment : ∀ q : ι → ℝ,
      (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
        k * ∑ i, (CellLaplacian.apply g q i) ^ 2 / m i) :
    (∑ i, m i * r i ^ 2) ≤ k * w ^ 2 := by
  obtain ⟨q, hq⟩ := CellLaplacian.exists_apply_eq_of_sum_eq_zero
    g hg hg0 G hG hpos (fun i => m i * r i) hmean
  have hdual := fixed_mass_flux_duality q r v g b hg hb hfixed
  have hdual' : (∑ i, m i * r i ^ 2) =
      -(∑ i, inner ℝ (v i) (∑ j, (q i - q j) • b i j)) := by
    calc
      (∑ i, m i * r i ^ 2) = ∑ i, r i * CellLaplacian.apply g q i := by
        rw [hq]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := hdual
  have hmoment' : (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
      k * ∑ i, m i * r i ^ 2 := by
    convert hmoment q using 1
    all_goals try with_reducible_and_instances rfl
    rw [hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hm i).ne']
  simpa only [Finset.mem_univ, forall_const] using
    intercept_energy_le Finset.univ m r v (fun i => ∑ j, (q i - q j) • b i j)
      (fun i _ => hm i) hk hspeed hdual' hmoment'

/-- The exact universal moment constant yields the energy input used by the
finite affine potential-path estimate. -/
theorem fixed_mass_intercept_energy_le_162
    (g : ι → ι → ℝ) (b : ι → ι → F)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (m r : ι → ℝ) (v : ι → F) {R w : ℝ}
    (hm : ∀ i, 0 < m i) (hmean : ∑ i, m i * r i = 0)
    (hfixed : ∀ i, CellLaplacian.apply g r i +
      (∑ j, inner ℝ (b i j) (v i - v j)) = 0)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hmoment : ∀ q : ι → ℝ,
      (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
        162 * R ^ 2 * ∑ i, (CellLaplacian.apply g q i) ^ 2 / m i) :
    (∑ i, m i * r i ^ 2) ≤ 162 * R ^ 2 * w ^ 2 :=
  fixed_mass_intercept_energy_le g b hg hb hg0 G hG hpos m r v hm
    (by positivity) hmean hfixed hspeed hmoment

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_LineDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology

namespace Problem358

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasDerivAt_line_of_hasLineDerivAt
    {f : V → F} {x v : V} {t : ℝ} {p : F}
    (h : HasLineDerivAt ℝ f p (x + t • v) v) :
    HasDerivAt (fun r : ℝ => f (x + r • v)) p t := by
  have h' : HasDerivAt (fun r : ℝ => f ((x + t • v) + r • v)) p (t - t) := by
    simpa only [HasLineDerivAt, sub_self] using h
  have hh := h'.comp_sub_const t t
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  congr 1
  simp only [sub_smul]
  abel

lemma norm_sub_le_of_continuous_linear_line_derivatives
    {s : Set V} (hs : Convex ℝ s) {f : V → F} {D : V → V →L[ℝ] F}
    (hD : ∀ x ∈ s, ∀ v, HasLineDerivAt ℝ f (D x v) x v)
    {A : V →L[ℝ] F} {C : ℝ} (hb : ∀ x ∈ s, ‖D x - A‖ ≤ C)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - A (y - x)‖ ≤ C * ‖y - x‖ := by
  let v := y - x
  let g : ℝ → F := fun t => f (x + t • v) - t • A v
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g ((D (x + t • v) - A) v) t := by
    intro t ht
    have hz : x + t • v ∈ s := hs.add_smul_sub_mem hx hy ht
    have hh := hasDerivAt_line_of_hasLineDerivAt (hD _ hz v)
    simpa only [g, sub_apply, one_smul, Pi.sub_def, id_eq] using
      hh.sub ((hasDerivAt_id t).smul_const (A v))
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖(D (x + t • v) - A) v‖ ≤ C * ‖v‖ := by
    intro t ht
    have hz : x + t • v ∈ s := hs.add_smul_sub_mem hx hy (Ico_subset_Icc_self ht)
    exact ((D (x + t • v) - A).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb _ hz) (norm_nonneg v))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) hbound
  simpa only [g, v, one_smul, zero_smul, add_zero, sub_zero, add_sub_cancel_left,
    add_sub_cancel, sub_sub_sub_cancel_right, sub_right_comm] using hm

/-- A continuous field of bounded linear directional derivatives implies strict
Fréchet differentiability. No completeness or finite-dimensional hypothesis is needed. -/
lemma hasStrictFDerivAt_of_continuousAt_lineDeriv
    {f : V → F} {D : V → V →L[ℝ] F} {x : V}
    (hD : ∀ᶠ y in 𝓝 x, ∀ v, HasLineDerivAt ℝ f (D y v) y v)
    (hc : ContinuousAt D x) : HasStrictFDerivAt f (D x) x := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hD
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  let η := min r δ
  have hη : 0 < η := lt_min hr hδ
  have hline : ∀ y ∈ Metric.ball x η, ∀ v, HasLineDerivAt ℝ f (D y v) y v := by
    intro y hy
    exact hball (Metric.mem_ball.mpr (lt_of_lt_of_le
      (Metric.mem_ball.mp hy) (min_le_left r δ)))
  have hbound : ∀ y ∈ Metric.ball x η, ‖D y - D x‖ ≤ ε := by
    intro y hy
    have hh := hclose (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right r δ))
    exact le_of_lt (by simpa only [dist_eq_norm] using hh)
  have hevent : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x η := Metric.ball_mem_nhds x hη
  filter_upwards [hevent.prod_nhds hevent] with p hp
  exact norm_sub_le_of_continuous_linear_line_derivatives
    (convex_ball x η) hline hbound hp.2 hp.1

/-- On an open set, a continuous field of bounded linear line derivatives gives C¹. -/
lemma contDiffOn_one_of_continuousOn_lineDeriv
    {s : Set V} (hs : IsOpen s) {f : V → F} {D : V → V →L[ℝ] F}
    (hD : ∀ x ∈ s, ∀ v, HasLineDerivAt ℝ f (D x v) x v)
    (hc : ContinuousOn D s) : ContDiffOn ℝ 1 f s := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_one_iff]
  refine ⟨D, s, hs.mem_nhds hx, hc, ?_⟩
  intro y hy
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_of_continuousAt_lineDeriv
  · filter_upwards [hs.mem_nhds hy] with z hz
    exact hD z hz
  · exact (hc y hy).continuousAt (hs.mem_nhds hy)

end Problem358

end

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace Problem358.FaceDerivative

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Operator-norm continuity of the face derivative follows solely from continuity
of its nonzero normal scale, face mass, and vector face moment. -/
theorem continuousAt_linearMap {P : Type*} [TopologicalSpace P]
    {A M : P → ℝ} {B : P → V} {p : P}
    (hA : ContinuousAt A p) (hM : ContinuousAt M p) (hB : ContinuousAt B p)
    (hzero : A p ≠ 0) :
    ContinuousAt (fun q => linearMap (A q) (M q) (B q)) p := by
  unfold linearMap
  exact (hA.inv₀ hzero).smul
    ((hM.smul continuousAt_const).add
      (((innerSL ℝ).continuous.continuousAt.comp hB).clm_comp continuousAt_const))

end Problem358.FaceDerivative

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MassDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized cell-mass line derivative with canonical coefficients. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Compact convex positive-cell geometry alone gives the normalized mass
derivative. The auxiliary interior tie points are chosen internally. -/
theorem hasDerivAt_uniformMass_line
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y v : ι → E d) (c r : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i : ι) :
    HasDerivAt (fun t : ℝ => (uniformMeasure K).real
      (closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i))
      (∑ j, (
        (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
          (closedCell K y c i ∩ closedCell K y c j)).toReal /
            ((volume K).toReal * ‖y i - y j‖) * (r i - r j) +
          ⟪faceMoment K y c i j, v i - v j⟫)) 0 := by
  classical
  have hex : ∀ j, ∃ z : E d, j ≠ i →
      z ∈ interior K ∧ ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j := by
    intro j
    by_cases hji : j = i
    · exact ⟨0, fun h => (h hji).elim⟩
    · obtain ⟨z, hz, hzt⟩ := exists_equality_interior_of_positive_cells
        hρ hconv y c hy (Ne.symm hji) (hpos i) (hpos j)
      exact ⟨z, fun _ => ⟨hz, hzt⟩⟩
  choose z hz using hex
  have hd := PositiveCellFullDerivative.hasDerivAt_closedCell_integral
    hρ hK hconv y v c r hy hpos (fun _ => (1 : ℝ)) continuous_const i z
    (fun j hji => (hz j hji).1) (fun j hji => (hz j hji).2)
  have hd' := hasDerivAt_uniformMass_of_integral_one hK.isClosed
    (fun t j => y j + t • v j) (fun t j => c j + t * r j) i hd
  let D : ι → ℝ := fun j =>
    (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)
      (closedCell K y c i ∩ closedCell K y c j)).toReal /
        ((volume K).toReal * ‖y i - y j‖) * (r i - r j) +
      ⟪faceMoment K y c i j, v i - v j⟫
  have hD : D i = 0 := by simp [D]
  have heq : (volume K).toReal⁻¹ *
      (∑ j ∈ Finset.univ.erase i,
        PositiveCellFullDerivative.faceVariation K y v c r (fun _ => 1) i j (z j)) =
        ∑ j, D j := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ j ∈ Finset.univ.erase i, D j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        exact PositiveCellFullDerivative.normalized_faceVariation_one hK y v c r
          (hy.ne hji.symm) (hz j hji).2
      _ = ∑ j, D j := by
        simpa only [hD, add_zero] using
          (Finset.sum_erase_add Finset.univ D (Finset.mem_univ i))
  rw [heq] at hd'
  simpa only [D] using hd'

end Problem358.CellGeometry

end

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace BigOperators
namespace Problem358.PositiveCellFullDerivative

open CellGeometry

/-- The stationary coordinate face derivative has exactly the canonical vector
coefficient and source-volume normalization. -/
theorem normalized_faceVariation_coordinate_stationary
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Set (E d)} (hK : IsCompact K) (y : ι → E d) (c q : ι → ℝ)
    {i j : ι} (hy : y i ≠ y j) {z : E d}
    (htie : ⟪z, y i⟫_ℝ + c i = ⟪z, y j⟫_ℝ + c j) (k : Fin d) :
    (volume K).toReal⁻¹ * faceVariation K y (fun _ => 0) c q (fun x => x k) i j z =
      (q i - q j) * faceMoment K y c i j k := by
  have hid : IntegrableOn (fun x : E d => x)
      (closedCell K y c i ∩ closedCell K y c j)
      (IntrinsicSurface.interfaceMeasure (y i) (y j) (c i) (c j)) :=
    IntrinsicSurface.integrableOn_interfaceMeasure _ _ _ _
      ((isCompact_closedCell hK y c i).inter (isCompact_closedCell hK y c j))
      continuous_id.continuousOn
  rw [faceVariation_eq_intrinsic hK.isClosed y (fun _ => 0) c q (fun x => x k) hy htie]
  simp only [sub_self, inner_zero_left, add_zero]
  rw [integral_const_mul]
  unfold faceMoment
  rw [PiLp.smul_apply, CellVectorDerivative.integral_coordinate hid k]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Actual stationary-site moment differential with the canonical intrinsic
face moments. No directional derivative or face regularity premise remains. -/
theorem hasDerivAt_uniform_closedCell_moment_stationary
    {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c q : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i : ι) :
    HasDerivAt (fun t : ℝ => ∫ x in
      closedCell K y (fun j => c j + t * q j) i, x ∂uniformMeasure K)
      (∑ j, (q i - q j) • faceMoment K y c i j) 0 := by
  classical
  have hex : ∀ j, ∃ z : E d, j ≠ i → z ∈ interior K ∧
      ⟪z, y i⟫_ℝ + c i = ⟪z, y j⟫_ℝ + c j := by
    intro j
    by_cases hji : j = i
    · exact ⟨0, fun h => (h hji).elim⟩
    · obtain ⟨z, hz, he⟩ := exists_equality_interior_of_positive_cells hρ hconv y c hy
        (Ne.symm hji) (hpos i) (hpos j)
      exact ⟨z, fun _ => ⟨hz, he⟩⟩
  choose z hz using hex
  have hd := hasDerivAt_uniform_closedCell_moment hρ hK hconv y (fun _ => 0) c q hy hpos
    i z (fun j hj => (hz j hj).1) (fun j hj => (hz j hj).2)
  have heq : (volume K).toReal⁻¹ • (WithLp.toLp 2 fun k : Fin d =>
      ∑ j ∈ Finset.univ.erase i, faceVariation K y (fun _ => 0) c q (fun x => x k) i j (z j)) =
      ∑ j, (q i - q j) • faceMoment K y c i j := by
    have hsum : (∑ j ∈ Finset.univ.erase i, (q i - q j) • faceMoment K y c i j) =
        ∑ j, (q i - q j) • faceMoment K y c i j := by
      simp
    rw [← hsum]
    apply PiLp.ext
    intro k
    change (volume K).toReal⁻¹ * (∑ j ∈ Finset.univ.erase i,
      faceVariation K y (fun _ => 0) c q (fun x => x k) i j (z j)) =
      (EuclideanSpace.proj k) (∑ j ∈ Finset.univ.erase i,
        (q i - q j) • faceMoment K y c i j)
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact normalized_faceVariation_coordinate_stationary hK y c q
      (hy.ne (Finset.ne_of_mem_erase hj).symm) ((hz j (Finset.ne_of_mem_erase hj)).2) k
  rw [heq] at hd
  simpa only [smul_zero, add_zero] using hd

end Problem358.PositiveCellFullDerivative

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Geometry supplies all directional derivatives of the true uniform masses. -/
theorem hasLineDerivAt_uniformMass
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i : ι)
    (w : (ι → E d) × (ι → ℝ)) :
    HasLineDerivAt ℝ (fun p : (ι → E d) × (ι → ℝ) =>
      (uniformMeasure K).real (closedCell K p.1 p.2 i))
      (massLinearMap K y c i w) (y, c) w := by
  rcases w with ⟨v, r⟩
  rw [massLinearMap_apply]
  change HasDerivAt (fun t : ℝ => (uniformMeasure K).real
    (closedCell K (fun j => y j + t • v j) (fun j => c j + t * r j) i)) _ 0
  exact hasDerivAt_uniformMass_line hρ hK hconv y v c r hy hpos i

/-- Continuity of the true mass derivative in operator norm. -/
theorem continuousAt_massLinearMap
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0) (i : ι) :
    ContinuousAt (fun p : (ι → E d) × (ι → ℝ) =>
      massLinearMap K p.1 p.2 i) (y, c) := by
  unfold massLinearMap FaceDerivative.cellLinearMap
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact (FaceDerivative.continuousAt_linearMap continuousAt_const
    (continuousAt_canonicalFaceWeight hρ hK hconv y c hy hpos i j)
    (continuousAt_faceMoment hρ hK hconv y c hy hpos i j)
    (by norm_num)).clm_comp continuousAt_const

omit [Fintype ι] [DecidableEq ι] in
theorem nonzero_cellMass_of_positive {K : Set (E d)}
    {p : (ι → E d) × (ι → ℝ)} (hp : p ∈ positiveMassConfigurations K) (i : ι) :
    uniformMeasure K (closedCell K p.1 p.2 i) ≠ 0 := by
  intro h
  have hh := hp.2 i
  simp only [Measure.real, h, ENNReal.toReal_zero, lt_self_iff_false] at hh

/-- Joint C¹ regularity of the entire genuine normalized mass map, on its open
positive-cell locus. All face calculus hypotheses have been discharged. -/
theorem contDiffOn_uniformMassMap
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K) :
    ContDiffOn ℝ 1 (fun p : (ι → E d) × (ι → ℝ) =>
      fun i => (uniformMeasure K).real (closedCell K p.1 p.2 i))
      (positiveMassConfigurations K) := by
  apply contDiffOn_pi.mpr
  intro i
  apply Problem358.contDiffOn_one_of_continuousOn_lineDeriv
    (isOpen_distinct_positive_real_closedCell hK.measurableSet)
    (D := fun p => massLinearMap K p.1 p.2 i)
  · intro p hp
    exact hasLineDerivAt_uniformMass (uniformMeasure_absolutelyContinuous K)
      hK hconv p.1 p.2 hp.1 (nonzero_cellMass_of_positive hp) i
  · intro p hp
    exact (continuousAt_massLinearMap (uniformMeasure_absolutelyContinuous K)
      hK hconv p.1 p.2 hp.1 (nonzero_cellMass_of_positive hp) i).continuousWithinAt

/-- The pointwise C¹ form consumed by normalized implicit-function arguments. -/
theorem contDiffAt_uniformMassMap
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < (uniformMeasure K).real (closedCell K y c i)) :
    ContDiffAt ℝ 1 (fun p : (ι → E d) × (ι → ℝ) =>
      fun i => (uniformMeasure K).real (closedCell K p.1 p.2 i)) (y, c) :=
  (contDiffOn_uniformMassMap hK hconv (y, c) ⟨hy, hpos⟩).contDiffAt
    ((isOpen_distinct_positive_real_closedCell hK.measurableSet).mem_nhds ⟨hy, hpos⟩)

end Problem358.CellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_MomentAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem358

/-- Uniform comparisons of nearby cell masses, in the normalization used in
    the finite-difference estimate. -/
theorem nearby_mass_square_bound {M α γ : ℝ}
    (hM : 0 < M) (hα : 0 ≤ α) (hαM : α ≤ 2 * M)
    (hγM : M / 2 ≤ γ) : α ^ 2 / M ≤ 8 * γ := by
  apply (div_le_iff₀ hM).2
  have hsq : α ^ 2 ≤ (2 * M) ^ 2 := (sq_le_sq₀ hα (by positivity)).2 hαM
  nlinarith

/-- The reciprocal comparison for nearby cell masses. -/
theorem nearby_mass_reciprocal_bound {M γ δ : ℝ}
    (hM : 0 < M) (hγM : M / 2 ≤ γ) :
    δ ^ 2 / γ ≤ 2 * (δ ^ 2 / M) := by
  have hγ : 0 < γ := by linarith
  apply (div_le_iff₀ hγ).2
  have hm : δ ^ 2 * M ≤ δ ^ 2 * (2 * γ) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg δ)
  calc
    δ ^ 2 ≤ (2 * δ ^ 2 * γ) / M := (le_div_iff₀ hM).2 (by nlinarith)
    _ = 2 * (δ ^ 2 / M) * γ := by ring

/-- A finite-difference moment estimate with a constant independent of the
    number of cells or the smallest cell mass. The geometric input is the
    midpoint energy estimate and the elementary bound on each moment change. -/
theorem stationary_moment_finite_difference
    {ι V : Type*} [Fintype ι] [SeminormedAddCommGroup V]
    (M α γ δ D : ι → ℝ) (Δ : ι → V) (R : ℝ)
    (hM : ∀ i, 0 < M i) (hα : ∀ i, 0 ≤ α i)
    (hαM : ∀ i, α i ≤ 2 * M i)
    (hγM : ∀ i, M i / 2 ≤ γ i)
    (hD : ∀ i, 0 ≤ D i) (hR : 0 ≤ R)
    (hΔ : ∀ i, ‖Δ i‖ ≤ R * |δ i| + α i * Real.sqrt (D i))
    (henergy : (∑ i, γ i * D i) ≤
      5 * R ^ 2 * (∑ i, δ i ^ 2 / γ i)) :
    (∑ i, ‖Δ i‖ ^ 2 / M i) ≤
      162 * R ^ 2 * (∑ i, δ i ^ 2 / M i) := by
  have hpoint (i : ι) : ‖Δ i‖ ^ 2 ≤
      2 * R ^ 2 * δ i ^ 2 + 2 * α i ^ 2 * D i := by
    have hsq := (sq_le_sq₀ (norm_nonneg (Δ i))
      (show 0 ≤ R * |δ i| + α i * Real.sqrt (D i) from
        add_nonneg (mul_nonneg hR (abs_nonneg _))
          (mul_nonneg (hα i) (Real.sqrt_nonneg _)))).2 (hΔ i)
    have ha : (R * |δ i|) ^ 2 = R ^ 2 * δ i ^ 2 := by
      rw [mul_pow, sq_abs]
    have hb : (α i * Real.sqrt (D i)) ^ 2 = α i ^ 2 * D i := by
      rw [mul_pow, Real.sq_sqrt (hD i)]
    nlinarith [sq_nonneg (R * |δ i| - α i * Real.sqrt (D i))]
  have hterm (i : ι) : ‖Δ i‖ ^ 2 / M i ≤
      2 * R ^ 2 * (δ i ^ 2 / M i) + 16 * (γ i * D i) := by
    have hmass := nearby_mass_square_bound (hM i) (hα i) (hαM i) (hγM i)
    have hmul := mul_le_mul_of_nonneg_right hmass (hD i)
    calc
      ‖Δ i‖ ^ 2 / M i ≤
          (2 * R ^ 2 * δ i ^ 2 + 2 * α i ^ 2 * D i) / M i :=
        div_le_div_of_nonneg_right (hpoint i) (hM i).le
      _ = 2 * R ^ 2 * (δ i ^ 2 / M i) +
          2 * (α i ^ 2 / M i * D i) := by ring
      _ ≤ 2 * R ^ 2 * (δ i ^ 2 / M i) + 16 * (γ i * D i) := by
        linarith
  have hrecip : (∑ i, δ i ^ 2 / γ i) ≤
      2 * (∑ i, δ i ^ 2 / M i) := by
    calc
      (∑ i, δ i ^ 2 / γ i) ≤ ∑ i, 2 * (δ i ^ 2 / M i) :=
        Finset.sum_le_sum fun i _ => nearby_mass_reciprocal_bound (hM i) (hγM i)
      _ = _ := by rw [Finset.mul_sum]
  have henergy' : (∑ i, γ i * D i) ≤
      10 * R ^ 2 * (∑ i, δ i ^ 2 / M i) := by
    have hm := mul_le_mul_of_nonneg_left hrecip (show 0 ≤ 5 * R ^ 2 by positivity)
    nlinarith
  calc
    (∑ i, ‖Δ i‖ ^ 2 / M i) ≤
        ∑ i, (2 * R ^ 2 * (δ i ^ 2 / M i) + 16 * (γ i * D i)) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * R ^ 2 * (∑ i, δ i ^ 2 / M i) + 16 * (∑ i, γ i * D i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 162 * R ^ 2 * (∑ i, δ i ^ 2 / M i) := by linarith

/-- Positive limiting cell masses give all nearby-mass comparisons
simultaneously, with no uniform lower bound on the finite configuration. -/
theorem eventually_nearby_mass_bounds
    {ι A : Type*} [Finite ι] {l : Filter A}
    (M : ι → ℝ) (α β : A → ι → ℝ)
    (hM : ∀ i, 0 < M i)
    (hα : ∀ i, Filter.Tendsto (fun a => α a i) l (nhds (M i)))
    (hβ : ∀ i, Filter.Tendsto (fun a => β a i) l (nhds (M i))) :
    ∀ᶠ a in l, ∀ i, 0 < α a i ∧ 0 < β a i ∧
      α a i ≤ 2 * M i ∧ M i / 2 ≤ Real.sqrt (α a i * β a i) := by
  apply Filter.eventually_all.mpr
  intro i
  have hγ : Filter.Tendsto (fun a => Real.sqrt (α a i * β a i)) l (nhds (M i)) := by
    simpa only [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos (hM i)] using
      ((hα i).mul (hβ i)).sqrt
  filter_upwards [(hα i).eventually_const_lt (hM i),
    (hβ i).eventually_const_lt (hM i),
    (hα i).eventually_lt_const (show M i < 2 * M i by linarith [hM i]),
    hγ.eventually_const_lt (show M i / 2 < M i by linarith [hM i])]
    with a ha hb haM hγM
  exact ⟨ha, hb, haM.le, hγM.le⟩

end Problem358

end

noncomputable section

open scoped BigOperators Topology

namespace Problem358

/-- Symmetric moment differences converge to the negative derivative. -/
theorem tendsto_symmetric_moment_quotient {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V} {v : V} (hf : HasDerivAt f v 0) :
    Filter.Tendsto (fun s : ℝ => (2 * s)⁻¹ • (f (-s) - f s))
      (𝓝[>] 0) (𝓝 (-v)) := by
  have hn : HasDerivAt (fun s : ℝ => f (-s)) (-v) 0 := by
    have hf' : HasDerivAt f v (- (0 : ℝ)) := by simpa using hf
    simpa [Function.comp_def] using hf'.scomp 0 (hasDerivAt_neg 0)
  have hd := (hn.sub hf).const_smul (1 / 2 : ℝ)
  have ht := hd.tendsto_slope_zero_right
  have htarget : (1 / 2 : ℝ) • (-v - v) = -v := by module
  rw [htarget] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext s
  simp only [zero_add, Pi.smul_apply, Pi.sub_apply, neg_zero, sub_self, smul_zero, sub_zero,
    smul_smul]
  congr 1
  simp [mul_inv_rev]

/-- Passing a uniform symmetric finite-difference estimate to cell derivatives.
The geometric construction supplies `hfinite`; this lemma performs the limit step. -/
theorem moment_derivative_bound {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : ι → ℝ → V} {m : ι → ℝ → ℝ}
    {dB : ι → V} {dm M : ι → ℝ} {C : ℝ}
    (hB : ∀ i, HasDerivAt (B i) (dB i) 0)
    (hm : ∀ i, HasDerivAt (m i) (dm i) 0)
    (hfinite : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (∑ i, ‖B i (-s) - B i s‖ ^ 2 / M i) ≤
        C * ∑ i, (m i (-s) - m i s) ^ 2 / M i) :
    (∑ i, ‖dB i‖ ^ 2 / M i) ≤ C * ∑ i, dm i ^ 2 / M i := by
  have hl : Filter.Tendsto
      (fun s : ℝ => ∑ i, ‖(2 * s)⁻¹ • (B i (-s) - B i s)‖ ^ 2 / M i)
      (𝓝[>] 0) (𝓝 (∑ i, ‖dB i‖ ^ 2 / M i)) := by
    apply tendsto_finsetSum
    intro i _
    simpa using (((tendsto_symmetric_moment_quotient (hB i)).norm).pow 2).div_const (M i)
  have hr : Filter.Tendsto
      (fun s : ℝ => ∑ i, ‖(2 * s)⁻¹ • (m i (-s) - m i s)‖ ^ 2 / M i)
      (𝓝[>] 0) (𝓝 (∑ i, dm i ^ 2 / M i)) := by
    apply tendsto_finsetSum
    intro i _
    simpa [Real.norm_eq_abs, sq_abs] using
      (((tendsto_symmetric_moment_quotient (hm i)).norm).pow 2).div_const (M i)
  apply le_of_tendsto_of_tendsto hl (hr.const_mul C)
  filter_upwards [hfinite] with s hs
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg ((2 * s)⁻¹))
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    mul_div_assoc, Finset.mul_sum, mul_assoc, mul_left_comm] using hh

end Problem358

end

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.MomentCouplingBounds

variable {A F : Type*} [MeasurableSpace A] {μ : Measure A}
  [IsProbabilityMeasure μ] [NormedAddCommGroup F]

/-- The elementary probability-space L1/L2 comparison for a norm. -/
theorem integral_norm_le_sqrt_integral_sq_norm {f : A → F} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  apply Real.le_sqrt_of_sq_le
  have h := ProbabilityTheory.variance_nonneg (fun x => ‖f x‖) μ
  rw [ProbabilityTheory.variance_eq_sub hf.norm] at h
  exact sub_nonneg.mp h

/-- A coupling's quadratic displacement bounds the displacement of its barycentres. -/
theorem norm_integral_sub_le_sqrt [NormedSpace ℝ F] {X Z : A → F}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) :
    ‖(∫ x, X x ∂μ) - ∫ x, Z x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) := by
  rw [← integral_sub (hX.integrable (by norm_num)) (hZ.integrable (by norm_num))]
  exact (norm_integral_le_integral_norm _).trans
    (integral_norm_le_sqrt_integral_sq_norm (hX.sub hZ))

/-- Squared norms are `2R`-Lipschitz on a ball of radius `R`. -/
theorem abs_sq_norm_sub_le {R : ℝ} {x z : F} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |‖x‖ ^ 2 - ‖z‖ ^ 2| ≤ 2 * R * ‖x - z‖ := by
  have hid : ‖x‖ ^ 2 - ‖z‖ ^ 2 = (‖x‖ - ‖z‖) * (‖x‖ + ‖z‖) := by ring
  rw [hid, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    |‖x‖ - ‖z‖| * (‖x‖ + ‖z‖) ≤ ‖x - z‖ * (‖x‖ + ‖z‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x z)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖x - z‖ * (2 * R) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = _ := by ring

/-- The quadratic concave potential used in the midpoint argument has controlled
expectation difference under a bounded coupling. -/
theorem quadratic_potential_expectation_sub_le {R : ℝ} (hR : 0 ≤ R)
    {X Z : A → F} (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ)
    (hXR : ∀ᵐ x ∂μ, ‖X x‖ ≤ R) (hZR : ∀ᵐ x ∂μ, ‖Z x‖ ≤ R) :
    |(∫ x, R ^ 2 - ‖X x‖ ^ 2 ∂μ) - (∫ x, R ^ 2 - ‖Z x‖ ^ 2 ∂μ)| ≤
      2 * R * Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) := by
  have hXi : Integrable (fun x => R ^ 2 - ‖X x‖ ^ 2) μ :=
    (integrable_const _).sub (hX.integrable_norm_pow (by norm_num))
  have hZi : Integrable (fun x => R ^ 2 - ‖Z x‖ ^ 2) μ :=
    (integrable_const _).sub (hZ.integrable_norm_pow (by norm_num))
  have hXZ : Integrable (fun x => ‖X x - Z x‖) μ :=
    (hX.sub hZ).norm.integrable (by norm_num)
  rw [← integral_sub hXi hZi, ← Real.norm_eq_abs]
  calc
    ‖∫ x, (R ^ 2 - ‖X x‖ ^ 2) - (R ^ 2 - ‖Z x‖ ^ 2) ∂μ‖ ≤
        ∫ x, ‖(R ^ 2 - ‖X x‖ ^ 2) - (R ^ 2 - ‖Z x‖ ^ 2)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, 2 * R * ‖X x - Z x‖ ∂μ := by
      apply integral_mono_ae (hXi.sub hZi).norm (hXZ.const_mul (2 * R))
      filter_upwards [hXR, hZR] with x hx hz
      rw [Real.norm_eq_abs]
      have h := abs_sq_norm_sub_le hx hz
      change |(R ^ 2 - ‖X x‖ ^ 2) - (R ^ 2 - ‖Z x‖ ^ 2)| ≤ _
      have heq : (R ^ 2 - ‖X x‖ ^ 2) - (R ^ 2 - ‖Z x‖ ^ 2) =
          -(‖X x‖ ^ 2 - ‖Z x‖ ^ 2) := by ring
      rw [heq, abs_neg]
      exact h
    _ = 2 * R * ∫ x, ‖X x - Z x‖ ∂μ := integral_const_mul _ _
    _ ≤ 2 * R * Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_norm_le_sqrt_integral_sq_norm (hX.sub hZ))
        (by positivity)

/-- The expectation of a bounded random vector lies in the same norm ball. -/
theorem norm_integral_le_of_ae_norm_le [NormedSpace ℝ F] {X : A → F} {R : ℝ}
    (hX : Integrable X μ) (hXR : ∀ᵐ x ∂μ, ‖X x‖ ≤ R) :
    ‖∫ x, X x ∂μ‖ ≤ R := by
  calc
    ‖∫ x, X x ∂μ‖ ≤ ∫ x, ‖X x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : A, R ∂μ := integral_mono_ae hX.norm (integrable_const _) hXR
    _ = R := by simp

/-- The unnormalized cell-moment difference estimate in the stationary-site proof. -/
theorem weighted_barycentre_sub_le [NormedSpace ℝ F] {X Z : A → F}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) {R α β : ℝ}
    (hα : 0 ≤ α) (hZR : ∀ᵐ x ∂μ, ‖Z x‖ ≤ R) :
    ‖α • (∫ x, X x ∂μ) - β • (∫ x, Z x ∂μ)‖ ≤
      R * |α - β| + α * Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) := by
  have hZb := norm_integral_le_of_ae_norm_le (hZ.integrable (by norm_num)) hZR
  have heq : α • (∫ x, X x ∂μ) - β • (∫ x, Z x ∂μ) =
      (α - β) • (∫ x, Z x ∂μ) + α • ((∫ x, X x ∂μ) - ∫ x, Z x ∂μ) := by module
  rw [heq]
  calc
    ‖(α - β) • (∫ x, Z x ∂μ) + α • ((∫ x, X x ∂μ) - ∫ x, Z x ∂μ)‖ ≤
        ‖(α - β) • (∫ x, Z x ∂μ)‖ + ‖α • ((∫ x, X x ∂μ) - ∫ x, Z x ∂μ)‖ :=
      norm_add_le _ _
    _ = |α - β| * ‖∫ x, Z x ∂μ‖ +
        α * ‖(∫ x, X x ∂μ) - ∫ x, Z x ∂μ‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα]
    _ ≤ |α - β| * R + α * Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) :=
      add_le_add (mul_le_mul_of_nonneg_left hZb (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_integral_sub_le_sqrt hX hZ) hα)
    _ = _ := by ring

end Problem358.MomentCouplingBounds

namespace Problem358.MidpointEnergy
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma quadraticPotential_midpoint (R : ℝ) (x z : F) :
    quadraticPotential R ((1 / 2 : ℝ) • (x + z)) =
      (quadraticPotential R x + quadraticPotential R z) / 2 + ‖x - z‖ ^ 2 / 4 := by
  unfold quadraticPotential
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    mul_pow, norm_add_sq_real, norm_sub_sq_real]
  ring

omit [InnerProductSpace ℝ F] in
lemma quadraticPotential_nonneg {R : ℝ} {x : F} (hx : ‖x‖ ≤ R) :
    0 ≤ quadraticPotential R x :=
  sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hx 2)

omit [InnerProductSpace ℝ F] in
lemma quadraticPotential_le (R : ℝ) (x : F) :
    quadraticPotential R x ≤ R ^ 2 := sub_le_self _ (sq_nonneg _)

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]

/-- The integrated parallelogram identity gives the exact midpoint energy gain. -/
theorem integral_quadraticPotential_midpoint (R : ℝ) {X Z : A → F}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) :
    (∫ x, quadraticPotential R ((1 / 2 : ℝ) • (X x + Z x)) ∂μ) =
      ((∫ x, quadraticPotential R (X x) ∂μ) +
        (∫ x, quadraticPotential R (Z x) ∂μ)) / 2 +
      (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) / 4 := by
  have hXi : Integrable (fun x => quadraticPotential R (X x)) μ :=
    (integrable_const _).sub (hX.integrable_norm_pow (by norm_num))
  have hZi : Integrable (fun x => quadraticPotential R (Z x)) μ :=
    (integrable_const _).sub (hZ.integrable_norm_pow (by norm_num))
  have hDi : Integrable (fun x => ‖X x - Z x‖ ^ 2) μ :=
    (hX.sub hZ).integrable_norm_pow (by norm_num)
  simp_rw [quadraticPotential_midpoint]
  have hAi : Integrable (fun x =>
      (quadraticPotential R (X x) + quadraticPotential R (Z x)) / 2) μ :=
    (hXi.add hZi).div_const 2
  rw [integral_add hAi (hDi.div_const 4),
    integral_div, integral_add hXi hZi, integral_div]

variable [MeasurableSpace F] [BorelSpace F]

omit [InnerProductSpace ℝ F] in
/-- A bounded-support measure integrates the nonnegative quadratic potential. -/
theorem integrable_quadraticPotential_of_ae_bound {ρ : Measure F} [IsFiniteMeasure ρ]
    {R : ℝ} (hρ : ∀ᵐ x ∂ρ, ‖x‖ ≤ R) : Integrable (quadraticPotential R) ρ := by
  apply (integrable_const (R ^ 2)).mono'
  · exact (show Continuous (quadraticPotential R) by unfold quadraticPotential; fun_prop).aestronglyMeasurable
  · filter_upwards [hρ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (quadraticPotential_nonneg hx)]
    exact quadraticPotential_le R x

/-- Cellwise measure domination gives the midpoint energy inequality.
The geometric existence of the dominated coupling is an explicit hypothesis. -/
theorem scaled_midpoint_energy_le {ρ : Measure F} [IsFiniteMeasure ρ]
    {R γ : ℝ} (hγ : 0 ≤ γ) {X Z : A → F}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ)
    (hρ : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (hdom : ENNReal.ofReal γ •
      Measure.map (fun x => (1 / 2 : ℝ) • (X x + Z x)) μ ≤ ρ) :
    γ * (((∫ x, quadraticPotential R (X x) ∂μ) +
      (∫ x, quadraticPotential R (Z x) ∂μ)) / 2 +
      (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) / 4) ≤
      ∫ x, quadraticPotential R x ∂ρ := by
  have hmid : MemLp (fun x => (1 / 2 : ℝ) • (X x + Z x)) 2 μ :=
    (hX.add hZ).const_smul (1 / 2 : ℝ)
  have hnonneg : 0 ≤ᵐ[ρ] quadraticPotential R := by
    filter_upwards [hρ] with x hx
    exact quadraticPotential_nonneg hx
  have h := integral_mono_measure hdom hnonneg (integrable_quadraticPotential_of_ae_bound hρ)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hγ, smul_eq_mul,
    integral_map hmid.aemeasurable
      (show AEStronglyMeasurable (quadraticPotential R) _ from
        (show Continuous (quadraticPotential R) by unfold quadraticPotential; fun_prop).aestronglyMeasurable),
    integral_quadraticPotential_midpoint R hX hZ] at h
  exact h

end Problem358.MidpointEnergy

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_StationaryMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem358.StationaryMoment

open MidpointEnergy MomentCouplingBounds

variable {ι A F : Type*} [Fintype ι] [MeasurableSpace A]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [InnerProductSpace ℝ F] in
/-- A partition expressed by scaled pushforward laws gives its weighted
quadratic-potential integral identity. -/
theorem integral_partition_pushforwards
    (μ : ι → Measure A) [∀ i, IsFiniteMeasure (μ i)]
    (X : ι → A → F) (w : ι → ℝ) (ρ : Measure F) (R : ℝ)
    (hX : ∀ i, MemLp (X i) 2 (μ i)) (hw : ∀ i, 0 ≤ w i)
    (hpartition : (∑ i, ENNReal.ofReal (w i) • Measure.map (X i) (μ i)) = ρ) :
    (∫ x, quadraticPotential R x ∂ρ) =
      ∑ i, w i * ∫ a, quadraticPotential R (X i a) ∂μ i := by
  have hΦ : StronglyMeasurable (quadraticPotential R (F := F)) :=
    (show Continuous (quadraticPotential R (F := F)) by
      unfold quadraticPotential
      fun_prop).stronglyMeasurable
  have hmap (i : ι) : Integrable (quadraticPotential R)
      (Measure.map (X i) (μ i)) := by
    apply (integrable_map_measure hΦ.aestronglyMeasurable (hX i).aemeasurable).2
    exact (integrable_const _).sub ((hX i).integrable_norm_pow (by norm_num))
  rw [← hpartition, integral_finsetSum_measure
    (fun i _ => (hmap i).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hw i), smul_eq_mul,
    integral_map (hX i).aemeasurable hΦ.aestronglyMeasurable]

/-- The full finite-difference moment estimate assembled from actual midpoint
measure domination and endpoint partition laws. The existence of those dominated
couplings is an explicit input, not a conclusion of this theorem. -/
theorem conditional_stationary_moment_finite_difference
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (X Z : ι → A → F) (η : ι → Measure F) (ρ : Measure F)
    [∀ i, IsFiniteMeasure (η i)]
    (M α β γ : ι → ℝ) {R : ℝ}
    (hX : ∀ i, MemLp (X i) 2 (μ i)) (hZ : ∀ i, MemLp (Z i) 2 (μ i))
    (hR : 0 ≤ R) (hM : ∀ i, 0 < M i)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαM : ∀ i, α i ≤ 2 * M i) (hγM : ∀ i, M i / 2 ≤ γ i)
    (hγsq : ∀ i, γ i ^ 2 = α i * β i)
    (hXR : ∀ i, ∀ᵐ a ∂μ i, ‖X i a‖ ≤ R)
    (hZR : ∀ i, ∀ᵐ a ∂μ i, ‖Z i a‖ ≤ R)
    (hηR : ∀ i, ∀ᵐ x ∂η i, ‖x‖ ≤ R)
    (hpartition : (∑ i, η i) = ρ)
    (hminus : (∑ i, ENNReal.ofReal (α i) • Measure.map (X i) (μ i)) = ρ)
    (hplus : (∑ i, ENNReal.ofReal (β i) • Measure.map (Z i) (μ i)) = ρ)
    (hdom : ∀ i, ENNReal.ofReal (γ i) •
      Measure.map (fun a => (1 / 2 : ℝ) • (X i a + Z i a)) (μ i) ≤ η i) :
    (∑ i, ‖α i • (∫ a, X i a ∂μ i) - β i • (∫ a, Z i a ∂μ i)‖ ^ 2 / M i) ≤
      162 * R ^ 2 * ∑ i, (α i - β i) ^ 2 / M i := by
  let D : ι → ℝ := fun i => ∫ a, ‖X i a - Z i a‖ ^ 2 ∂μ i
  let Am : ι → ℝ := fun i => ∫ a, quadraticPotential R (X i a) ∂μ i
  let Ap : ι → ℝ := fun i => ∫ a, quadraticPotential R (Z i a) ∂μ i
  have hγ : ∀ i, 0 < γ i := fun i =>
    lt_of_lt_of_le (half_pos (hM i)) (hγM i)
  have hD : ∀ i, 0 ≤ D i := fun i => integral_nonneg (fun _ => sq_nonneg _)
  have hAm : ∀ i, Am i ≤ R ^ 2 := by
    intro i
    have hi : Integrable (fun a => quadraticPotential R (X i a)) (μ i) :=
      (integrable_const _).sub ((hX i).integrable_norm_pow (by norm_num))
    have hh := integral_mono_ae hi (integrable_const (R ^ 2))
      (Filter.Eventually.of_forall (fun a => quadraticPotential_le R (X i a)))
    simpa [Am] using hh
  have hAp : ∀ i, Ap i ≤ R ^ 2 := by
    intro i
    have hi : Integrable (fun a => quadraticPotential R (Z i a)) (μ i) :=
      (integrable_const _).sub ((hZ i).integrable_norm_pow (by norm_num))
    have hh := integral_mono_ae hi (integrable_const (R ^ 2))
      (Filter.Eventually.of_forall (fun a => quadraticPotential_le R (Z i a)))
    simpa [Ap] using hh
  have hdiff : ∀ i, |Am i - Ap i| ≤ 2 * R * Real.sqrt (D i) := by
    intro i
    exact quadratic_potential_expectation_sub_le hR (hX i) (hZ i) (hXR i) (hZR i)
  have haggregate : (∑ i, γ i * ((Am i + Ap i) / 2 + D i / 4)) ≤
      ∑ i, (α i * Am i + β i * Ap i) / 2 := by
    calc
      (∑ i, γ i * ((Am i + Ap i) / 2 + D i / 4)) ≤
          ∑ i, ∫ x, quadraticPotential R x ∂η i := by
        exact Finset.sum_le_sum (fun i _ =>
          scaled_midpoint_energy_le (hγ i).le (hX i) (hZ i) (hηR i) (hdom i))
      _ = ∫ x, quadraticPotential R x ∂ρ := by
        rw [← hpartition]
        symm
        exact integral_finsetSum_measure (fun i _ =>
          integrable_quadraticPotential_of_ae_bound (hηR i))
      _ = ∑ i, (α i * Am i + β i * Ap i) / 2 := by
        have hm := integral_partition_pushforwards μ X α ρ R hX hα hminus
        have hp := integral_partition_pushforwards μ Z β ρ R hZ hβ hplus
        change (∫ x, quadraticPotential R x ∂ρ) =
          ∑ i, (α i * (∫ a, quadraticPotential R (X i a) ∂μ i) +
            β i * (∫ a, quadraticPotential R (Z i a) ∂μ i)) / 2
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← hm, ← hp]
        ring
  have henergy : (∑ i, γ i * D i) ≤
      5 * R ^ 2 * ∑ i, (α i - β i) ^ 2 / γ i :=
    midpoint_aggregate_transport Finset.univ α β γ D Am Ap
      (fun i _ => hα i) (fun i _ => hβ i) (fun i _ => hγ i)
      (fun i _ => hγsq i) (fun i _ => hD i) hR
      (fun i _ => hAm i) (fun i _ => hAp i) (fun i _ => hdiff i) haggregate
  exact stationary_moment_finite_difference M α γ (fun i => α i - β i) D
    (fun i => α i • (∫ a, X i a ∂μ i) - β i • (∫ a, Z i a ∂μ i)) R
    hM hα hαM hγM hD hR
    (fun i => weighted_barycentre_sub_le (hX i) (hZ i) (hα i) (hZR i)) henergy

/-- A packaged midpoint comparison proves the uniform finite-difference bound. -/
theorem MidpointComparisonData.finite_difference
    {M α β : ι → ℝ} {Δ : ι → F} {ρ : Measure F} {R : ℝ}
    (data : MidpointComparisonData A M α β Δ ρ R)
    (hR : 0 ≤ R) (hM : ∀ i, 0 < M i) :
    (∑ i, ‖Δ i‖ ^ 2 / M i) ≤ 162 * R ^ 2 * ∑ i, (α i - β i) ^ 2 / M i := by
  let : ∀ i, IsProbabilityMeasure (data.sample i) := data.sample_probability
  let : ∀ i, IsFiniteMeasure (data.middleCell i) := data.middleCell_finite
  have h := conditional_stationary_moment_finite_difference
    data.sample data.leftPoint data.rightPoint data.middleCell ρ M α β data.geometricMass
    data.left_memLp data.right_memLp hR hM data.left_mass_nonneg data.right_mass_nonneg
    data.left_mass_le data.geometric_mass_ge data.geometric_mass_sq
    data.left_bounded data.right_bounded data.middle_bounded data.middle_partition
    data.left_partition data.right_partition data.midpoint_dominated
  simpa only [data.moment_difference] using h

/-- Conditional stationary-site derivative estimate. Its inputs are ordinary
derivatives and actual midpoint comparison data for sufficiently small positive
perturbations; no quantitative limiting inequality is assumed. -/
theorem stationary_moment_derivative_of_midpoint_data
    {B : ι → ℝ → F} {m : ι → ℝ → ℝ} {dB : ι → F} {dm M : ι → ℝ}
    {ρ : Measure F} {R : ℝ}
    (hR : 0 ≤ R) (hM : ∀ i, 0 < M i)
    (hB : ∀ i, HasDerivAt (B i) (dB i) 0)
    (hm : ∀ i, HasDerivAt (m i) (dm i) 0)
    (hdata : ∀ᶠ s : ℝ in 𝓝[>] 0, Nonempty
      (MidpointComparisonData A M (fun i => m i (-s)) (fun i => m i s)
        (fun i => B i (-s) - B i s) ρ R)) :
    (∑ i, ‖dB i‖ ^ 2 / M i) ≤ 162 * R ^ 2 * ∑ i, dm i ^ 2 / M i := by
  apply moment_derivative_bound hB hm
  filter_upwards [hdata] with s hs
  obtain ⟨data⟩ := hs
  exact data.finite_difference hR hM

end Problem358.StationaryMoment

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem358.StationaryMoment

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- The stationary-site moment derivative bound for actual moving cells.
Only ordinary derivatives and genuine normalized midpoint couplings are
assumed. All nearby mass comparisons follow from continuity. -/
theorem stationary_moment_derivative_of_normalized_cells
    (ρ : Measure F) [IsFiniteMeasure ρ] (P : ℝ → ι → Set F)
    (hP : ∀ s, AECellPartition ρ (P s))
    (R : ℝ) (hR : 0 ≤ R) (hbounded : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (dB : ι → F) (dm : ι → ℝ)
    (hM : ∀ i, 0 < ρ.real (P 0 i))
    (hB : ∀ i, HasDerivAt (fun s => ∫ x in P s i, x ∂ρ) (dB i) 0)
    (hm : ∀ i, HasDerivAt (fun s => ρ.real (P s i)) (dm i) 0)
    (hw : ∀ᶠ s : ℝ in 𝓝[>] 0,
      Nonempty (NormalizedMidpointWitness ρ (P (-s)) (P s) (P 0))) :
    (∑ i, ‖dB i‖ ^ 2 / ρ.real (P 0 i)) ≤
      162 * R ^ 2 * ∑ i, dm i ^ 2 / ρ.real (P 0 i) := by
  have hneg : Filter.Tendsto (fun s : ℝ => -s) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmass := eventually_nearby_mass_bounds (fun i => ρ.real (P 0 i))
    (fun s i => ρ.real (P (-s) i)) (fun s i => ρ.real (P s i)) hM
    (fun i => (hm i).continuousAt.tendsto.comp hneg)
    (fun i => (hm i).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  apply stationary_moment_derivative_of_midpoint_data (A := F × F) hR hM hB hm
  filter_upwards [hw, hmass] with s hs hms
  obtain ⟨w⟩ := hs
  let : ∀ i, IsProbabilityMeasure (w.coupling i) := w.probability
  have hleftpos : ∀ i, ρ (P (-s) i) ≠ 0 := by
    intro i hz
    have hp := (hms i).1
    simp [Measure.real_def, hz] at hp
  have hrightpos : ∀ i, ρ (P s i) ≠ 0 := by
    intro i hz
    have hp := (hms i).2.1
    simp [Measure.real_def, hz] at hp
  exact ⟨midpointComparisonData_of_normalized_cells ρ (P (-s)) (P s) (P 0)
    (hP (-s)) (hP s) (hP 0) hleftpos hrightpos w.coupling
    w.left_marginal w.right_marginal (fun i => ρ.real (P 0 i))
    (fun i => Real.sqrt (ρ.real (P (-s) i) * ρ.real (P s i))) R hbounded
    (fun i => (hms i).2.2.1) (fun i => (hms i).2.2.2)
    (fun i => Real.sq_sqrt (mul_nonneg (hms i).1.le (hms i).2.1.le))
    w.midpoint_dominated⟩

end Problem358.StationaryMoment

end

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Problem358
namespace CellGeometry

/-- The actual distinct-site closed cells form the normalized source partition. -/
theorem aePartition_uniform_closedCell {d : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) :
    StationaryMoment.AECellPartition (uniformMeasure K) (closedCell K y c) where
  measurable i := (isClosed_closedCell hK y c i).measurableSet
  disjoint := pairwise_aedisjoint_closedCell
    (Measure.absolutelyContinuous_restrict.smul_left _) K y c hy
  cover := by
    simpa only [iUnion_closedCell] using UniformSource.ae_mem hK.measurableSet

/-- The raw-volume geometric mean converts to the geometric mean of normalized
cell masses with exactly one source-volume factor. -/
theorem ofReal_sqrt_uniform_cell_masses {d : ℕ} {K U V : Set (E d)}
    (hKpos : 0 < volume K) (hKfinite : volume K ≠ ∞)
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUK : U ⊆ K) (hVK : V ⊆ K) :
    ENNReal.ofReal (Real.sqrt ((uniformMeasure K).real U * (uniformMeasure K).real V)) =
      (volume K)⁻¹ * ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) := by
  rw [uniformMeasure_real_cell hU hUK, uniformMeasure_real_cell hV hVK]
  have hk : 0 < (volume K).toReal := ENNReal.toReal_pos hKpos.ne' hKfinite
  have heq : (volume U).toReal / (volume K).toReal *
      ((volume V).toReal / (volume K).toReal) =
      ((volume U).toReal * (volume V).toReal) / ((volume K).toReal ^ 2) := by ring
  rw [heq, Real.sqrt_div (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
    Real.sqrt_sq hk.le, ENNReal.ofReal_div_of_pos hk, ENNReal.ofReal_toReal hKfinite,
    div_eq_mul_inv, mul_comm]

/-- A raw midpoint coupling supported by a middle cell yields the exact normalized
restricted domination used in the stationary moment estimate. -/
theorem normalized_midpoint_domination {d : ℕ} {K U V H : Set (E d)}
    (hKpos : 0 < volume K) (hKfinite : volume K ≠ ∞)
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hH : MeasurableSet H)
    (hUK : U ⊆ K) (hVK : V ⊆ K) (hHK : H ⊆ K)
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (uniformMeasure U) (uniformMeasure V) π)
    (hsupport : ∀ x ∈ U, ∀ z ∈ V, (1 / 2 : ℝ) • (x + z) ∈ H)
    (hdom : ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
      Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    ENNReal.ofReal (Real.sqrt ((uniformMeasure K).real U * (uniformMeasure K).real V)) •
      Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤
        (uniformMeasure K).restrict H := by
  have hl : ∀ᵐ p : E d × E d ∂π, p.1 ∈ U := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hπ.2.1]
    exact UniformSource.ae_mem hU
  have hr : ∀ᵐ p : E d × E d ∂π, p.2 ∈ V := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact UniformSource.ae_mem hV
  have hm : ∀ᵐ x ∂Measure.map
      (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π, x ∈ H := by
    apply (ae_map_iff (by fun_prop) hH).2
    filter_upwards [hl, hr] with p hp hq
    exact hsupport p.1 hp p.2 hq
  have hraw := Measure.restrict_mono (Subset.refl H) hdom
  rw [Measure.restrict_smul, Measure.restrict_eq_self_of_ae_mem hm] at hraw
  rw [ofReal_sqrt_uniform_cell_masses hKpos hKfinite hU hV hUK hVK,
    mul_smul, uniformMeasure, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset hHK]
  exact smul_le_smul_left _ hraw

/-- A raw dominated coupling of the two opposite intercept cells supplies the
exact normalized cell witness, with all support and normalization requirements
derived from the actual affine cell geometry. -/
theorem normalized_witness_closedCells {d : ℕ} {ι : Type*} [Fintype ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (y : ι → E d) (c q : ι → ℝ) (s : ℝ)
    (hraw : ∀ i, ∃ π : Measure (E d × E d),
      IsCoupling (uniformMeasure (closedCell K y (fun j => c j - s * q j) i))
        (uniformMeasure (closedCell K y (fun j => c j + s * q j) i)) π ∧
      ENNReal.ofReal (Real.sqrt
        ((volume (closedCell K y (fun j => c j - s * q j) i)).toReal *
          (volume (closedCell K y (fun j => c j + s * q j) i)).toReal)) •
        Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    Nonempty (StationaryMoment.NormalizedMidpointWitness (uniformMeasure K)
      (closedCell K y (fun j => c j - s * q j))
      (closedCell K y (fun j => c j + s * q j)) (closedCell K y c)) := by
  classical
  choose π hπ hdom using hraw
  have hk : 0 < volume K := Measure.measure_pos_of_nonempty_interior volume hKi
  refine ⟨{ coupling := π
            probability := fun i => (hπ i).1
            left_marginal := ?_
            right_marginal := ?_
            midpoint_dominated := ?_ }⟩
  · intro i
    change Measure.map Prod.fst (π i) =
      NormalizedCell.measure (uniformMeasure K) (closedCell K y (fun j => c j - s * q j) i)
    rw [normalizedCell_uniformMeasure hk hK.measure_ne_top
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet (closedCell_subset _ _ _ _)]
    exact (hπ i).2.1
  · intro i
    change Measure.map Prod.snd (π i) =
      NormalizedCell.measure (uniformMeasure K) (closedCell K y (fun j => c j + s * q j) i)
    rw [normalizedCell_uniformMeasure hk hK.measure_ne_top
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet (closedCell_subset _ _ _ _)]
    exact (hπ i).2.2
  · intro i
    apply normalized_midpoint_domination hk hK.measure_ne_top
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet
      (isClosed_closedCell hK.isClosed _ _ _).measurableSet
      (closedCell_subset _ _ _ _) (closedCell_subset _ _ _ _) (closedCell_subset _ _ _ _)
      (hπ i) ?_ (hdom i)
    intro x hx z hz
    simpa only [smul_add] using midpoint_mem_closedCell hconv y c q i s hx hz

end CellGeometry
end Problem358

namespace Problem358.CellGeometry

/-- Stationary-site moment coercivity for the actual affine cells. The only
geometric input not supplied internally is the convex-body midpoint coupling;
ordinary mass and moment derivatives are left in the form delivered by cell
calculus. In particular no cell partition, scaled-law, nearby-mass, or energy
hypothesis remains. -/
theorem stationary_moment_derivative_of_convex_midpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (y : ι → E d) (c q : ι → ℝ)
    (hy : Function.Injective y) (R : ℝ) (hR : 0 ≤ R)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (dB : ι → E d) (dm : ι → ℝ)
    (hM : ∀ i, 0 < (uniformMeasure K).real (closedCell K y c i))
    (hB : ∀ i, HasDerivAt
      (fun s : ℝ => ∫ x in closedCell K y (fun j => c j + s * q j) i, x ∂uniformMeasure K)
      (dB i) 0)
    (hm : ∀ i, HasDerivAt
      (fun s : ℝ => (uniformMeasure K).real (closedCell K y (fun j => c j + s * q j) i))
      (dm i) 0)
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    (∑ i, ‖dB i‖ ^ 2 / (uniformMeasure K).real (closedCell K y c i)) ≤
      162 * R ^ 2 * ∑ i, dm i ^ 2 / (uniformMeasure K).real (closedCell K y c i) := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hKi
  let P : ℝ → ι → Set (E d) := fun s => closedCell K y (fun j => c j + s * q j)
  have hzero : P 0 = closedCell K y c := by
    simp only [P, zero_mul, add_zero]
  have hP : ∀ s, StationaryMoment.AECellPartition (uniformMeasure K) (P s) :=
    fun s => aePartition_uniform_closedCell hK.isClosed y _ hy
  have hmass0 : ∀ i, 0 < (uniformMeasure K).real (P 0 i) := by rwa [hzero]
  have hneg : Filter.Tendsto (fun s : ℝ => -s) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmass := eventually_nearby_mass_bounds (fun i => (uniformMeasure K).real (P 0 i))
    (fun s i => (uniformMeasure K).real (P (-s) i))
    (fun s i => (uniformMeasure K).real (P s i)) hmass0
    (fun i => (hm i).continuousAt.tendsto.comp hneg)
    (fun i => (hm i).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hvol {A : Set (E d)} (ha : 0 < (uniformMeasure K).real A) : 0 < volume A := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hzero' : (uniformMeasure K).real A = 0 := by
      simp only [Measure.real_def, hac hz, ENNReal.toReal_zero]
    exact ha.ne' hzero'
  have hw : ∀ᶠ s : ℝ in 𝓝[>] 0,
      Nonempty (StationaryMoment.NormalizedMidpointWitness (uniformMeasure K)
        (P (-s)) (P s) (P 0)) := by
    filter_upwards [hmass] with s hs
    have hraw : ∀ i, ∃ π : Measure (E d × E d),
        IsCoupling (uniformMeasure (closedCell K y (fun j => c j - s * q j) i))
          (uniformMeasure (closedCell K y (fun j => c j + s * q j) i)) π ∧
        ENNReal.ofReal (Real.sqrt
          ((volume (closedCell K y (fun j => c j - s * q j) i)).toReal *
            (volume (closedCell K y (fun j => c j + s * q j) i)).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
      intro i
      apply hmid _ _ (isCompact_closedCell hK _ _ _) (convex_closedCell hconv _ _ _) _
        (isCompact_closedCell hK _ _ _) (convex_closedCell hconv _ _ _) _
      · apply hvol
        simpa only [P, neg_mul, sub_eq_add_neg] using (hs i).1
      · exact hvol (hs i).2.1
    simpa only [P, neg_mul, sub_eq_add_neg, zero_mul, add_zero] using
      normalized_witness_closedCells hK hconv hKi y c q s hraw
  have h := StationaryMoment.stationary_moment_derivative_of_normalized_cells
    (uniformMeasure K) P hP R hR hbounded dB dm hmass0 hB hm hw
  simpa only [hzero] using h

end Problem358.CellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_InterceptEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358.CellGeometry

/-- The stationary moment estimate in the face-coordinate form required by the
mass-Jacobian argument. The two derivative hypotheses are ordinary derivatives
of the actual closed-cell integrals, not quantitative inequalities. -/
theorem stationary_face_moment_estimate
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (y : ι → E d) (c q : ι → ℝ)
    (hy : Function.Injective y) (R : ℝ) (hR : 0 ≤ R)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i)
    (hmass : ∀ i, (uniformMeasure K).real (closedCell K y c i) = m i)
    (g : ι → ι → ℝ) (b : ι → ι → E d)
    (hB : ∀ i, HasDerivAt
      (fun s : ℝ => ∫ x in closedCell K y (fun j => c j + s * q j) i,
        x ∂uniformMeasure K) (∑ j, (q i - q j) • b i j) 0)
    (hM : ∀ i, HasDerivAt
      (fun s : ℝ => (uniformMeasure K).real
        (closedCell K y (fun j => c j + s * q j) i))
      (CellLaplacian.apply g q i) 0)
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    (∑ i, ‖∑ j, (q i - q j) • b i j‖ ^ 2 / m i) ≤
      162 * R ^ 2 * ∑ i, (CellLaplacian.apply g q i) ^ 2 / m i := by
  have hpos : ∀ i, 0 < (uniformMeasure K).real (closedCell K y c i) := by
    intro i
    rw [hmass i]
    exact hm i
  simpa only [hmass] using stationary_moment_derivative_of_convex_midpoint
    hK hconv hKi y c q hy R hR hbounded
    (fun i => ∑ j, (q i - q j) • b i j) (CellLaplacian.apply g q) hpos hB hM hmid

/-- Actual cell derivatives and convex-body midpoint couplings supply the full
weighted intercept-energy estimate. No moment inequality or inverse-Jacobian
estimate is assumed: the stationary estimate and connected range argument are
both invoked internally. -/
theorem fixed_mass_intercept_energy_of_convex_midpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty) (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (R : ℝ) (hR : 0 ≤ R)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (m r : ι → ℝ) (v : ι → E d) {w : ℝ}
    (hm : ∀ i, 0 < m i)
    (hmass : ∀ i, (uniformMeasure K).real (closedCell K y c i) = m i)
    (g : ι → ι → ℝ) (b : ι → ι → E d)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (hmean : ∑ i, m i * r i = 0)
    (hfixed : ∀ i, CellLaplacian.apply g r i +
      (∑ j, inner ℝ (b i j) (v i - v j)) = 0)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hB : ∀ (q : ι → ℝ) i, HasDerivAt
      (fun s : ℝ => ∫ x in closedCell K y (fun j => c j + s * q j) i,
        x ∂uniformMeasure K) (∑ j, (q i - q j) • b i j) 0)
    (hM : ∀ (q : ι → ℝ) i, HasDerivAt
      (fun s : ℝ => (uniformMeasure K).real
        (closedCell K y (fun j => c j + s * q j) i))
      (CellLaplacian.apply g q i) 0)
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    (∑ i, m i * r i ^ 2) ≤ 162 * R ^ 2 * w ^ 2 := by
  apply Problem358.fixed_mass_intercept_energy_le_162 g b hg hb hg0 G hG hpos
    m r v hm hmean hfixed hspeed
  intro q
  exact stationary_face_moment_estimate hK hconv hKi y c q hy R hR hbounded
    m hm hmass g b (hB q) (hM q) hmid

end Problem358.CellGeometry

end

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal ContDiff

namespace Problem358.FixedMassIntercepts

/-- The canonical prescribed-mass intercept path has the required uniform
weighted derivative energy. All branch existence, uniqueness, differentiability,
normalization and fixed-mass differentiation are supplied internally. The
remaining inputs are the actual geometric mass/moment differentials and the
convex-body midpoint coupling. -/
theorem intercepts_comp_deriv_energy_le_of_convex_midpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (Y : ℝ → (ι → E d)) (v : ι → E d) (t : ℝ)
    (hY : HasDerivAt Y v t) (hy : Function.Injective (Y t))
    (R : ℝ) (hR : 0 ≤ R) {w : ℝ}
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (g : ι → ι → ℝ) (b : ι → ι → E d)
    (hg : ∀ i j, g i j = g j i) (hb : ∀ i j, b i j = b j i)
    (hg0 : ∀ i j, 0 ≤ g i j) (G : SimpleGraph ι)
    (hG : G.Connected) (hpos : ∀ i j, G.Adj i j → 0 < g i j)
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hC1 : ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m)
      (Y t, intercepts hK hconv hKi m hm hsum (Y t)))
    (hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A
      (Y t, intercepts hK hconv hKi m hm hsum (Y t)))
    (hA : ∀ q : CellLaplacian.normalizedSpace m, A (0, q) = CellLaplacian.apply g q)
    (hsite : A (v, 0) = CellLaplacian.siteFlux b v)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hB : ∀ (q : ι → ℝ) i, HasDerivAt
      (fun s : ℝ => ∫ x in CellGeometry.closedCell K (Y t)
        (fun j => (intercepts hK hconv hKi m hm hsum (Y t) : ι → ℝ) j + s * q j) i,
        x ∂uniformMeasure K) (∑ j, (q i - q j) • b i j) 0)
    (hM : ∀ (q : ι → ℝ) i, HasDerivAt
      (fun s : ℝ => (uniformMeasure K).real (CellGeometry.closedCell K (Y t)
        (fun j => (intercepts hK hconv hKi m hm hsum (Y t) : ι → ℝ) j + s * q j) i))
      (CellLaplacian.apply g q i) 0)
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    let C := fun q => intercepts hK hconv hKi m hm hsum (Y q)
    HasDerivAt C (deriv C t) t ∧
      (∑ i, m i * ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i ^ 2) ≤
        162 * R ^ 2 * w ^ 2 := by
  let C := fun q => intercepts hK hconv hKi m hm hsum (Y q)
  have hregular := contDiffAt_intercepts_of_massDifferential hK hconv hKi m hm hsum
    (Y t) hy g hg hg0 G hG hpos A hC1 hD hA
  have hs := hregular.differentiableAt (by norm_num)
  obtain ⟨hdC, hfixed, hmean⟩ := hasDerivAt_intercepts_comp_and_mass_constraint
    hK hconv hKi m hm hsum Y v t hY hy hs A hD
  refine ⟨hdC, ?_⟩
  apply CellGeometry.fixed_mass_intercept_energy_of_convex_midpoint
    hK hconv hKi (Y t) (C t) hy R hR hbounded m
    ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) v hm
    (fun i => congrFun (intercepts_spec hK hconv hKi m hm hsum (Y t) hy) i)
    g b hg hb hg0 G hG hpos hmean _ hspeed hB hM hmid
  have hsplit : A (v, deriv C t) = A (v, 0) + A (0, deriv C t) := by
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  rw [hsplit, hA, hsite] at hfixed
  intro i
  have hi := congrFun hfixed i
  change CellLaplacian.siteFlux b v i + CellLaplacian.apply g
    ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i = 0 at hi
  simpa only [CellLaplacian.siteFlux, add_comm] using hi

end Problem358.FixedMassIntercepts

namespace Problem358.CellGeometry

/-- Any Fréchet derivative of the actual normalized mass map has the canonical
geometric formula. This follows by uniqueness from the proved line derivative;
it is independent of how the bounded linear operator was constructed. -/
theorem normalizedMassMap_derivative_apply
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (m : ι → ℝ) (y : ι → E d) (c : CellLaplacian.normalizedSpace m)
    (hy : Function.Injective y) (hpos : ∀ i, ρ (closedCell K y c i) ≠ 0)
    (A : ((ι → E d) × CellLaplacian.normalizedSpace m) →L[ℝ] (ι → ℝ))
    (hD : HasFDerivAt (normalizedMassMap K m) A (y, c))
    (v : ι → E d) (q : CellLaplacian.normalizedSpace m) :
    A (v, q) = CellLaplacian.apply (PositiveFacet.canonicalFaceWeight K y c) q +
      CellLaplacian.siteFlux (faceMoment K y c) v := by
  classical
  have hd := hD.hasLineDerivAt (v, q)
  change HasDerivAt (fun s : ℝ => normalizedMassMap K m ((y, c) + s • (v, q)))
    (A (v, q)) 0 at hd
  funext i
  apply (hasDerivAt_pi.mp hd i).unique
  simpa [normalizedMassMap, CellLaplacian.apply, CellLaplacian.siteFlux,
    PositiveFacet.canonicalFaceWeight, Finset.sum_add_distrib,
    Pi.add_def, Pi.smul_def, smul_eq_mul] using
    hasDerivAt_uniformMass_line hρ hK hconv y v c q hy hpos i

end Problem358.CellGeometry

namespace Problem358.FixedMassIntercepts

/-- Genuine C¹ regularity of the normalized mass map implies C¹ regularity of
the canonical prescribed-mass choice. The geometric derivative and connected
Laplacian are identified internally, independently of any operator API. -/
theorem contDiffAt_intercepts_of_normalizedMassC1
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y)
    (hC1 : ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m)
      (y, intercepts hK hconv hKi m hm hsum y)) :
    ContDiffAt ℝ 1 (intercepts hK hconv hKi m hm hsum) y := by
  classical
  let c := intercepts hK hconv hKi m hm hsum y
  let g := PositiveFacet.canonicalFaceWeight K y c
  have hρ : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hpos : ∀ i, uniformMeasure K (CellGeometry.closedCell K y c i) ≠ 0 := by
    intro i hz
    have hi := congrFun (intercepts_spec hK hconv hKi m hm hsum y hy) i
    change (uniformMeasure K).real (CellGeometry.closedCell K y c i) = m i at hi
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hi
    exact (hm i).ne' hi.symm
  obtain ⟨G, hG, hGp⟩ := PositiveFacet.canonicalFaceWeight_connected
    (uniformMeasure K) hρ K hK hconv y c hy hpos
  let A := fderiv ℝ (CellGeometry.normalizedMassMap K m) (y, c)
  have hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A (y, c) :=
    (hC1.differentiableAt (by norm_num)).hasFDerivAt
  apply contDiffAt_intercepts_of_massDifferential hK hconv hKi m hm hsum y hy g
    (PositiveFacet.canonicalFaceWeight_symm K y c)
    (PositiveFacet.canonicalFaceWeight_nonneg K y c) G hG hGp A hC1 hD
  intro q
  funext i
  simpa [CellLaplacian.siteFlux, g] using congrFun
    (CellGeometry.normalizedMassMap_derivative_apply hρ hK hconv m y c hy hpos A hD 0 q) i

/-- Pointwise derivative energy for the actual canonical intercepts, with every
face, graph, mass and moment differential supplied by the geometry. Only C¹
regularity of the actual normalized mass map and the convex midpoint coupling
remain as analytic inputs. No operator formula or chosen-branch hypothesis is
assumed. -/
theorem intercepts_comp_deriv_energy_le_of_massC1_convex_midpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (Y : ℝ → (ι → E d)) (v : ι → E d) (t : ℝ)
    (hY : HasDerivAt Y v t) (hy : Function.Injective (Y t))
    (R : ℝ) (hR : 0 ≤ R) {w : ℝ}
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ w ^ 2)
    (hC1 : ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m)
      (Y t, intercepts hK hconv hKi m hm hsum (Y t)))
    (hmid : ∀ (U V : Set (E d)), IsCompact U → Convex ℝ U → 0 < volume U →
      IsCompact V → Convex ℝ V → 0 < volume V →
      ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure U) (uniformMeasure V) π ∧
        ENNReal.ofReal (Real.sqrt ((volume U).toReal * (volume V).toReal)) •
          Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume) :
    let C := fun q => intercepts hK hconv hKi m hm hsum (Y q)
    HasDerivAt C (deriv C t) t ∧
      (∑ i, m i * ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i ^ 2) ≤
        162 * R ^ 2 * w ^ 2 := by
  classical
  let c := intercepts hK hconv hKi m hm hsum (Y t)
  let g := PositiveFacet.canonicalFaceWeight K (Y t) c
  let b := CellGeometry.faceMoment K (Y t) c
  have hρ : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hpos : ∀ i, uniformMeasure K (CellGeometry.closedCell K (Y t) c i) ≠ 0 := by
    intro i hz
    have hi := congrFun (intercepts_spec hK hconv hKi m hm hsum (Y t) hy) i
    change (uniformMeasure K).real (CellGeometry.closedCell K (Y t) c i) = m i at hi
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hi
    exact (hm i).ne' hi.symm
  obtain ⟨G, hG, hGp⟩ := PositiveFacet.canonicalFaceWeight_connected
    (uniformMeasure K) hρ K hK hconv (Y t) c hy hpos
  let A := fderiv ℝ (CellGeometry.normalizedMassMap K m) (Y t, c)
  have hD : HasFDerivAt (CellGeometry.normalizedMassMap K m) A (Y t, c) :=
    (hC1.differentiableAt (by norm_num)).hasFDerivAt
  have hformula := CellGeometry.normalizedMassMap_derivative_apply
    hρ hK hconv m (Y t) c hy hpos A hD
  apply intercepts_comp_deriv_energy_le_of_convex_midpoint hK hconv hKi m hm hsum
    Y v t hY hy R hR hbounded g b
    (PositiveFacet.canonicalFaceWeight_symm K (Y t) c)
    (CellGeometry.faceMoment_symm K (Y t) c)
    (PositiveFacet.canonicalFaceWeight_nonneg K (Y t) c) G hG hGp A hC1 hD
  · intro q
    funext i
    simpa [CellLaplacian.siteFlux, b, g] using congrFun (hformula 0 q) i
  · funext i
    simpa [CellLaplacian.apply, b, g] using congrFun (hformula v 0) i
  · exact hspeed
  · intro q i
    exact PositiveCellFullDerivative.hasDerivAt_uniform_closedCell_moment_stationary
      hρ hK hconv (Y t) c q hy hpos i
  · intro q i
    simpa [CellLaplacian.apply, g, PositiveFacet.canonicalFaceWeight] using
      CellGeometry.hasDerivAt_uniformMass_line hρ hK hconv (Y t) (fun _ => 0) c q hy hpos i
  · exact hmid

end Problem358.FixedMassIntercepts

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_TriangularRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem358.TriangularRecursion

/-- Joint measurability of all conditional samplers gives a measurable full sampler. -/
theorem measurable_sample (Q : ConditionalFamily)
    (hQ : ∀ n, Measurable (fun p : (Fin n → ℝ) × ℝ => Q n p.1 p.2)) :
    ∀ n, Measurable (sample Q n) := by
  intro n
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
      have hi : Measurable (fun s : Fin (n+1) → ℝ => Fin.init s) := by
        apply Measurable.of_eval
        intro i
        exact measurable_pi_apply i.castSucc
      have hp := ih.comp hi
      apply Measurable.of_eval
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [sample_last, Function.comp_def] using
          (hQ n).comp (hp.prodMk (measurable_pi_apply (Fin.last n)))
      · simpa only [sample, Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp hp

/-- This is the exact triangular decomposition required by iterated substitution. -/
theorem midpoint_snoc (Q R : ConditionalFamily) (n : ℕ) (s : Fin n → ℝ) (t : ℝ) :
    midpoint Q R (n+1) (Fin.snoc s t) =
      Fin.snoc (midpoint Q R n s) (midpointFiber Q R n s t) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [midpoint, midpointFiber]
  · simp [midpoint, sample_snoc]

end Problem358.TriangularRecursion

end

/-! Finite-prefix density normalization for the canonical triangular sampler.
These are conditional identities, not existence of geometric section data. -/

noncomputable section
open Set
open scoped BigOperators
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

lemma InUnitCube.init {n : ℕ} {u : Coordinates (n + 1)} (hu : InUnitCube u) :
    InUnitCube (Fin.init u) := fun i => hu i.castSucc

lemma InUnitCube.last {n : ℕ} {u : Coordinates (n + 1)} (hu : InUnitCube u) :
    u (Fin.last n) ∈ Ioo (0 : ℝ) 1 := hu (Fin.last n)

end Problem358.TriangularDensity

end

/-! Positivity and almost-everywhere parameter support for finite triangular samplers. -/

noncomputable section
open MeasureTheory Set
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

/-- The finite product of interval-restricted Lebesgue measures is concentrated
on the open unit cube, including the zero-dimensional case. -/
theorem ae_inUnitCube (n : ℕ) :
    ∀ᵐ u ∂(Measure.pi fun _ : Fin n =>
      (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), InUnitCube u := by
  apply Filter.eventually_all.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioo)

/-- Positive longitudinal derivatives along valid sampled prefixes give a
positive diagonal product. No assumptions above the finite cutoff are needed. -/
theorem diagonalProduct_pos_of_le (q dq : ConditionalFamily) (N : ℕ)
    (hpos : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n u) t) :
    ∀ n, n ≤ N → ∀ u, InUnitCube u → 0 < diagonalProduct q dq n u := by
  intro n
  induction n with
  | zero =>
      intro hn u hu
      exact zero_lt_one
  | succ n ih =>
      intro hn u hu
      exact mul_pos (ih (by omega) (Fin.init u) hu.init)
        (hpos n (by omega) (Fin.init u) hu.init _ hu.last)

end Problem358.TriangularDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_TriangularSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem358

/-- Appending the last coordinate identifies a finite product law with a product of
its prefix law and its last-coordinate law. -/
theorem measurePreserving_finSnoc {X : Type*} [MeasurableSpace X]
    (n : ℕ) (η : Measure X) [SigmaFinite η] :
    MeasurePreserving (fun p : (Fin n → X) × X => Fin.snoc p.1 p.2)
      ((Measure.pi fun _ : Fin n => η).prod η)
      (Measure.pi fun _ : Fin (n + 1) => η) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => η)
    (Fin.last n)).symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X)
      (Fin.last n))
  have hh := h.comp (Measure.measurePreserving_swap
    (μ := Measure.pi fun _ : Fin n => η) (ν := η))
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last,
    Fin.snocEquiv, Function.comp_def] using hh

end Problem358

end

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Problem358

namespace TriangularSampling

variable {A B X Y : Type*}
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable triangular sampler has the prescribed dependent-product law
when its prefix has the prescribed law and its last coordinate has the
prescribed conditional law almost everywhere. -/
theorem map_prod_eq_compProd
    (μ : Measure A) (η : Measure B) (ρ : Measure X) (κ : Kernel X Y)
    [SFinite μ] [SFinite η] [SFinite ρ] [IsSFiniteKernel κ]
    (F : A → X) (G : A × B → Y)
    (hF : Measurable F) (hG : Measurable G)
    (hbase : Measure.map F μ = ρ)
    (hfiber : ∀ᵐ a ∂μ, Measure.map (fun b => G (a, b)) η = κ (F a)) :
    Measure.map (fun p : A × B => (F p.1, G p)) (μ.prod η) = ρ ⊗ₘ κ := by
  ext s hs
  have hpair : Measurable (fun p : A × B => (F p.1, G p)) :=
    (hF.comp measurable_fst).prodMk hG
  rw [Measure.map_apply hpair hs, Measure.prod_apply (hs.preimage hpair),
    Measure.compProd_apply hs, ← hbase,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hF]
  apply lintegral_congr_ae
  filter_upwards [hfiber] with a ha
  change η ((fun b => G (a, b)) ⁻¹' (Prod.mk (F a) ⁻¹' s)) =
    κ (F a) (Prod.mk (F a) ⁻¹' s)
  have hGa : Measurable (fun b : B => G (a, b)) :=
    hG.comp measurable_prodMk_left
  have hsa : MeasurableSet (Prod.mk (F a) ⁻¹' s) :=
    measurable_prodMk_left hs
  rw [← ha]
  exact (Measure.map_apply hGa hsa).symm

/-- Splitting a finite product at its last coordinate preserves its product law. -/
theorem map_init_last_pi {Z : Type*} [MeasurableSpace Z]
    (η : Measure Z) [SigmaFinite η] (n : ℕ) :
    Measure.map (fun s : Fin (n + 1) → Z => (Fin.init s, s (Fin.last n)))
      (Measure.pi (fun _ : Fin (n + 1) => η)) =
      (Measure.pi (fun _ : Fin n => η)).prod η := by
  have h := Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => η) (Fin.last n))
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply,
    Fin.insertNthEquiv_symm_apply, Fin.removeNth_last, Prod.swap_prod_mk] using h.map_eq

/-- The last-coordinate induction step for the law of a finite triangular sampler. -/
theorem map_snoc_pi_eq
    (n : ℕ) (η : Measure B) [SigmaFinite η]
    (ρ : Measure (Fin n → Y)) (κ : Kernel (Fin n → Y) Y)
    [SFinite ρ] [IsSFiniteKernel κ]
    (F : (Fin n → B) → (Fin n → Y)) (G : (Fin n → B) × B → Y)
    (hF : Measurable F) (hG : Measurable G)
    (hbase : Measure.map F (Measure.pi (fun _ : Fin n => η)) = ρ)
    (hfiber : ∀ᵐ a ∂Measure.pi (fun _ : Fin n => η),
      Measure.map (fun b => G (a, b)) η = κ (F a)) :
    Measure.map (fun s : Fin (n + 1) → B =>
      Fin.snoc (F (Fin.init s)) (G (Fin.init s, s (Fin.last n))))
      (Measure.pi (fun _ : Fin (n + 1) => η)) =
      Measure.map (fun p : (Fin n → Y) × Y => (Fin.snoc p.1 p.2 : Fin (n + 1) → Y)) (ρ ⊗ₘ κ) := by
  let μ := Measure.pi (fun _ : Fin n => η)
  have hsplit : Measurable (fun s : Fin (n + 1) → B =>
      (Fin.init s, s (Fin.last n))) :=
    (measurable_pi_iff.2 fun i => measurable_pi_apply i.castSucc).prodMk
      (measurable_pi_apply (Fin.last n))
  have hsnoc : Measurable (fun p : (Fin n → Y) × Y => (Fin.snoc p.1 p.2 : Fin (n + 1) → Y)) := by
    apply measurable_pi_iff.2
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (measurable_snd : Measurable (fun p : (Fin n → Y) × Y => p.2))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp
          (measurable_fst : Measurable (fun p : (Fin n → Y) × Y => p.1))
  have hpair : Measurable (fun p : (Fin n → B) × B => (F p.1, G p)) :=
    (hF.comp measurable_fst).prodMk hG
  have htotal : Measurable (fun p : (Fin n → B) × B =>
      (Fin.snoc (F p.1) (G p) : Fin (n + 1) → Y)) := by
    simpa only [Function.comp_def] using hsnoc.comp hpair
  calc
    _ = Measure.map (fun p : (Fin n → B) × B => (Fin.snoc (F p.1) (G p) : Fin (n + 1) → Y))
        (μ.prod η) := by
      rw [show μ.prod η = Measure.map
        (fun s : Fin (n + 1) → B => (Fin.init s, s (Fin.last n)))
        (Measure.pi (fun _ : Fin (n + 1) => η)) from
          (map_init_last_pi η n).symm]
      rw [Measure.map_map htotal hsplit]
      rfl
    _ = Measure.map (fun p : (Fin n → Y) × Y => (Fin.snoc p.1 p.2 : Fin (n + 1) → Y))
        (Measure.map (fun p : (Fin n → B) × B => (F p.1, G p)) (μ.prod η)) := by
      rw [Measure.map_map hsnoc hpair]
      rfl
    _ = _ := by
      rw [map_prod_eq_compProd μ η ρ κ F G hF hG hbase hfiber]

end TriangularSampling

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_NormalizedSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Classical
open scoped ENNReal

namespace Problem358.NormalizedSections

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem measurable_sectionDensity (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry (sectionDensity ν q)) := by
  exact hq.div ((measurable_sectionMass ν hq).comp measurable_fst)

/-- Every nonzero finite section has a normalized probability density. -/
theorem lintegral_sectionDensity_eq_one (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (a : A) (h0 : sectionMass ν q a ≠ 0) (hfin : sectionMass ν q a ≠ ∞) :
    (∫⁻ b, sectionDensity ν q a b ∂ν) = 1 := by
  simp only [sectionDensity, div_eq_mul_inv]
  rw [lintegral_mul_const _ hq.of_uncurry_left]
  exact ENNReal.mul_inv_cancel h0 hfin

theorem isProbabilityMeasure_sectionLaw (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (a : A) (h0 : sectionMass ν q a ≠ 0) (hfin : sectionMass ν q a ≠ ∞) :
    IsProbabilityMeasure (sectionLaw ν q a) := by
  constructor
  rw [sectionLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_sectionDensity_eq_one ν hq a h0 hfin

/-- Multiplication by the section mass cancels conditional normalization, including
zero-mass sections; only infinite-mass sections have to be excluded. -/
theorem sectionMass_mul_lintegral_sectionLaw (ν : Measure B)
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (a : A) (hfin : sectionMass ν q a ≠ ∞)
    {f : B → ℝ≥0∞} (hf : Measurable f) :
    sectionMass ν q a * (∫⁻ b, f b ∂sectionLaw ν q a) =
      ∫⁻ b, q a b * f b ∂ν := by
  by_cases h0 : sectionMass ν q a = 0
  · rw [h0, zero_mul]
    have hz : q a =ᵐ[ν] 0 := (lintegral_eq_zero_iff hq.of_uncurry_left).mp h0
    symm
    apply lintegral_eq_zero_iff (hq.of_uncurry_left.mul hf) |>.mpr
    filter_upwards [hz] with b hb
    simp [hb]
  · have hd : Measurable (sectionDensity ν q a) :=
      hq.of_uncurry_left.div measurable_const
    rw [sectionLaw, lintegral_withDensity_eq_lintegral_mul ν hd hf]
    have he : (fun b => sectionDensity ν q a b * f b) =
        (fun b => (sectionMass ν q a)⁻¹ * (q a b * f b)) := by
      funext b
      simp only [sectionDensity, div_eq_mul_inv]
      ac_rfl
    change sectionMass ν q a * (∫⁻ b, sectionDensity ν q a b * f b ∂ν) = _
    have hj : Measurable (fun b => q a b * f b) := hq.of_uncurry_left.mul hf
    rw [he, lintegral_const_mul _ hj,
      ← mul_assoc, ENNReal.mul_inv_cancel h0 hfin, one_mul]

/-- Conditional integration preserves measurability in the parameter. -/
theorem measurable_lintegral_sectionLaw (ν : Measure B) [SFinite ν]
    {q f : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun a => ∫⁻ b, f a b ∂sectionLaw ν q a) := by
  have he : (fun a => ∫⁻ b, f a b ∂sectionLaw ν q a) =
      (fun a => ∫⁻ b, sectionDensity ν q a b * f a b ∂ν) := by
    funext a
    exact lintegral_withDensity_eq_lintegral_mul ν
      ((measurable_sectionDensity ν hq).of_uncurry_left) hf.of_uncurry_left
  rw [he]
  exact ((measurable_sectionDensity ν hq).mul hf).lintegral_prod_right

/-- Exact disintegration of a product density into its section mass and normalized
section laws. The finite-mass hypothesis is only almost everywhere. -/
theorem lintegral_reassemble_sections (μ : Measure A) (ν : Measure B) [SFinite ν]
    {q f : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞) :
    (∫⁻ a, ∫⁻ b, f a b ∂sectionLaw ν q a ∂μ.withDensity (sectionMass ν q)) =
      ∫⁻ p, f p.1 p.2 ∂(μ.prod ν).withDensity (Function.uncurry q) := by
  rw [lintegral_withDensity_eq_lintegral_mul μ (measurable_sectionMass ν hq)
    (measurable_lintegral_sectionLaw ν hq hf)]
  have hfp : Measurable (fun p : A × B => f p.1 p.2) := hf
  rw [lintegral_withDensity_eq_lintegral_mul (μ.prod ν) hq hfp]
  rw [lintegral_prod _ (hq.mul hfp).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hfin] with a ha
  exact sectionMass_mul_lintegral_sectionLaw ν hq a ha hf.of_uncurry_left

theorem sectionKernel_apply (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (a : A) :
    sectionKernel ν q a = sectionLaw ν q a := by
  rw [sectionKernel, ProbabilityTheory.Kernel.withDensity_apply _
    (measurable_sectionDensity ν hq)]
  rfl

/-- The conditional kernel is uniformly finite, including its zero/infinite section defaults. -/
theorem isFiniteKernel_sectionKernel (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    ProbabilityTheory.IsFiniteKernel (sectionKernel ν q) := by
  constructor
  refine ⟨1, by simp, fun a => ?_⟩
  rw [sectionKernel_apply ν hq, sectionLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  simp only [sectionDensity, div_eq_mul_inv]
  rw [lintegral_mul_const _ hq.of_uncurry_left]
  exact ENNReal.mul_inv_le_one _

/-- Measure-level disintegration, ready to compose with conditional quantile laws.
Zero-mass fibers require no arbitrary probability choice because their marginal weight vanishes. -/
theorem compProd_sectionKernel (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q))
    (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞) :
    (μ.withDensity (sectionMass ν q)).compProd (sectionKernel ν q) =
      (μ.prod ν).withDensity (Function.uncurry q) := by
  let := isFiniteKernel_sectionKernel ν hq
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf]
  simp_rw [sectionKernel_apply ν hq]
  have hf' : Measurable (Function.uncurry (fun a b => f (a, b))) :=
    hf.comp (measurable_fst.prodMk measurable_snd)
  exact lintegral_reassemble_sections μ ν hq hf' hfin

/-- The marginal density of a uniform region is exactly its section volume. -/
theorem sectionMass_setDensity (ν : Measure B) {U : Set (A × B)}
    (hU : MeasurableSet U) (a : A) :
    sectionMass ν (setDensity U) a = ν (Prod.mk a ⁻¹' U) := by
  have he : (setDensity U a) = (Prod.mk a ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext b
    rfl
  rw [sectionMass, he]
  exact lintegral_indicator_one (hU.preimage measurable_prodMk_left)

/-- The conditional law of a region is the normalized restricted volume of its fiber. -/
theorem sectionLaw_setDensity (ν : Measure B) {U : Set (A × B)}
    (hU : MeasurableSet U) (a : A) :
    sectionLaw ν (setDensity U) a =
      (ν (Prod.mk a ⁻¹' U))⁻¹ • ν.restrict (Prod.mk a ⁻¹' U) := by
  classical
  have he : sectionDensity ν (setDensity U) a =
      (Prod.mk a ⁻¹' U).indicator (fun _ => (ν (Prod.mk a ⁻¹' U))⁻¹) := by
    funext b
    rw [sectionDensity, sectionMass_setDensity ν hU]
    by_cases hb : (a, b) ∈ U <;> simp [setDensity, Set.indicator, hb]
  rw [sectionLaw, he, withDensity_indicator (hU.preimage measurable_prodMk_left),
    withDensity_const]

/-- Disintegrating the restriction to a region gives its volume marginal and uniform fibers. -/
theorem compProd_setSections (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U)
    (hfin : ∀ᵐ a ∂μ, ν (Prod.mk a ⁻¹' U) ≠ ∞) :
    (μ.withDensity (sectionMass ν (setDensity U))).compProd
      (sectionKernel ν (setDensity U)) = (μ.prod ν).restrict U := by
  have hfin' : ∀ᵐ a ∂μ, sectionMass ν (setDensity U) a ≠ ∞ := by
    simpa only [sectionMass_setDensity ν hU] using hfin
  rw [compProd_sectionKernel μ ν (measurable_setDensity hU) hfin']
  have he : Function.uncurry (setDensity U) = U.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    rcases p with ⟨a, b⟩
    rfl
  rw [he, withDensity_indicator hU, withDensity_const, one_smul]

/-- Finite mass of the whole region discharges the only section-finiteness premise. -/
theorem compProd_setSections_of_finite (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U)
    (hfin : (μ.prod ν) U ≠ ∞) :
    (μ.withDensity (sectionMass ν (setDensity U))).compProd
      (sectionKernel ν (setDensity U)) = (μ.prod ν).restrict U := by
  apply compProd_setSections μ ν hU
  have hm := measurable_sectionMass ν (measurable_setDensity hU)
  have hi : (∫⁻ a, sectionMass ν (setDensity U) a ∂μ) ≠ ∞ := by
    simpa only [sectionMass_setDensity ν hU, ← Measure.prod_apply hU] using hfin
  filter_upwards [ae_lt_top hm hi] with a ha
  simpa only [sectionMass_setDensity ν hU] using ha.ne

theorem isMarkovKernel_completedSectionKernel (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (b₀ : B) :
    ProbabilityTheory.IsMarkovKernel (completedSectionKernel ν hq b₀) := by
  constructor
  intro a
  classical
  by_cases ha : a ∈ goodSections ν q
  · rw [completedSectionKernel, ProbabilityTheory.Kernel.piecewise_apply, ite_eq_left ha,
      sectionKernel_apply ν hq]
    exact isProbabilityMeasure_sectionLaw ν hq a ha.1 ha.2
  · rw [completedSectionKernel, ProbabilityTheory.Kernel.piecewise_apply, ite_eq_right ha]
    change IsProbabilityMeasure (Measure.dirac b₀)
    infer_instance

/-- Exceptional-fiber completion does not change the conditional law marginal-a.e. -/
theorem completedSectionKernel_ae_eq (μ : Measure A) (ν : Measure B) [SFinite ν]
    {q : A → B → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (b₀ : B)
    (hfin : ∀ᵐ a ∂μ, sectionMass ν q a ≠ ∞) :
    completedSectionKernel ν hq b₀ =ᵐ[μ.withDensity (sectionMass ν q)] sectionKernel ν q := by
  apply (ae_withDensity_iff (measurable_sectionMass ν hq)).mpr
  filter_upwards [hfin] with a ha h0
  rw [completedSectionKernel, ProbabilityTheory.Kernel.piecewise_apply, ite_eq_left]
  exact ⟨h0, ha⟩

/-- Exact probability-level disintegration of a uniform region. The total
Markov kernel still uses the unnormalized fiber density, so all normalization
of the whole region is confined to the prefix marginal. -/
theorem compProd_uniformSetSections (μ : Measure A) [SFinite μ]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U)
    (b₀ : B) (hfin : (μ.prod ν) U ≠ ∞) :
    (((μ.prod ν) U)⁻¹ • μ.withDensity (sectionMass ν (setDensity U))).compProd
      (completedSectionKernel ν (measurable_setDensity hU) b₀) =
      ((μ.prod ν) U)⁻¹ • (μ.prod ν).restrict U := by
  let := isMarkovKernel_completedSectionKernel ν (measurable_setDensity hU) b₀
  let := isFiniteKernel_sectionKernel ν (measurable_setDensity hU)
  have hm := measurable_sectionMass ν (measurable_setDensity hU)
  have hi : (∫⁻ a, sectionMass ν (setDensity U) a ∂μ) ≠ ∞ := by
    simpa only [sectionMass_setDensity ν hU, ← Measure.prod_apply hU] using hfin
  have hf : ∀ᵐ a ∂μ, sectionMass ν (setDensity U) a ≠ ∞ := by
    filter_upwards [ae_lt_top hm hi] with a ha
    exact ha.ne
  rw [Measure.compProd_smul_left,
    Measure.compProd_congr
      (completedSectionKernel_ae_eq μ ν (measurable_setDensity hU) b₀ hf),
    compProd_setSections_of_finite μ ν hU hfin]

end Problem358.NormalizedSections

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_PrefixSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem358.FinitePrefix

/-- Appending coordinate blocks preserves the product Lebesgue measure. -/
theorem measurePreserving_append (n m : ℕ) :
    MeasurePreserving (append n m) (volume.prod volume) volume := by
  have h₁ := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Fin m => ℝ)
  have h₂ := volume_measurePreserving_piCongrLeft (fun _ : Fin (n + m) => ℝ)
    (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))
  have he : (append n m : (Coordinates n × Coordinates m) → Coordinates (n+m)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm := by
    funext p i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
        Equiv.piCongrLeft_apply, Equiv.sumPiEquivProdPi]
  rw [he]
  exact h₂.comp h₁

/-- The bounded-prefix coordinate split has unit Jacobian. -/
theorem measurePreserving_join {n d : ℕ} (h : n ≤ d) :
    MeasurePreserving (join h) (volume.prod volume) volume := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin d => ℝ)
    (finCongr (Nat.add_sub_of_le h))).comp (measurePreserving_append n (d-n))

/-- Restriction to a body commutes with coordinate reassembly. -/
theorem measurePreserving_join_restrict {n d : ℕ} (h : n ≤ d)
    {K : Set (Coordinates d)} (hK : MeasurableSet K) :
    MeasurePreserving (join h)
      ((volume.prod volume).restrict (join h ⁻¹' K)) (volume.restrict K) :=
  (measurePreserving_join h).restrict_preimage hK

theorem continuous_headBlock {n d : ℕ} (h : n ≤ d) : Continuous (headBlock h) := by
  exact continuous_pi (fun i => continuous_apply (leftIndex h i))

private theorem measurePreserving_scalarBlock :
    MeasurePreserving scalarBlock volume volume := by
  exact MeasurePreserving.symm scalarBlock.symm.toHomeomorph.toMeasurableEquiv
    (volume_preserving_piUnique (fun _ : Fin 1 => ℝ))

theorem measurePreserving_tripleSplit {n d : ℕ} (h : n < d) :
    MeasurePreserving (tripleSplit h) volume volume := by
  have hs := (measurePreserving_append 1 (d - (n + 1))).comp
    (measurePreserving_scalarBlock.prod (MeasurePreserving.id volume))
  exact ((volume_measurePreserving_piCongrLeft (fun _ : Fin d => ℝ)
    (finCongr (by omega : n + (1 + (d - (n + 1))) = d))).comp
      (measurePreserving_append n (1 + (d - (n + 1))))).comp
        ((MeasurePreserving.id volume).prod hs)

end Problem358.FinitePrefix

end

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Problem358.FinitePrefix

lemma prefixDomain_iff {d n : ℕ} {K : Set (Coordinates d)} {h : n ≤ d}
    {a : Coordinates n} : a ∈ prefixDomain K h ↔
      ∃ b : Coordinates (d - n), join h (a,b) ∈ interior K := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨tailBlock h x, by simpa only [join_prefix_suffix] using hx⟩
  · rintro ⟨b,hb⟩
    exact ⟨join h (a,b),hb,prefix_join h a b⟩

lemma isCompact_prefixSection {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (h : n ≤ d) (a : Coordinates n) :
    IsCompact (prefixSection K h a) := by
  exact AffineSlice.isCompact_fiber
    ((join h).toHomeomorph.isCompact_preimage.mpr hK) a

lemma prefixSection_interior_nonempty {d n : ℕ} {K : Set (Coordinates d)}
    {h : n ≤ d} {a : Coordinates n} (ha : a ∈ prefixDomain K h) :
    (interior (prefixSection K h a)).Nonempty := by
  obtain ⟨b,hb⟩ := prefixDomain_iff.mp ha
  refine ⟨b, preimage_interior_subset_interior_preimage ?_ hb⟩
  exact (join h).continuous.comp (continuous_const.prodMk continuous_id)

lemma prefixSection_volume_pos {d n : ℕ} {K : Set (Coordinates d)}
    {h : n ≤ d} {a : Coordinates n} (ha : a ∈ prefixDomain K h) :
    0 < volume (prefixSection K h a) :=
  measure_pos_of_nonempty_interior volume (prefixSection_interior_nonempty ha)

lemma prefixSection_volumeReal_pos {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) {h : n ≤ d} {a : Coordinates n}
    (ha : a ∈ prefixDomain K h) :
    0 < (volume (prefixSection K h a)).toReal :=
  ENNReal.toReal_pos (prefixSection_volume_pos ha).ne'
    (isCompact_prefixSection hK h a).measure_ne_top

lemma prefixDomain_zero {d : ℕ} {K : Set (Coordinates d)}
    (hK : (interior K).Nonempty) (a : Coordinates 0) :
    a ∈ prefixDomain K (Nat.zero_le d) := by
  obtain ⟨x,hx⟩ := hK
  exact ⟨x,hx,Subsingleton.elim _ _⟩

lemma prefixSection_full {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∈ K) :
    prefixSection K (le_refl d) a = univ := by
  ext b
  simp [prefixSection,ha]

end Problem358.FinitePrefix

end

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- The density of an actual bounded coordinate prefix is the volume of its
remaining-coordinate section. No convexity or positive-volume assumption is needed. -/
theorem map_headBlock_restrict {n d : ℕ} (h : n ≤ d)
    {K : Set (Coordinates d)} (hK : MeasurableSet K) :
    Measure.map (headBlock h) (volume.restrict K) =
      volume.withDensity (fun a : Coordinates n =>
        volume {b : Coordinates (d-n) | join h (a,b) ∈ K}) := by
  rw [← (measurePreserving_join_restrict h hK).map_eq]
  rw [Measure.map_map (continuous_headBlock h).measurable (join h).continuous.measurable]
  have he : headBlock h ∘ join h = Prod.fst := by
    funext p
    exact prefix_join h p.1 p.2
  rw [he]
  exact SectionMarginal.map_fst_restrict volume volume _
    (hK.preimage (join h).continuous.measurable)

/-- Actual normalized prefix laws have the common normalization by full body
volume, not by the individual section mass. -/
theorem map_headBlock_normalized_restrict {n d : ℕ} (h : n ≤ d)
    {K : Set (Coordinates d)} (hK : MeasurableSet K) :
    Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K) =
      (volume K)⁻¹ • volume.withDensity (fun a : Coordinates n =>
        volume {b : Coordinates (d-n) | join h (a,b) ∈ K}) := by
  rw [Measure.map_smul,
    map_headBlock_restrict h hK]

end Problem358.FinitePrefix

end

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- Taking a bounded coordinate prefix is an open map, including the empty
and the full prefix. -/
theorem isOpenMap_headBlock {n d : ℕ} (h : n ≤ d) :
    IsOpenMap (headBlock h) := by
  have hh := isOpenMap_fst.comp (join h).symm.toHomeomorph.isOpenMap
  change IsOpenMap (fun x : Coordinates d => ((join h).symm x).1) at hh
  simpa only [join_symm_apply] using hh

/-- The valid prefixes of a body form an open set. -/
theorem isOpen_prefixDomain {n d : ℕ} (K : Set (Coordinates d)) (h : n ≤ d) :
    IsOpen (prefixDomain K h) :=
  isOpenMap_headBlock h _ isOpen_interior

/-- Any law carried by the body's interior has its prefix law carried by the
valid prefix domain. No choice of conditional law on bad prefixes is relevant. -/
theorem ae_mem_prefixDomain_map {n d : ℕ} {K : Set (Coordinates d)}
    (h : n ≤ d) {μ : Measure (Coordinates d)}
    (hμ : ∀ᵐ x ∂μ, x ∈ interior K) :
    ∀ᵐ a ∂Measure.map (headBlock h) μ, a ∈ prefixDomain K h := by
  apply (ae_map_iff (continuous_headBlock h).measurable.aemeasurable
    (isOpen_prefixDomain K h).measurableSet).2
  filter_upwards [hμ] with x hx
  exact ⟨x, hx, rfl⟩

/-- Convex boundaries are null, so normalization of restricted volume does
not place any mass on the boundary. Degenerate volume is allowed. -/
theorem ae_mem_interior_normalized_restrict {d : ℕ} {K : Set (Coordinates d)}
    (hK : Convex ℝ K) :
    ∀ᵐ x ∂((volume K)⁻¹ • volume.restrict K), x ∈ interior K := by
  apply Measure.ae_smul_measure
  have heq : volume.restrict K = volume.restrict (interior K) :=
    Measure.restrict_congr_set
      (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume)).symm
  rw [heq]
  exact ae_restrict_mem measurableSet_interior

/-- The actual normalized prefix marginal is almost surely a valid interior
prefix. This is the support input for geometric conditional quantiles. -/
theorem ae_mem_prefixDomain_map_normalized_restrict {n d : ℕ}
    {K : Set (Coordinates d)} (hK : Convex ℝ K) (h : n ≤ d) :
    ∀ᵐ a ∂Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K),
      a ∈ prefixDomain K h :=
  ae_mem_prefixDomain_map h (ae_mem_interior_normalized_restrict hK)

/-- A sampler with the actual prefix marginal almost surely reaches the valid
prefix domain, independently of its values on parameter-null sets. -/
theorem ae_sample_mem_prefixDomain {A : Type*} [MeasurableSpace A]
    {n d : ℕ} {K : Set (Coordinates d)} (hK : Convex ℝ K) (h : n ≤ d)
    {η : Measure A} {F : A → Coordinates n} (hF : AEMeasurable F η)
    (hlaw : Measure.map F η =
      Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K)) :
    ∀ᵐ a ∂η, F a ∈ prefixDomain K h := by
  apply ae_of_ae_map hF
  rw [hlaw]
  exact ae_mem_prefixDomain_map_normalized_restrict hK h

end Problem358.FinitePrefix

namespace Problem358.FinitePrefix

/-- A zero-dimensional terminal section has volume one on the body. -/
theorem volume_prefixSection_full {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∈ K) :
    volume (prefixSection K (le_refl d) a) = 1 := by
  rw [prefixSection_full ha]
  simp [volume_pi, Measure.pi_univ]

/-- In particular the terminal density is one at every valid full prefix. -/
theorem volume_prefixSection_full_of_mem_domain {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∈ prefixDomain K (le_refl d)) :
    volume (prefixSection K (le_refl d) a) = 1 := by
  apply volume_prefixSection_full
  exact interior_subset (by simpa only [prefixDomain_full] using ha)

/-- The terminal real density used by the telescoping derivative product. -/
theorem volumeReal_prefixSection_full {d : ℕ} {K : Set (Coordinates d)}
    {a : Coordinates d} (ha : a ∈ prefixDomain K (le_refl d)) :
    (volume (prefixSection K (le_refl d) a)).toReal = 1 := by
  rw [volume_prefixSection_full_of_mem_domain ha, ENNReal.toReal_one]

/-- The normalized zero-prefix law is the unit-volume law on the empty product. -/
theorem normalized_initial_prefix_law {d : ℕ} {K : Set (Coordinates d)}
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    (volume K)⁻¹ • volume.withDensity
      (fun a : Coordinates 0 => volume (prefixSection K (Nat.zero_le d) a)) =
        (volume : Measure (Coordinates 0)) := by
  simp only [volume_prefixSection_zero, withDensity_const, smul_smul]
  rw [ENNReal.inv_mul_cancel hK0 hKtop, one_smul]

end Problem358.FinitePrefix

end

noncomputable section
open MeasureTheory

namespace Problem358.FinitePrefix

/-- A three-block split is the next prefix split after installing its scalar coordinate. -/
theorem tripleSplit_eq_join_snoc {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n + 1))) :
    tripleSplit h (x, t, z) = join (Nat.succ_le_of_lt h) (Fin.snoc x t, z) := by
  simpa only [headBlock_tripleSplit, tailBlock_tripleSplit] using
    (join_prefix_suffix (Nat.succ_le_of_lt h) (tripleSplit h (x, t, z))).symm

/-- Regrouping a scalar and a tail has unit Jacobian. -/
theorem measurePreserving_tailJoin {n d : ℕ} (h : n < d) :
    MeasurePreserving (tailJoin h) (volume.prod volume) volume := by
  have hs : MeasurePreserving
      (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm volume volume :=
    MeasurePreserving.symm
      (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph.toMeasurableEquiv
      (volume_preserving_piUnique (fun _ : Fin 1 => ℝ))
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (d - n) => ℝ)
    (finCongr (by omega : 1 + (d - (n + 1)) = d - n))).comp
      ((measurePreserving_append 1 (d - (n + 1))).comp
        (hs.prod (MeasurePreserving.id volume)))

/-- The same three-block split regrouped at the old prefix. -/
theorem tripleSplit_eq_join_tailJoin {n d : ℕ} (h : n < d)
    (x : Coordinates n) (t : ℝ) (z : Coordinates (d - (n + 1))) :
    tripleSplit h (x, t, z) = join h.le (x, tailJoin h (t, z)) := by
  ext i
  obtain ⟨i, rfl⟩ := (finCongr (Nat.add_sub_of_le h.le)).surjective i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change tripleSplit h (x,t,z) (leftIndex h.le j) =
      join h.le (x,tailJoin h (t,z)) (leftIndex h.le j)
    simp
  · change tripleSplit h (x,t,z) (rightIndex h.le j) =
      join h.le (x,tailJoin h (t,z)) (rightIndex h.le j)
    rw [join_right]
    obtain ⟨j, rfl⟩ := (finCongr (by omega : 1 + (d - (n+1)) = d-n)).surjective j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
      subst k
      have hi : rightIndex h.le
          (finCongr (by omega : 1 + (d - (n+1)) = d-n)
            (Fin.castAdd (d-(n+1)) (0 : Fin 1))) = ⟨n,h⟩ := by
        ext
        simp [rightIndex]
      rw [hi, tripleSplit_next]
      change t = Fin.append (fun _ : Fin 1 => t) z
        (Fin.cast (by omega : d-n = 1+(d-(n+1)))
          (Fin.cast (by omega : 1+(d-(n+1)) = d-n)
            (Fin.castAdd (d-(n+1)) (0 : Fin 1))))
      simp
    · have hi : rightIndex h.le
          (finCongr (by omega : 1 + (d - (n+1)) = d-n) (Fin.natAdd 1 k)) =
          rightIndex (Nat.succ_le_of_lt h) k := by
        ext
        simp only [rightIndex, finCongr, Equiv.coe_fn_mk, Fin.val_cast, Fin.val_natAdd]
        omega
      rw [hi, tripleSplit_right]
      change z k = Fin.append (fun _ : Fin 1 => t) z
        (Fin.cast (by omega : d-n = 1+(d-(n+1)))
          (Fin.cast (by omega : 1+(d-(n+1)) = d-n) (Fin.natAdd 1 k)))
      simp

/-- Fixing the old prefix gives exactly the old tail section, in regrouped coordinates. -/
theorem tripleSplit_parentSection {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) :
    AffineSlice.fiber (tripleSplit h ⁻¹' K) a =
      tailJoin h ⁻¹' prefixSection K h.le a := by
  ext p
  change tripleSplit h (a,p.1,p.2) ∈ K ↔ join h.le (a,tailJoin h p) ∈ K
  rw [tripleSplit_eq_join_tailJoin]

/-- Parent section volume is unchanged by splitting off its next scalar coordinate. -/
theorem tripleSplit_parentSection_volume {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) :
    (volume.prod volume) (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) =
      volume (prefixSection K h.le a) := by
  rw [tripleSplit_parentSection]
  exact (measurePreserving_tailJoin h).measure_preimage_emb
    (tailJoin h).toHomeomorph.measurableEmbedding _

/-- Real-valued parent section volume, matching the conditional density denominator. -/
theorem tripleSplit_parentSection_volumeReal {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) :
    (volume.prod volume).real (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) =
      volume.real (prefixSection K h.le a) := by
  simp only [Measure.real, tripleSplit_parentSection_volume]

/-- The scalar child section is precisely the section at the extended prefix. -/
theorem tripleSplit_childSection {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) (t : ℝ) :
    AffineSlice.fiber (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) t =
      prefixSection K (Nat.succ_le_of_lt h) (Fin.snoc a t) := by
  ext z
  change tripleSplit h (a,t,z) ∈ K ↔ join (Nat.succ_le_of_lt h) (Fin.snoc a t,z) ∈ K
  rw [tripleSplit_eq_join_snoc]

/-- The real-valued child section identity used by inverse-CDF derivatives. -/
theorem tripleSplit_childSection_volumeReal {n d : ℕ} (h : n < d)
    (K : Set (Coordinates d)) (a : Coordinates n) (t : ℝ) :
    volume.real (AffineSlice.fiber (AffineSlice.fiber (tripleSplit h ⁻¹' K) a) t) =
      volume.real (prefixSection K (Nat.succ_le_of_lt h) (Fin.snoc a t)) := by
  rw [tripleSplit_childSection]

end Problem358.FinitePrefix

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_Midpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-! One-dimensional substitution estimates for midpoint-coupling constructions.
These lemmas do not assume or assert existence of a triangular quantile map. -/

namespace Problem358

/-- Injective one-dimensional substitution followed by enlargement of the image.
No measurability assumption on the nonnegative integrand is needed. -/
theorem lintegral_jacobian_comp_le {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hderiv : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hinj : InjOn f s) (g : ℝ → ℝ≥0∞) :
    (∫⁻ x in s, ENNReal.ofReal (|f' x|) * g (f x)) ≤ ∫⁻ y, g y := by
  rw [← lintegral_image_eq_lintegral_abs_deriv_mul hs hderiv hinj]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

/-- The derivative of the midpoint exceeds the geometric mean of the two
nonnegative derivatives. -/
theorem midpoint_derivative_ge_geometric_mean {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (u - v)]

/-- Midpoint substitution with geometric-mean Jacobian weight. This is the
one-dimensional step in the triangular domination argument. -/
theorem lintegral_midpoint_geometric_jacobian_le
    {s : Set ℝ} {f f' g g' : ℝ → ℝ}
    (hs : MeasurableSet s) (hconv : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hg : ∀ x ∈ s, HasDerivWithinAt g (g' x) s x)
    (hfpos : ∀ x ∈ s, 0 < f' x) (hgpos : ∀ x ∈ s, 0 < g' x)
    (w : ℝ → ℝ≥0∞) :
    (∫⁻ x in s, ENNReal.ofReal (Real.sqrt (f' x * g' x)) *
      w ((f x + g x) / 2)) ≤ ∫⁻ y, w y := by
  have hmid (x : ℝ) (hx : x ∈ s) :
      HasDerivWithinAt (fun t => (f t + g t) / 2)
        ((f' x + g' x) / 2) s x :=
    ((hf x hx).add (hg x hx)).div_const 2
  have hmidpos (x : ℝ) (hx : x ∈ s) : 0 < (f' x + g' x) / 2 := by
    have h1 := hfpos x hx
    have h2 := hgpos x hx
    positivity
  have hmono : StrictMonoOn (fun t => (f t + g t) / 2) s := by
    apply strictMonoOn_of_hasDerivWithinAt_pos hconv
      (fun x hx => (hmid x hx).continuousWithinAt)
      (fun x hx => (hmid x (interior_subset hx)).mono interior_subset)
    intro x hx
    exact hmidpos x (interior_subset hx)
  calc
    (∫⁻ x in s, ENNReal.ofReal (Real.sqrt (f' x * g' x)) * w ((f x + g x) / 2)) ≤
        ∫⁻ x in s, ENNReal.ofReal (|(f' x + g' x) / 2|) * w ((f x + g x) / 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_pos (hmidpos x hx)]
      exact midpoint_derivative_ge_geometric_mean (hfpos x hx).le (hgpos x hx).le
    _ ≤ ∫⁻ y, w y := lintegral_jacobian_comp_le hs hmid hmono.injOn w

end Problem358

end

/-!
# Integral identities for the midpoint cell estimate

The integral estimates assume domination by a midpoint coupling.
-/

/-!+# Transfer of midpoint couplings from coordinates to Euclidean space

The construction of a coordinate coupling remains an explicit hypothesis.
The volume-preserving change of representation includes
normalization and the midpoint domination inequality.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358.MidpointCoordinates

lemma volume_preimage_toLp {d : ℕ} {K : Set (E d)} (hK : MeasurableSet K) :
    volume ((WithLp.toLp 2) ⁻¹' K) = volume K :=
  (PiLp.volume_preserving_toLp (Fin d)).measure_preimage hK.nullMeasurableSet

/-- The ordinary coordinate-space normalization maps to the exact source used
in the challenge, with no additional volume constants. -/
lemma map_coordinateUniform {d : ℕ} {K : Set (E d)} (hK : MeasurableSet K) :
    Measure.map (WithLp.toLp 2) (coordinateUniform K) = uniformMeasure K := by
  unfold coordinateUniform uniformMeasure
  rw [volume_preimage_toLp hK,
    Measure.map_smul,
    ← Measure.restrict_map (PiLp.volume_preserving_toLp (Fin d)).measurable hK,
    (PiLp.volume_preserving_toLp (Fin d)).map_eq]

lemma measurable_liftPair (d : ℕ) : Measurable (@liftPair d) :=
  ((PiLp.volume_preserving_toLp (Fin d)).measurable.comp measurable_fst).prodMk
    ((PiLp.volume_preserving_toLp (Fin d)).measurable.comp measurable_snd)

lemma liftPair_midpoint {d : ℕ} (p : Coordinates d × Coordinates d) :
    (1 / 2 : ℝ) • ((liftPair p).1 + (liftPair p).2) =
      WithLp.toLp 2 ((1 / 2 : ℝ) • (p.1 + p.2)) := by
  simp only [liftPair, WithLp.toLp_smul, WithLp.toLp_add]

/-- Pushing both coordinates through `toLp` preserves both exact marginals. -/
lemma lift_coupling {d : ℕ} {K L : Set (E d)}
    (hK : MeasurableSet K) (hL : MeasurableSet L)
    {π : Measure (Coordinates d × Coordinates d)}
    (hπ : IsProbabilityMeasure π)
    (hfst : Measure.map Prod.fst π = coordinateUniform K)
    (hsnd : Measure.map Prod.snd π = coordinateUniform L) :
    IsCoupling (uniformMeasure K) (uniformMeasure L) (Measure.map liftPair π) := by
  let := hπ
  refine ⟨Measure.isProbabilityMeasure_map (measurable_liftPair d).aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (measurable_liftPair d)]
    change Measure.map ((WithLp.toLp 2) ∘ Prod.fst) π = uniformMeasure K
    rw [← Measure.map_map (PiLp.volume_preserving_toLp (Fin d)).measurable
      measurable_fst, hfst, map_coordinateUniform hK]
  · rw [Measure.map_map measurable_snd (measurable_liftPair d)]
    change Measure.map ((WithLp.toLp 2) ∘ Prod.snd) π = uniformMeasure L
    rw [← Measure.map_map (PiLp.volume_preserving_toLp (Fin d)).measurable
      measurable_snd, hsnd, map_coordinateUniform hL]

/-- A weighted midpoint domination inequality survives the coordinate change. -/
lemma lift_midpoint_domination {d : ℕ}
    {π : Measure (Coordinates d × Coordinates d)} {c : ℝ≥0∞}
    (hdom : c • Measure.map
      (fun p : Coordinates d × Coordinates d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤
        volume) :
    c • Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2))
      (Measure.map liftPair π) ≤ volume := by
  have h := Measure.map_mono hdom (PiLp.volume_preserving_toLp (Fin d)).measurable
  rw [Measure.map_smul,
    Measure.map_map
    (PiLp.volume_preserving_toLp (Fin d)).measurable (by fun_prop),
    (PiLp.volume_preserving_toLp (Fin d)).map_eq] at h
  rw [Measure.map_map (by fun_prop) (measurable_liftPair d)]
  have hfun : (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) ∘ liftPair =
      (WithLp.toLp 2) ∘
        (fun p : Coordinates d × Coordinates d => (1 / 2 : ℝ) • (p.1 + p.2)) := by
    funext p
    exact liftPair_midpoint p
  rw [hfun]
  exact h

/-- Coordinate-space dominated midpoint witnesses give the corresponding
Euclidean-space witnesses. No existence assumption is hidden in the change
of representation. -/
theorem exists_lifted_midpoint_coupling {d : ℕ} {K L : Set (E d)}
    (hK : MeasurableSet K) (hL : MeasurableSet L) (c : ℝ≥0∞)
    (h : ∃ π : Measure (Coordinates d × Coordinates d), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = coordinateUniform K ∧
      Measure.map Prod.snd π = coordinateUniform L ∧
      c • Measure.map
        (fun p : Coordinates d × Coordinates d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤
        volume) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      c • Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
  obtain ⟨π, hπ, hfst, hsnd, hdom⟩ := h
  exact ⟨Measure.map liftPair π, lift_coupling hK hL hπ hfst hsnd,
    lift_midpoint_domination hdom⟩

/-- Passing to the interior of a convex body does not change its volume. -/
lemma volume_interior {d : ℕ} {K : Set (E d)} (hK : Convex ℝ K) :
    volume (interior K) = volume K :=
  measure_congr (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume))

/-- The common-source sampler formulation constructs the joint coupling rather
than requiring it as a separate input. -/
theorem exists_midpoint_coupling_of_coordinate_samplers
    {Ω : Type*} [MeasurableSpace Ω] {ρ : Measure Ω} [IsProbabilityMeasure ρ]
    {d : ℕ} {K L : Set (E d)} (hK : MeasurableSet K) (hL : MeasurableSet L)
    (X Y : Ω → Coordinates d) (hX : Measurable X) (hY : Measurable Y)
    (hXlaw : Measure.map X ρ = coordinateUniform K)
    (hYlaw : Measure.map Y ρ = coordinateUniform L) (c : ℝ≥0∞)
    (hdom : c • Measure.map (fun ω => (1 / 2 : ℝ) • (X ω + Y ω)) ρ ≤ volume) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      c • Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
  apply exists_lifted_midpoint_coupling hK hL c
  refine ⟨Measure.map (fun ω => (X ω, Y ω)) ρ,
    Measure.isProbabilityMeasure_map (hX.prodMk hY).aemeasurable, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    exact hXlaw
  · rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    exact hYlaw
  · rw [Measure.map_map (by fun_prop) (hX.prodMk hY)]
    exact hdom

end Problem358.MidpointCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_TriangularDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.TriangularDomination

/-- One genuine induction step for triangular changes of variables. The last output
coordinate may depend on every preceding input coordinate, but the preceding output
coordinates do not depend on the last input coordinate. No joint differentiability is
needed: measurable weights and the two lower-dimensional integral bounds suffice. -/
theorem WeightedDomination.triangular_ae
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure A} {ν : Measure B} {ρ : Measure C} {σ : Measure D}
    [SFinite ρ] [SFinite σ]
    {F : A → B} {G : A → C → D}
    {J : A → ℝ≥0∞} {j : A → C → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable (fun p : A × C => G p.1 p.2))
    (hJ : Measurable J) (hj : Measurable (fun p : A × C => j p.1 p.2))
    (hbase : WeightedDomination μ ν F J)
    (hfiber : ∀ᵐ a ∂μ, WeightedDomination ρ σ (G a) (j a)) :
    WeightedDomination (μ.prod ρ) (ν.prod σ)
      (fun p : A × C => (F p.1, G p.1 p.2))
      (fun p : A × C => J p.1 * j p.1 p.2) := by
  intro w hw
  have hmap : Measurable (fun p : A × C => (F p.1, G p.1 p.2)) :=
    (hF.comp measurable_fst).prodMk hG
  have hweight : Measurable (fun p : A × C => J p.1 * j p.1 p.2) :=
    (hJ.comp measurable_fst).mul hj
  have htotal : Measurable (fun p : A × C =>
      (J p.1 * j p.1 p.2) * w (F p.1, G p.1 p.2)) :=
    hweight.mul (hw.comp hmap)
  change (∫⁻ p : A × C, (J p.1 * j p.1 p.2) * w (F p.1, G p.1 p.2) ∂μ.prod ρ) ≤ _
  rw [lintegral_prod _ htotal.aemeasurable,
    lintegral_prod _ hw.aemeasurable]
  calc
    _ = ∫⁻ a, J a * (∫⁻ c, j a c * w (F a, G a c) ∂ρ) ∂μ := by
      apply lintegral_congr
      intro a
      have hj' : Measurable (j a) := hj.comp (measurable_const.prodMk measurable_id)
      have hG' : Measurable (G a) := hG.comp (measurable_const.prodMk measurable_id)
      simp only [mul_assoc]
      exact lintegral_const_mul _ (hj'.mul (hw.comp (measurable_const.prodMk hG')))
    _ ≤ ∫⁻ a, J a * (∫⁻ d, w (F a, d) ∂σ) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hfiber] with a ha
      exact mul_le_mul_right (ha _
        (hw.comp (measurable_const.prodMk measurable_id))) (J a)
    _ ≤ ∫⁻ b, ∫⁻ d, w (b, d) ∂σ ∂ν :=
      hbase _ hw.lintegral_prod_right'

/-- A pointwise smaller weight preserves the integral domination. -/
theorem WeightedDomination.mono_weight
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {F : A → B} {J K : A → ℝ≥0∞}
    (h : WeightedDomination μ ν F J) (hK : K ≤ᵐ[μ] J) :
    WeightedDomination μ ν F K := by
  intro w hw
  apply le_trans _ (h w hw)
  apply lintegral_mono_ae
  filter_upwards [hK] with a ha
  exact mul_le_mul_left ha (w (F a))

/-- Integral domination gives the expected domination of weighted image measures. -/
theorem WeightedDomination.map_withDensity_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {F : A → B} {J : A → ℝ≥0∞}
    (h : WeightedDomination μ ν F J) (hF : Measurable F) :
    Measure.map F (μ.withDensity J) ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  have htest := h (s.indicator (fun _ => 1)) (measurable_const.indicator hs)
  have heq : (fun a => J a * s.indicator (fun _ => (1 : ℝ≥0∞)) (F a)) =
      (F ⁻¹' s).indicator J := by
    funext a
    by_cases ha : F a ∈ s <;> simp [ha]
  rw [heq, lintegral_indicator (hs.preimage hF), lintegral_indicator hs] at htest
  rw [Measure.map_apply hF hs, withDensity_apply _ (hs.preimage hF)]
  simpa using htest

/-- A uniform lower Jacobian bound gives the unweighted pushforward bound. -/
theorem WeightedDomination.smul_map_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {F : A → B} {J : A → ℝ≥0∞}
    (h : WeightedDomination μ ν F J) (hF : Measurable F)
    {c : ℝ≥0∞} (hc : ∀ᵐ a ∂μ, c ≤ J a) :
    c • Measure.map F μ ≤ ν := by
  have h' := (h.mono_weight hc).map_withDensity_le hF
  simpa [withDensity_const, Measure.map_smul] using h'

end Problem358.TriangularDomination

end

/-! The measurable geometric Jacobian weight for two finite triangular samplers.
The weight is defined globally, but its identification with the geometric mean
of diagonal products only uses positivity on valid sampling parameters. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open Problem358.TriangularRecursion

namespace Problem358.TriangularDensity

/-- Measurability requires no sign conditions or information above the cutoff. -/
theorem measurable_geometricWeight_of_le (q r dq dr : ConditionalFamily) (N : ℕ)
    (hQ : ∀ n, n ≤ N → Measurable (sample q n))
    (hR : ∀ n, n ≤ N → Measurable (sample r n))
    (hD : ∀ n, n < N → Measurable (fun p : Coordinates n × ℝ => dq n p.1 p.2))
    (hE : ∀ n, n < N → Measurable (fun p : Coordinates n × ℝ => dr n p.1 p.2)) :
    ∀ n, n ≤ N → Measurable (geometricWeight q r dq dr n) := by
  intro n
  induction n with
  | zero => intro _; exact measurable_const
  | succ n ih =>
      intro hn
      have hnle : n ≤ N := by omega
      have hnlt : n < N := by omega
      have hi : Measurable (fun u : Coordinates (n + 1) => Fin.init u) := by
        apply Measurable.of_eval
        intro i
        exact measurable_pi_apply i.castSucc
      have hd := (hD n hnlt).comp
        (((hQ n hnle).comp hi).prodMk (measurable_pi_apply (Fin.last n)))
      have he := (hE n hnlt).comp
        (((hR n hnle).comp hi).prodMk (measurable_pi_apply (Fin.last n)))
      exact ((ih hnle).comp hi).mul ((hd.mul he).sqrt.ennreal_ofReal)

/-- On the open parameter cube, the geometric weight is exactly the geometric
mean of both diagonal derivative products. This is deliberately not claimed
outside the cube, where the supplied derivative fields need not be positive. -/
theorem geometricWeight_eq_ofReal_sqrt_diagonalProduct
    (q r dq dr : ConditionalFamily) (N : ℕ)
    (hD : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n u) t)
    (hE : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dr n (sample r n u) t) :
    ∀ n, n ≤ N → ∀ u, InUnitCube u →
      geometricWeight q r dq dr n u = ENNReal.ofReal (Real.sqrt
        (diagonalProduct q dq n u * diagonalProduct r dr n u)) := by
  intro n
  induction n with
  | zero =>
      intro hn u hu
      simp only [geometricWeight, diagonalProduct, mul_one, Real.sqrt_one, ENNReal.ofReal_one]
  | succ n ih =>
      intro hn u hu
      have hnle : n ≤ N := by omega
      have hp : 0 ≤ diagonalProduct q dq n (Fin.init u) *
          diagonalProduct r dr n (Fin.init u) :=
        (mul_pos (diagonalProduct_pos_of_le q dq N hD n hnle _ hu.init)
          (diagonalProduct_pos_of_le r dr N hE n hnle _ hu.init)).le
      rw [geometricWeight, ih hnle _ hu.init]
      rw [diagonalProduct, diagonalProduct]
      have hreorder :
          (diagonalProduct q dq n (Fin.init u) *
            dq n (sample q n (Fin.init u)) (u (Fin.last n))) *
          (diagonalProduct r dr n (Fin.init u) *
            dr n (sample r n (Fin.init u)) (u (Fin.last n))) =
          (diagonalProduct q dq n (Fin.init u) *
            diagonalProduct r dr n (Fin.init u)) *
          (dq n (sample q n (Fin.init u)) (u (Fin.last n)) *
            dr n (sample r n (Fin.init u)) (u (Fin.last n))) := by ring
      rw [hreorder, Real.sqrt_mul hp, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-- Constant terminal products turn the Jacobian into a constant almost
certainly, exactly the normalization needed by midpoint measure domination. -/
theorem geometricWeight_ae_eq_constant
    (q r dq dr : ConditionalFamily) (N : ℕ) (A B : ℝ)
    (hD : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n u) t)
    (hE : ∀ n, n < N → ∀ u, InUnitCube u → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dr n (sample r n u) t)
    (hA : ∀ u, InUnitCube u → diagonalProduct q dq N u = A)
    (hB : ∀ u, InUnitCube u → diagonalProduct r dr N u = B) :
    ∀ᵐ u ∂(Measure.pi fun _ : Fin N =>
      (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      geometricWeight q r dq dr N u = ENNReal.ofReal (Real.sqrt (A * B)) := by
  filter_upwards [ae_inUnitCube N] with u hu
  rw [geometricWeight_eq_ofReal_sqrt_diagonalProduct q r dq dr N hD hE N
    (le_refl N) u hu, hA u hu, hB u hu]

end Problem358.TriangularDensity

end

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem358.TriangularDomination

/-- Finite-cutoff version: no maps, derivatives, or substitution bounds beyond
the requested ambient dimension need to satisfy any hypotheses. -/
theorem weightedDomination_triangular_recursion_of_le
    (N : ℕ)
    (η : Measure ℝ) [SigmaFinite η]
    (F : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ))
    (G : (n : ℕ) → ((Fin n → ℝ) × ℝ) → ℝ)
    (J : (n : ℕ) → (Fin n → ℝ) → ℝ≥0∞)
    (j : (n : ℕ) → ((Fin n → ℝ) × ℝ) → ℝ≥0∞)
    (hF : ∀ n, n ≤ N → Measurable (F n))
    (hG : ∀ n, n < N → Measurable (G n))
    (hJ : ∀ n, n ≤ N → Measurable (J n))
    (hj : ∀ n, n < N → Measurable (j n))
    (hzero : ∀ s, J 0 s = 1)
    (hrecursion : ∀ n, n < N → ∀ s t,
      F (n + 1) (Fin.snoc s t) = Fin.snoc (F n s) (G n (s, t)))
    (hweight : ∀ n, n < N → ∀ s t,
      J (n + 1) (Fin.snoc s t) = J n s * j n (s, t))
    (hfiber : ∀ n, n < N → ∀ᵐ s ∂(Measure.pi fun _ : Fin n => η),
      WeightedDomination η volume (fun t => G n (s, t)) (fun t => j n (s, t))) :
    ∀ n, n ≤ N → WeightedDomination (Measure.pi fun _ : Fin n => η)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) (F n) (J n) := by
  intro n
  induction n with
  | zero =>
    intro _ w hw
    have hmap : F 0 = id := by
      funext s
      exact Subsingleton.elim _ _
    have hmeasure : (Measure.pi fun _ : Fin 0 => η) =
        (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) := by
      congr 1
      funext i
      exact Fin.elim0 i
    simp only [hzero, one_mul, hmap, id_eq, hmeasure, le_refl]
  | succ n ih =>
    intro hn w hw
    have hnlt : n < N := by omega
    have hnle : n ≤ N := by omega
    have ih := ih hnle
    have hsource := measurePreserving_finSnoc n η
    have htarget := measurePreserving_finSnoc n (volume : Measure ℝ)
    have hdom := ih.triangular_ae
      (G := fun s t => G n (s, t)) (j := fun s t => j n (s, t))
      (hF n hnle) (hG n hnlt) (hJ n hnle) (hj n hnlt) (hfiber n hnlt)
    have hw' : Measurable (fun p : (Fin n → ℝ) × ℝ => w (Fin.snoc p.1 p.2)) :=
      hw.comp htarget.measurable
    have hbound := hdom _ hw'
    have hsourceIntegral := hsource.lintegral_comp
      ((hJ (n + 1) hn).mul (hw.comp (hF (n + 1) hn)))
    have htargetIntegral := htarget.lintegral_comp hw
    change (∫⁻ p : (Fin n → ℝ) × ℝ,
      J (n + 1) (Fin.snoc p.1 p.2) * w (F (n + 1) (Fin.snoc p.1 p.2))
        ∂(Measure.pi fun _ : Fin n => η).prod η) = _ at hsourceIntegral
    simp_rw [hweight n hnlt, hrecursion n hnlt] at hsourceIntegral
    exact hsourceIntegral.symm.trans_le (hbound.trans_eq htargetIntegral)

end Problem358.TriangularDomination

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358.TriangularRecursion

open TriangularDensity TriangularDomination

/-- Measurability of the midpoint needs only the two samplers at the depth in
question, not any conditional functions after that depth. -/
theorem measurable_midpoint_of_samples (q r : ConditionalFamily) (n : ℕ)
    (hq : Measurable (sample q n)) (hr : Measurable (sample r n)) :
    Measurable (midpoint q r n) := by
  apply Measurable.of_eval
  intro i
  exact (((measurable_pi_apply i).comp hq).add
    ((measurable_pi_apply i).comp hr)).div_const 2

/-- Specialization of finite triangular substitution to the canonical paired
samplers. Regularity is needed only on sampled open-unit-cube prefixes. The
recursive weight is the product of geometric means of longitudinal derivatives. -/
theorem weightedDomination_midpoint_of_weight
    (q r dq dr : ConditionalFamily) (N : ℕ)
    (hq : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => q n p.1 p.2))
    (hr : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => r n p.1 p.2))
    (hdq : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => dq n p.1 p.2))
    (hdr : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => dr n p.1 p.2))
    (hsq : ∀ n, n ≤ N → Measurable (sample q n))
    (hsr : ∀ n, n ≤ N → Measurable (sample r n))
    (hderivq : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (q n (sample q n s)) (dq n (sample q n s) t) t)
    (hderivr : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (r n (sample r n s)) (dr n (sample r n s) t) t)
    (hposq : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n s) t)
    (hposr : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dr n (sample r n s) t)
    (J : (n : ℕ) → (Fin n → ℝ) → ℝ≥0∞)
    (hJ : ∀ n, n ≤ N → Measurable (J n))
    (hzero : ∀ s, J 0 s = 1)
    (hweight : ∀ n, n < N → ∀ s t,
      J (n + 1) (Fin.snoc s t) = J n s * ENNReal.ofReal
        (Real.sqrt (dq n (sample q n s) t * dr n (sample r n s) t))) :
    WeightedDomination
      (Measure.pi fun _ : Fin N => volume.restrict (Ioo (0 : ℝ) 1))
      (Measure.pi fun _ : Fin N => (volume : Measure ℝ)) (midpoint q r N) (J N) := by
  apply weightedDomination_triangular_recursion_of_le N
    (volume.restrict (Ioo (0 : ℝ) 1)) (midpoint q r)
    (fun n p => midpointFiber q r n p.1 p.2) J
    (fun n p => ENNReal.ofReal (Real.sqrt
      (dq n (sample q n p.1) p.2 * dr n (sample r n p.1) p.2)))
    (fun n hn => measurable_midpoint_of_samples q r n (hsq n hn) (hsr n hn))
    ?_ hJ ?_ hzero (fun n _ s t => midpoint_snoc q r n s t) hweight ?_ N le_rfl
  · intro n hn
    exact (((hq n hn).comp (((hsq n hn.le).comp measurable_fst).prodMk
      measurable_snd)).add
      ((hr n hn).comp (((hsr n hn.le).comp measurable_fst).prodMk
      measurable_snd))).div_const 2
  · intro n hn
    exact ((((hdq n hn).comp (((hsq n hn.le).comp measurable_fst).prodMk
      measurable_snd)).mul
      ((hdr n hn).comp (((hsr n hn.le).comp measurable_fst).prodMk
      measurable_snd))).sqrt).ennreal_ofReal
  · intro n hn
    filter_upwards [TriangularDensity.ae_inUnitCube n] with s hs
    intro w _
    exact lintegral_midpoint_geometric_jacobian_le measurableSet_Ioo (convex_Ioo 0 1)
      (fun t ht => (hderivq n hn s hs t ht).hasDerivWithinAt)
      (fun t ht => (hderivr n hn s hs t ht).hasDerivWithinAt)
      (hposq n hn s hs) (hposr n hn s hs) w

/-- Canonical finite-dimensional midpoint domination. The only quantitative
input is the two constant terminal diagonal products; all weighted substitution
and measurable-Jacobian conditions are discharged from the scalar data. -/
theorem midpoint_smul_map_le_of_diagonalProducts
    (q r dq dr : ConditionalFamily) (N : ℕ) (A B : ℝ)
    (hq : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => q n p.1 p.2))
    (hr : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => r n p.1 p.2))
    (hdq : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => dq n p.1 p.2))
    (hdr : ∀ n, n < N → Measurable (fun p : (Fin n → ℝ) × ℝ => dr n p.1 p.2))
    (hsq : ∀ n, n ≤ N → Measurable (sample q n))
    (hsr : ∀ n, n ≤ N → Measurable (sample r n))
    (hderivq : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (q n (sample q n s)) (dq n (sample q n s) t) t)
    (hderivr : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (r n (sample r n s)) (dr n (sample r n s) t) t)
    (hposq : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dq n (sample q n s) t)
    (hposr : ∀ n, n < N → ∀ s, InUnitCube s → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < dr n (sample r n s) t)
    (hA : ∀ s, InUnitCube s → diagonalProduct q dq N s = A)
    (hB : ∀ s, InUnitCube s → diagonalProduct r dr N s = B) :
    ENNReal.ofReal (Real.sqrt (A * B)) •
      Measure.map (midpoint q r N)
        (Measure.pi fun _ : Fin N => volume.restrict (Ioo (0 : ℝ) 1)) ≤
      Measure.pi fun _ : Fin N => (volume : Measure ℝ) := by
  have hdom := weightedDomination_midpoint_of_weight q r dq dr N
    hq hr hdq hdr hsq hsr hderivq hderivr hposq hposr
    (geometricWeight q r dq dr)
    (measurable_geometricWeight_of_le q r dq dr N hsq hsr hdq hdr)
    (geometricWeight_zero q r dq dr)
    (fun n _ s t => geometricWeight_snoc q r dq dr n s t)
  apply hdom.smul_map_le
    (measurable_midpoint_of_samples q r N (hsq N le_rfl) (hsr N le_rfl))
  filter_upwards [geometricWeight_ae_eq_constant q r dq dr N A B hposq hposr hA hB]
    with s hs
  exact hs.ge

end Problem358.TriangularRecursion

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_PrefixSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Problem358.FinitePrefix

lemma bodyQuantileFamily_of_lt {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (t : ℝ) :
    bodyQuantileFamily hK hc n a t = (exists_prefix_quantile hK hc h).choose (a,t) := by
  simp only [bodyQuantileFamily, dite_eq_left h]

lemma measurable_bodyQuantileFamily {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (n : ℕ) :
    Measurable (fun p : Coordinates n × ℝ => bodyQuantileFamily hK hc n p.1 p.2) := by
  by_cases h : n < d
  · simpa only [bodyQuantileFamily, dite_eq_left h] using
      (exists_prefix_quantile hK hc h).choose_spec.1
  · simp only [bodyQuantileFamily, dite_eq_right h]
    exact measurable_const

lemma bodyQuantileFamily_law {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (ha : a ∈ prefixDomain K h.le) :
    Measure.map (bodyQuantileFamily hK hc n a)
      (volume.restrict (Ioo (0 : ℝ) 1)) =
      Measure.map Prod.fst
        (((volume.prod volume) (ConvexTriangularSampler.sectionBody (stepBody K h) a))⁻¹ •
          (volume.prod volume).restrict
            (ConvexTriangularSampler.sectionBody (stepBody K h) a)) := by
  have heq : bodyQuantileFamily hK hc n a =
      fun s => (exists_prefix_quantile hK hc h).choose (a,s) :=
    funext (bodyQuantileFamily_of_lt hK hc h a)
  rw [heq]
  exact (exists_prefix_quantile hK hc h).choose_spec.2.1 a ha

lemma bodyQuantileFamily_mem {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (ha : a ∈ prefixDomain K h.le)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Fin.snoc a (bodyQuantileFamily hK hc n a s) ∈
      prefixDomain K (Nat.succ_le_of_lt h) := by
  simpa only [bodyQuantileFamily, dite_eq_left h] using
    (exists_prefix_quantile hK hc h).choose_spec.2.2.1 a ha s hs

lemma measurable_bodyDerivativeFamily {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (n : ℕ) :
    Measurable (fun p : Coordinates n × ℝ => bodyDerivativeFamily hK hc n p.1 p.2) := by
  by_cases h : n < d
  · simp only [bodyDerivativeFamily, dite_eq_left h]
    have hk : MeasurableSet (stepBody K h) :=
      hK.measurableSet.preimage (tripleSplit h).continuous.measurable
    exact ((ConvexTriangularSampler.measurable_sectionDensity volume hk).comp
      (measurable_fst.prodMk (measurable_bodyQuantileFamily hK hc n))).inv
  · simp only [bodyDerivativeFamily, dite_eq_right h]
    exact measurable_const

lemma bodyQuantileFamily_hasDerivAt {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (ha : a ∈ prefixDomain K h.le)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (bodyQuantileFamily hK hc n a) (bodyDerivativeFamily hK hc n a s) s := by
  have heq : bodyQuantileFamily hK hc n a =
      fun t => (exists_prefix_quantile hK hc h).choose (a,t) :=
    funext (bodyQuantileFamily_of_lt hK hc h a)
  rw [heq]
  simpa only [bodyDerivativeFamily, bodyQuantileFamily, dite_eq_left h] using
    (exists_prefix_quantile hK hc h).choose_spec.2.2.2.1 a ha s hs

lemma bodyDerivativeFamily_pos {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (ha : a ∈ prefixDomain K h.le)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    0 < bodyDerivativeFamily hK hc n a s := by
  simpa only [bodyDerivativeFamily, bodyQuantileFamily, dite_eq_left h] using
    (exists_prefix_quantile hK hc h).choose_spec.2.2.2.2 a ha s hs

end Problem358.FinitePrefix

end

noncomputable section
open Set MeasureTheory

namespace Problem358.FinitePrefix

/-- The actual recursively sampled prefix stays in the projection of the body's interior. -/
theorem bodySample_mem {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∀ n, ∀ h : n ≤ d, ∀ s : Coordinates n,
      TriangularDensity.InUnitCube s →
        TriangularRecursion.sample (bodyQuantileFamily hK hc) n s ∈ prefixDomain K h := by
  intro n
  induction n with
  | zero =>
    intro h s hs
    exact prefixDomain_zero hne _
  | succ n ih =>
    intro h s hs
    exact bodyQuantileFamily_mem hK hc (by omega)
      (TriangularRecursion.sample (bodyQuantileFamily hK hc) n (Fin.init s))
      (ih (by omega) _ hs.init) _ hs.last

/-- Derivative regularity along each scalar input of the concrete sampler. -/
theorem bodySample_fiber_hasDerivAt {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (h : n < d) (s : Coordinates n) (hs : TriangularDensity.InUnitCube s)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (bodyQuantileFamily hK hc n (TriangularRecursion.sample (bodyQuantileFamily hK hc) n s))
      (bodyDerivativeFamily hK hc n (TriangularRecursion.sample (bodyQuantileFamily hK hc) n s) t) t :=
  bodyQuantileFamily_hasDerivAt hK hc h _ (bodySample_mem hK hc hne n h.le s hs) t ht

lemma bodySample_fiber_derivative_pos {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (h : n < d) (s : Coordinates n) (hs : TriangularDensity.InUnitCube s)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < bodyDerivativeFamily hK hc n
      (TriangularRecursion.sample (bodyQuantileFamily hK hc) n s) t :=
  bodyDerivativeFamily_pos hK hc h _ (bodySample_mem hK hc hne n h.le s hs) t ht

/-- The concrete derivative is exactly the ratio of consecutive prefix volumes. -/
lemma bodyDerivativeFamily_eq_ratio {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (t : ℝ) :
    bodyDerivativeFamily hK hc n a t =
      volume.real (prefixSection K h.le a) /
        volume.real (prefixSection K (Nat.succ_le_of_lt h)
          (Fin.snoc a (bodyQuantileFamily hK hc n a t))) := by
  simp only [bodyDerivativeFamily, dite_eq_left h, ConvexTriangularSampler.sectionDensity,
    ConvexTriangularSampler.sectionBody, stepBody, inv_div,
    tripleSplit_parentSection_volumeReal, tripleSplit_childSection_volumeReal]

/-- The diagonal derivatives telescope through the actual geometric section volumes. -/
theorem bodySample_diagonalProduct_eq_ratio {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∀ n, ∀ h : n ≤ d, ∀ s : Coordinates n, TriangularDensity.InUnitCube s →
      TriangularDensity.diagonalProduct (bodyQuantileFamily hK hc)
        (bodyDerivativeFamily hK hc) n s =
          (volume K).toReal /
            volume.real (prefixSection K h
              (TriangularRecursion.sample (bodyQuantileFamily hK hc) n s)) := by
  have hvol : 0 < (volume K).toReal :=
    ENNReal.toReal_pos (MeasureTheory.Measure.measure_pos_of_nonempty_interior volume hne).ne'
      hK.measure_ne_top
  intro n
  induction n with
  | zero =>
    intro h s hs
    simp only [TriangularDensity.diagonalProduct, TriangularRecursion.sample,
      MeasureTheory.Measure.real, volume_prefixSection_zero]
    exact (div_self hvol.ne').symm
  | succ n ih =>
    intro h s hs
    have hn : n < d := by omega
    have hp := prefixSection_volumeReal_pos hK
      (bodySample_mem hK hc hne n hn.le (Fin.init s) hs.init)
    rw [TriangularDensity.diagonalProduct, ih hn.le _ hs.init,
      bodyDerivativeFamily_eq_ratio hK hc hn]
    change _ = (volume K).toReal /
      volume.real (prefixSection K h
        (Fin.snoc (TriangularRecursion.sample (bodyQuantileFamily hK hc) n (Fin.init s))
          (bodyQuantileFamily hK hc n
            (TriangularRecursion.sample (bodyQuantileFamily hK hc) n (Fin.init s))
            (s (Fin.last n)))))
    change 0 < volume.real (prefixSection K hn.le
      (TriangularRecursion.sample (bodyQuantileFamily hK hc) n (Fin.init s))) at hp
    field_simp [hp.ne']

/-- The full Jacobian product is the body's volume, with no seed dependence. -/
theorem bodySample_diagonalProduct_eq_volume {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (s : Coordinates d) (hs : TriangularDensity.InUnitCube s) :
    TriangularDensity.diagonalProduct (bodyQuantileFamily hK hc)
      (bodyDerivativeFamily hK hc) d s = (volume K).toReal := by
  rw [bodySample_diagonalProduct_eq_ratio hK hc hne d (le_refl d) s hs]
  change _ / (volume (prefixSection K (le_refl d)
    (TriangularRecursion.sample (bodyQuantileFamily hK hc) d s))).toReal = _
  rw [volumeReal_prefixSection_full (bodySample_mem hK hc hne d (le_refl d) s hs), div_one]

end Problem358.FinitePrefix

end

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace Problem358.FinitePrefix

theorem prefixLaw_density {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n ≤ d) :
    prefixLaw K h = (volume K)⁻¹ •
      volume.withDensity (fun a => volume (prefixSection K h a)) :=
  map_headBlock_normalized_restrict h hK

theorem isProbabilityMeasure_normalizedVolume {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) :
    IsProbabilityMeasure ((volume K)⁻¹ • volume.restrict K) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_pos_of_nonempty_interior volume hi).ne'
    hK.measure_ne_top

theorem isProbabilityMeasure_prefixLaw {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) (h : n ≤ d) :
    IsProbabilityMeasure (prefixLaw K h) := by
  let := isProbabilityMeasure_normalizedVolume hK hi
  exact (Measure.isProbabilityMeasure_map_iff
    (continuous_headBlock h).measurable.aemeasurable).mpr inferInstance

theorem volume_stepBody {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) : volume (stepBody K h) = volume K := by
  exact (measurePreserving_tripleSplit h).measure_preimage hK.nullMeasurableSet

theorem map_tripleSplit_normalized {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) :
    Measure.map (tripleSplit h)
      ((volume K)⁻¹ • volume.restrict (stepBody K h)) =
      (volume K)⁻¹ • volume.restrict K := by
  rw [Measure.map_smul]
  exact congrArg (fun μ => (volume K)⁻¹ • μ)
    ((measurePreserving_tripleSplit h).restrict_preimage hK).map_eq

theorem prefixLaw_eq_step_fst {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) :
    prefixLaw K h.le = Measure.map Prod.fst
      ((volume K)⁻¹ • volume.restrict (stepBody K h)) := by
  unfold prefixLaw
  rw [← map_tripleSplit_normalized hK h,
    Measure.map_map (continuous_headBlock h.le).measurable (tripleSplit h).continuous.measurable]
  congr 1
  funext p
  ext i
  exact tripleSplit_left h p.1 p.2.1 p.2.2 i

theorem prefixLaw_succ_eq_step_map {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) :
    prefixLaw K (Nat.succ_le_of_lt h) =
      Measure.map (fun p : Coordinates n × (ℝ × Coordinates (d-(n+1))) =>
        Fin.snoc p.1 p.2.1)
        ((volume K)⁻¹ • volume.restrict (stepBody K h)) := by
  unfold prefixLaw
  rw [← map_tripleSplit_normalized hK h,
    Measure.map_map (continuous_headBlock (Nat.succ_le_of_lt h)).measurable
      (tripleSplit h).continuous.measurable]
  congr 1
  funext p
  exact headBlock_tripleSplit h p.1 p.2.1 p.2.2

theorem isMarkovKernel_prefixKernel {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) : IsMarkovKernel (prefixKernel hK h) := by
  let := NormalizedSections.isMarkovKernel_completedSectionKernel
    (volume.prod volume)
    (NormalizedSections.measurable_setDensity (measurableSet_stepBody hK h)) (0, 0)
  exact Kernel.IsMarkovKernel.map _ measurable_fst

theorem prefixKernel_apply_valid {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (h : n < d)
    {a : Coordinates n} (ha : a ∈ prefixDomain K h.le) :
    prefixKernel hK.measurableSet h a = Measure.map Prod.fst
      (((volume.prod volume) (ConvexTriangularSampler.sectionBody (stepBody K h) a))⁻¹ •
        (volume.prod volume).restrict
          (ConvexTriangularSampler.sectionBody (stepBody K h) a)) := by
  classical
  have hm := measurableSet_stepBody hK.measurableSet h
  have hcompact : IsCompact (stepBody K h) :=
    (tripleSplit h).toHomeomorph.isCompact_preimage.mpr hK
  have hvalid : a ∈ ConvexTriangularSampler.valid (stepBody K h) := by
    rwa [valid_stepBody]
  have hgood : a ∈ NormalizedSections.goodSections (volume.prod volume)
      (NormalizedSections.setDensity (stepBody K h)) := by
    change _ ≠ 0 ∧ _ ≠ ∞
    rw [NormalizedSections.sectionMass_setDensity _ hm]
    exact ⟨(measure_pos_of_nonempty_interior _
      (ConvexTriangularSampler.sectionBody_interior_nonempty ⟨a, hvalid⟩)).ne',
      (ConvexTriangularSampler.isCompact_sectionBody hcompact a).measure_ne_top⟩
  rw [prefixKernel, Kernel.map_apply _ measurable_fst,
    NormalizedSections.completedSectionKernel, Kernel.piecewise_apply, ite_eq_left hgood,
    NormalizedSections.sectionKernel_apply _
      (NormalizedSections.measurable_setDensity hm),
    NormalizedSections.sectionLaw_setDensity _ hm]
  rfl

theorem prefixLaw_compProd_prefixKernel {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) (h : n < d) :
    (prefixLaw K h.le).compProd (prefixKernel hK.measurableSet h) =
      Measure.map (Prod.map id Prod.fst)
        ((volume K)⁻¹ • volume.restrict (stepBody K h)) := by
  let := isProbabilityMeasure_prefixLaw hK hi h.le
  have hm := measurableSet_stepBody hK.measurableSet h
  let := NormalizedSections.isMarkovKernel_completedSectionKernel
    (volume.prod volume) (NormalizedSections.measurable_setDensity hm) (0, 0)
  have hvol : (volume.prod (volume.prod volume)) (stepBody K h) = volume K :=
    volume_stepBody hK.measurableSet h
  have hρ : prefixLaw K h.le = (volume K)⁻¹ •
      volume.withDensity (NormalizedSections.sectionMass (volume.prod volume)
        (NormalizedSections.setDensity (stepBody K h))) := by
    rw [prefixLaw_eq_step_fst hK.measurableSet h,
      Measure.map_smul]
    congr 1
    rw [volume_eq_prod, volume_eq_prod,
      SectionMarginal.map_fst_restrict volume (volume.prod volume) _ hm]
    congr 1
    funext a
    exact (NormalizedSections.sectionMass_setDensity _ hm a).symm
  rw [prefixKernel, Measure.compProd_map measurable_fst, hρ]
  congr 1
  have hd := NormalizedSections.compProd_uniformSetSections volume
    (volume.prod volume) hm (0, 0) (hvol ▸ hK.measure_ne_top)
  simpa only [hvol, volume_eq_prod] using hd

/-- Genuine one-step disintegration of the geometric prefix laws. -/
theorem prefixLaw_succ {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) (h : n < d) :
    prefixLaw K (Nat.succ_le_of_lt h) =
      Measure.map (fun p : Coordinates n × ℝ => Fin.snoc p.1 p.2)
        ((prefixLaw K h.le).compProd (prefixKernel hK.measurableSet h)) := by
  rw [prefixLaw_compProd_prefixKernel hK hi h,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact prefixLaw_succ_eq_step_map hK.measurableSet h

end Problem358.FinitePrefix

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358.FinitePrefix

open TriangularRecursion

/-- The midpoint of the two actual convex-body samplers has the sharp geometric
volume domination. All scalar differentiability, prefix support, measurability,
and terminal Jacobian identities are consequences of the two bodies. -/
theorem bodyMidpoint_smul_map_le_volume
    {d : ℕ} {K L : Set (Coordinates d)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hiK : (interior K).Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hiL : (interior L).Nonempty) :
    ENNReal.ofReal (Real.sqrt ((volume K).toReal * (volume L).toReal)) •
      Measure.map (midpoint (bodyQuantileFamily hK hcK) (bodyQuantileFamily hL hcL) d)
        (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) ≤
      (volume : Measure (Coordinates d)) := by
  simpa only [volume_pi] using
    midpoint_smul_map_le_of_diagonalProducts
      (bodyQuantileFamily hK hcK) (bodyQuantileFamily hL hcL)
      (bodyDerivativeFamily hK hcK) (bodyDerivativeFamily hL hcL)
      d (volume K).toReal (volume L).toReal
      (fun n _ => measurable_bodyQuantileFamily hK hcK n)
      (fun n _ => measurable_bodyQuantileFamily hL hcL n)
      (fun n _ => measurable_bodyDerivativeFamily hK hcK n)
      (fun n _ => measurable_bodyDerivativeFamily hL hcL n)
      (fun n _ => measurable_sample _ (measurable_bodyQuantileFamily hK hcK) n)
      (fun n _ => measurable_sample _ (measurable_bodyQuantileFamily hL hcL) n)
      (fun _ hn s hs t ht => bodySample_fiber_hasDerivAt hK hcK hiK hn s hs t ht)
      (fun _ hn s hs t ht => bodySample_fiber_hasDerivAt hL hcL hiL hn s hs t ht)
      (fun _ hn s hs t ht => bodySample_fiber_derivative_pos hK hcK hiK hn s hs t ht)
      (fun _ hn s hs t ht => bodySample_fiber_derivative_pos hL hcL hiL hn s hs t ht)
      (bodySample_diagonalProduct_eq_volume hK hcK hiK)
      (bodySample_diagonalProduct_eq_volume hL hcL hiL)

end Problem358.FinitePrefix

end

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace Problem358.FinitePrefix

/-- Every stage of the actual convex-body quantile construction has the
corresponding geometric prefix marginal. -/
theorem map_bodyQuantile_sample_prefix {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    ∀ n (h : n ≤ d),
      Measure.map (TriangularRecursion.sample (bodyQuantileFamily hK hc) n)
        (Measure.pi (fun _ : Fin n => volume.restrict (Ioo (0 : ℝ) 1))) =
          prefixLaw K h := by
  intro n
  induction n with
  | zero =>
      intro h
      change Measure.map id _ = _
      rw [Measure.map_id, prefixLaw_density hK.measurableSet h,
        normalized_initial_prefix_law
          (measure_pos_of_nonempty_interior volume hi).ne' hK.measure_ne_top]
      rw [Measure.pi_of_empty, volume_pi_eq_dirac]
  | succ n ih =>
      intro h
      have hn : n < d := h
      have hbase := ih hn.le
      let := isProbabilityMeasure_prefixLaw hK hi hn.le
      let := isMarkovKernel_prefixKernel hK.measurableSet hn
      have hF := TriangularRecursion.measurable_sample (bodyQuantileFamily hK hc)
        (measurable_bodyQuantileFamily hK hc) n
      have hG : Measurable (fun p : Coordinates n × ℝ =>
          bodyQuantileFamily hK hc n
            (TriangularRecursion.sample (bodyQuantileFamily hK hc) n p.1) p.2) := by
        exact (measurable_bodyQuantileFamily hK hc n).comp
          ((hF.comp measurable_fst).prodMk measurable_snd)
      have hgood := ae_sample_mem_prefixDomain hc hn.le hF.aemeasurable hbase
      have hfiber : ∀ᵐ a ∂Measure.pi
          (fun _ : Fin n => volume.restrict (Ioo (0 : ℝ) 1)),
          Measure.map (bodyQuantileFamily hK hc n
            (TriangularRecursion.sample (bodyQuantileFamily hK hc) n a))
              (volume.restrict (Ioo (0 : ℝ) 1)) =
          prefixKernel hK.measurableSet hn
            (TriangularRecursion.sample (bodyQuantileFamily hK hc) n a) := by
        filter_upwards [hgood] with a ha
        exact (bodyQuantileFamily_law hK hc hn _ ha).trans
          (prefixKernel_apply_valid hK hn ha).symm
      rw [prefixLaw_succ hK hi hn]
      exact TriangularSampling.map_snoc_pi_eq n (volume.restrict (Ioo (0 : ℝ) 1))
        (prefixLaw K hn.le) (prefixKernel hK.measurableSet hn)
        (TriangularRecursion.sample (bodyQuantileFamily hK hc) n)
        (fun p => bodyQuantileFamily hK hc n
          (TriangularRecursion.sample (bodyQuantileFamily hK hc) n p.1) p.2)
        hF hG hbase hfiber

/-- The concrete, globally measurable triangular quantile sampler has exactly
the uniform probability law of the convex body. -/
theorem map_bodyQuantile_sample {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    Measure.map (TriangularRecursion.sample (bodyQuantileFamily hK hc) d)
      (Measure.pi (fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1))) =
        (volume K)⁻¹ • volume.restrict K := by
  simpa only [prefixLaw_full] using map_bodyQuantile_sample_prefix hK hc hi d le_rfl

end Problem358.FinitePrefix

end

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Problem358

/-- A convex body of positive volume has a nonempty interior. -/
lemma convex_interior_nonempty_of_volume_pos {d : ℕ} {K : Set (E d)}
    (hc : Convex ℝ K) (hvol : 0 < volume K) : (interior K).Nonempty := by
  by_contra h
  have he : interior K = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hv := MidpointCoordinates.volume_interior hc
  rw [he, measure_empty] at hv
  exact hvol.ne' hv.symm

/-- All body hypotheses survive the canonical volume-preserving Euclidean coordinate map. -/
lemma coordinate_body_geometry {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty) :
    IsCompact ((WithLp.toLp 2) ⁻¹' K) ∧
      Convex ℝ ((WithLp.toLp 2) ⁻¹' K) ∧
      (interior ((WithLp.toLp 2) ⁻¹' K)).Nonempty := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have he : (e : (Fin d → ℝ) → E d) = WithLp.toLp 2 := rfl
  rw [← he]
  refine ⟨e.toHomeomorph.isCompact_preimage.mpr hK, hc.linear_preimage e.toLinearMap, ?_⟩
  change (interior (e.toHomeomorph ⁻¹' K)).Nonempty
  rw [← e.toHomeomorph.preimage_interior]
  exact hne.preimage e.surjective

/-- Every pair of compact convex bodies admits a uniform coupling whose midpoint
law is dominated by volume with the geometric-mean volume factor. -/
theorem exists_convexBody_midpoint_coupling {d : ℕ} {K L : Set (E d)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hiK : (interior K).Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hiL : (interior L).Nonempty) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      ENNReal.ofReal (Real.sqrt ((volume K).toReal * (volume L).toReal)) •
        Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
  obtain ⟨hK', hcK', hiK'⟩ := coordinate_body_geometry hK hcK hiK
  obtain ⟨hL', hcL', hiL'⟩ := coordinate_body_geometry hL hcL hiL
  let Q := FinitePrefix.bodyQuantileFamily hK' hcK'
  let R := FinitePrefix.bodyQuantileFamily hL' hcL'
  let : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
    simp [Real.volume_Ioo]⟩
  have hdom := FinitePrefix.bodyMidpoint_smul_map_le_volume hK' hcK' hiK' hL' hcL' hiL'
  rw [MidpointCoordinates.volume_preimage_toLp hK.measurableSet,
    MidpointCoordinates.volume_preimage_toLp hL.measurableSet] at hdom
  apply MidpointCoordinates.exists_midpoint_coupling_of_coordinate_samplers
    (ρ := Measure.pi (fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)))
    hK.measurableSet hL.measurableSet
    (TriangularRecursion.sample Q d) (TriangularRecursion.sample R d)
    (TriangularRecursion.measurable_sample Q (FinitePrefix.measurable_bodyQuantileFamily hK' hcK') d)
    (TriangularRecursion.measurable_sample R (FinitePrefix.measurable_bodyQuantileFamily hL' hcL') d)
    (FinitePrefix.map_bodyQuantile_sample hK' hcK' hiK')
    (FinitePrefix.map_bodyQuantile_sample hL' hcL' hiL')
  convert hdom using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext s i
  simp [TriangularRecursion.midpoint, Q, R, div_eq_mul_inv, mul_comm]

/-- Positive volume suffices, including in dimension zero. -/
theorem exists_convexBody_midpoint_coupling_of_pos {d : ℕ} {K L : Set (E d)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hvK : 0 < volume K)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hvL : 0 < volume L) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      ENNReal.ofReal (Real.sqrt ((volume K).toReal * (volume L).toReal)) •
        Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume :=
  exists_convexBody_midpoint_coupling hK hcK
    (convex_interior_nonempty_of_volume_pos hcK hvK) hL hcL
    (convex_interior_nonempty_of_volume_pos hcL hvL)

end Problem358

end

end OAI
end

section
-- module Solutions.OAIQ5_T2.Brenier_CanonicalPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal ContDiff

namespace Problem358.FixedMassIntercepts

/-- Canonical closed-cell intercepts give the entire normalized path interface:
measurability is global, while differentiability and derivative continuity are
needed only on the open interval where the sites are distinct. -/
theorem exists_canonical_atomic_intercept_path
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y z : ι → E d) {κ : ℝ} {R : ℝ≥0}
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (fun i => (1-t) • y i + t • z i))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) 1,
      ContDiffAt ℝ 1 (fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
        (fun i => (1-q) • y i + q • z i)) t)
    (henergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      let C := fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
        (fun i => (1-q) • y i + q • z i)
      (∑ i, m i * ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i ^ 2) ≤
        κ * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i-z i‖ ^ 2) :
    ∃ c r : ι → ℝ → ℝ,
      (∀ i, Measurable (c i)) ∧
      (∀ i, ContinuousOn (r i) (Ioo 0 1)) ∧
      (∀ i t, t ∈ Ioo 0 1 → HasDerivAt (c i) (r i t) t) ∧
      (∀ t ∈ Ioo 0 1, ∀ i,
        (uniformMeasure K).real (CellGeometry.closedCell K
          (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i) ∧
      (∀ t ∈ Ioo 0 1, (∑ i, m i * c i t) = 0) ∧
      ∀ t ∈ Ioo 0 1, (∑ i, m i * r i t ^ 2) ≤
        κ * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i-z i‖ ^ 2 := by
  let C := fun (q : ℝ) => intercepts hK hconv hKi m hm hsum
    (fun i => (1-q) • y i + q • z i)
  let c : ι → ℝ → ℝ := fun i t => (C t : ι → ℝ) i
  let L : ι → CellLaplacian.normalizedSpace m →L[ℝ] ℝ := fun i =>
    (ContinuousLinearMap.proj i).comp (CellLaplacian.normalizedSpace m).subtypeL
  have hcoord : ∀ i t, t ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (c i) (((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i) t := by
    intro i t ht
    exact (L i).hasFDerivAt.comp_hasDerivAt t
      ((hregular t ht).differentiableAt (by norm_num)).hasDerivAt
  refine ⟨c, fun i => deriv (c i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (measurable_pi_apply i).comp
      ((measurable_intercepts_coe hK hconv hKi m hm hsum).comp (by fun_prop))
  · intro i
    have hci : ContDiffOn ℝ 1 (c i) (Ioo 0 1) := by
      intro t ht
      exact ((L i).contDiff.contDiffAt.comp t (hregular t ht)).contDiffWithinAt
    exact hci.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  · intro i t ht
    exact (hcoord i t ht).differentiableAt.hasDerivAt
  · intro t ht i
    exact congrFun (intercepts_spec hK hconv hKi m hm hsum
      (fun j => (1-t) • y j + t • z j) (hinj t ht)) i
  · intro t _
    exact (C t).property
  · intro t ht
    have heq : ∀ i, deriv (c i) t =
        ((deriv C t : CellLaplacian.normalizedSpace m) : ι → ℝ) i :=
      fun i => (hcoord i t ht).deriv
    simp_rw [heq]
    exact henergy t ht

end Problem358.FixedMassIntercepts

end

noncomputable section

open Set MeasureTheory
open scoped BigOperators NNReal ContDiff

namespace Problem358.FixedMassIntercepts

/-- Positive prescribed masses along distinct affine site paths admit genuine
normalized intercepts with continuous derivatives and the uniform geometric
energy bound. All mass regularity and midpoint-coupling inputs are discharged. -/
theorem exists_actual_atomic_intercept_path_oai
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y z : ι → E d) (R : ℝ≥0)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (fun i => (1-t) • y i + t • z i)) :
    ∃ c r : ι → ℝ → ℝ,
      (∀ i, Measurable (c i)) ∧
      (∀ i, ContinuousOn (r i) (Ioo 0 1)) ∧
      (∀ i t, t ∈ Ioo 0 1 → HasDerivAt (c i) (r i t) t) ∧
      (∀ t ∈ Ioo 0 1, ∀ i,
        (uniformMeasure K).real (CellGeometry.closedCell K
          (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i) ∧
      (∀ t ∈ Ioo 0 1, (∑ i, m i * c i t) = 0) ∧
      ∀ t ∈ Ioo 0 1, (∑ i, m i * r i t ^ 2) ≤
        162 * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i-z i‖ ^ 2 := by
  classical
  let Y : ℝ → (ι → E d) := fun t i => (1-t) • y i + t • z i
  let C := fun t => intercepts hK hconv hKi m hm hsum (Y t)
  let v : ι → E d := fun i => z i - y i
  have hmassC1 : ∀ t ∈ Ioo (0 : ℝ) 1,
      ContDiffAt ℝ 1 (CellGeometry.normalizedMassMap K m) (Y t, C t) := by
    intro t ht
    apply CellGeometry.contDiffAt_normalizedMassMap_of_raw m (Y t, C t)
    apply CellGeometry.contDiffAt_uniformMassMap hK hconv (Y t) (C t) (hinj t ht)
    intro i
    have hi := congrFun (intercepts_spec hK hconv hKi m hm hsum (Y t) (hinj t ht)) i
    change (uniformMeasure K).real (CellGeometry.closedCell K (Y t) (C t) i) = m i at hi
    rw [hi]
    exact hm i
  apply exists_canonical_atomic_intercept_path hK hconv hKi m hm hsum y z
    (κ := 162) (R := R) hinj
  · intro t ht
    have hYc : ContDiffAt ℝ 1 Y t := by dsimp [Y]; fun_prop
    exact (contDiffAt_intercepts_of_normalizedMassC1 hK hconv hKi m hm hsum
      (Y t) (hinj t ht) (hmassC1 t ht)).comp t hYc
  · intro t ht
    have hYd : HasDerivAt Y v t := by
      apply hasDerivAt_pi.mpr
      intro i
      have heq : (fun q : ℝ => Y q i) = fun q => y i + q • (z i - y i) := by
        funext q
        dsimp [Y]
        module
      rw [heq]
      simpa only [v, one_smul] using!
        ((hasDerivAt_id t).smul_const (z i - y i)).const_add (y i)
    let e : ℝ := ∑ i, m i * ‖y i-z i‖ ^ 2
    have he : 0 ≤ e := Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
    have hspeed : (∑ i, m i * ‖v i‖ ^ 2) ≤ Real.sqrt e ^ 2 := by
      rw [Real.sq_sqrt he]
      exact le_of_eq (Finset.sum_congr rfl fun i _ => by simp only [v, norm_sub_rev])
    have henergy := intercepts_comp_deriv_energy_le_of_massC1_convex_midpoint
      hK hconv hKi m hm hsum Y v t hYd (hinj t ht) R R.property
      hbounded hspeed (hmassC1 t ht)
      (fun U V hU hcU hvU hV hcV hvV =>
        exists_convexBody_midpoint_coupling_of_pos hU hcU hvU hV hcV hvV)
    simpa only [Real.sq_sqrt he] using henergy.2

end Problem358.FixedMassIntercepts

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path_oai.{u_1} := @OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path_oai.{u_1}
