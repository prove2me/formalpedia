-- Prove2me | solution 1 for OAI.DoublingHilbert.anisotropic_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:27:22.508108+00:00
-- url     : https://prove2.me/submissions/ed827a0f-59d1-4bbb-a65a-7f23df555956

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Energy.lean:L125-L205
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.anisotropic_energy_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Theorems.Thm_OAI_DoublingHilbert_IsBoundedField_select
import Theorems.Thm_OAI_DoublingHilbert_ae_horizontal_pair
import Theorems.Thm_OAI_DoublingHilbert_ae_vertical_pair
import Theorems.Thm_OAI_DoublingHilbert_horizontalColumn_mean
import Theorems.Thm_OAI_DoublingHilbert_integral_variance_identity
import Theorems.Thm_OAI_DoublingHilbert_verticalColumn_x_mean
import Theorems.Thm_OAI_DoublingHilbert_verticalColumn_y_mean
import Theorems.Thm_OAI_DoublingHilbert_vertical_variance_bound

-- ---- from OAI.Geometry.DoublingHilbert.Integration ----
namespace OAI

/-! Line integration and global Lipschitz extensions of sheets. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace DoublingHilbert

section FTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end FTC

section MeanSquares
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Hilbert-space Cauchy--Schwarz in the form needed for line transport;
in fact convexity makes this valid for every normed target. -/
theorem norm_average_sq_le_average_norm_sq [IsFiniteMeasure μ] [NeZero μ]
    {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) :
    ‖⨍ x, G x ∂μ‖ ^ 2 ≤ ⨍ x, ‖G x‖ ^ 2 ∂μ := by
  exact ((convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set E))).pow
    (fun _ _ => norm_nonneg _) 2).map_average_le
      (continuous_norm.pow 2).continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) hG hG2

/-- The integral version of the preceding averaged estimate, retaining the exact mass. -/
theorem norm_integral_sq_le_mass_mul [IsFiniteMeasure μ]
    {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) :
    ‖∫ x, G x ∂μ‖ ^ 2 ≤ μ.real Set.univ * (∫ x, ‖G x‖ ^ 2 ∂μ) := by
  by_cases hμ : μ = 0
  · subst μ; simp
  have : NeZero μ := ⟨hμ⟩
  have hm := measureReal_univ_pos (μ := μ)
  have hj := norm_average_sq_le_average_norm_sq hG hG2
  simp only [average_eq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg hm.le, smul_eq_mul, ← div_eq_inv_mul] at hj
  have hj' := mul_le_mul_of_nonneg_left hj (sq_nonneg (μ.real univ))
  field_simp at hj'
  nlinarith

end MeanSquares
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section PartialIntegration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem norm_column_le {f : ℝ × ℝ → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : ℝ × ℝ) (p : ℝ × ℝ) : ‖column f v p‖ ≤ C * ‖v‖ :=
  ((fderiv ℝ f p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

omit [CompleteSpace E] in
theorem stronglyMeasurable_column (f : ℝ × ℝ → E) (v : ℝ × ℝ) :
    StronglyMeasurable (column f v) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact ((ContinuousLinearMap.apply ℝ E v).continuous.measurable.comp
    (measurable_fderiv ℝ f)).stronglyMeasurable

end PartialIntegration
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section Extensions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem globalSheet_lipschitz {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) :
    ∃ L : NNReal, LipschitzWith L (globalSheet hf w) := by
  obtain ⟨L, hL, _⟩ :=
    (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose_spec
  exact ⟨L, hL⟩

end Extensions
end
end DoublingHilbert

end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.Rectangles ----
namespace OAI

/-! Rectangle probability measures, transport estimates, and finite averaging. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace DoublingHilbert

namespace Segment

end Segment

namespace Rectangle

end Rectangle

section BoundedFields
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

namespace IsBoundedField

theorem integrable {g : X → E} (hg : IsBoundedField g) (μ : Measure X)
    [IsFiniteMeasure μ] : Integrable g μ := by
  obtain ⟨M, hM⟩ := hg.2
  exact Integrable.of_bound hg.1.aestronglyMeasurable M (Eventually.of_forall hM)

theorem norm_sq {g : X → E} (hg : IsBoundedField g) :
    IsBoundedField (fun x => ‖g x‖ ^ 2) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.norm.pow 2, M ^ 2, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM x) 2

theorem sub {f g : X → E} (hf : IsBoundedField f) (hg : IsBoundedField g) :
    IsBoundedField (fun x => f x - g x) := by
  obtain ⟨M, hM⟩ := hf.2
  obtain ⟨N, hN⟩ := hg.2
  exact ⟨hf.1.sub hg.1, M + N, fun x => (norm_sub_le _ _).trans (add_le_add (hM x) (hN x))⟩

theorem const (e : E) : IsBoundedField (fun _ : X => e) :=
  ⟨stronglyMeasurable_const, ‖e‖, fun _ => le_rfl⟩

end IsBoundedField
end BoundedFields

end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

namespace Rectangle

end Rectangle

namespace IsBoundedField
variable {X Y I E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E]

variable [NormedSpace ℝ E]

end IsBoundedField
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

section RectangleFTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem boundedField_column {f : Base → E} {C : NNReal} (hf : LipschitzWith C f)
    (v : Base) : IsBoundedField (column f v) :=
  ⟨stronglyMeasurable_column f v, C * ‖v‖, norm_column_le hf v⟩

end RectangleFTC
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace Rectangle

end Rectangle

section LocalSquare
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end LocalSquare
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace Segment

end Segment

namespace Rectangle

end Rectangle
end
end DoublingHilbert

end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.Grids ----
namespace OAI

/-! Fine period grids, energy sampling, and sheet separation. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem measurable_stripColor (N : ℕ) (hN : 0 < N) (h : ℝ) :
    Measurable (stripColor N hN h) := by
  let c : ℤ → Fin N := fun z => ⟨(z % (N : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg z (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos z (by exact_mod_cast hN : (0 : ℤ) < N)
    exact_mod_cast (Int.toNat_lt hnonneg).mpr hlt⟩
  exact (measurable_of_countable c).comp
    (Int.measurable_floor.comp (measurable_id.div_const h))

namespace Segment

end Segment

end
end DoublingHilbert

namespace DoublingHilbert
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

namespace Segment

end Segment

namespace Rectangle

end Rectangle

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section SheetGeometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

end SheetGeometry

end
end DoublingHilbert

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.SelectedSheets ----
namespace OAI

/-! Periodic selections of sheets and stripewise derivative means. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace IsBoundedField
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem add {f g : X → E} (hf : IsBoundedField f) (hg : IsBoundedField g) :
    IsBoundedField (fun x => f x + g x) := by
  obtain ⟨M, hM⟩ := hf.2
  obtain ⟨N, hN⟩ := hg.2
  exact ⟨hf.1.add hg.1, M + N,
    fun x => (norm_add_le _ _).trans (add_le_add (hM x) (hN x))⟩

theorem const_mul {g : X → ℝ} (hg : IsBoundedField g) (r : ℝ) :
    IsBoundedField (fun x => r * g x) := by
  obtain ⟨M, hM⟩ := hg.2
  refine ⟨hg.1.const_mul r, ‖r‖ * M, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg r)

end IsBoundedField

section StripeMeans
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

end StripeMeans
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

namespace PeriodGrid
variable {j : ℕ}

end PeriodGrid

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

namespace Rectangle

end Rectangle

section SelectedSheets
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem bounded_horizontalColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (v : Base) :
    IsBoundedField (horizontalColumn hf w j v) := by
  unfold horizontalColumn
  apply IsBoundedField.select (g := fun i p => column (addedSheet hf w j i) v p)
    _ ((measurable_stripColor (colors j) (colors_pos j) (scale j)).comp measurable_snd)
  intro i
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  exact boundedField_column hC v

omit [CompleteSpace E] in
theorem bounded_verticalColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (v : Base) :
    IsBoundedField (verticalColumn hf w j v) := by
  unfold verticalColumn
  apply IsBoundedField.select (g := fun i p => column (addedSheet hf w j i) v p)
    _ ((measurable_stripColor (colors j) (colors_pos j) (stripWidth j)).comp measurable_fst)
  intro i
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  exact boundedField_column hC v

end SelectedSheets
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section
section VerticalStripeMean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end VerticalStripeMean
end
end DoublingHilbert

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.Extremal ----
namespace OAI

/-! Compact lexicographic extrema and quantitative second-moment estimates. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory
open scoped BigOperators

section Moments

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Small moment error and an upper second moment force small mean-square variation. -/
theorem variance_le_of_moments {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) {M : ℝ}
    (hM : (∫ x, ‖G x‖ ^ 2 ∂μ) ≤ M) :
    (∫ x, ‖G x - a‖ ^ 2 ∂μ) ≤ M - ‖a‖ ^ 2 +
      2 * ‖a‖ * ‖(∫ x, G x ∂μ) - a‖ := by
  rw [integral_variance_identity hG hG2 a]
  have h := real_inner_le_norm (-a) ((∫ x, G x ∂μ) - a)
  simp only [inner_neg_left, norm_neg] at h
  nlinarith

end Moments

end DoublingHilbert

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.Energy ----
namespace OAI

/-! Anisotropic energy bounds and arbitrarily small-energy period grids. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

/-- A squared triangle inequality with the same reference vector. -/
theorem norm_sub_sq_le_two {E : Type*} [NormedAddCommGroup E] (a b c : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a - c‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have h := norm_sub_le_norm_sub_add_norm_sub a c b
  rw [norm_sub_rev c b] at h
  have hs := pow_le_pow_left₀ (norm_nonneg (a - b)) h 2
  nlinarith [sq_nonneg (‖a - c‖ - ‖b - c‖)]

section ProbabilityEnergy
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_mean_sub_le_of_energy {F : X → E} (hF : IsBoundedField F)
    (a : E) {t : ℝ} (ht : 0 ≤ t)
    (he : (∫ x, ‖F x - a‖ ^ 2 ∂μ) ≤ t ^ 2) :
    ‖(∫ x, F x ∂μ) - a‖ ≤ t := by
  have hf := hF.sub (IsBoundedField.const a)
  have hb := norm_integral_sq_le_mass_mul (hf.integrable μ) (hf.norm_sq.integrable μ)
  rw [probReal_univ, one_mul, integral_sub (hF.integrable μ) (integrable_const a),
    integral_const, probReal_univ, one_smul] at hb
  exact (sq_le_sq₀ (norm_nonneg _) ht).mp (hb.trans he)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem energy_sub_le_two {F G : X → E} (hF : IsBoundedField F)
    (hG : IsBoundedField G) (a : E) :
    (∫ x, ‖G x - F x‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖G x - a‖ ^ 2 ∂μ) + 2 * (∫ x, ‖F x - a‖ ^ 2 ∂μ) := by
  have hGa := (hG.sub (IsBoundedField.const a)).norm_sq
  have hFa := (hF.sub (IsBoundedField.const a)).norm_sq
  have hb := integral_mono ((hG.sub hF).norm_sq.integrable μ)
    (((hGa.const_mul 2).add (hFa.const_mul 2)).integrable μ)
    (fun x => norm_sub_sq_le_two (G x) (F x) a)
  simpa only [integral_add ((hGa.const_mul 2).integrable μ) ((hFa.const_mul 2).integrable μ),
    integral_const_mul] using hb

end ProbabilityEnergy

section Energies
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem bounded_baseColumn {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (v : Base) :
    IsBoundedField (column (globalSheet hf w) v) := by
  obtain ⟨C, hC⟩ := globalSheet_lipschitz hf w
  exact boundedField_column hC v

end Energies

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

section AnisotropicEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Finite-epsilon anisotropic energy estimates. -/
theorem anisotropic_energy_bound {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (G : PeriodGrid j) (hQ : G.rectangle.closed ⊆ sheetDomain w)
    {A B C ε t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hfirst : ∀ z ∈ derivativeCompact f, z.1 ≤ A)
    (hbarrier : ∀ z ∈ derivativeCompact f, z.2 ≤ B + ε + C * (A - z.1))
    (u v : E) (hu : ‖u‖ ≤ 2 * D) (hv : ‖v‖ ≤ 2 * D)
    (hnearu : A - ‖u‖ ^ 2 ≤ t) (hnearv : B - ‖v‖ ^ 2 ≤ t)
    (hbaseu : (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2)
    (hbasev : (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2)
    (hrx : scale j / G.rectangle.x.length ≤ t)
    (hry : scale j / G.rectangle.y.length ≤ t) :
    (∫ p, horizontalEnergy hf w j p ∂G.rectangle.law) ≤ horizontalCoefficient D * t ∧
    (∫ p, verticalEnergy hf w j p ∂G.rectangle.law) ≤
      2 * ε + 16 * C * (D : ℝ) ^ 2 / (widthFactor j : ℝ) + verticalCoefficient D C * t := by
  let Q := G.rectangle
  let H := horizontalColumn hf w j (1, 0)
  let X := verticalColumn hf w j (1, 0)
  let Y := verticalColumn hf w j (0, 1)
  let F₁ := column (globalSheet hf w) (1, 0)
  let F₂ := column (globalSheet hf w) (0, 1)
  have bH : IsBoundedField H := bounded_horizontalColumn hf w j _
  have bX : IsBoundedField X := bounded_verticalColumn hf w j _
  have bY : IsBoundedField Y := bounded_verticalColumn hf w j _
  have bF₁ : IsBoundedField F₁ := bounded_baseColumn hf w _
  have bF₂ : IsBoundedField F₂ := bounded_baseColumn hf w _
  have hmu : ‖(∫ p, F₁ p ∂Q.law) - u‖ ≤ t :=
    norm_mean_sub_le_of_energy bF₁ u ht hbaseu
  have hmv : ‖(∫ p, F₂ p ∂Q.law) - v‖ ≤ t :=
    norm_mean_sub_le_of_energy bF₂ v ht hbasev
  have hrx' : 2 * (D : ℝ) * scale j / Q.x.length ≤ 2 * D * t := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hrx (by positivity : 0 ≤ 2 * (D : ℝ))
  have hry' : 2 * (D : ℝ) * scale j / Q.y.length ≤ 2 * D * t := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hry (by positivity : 0 ≤ 2 * (D : ℝ))
  have hmH : ‖(∫ p, H p ∂Q.law) - u‖ ≤ (2 * D + 1) * t := by
    have h := horizontalColumn_mean hf w j hj Q hQ
    have htri := norm_sub_le_norm_sub_add_norm_sub (∫ p, H p ∂Q.law) (∫ p, F₁ p ∂Q.law) u
    change ‖(∫ p, H p ∂Q.law) - (∫ p, F₁ p ∂Q.law)‖ ≤ _ at h
    linarith
  have hmX : ‖(∫ p, X p ∂Q.law) - u‖ ≤ 2 * D / (widthFactor j : ℝ) + t := by
    have h := verticalColumn_x_mean hf w j hj G hQ
    have htri := norm_sub_le_norm_sub_add_norm_sub (∫ p, X p ∂Q.law) (∫ p, F₁ p ∂Q.law) u
    change ‖(∫ p, X p ∂Q.law) - (∫ p, F₁ p ∂Q.law)‖ ≤ _ at h
    linarith
  have hmY : ‖(∫ p, Y p ∂Q.law) - v‖ ≤ (2 * D + 1) * t := by
    have h := verticalColumn_y_mean hf w j hj Q hQ
    have htri := norm_sub_le_norm_sub_add_norm_sub (∫ p, Y p ∂Q.law) (∫ p, F₂ p ∂Q.law) v
    change ‖(∫ p, Y p ∂Q.law) - (∫ p, F₂ p ∂Q.law)‖ ≤ _ at h
    linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  constructor
  · have hsecond : (∫ p, ‖H p‖ ^ 2 ∂Q.law) ≤ A := by
      have hb := integral_mono_ae (bH.norm_sq.integrable Q.law) (integrable_const A)
        ((ae_horizontal_pair hf w j hj Q hQ).mono fun p hp => hfirst _ hp)
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hb
    have hvar := variance_le_of_moments (bH.integrable Q.law) (bH.norm_sq.integrable Q.law) u hsecond
    have hmprod : 2 * ‖u‖ * ‖(∫ p, H p ∂Q.law) - u‖ ≤
        2 * (2 * D) * ((2 * D + 1) * t) := by gcongr
    have hcompare := energy_sub_le_two (μ := Q.law) bF₁ bH u
    change (∫ p, ‖H p - F₁ p‖ ^ 2 ∂Q.law) ≤ horizontalCoefficient D * t
    unfold horizontalCoefficient
    nlinarith
  · have hvar := vertical_variance_bound (bX.integrable Q.law) (bX.norm_sq.integrable Q.law)
      (bY.integrable Q.law) (bY.norm_sq.integrable Q.law) (ae_vertical_pair hf w j hj Q hQ)
      hC hbarrier u v hu hv
    have hvar' : (∫ p, ‖Y p - v‖ ^ 2 ∂Q.law) ≤
        t + ε + C * (t + 4 * D * (2 * D / (widthFactor j : ℝ) + t)) +
          4 * D * ((2 * D + 1) * t) := by
      refine hvar.trans ?_
      change B - ‖v‖ ^ 2 + ε + C * (A - ‖u‖ ^ 2 + 2 * (2 * D) * ‖(∫ p, X p ∂Q.law) - u‖) +
        2 * (2 * D) * ‖(∫ p, Y p ∂Q.law) - v‖ ≤ _
      have hfour : (2 : ℝ) * (2 * D) = 4 * D := by ring
      rw [hfour]
      gcongr
    have hcompare := energy_sub_le_two (μ := Q.law) bF₂ bY v
    change (∫ p, ‖Y p - F₂ p‖ ^ 2 ∂Q.law) ≤ _
    calc
      _ ≤ 2 * (t + ε + C * (t + 4 * D * (2 * D / (widthFactor j : ℝ) + t)) +
          4 * D * ((2 * D + 1) * t)) + 2 * t := by nlinarith
      _ = _ := by unfold verticalCoefficient; ring

end AnisotropicEnergy
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section
section NearMaxGrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end NearMaxGrid
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

section SmallEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end SmallEnergy
end
end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem solution {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (hj : w j = 0)
    (G : PeriodGrid j) (hQ : G.rectangle.closed ⊆ sheetDomain w)
    {A B C ε t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hfirst : ∀ z ∈ derivativeCompact f, z.1 ≤ A)
    (hbarrier : ∀ z ∈ derivativeCompact f, z.2 ≤ B + ε + C * (A - z.1))
    (u v : E) (hu : ‖u‖ ≤ 2 * D) (hv : ‖v‖ ≤ 2 * D)
    (hnearu : A - ‖u‖ ^ 2 ≤ t) (hnearv : B - ‖v‖ ^ 2 ≤ t)
    (hbaseu : (∫ p, ‖column (globalSheet hf w) (1, 0) p - u‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2)
    (hbasev : (∫ p, ‖column (globalSheet hf w) (0, 1) p - v‖ ^ 2 ∂G.rectangle.law) ≤ t ^ 2)
    (hrx : scale j / G.rectangle.x.length ≤ t)
    (hry : scale j / G.rectangle.y.length ≤ t) :
    (∫ p, horizontalEnergy hf w j p ∂G.rectangle.law) ≤ horizontalCoefficient D * t ∧
    (∫ p, verticalEnergy hf w j p ∂G.rectangle.law) ≤
      2 * ε + 16 * C * (D : ℝ) ^ 2 / (widthFactor j : ℝ) + verticalCoefficient D C * t := by
  first
    | exact OAI.DoublingHilbert.anisotropic_energy_bound hf w j hj G hQ hC ht ht1 hfirst hbarrier u v hu hv hnearu hnearv hbaseu hbasev hrx hry
    | exact OAI.DoublingHilbert.anisotropic_energy_bound
    | (apply OAI.DoublingHilbert.anisotropic_energy_bound <;> assumption)
    | (intros; apply OAI.DoublingHilbert.anisotropic_energy_bound <;> assumption)
