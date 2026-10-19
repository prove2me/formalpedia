-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.planeEnergy_hasDerivAt_time
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:51:35.339618+00:00
-- url     : https://prove2.me/submissions/f9b9e5d5-4a2c-4305-9485-94f8759224e9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneTime.lean:L14-L66
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.planeEnergy_hasDerivAt_time. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Theorems.Thm_OAI_TriangularHilbert_Heat_exists_heat_uniform_majorant
import Theorems.Thm_OAI_TriangularHilbert_Heat_finite_variance_bounds
import Theorems.Thm_OAI_TriangularHilbert_Heat_heatEnergy_hasDerivAt_variance
import Theorems.Thm_OAI_TriangularHilbert_Heat_heatPlane_integrable
import Theorems.Thm_OAI_TriangularHilbert_Heat_rowStar_differentiableAt
import Theorems.Thm_OAI_TriangularHilbert_Heat_weight_hasDerivAt_center
import Theorems.Thm_OAI_TriangularHilbert_Heat_weight_hasDerivAt_variance
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_hasFDerivWithinAt

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

theorem traceReal_mul_comm (A B : Matrix ι ι ℂ) : traceReal (A * B) = traceReal (B * A) := by
  unfold traceReal; rw [Matrix.trace_mul_comm]
variable [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem regularize_posDef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 < η) : (regularize P η).PosDef :=
  Matrix.PosDef.posSemidef_add hP (Matrix.PosDef.one.smul hη)

omit [Fintype ι] in
theorem regularize_posSemidef {P : Matrix ι ι ℂ} (hP : P.PosSemidef)
    {η : ℝ} (hη : 0 ≤ η) : (regularize P η).PosSemidef :=
  hP.add (Matrix.PosSemidef.one.smul hη)

theorem continuous_sqrt_matrix {X : Type uX} [TopologicalSpace X]
    {P : X → Matrix ι ι ℂ} (hP : _root_.Continuous P)
    (hn : ∀ x, (P x).PosSemidef) : _root_.Continuous (fun x => CFC.sqrt (P x)) :=
  CFC.continuousOn_sqrt.comp_continuous hP (fun x => (hn x).nonneg)

theorem continuous_energyGram : _root_.Continuous
    (fun R : Matrix ι ι ℂ => energy (Rᴴ * R)) := by
  unfold energy
  exact traceRealCLM.continuous.comp
    ((continuous_star.mul continuous_id).mul
      (continuous_sqrt_matrix (continuous_star.mul continuous_id)
        Matrix.posSemidef_conjTranspose_mul_self))

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma gradient_gram (R D A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceReal (A * (Rᴴ * D + Dᴴ * R)) = 2 * hsReal (R * A) D := by
  have he : traceReal (A * (Dᴴ * R)) = traceReal (A * (Rᴴ * D)) := by
    rw [traceReal_mul_comm, ← traceReal_star (Dᴴ * R * A)]
    simp only [Matrix.conjTranspose_mul, hA.eq, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  simp only [hsReal, Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc,
    mul_add, traceReal_add, he]
  ring

lemma energyGradient_gram (P R D : Matrix ι ι ℂ) :
    energyGradient P (Rᴴ * D + Dᴴ * R) =
      3 * hsReal (R * CFC.sqrt P) D := by
  have hs : (CFC.sqrt P).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  rw [energyGradient_apply, gradient_gram R D (CFC.sqrt P) hs]
  ring

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneChart ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open MatrixEnergy
noncomputable section

lemma chart_continuous (i : Three) : Continuous (fun q : ℝ × (ℝ × ℝ) => chart i q.1 q.2) := by
  unfold chart
  split_ifs <;> fun_prop

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GramDeriv ----
namespace OAI

universe uι uE uF

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter MeasureTheory
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma regularized_energyGram_hasFDerivAt (R : Matrix ι ι ℂ) {η : ℝ} (hη : 0 < η) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => energy (regularize (Xᴴ * X) η))
      (gramGradientAt R (regularize (Rᴴ * R) η)) R := by
  have hg := (((hasFDerivAt_id R (𝕜 := ℝ)).star).mul' (hasFDerivAt_id R)).add_const
    (η • (1 : Matrix ι ι ℂ))
  have hp := regularize_posDef (Matrix.posSemidef_conjTranspose_mul_self R) hη
  have hn : ∀ᶠ X : Matrix ι ι ℂ in 𝓝 R, 0 ≤ regularize (Xᴴ * X) η :=
    Eventually.of_forall fun X =>
      (regularize_posSemidef (Matrix.posSemidef_conjTranspose_mul_self X) hη.le).nonneg
  have hh := (energy_hasFDerivWithinAt hp).comp_hasFDerivAt R hg hn
  convert! hh using 1
  ext D
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, id_eq,
    ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.star_eq_conjTranspose]
  rw [energyGradient_gram, gramGradientAt_apply]

lemma continuousAt_tendstoUniformlyOnFilter {E : Type uE} {F : Type uF} [TopologicalSpace E]
    [UniformSpace F] {H : ℝ × E → F} {x : E}
    (hH : ContinuousAt H (0, x)) :
    TendstoUniformlyOnFilter (fun η y => H (η, y)) (fun y => H (0, y))
      (𝓝[>] 0) (𝓝 x) := by
  apply tendstoUniformlyOnFilter_iff_tendsto.mpr
  have hp : (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x ≤ 𝓝 (0, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have h₂ : Tendsto H ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (H (0, x))) :=
    hH.mono_left hp
  have h₁ : Tendsto (fun p : ℝ × E => H (0, p.2))
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (H (0, x))) :=
    hH.tendsto.comp (tendsto_const_nhds.prodMk_nhds tendsto_snd)
  exact (h₁.prodMk_nhds h₂).mono_right (nhds_le_uniformity _)

lemma continuous_gramRegularization : Continuous
    (fun p : ℝ × Matrix ι ι ℂ => gramRegularization p.1 p.2) := by
  unfold gramRegularization regularize
  fun_prop

lemma gramRegularization_posSemidef (η : ℝ) (R : Matrix ι ι ℂ) :
    (gramRegularization η R).PosSemidef :=
  regularize_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _) (sq_nonneg _)

lemma continuous_regularizedGradient : Continuous
    (fun p : ℝ × Matrix ι ι ℂ => gramGradientAt p.2 (gramRegularization p.1 p.2)) := by
  unfold gramGradientAt
  have hs : Continuous (fun p : ℝ × Matrix ι ι ℂ => CFC.sqrt (gramRegularization p.1 p.2)) :=
    continuous_sqrt_matrix continuous_gramRegularization
      (fun p => gramRegularization_posSemidef p.1 p.2)
  have hr : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      (p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ) := (continuous_snd.mul hs).star
  have hm : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ))
        ((p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ)) :=
    (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ)).continuous.comp hr
  have ht : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      traceRealCLM.comp ((ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ))
        ((p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ))) :=
    (ContinuousLinearMap.compL ℝ (Matrix ι ι ℂ) (Matrix ι ι ℂ) ℝ
      traceRealCLM).continuous.comp hm
  exact ht.const_smul (3 : ℝ)

lemma eventually_regularizedEnergy_deriv (R : Matrix ι ι ℂ) :
    ∀ᶠ p : ℝ × Matrix ι ι ℂ in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 R,
      HasFDerivAt (fun X => energy (gramRegularization p.1 X))
        (gramGradientAt p.2 (gramRegularization p.1 p.2)) p.2 := by
  have hp0 : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
  have hh : ∀ᶠ p : ℝ × Matrix ι ι ℂ in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 R, 0 < p.1 :=
    hp0.prod_inl _
  filter_upwards [hh] with p hp
  exact regularized_energyGram_hasFDerivAt p.2 (sq_pos_of_pos hp)

lemma continuous_regularizedEnergy_single (R : Matrix ι ι ℂ) :
    Continuous (fun η : ℝ => energy (gramRegularization η R)) := by
  have hp : Continuous (fun η : ℝ => gramRegularization η R) := by
    unfold gramRegularization regularize
    fun_prop
  exact traceRealCLM.continuous.comp (hp.mul (continuous_sqrt_matrix hp
    (fun η => gramRegularization_posSemidef η R)))

lemma tendsto_regularizedEnergy (R : Matrix ι ι ℂ) :
    Tendsto (fun η => energy (gramRegularization η R))
      (𝓝[>] 0) (𝓝 (energy (Rᴴ * R))) := by
  have ht := (continuous_regularizedEnergy_single R).tendsto (0 : ℝ)
  rw [gramRegularization_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

theorem energyGram_hasFDerivAt (R : Matrix ι ι ℂ) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => energy (Xᴴ * X))
      (gramGradientAt R (Rᴴ * R)) R := by
  have hh := hasFDerivAt_of_tendstoUniformlyOnFilter (𝕜 := ℝ) (x := R)
    (f := fun (η : ℝ) (X : Matrix ι ι ℂ) => energy (gramRegularization η X))
    (f' := fun (η : ℝ) (X : Matrix ι ι ℂ) => gramGradientAt X (gramRegularization η X))
    (g := fun X : Matrix ι ι ℂ => energy (Xᴴ * X))
    (g' := fun X : Matrix ι ι ℂ => gramGradientAt X (gramRegularization 0 X))
    (continuousAt_tendstoUniformlyOnFilter
      (continuous_regularizedGradient.continuousAt (x := (0, R))))
    (eventually_regularizedEnergy_deriv R)
    (Eventually.of_forall (fun X => tendsto_regularizedEnergy X))
  simpa only [gramRegularization_zero] using hh

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatTime ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uν uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section

lemma hasDerivAt_of_coordinates {ν : Type uν} [Fintype ν] [DecidableEq ν]
    {f : (ν → ℝ) → ℝ} {g : ℝ → ν → ℝ} {g' k : ν → ℝ} {s : ℝ}
    (hf : DifferentiableAt ℝ f (g s)) (hg : HasDerivAt g g' s)
    (hk : ∀ i, HasDerivAt (fun q => f (Function.update (g s) i q)) (k i) (g s i)) :
    HasDerivAt (fun t => f (g t)) (∑ i, g' i * k i) s := by
  let T := fderiv ℝ f (g s)
  have hTi : ∀ i, T (Pi.single i 1) = k i := by
    intro i
    have hfu : HasFDerivAt f T (Function.update (g s) i (g s i)) := by
      simpa only [Function.update_eq_self] using hf.hasFDerivAt
    have hi := hfu.comp_hasDerivAt (g s i)
      ((hasFDerivAt_update (i := i) (g s) (g s i)).hasDerivAt)
    have he : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) : ℝ →L[ℝ] (ν → ℝ)) 1 =
        Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [he] at hi
    exact hi.unique (hk i)
  have hT : T g' = ∑ i, g' i * k i := by
    conv_lhs => rw [← Finset.univ_sum_single g']
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (g' i) = g' i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [he, map_smul, hTi, smul_eq_mul]
  have hd := hf.hasFDerivAt.comp_hasDerivAt s hg
  change HasDerivAt _ (T g') s at hd
  rwa [hT] at hd

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_differentiableAt_variances (h a b : ℝ) (w : Three)
    {σ : Three → ℝ} (hσ : 0 < σ w) :
    DifferentiableAt ℝ (fun τ : Three → ℝ => weight h a b (τ w)) σ := by
  have hap : DifferentiableAt ℝ (fun τ : Three → ℝ => τ w) σ := by
    convert! (ContinuousLinearMap.proj w : (Three → ℝ) →L[ℝ] ℝ).differentiableAt
  have hd := (weight_hasDerivAt_variance h a b (σ w) hσ).differentiableAt.comp σ hap
  exact hd

omit [DecidableEq ι] in
lemma heatArray_differentiableAt_variances (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) (p : Three → ℝ)
    {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    DifferentiableAt ℝ (fun τ => heatArray A h u p τ v) σ := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have hleft := (weight_differentiableAt_variances h (u i) (p v) v (hσ v)).sqrt
    (weight_pos hh (hσ v) (u i) (p v)).ne'
  have hright := (weight_differentiableAt_variances h (u j) (p (v+1)) (v+1) (hσ (v+1))).sqrt
    (weight_pos hh (hσ (v+1)) (u j) (p (v+1))).ne'
  exact ((Complex.ofRealCLM.differentiableAt.comp σ hleft).mul_const (A v i j)).mul
    (Complex.ofRealCLM.differentiableAt.comp σ hright)

lemma heatEnergy_differentiableAt_variances (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) (p : Three → ℝ)
    {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    DifferentiableAt ℝ (fun τ => heatEnergy A h u p τ v) σ := by
  have hd := (energyGram_hasFDerivAt (rowStar (heatArray A h u p σ) v)).differentiableAt.comp σ
    (rowStar_differentiableAt (heatArray_differentiableAt_variances A hh u p hσ) v)
  exact hd

lemma heatEnergy_hasDerivAt_time (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) (v : Three) :
    HasDerivAt (fun t => heatEnergy A h u p (fun w => α w * t) v)
      (∑ w, α w * heatVariance A h u p (fun w => α w * s) v w) s := by
  apply hasDerivAt_of_coordinates (f := fun τ => heatEnergy A h u p τ v)
    (g := fun t w => α w * t) (g' := α)
    (heatEnergy_differentiableAt_variances A hh u p (fun w => mul_pos (hα w) hs) v)
  · apply hasDerivAt_pi.mpr
    intro w
    convert! (hasDerivAt_id s).const_mul (α w) using 1
    simp only [mul_one]
  · exact fun w => heatEnergy_hasDerivAt_variance A hh u p (fun a => mul_pos (hα a) hs) v w

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatContinuous ----
namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma heatArray_differentiableAt_centers (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    (p : Three → ℝ) (v : Three) :
    DifferentiableAt ℝ (fun q => heatArray A h u q σ v) p := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have happ (w : Three) : DifferentiableAt ℝ (fun q : Three → ℝ => q w) p := by
    convert! (ContinuousLinearMap.proj w : (Three → ℝ) →L[ℝ] ℝ).differentiableAt
  have hw (a : Three) (k : ι) : DifferentiableAt ℝ
      (fun q : Three → ℝ => weight h (u k) (q a) (σ a)) p := by
    have hd := (weight_hasDerivAt_center h (u k) (p a) (σ a) (hσ a)).differentiableAt.comp p (happ a)
    exact hd
  have hleft := (hw v i).sqrt (weight_pos hh (hσ v) (u i) (p v)).ne'
  have hright := (hw (v+1) j).sqrt (weight_pos hh (hσ (v+1)) (u j) (p (v+1))).ne'
  exact ((Complex.ofRealCLM.differentiableAt.comp p hleft).mul_const (A v i j)).mul
    (Complex.ofRealCLM.differentiableAt.comp p hright)

lemma continuous_heatRow (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    Continuous (fun p => rowStar (heatArray A h u p σ) v) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (rowStar_differentiableAt (heatArray_differentiableAt_centers A hh u hσ p) v).continuousAt

lemma continuous_heatEnergy (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    Continuous (fun p => heatEnergy A h u p σ v) := by
  exact continuous_energyGram.comp (continuous_heatRow A hh u hσ v)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneIntegral ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma measurable_chart (i : Three) (d : ℝ) : Measurable (chart i d) :=
  ((chart_continuous i).comp (continuous_const.prodMk continuous_id)).measurable

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneTime ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma planeEnergy_hasDerivAt_time (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) (v : Three) :
    HasDerivAt (fun t => planeIntegral (fun p => heatEnergy A h u p (fun w => α w*t) v) d)
      (∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d) s := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds α hα
  have hb : 0 < b := ha.trans_le hab
  have has : 0 < a*(s/2) := mul_pos ha (by linarith)
  have habs : a*(s/2) ≤ b*(2*s) := by gcongr; linarith
  obtain ⟨B,hB,hBn,hbound⟩ := exists_heat_uniform_majorant A hh has habs (abs_nonneg d) u
  let C := ∑ w, α w
  have hC : 0 ≤ C := Finset.sum_nonneg (fun w _ => (hα w).le)
  have hσ : ∀ w, 0 < α w*s := fun w => mul_pos (hα w) hs
  have hint := (heatPlane_integrable A hh u d hσ).energy 2 v
  have hvar := (heatPlane_integrable A hh u d hσ).variance 2 v
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*s) v w) := by
    exact (Finset.aestronglyMeasurable_fun_sum Finset.univ (fun w _ =>
        (hvar w).aestronglyMeasurable.const_mul (α w)))
  have hboundσ (t : ℝ) (ht : t ∈ Set.Ioo (s/2) (2*s)) :
      (∀ w, a*(s/2) ≤ α w*t) ∧ (∀ w, α w*t ≤ b*(2*s)) := by
    have ht0 : 0 < t := (by linarith : 0 < s/2).trans ht.1
    constructor
    · intro w; exact mul_le_mul (hla w) ht.1.le (by linarith) (hα w).le
    · intro w; exact mul_le_mul (hlb w) ht.2.le ht0.le hb.le
  have hn : Set.Ioo (s/2) (2*s) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hfmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (fun z : ℝ × ℝ => heatEnergy A h u (chart 2 d z) (fun w => α w*t) v) := by
    filter_upwards [hn] with t ht
    have ht0 : 0 < t := (by linarith : 0 < s/2).trans ht.1
    exact ((continuous_heatEnergy A hh u (fun w => mul_pos (hα w) ht0) v).measurable.comp
      (measurable_chart 2 d)).aestronglyMeasurable
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z => heatEnergy A h u (chart 2 d z) (fun w => α w*t) v)
    (F' := fun t z => ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*t) v w)
    (bound := fun z => C*B z) hn hfmeas hint hmeas
    (Eventually.of_forall (fun z t ht => by
      calc
        _ ≤ ∑ w, ‖α w * heatVariance A h u (chart 2 d z) (fun a => α a*t) v w‖ := norm_sum_le _ _
        _ ≤ ∑ w, α w * B z := by
          apply Finset.sum_le_sum
          intro w _
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hα w)]
          exact mul_le_mul_of_nonneg_left
            ((hbound 2 d z (le_refl _) _ (hboundσ t ht).1 (hboundσ t ht).2).variance v w) (hα w).le
        _ = C*B z := (Finset.sum_mul _ _ _).symm))
    (hB.const_mul C)
    (Eventually.of_forall (fun z t ht => heatEnergy_hasDerivAt_time A hh u (chart 2 d z) α hα
      ((by linarith : 0 < s/2).trans ht.1) v))).2
  have he : (∫ z : ℝ × ℝ, ∑ w, α w * heatVariance A h u (chart 2 d z) (fun a => α a*s) v w) =
      ∑ w, α w * planeIntegral (fun p => heatVariance A h u p (fun a => α a*s) v w) d := by
    rw [integral_finsetSum _ (fun w _ => (hvar w).const_mul (α w))]
    simp only [integral_const_mul, planeIntegral]
  rw [he] at hder
  exact hder

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.planeEnergy_hasDerivAt_time.{uι} := @_root_.OAI.TriangularHilbert.Heat.planeEnergy_hasDerivAt_time.{uι}
