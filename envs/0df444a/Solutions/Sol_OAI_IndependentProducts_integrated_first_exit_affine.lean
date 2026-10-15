-- Prove2me | solution 1 for OAI.IndependentProducts.integrated_first_exit_affine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:24:02.006858+00:00
-- url     : https://prove2.me/submissions/da230e18-d700-4a6f-a31e-c63ca0f78845

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ConditionalBounds.lean:L124-L173
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.integrated_first_exit_affine. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Theorems.Thm_OAI_IndependentProducts_signed_first_moment

-- ---- from OAI.Analysis.ProductSpaces.GaussianMoments ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section WeightedMoments
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}

variable [IsProbabilityMeasure P]

end WeightedMoments
section GaussianVector
variable {ι : Type uι} [Fintype ι]

end GaussianVector
end IndependentProducts

namespace IndependentProducts

lemma integrable_excess {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable X P) (t r : ℝ) :
    Integrable (fun ω => excess t r (X ω)) P :=
  ((hX.abs.const_mul t).sub (integrable_const r)).sup (integrable_const 0)

end IndependentProducts

namespace IndependentProducts

section GaussianFinite
variable {ι : Type uι} [Fintype ι]

end GaussianFinite
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.RandomSigns ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

lemma euclidSize_nonneg {ι : Type uι} [Fintype ι] (a : ι → ℝ) : 0 ≤ euclidSize a := Real.sqrt_nonneg _

lemma euclidSize_sq {ι : Type uι} [Fintype ι] (a : ι → ℝ) : euclidSize a ^ 2 = ∑ i, a i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma euclidSize_le_sum_abs {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    euclidSize a ≤ ∑ i, |a i| := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (a i))
  simp only [sq_abs] at h
  have hsum : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [euclidSize_sq a, euclidSize_nonneg a]

lemma integrable_euclidSize {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun ω => euclidSize (fun i => X i ω)) P := by
  apply Integrable.mono' (integrable_finsetSum _ (fun i _ => (hX i).abs))
  · unfold euclidSize
    fun_prop
  · exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (euclidSize_nonneg _)]
      exact euclidSize_le_sum_abs _)

section SignVector
variable {ι : Type uι} [Fintype ι]

end SignVector
end IndependentProducts

namespace IndependentProducts
section Symmetrization
variable {ι : Type uι} [Fintype ι]

end Symmetrization
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.ConditionalBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΛ uΩ uι

namespace IndependentProducts
section ConditionalScalar
variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω)
variable (hμ : MemLp (fun w : ℝ => w) 2 μ)

variable [IsProbabilityMeasure ν]

include hμ in
lemma integrable_firstExitSum (B : ι → Ω → ℝ) (hB : ∀ i, Integrable (B i) ν)
    (hBm : ∀ i, Measurable (B i)) :
    Integrable (firstExitSum ν B) ((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))) := by
  apply integrable_finsetSum
  intro i hi
  have hb : Integrable (fun b : ι → Ω => B i (b i)) (Measure.pi (fun _ : ι => ν)) :=
    (measurePreserving_eval (fun _ : ι => ν) i).integrable_comp (hBm i).aestronglyMeasurable |>.mpr (hB i)
  have hw : Integrable (fun w : ι → ℝ => w i) (Measure.pi (fun _ : ι => μ)) :=
    (hμ.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)).integrable (by norm_num)
  exact (hb.mul_prod hw).sub (integrable_const _)

include hμ in
lemma first_exit_scalar_bound (B : ι → Ω → ℝ) (hB : ∀ i, Integrable (B i) ν)
    (hBm : ∀ i, Measurable (B i)) (t A D r : ℝ)
    (hscalar : ∀ a : ι → ℝ, ∀ b : ℝ,
      A * euclidSize a - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, a i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    A * (∫ b : ι → Ω, euclidSize (fun i => B i (b i)) ∂Measure.pi (fun _ : ι => ν)) - D * r ≤
      ∫ z : (ι → Ω) × (ι → ℝ), excess t r (firstExitSum ν B z)
        ∂(Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ)) := by
  let Pb := Measure.pi (fun _ : ι => ν)
  let Pw := Measure.pi (fun _ : ι => μ)
  have hB' : ∀ i, Integrable (fun b : ι → Ω => B i (b i)) Pb := fun i =>
    (measurePreserving_eval (fun _ : ι => ν) i).integrable_comp (hBm i).aestronglyMeasurable |>.mpr (hB i)
  have hs := integrable_euclidSize (fun i (b : ι → Ω) => B i (b i)) hB'
  have hp := integrable_excess (integrable_firstExitSum μ ν hμ B hB hBm) t r
  rw [integral_prod _ hp]
  calc
    _ = ∫ b : ι → Ω, (A * euclidSize (fun i => B i (b i)) - D * r) ∂Pb := by
      rw [integral_sub (hs.const_mul _) (integrable_const _), integral_const_mul, integral_const]
      simp [Pb]
    _ ≤ _ := by
      apply integral_mono ((hs.const_mul _).sub (integrable_const _)) hp.integral_prod_left
      intro b
      have he : ∀ w : ι → ℝ, firstExitSum ν B (b, w) =
          -(∑ i, ∫ u, B i u ∂ν) + ∑ i, B i (b i) * w i := by
        intro w
        simp only [firstExitSum, Finset.sum_sub_distrib]
        ring
      simp_rw [he]
      exact hscalar (fun i => B i (b i)) _

end ConditionalScalar

end IndependentProducts

namespace IndependentProducts
section IntegratedConditional
variable {ι : Type uι} {Ω : Type uΩ} {Λ : Type uΛ}
  [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Λ]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (η : Measure Λ) [IsProbabilityMeasure η]

lemma integrated_first_exit_affine
    (hμ : MemLp (fun w : ℝ => w) 2 μ) (hmean : ∫ w : ℝ, w ∂μ = 1)
    (B : Λ → ι → Ω → ℝ) (hB : ∀ old i, Integrable (B old i) ν)
    (hBm : ∀ old i, Measurable (B old i))
    (U : Λ → ℝ) (hU : Integrable U η)
    (hS : Integrable (fun z : (ι → Ω) × Λ => euclidSize (fun i => B z.2 i (z.1 i)))
      ((Measure.pi (fun _ : ι => ν)).prod η))
    (hY : Integrable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ => firstExitSum ν (B z.2) z.1)
      (((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η))
    (t A D : ℝ) (hA : 0 ≤ A) (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ a : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize a - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, a i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) *
      (∫ z : ((ι → Ω) × (ι → ℝ)) × Λ, |firstExitSum ν (B z.2) z.1|
        ∂((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η) -
      D * (∫ old, |U old| ∂η) ≤
      ∫ z : ((ι → Ω) × (ι → ℝ)) × Λ, excess t |U z.2| (firstExitSum ν (B z.2) z.1)
        ∂((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η := by
  let Pb := Measure.pi (fun _ : ι => ν)
  let Pw := Measure.pi (fun _ : ι => μ)
  let C := 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ)
  let S : Λ → ℝ := fun old => ∫ b : ι → Ω, euclidSize (fun i => B old i (b i)) ∂Pb
  have hs : Integrable S η := hS.integral_prod_right
  have hphi : Integrable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ =>
      excess t |U z.2| (firstExitSum ν (B z.2) z.1)) ((Pb.prod Pw).prod η) :=
    ((hY.abs.const_mul t).sub (hU.abs.comp_snd (Pb.prod Pw))).sup (integrable_const 0)
  rw [integral_prod_symm _ hY.abs, integral_prod_symm _ hphi]
  have hn : (∫ old, ∫ z : (ι → Ω) × (ι → ℝ), |firstExitSum ν (B old) z| ∂Pb.prod Pw ∂η) ≤
      C * ∫ old, S old ∂η := by
    rw [← integral_const_mul]
    apply integral_mono hY.abs.integral_prod_right (hs.const_mul C)
    intro old
    exact signed_first_moment μ hμ hmean (fun _ : ι => ν) (B old) (hB old) (hBm old)
  have hg : A * (∫ old, S old ∂η) - D * (∫ old, |U old| ∂η) ≤
      ∫ old, ∫ z : (ι → Ω) × (ι → ℝ), excess t |U old| (firstExitSum ν (B old) z) ∂Pb.prod Pw ∂η := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hs.const_mul A) (hU.abs.const_mul D)]
    apply integral_mono ((hs.const_mul A).sub (hU.abs.const_mul D)) hphi.integral_prod_right
    intro old
    exact first_exit_scalar_bound μ ν hμ (B old) (hB old) (hBm old) t A D |U old|
      (fun a b => hscalar a b |U old| (abs_nonneg _))
  have hd : (∫ old, ∫ z : (ι → Ω) × (ι → ℝ), |firstExitSum ν (B old) z| ∂Pb.prod Pw ∂η) / C ≤
      ∫ old, S old ∂η := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hn)
  have hh := mul_le_mul_of_nonneg_left hd hA
  change A / C * _ - D * _ ≤ _
  calc
    _ = A * ((∫ old, ∫ z : (ι → Ω) × (ι → ℝ), |firstExitSum ν (B old) z| ∂Pb.prod Pw ∂η) / C) -
        D * (∫ old, |U old| ∂η) := by ring
    _ ≤ A * (∫ old, S old ∂η) - D * (∫ old, |U old| ∂η) := sub_le_sub_right hh _
    _ ≤ _ := hg

end IntegratedConditional
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΛ uΩ uι
variable {ι : Type uι} {Ω : Type uΩ} {Λ : Type uΛ}
  [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Λ]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (η : Measure Λ) [IsProbabilityMeasure η]

theorem solution
    (hμ : MemLp (fun w : ℝ => w) 2 μ) (hmean : ∫ w : ℝ, w ∂μ = 1)
    (B : Λ → ι → Ω → ℝ) (hB : ∀ old i, Integrable (B old i) ν)
    (hBm : ∀ old i, Measurable (B old i))
    (U : Λ → ℝ) (hU : Integrable U η)
    (hS : Integrable (fun z : (ι → Ω) × Λ => euclidSize (fun i => B z.2 i (z.1 i)))
      ((Measure.pi (fun _ : ι => ν)).prod η))
    (hY : Integrable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ => firstExitSum ν (B z.2) z.1)
      (((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η))
    (t A D : ℝ) (hA : 0 ≤ A) (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ a : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize a - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, a i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) *
      (∫ z : ((ι → Ω) × (ι → ℝ)) × Λ, |firstExitSum ν (B z.2) z.1|
        ∂((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η) -
      D * (∫ old, |U old| ∂η) ≤
      ∫ z : ((ι → Ω) × (ι → ℝ)) × Λ, excess t |U z.2| (firstExitSum ν (B z.2) z.1)
        ∂((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η := by
  first
    | exact OAI.IndependentProducts.integrated_first_exit_affine hμ hmean B hB hBm U hU hS hY t A D hA hC hscalar
    | exact OAI.IndependentProducts.integrated_first_exit_affine μ ν η hμ hmean B hB hBm U hU hS hY t A D hA hC hscalar
    | exact OAI.IndependentProducts.integrated_first_exit_affine
    | (apply OAI.IndependentProducts.integrated_first_exit_affine <;> assumption)
    | (intros; apply OAI.IndependentProducts.integrated_first_exit_affine <;> assumption)
