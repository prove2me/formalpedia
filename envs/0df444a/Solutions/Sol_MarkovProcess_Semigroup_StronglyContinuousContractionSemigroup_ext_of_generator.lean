-- Prove2me | solution 1 for MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.ext_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:15:45.543987+00:00
-- url     : https://prove2.me/submissions/c7ab7e15-c970-4615-b8f2-9938350e2853

import Definitions.Def_MarkovProcess_V3H_Semigroup_GeneratorUniqueness_43727223
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The generator determines the semigroup

Two strongly continuous contraction semigroups with the same generator domain and the same
generator on it are equal (`ext_of_generator`).

The proof interpolates between the two evolutions: for a vector `f` of the common domain and a
fixed time `t`, the path `s ↦ S (t - s) (T s f)` on `[0, t]` is continuous and has right
derivative zero, because

`S (t - s - h) (T (s + h) f) - S (t - s) (T s f)
    = S (t - s - h) ((T h - 1) (T s f) - (S h - 1) (T s f))`,

and the two difference quotients on the right converge to the common value of the generators at
`T s f`.  Grönwall's inequality then makes the path constant, and its two endpoints are `S t f`
and `T t f`.  Density of the generator domain extends the identity to the whole space.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S T : StronglyContinuousContractionSemigroup E)

/-- The interpolation `s ↦ S (t - s) (T s f)` between the orbit of `f` under `T` and its orbit
under `S`, read at real times. -/
private def transferOrbit (f : E) (t s : ℝ) : E :=
  S (Real.toNNReal (t - s)) (T (Real.toNNReal s) f)

private theorem transferOrbit_apply (f : E) (t s : ℝ) :
    S.transferOrbit T f t s = S (Real.toNNReal (t - s)) (T (Real.toNNReal s) f) := rfl

private theorem continuous_transferOrbit (f : E) (t : ℝ) :
    Continuous (S.transferOrbit T f t) :=
  S.continuous_operator_apply
    (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
    (T.continuous_operator_toNNReal f)

private theorem transferOrbit_zero (f : E) (t : ℝ) :
    S.transferOrbit T f t 0 = S (Real.toNNReal t) f := by
  rw [transferOrbit_apply, sub_zero, Real.toNNReal_zero, T.zero_apply]

private theorem transferOrbit_self (f : E) (t : ℝ) :
    S.transferOrbit T f t t = T (Real.toNNReal t) f := by
  rw [transferOrbit_apply, sub_self, Real.toNNReal_zero, S.zero_apply]

/-- The interpolation has vanishing right derivative at every time of `[0, t)`. -/
private theorem hasDerivWithinAt_transferOrbit
    (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩)
    {f : E} (hf : f ∈ S.generatorDomain) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (S.transferOrbit T f t) 0 (Ici s) s := by
  have hfT : f ∈ T.generatorDomain := by rwa [← hdom]
  have hgT : T (Real.toNNReal s) f ∈ T.generatorDomain :=
    T.operator_mem_generatorDomain ⟨f, hfT⟩ (Real.toNNReal s)
  have hgS : T (Real.toNNReal s) f ∈ S.generatorDomain := by rwa [hdom]
  have hto : Tendsto (fun y : ℝ ↦ Real.toNNReal (y - s)) (𝓝[>] s) (𝓝[>] 0) := by
    have h := tendsto_toNNReal_sub (Real.toNNReal s)
    rwa [Real.coe_toNNReal s hs] at h
  have hbound : Tendsto (fun y : ℝ ↦
      ‖T.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s)) -
        S.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s))‖)
      (𝓝[>] s) (𝓝 0) := by
    have hT' := (T.tendsto_generator ⟨T (Real.toNNReal s) f, hgT⟩).comp hto
    have hS' := (S.tendsto_generator ⟨T (Real.toNNReal s) f, hgS⟩).comp hto
    have hdiff := hT'.sub hS'
    rw [← hgen _ hgS hgT, sub_self] at hdiff
    simpa using hdiff.norm
  have hslope : ∀ y ∈ Ioo s t, slope (S.transferOrbit T f t) s y =
      S (Real.toNNReal (t - y))
        (T.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s)) -
          S.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s))) := by
    intro y hy
    have hsy : (0 : ℝ) ≤ y - s := sub_nonneg.mpr hy.1.le
    have hcoe : ((Real.toNNReal (y - s) : NNReal) : ℝ) = y - s := Real.coe_toNNReal _ hsy
    have hy0 : (0 : ℝ) ≤ y := hs.trans hy.1.le
    have hsplit : Real.toNNReal y = Real.toNNReal (y - s) + Real.toNNReal s := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, hcoe, Real.coe_toNNReal s hs, Real.coe_toNNReal y hy0]
      ring
    have hwindow : Real.toNNReal (t - s) = Real.toNNReal (t - y) + Real.toNNReal (y - s) := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, hcoe, Real.coe_toNNReal _ (sub_nonneg.mpr hy.2.le),
        Real.coe_toNNReal _ (sub_nonneg.mpr (hy.1.trans hy.2).le)]
      ring
    have key : S.transferOrbit T f t y - S.transferOrbit T f t s =
        S (Real.toNNReal (t - y))
          (T (Real.toNNReal (y - s)) (T (Real.toNNReal s) f) -
            S (Real.toNNReal (y - s)) (T (Real.toNNReal s) f)) := by
      rw [transferOrbit_apply, transferOrbit_apply, hsplit, T.add_apply, hwindow, S.add_apply,
        ← map_sub]
    rw [slope_def_module, key, T.differenceQuotient_apply, S.differenceQuotient_apply, hcoe,
      ← smul_sub, map_smul, sub_sub_sub_cancel_right]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Ici s \ {s} = Ioi s := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun hy ↦ lt_of_le_of_ne hy.1 (Ne.symm hy.2), fun hy ↦ ⟨hy.le, hy.ne'⟩⟩
  rw [hdiff]
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Ioo_mem_nhdsGT hst] with y hy
  rw [hslope y hy]
  exact S.norm_apply_le _ _

variable [CompleteSpace E]



end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The generator determines the semigroup

Two strongly continuous contraction semigroups with the same generator domain and the same
generator on it are equal (`ext_of_generator`).

The proof interpolates between the two evolutions: for a vector `f` of the common domain and a
fixed time `t`, the path `s ↦ S (t - s) (T s f)` on `[0, t]` is continuous and has right
derivative zero, because

`S (t - s - h) (T (s + h) f) - S (t - s) (T s f)
    = S (t - s - h) ((T h - 1) (T s f) - (S h - 1) (T s f))`,

and the two difference quotients on the right converge to the common value of the generators at
`T s f`.  Grönwall's inequality then makes the path constant, and its two endpoints are `S t f`
and `T t f`.  Density of the generator domain extends the identity to the whole space.
-/

open Filter Set Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S T : StronglyContinuousContractionSemigroup E)













variable [CompleteSpace E]

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
theorem solution (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩) :
    S = T := by
  have hcore : ∀ (t : NNReal) (f : E), f ∈ S.generatorDomain → S t f = T t f := by
    intro t f hf
    have hconst := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := fun s ↦ S.transferOrbit T f t s - S.transferOrbit T f t 0)
      (f' := fun _ ↦ (0 : E)) (K := 0) (a := 0) (b := (t : ℝ))
      (((S.continuous_transferOrbit T f t).sub continuous_const).continuousOn)
      (fun s hs ↦
        (S.hasDerivWithinAt_transferOrbit T hdom hgen hf hs.1 hs.2).sub_const _)
      (sub_self _)
      (fun s _ ↦ by rw [norm_zero, zero_mul])
      (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
    rw [sub_eq_zero, transferOrbit_self, transferOrbit_zero, Real.toNNReal_coe] at hconst
    exact hconst.symm
  refine StronglyContinuousContractionSemigroup.ext fun t ↦ ?_
  refine DFunLike.coe_injective ?_
  refine Continuous.ext_on S.dense_generatorDomain (S t).continuous (T t).continuous ?_
  intro f hf
  exact hcore t f hf
