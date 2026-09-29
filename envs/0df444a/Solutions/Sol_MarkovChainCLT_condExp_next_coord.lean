-- Prove2me | solution 1 for MarkovChainCLT.condExp_next_coord
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T23:15:47.480271+00:00
-- url     : https://prove2.me/submissions/ca0439ec-ade7-4ed4-bb7a-9413666e60f0

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Theorems.Thm_MarkovChainCLT_setIntegral_next_coord_eq
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (h : X → ℝ) (hh : Measurable h) (B : ℝ) (hB : ∀ x, |h x| ≤ B) (k : ℕ) :
    (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k)))
      =ᵐ[chainMeasure P lam] (chainMeasure P lam)[fun ω : ℕ → X => h (ω (k + 1)) |
        MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k) inferInstance] := by
  classical
  have hmle : MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k) inferInstance
      ≤ (inferInstance : MeasurableSpace (ℕ → X)) := (measurable_frestrictLe k).comap_le
  haveI : IsFiniteMeasure ((chainMeasure P lam).trim hmle) := isFiniteMeasure_trim hmle
  have hhs : StronglyMeasurable h := hh.stronglyMeasurable
  have hfmeas : Measurable (fun ω : ℕ → X => h (ω (k + 1))) :=
    hh.comp (measurable_pi_apply (k + 1))
  have hgmeas : Measurable (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k))) :=
    (hhs.integral_kernel (κ := P)).measurable.comp (measurable_pi_apply k)
  have hgB : ∀ ω : ℕ → X, |∫ y, h y ∂(P (ω k))| ≤ B := by
    intro ω
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun y => |h y|) (P (ω k)) :=
      ⟨(continuous_abs.measurable.comp hh).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun z => by simpa using hB z))⟩
    have h2 := integral_mono h1 (integrable_const B) (fun z => hB z)
    simpa using h2
  have hfint : Integrable (fun ω : ℕ → X => h (ω (k + 1))) (chainMeasure P lam) :=
    ⟨hfmeas.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun ω => by simpa using hB _))⟩
  have hgint : Integrable (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k))) (chainMeasure P lam) :=
    ⟨hgmeas.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := B) (ae_of_all _ (fun ω => by simpa using hgB ω))⟩
  -- `g` is measurable with respect to the past
  have hco : Measurable[MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k)
      inferInstance] (fun ω : ℕ → X => ω k) := by
    have h1 : Measurable[MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k)
        inferInstance] (frestrictLe (π := fun _ : ℕ => X) k) := Measurable.of_comap_le le_rfl
    have h2 := (measurable_pi_apply (⟨k, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic k)).comp h1
    exact h2
  have hgm : StronglyMeasurable[MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]
      (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k))) :=
    (Measurable.comp (hhs.integral_kernel (κ := P)).measurable hco).stronglyMeasurable
  refine ae_eq_condExp_of_forall_setIntegral_eq hmle hfint
    (fun s _ _ => hgint.integrableOn) (fun s hs _ => ?_) hgm.aestronglyMeasurable
  obtain ⟨A₀, hA₀, rfl⟩ := hs
  exact (setIntegral_next_coord_eq P lam h hh B hB k A₀ hA₀).symm
