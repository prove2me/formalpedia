-- Prove2me | solution 1 for MartOT.Product.plan_determined_by_targets
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:22:18.002093+00:00
-- url     : https://prove2.me/submissions/2aa03c3d-84ab-45ea-9e5f-bc9e8b815fd9

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

theorem solution (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (π π' : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsPlan μ ν π) (hπ' : MartOT.Var.IsPlan μ ν π')
    (h : ∀ t : ℝ, MartOT.Var.targetUpTo π t = MartOT.Var.targetUpTo π' t) :
    π = π' := by
  have hfin : ∀ κ : Measure (ℝ × ℝ), MartOT.Var.IsPlan μ ν κ → IsFiniteMeasure κ := by
    intro κ hκ
    refine ⟨?_⟩
    have : κ Set.univ = μ Set.univ := by
      rw [← hκ.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [this]; exact measure_lt_top μ _
  have := hfin π hπ
  have := hfin π' hπ'
  refine Measure.ext_prod (fun {s} {t} hs ht => ?_)
  let ρ := fun (κ : Measure (ℝ × ℝ)) => (κ.restrict (Set.univ ×ˢ t)).map Prod.fst
  have key : ∀ κ : Measure (ℝ × ℝ), ∀ A, MeasurableSet A → ρ κ A = κ (A ×ˢ t) := by
    intro κ A hA
    simp only [ρ]
    rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
    congr 1; ext ⟨x, y⟩; simp
  have heq : ρ π = ρ π' := by
    refine Measure.ext_of_Iic _ _ (fun a => ?_)
    rw [key _ _ measurableSet_Iic, key _ _ measurableSet_Iic]
    have h2 := congrArg (fun m => m t) (h a)
    simp only [MartOT.Var.targetUpTo] at h2
    rw [Measure.map_apply measurable_snd ht, Measure.map_apply measurable_snd ht,
      Measure.restrict_apply (measurable_snd ht), Measure.restrict_apply (measurable_snd ht)] at h2
    convert h2 using 2 <;> ext ⟨x, y⟩ <;> simp [and_comm]
  rw [← key π s hs, ← key π' s hs, heq]
