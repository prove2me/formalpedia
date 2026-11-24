-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyPosNegJumpSumsIndepV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T13:47:37.489579+00:00
-- url     : https://prove2.me/submissions/ca84dd30-3648-44ef-97e6-d166edc13da7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanIndependentPathsV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyJordanSposSnegEqJumpPlusDriftV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Pos/neg jump-sum path independence from Jordan path independence by subtracting
deterministic drifts supplied by `bvLevyJordanSposSnegEqJumpPlusDriftV1`.
-/

private lemma measurable_sub_linearDrift (c : ℝ) :
    Measurable (fun (f : ℝ≥0 → ℝ) => fun t : ℝ≥0 => f t - c * (t : ℝ)) :=
  measurable_pi_lambda _ fun t => (measurable_pi_apply t).sub measurable_const

private lemma iIndepFun_sub_linearDrifts
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : ℝ≥0 → Ω → ℝ) (cA cB : ℝ)
    (h : iIndepFun
      (fun (i : Fin 2) (ω : Ω) (t : ℝ≥0) => if i = 0 then A t ω else B t ω) P) :
    iIndepFun
      (fun (i : Fin 2) (ω : Ω) (t : ℝ≥0) =>
        if i = 0 then A t ω - cA * (t : ℝ) else B t ω - cB * (t : ℝ)) P := by
  let S : Fin 2 → Ω → (ℝ≥0 → ℝ) := fun i ω t => if i = 0 then A t ω else B t ω
  let φ : Fin 2 → (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) := fun i f t =>
    f t - (if i = 0 then cA else cB) * (t : ℝ)
  have hφ : ∀ i, Measurable (φ i) := fun i => by
    simpa [φ] using measurable_sub_linearDrift (if i = 0 then cA else cB)
  have hcomp : iIndepFun (fun i => φ i ∘ S i) P := h.comp φ hφ
  convert hcomp using 1
  funext i ω t
  by_cases hi : i = 0 <;> simp [hi, φ, S, Function.comp]

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
          X s.1 ω) 0
    ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then Jpos t ω else Jneg t ω) P := by
  dsimp only
  let V : ℝ≥0 → Ω → ℝ := fun t ω =>
    variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
  let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
  let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
  let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (X s.1 ω -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
  let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
        X s.1 ω) 0
  have hS :
      iIndepFun
        (fun (i : Fin 2) (ω : Ω) (t : ℝ≥0) =>
          if i = 0 then Spos t ω else Sneg t ω) P :=
    Kyprianou.Ch02.bvLevyCanonicalJordanIndependentPathsV1 P X hX hBV
  refine Exists.elim
    (Kyprianou.Ch02.bvLevyJordanSposSnegEqJumpPlusDriftV1 P X hX hBV)
    fun dpos hex =>
      Exists.elim hex fun dneg hpack => ?_
  rcases hpack with ⟨_, _, hSpos, hSneg⟩
  have hSdrift :
      iIndepFun
        (fun (i : Fin 2) (ω : Ω) (t : ℝ≥0) =>
          if i = 0 then Spos t ω - dpos * (t : ℝ)
          else Sneg t ω - dneg * (t : ℝ)) P :=
    iIndepFun_sub_linearDrifts P Spos Sneg dpos dneg hS
  have hae :
      ∀ i : Fin 2,
        (fun (ω : Ω) (t : ℝ≥0) =>
            if i = 0 then Spos t ω - dpos * (t : ℝ)
            else Sneg t ω - dneg * (t : ℝ)) =ᵐ[P]
          fun (ω : Ω) (t : ℝ≥0) => if i = 0 then Jpos t ω else Jneg t ω := by
    intro i
    filter_upwards [hSpos, hSneg] with ω hpos hneg
    funext t
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte]
      exact sub_eq_of_eq_add (hpos t)
    · simp only [hi, ↓reduceIte]
      exact sub_eq_of_eq_add (hneg t)
  exact (iIndepFun_congr hae).mp hSdrift
