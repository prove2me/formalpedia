-- Prove2me | solution 1 for Kyprianou.Ch01.branchingFirstJumpRenewalGivesAncestorConvolution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T13:58:34.062803+00:00
-- url     : https://prove2.me/submissions/ab5b8d51-1ddd-4034-8424-046b9558f052
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingRenewalSolutionUnique
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorPowersSolveRenewal

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

noncomputable def convPow (p : PMF ℕ) : ℕ → PMF ℕ :=
  Nat.rec (PMF.pure 0) (fun _ prev => prev.bind (fun n => p.map (fun m => n + m)))

lemma pmf_map_map {α β γ : Type*} (g : β → γ) (f : α → β) (p : PMF α) :
    (p.map f).map g = p.map (g ∘ f) := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp, PMF.bind_bind]
  refine congrArg (PMF.bind p) ?_
  funext a
  simp [Function.comp, PMF.pure_bind]

lemma conv_assoc (p q r : PMF ℕ) :
    ((p.bind fun n => q.map fun m => n + m).bind fun x => r.map fun y => x + y) =
      p.bind fun n =>
        ((q.bind fun m => r.map fun y => m + y).map fun z => n + z) := by
  rw [PMF.bind_bind]
  refine congrArg (PMF.bind p) ?_
  funext n
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind q) ?_
  funext m
  simp only [Function.comp]
  rw [pmf_map_map]
  have hfun : ((fun z => n + z) ∘ fun y => m + y) = fun y => n + (m + y) := by
    funext y
    rfl
  rw [hfun]
  refine congrArg (fun f => PMF.map f r) ?_
  funext y
  exact Nat.add_assoc n m y

lemma convPow_add (p : PMF ℕ) (a b : ℕ) :
    convPow p (a + b) =
      (convPow p a).bind (fun n => (convPow p b).map (fun m => n + m)) := by
  induction b with
  | zero =>
      rw [Nat.add_zero]
      have h0 : convPow p 0 = PMF.pure 0 := rfl
      rw [h0]
      have hfun :
          (fun n => (PMF.pure (0 : ℕ)).map (fun m => n + m)) = PMF.pure := by
        funext n
        rw [← PMF.bind_pure_comp, PMF.pure_bind]
        simp [Function.comp]
      rw [hfun, PMF.bind_pure]
  | succ b ih =>
      rw [Nat.add_succ]
      have hstep : convPow p (a + b + 1) =
          (convPow p (a + b)).bind (fun x => p.map (fun y => x + y)) := rfl
      rw [hstep, ih]
      have hnext : convPow p (b + 1) =
          (convPow p b).bind (fun m => p.map (fun y => m + y)) := rfl
      rw [hnext]
      exact conv_assoc (convPow p a) (convPow p b) p

theorem solution
    (rate : ℝ) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (K : PopulationLaws)
    (hZero : ∀ t : ℝ≥0, ∀ k : ℕ, K 0 t k = (PMF.pure 0) k)
    (hRenew : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
      IntervalIntegrable
        (fun s : ℝ =>
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) ∧
      (K y t k).toReal =
        (if k = y then Real.exp (-(rate * (y : ℝ) * (t : ℝ))) else 0) +
          ∫ s in (0 : ℝ)..(t : ℝ),
            (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
              ∑' j : ℕ, (offspring j).toReal *
                (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
    (a b : ℕ) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    K (a + b) t k =
      ((K a t).bind (fun n => (K b t).map (fun m => n + m))) k := by
  let C : PopulationLaws := fun y s => convPow (K 1 s) y
  have hC0 : ∀ s : ℝ≥0, C 0 s = PMF.pure 0 := by
    intro s
    rfl
  have hCSucc : ∀ y : ℕ, ∀ s : ℝ≥0,
      C (y + 1) s = (C y s).bind (fun n => (K 1 s).map (fun m => n + m)) := by
    intro y s
    rfl
  have hCRenew :=
    branchingOneAncestorPowersSolveRenewal rate hrate offspring K hZero hRenew
      C hC0 hCSucc
  have hLZero : ∀ s : ℝ≥0, ∀ j : ℕ, C 0 s j = (PMF.pure 0) j := by
    intro s j
    rw [hC0 s]
  have hEq :=
    branchingRenewalSolutionUnique rate hrate offspring K C hZero hLZero hRenew hCRenew
  have hPow : ∀ y : ℕ, K y t = C y t := by
    intro y
    exact PMF.ext fun j => hEq y t ht j
  have hCpow : ∀ y : ℕ, C y t = convPow (K 1 t) y := by
    intro y
    rfl
  rw [hPow (a + b), hCpow (a + b), convPow_add (K 1 t) a b,
    ← hCpow a, ← hCpow b, ← hPow a, ← hPow b]
