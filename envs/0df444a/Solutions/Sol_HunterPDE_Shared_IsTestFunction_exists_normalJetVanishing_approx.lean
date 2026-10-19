-- Prove2me | solution 1 for HunterPDE.Shared.IsTestFunction.exists_normalJetVanishing_approx
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T15:28:08.074187+00:00
-- url     : https://prove2.me/submissions/4f7e670f-3ad9-4e9f-90b6-2294e018bc05

import Theorems.Thm_HunterPDE_Shared_uniform_normalCutoff_multiDeriv_bound
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory Filter HunterPDE.Shared
open scoped Topology ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} (i : Fin n) (α : Fin n → ℕ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : IsTestFunction Set.univ ψ)
    (hb : ∀ r : ℕ, r < α i → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0) :
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∃ φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
          (∀ j, IsTestFunction {x | 0 < x i} (φ j)) ∧
          (∀ j x, ‖φ j x‖ ≤ K.indicator (fun _ => C) x ∧
            ‖multiDeriv (φ j) α x‖ ≤ K.indicator (fun _ => C) x) ∧
          (∀ x : EuclideanSpace ℝ (Fin n), 0 < x i →
            Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)) ∧
            Tendsto (fun j => multiDeriv (φ j) α x) atTop (𝓝 (multiDeriv ψ α x))) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let t : E →L[ℝ] ℝ := EuclideanSpace.proj i
  let q : ℝ → ℝ := fun s => Real.smoothTransition (s - 1)
  have hq : ContDiff ℝ ∞ q :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hlo (s : ℝ) (hs : s ≤ 1) : q s = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hhi (s : ℝ) (hs : 2 ≤ s) : q s = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  obtain ⟨B, hB, hbound⟩ := uniform_normalCutoff_multiDeriv_bound
    i α ψ hψ.1 hψ.2.1 hb q hq hlo hhi
  obtain ⟨A₀, hA₀⟩ := hψ.2.1.exists_bound_of_continuous hψ.1.continuous
  let A := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hval (x : E) : ‖ψ x‖ ≤ A := (hA₀ x).trans (le_max_left _ _)
  let a : ℕ → ℝ := fun j => (j : ℝ) + 1
  have ha (j : ℕ) : 1 ≤ a j := by
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hapos (j : ℕ) : 0 < a j := lt_of_lt_of_le zero_lt_one (ha j)
  let φ : ℕ → E → ℝ := fun j x => q (a j * t x) * ψ x
  have hsmooth (j : ℕ) : ContDiff ℝ ∞ (φ j) :=
    (hq.comp (contDiff_const.mul t.contDiff)).mul hψ.1
  have hcompact (j : ℕ) : HasCompactSupport (φ j) := hψ.2.1.mul_left
  have hsupport (j : ℕ) : tsupport (φ j) ⊆ tsupport ψ := tsupport_mul_subset_right
  have hinterior (j : ℕ) : tsupport (φ j) ⊆ {x : E | 0 < x i} := by
    have hclosed : IsClosed {x : E | 1 ≤ a j * t x} :=
      isClosed_le continuous_const (continuous_const.mul t.continuous)
    have hin : tsupport (φ j) ⊆ {x : E | 1 ≤ a j * t x} := by
      apply closure_minimal _ hclosed
      intro x hx
      change 1 ≤ a j * t x
      by_contra hh
      have hz : q (a j * t x) = 0 := hlo _ (le_of_not_ge hh)
      exact hx (by simp [φ, hz])
    intro x hx
    have hh := hin hx
    change 1 ≤ a j * t x at hh
    change 0 < t x
    nlinarith [hapos j]
  -- Locality of iterated partials needs no smoothness assumptions.
  have hlocal : ∀ (l : List (Fin n)) (f g : E → ℝ) (x : E),
      f =ᶠ[𝓝 x] g → iteratedPartial f l =ᶠ[𝓝 x] iteratedPartial g l := by
    intro l
    induction l with
    | nil => intro f g x h; exact h
    | cons k l ih =>
      intro f g x h
      have hd := (ih f g x h).fderiv (𝕜 := ℝ)
      exact hd.mono (fun y hy => congrArg (fun L => L (EuclideanSpace.single k 1)) hy)
  have hsuppder : ∀ (l : List (Fin n)) (f : E → ℝ),
      tsupport (iteratedPartial f l) ⊆ tsupport f := by
    intro l
    induction l with
    | nil => intro f; exact Set.Subset.rfl
    | cons k l ih =>
      intro f
      exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single k 1)).trans (ih f)
  let C := A + B
  have hC : 0 ≤ C := add_nonneg hA hB
  have hφval (j : ℕ) (x : E) : ‖φ j x‖ ≤ C := by
    have hqb : ‖q (a j * t x)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    calc
      ‖φ j x‖ = ‖q (a j * t x)‖ * ‖ψ x‖ := norm_mul _ _
      _ ≤ 1 * A := mul_le_mul hqb (hval x) (norm_nonneg _) zero_le_one
      _ ≤ C := by dsimp [C]; linarith
  have hφder (j : ℕ) (x : E) : ‖multiDeriv (φ j) α x‖ ≤ C :=
    (hbound (a j) (ha j) x).trans (by dsimp [C]; linarith)
  refine ⟨tsupport ψ, hψ.2.1, C, hC, φ, ?_, ?_, ?_⟩
  · intro j; exact ⟨hsmooth j, hcompact j, hinterior j⟩
  · intro j x
    by_cases hx : x ∈ tsupport ψ
    · simp only [Set.indicator_of_mem hx]
      exact ⟨hφval j x, hφder j x⟩
    · have hv : φ j x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hsupport j hh))
      have hd : multiDeriv (φ j) α x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hh => hx (hsupport j (hsuppder (multiIndexList α) (φ j) hh)))
      simp [Set.indicator_of_notMem hx, hv, hd]
  · intro x hx
    have he : ∀ᶠ j : ℕ in atTop, 2 < a j * t x := by
      have htend : Tendsto (fun j : ℕ => a j * t x) atTop atTop :=
        (tendsto_atTop_add_const_right atTop 1
          (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_mul_const hx
      exact htend.eventually (eventually_gt_atTop 2)
    have hnear (j : ℕ) (hj : 2 < a j * t x) : φ j =ᶠ[𝓝 x] ψ := by
      have hh : ∀ᶠ y in 𝓝 x, 2 < a j * t y :=
        (isOpen_lt continuous_const (continuous_const.mul t.continuous)).mem_nhds hj
      filter_upwards [hh] with y hy
      simp [φ, hhi _ hy.le]
    have hev : (fun j => φ j x) =ᶠ[atTop] (fun _ => ψ x) :=
      he.mono (fun j hj => (hnear j hj).eq_of_nhds)
    have hed : (fun j => multiDeriv (φ j) α x) =ᶠ[atTop]
        (fun _ => multiDeriv ψ α x) :=
      he.mono (fun j hj => (hlocal (multiIndexList α) (φ j) ψ x (hnear j hj)).eq_of_nhds)
    exact ⟨tendsto_const_nhds.congr' hev.symm, tendsto_const_nhds.congr' hed.symm⟩
