-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzAffineAEDerivativeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:27:51.753873+00:00
-- url     : https://prove2.me/submissions/2bf13030-a120-41fc-a632-788e687edca0

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ)
    (hPositive : ∀ s ∈ Ioc l r, 0 < U s) :
    ∀ᵐ s ∂volume, s ∈ Ioc l r →
      deriv (fun u : ℝ => f (U u, a + c * u)) s =
        fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
          c * fderiv ℝ f (U s, a + c * s) (0, 1) := by
  let q : ℝ → ℝ × ℝ := fun s => (U s, a + c * s)
  let H : Set (ℝ × ℝ) := Set.prod (Ici (0 : ℝ)) Set.univ
  have hDeriv :
      ∀ᵐ s ∂volume, s ∈ Ioc l r →
        deriv (f ∘ q) s =
          fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
            c * fderiv ℝ f (U s, a + c * s) (0, 1) := by
    filter_upwards [hU.ae_differentiableAt_real] with s hs hsI
    have hPos : 0 < U s := hPositive s hsI
    have hmem : H ∈ 𝓝 (q s) := by
      refine Filter.mem_of_superset
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds
          (show q s ∈ Set.prod (Ioi (0 : ℝ)) Set.univ from
            ⟨hPos, mem_univ _⟩)) ?_
      intro z hz
      exact ⟨show z.1 ∈ Ici (0 : ℝ) from le_of_lt (show 0 < z.1 from hz.1), hz.2⟩
    have hDiff :=
      (hf.differentiableOn_one (q s)
        (show q s ∈ H from ⟨le_of_lt hPos, mem_univ _⟩)).differentiableAt hmem
    have hqDeriv : HasDerivAt q (deriv U s, c) s := by
      simpa [q, id] using hs.hasDerivAt.prodMk
        (((hasDerivAt_id s).const_mul c).const_add a)
    have hFD := hDiff.hasFDerivAt.comp_hasDerivAt s hqDeriv
    have hvec : (deriv U s, c) =
        (deriv U s) • ((1, 0) : ℝ × ℝ) + c • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    calc
      deriv (f ∘ q) s = fderiv ℝ f (q s) (deriv U s, c) := hFD.deriv
      _ = fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
          c * fderiv ℝ f (U s, a + c * s) (0, 1) := by
            simp only [q, hvec, map_add, map_smul, smul_eq_mul]
            ring
  simpa only [q, Function.comp_def] using hDeriv
