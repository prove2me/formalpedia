-- Prove2me | solution 1 for HunterPDE.Compactness.memW0_of_bounded_trace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T20:54:15.820804+00:00
-- url     : https://prove2.me/submissions/006cb53d-95d0-45e4-855d-da309808d748

import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_zeroExtension_of_bounded_trace_eq_zero
import Theorems.Thm_HunterPDE_Sobolev_exists_interior_test_approx_of_supported_halfSpace
import Theorems.Thm_HunterPDE_Compactness_memW_iff_sobolev
import Theorems.Thm_HunterPDE_Compactness_sobolevNorm_restrict_le
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (C : ℝ≥0) (T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hlinear : (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g))
    (hbound : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f))
    (hsmooth : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')))
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW 1 p (upperHalfSpace m) f)
    (hzero : T f =ᵐ[volume] 0) : MemW0 1 p (upperHalfSpace m) f := by
  classical
  have hH : IsOpen (upperHalfSpace m) :=
    isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  let F := (upperHalfSpace m).indicator f
  have hFW : MemW 1 p Set.univ F := by
    intro α hα
    obtain ⟨g, hg, hgp⟩ := hf α hα
    refine ⟨(upperHalfSpace m).indicator g, ?_, ?_⟩
    · exact HunterPDE.Shared.HasWeakDeriv.zeroExtension_of_bounded_trace_eq_zero
        hp hp' C T hlinear hbound hsmooth f hf hzero α (Finset.mem_filter.mp hα).2
        g hg hgp
    · simpa only [Measure.restrict_univ] using
        (memLp_indicator_iff_restrict hH.measurableSet).2 hgp
  have hF : HunterPDE.Sobolev.MemW 1 p Set.univ F :=
    (memW_iff_sobolev Set.univ F).1 hFW
  have hsupport : ∀ᵐ x ∂volume, x ∉ closedUpperHalfSpace m → F x = 0 := by
    apply Filter.Eventually.of_forall
    intro x hx
    change ¬ 0 ≤ x (Fin.last m) at hx
    apply Set.indicator_of_notMem
    intro hpos
    change 0 < x (Fin.last m) at hpos
    exact hx (le_of_lt hpos)
  refine ⟨hf, ?_⟩
  intro ε hε
  obtain ⟨φ, hφ, hφW, happrox⟩ :=
    HunterPDE.Sobolev.exists_interior_test_approx_of_supported_halfSpace
      hp hp' F hF hsupport ε hε
  have hdiff : HunterPDE.Sobolev.MemW 1 p Set.univ (F - φ) := by
    refine ⟨hF.1.sub hφW.1, ?_⟩
    intro α hα
    obtain ⟨u, hu, hup⟩ := hF.2 α hα
    obtain ⟨v, hv, hvp⟩ := hφW.2 α hα
    exact ⟨u - v, hu.sub hv, hup.sub hvp⟩
  have heq : f =ᵐ[volume.restrict (upperHalfSpace m)] F := by
    filter_upwards [ae_restrict_mem hH.measurableSet] with x hx
    exact (Set.indicator_of_mem hx f).symm
  exact ⟨φ, hφ, lt_of_le_of_lt
    (sobolevNorm_restrict_le _ hH _ _ hdiff
      (heq.sub (Filter.Eventually.of_forall fun _ => rfl))) happrox⟩
