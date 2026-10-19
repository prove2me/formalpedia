-- Prove2me | solution 1 for HunterPDE.Compactness.exists_global_testFunction_halfSpace_approx
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T22:11:16.399985+00:00
-- url     : https://prove2.me/submissions/7c5d538e-71de-4418-912b-9080b0ac252e

import Theorems.Thm_HunterPDE_Compactness_exists_sobolev_extension_halfSpace
import Theorems.Thm_HunterPDE_Compactness_sobolevNorm_restrict_le
import Theorems.Thm_HunterPDE_Sobolev_smooth_approximation
import Theorems.Thm_HunterPDE_Sobolev_smooth_compact_cutoff_approximation
import Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_sub_triangle
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Theorems.Thm_HunterPDE_Compactness_memW_iff_sobolev
import Theorems.Thm_HunterPDE_Sobolev_memW_of_isTestFunction
import Theorems.Thm_HunterPDE_Sobolev_IsTestFunction_iteratedPartial

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal
set_option autoImplicit false

theorem solution (m k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW k p (upperHalfSpace m) f)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, HunterPDE.Shared.IsTestFunction Set.univ φ ∧ MemW k p (upperHalfSpace m) φ ∧
      sobolevNorm k p (upperHalfSpace m) (f - φ) < ε := by
  obtain ⟨F, hF, hFf⟩ := exists_sobolev_extension_halfSpace m k p hp hp' f hf
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨g, hg, hgW, hFg⟩ :=
    HunterPDE.Sobolev.smooth_approximation hp hp' F hF (ε / 2) hhalf
  obtain ⟨φ, hφ, hφW, hgφ⟩ :=
    HunterPDE.Sobolev.smooth_compact_cutoff_approximation hp hp' g hg hgW
      (ε / 2) hhalf
  have hFφ : HunterPDE.Sobolev.MemW k p Set.univ (F - φ) := by
    refine ⟨hF.1.sub hφW.1, ?_⟩
    intro α hα
    obtain ⟨u, hu, hup⟩ := hF.2 α hα
    obtain ⟨v, hv, hvp⟩ := hφW.2 α hα
    exact ⟨u - v, hu.sub hv, hup.sub hvp⟩
  have hφH : MemW k p (upperHalfSpace m) φ := by
    apply (memW_iff_sobolev _ _).mpr
    refine ⟨hφW.1.mono_set (Set.subset_univ _), ?_⟩
    intro α hα
    obtain ⟨g, hg, hgp⟩ := hφW.2 α hα
    refine ⟨g, ⟨hg.1.mono_set (Set.subset_univ _),
      hg.2.1.mono_set (Set.subset_univ _), ?_⟩, ?_⟩
    · intro ψ hψ
      have hz (u : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
          (hu : HunterPDE.Sobolev.IsTestFunction (upperHalfSpace m) u)
          (v : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) :
          (∫ x in upperHalfSpace m, v x * u x) = ∫ x, v x * u x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hu.2.2 h)), mul_zero]
      rw [hz ψ hψ g, hz _ (hψ.iteratedPartial α) φ]
      simpa only [Measure.restrict_univ] using
        hg.2.2 ψ ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
    · have hgp' : MemLp g p volume := by simpa only [Measure.restrict_univ] using hgp
      exact hgp'.restrict _
  refine ⟨φ, ⟨hφ.1, hφ.2.1, hφ.2.2⟩, hφH, ?_⟩
  · have hH : IsOpen (upperHalfSpace m) :=
      isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
    calc
      sobolevNorm k p (upperHalfSpace m) (f - φ) ≤
          HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - φ) :=
        sobolevNorm_restrict_le _ hH _ _ hFφ
          (hFf.symm.sub (Filter.Eventually.of_forall fun _ => rfl))
      _ ≤ HunterPDE.Sobolev.sobolevNorm k p Set.univ (F - g) +
          HunterPDE.Sobolev.sobolevNorm k p Set.univ (g - φ) :=
        HunterPDE.Sobolev.sobolevNorm_sub_triangle hp hp' Set.univ isOpen_univ
          F g φ hF hgW hφW
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hFg hgφ
      _ = ε := ENNReal.add_halves ε
