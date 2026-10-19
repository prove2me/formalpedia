-- Prove2me | solution 1 for HunterPDE.Compactness.boundedMap_vanishes_on_memW0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T20:32:35.229605+00:00
-- url     : https://prove2.me/submissions/769c50b1-6898-42fb-949e-7bb143b6186e

import Theorems.Thm_HunterPDE_Compactness_memW_iff_sobolev
import Theorems.Thm_HunterPDE_Sobolev_memW_of_isTestFunction
import Theorems.Thm_HunterPDE_Sobolev_IsTestFunction_iteratedPartial
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Data.ENNReal.Inv

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {n k d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ)
    (C : ℝ≥0)
    (hsub : ∀ f g, MemW k p Ω f → MemW k p Ω g →
      T (f - g) =ᵐ[volume] T f - T g)
    (hbound : ∀ f, MemW k p Ω f → MemLp (T f) p volume ∧
      eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm k p Ω f)
    (hzero : ∀ φ, HunterPDE.Shared.IsTestFunction Ω φ → T φ =ᵐ[volume] 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW0 k p Ω f) :
    T f =ᵐ[volume] 0 := by
  have htest (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (hφ : HunterPDE.Shared.IsTestFunction Ω φ) : MemW k p Ω φ := by
    have hw := HunterPDE.Sobolev.memW_of_isTestFunction (k := k) hp φ
      ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
    apply (memW_iff_sobolev Ω φ).mpr
    refine ⟨hw.1.mono_set (Set.subset_univ _), ?_⟩
    intro α hα
    obtain ⟨g, hg, hgp⟩ := hw.2 α hα
    refine ⟨g, ⟨hg.1.mono_set (Set.subset_univ _),
      hg.2.1.mono_set (Set.subset_univ _), ?_⟩, ?_⟩
    · intro ψ hψ
      have hz (u : EuclideanSpace ℝ (Fin n) → ℝ)
          (hu : HunterPDE.Sobolev.IsTestFunction Ω u)
          (v : EuclideanSpace ℝ (Fin n) → ℝ) :
          ∫ x in Ω, v x * u x = ∫ x, v x * u x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hu.2.2 h)), mul_zero]
      rw [hz ψ hψ g, hz _ (hψ.iteratedPartial α) φ]
      simpa only [Measure.restrict_univ] using
        hg.2.2 ψ ⟨hψ.1, hψ.2.1, Set.subset_univ _⟩
    · have hgp' : MemLp g p volume := by
        simpa only [Measure.restrict_univ] using hgp
      exact hgp'.restrict Ω
  have hnorm : eLpNorm (T f) p volume = 0 := by
    apply le_antisymm ?_ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε' : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
    obtain ⟨φ, hφ, hdist⟩ := hf.2 ((ε : ℝ≥0∞) / (C + 1 : ℝ≥0))
      (ENNReal.div_pos hε' ENNReal.coe_ne_top)
    have hφW := htest φ hφ
    have hfW := (memW_iff_sobolev Ω f).mp hf.1
    have hgW := (memW_iff_sobolev Ω φ).mp hφW
    have hdiff : MemW k p Ω (f - φ) := by
      apply (memW_iff_sobolev Ω (f - φ)).mpr
      refine ⟨hfW.1.sub hgW.1, ?_⟩
      intro α hα
      obtain ⟨u, hu, hup⟩ := hfW.2 α hα
      obtain ⟨v, hv, hvp⟩ := hgW.2 α hα
      exact ⟨u - v, hu.sub hv, hup.sub hvp⟩
    have heq : T (f - φ) =ᵐ[volume] T f := by
      filter_upwards [hsub f φ hf.1 hφW, hzero φ hφ] with x hx hz
      simpa only [Pi.sub_apply, hz, Pi.zero_apply, sub_zero] using hx
    calc
      eLpNorm (T f) p volume = eLpNorm (T (f - φ)) p volume :=
        eLpNorm_congr_ae heq.symm
      _ ≤ (C : ℝ≥0∞) * sobolevNorm k p Ω (f - φ) := (hbound _ hdiff).2
      _ ≤ ((C + 1 : ℝ≥0) : ℝ≥0∞) * sobolevNorm k p Ω (f - φ) :=
        mul_le_mul_left (by exact_mod_cast le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ 1 from zero_le)) _
      _ ≤ ε := (ENNReal.mul_lt_of_lt_div' hdist).le
      _ = 0 + ε := (zero_add _).symm
  exact (eLpNorm_eq_zero_iff (hbound f hf.1).1.1 (ne_of_gt (zero_lt_one.trans_le hp))).mp hnorm
