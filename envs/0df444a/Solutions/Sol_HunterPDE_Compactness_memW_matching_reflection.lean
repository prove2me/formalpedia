-- Prove2me | solution 1 for HunterPDE.Compactness.memW_matching_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T09:40:35.755293+00:00
-- url     : https://prove2.me/submissions/985bdd48-6dd1-4ec8-a475-5c20c0e29f42

import Theorems.Thm_MeasureTheory_MemLp_finite_halfSpace_reflection
import Theorems.Thm_HunterPDE_Shared_integral_matchingReflection_mul_testFunction
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_zero_ae_eq
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution {n : ℕ} (i : Fin n) (k N : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (b c : Fin N → ℝ) (hb : ∀ j, 0 < b j)
    (hc : ∀ r : ℕ, r ≤ k → ∑ j : Fin N, c j * (-b j) ^ r = 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : HunterPDE.Compactness.MemW k p {x | 0 < x i} f) :
    HunterPDE.Compactness.MemW k p Set.univ
      (fun x => if 0 < x i then f x else
        ∑ j : Fin N, c j * f (WithLp.toLp 2 (Function.update (fun l => x l) i (-b j * x i)))) := by
  classical
  let H : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < x i}
  have hH : IsOpen H := isOpen_lt continuous_const (EuclideanSpace.proj i).continuous
  have hzero : (fun _ : Fin n => 0) ∈ HunterPDE.Compactness.multiIndicesLe n k := by
    simp [HunterPDE.Compactness.multiIndicesLe, Fintype.mem_piFinset]
  have hDzero (φ : EuclideanSpace ℝ (Fin n) → ℝ) :
      HunterPDE.Shared.multiDeriv φ (fun _ => 0) = φ := by
    have hlist : HunterPDE.Shared.multiIndexList (fun _ : Fin n => 0) = [] :=
      List.flatMap_eq_nil_iff.mpr (by intro j _; rfl)
    change HunterPDE.Shared.iteratedPartial φ
      (HunterPDE.Shared.multiIndexList (fun _ => 0)) = φ
    rw [hlist]
    rfl
  obtain ⟨g₀, hd₀, hg₀⟩ := hf _ hzero
  have hz : HunterPDE.Sobolev.HasWeakDeriv H (fun _ => 0) f g₀ := by
    refine ⟨hd₀.1, hd₀.2.1, ?_⟩
    intro φ hφ
    simpa [hDzero, HunterPDE.Sobolev.iteratedPartial] using hd₀.2.2 φ hφ
  have hfp : MemLp f p (volume.restrict H) :=
    hg₀.ae_eq (HunterPDE.Sobolev.HasWeakDeriv.zero_ae_eq hH hz)
  have hEF := MeasureTheory.MemLp.finite_halfSpace_reflection i p b c hb f hfp
  have hEFli := (hEF.locallyIntegrable hp).locallyIntegrableOn Set.univ
  intro α hα
  by_cases hαzero : α = 0
  · subst α
    refine ⟨_, ⟨hEFli, hEFli, ?_⟩, ?_⟩
    · intro φ _
      simp only [show (0 : Fin n → ℕ) = (fun _ => 0) from rfl,
        hDzero, Finset.sum_const_zero, pow_zero, one_mul]
    · simpa only [Measure.restrict_univ] using hEF
  obtain ⟨g, hd, hg⟩ := hf α hα
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    if 0 < x i then g x else ∑ j : Fin N, (c j * (-b j) ^ (α i)) *
      g (WithLp.toLp 2 (Function.update (fun l => x l) i (-b j * x i)))
  have hG : MemLp G p volume :=
    MeasureTheory.MemLp.finite_halfSpace_reflection i p b
      (fun j => c j * (-b j) ^ (α i)) hb g hg
  have hai : α i ≤ k := le_trans
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (α j))
      (Finset.mem_univ i)) (Finset.mem_filter.mp hα).2
  refine ⟨G, ⟨hEFli, (hG.locallyIntegrable hp).locallyIntegrableOn _, ?_⟩, ?_⟩
  · intro φ hφ
    simpa only [G, Measure.restrict_univ] using
      HunterPDE.Shared.integral_matchingReflection_mul_testFunction i α p hp b c hb
        (fun r hr => hc r (le_trans (Nat.le_of_lt hr) hai)) f g hfp hg hd φ hφ
  · simpa only [Measure.restrict_univ] using hG
