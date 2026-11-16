-- Prove2me | solution 1 for IAFTRL.lemma_J_3_finite
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:06:20.700542+00:00
-- url     : https://prove2.me/submissions/c76ebdbc-e276-401d-83ed-543a9af7079b

import Mathlib
import Definitions.Def_IAFTRL_IsGOptLaw
import Theorems.Thm_BanditAlgorithm_kiefer_wolfowitz_equivalence

open Matrix MeasureTheory IAFTRL

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤) :
    ∃ π : Fin K → ℝ, IsGOptLaw arms π := by
  classical
  set A : Set (Fin d → ℝ) := Set.range arms with hAdef
  have hAc : IsCompact A := (Set.finite_range arms).isCompact
  obtain ⟨hall, πs, hdes, hG, -⟩ :=
    BanditAlgorithm.kiefer_wolfowitz_equivalence (by omega) A hAc hspan
  have hGval : BanditAlgorithm.designGValue d A πs = d := ((hall πs hdes).2).1 hG
  obtain ⟨hprob, hnull⟩ := hdes
  set S : Finset (Fin d → ℝ) := Finset.univ.image arms with hSdef
  have hS : (S : Set (Fin d → ℝ)) = A := by simp [S, A]
  -- integrals against `πs` are finite sums over the support `S`
  have hint : ∀ f : (Fin d → ℝ) → ℝ, ∫ x, f x ∂πs = ∑ x ∈ S, πs.real {x} * f x := by
    intro f
    have hres : πs.restrict (S : Set (Fin d → ℝ)) = πs := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff, hS]
      exact hnull
    rw [← hres, setIntegral_finset S IntegrableOn.finset]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [smul_eq_mul, Measure.real, Measure.real, Measure.restrict_apply (measurableSet_singleton x)]
    congr 3
    exact (Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr hx))).symm
  -- the weights: split the mass of each support point equally among its indices
  let c : (Fin d → ℝ) → ℝ := fun x => ((Finset.univ.filter fun j => arms j = x).card : ℝ)
  let π : Fin K → ℝ := fun j => πs.real {arms j} / c (arms j)
  have hc : ∀ j, 0 < c (arms j) := by
    intro j
    have : j ∈ Finset.univ.filter fun j' => arms j' = arms j := by simp
    have h := Finset.card_pos.mpr ⟨j, this⟩
    simp only [c]
    exact_mod_cast h
  have hsum : ∀ g : (Fin d → ℝ) → ℝ, ∑ j, π j * g (arms j) = ∑ x ∈ S, πs.real {x} * g x := by
    intro g
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := arms)
      (fun j _ => by simp [S])]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨j0, -, rfl⟩ := Finset.mem_image.mp hx
    have hcx : 0 < c (arms j0) := hc j0
    calc ∑ j ∈ Finset.univ.filter (fun j => arms j = arms j0), π j * g (arms j)
        = ∑ j ∈ Finset.univ.filter (fun j => arms j = arms j0),
            πs.real {arms j0} / c (arms j0) * g (arms j0) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [π, (Finset.mem_filter.mp hj).2]
      _ = c (arms j0) * (πs.real {arms j0} / c (arms j0) * g (arms j0)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = πs.real {arms j0} * g (arms j0) := by
          field_simp
  -- the allocation matrix of `π` is the design matrix of `πs`
  have hmat : BanditAlgorithm.linearAllocationMatrix arms π = BanditAlgorithm.designMatrix d πs := by
    ext i k
    simp only [BanditAlgorithm.linearAllocationMatrix, BanditAlgorithm.designMatrix,
      Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Matrix.of_apply]
    rw [hint (fun a => a i * a k)]
    exact hsum (fun a => a i * a k)
  refine ⟨π, fun j => div_nonneg measureReal_nonneg (hc j).le, ?_, ?_, ?_⟩
  · have h1 := hsum (fun _ => 1)
    have h2 := hint (fun _ => 1)
    simp only [mul_one] at h1 h2
    rw [h1, ← h2]
    simp
  · rw [hmat]; exact hG.1
  · intro a
    rw [hmat, ← hGval]
    unfold BanditAlgorithm.designGValue
    apply le_csSup
    · exact ((Set.finite_range arms).image _).bddAbove
    · exact ⟨arms a, ⟨a, rfl⟩, rfl⟩
