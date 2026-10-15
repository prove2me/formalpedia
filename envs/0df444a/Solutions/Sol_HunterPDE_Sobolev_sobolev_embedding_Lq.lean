-- Prove2me | solution 1 for HunterPDE.Sobolev.sobolev_embedding_Lq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T19:26:02.980289+00:00
-- url     : https://prove2.me/submissions/30b05018-1673-4d65-b1b6-bf325fca3858

import Theorems.Thm_HunterPDE_Sobolev_sobolev_endpoint_embedding
import Theorems.Thm_MeasureTheory_eLpNorm_le_max_of_memLp
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_zero_ae_eq
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open MeasureTheory HunterPDE.Sobolev

theorem solution {n : ℕ} {p q : ℝ} (hp : 1 ≤ p) (hpn : p < n) (hpq : p ≤ q)
    (hq : q ≤ sobolevConjugate n p) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW 1 (ENNReal.ofReal p) Set.univ f →
        MemLp f (ENNReal.ofReal q) volume ∧
          eLpNorm f (ENNReal.ofReal q) volume ≤
            (C : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨C, hC⟩ := sobolev_endpoint_embedding hp hpn
  refine ⟨max 1 C, ?_⟩
  intro f hf
  obtain ⟨g, hg, hgp⟩ := hf.2 (fun _ => 0) (by simp)
  have hgf : g =ᵐ[volume] f := by
    simpa only [Measure.restrict_univ] using hg.zero_ae_eq isOpen_univ
  have hfp : MemLp f (ENNReal.ofReal p) volume := by
    exact (show MemLp g (ENNReal.ofReal p) volume by
      simpa only [Measure.restrict_univ] using hgp).ae_eq hgf
  have hchosen : HasWeakDeriv Set.univ (fun _ => 0) f
      (weakDeriv Set.univ (fun _ => 0) f) := by
    unfold weakDeriv
    rw [dif_pos (show ∃ g, HasWeakDeriv Set.univ (fun _ => 0) f g from ⟨g, hg⟩)]
    exact Exists.choose_spec _
  have hz : weakDeriv Set.univ (fun _ => 0) f =ᵐ[volume] f := by
    simpa only [Measure.restrict_univ] using hchosen.zero_ae_eq isOpen_univ
  have hzero : (fun _ : Fin n => 0) ∈ multiIndices n 1 := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, by simp⟩
    exact Finset.mem_image.mpr ⟨fun _ => (0 : Fin 2), Finset.mem_univ _, rfl⟩
  have hpNorm : eLpNorm f (ENNReal.ofReal p) volume ≤
      sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by
    rw [sobolevNorm, if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
    have hsum := Finset.single_le_sum (s := multiIndices n 1)
      (f := fun α => eLpNorm (weakDeriv Set.univ α f) (ENNReal.ofReal p)
        (volume.restrict Set.univ) ^ p) (fun _ _ => bot_le) hzero
    have hroot := ENNReal.rpow_le_rpow hsum (by positivity : 0 ≤ 1 / p)
    simpa only [Measure.restrict_univ, eLpNorm_congr_ae hz,
      ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] using hroot
  obtain ⟨hfr, hbound⟩ := hC f hf
  have hinter := eLpNorm_le_max_of_memLp hp0 hpq hq hfp hfr
  refine ⟨⟨hfp.aestronglyMeasurable, hinter.trans_lt ?_⟩, ?_⟩
  · exact max_lt hfp.eLpNorm_lt_top hfr.eLpNorm_lt_top
  · apply hinter.trans
    apply max_le
    · calc
        _ ≤ sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := hpNorm
        _ = (1 : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := (one_mul _).symm
        _ ≤ _ := mul_le_mul_left (by exact_mod_cast (le_max_left (1 : NNReal) C)) _
    · exact hbound.trans (mul_le_mul_left (by exact_mod_cast (le_max_right (1 : NNReal) C)) _)
