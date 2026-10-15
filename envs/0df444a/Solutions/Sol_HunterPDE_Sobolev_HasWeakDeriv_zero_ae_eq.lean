-- Prove2me | solution 1 for HunterPDE.Sobolev.HasWeakDeriv.zero_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T19:25:33.276322+00:00
-- url     : https://prove2.me/submissions/d703c71c-8449-4671-9951-2fd6515a19a7

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_ae_eq

open MeasureTheory HunterPDE.Sobolev

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : HasWeakDeriv Ω (fun _ => 0) f g) :
    g =ᵐ[volume.restrict Ω] f := by
  have hzero (φ : EuclideanSpace ℝ (Fin n) → ℝ) :
      iteratedPartial (fun _ : Fin n => 0) φ = φ := by
    simp only [iteratedPartial, Function.iterate_zero, id_eq]
    induction List.finRange n with
    | nil => rfl
    | cons i l ih => simpa only [List.foldr_cons, id_eq] using ih
  have hf : HasWeakDeriv Ω (fun _ => 0) f f := by
    refine ⟨hg.1, hg.1, ?_⟩
    intro φ _
    simp [hzero]
  exact hg.ae_eq hΩ hf
