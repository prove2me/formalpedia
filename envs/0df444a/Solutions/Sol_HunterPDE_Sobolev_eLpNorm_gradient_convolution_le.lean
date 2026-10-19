-- Prove2me | solution 1 for HunterPDE.Sobolev.eLpNorm_gradient_convolution_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T17:53:21.286468+00:00
-- url     : https://prove2.me/submissions/f30385d2-ea86-4031-b22c-b0406010c110

import Theorems.Thm_HunterPDE_Shared_gradient_convolution_ae
import Theorems.Thm_MeasureTheory_eLpNorm_convolution_le_of_nonneg_normalized
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory ContinuousLinearMap HunterPDE.Shared
open scoped Convolution ENNReal
set_option autoImplicit false

theorem solution {n : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hloc : LocallyIntegrable f volume)
    (hf : ∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) f g ∧ MemLp g p volume)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : HunterPDE.Shared.IsTestFunction Set.univ ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    eLpNorm (fun x => ‖gradient (ρ ⋆[lsmul ℝ ℝ, volume] f) x‖) p volume ≤
      eLpNorm (HunterPDE.Shared.weakGradNorm Set.univ f) p volume := by
  classical
  let d := fun i : Fin n => weakDeriv Set.univ (Pi.single i 1) f
  have hd (i : Fin n) : HasWeakDeriv Set.univ (Pi.single i 1) f (d i) := by
    have he : ∃ g, HasWeakDeriv Set.univ (Pi.single i 1) f g :=
      ⟨(hf i).choose, (hf i).choose_spec.1⟩
    dsimp [d]
    unfold weakDeriv
    rw [dif_pos he]
    exact Exists.choose_spec _
  have hdp (i : Fin n) : MemLp (d i) p volume := by
    obtain ⟨g, hg, hgp⟩ := hf i
    have hae := (hd i).ae_eq isOpen_univ hg
    rw [Measure.restrict_univ] at hae
    exact hgp.ae_eq hae.symm
  let G := fun x => (WithLp.toLp 2 (fun i => d i x) : EuclideanSpace ℝ (Fin n))
  have hG : MemLp G p volume := memLp_piLp_iff.mpr hdp
  have hnorm (x) : ‖G x‖ = weakGradNorm Set.univ f x := by
    simp [G, d, EuclideanSpace.norm_eq, weakGradNorm, Real.norm_eq_abs, sq_abs]
  have hae := gradient_convolution_ae f hloc d hd ρ hρ
  have hb (x : EuclideanSpace ℝ (Fin n)) :
      ‖∫ y, ρ y • G (x-y)‖ ≤
        (ρ ⋆[lsmul ℝ ℝ, volume] (fun z => ‖G z‖)) x := by
    calc
      _ ≤ ∫ y, ‖ρ y • G (x-y)‖ := norm_integral_le_integral_norm _
      _ = _ := by
        simp only [convolution, lsmul_apply, smul_eq_mul, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg (hρ0 _)]
  rw [eLpNorm_norm]
  calc
    _ ≤ eLpNorm (ρ ⋆[lsmul ℝ ℝ, volume] (fun z => ‖G z‖)) p volume := by
      apply eLpNorm_mono_ae_real
      filter_upwards [hae] with x hx
      rw [hx]
      exact hb x
    _ ≤ eLpNorm (fun z => ‖G z‖) p volume :=
      MeasureTheory.eLpNorm_convolution_le_of_nonneg_normalized hp hptop
        ρ hρ.1.continuous hρ.2.1 hρ0 hρ1 _ hG.norm
    _ = _ := by simp_rw [hnorm]
