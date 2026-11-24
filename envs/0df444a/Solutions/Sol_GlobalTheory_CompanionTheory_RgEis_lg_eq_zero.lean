-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.lg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:05:17.114311+00:00
-- url     : https://prove2.me/submissions/fb23787f-88e9-43fd-80b5-deb460f22ebc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [Field E]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (A : Ad E R) (hA : A.GoodL) (u : Rˣ) (h1 : (u : R) ∈ A.O)
    (h2 : ((u⁻¹ : Rˣ) : R) ∈ A.O) (hw : ∀ w, ‖A.φ w (u : R)‖ = 1) : A.lg u = 0 := by
  let j : Rˣ →* GL Unit R := Units.map (Matrix.scalar Unit : R →+* Matrix Unit Unit R).toMonoidHom
  have hj : j u ∈ A.kGL Unit := by
    refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
    · simpa [j] using h1
    · have : ((j u)⁻¹ : GL Unit R) = j u⁻¹ := (map_inv j u).symm
      rw [this]
      simpa [j] using h2
    · rw [Matrix.mem_unitaryGroup_iff]
      ext r c
      simp [j, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw w]
  have hdet : Continuous fun g : GL Unit R => (Matrix.GeneralLinearGroup.det g : Rˣ) := by
    rw [Units.continuous_iff]
    constructor
    · exact Units.continuous_val.matrix_det
    · have : (fun g : GL Unit R => (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R)) =
          fun g => ((g⁻¹ : GL Unit R) : Matrix Unit Unit R).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [this]
      exact (Units.continuous_val.comp continuous_inv).matrix_det
  have hc : Continuous fun g : GL Unit R => A.lg (Matrix.GeneralLinearGroup.det g) :=
    hA.lgcont.comp hdet
  obtain ⟨C, hC⟩ := (hA.kcpt Unit).exists_bound_of_continuousOn hc.continuousOn
  have hone : A.lg 1 = 0 := by
    have := hA.lgmul 1 1
    rw [mul_one] at this
    linarith
  have hpow : ∀ n : ℕ, A.lg (u ^ n) = n * A.lg u := by
    intro n
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hA.lgmul, ih]; push_cast; ring
  have hdj : Matrix.GeneralLinearGroup.det (j u) = u := by
    apply Units.ext
    simp [j, Matrix.GeneralLinearGroup.val_det_apply]
  have hb : ∀ n : ℕ, (n : ℝ) * |A.lg u| ≤ C := by
    intro n
    have := hC (j u ^ n) (pow_mem hj n)
    rw [map_pow, hdj, hpow, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
    exact this
  by_contra hne
  have hpos : 0 < |A.lg u| := abs_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |A.lg u|)
  have := hb n
  rw [div_lt_iff₀ hpos] at hn
  linarith
end GlobalTheory.CompanionTheory.RgEis
