-- Prove2me | solution 1 for GlobalTheory.PairingInvariants.exists_unitary_diagonal_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:54.668431+00:00
-- url     : https://prove2.me/submissions/ab0f0942-d728-4532-bdf5-5470404c89f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.PairingInvariants
namespace GlobalTheory.PairingInvariants
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g) :
    ∃ (u₁ u₂ : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ), u₁ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      u₂ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      g = u₁ * diagonal (fun i => cexp (a i)) * u₂ := by
  have hP : (gᴴ * g).PosDef := Matrix.PosDef.conjTranspose_mul_self g (Matrix.mulVec_injective_iff_isUnit.2 hg)
  have hH := hP.isHermitian
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUm : U ∈ Matrix.unitaryGroup (Fin n) ℂ := hH.eigenvectorUnitary.2
  have h1 : star U * (gᴴ * g) * U = diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [hU, Function.comp_def] using this
  have hpos : ∀ i, 0 < hH.eigenvalues i := hP.eigenvalues_pos
  let a : Fin n → ℝ := fun i => Real.log (hH.eigenvalues i) / 2
  have ha : ∀ i, cexp (-(a i : ℂ)) * ((hH.eigenvalues i : ℝ) : ℂ) * cexp (-(a i : ℂ)) = 1 := by
    intro i
    have : ((hH.eigenvalues i : ℝ) : ℂ) = cexp ((a i : ℂ) + a i) := by
      rw [← Complex.ofReal_add, ← Complex.ofReal_exp]
      congr 1
      simp only [a, add_halves]
      rw [Real.exp_log (hpos i)]
    rw [this, ← Complex.exp_add, ← Complex.exp_add]
    simp
  refine ⟨g * U * diagonal (fun i => cexp (-(a i : ℂ))), star U, a, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have hd : star (diagonal (fun i => cexp (-(a i : ℂ)))) = diagonal (fun i => cexp (-(a i : ℂ))) := by
      rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose]
      congr 1
      funext i
      simp [← Complex.exp_conj]
    rw [star_mul, star_mul, hd]
    calc _ = diagonal (fun i => cexp (-(a i : ℂ))) * (star U * (gᴴ * g) * U) * diagonal (fun i => cexp (-(a i : ℂ))) := by
            simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
      _ = 1 := by
            rw [h1, diagonal_mul_diagonal, diagonal_mul_diagonal]
            simp only [ha, diagonal_one]
  · exact Unitary.star_mem hUm
  · have h2 : diagonal (fun i => cexp (-(a i : ℂ))) * diagonal (fun i => cexp (a i : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal]
      simp [← Complex.exp_add]
    have h3 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hUm
    rw [Matrix.mul_assoc (g * U), h2, Matrix.mul_one, Matrix.mul_assoc, h3, Matrix.mul_one]
end GlobalTheory.PairingInvariants
