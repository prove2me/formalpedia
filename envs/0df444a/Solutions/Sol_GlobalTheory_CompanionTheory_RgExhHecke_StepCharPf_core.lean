-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:38:30.635969+00:00
-- url     : https://prove2.me/submissions/b2d546dc-6564-40e6-b90e-8f92baa55805

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_PolyFn_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
theorem _root_.solution {D c ν : A} {k M : ℕ} {w r : ℂ} (hw : w ≠ 0) (hν : ν ^ M = 0)
    (hN : (c - algebraMap ℂ A (r * w)) ^ k = 0) (hcν : Commute c ν) (hDν : Commute D ν)
    (hid : D * (algebraMap ℂ A w + ν) = c * (algebraMap ℂ A (w + 1) + ν)) :
    (D - algebraMap ℂ A (r * (w + 1))) ^ (k + M) = 0 := by
  have cA : ∀ (s : ℂ) (T : A), Commute (algebraMap ℂ A s) T := fun s T => Algebra.commutes s T
  obtain ⟨N, hNdef⟩ : ∃ N, N = c - algebraMap ℂ A (r * w) := ⟨_, rfl⟩
  have hc : c = N + algebraMap ℂ A (r * w) := by rw [hNdef]; abel
  rw [← hNdef] at hN
  have hNν : Commute N ν := by rw [hNdef]; exact hcν.sub_left (cA _ _)
  obtain ⟨G, hG⟩ : ∃ G, G = algebraMap ℂ A (w + 1) + ν := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = algebraMap ℂ A w + ν := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = D - algebraMap ℂ A (r * (w + 1)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H, H = algebraMap ℂ A r * ν := ⟨_, rfl⟩
  have hxg : x * g = N * G - H := by
    have e : x * g = D * g - algebraMap ℂ A (r * (w + 1)) * g := by rw [hx, sub_mul]
    rw [e, hg, hid, hc, hG, hH]
    simp only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_smul]
    module
  have hNG : Commute N G := by rw [hG]; exact (cA _ _).symm.add_right hNν
  have hνH : Commute ν H := by rw [hH]; exact (cA _ _).symm.mul_right (Commute.refl ν)
  have h1 : (N * G) ^ k = 0 := by rw [hNG.mul_pow, hN, zero_mul]
  have h2 : (-H) ^ M = 0 := by
    have : H ^ M = 0 := by rw [hH, (cA _ _).mul_pow, hν, mul_zero]
    rcases neg_one_pow_eq_or ℤ M with e | e <;> simp [neg_pow H, this]
  have hNH : Commute N H := by rw [hH]; exact (cA _ _).symm.mul_right hNν
  have hGH : Commute G H := by
    rw [hG]
    exact (cA _ _).add_left hνH
  have hcomm : Commute (N * G) (-H) := (hNH.mul_left hGH).neg_right
  have h3 : (x * g) ^ (k + M) = 0 := by
    rw [hxg, sub_eq_add_neg]
    exact hcomm.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h1 h2 (by omega)
  have hxc : Commute x g := by
    rw [hx, hg]
    exact ((cA _ _).symm.sub_left (cA _ _)).add_right (hDν.sub_left (cA _ _))
  have hgu : IsUnit g := by
    rw [hg]
    exact IsNilpotent.isUnit_add_left_of_commute ⟨M, hν⟩ ((IsUnit.mk0 w hw).map (algebraMap ℂ A))
      (cA _ _).symm
  have h4 : x ^ (k + M) * g ^ (k + M) = 0 := by rw [← hxc.mul_pow, h3]
  rw [← hx]
  exact (hgu.pow _).mul_left_eq_zero.1 h4
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
