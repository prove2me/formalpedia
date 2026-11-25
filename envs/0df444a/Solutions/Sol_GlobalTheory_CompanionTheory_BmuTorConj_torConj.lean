-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuTorConj.torConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:08.529276+00:00
-- url     : https://prove2.me/submissions/10933dc5-1bf4-476a-a93c-c1ea4f24cbe0

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugacy
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorConj_exists_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorConj_uw_col
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorConj_uw_row
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuTorConj
namespace GlobalTheory.CompanionTheory.BmuTorConj
theorem _root_.solution : CompanionTheory.Bmu.TorConj := by
  unfold CompanionTheory.Bmu.TorConj
  intro k r z c hz hc
  obtain ⟨T, hT0, hT1, hTc⟩ := exists_scale r c hc
  obtain ⟨d, hd⟩ : ∃ d : Fin (2 * r + k + 1) → ℂ, d = fun i =>
      if i.val < r then T i.val else if i.val ≤ r + k then 1 else (star (T (2 * r + k - i.val)))⁻¹ :=
    ⟨_, rfl⟩
  have hdlow : ∀ i : Fin (2 * r + k + 1), i.val < r → d i = T i.val := fun i hi => by
    rw [hd]; simp only; rw [if_pos hi]
  have hdmid : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → d i = 1 := fun i h1 h2 => by
    rw [hd]; simp only; rw [if_neg (by omega), if_pos h2]
  have hdhigh : ∀ i : Fin (2 * r + k + 1), r + k < i.val → d i = (star (T (2 * r + k - i.val)))⁻¹ :=
    fun i hi => by
      rw [hd]; simp only; rw [if_neg (by omega), if_neg (by omega)]
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    by_cases h1 : i.val < r
    · rw [hdlow i h1]; exact hT0 _
    by_cases h2 : i.val ≤ r + k
    · rw [hdmid i (by omega) h2]; exact one_ne_zero
    · rw [hdhigh i (by omega)]; exact inv_ne_zero (star_ne_zero.mpr (hT0 _))
  have hHnz : ∀ i j : Fin (2 * r + k + 1), Hpk k r i j ≠ 0 →
      (i.val < r ∧ i.val + j.val = 2 * r + k) ∨ (j.val < r ∧ i.val + j.val = 2 * r + k) ∨
        (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := by
    intro i j h
    unfold Hpk at h
    split_ifs at h with h1 h2 h3 <;> first | exact absurd rfl h | tauto
  have hkey : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1 := by
    intro i j h
    have hilt := i.isLt
    have hjlt := j.isLt
    rcases hHnz i j h with ⟨hi, hij⟩ | ⟨hj, hij⟩ | ⟨hi1, hi2, rfl⟩
    · rw [hdlow i hi, hdhigh j (by omega), show 2 * r + k - j.val = i.val by omega]
      exact mul_inv_cancel₀ (star_ne_zero.mpr (hT0 _))
    · rw [hdhigh i (by omega), hdlow j hj, show 2 * r + k - i.val = j.val by omega]
      simp [hT0 j.val]
    · rw [hdmid i hi1 hi2]; simp
  have hdiagU : ∀ e : Fin (2 * r + k + 1) → ℂ, (∀ i j, Hpk k r i j ≠ 0 → star (e i) * e j = 1) →
      diagonal e ∈ UH (Hpk k r) := by
    intro e he
    show (diagonal e)ᴴ * Hpk k r * diagonal e = Hpk k r
    ext i j
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply]
    by_cases h0 : Hpk k r i j = 0
    · rw [h0]; ring
    · calc star (e i) * Hpk k r i j * e j = (star (e i) * e j) * Hpk k r i j := by ring
        _ = Hpk k r i j := by rw [he i j h0, one_mul]
  have hUmul : ∀ A B, A ∈ UH (Hpk k r) → B ∈ UH (Hpk k r) → A * B ∈ UH (Hpk k r) := by
    intro A B hA hB
    have hA' : Aᴴ * Hpk k r * A = Hpk k r := hA
    have hB' : Bᴴ * Hpk k r * B = Hpk k r := hB
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [conjTranspose_mul]
    calc Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hA', hB']
  have hτU : diagonal d ∈ UH (Hpk k r) := hdiagU d hkey
  have hτinvU : diagonal (fun i => (d i)⁻¹) ∈ UH (Hpk k r) := by
    refine hdiagU _ fun i j h => ?_
    rw [star_inv₀, ← mul_inv, hkey i j h, inv_one]
  have hτinv : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    have he : (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) := funext fun i => inv_mul_cancel₀ (hd0 i)
    rw [he, diagonal_one]
  have hcomm : ∀ h ∈ UWset k r z, diagonal d * h = h * diagonal d := by
    intro h hh
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hij : i = j
    · subst hij; ring
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_row k r z h hh i hi j, if_neg (fun e => hij e.symm)]; ring
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [uw_col k r z h hh j hj i, if_neg hij]; ring
    push_neg at hi hj
    rw [hdmid i hi.1 hi.2, hdmid j hj.1 hj.2]; ring
  have hzd : ∀ j, (d j)⁻¹ * z j = z j := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
    · push_neg at hj; rw [hdmid j hj.1 hj.2, inv_one, one_mul]
  refine ⟨diagonal d, hτU, hcomm, fun m hm => ?_⟩
  rw [hτinv]
  obtain ⟨hmU, hm2, hm3⟩ := hm
  have hent : ∀ i j, (diagonal d * m * diagonal (fun i => (d i)⁻¹)) i j = d i * m i j * (d j)⁻¹ := by
    intro i j
    rw [mul_diagonal, diagonal_mul]
  refine ⟨⟨hUmul _ _ (hUmul _ _ hτU hmU) hτinvU, ?_, ?_⟩, ?_⟩
  · intro a i hai
    rw [hent, hm2 a i hai]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · intro i j hj1 hj2 hi
    rw [hent, hm3 i j hj1 hj2 hi]
    split_ifs with h
    · subst h; rw [mul_one, mul_inv_cancel₀ (hd0 _)]
    · simp
  · have hsum : ∑ a, c a * PI.BesselMapUniq.ellA k r z (diagonal d * m * diagonal (fun i => (d i)⁻¹)) a =
        cStd * ell k r z m := by
      rw [ell, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [PI.BesselMapUniq.ellA]
      have e1 : d (eI k r a) = T a.val := hdlow _ a.isLt
      split_ifs with ha
      · have e2 : d (eI k r ⟨a.val + 1, ha⟩) = T (a.val + 1) := hdlow _ ha
        rw [hent, e1, e2, ← mul_assoc, ← mul_assoc, hTc a,
          mul_right_comm (cStd * T (a.val + 1)), mul_inv_cancel_right₀ (hT0 _)]
      · have hmv : (diagonal d * m * diagonal (fun i => (d i)⁻¹)).mulVec z (eI k r a) =
            d (eI k r a) * m.mulVec z (eI k r a) := by
          simp only [mulVec, dotProduct, hent, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc d (eI k r a) * m (eI k r a) j * (d j)⁻¹ * z j
              = d (eI k r a) * m (eI k r a) j * ((d j)⁻¹ * z j) := by ring
            _ = d (eI k r a) * (m (eI k r a) j * z j) := by rw [hzd j]; ring
        rw [hmv, e1, ← mul_assoc, hTc a, hT1 _ (by omega), mul_one]
    rw [PI.BesselMapUniq.psiGen, psi, hsum]
end GlobalTheory.CompanionTheory.BmuTorConj
