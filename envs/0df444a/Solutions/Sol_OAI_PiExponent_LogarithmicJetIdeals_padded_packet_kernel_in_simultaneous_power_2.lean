-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.padded_packet_kernel_in_simultaneous_power
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:30:58.818608+00:00
-- url     : https://prove2.me/submissions/3dfc9792-3875-4777-8913-7e86cc5bc0d5

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weight_mem_strictWeightedSimplex
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_formalJet_coeff_zero_implies_local_power_coeff_transfer
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeal_power_membership_iff_polynomialJet_coefficients
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localJetIdeals_pairwise_comaximal
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_mem_iInf_pow_of_pairwise_isCoprime

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

/-- The kernel of the padded raw packet map is contained in the corresponding power of the
simultaneous logarithmic jet ideal. -/
theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (S : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hS : 0 < S)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i ≤ S)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hpacket : rawPacketMap K v0 theta w (((n + m : ℕ) : ℝ) * S) r P = 0) :
    P ∈ (simultaneousJetIdeal K r T e) ^ n := by
  classical
  -- Positivity of the first row weight and of the rescaled tail weights.
  have hv0 : (0 : ℝ) < v0 := by simpa [InterpolationMatrix.rowWeights] using hv 0
  have hw : ∀ i : Fin m, 0 < w i / theta := by
    intro i
    simpa [InterpolationMatrix.rowWeights] using hv i.succ
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hHpos : (0 : ℝ) < ((n + m : ℕ) : ℝ) * S := by
    have hnm : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_pos_left hn m
    positivity
  -- Step 1: the padded packet vanishing gives the weighted formal-jet coefficient vanishing at
  -- every scaled centre.
  have hcoeff : ∀ j : Fin K, ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        ((n + m : ℕ) : ℝ) * S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (formalJet (fun i => (j.val : ℂ) * r i) P) = 0 := by
    intro j a ha
    have hmem : a ∈ OAI.PiExponent.strictWeightedSimplex
        (InterpolationMatrix.rowWeights v0 theta w) (((n + m : ℕ) : ℝ) * S) :=
      OAI.PiExponent.AdmissibleFormalInterpolation.weight_mem_strictWeightedSimplex
        v0 (fun i => w i / theta) (((n + m : ℕ) : ℝ) * S) hv0 hw hHpos a ha
    have hrow := congrFun hpacket (j, ⟨a, hmem⟩)
    simpa [rawPacketMap] using hrow
  -- Step 2: membership in each local jet ideal power.
  have hlocal : ∀ j : Fin K,
      P ∈ (localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ n := by
    intro j
    rw [localJetIdeal_power_membership_iff_polynomialJet_coefficients
      (fun i => (j.val : ℂ) * r i) T e he n P]
    intro u hu
    have hcu := weighted_formalJet_coeff_zero_implies_local_power_coeff_transfer
      v0 theta w S (fun i => (j.val : ℂ) * r i) T e hS hv he hscale hT n P
      (hcoeff j) (fun i => u i) hu
    have h1 : InterpolationMatrix.exponentVector (fun i => u i) = u := by
      ext i
      simp [InterpolationMatrix.exponentVector]
    have h2 : OAI.PiExponent.LogarithmicJetIdeals.localCoordinatePolynomial
          (fun i => (j.val : ℂ) * r i) T P =
        polynomialJet (fun i => (j.val : ℂ) * r i) T P := rfl
    rw [← h1, ← h2]
    exact hcu
  -- Step 3: combine the local memberships along the pairwise comaximal centres.
  have hcop : ∀ j k : Fin K, j ≠ k →
      IsCoprime (localJetIdeal (fun i => (j.val : ℂ) * r i) T e)
        (localJetIdeal (fun i => (k.val : ℂ) * r i) T e) := by
    intro j k hjk
    rw [Ideal.isCoprime_iff_sup_eq]
    exact localJetIdeals_pairwise_comaximal K r T e hc j k hjk
  have hmem := mem_iInf_pow_of_pairwise_isCoprime K n
    (fun j : Fin K => localJetIdeal (fun i => (j.val : ℂ) * r i) T e) hcop hlocal
  simpa [simultaneousJetIdeal] using hmem
