-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/28d89d66-c7a1-5296-aeab-e52e2746443a

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled
set_option autoImplicit false
open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

universe u

theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (ew eK : ℕ) (hew : 1 ≤ ew) (heK : 1 ≤ eK) (e : ℕ) (he : e = ew * eK)
    (e' : ℕ) (he' : 1 ≤ e')
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (x' : UVCrossingModel W (ϖ ^ e)) (hx' : x' ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (habx' : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = x')
    (hagree : ∀ r s : ℕ, 1 ≤ r → 0 < s → s < r * (e' * e) → (¬ ∃ d, d ≤ e' * ew ∧ s = r * (e' * e - d * eK)) →
        circleIndexDrop (fun w => ((r * e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * e' * e) s ab =
          circleIndexDrop (fun w => ((r * e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * e' * e) s ab')
    (φ : ℕ → ℤ)
    (hφ : ∀ t, φ t =
        ((gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (e' * e) t x).toNat : ℤ)
        - (gaussOrder (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (e' * e) t x').toNat)
    (G : ℕ → ℤ) (hG : ∀ d, G d = (φ (e' * e - d * eK) - φ (e' * e)) / eK) :
    (∀ d, d ≤ e' * ew → (eK : ℤ) ∣ φ (e' * e - d * eK) - φ (e' * e)) ∧
    (∀ d ∈ Finset.Ico 1 (e' * ew), (G d - G (d - 1)) - (G (d + 1) - G d) =
        (circleIndexDrop (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e)
            (e' * e - d * eK) ab : ℤ)
          - circleIndexDrop (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e)
            (e' * e - d * eK) ab') ∧
    G 1 - G 0 =
      -((sSup (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w)
            (e' * e) (e' * e) ab) : ℤ)
        - sSup (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w)
            (e' * e) (e' * e) ab')) ∧
    G (e' * ew) - G (e' * ew - 1) =
      -((sInf (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) 0 ab) : ℤ)
        - sInf (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) 0 ab')) ∧
    G 1 - G 0 = -(φ (e' * e) - φ (e' * e - 1)) ∧ G (e' * ew) - G (e' * ew - 1) = -(φ 1 - φ 0) := by
  have he1 : 1 ≤ e := by subst he; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hTN : e' * e = e' * ew * eK := by rw [he, Nat.mul_assoc]
  have hoff : ∀ r s : ℕ, 1 ≤ r → ¬ r ∣ s → 0 < s → s < r * e' * e →
      circleIndexDrop (fun w => ((r * e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * e' * e) s ab =
        circleIndexDrop (fun w => ((r * e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * e' * e) s ab' := by
    intro r s hr hrs hs0 hse
    refine hagree r s hr hs0 (by rw [← Nat.mul_assoc]; exact hse) ?_
    rintro ⟨d, -, rfl⟩
    exact hrs (Dvd.intro _ rfl)
  obtain ⟨hint, hbot, htop⟩ :=
    slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq ϖ hϖ e he1 e' he' x hx ab hb habx x' hx' ab' hb' habx'
      hoff
  have hint' : ∀ p : ℕ, 1 ≤ p → p + 1 ≤ e' * e →
      (φ p - φ (p - 1)) - (φ (p + 1) - φ p) =
        (circleIndexDrop (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) p ab : ℤ)
          - circleIndexDrop (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) p ab' := by
    intro p hp1 hpe
    have h := hint p hp1 hpe
    rw [hφ p, hφ (p - 1), hφ (p + 1)]
    exact h
  have hbot' : φ 1 - φ 0 =
      (sInf (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) 0 ab) : ℤ)
        - sInf (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) 0 ab') := by
    rw [hφ 1, hφ 0]; exact hbot
  have htop' : φ (e' * e) - φ (e' * e - 1) =
      (sSup (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) (e' * e) ab) : ℤ)
        - sSup (dominantIndices (fun w => ((e' : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (e' * e) (e' * e) ab') := by
    rw [hφ (e' * e), hφ (e' * e - 1)]; exact htop
  have hoff1 : ∀ p : ℕ, 1 ≤ p → p + 1 ≤ e' * e → (¬ ∃ d, d ≤ e' * ew ∧ p = e' * e - d * eK) →
      (φ p - φ (p - 1)) - (φ (p + 1) - φ p) = 0 := by
    intro p hp1 hpe hng
    rw [hint' p hp1 hpe]
    have h := hagree 1 p le_rfl hp1 (by omega) (by simpa using hng)
    simp only [one_mul] at h
    rw [h, sub_self]
  have affine : ∀ (a n : ℕ), (∀ j, 0 < j → j < n → (φ (a + j) - φ (a + j - 1)) - (φ (a + j + 1) - φ (a + j)) = 0) →
      ∀ j, j ≤ n → φ (a + j) = φ a + j * (φ (a + 1) - φ a) := by
    intro a n h
    have key : ∀ j, (j ≤ n → φ (a + j) = φ a + j * (φ (a + 1) - φ a)) ∧
        (j + 1 ≤ n → φ (a + (j + 1)) = φ a + ((j + 1 : ℕ) : ℤ) * (φ (a + 1) - φ a)) := by
      intro j
      induction j with
      | zero => exact ⟨fun _ => by simp, fun _ => by push_cast; ring⟩
      | succ j ih =>
          refine ⟨ih.2, fun hj => ?_⟩
          have h1 := ih.1 (by omega)
          have h2 := ih.2 (by omega)
          have h3 := h (j + 1) (by omega) (by omega)
          have e1 : a + (j + 1) - 1 = a + j := by omega
          have e2 : a + (j + 1) + 1 = a + (j + 1 + 1) := by omega
          rw [e1, e2] at h3
          push_cast at h1 h2 ⊢
          linear_combination 2 * h2 - h1 - h3
    exact fun j hj => (key j).1 hj
  have hgrid : ∀ d, d ≤ e' * ew → d * eK ≤ e' * e := fun d hd => by
    rw [hTN]; exact Nat.mul_le_mul_right _ hd
  have σ_spec : ∀ d, 1 ≤ d → d ≤ e' * ew →
      (∀ j, j ≤ eK → φ (e' * e - d * eK + j) = φ (e' * e - d * eK) + j * (φ (e' * e - d * eK + 1) - φ (e' * e - d * eK))) := by
    intro d hd1 hd j hj
    refine affine (e' * e - d * eK) eK ?_ j hj
    intro i hi0 hi
    have hde := hgrid d hd
    refine hoff1 (e' * e - d * eK + i) (by omega) (by
      have : (d - 1) * eK + eK = d * eK := by
        rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega) |>.trans (le_refl _))]
      omega) ?_
    rintro ⟨d', hd', hEq⟩
    have hde' := hgrid d' hd'
    have h1 : d * eK = d' * eK + i := by omega
    have h2 : eK ∣ i := by
      have : i = d * eK - d' * eK := by omega
      rw [this, ← Nat.sub_mul]
      exact Dvd.intro_left _ rfl
    exact absurd (Nat.le_of_dvd hi0 h2) (by omega)
  set σ : ℕ → ℤ := fun d => φ (e' * e - d * eK + 1) - φ (e' * e - d * eK) with hσ
  have htopblk : ∀ d, 1 ≤ d → d ≤ e' * ew → φ (e' * e - (d - 1) * eK) = φ (e' * e - d * eK) + eK * σ d := by
    intro d hd1 hd
    have h := σ_spec d hd1 hd eK le_rfl
    have hidx : e' * e - d * eK + eK = e' * e - (d - 1) * eK := by
      have hde := hgrid d hd
      have : (d - 1) * eK + eK = d * eK := by
        rw [Nat.sub_mul, one_mul]; exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hd1)
      omega
    rw [hidx] at h
    rw [h]
  have htopstep : ∀ d, 1 ≤ d → d ≤ e' * ew → φ (e' * e - (d - 1) * eK) - φ (e' * e - (d - 1) * eK - 1) = σ d := by
    intro d hd1 hd
    have hA := σ_spec d hd1 hd eK le_rfl
    have hB := σ_spec d hd1 hd (eK - 1) (by omega)
    have hde := hgrid d hd
    have hidx : e' * e - d * eK + eK = e' * e - (d - 1) * eK := by
      have : (d - 1) * eK + eK = d * eK := by
        rw [Nat.sub_mul, one_mul]; exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hd1)
      omega
    have hidx' : e' * e - d * eK + (eK - 1) = e' * e - (d - 1) * eK - 1 := by omega
    rw [hidx] at hA; rw [hidx'] at hB
    rw [hA, hB]
    rw [Nat.cast_sub heK]
    push_cast
    ring
  have hcum : ∀ d, d ≤ e' * ew → φ (e' * e - d * eK) - φ (e' * e) = -(eK : ℤ) * ∑ i ∈ Finset.Icc 1 d, σ i := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
        have h1 := ih (by omega)
        have h2 := htopblk (d + 1) (by omega) hd
        simp only [Nat.add_sub_cancel] at h2
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ d + 1)]
        linear_combination h1 - h2
  have hGd : ∀ d, d ≤ e' * ew → G d = -∑ i ∈ Finset.Icc 1 d, σ i := by
    intro d hd
    rw [hG d, hcum d hd]
    have heK0 : (eK : ℤ) ≠ 0 := by exact_mod_cast (show eK ≠ 0 by omega)
    rw [show -(eK : ℤ) * ∑ i ∈ Finset.Icc 1 d, σ i = (eK : ℤ) * (-∑ i ∈ Finset.Icc 1 d, σ i) by ring,
      Int.mul_ediv_cancel_left _ heK0]
  have hGstep : ∀ d, 1 ≤ d → d ≤ e' * ew → G d - G (d - 1) = -σ d := by
    intro d hd1 hd
    rw [hGd d hd, hGd (d - 1) (by omega)]
    have : Finset.Icc 1 d = Finset.Icc 1 (d - 1 + 1) := by rw [Nat.sub_add_cancel hd1]
    rw [this, Finset.sum_Icc_succ_top (by omega : 1 ≤ d - 1 + 1), Nat.sub_add_cancel hd1]
    ring
  have hN1 : 1 ≤ e' * ew := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h0 : e' * e - e' * ew * eK = 0 := by rw [hTN, Nat.sub_self]
  have hraw1 : G 1 - G 0 = -(φ (e' * e) - φ (e' * e - 1)) := by
    rw [hGstep 1 le_rfl hN1]
    have := htopstep 1 le_rfl hN1
    simp only [Nat.sub_self, zero_mul, Nat.sub_zero] at this
    rw [← this]
  have hraw2 : G (e' * ew) - G (e' * ew - 1) = -(φ 1 - φ 0) := by
    rw [hGstep (e' * ew) hN1 le_rfl]
    simp only [hσ]
    rw [h0, zero_add]
  refine ⟨?_, ?_, ?_, ?_, hraw1, hraw2⟩
  · intro d hd
    rw [hcum d hd]
    exact ⟨-∑ i ∈ Finset.Icc 1 d, σ i, by ring⟩
  · intro d hd
    rw [Finset.mem_Ico] at hd
    have h3 := hGstep (d + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at h3
    rw [hGstep d hd.1 (by omega), h3]
    have h1 : σ (d + 1) = φ (e' * e - d * eK) - φ (e' * e - d * eK - 1) := by
      have := htopstep (d + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this
      exact this.symm
    have hde := hgrid d (by omega)
    have hde1 := hgrid (d + 1) (by omega)
    have h2 := hint' (e' * e - d * eK) (by
      have : d * eK + eK = (d + 1) * eK := by ring
      omega) (by
      have : 1 ≤ d * eK := Nat.le_mul_of_pos_left _ hd.1 |>.trans' heK |> fun h => by nlinarith
      omega)
    rw [← h2, h1]
    simp only [hσ]
    ring
  · rw [hGstep 1 le_rfl hN1]
    have := htopstep 1 le_rfl hN1
    simp only [Nat.sub_self, zero_mul, Nat.sub_zero] at this
    rw [← this, htop']
  · have h := hGstep (e' * ew) hN1 le_rfl
    rw [h]
    simp only [hσ]
    rw [h0, zero_add, hbot']

#print axioms solution

end S_ModularCurve_UVCrossingModel_gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq_scaled (solution)
