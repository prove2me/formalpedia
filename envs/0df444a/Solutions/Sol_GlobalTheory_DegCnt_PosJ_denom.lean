-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:49:11.414803+00:00
-- url     : https://prove2.me/submissions/f6931052-a270-4bda-9e3b-0dc08dc75467

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_wden
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_ipow_zero
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_ipow_mul
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_one_mem_ipow
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_mem_ipow_of
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_B_vec
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_exists_mono
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_OrbitDenom_block_of
import Theorems.Thm_GlobalTheory_OrbitDenom_entry_symm
import Theorems.Thm_GlobalTheory_OrbitDenom_unit_cut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open GlobalTheory.HL Matrix Formalism.MainNotions.S.Loc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution (𝔠 : Ideal (𝓞 K))
    (hD : ∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠,
      ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K))
    (A B : Matrix (Fin N.j) (Fin N.j) K) (hA : IsUni A) (hB : IsUni B)
    (hA0 : ∀ a b : Fin N.j, sameBlock N.w.blocks a b = true → a ≠ b → A a b = 0)
    (hZ : ∀ a b : Fin N.j, H.B (vec (ej N.F N.j_le) A a) (vec (ej N.F' N.j_le) B b) ∈
      ipow N.𝔡 (((r : ℤ) - (a : ℕ)) + ((r : ℤ) - (b : ℕ)))) (a b : Fin N.j) :
    (∀ x ∈ 𝔠, (x : K) * A b a ∈ ipow N.𝔡 (((r : ℤ) - (a : ℕ)) - ((r : ℤ) - (b : ℕ)))) ∧
    ∀ x ∈ 𝔠, ∀ x' ∈ 𝔠, (x : K) * x' * star (B b a) ∈ ipow N.𝔡 (((r : ℤ) - (a : ℕ)) - ((r : ℤ) - (b : ℕ))) := by
  obtain ⟨l', l, t, e1, e2, e3, e4, e5, e6, e7⟩ :=
    GlobalTheory.OrbitDenom.block_of N.w.blocks b (by rw [N.w.size]; exact b.2)
  rw [N.w.size] at e3
  have e3' : l' ≤ N.j := by omega
  set W : Matrix (Fin N.j) (Fin N.j) K := Matrix.of fun a b => H.B (ej N.F N.j_le a) (ej N.F' N.j_le b) with hW
  have hWe : ∀ a b : Fin N.j, W a b = ptEntryL N.w.blocks a b * ((N.sgn b : ℤ) : K) := fun a b => N.pair a b
  have hc : ∀ a b : Fin N.j, l ≤ (a : ℕ) → (b : ℕ) < l → W a b = 0 := fun a b ha hb => by
    rw [hWe, e6 _ _ ha hb, zero_mul]
  have hc' : ∀ a b : Fin N.j, l' ≤ (a : ℕ) → (b : ℕ) < l' → W a b = 0 := fun a b ha hb => by
    rw [hWe, e7 _ _ ha hb, zero_mul]
  have hdet : W.det ≠ 0 := by
    obtain ⟨σ, β, c, hσ, -, -, -, hc, hW'⟩ := exists_mono N
    have : W * Matrix.of (fun p q => if q = σ p then (c q)⁻¹ else 0) = 1 := by
      ext p q
      simp only [hW, Matrix.mul_apply, Matrix.of_apply, hW', ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hσ]
      rcases eq_or_ne p q with h | h
      · subst h; simp [hc]
      · simp [h, h.symm]
    exact (Matrix.isUnit_det_of_right_inverse this).ne_zero
  obtain ⟨g1, g2⟩ := wden (fun n => (ipow N.𝔡 n).toAddSubgroup) (one_mem_ipow N.𝔡)
    (fun _ _ _ _ hx hy => ipow_mul N.𝔡_ne hx hy) e3 e3' r (fun a => (r : ℤ) - (a : ℕ)) (fun _ => rfl)
    Aᵀ W (B.map star) (fun p q h => hA.1 _ _ h) hA.2 (fun p q h => by simp [hB.1 _ _ h])
    (fun p => by simp [hB.2]) (fun p q => by rw [← B_vec]; exact hZ p q) hdet hc hc'
    (fun p q hp hq hne => by
      rcases lt_or_gt_of_ne hne with h | h
      · exact hA.1 _ _ h
      · have h' : (q : ℕ) < p := h
        exact hA0 _ _ (e4 _ _ hq (by omega) (by omega) hp) hne.symm)
    t (fun b => ((N.sgn b : ℤ) : K))
    (fun b => by
      rcases Int.units_eq_one_or (N.sgn b) with h | h
      · simpa [h] using one_mem_ipow N.𝔡
      · simpa [h] using one_mem_ipow N.𝔡)
    (fun b => by rcases Int.units_eq_one_or (N.sgn b) with h | h <;> simp [h])
    (fun a b hb' hb => by rw [hWe, GlobalTheory.OrbitDenom.entry_symm, e5 _ _ hb' hb, add_comm (b : ℕ) a])
    (fun a b ha' ha => by rw [hWe, e5 _ _ ha' ha]) b e1 e2 a
  have key : ∀ (m : ℕ) (hm : m ≤ N.j), (∀ a b : Fin N.j, m ≤ (a : ℕ) → (b : ℕ) < m → W a b = 0) →
      (W.submatrix (Fin.castLE hm) (Fin.castLE hm)).det ≠ 0 ∧
      ∀ x ∈ 𝔠, (x : K) / (W.submatrix (Fin.castLE hm) (Fin.castLE hm)).det ∈
        ipow N.𝔡 (-(2 * ∑ a : Fin m, ((r : ℤ) - ((Fin.castLE hm a : Fin N.j) : ℕ)))) := by
    intro m hm h0
    have h1 := (GlobalTheory.OrbitDenom.unit_cut hm W (IsUnit.mk0 _ hdet) h0).ne_zero
    refine ⟨h1, fun x hx => mem_ipow_of N.𝔡_ne (m := 2 * ∑ a ∈ Finset.range m, ((r : ℤ) - a)) fun y hy => ?_⟩
    have h2 := hD m (hm.trans (N.j_le.trans (Nat.le_succ r))) hm h1 x hx y hy
    have h3 : ∑ a : Fin m, ((r : ℤ) - ((Fin.castLE hm a : Fin N.j) : ℕ)) =
        ∑ a ∈ Finset.range m, ((r : ℤ) - a) := Fin.sum_univ_eq_sum_range (fun a : ℕ => (r : ℤ) - a) m
    rw [h3, add_neg_cancel, ipow_zero, ← mul_div_assoc, mul_comm y]
    exact h2
  obtain ⟨k1, k2⟩ := key l e3 hc
  obtain ⟨k3, k4⟩ := key l' e3' hc'
  refine ⟨fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · have := ipow_mul N.𝔡_ne (k2 x hx) g1
    convert this using 1
    · congr 1; ring
    · rw [Matrix.transpose_apply]; field_simp
  · have := ipow_mul N.𝔡_ne (k4 x' hx') (ipow_mul N.𝔡_ne (k2 x hx) g2)
    convert this using 1
    · congr 1; ring
    · rw [Matrix.map_apply]; field_simp
end GlobalTheory.DegCnt.PosJ
