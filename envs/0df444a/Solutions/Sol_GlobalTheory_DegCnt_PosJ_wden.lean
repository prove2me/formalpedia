-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.wden
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:31:36.657938+00:00
-- url     : https://prove2.me/submissions/caabfbfa-6adb-4ee8-8f58-da44b95d31d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_mono_mem
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_sc_mul
import Theorems.Thm_GlobalTheory_DegCnt_PosJ_sc_det
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_OrbitDenom_low_mem
import Theorems.Thm_GlobalTheory_OrbitDenom_up_mem
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
open LaurentPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution (I : ℤ → AddSubgroup K) (h1 : (1 : K) ∈ I 0)
    (hmul : ∀ m n x y, x ∈ I m → y ∈ I n → x * y ∈ I (m + n)) {n l' l : ℕ} (h : l ≤ n) (h' : l' ≤ n)
    (r : ℤ) (k : Fin n → ℤ) (hk : ∀ a, k a = r - (a : ℕ)) (A W B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ I (k a + k b)) (hW : W.det ≠ 0)
    (hc : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → W k b = 0)
    (hc' : ∀ k b : Fin n, l' ≤ (k : ℕ) → (b : ℕ) < l' → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → a ≠ b → A a b = 0)
    (t : K) (ε : Fin n → K) (hε : ∀ b, ε b ∈ I 0) (hε2 : ∀ b, ε b * ε b = 1)
    (hcol : ∀ a b : Fin n, l' ≤ (b : ℕ) → (b : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (hrow : ∀ a b : Fin n, l' ≤ (a : ℕ) → (a : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (i : Fin n) (hi' : l' ≤ (i : ℕ)) (hi : (i : ℕ) < l) (j : Fin n) :
    (W.submatrix (Fin.castLE h) (Fin.castLE h)).det * A j i ∈
        I (2 * ∑ a : Fin l, k (Fin.castLE h a) + (k j - k i)) ∧
      (W.submatrix (Fin.castLE h) (Fin.castLE h)).det * (W.submatrix (Fin.castLE h') (Fin.castLE h')).det *
        B i j ∈ I (2 * ∑ a : Fin l, k (Fin.castLE h a) + 2 * ∑ a : Fin l', k (Fin.castLE h' a) +
          (k j - k i)) := by
  set O := gradedSub I h1 hmul
  have gA : ∀ a b : Fin n, a < b → sc A k (-k) a b = 0 := fun a b hab => by simp [sc, hA a b hab]
  have class_group_mod_eq_torsion : ∀ a : Fin n, sc A k (-k) a a = 1 := fun a => by simp [sc, hA1]
  have gB : ∀ a b : Fin n, b < a → sc B (-k) k a b = 0 := fun a b hab => by simp [sc, hB a b hab]
  have gB1 : ∀ a : Fin n, sc B (-k) k a a = 1 := fun a => by simp [sc, hB1]
  have gZ : ∀ a b, (sc A k (-k) * sc W k k * sc B (-k) k) a b ∈ O := fun a b => by
    rw [sc_mul _ _ _ _ _ _ (by simp), sc_mul _ _ _ _ _ _ (by simp)]
    exact (mono_mem I h1 hmul _ _).2 (hZ a b)
  have gW : IsUnit (sc W k k).det := by
    rw [sc_det]
    exact ((IsUnit.mk0 _ hW).map _).mul (isUnit_T _)
  have gc : ∀ a b : Fin n, l ≤ (a : ℕ) → (b : ℕ) < l → sc W k k a b = 0 := fun a b ha hb => by
    simp [sc, hc a b ha hb]
  have gc' : ∀ a b : Fin n, l' ≤ (a : ℕ) → (b : ℕ) < l' → sc W k k a b = 0 := fun a b ha hb => by
    simp [sc, hc' a b ha hb]
  have gAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → sc A k (-k) a b ∈ O := fun a b ha hb => by
    by_cases e : a = b
    · rw [e, class_group_mod_eq_torsion]; exact O.one_mem
    · simp [sc, hAO a b ha hb e]
  have hd : ∀ (m : ℕ) (hm : m ≤ n), ((sc W k k).submatrix (Fin.castLE hm) (Fin.castLE hm)).det =
      C (W.submatrix (Fin.castLE hm) (Fin.castLE hm)).det * T (2 * ∑ a : Fin m, k (Fin.castLE hm a)) :=
    fun m hm => sc_det (W.submatrix (Fin.castLE hm) (Fin.castLE hm)) (fun a => k (Fin.castLE hm a))
  have ht : ∀ a b : Fin n, W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b →
      sc W k k a b = (if (a : ℕ) + b + 1 = l + l' then C t * T (2 * r + 1 - l - l') else 0) * C (ε b) := by
    intro a b e
    simp only [sc, Matrix.of_apply, e]
    split_ifs with e2
    · have : k a + k b = 2 * r + 1 - l - l' := by rw [hk, hk]; omega
      rw [this, map_mul]; ring
    · simp
  have g1 := GlobalTheory.OrbitDenom.low_mem O h _ _ _ gA class_group_mod_eq_torsion gB gB1 gZ gW gc gAO i hi' hi j
  have g2 := GlobalTheory.OrbitDenom.up_mem O h h' _ _ _ gA class_group_mod_eq_torsion gB gB1 gZ gW gc' gAO _ (fun b => C (ε b))
    (fun b => by simpa using (mono_mem I h1 hmul (ε b) 0).2 (hε b))
    (fun b => by rw [← map_mul, hε2, map_one])
    (fun a b hb' hb => ht a b (hcol a b hb' hb)) (fun a b ha' ha => ht a b (hrow a b ha' ha)) i hi' hi j
  rw [hd] at g1
  rw [hd, hd] at g2
  constructor
  · rw [← mono_mem I h1 hmul]
    convert g1 using 1
    simp only [sc, Matrix.of_apply, Pi.neg_apply, T_add, map_mul, sub_eq_add_neg]
    ring
  · rw [← mono_mem I h1 hmul]
    convert g2 using 1
    simp only [sc, Matrix.of_apply, Pi.neg_apply, T_add, map_mul, sub_eq_add_neg]
    ring
end GlobalTheory.DegCnt.PosJ
