-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.exists_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:06.840008+00:00
-- url     : https://prove2.me/submissions/917855ac-d7b0-4094-8975-733b3b518827

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_PeriodOnto_exists_frame
import Theorems.Thm_GlobalTheory_PeriodOnto_kap_apply
import Theorems.Thm_GlobalTheory_PeriodOnto_blockOf_apply
import Theorems.Thm_GlobalTheory_PeriodOnto_isUnit_block
import Theorems.Thm_GlobalTheory_PeriodOnto_im_form_eq
import Theorems.Thm_GlobalTheory_PeriodOnto_block_sign

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
namespace GlobalTheory.PeriodOnto
theorem _root_.solution {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ) {Λ : Type}
    (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (e : ι → Λ → Fin r → ℂ) (M : ι → Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ v t, blockOf idx q t (P v) = M t *ᵥ e t v) (G : ι → Matrix (Fin r) (Fin r) ℂ)
    (hGH : ∀ t, (G t).IsHermitian) (s : ι → ℝ) (hs : ∀ t, 0 < s t) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (h : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t, -2 * s t * (e t x ⬝ᵥ G t *ᵥ star (e t y)).im)
    (t : ι) :
    ∃ x : Matrix (Fin r) (Fin r) ℂ, x.det ≠ 0 ∧ (sgnMat r q * (xᵀ * G t * x.map conj)).PosDef ∧
      ∀ (v : Λ) (a : Fin r), P v (idx.symm (t, a)) =
        if (a : ℕ) < q then conj ((e t v ᵥ* (G t * x.map conj)) a) else (x⁻¹ *ᵥ e t v) a := by
  have hex : ∀ t, ∃ Mi : Matrix (Fin r) (Fin r) ℂ, M t * Mi = 1 := fun t =>
    (isUnit_block idx q P hspan e M hM t).exists_right_inv
  choose Mi hMi using hex
  have he : ∀ v t, e t v = Mi t *ᵥ blockOf idx q t (P v) := by
    intro v t
    rw [hM, mulVec_mulVec, mul_eq_one_comm.mp (hMi t), one_mulVec]
  let A : ι → Matrix (Fin r) (Fin r) ℂ := fun t => (Mi t)ᵀ * G t * (Mi t).map conj
  have hAH : ∀ t, (A t).IsHermitian := by
    intro t
    have : (Mi t)ᵀ = ((Mi t).map conj)ᴴ := by ext a b; simp [conjTranspose_apply]
    simp only [A]
    rw [this]
    exact isHermitian_conjTranspose_mul_mul _ (hGH t)
  have hform : ∀ (t : ι) (u w : Fin r → ℂ),
      (Mi t *ᵥ u) ⬝ᵥ G t *ᵥ star (Mi t *ᵥ w) = u ⬝ᵥ A t *ᵥ star w := by
    intro t u w
    have : star (Mi t *ᵥ w) = (Mi t).map conj *ᵥ star w := by
      ext a; simp [mulVec, dotProduct]
    simp only [A]
    rw [this, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]
  have hmain : ∀ x y, (hermForm Hm (P x) (P y)).im = ∑ t, -2 * s t *
      (blockOf idx q t (P x) ⬝ᵥ A t *ᵥ star (blockOf idx q t (P y))).im := by
    intro x y
    rw [h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [he x, he y, hform]
  have hsign := block_sign idx q A hAH s hs Hm hpos (im_form_eq idx q P hspan A s Hm hmain) t
  obtain ⟨x, hx0, hx1, hx2⟩ := exists_frame (G t) (M t) (Mi t) (hMi t) hsign.1 hsign.2
  refine ⟨x, hx0, hx1, fun v a => ?_⟩
  have h1 := congrFun (hM v t) a
  rw [blockOf_apply, kap_apply] at h1
  by_cases ha : (a : ℕ) < q
  · rw [if_pos ha] at h1 ⊢
    rw [(hx2 (e t v) a).1 ha, ← h1, Complex.conj_conj]
  · rw [if_neg ha] at h1 ⊢
    rw [(hx2 (e t v) a).2 ha, h1]
end GlobalTheory.PeriodOnto
