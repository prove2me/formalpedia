-- Prove2me | solution 1 for GlobalTheory.QRefl.exists_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:41.631372+00:00
-- url     : https://prove2.me/submissions/479ce4f0-84a0-4551-917f-d6ed9f14b06b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLattice
import Theorems.Thm_GlobalTheory_QRefl_hf_add_left
import Theorems.Thm_GlobalTheory_QRefl_hf_add_right
import Theorems.Thm_GlobalTheory_QRefl_hf_smul_left
import Theorems.Thm_GlobalTheory_QRefl_hf_smul_right
import Theorems.Thm_GlobalTheory_QRefl_hf_zero_left
import Theorems.Thm_GlobalTheory_QRefl_hf_zero_right
import Theorems.Thm_GlobalTheory_QRefl_cj_hf
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermOrthBasis_cj_hf
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_add_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_add_right
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.QRefl
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.QRefl
theorem _root_.solution (hH : IsHerm L Hm) {ι : Type} [Fintype ι] (b : ι → Fin n → E)
    (hb : Submodule.span E (Set.range b) = ⊤) (hu : ∀ i, IsUnit (hf L Hm (b i) (b i)))
    (ho : ∀ i j, i ≠ j → hf L Hm (b i) (b j) = 0) :
    ∃ c : (Fin n → E) →+ (Fin n → E), (∀ t v, c (t • v) = L.cj t • c v) ∧ (∀ v, c (c v) = v) ∧
      (∀ v w, hf L Hm (c v) (c w) = L.cj (hf L Hm v w)) ∧ ∀ i, c (b i) = b i := by
  let c : (Fin n → E) →+ (Fin n → E) := AddMonoidHom.mk'
    (fun v => ∑ i, (hf L Hm (b i) v * ↑(hu i).unit⁻¹) • b i) (fun u v => by
      simp only [hf_add_right, add_mul, add_smul, Finset.sum_add_distrib])
  have hcv : ∀ v, c v = ∑ i, (hf L Hm (b i) v * ↑(hu i).unit⁻¹) • b i := fun v => rfl
  have hs : ∀ t v, c (t • v) = L.cj t • c v := fun t v => by
    simp only [hcv, hf_smul_right, Finset.smul_sum, smul_smul, mul_assoc]
  have hbi : ∀ i, c (b i) = b i := fun i => by
    rw [hcv, Finset.sum_eq_single i]
    · rw [IsUnit.mul_val_inv, one_smul]
    · intro j _ hj
      rw [ho j i hj, zero_mul, zero_smul]
    · simp
  have hmem : ∀ v, v ∈ Submodule.span E (Set.range b) := fun v => hb ▸ Submodule.mem_top
  refine ⟨c, hs, fun v => ?_, fun v w => ?_, hbi⟩
  · induction hmem v using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; rw [hbi, hbi]
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add, map_add, h1, h2]
    | smul t x _ h => rw [hs, hs, L.cj_cj, h]
  · induction hmem v using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      induction hmem w using Submodule.span_induction with
      | mem _ h =>
        obtain ⟨j, rfl⟩ := h
        rw [hbi, hbi, cj_hf L Hm hH]
        by_cases hij : i = j
        · rw [hij]
        · rw [ho i j hij, ho j i (Ne.symm hij)]
      | zero => simp [hf_zero_right]
      | add x y _ _ h1 h2 => rw [map_add, hf_add_right, hf_add_right, h1, h2, map_add]
      | smul t x _ h => rw [hs, hf_smul_right, hf_smul_right, h, map_mul]
    | zero => simp [hf_zero_left]
    | add x y _ _ h1 h2 => rw [map_add, hf_add_left, hf_add_left, h1, h2, map_add]
    | smul t x _ h => rw [hs, hf_smul_left, hf_smul_left, h, map_mul]
end GlobalTheory.QRefl
