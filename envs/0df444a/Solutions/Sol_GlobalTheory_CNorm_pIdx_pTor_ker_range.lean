-- Prove2me | solution 1 for GlobalTheory.CNorm.pIdx_pTor_ker_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:22:50.15055+00:00
-- url     : https://prove2.me/submissions/7705eeb5-f9a0-443b-83ce-8fe55f3605f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
import Theorems.Thm_GlobalTheory_CNorm_pTor_eq_card_inf_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p g.ker ≠ 0 → pTor p g.ker ≠ 0 → pIdx p g.range ≠ 0 → pTor p g.range ≠ 0 → pIdx p (⊤ : Subgroup A) ≠ 0 ∧ pTor p (⊤ : Subgroup A) ≠ 0 ∧ pIdx p (⊤ : Subgroup A) * pTor p g.ker * pTor p g.range = pIdx p g.ker * pIdx p g.range * pTor p (⊤ : Subgroup A) := by
  intro p A A' _ _ g hIK hTK hIR hTR
  have hcomm : (powMonoidHom p : A' →* A').comp g = g.comp (powMonoidHom p : A →* A) := by
    ext a; simp [map_pow]
  have hRp : pows p g.range = (powMonoidHom p : A →* A).range.map g := by
    simp only [pows, MonoidHom.range_eq_map, Subgroup.map_map, hcomm]
  have hKpow : g.ker.map (powMonoidHom p : A →* A) ≤ g.ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact g.ker.pow_mem hk p

  have eA : pIdx p (⊤ : Subgroup A) =
      (powMonoidHom p : A →* A).range.relIndex g.ker * pIdx p g.range := by
    have h1 : pIdx p (⊤ : Subgroup A) = (powMonoidHom p : A →* A).range.index := by
      rw [pIdx, Subgroup.relIndex_top_right, pows, ← MonoidHom.range_eq_map]
    rw [h1, ← Subgroup.relIndex_mul_index
      (le_sup_left : (powMonoidHom p : A →* A).range ≤ (powMonoidHom p : A →* A).range ⊔ g.ker),
      Subgroup.relIndex_sup_left, ← Subgroup.comap_map_eq, Subgroup.index_comap, pIdx, hRp]

  have eK : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex
      ((powMonoidHom p : A →* A).range ⊓ g.ker) * (powMonoidHom p : A →* A).range.relIndex g.ker := by
    have h0 : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex g.ker := rfl
    rw [h0, ← Subgroup.relIndex_mul_relIndex _ ((powMonoidHom p : A →* A).range ⊓ g.ker) _
      (le_inf (Subgroup.map_le_range _ _) hKpow) inf_le_right, Subgroup.inf_relIndex_right]

  have hB : g.ker.comap (powMonoidHom p : A →* A) = (powMonoidHom p : A' →* A').ker.comap g := by
    ext a; simp [MonoidHom.mem_ker, map_pow]
  have hKB : g.ker ≤ g.ker.comap (powMonoidHom p : A →* A) := fun x hx => g.ker.pow_mem hx p
  have hQB : (powMonoidHom p : A →* A).ker ≤ g.ker.comap (powMonoidHom p : A →* A) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simp [Subgroup.mem_comap, hx]

  have eR : pTor p g.range = g.ker.relIndex (powMonoidHom p : A →* A).ker *
      (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
    have h1 : pTor p g.range = g.ker.relIndex (g.ker.comap (powMonoidHom p : A →* A)) := by
      rw [pTor_eq_card_inf_ker, Subgroup.relIndex_ker, hB, Subgroup.map_comap_eq]
    have h2 : (g.ker ⊔ (powMonoidHom p : A →* A).ker).relIndex
        (g.ker.comap (powMonoidHom p : A →* A)) =
        (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
      rw [← Subgroup.comap_map_eq, Subgroup.relIndex_comap, Subgroup.map_comap_eq]
    rw [h1, ← Subgroup.relIndex_mul_relIndex g.ker (g.ker ⊔ (powMonoidHom p : A →* A).ker) _
      le_sup_left (sup_le hKB hQB), h2,
      Subgroup.relIndex_sup_left]

  have eT : pTor p (⊤ : Subgroup A) = pTor p g.ker * g.ker.relIndex (powMonoidHom p : A →* A).ker := by
    have h := Subgroup.relIndex_mul_relIndex ⊥ (g.ker ⊓ (powMonoidHom p : A →* A).ker)
      (powMonoidHom p : A →* A).ker bot_le inf_le_right
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] at h
    rw [pTor_eq_card_inf_ker, pTor_eq_card_inf_ker, top_inf_eq, ← h]
  rw [eK] at hIK ⊢
  rw [eR] at hTR ⊢
  rw [eA, eT]
  refine ⟨mul_ne_zero (right_ne_zero_of_mul hIK) hIR, mul_ne_zero hTK (left_ne_zero_of_mul hTR), ?_⟩
  ring
end GlobalTheory.CNorm
