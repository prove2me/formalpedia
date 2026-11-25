-- Prove2me | solution 1 for GlobalTheory.FlagEich.eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:07.42499+00:00
-- url     : https://prove2.me/submissions/010e45be-01ce-4a82-af17-697e77990e84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_pairR
import Theorems.Thm_GlobalTheory_FlagEich_hf_sum_l
import Theorems.Thm_GlobalTheory_FlagEich_zero_of
import Theorems.Thm_GlobalTheory_FlagEich_mem_Nof
import Theorems.Thm_GlobalTheory_FlagEich_gsg
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FlagEich
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FlagEich
theorem _root_.solution {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g)
    (hfix : ∀ a : Fin r, n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) : n = 1 := by
  rw [mem_Nof] at hn
  obtain ⟨hiso, -, hp⟩ := hn
  have hiso' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := hiso
  refine LinearEquiv.ext fun v => ?_
  show n v = v
  obtain ⟨w, hw⟩ : ∃ w, w = v - ∑ a : Fin r, hf L S.Hm v (g a.castSucc) • gs a := ⟨_, rfl⟩
  have hwp : w ∈ perp L S.Hm (S.spanTo g r) := by
    show ∀ y ∈ S.spanTo g r, hf L S.Hm w y = 0
    refine pairR S le_rfl w (fun c _ => ?_)
    rw [hw, hf_sub_l, hf_sum_l]
    simp only [hf_smul_l, gsg S H1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, sub_self]
  have ht : n w - w ∈ S.spanTo g r := hp.2 w hwp
  have h0 : n w - w = 0 := zero_of S H1 _ ht (fun a => by
    have := hiso' w (gs a)
    rw [(hfix a).2] at this
    rw [hf_sub_l, this, sub_self])
  have hnw : n w = w := sub_eq_zero.mp h0
  have hv : v = w + ∑ a : Fin r, hf L S.Hm v (g a.castSucc) • gs a := by rw [hw, sub_add_cancel]
  conv_lhs => rw [hv]
  rw [map_add, map_sum, hnw]
  simp only [map_smul, (hfix _).2]
  exact hv.symm
end GlobalTheory.FlagEich
