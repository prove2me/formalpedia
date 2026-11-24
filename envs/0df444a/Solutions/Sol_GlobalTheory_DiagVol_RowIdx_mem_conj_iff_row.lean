-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.mem_conj_iff_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:07.839855+00:00
-- url     : https://prove2.me/submissions/c3d0ffbf-a1bb-411f-af02-61ff74baf5ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_row_inv_iff
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_residue_eq_zero_iff_of_isUnif
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_mem_map_conj_iff
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_conj_int_iff
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_red_incl_val
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_red_row_off

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.DiagVol GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.DiagVol.RowIdx
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) {t : ι}
    {S : Finset ι} (htS : t ∉ S) (hrow : ∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) (z : H) :
    (z : GL ι k) ∈ (KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom ↔
      (red (Subgroup.inclusion hHK z)).val t = (1 : Matrix ι ι 𝓀[k]) t := by
  set ρ : H →* GL ι 𝓀[k] := red.comp (Subgroup.inclusion hHK) with hρ
  have hint : ∀ w : H, ∀ r s, (w : GL ι k).val r s ∈ 𝒪[k] := fun w => ((mem_KO_iff _).1 (hHK w.2)).1

  have key : ∀ w : H, (∀ s, s ≠ t → (ϖ : k)⁻¹ * (w : GL ι k).val t s ∈ 𝒪[k]) ↔ (ρ w).val t = (1 : Matrix ι ι 𝓀[k]) t := by
    intro w
    constructor
    · intro h
      funext s
      by_cases hs : s = t
      · subst hs; exact red_row_off hHK hrow w s htS
      · show (red (Subgroup.inclusion hHK w)).val t s = _
        rw [red_incl_val hHK w t s (hint w t s), (residue_eq_zero_iff_of_isUnif hϖ _ _).2 (h s hs)]
        simp [Matrix.one_apply, Ne.symm hs]
    · intro h s hs
      have h1 := congrFun h s
      have h2 : (red (Subgroup.inclusion hHK w)).val t s = 0 := by
        rw [show (red (Subgroup.inclusion hHK w)).val t s = (ρ w).val t s from rfl, h1]
        simp [Matrix.one_apply, Ne.symm hs]
      rw [red_incl_val hHK w t s (hint w t s)] at h2
      exact (residue_eq_zero_iff_of_isUnif hϖ _ _).1 h2
  rw [mem_map_conj_iff, mem_KO_iff]
  have hinv : ((diagGL (Pi.mulSingle t ϖ))⁻¹ * (z : GL ι k) * diagGL (Pi.mulSingle t ϖ))⁻¹ =
      (diagGL (Pi.mulSingle t ϖ))⁻¹ * ((z⁻¹ : H) : GL ι k) * diagGL (Pi.mulSingle t ϖ) := by
    simp [mul_assoc]
  rw [hinv, conj_int_iff hϖ t _ (hint z), conj_int_iff hϖ t _ (hint z⁻¹)]
  change _ ↔ (ρ z).val t = _
  rw [key z, key z⁻¹]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := (row_inv_iff (1 : GL ι 𝓀[k]) (ρ z) t).1 (by simpa using h)
    rw [map_inv, ← this]; simp
end GlobalTheory.DiagVol.RowIdx
