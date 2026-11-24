-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.relIndex_rowCong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:02.708156+00:00
-- url     : https://prove2.me/submissions/634b10e3-5848-4b43-807d-763ab06421ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_row_inv_iff
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_red_incl_val
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_red_row_off
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_mem_conj_iff_row

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
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S →
    ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) →
    (∀ y : ι → k, (∀ s, y s ∈ 𝒪[k]) → (∀ s, s ∉ S → y s = 0) →
      ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0)) →
    ((KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom).relIndex H = resCard k ^ S.card := by
  intro k _ _ _ _ ι _ _ ϖ hϖ t S htS H hHK hrow hel
  set A := (KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom with hA
  set ρ : H →* GL ι 𝓀[k] := red.comp (Subgroup.inclusion hHK) with hρ
  have hint : ∀ w : H, ∀ r s, (w : GL ι k).val r s ∈ 𝒪[k] := fun w => ((mem_KO_iff _).1 (hHK w.2)).1
  let F : H → (S → 𝓀[k]) := fun x s => (ρ x⁻¹).val t s
  have hF : ∀ x y : H, F x = F y ↔ ((x⁻¹ * y : H) : GL ι k) ∈ A := by
    intro x y
    rw [mem_conj_iff_row hϖ hHK htS hrow]
    change _ ↔ (ρ (x⁻¹ * y)).val t = _
    rw [map_mul, map_inv, row_inv_iff, ← map_inv, ← map_inv]
    constructor
    · intro h
      funext s
      by_cases hs : s ∈ S
      · exact congrFun h ⟨s, hs⟩
      · rw [show (ρ x⁻¹).val t s = (red (Subgroup.inclusion hHK x⁻¹)).val t s from rfl,
          show (ρ y⁻¹).val t s = (red (Subgroup.inclusion hHK y⁻¹)).val t s from rfl,
          red_row_off hHK hrow _ s hs, red_row_off hHK hrow _ s hs]
    · intro h
      funext s
      exact congrFun h s.1
  have hsurj : Function.Surjective F := by
    intro w
    choose lift hlift using fun s : S => IsLocalRing.residue_surjective (R := 𝒪[k]) (w s)
    let y : ι → k := fun s => if h : s ∈ S then ((lift ⟨s, h⟩ : 𝒪[k]) : k) else 0
    obtain ⟨z, hzH, hz⟩ := hel y (fun s => by
        by_cases h : s ∈ S
        · simp only [y, h, dif_pos]; exact (lift ⟨s, h⟩).2
        · simp only [y, h, dif_neg, not_false_eq_true]; exact Subring.zero_mem _)
      (fun s hs => by simp [y, hs])
    refine ⟨(⟨z, hzH⟩ : H)⁻¹, ?_⟩
    funext s
    have hst : t ≠ s.1 := fun h => htS (h ▸ s.2)
    show (red (Subgroup.inclusion hHK ((⟨z, hzH⟩ : H)⁻¹)⁻¹)).val t s = w s
    rw [inv_inv, red_incl_val hHK _ t s (hint _ t s)]
    have e : (⟨((⟨z, hzH⟩ : H) : GL ι k).val t s, hint _ t s⟩ : 𝒪[k]) = lift s := by
      apply Subtype.ext
      show z.val t s = _
      rw [hz]
      simp [y, Matrix.one_apply, hst, s.2]
    rw [e, hlift]
  have hcard : Nat.card (H ⧸ A.subgroupOf H) = Nat.card (S → 𝓀[k]) := by
    refine Nat.card_congr (Equiv.ofBijective (Quotient.lift F fun a b hab => (hF a b).2 ?_) ⟨?_, ?_⟩)
    · have := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using this
    · intro a b
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      intro h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact (hF _ _).1 h
    · intro w
      obtain ⟨x, hx⟩ := hsurj w
      exact ⟨QuotientGroup.mk x, hx⟩
  rw [Subgroup.relIndex, Subgroup.index, hcard, Nat.card_fun, resCard, Nat.card_eq_fintype_card (α := S),
    Fintype.card_coe]
end GlobalTheory.DiagVol.RowIdx
