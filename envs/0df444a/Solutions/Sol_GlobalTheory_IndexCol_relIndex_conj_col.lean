-- Prove2me | solution 1 for GlobalTheory.IndexCol.relIndex_conj_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:09.87058+00:00
-- url     : https://prove2.me/submissions/d2dffdb6-c8c8-4e0a-8a7a-30ee42b064d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
import Theorems.Thm_GlobalTheory_IndexCol_mem_maximalIdeal_iff
import Theorems.Thm_GlobalTheory_IndexCol_col_inv_mul_iff
import Theorems.Thm_GlobalTheory_IndexCol_mem_conj_iff

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
open GlobalTheory GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.IndexCol
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S →
    ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ r, r ∉ S → x.val r t = (1 : Matrix ι ι k) r t) →
    (∀ y : ι → k, (∀ r, y r ∈ 𝒪[k]) → (∀ r, r ∉ S → y r = 0) →
      ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0)) →
    ((KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ))⁻¹)).toMonoidHom).relIndex H = resCard k ^ S.card := by
  intro k _ _ _ _ ι _ _ ϖ hϖ t S ht H hH hcol hel
  set A := (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom with hA

  have hQ0 : ∀ z ∈ H, (∀ r, r ≠ t → valuation k (z.val r t) < 1) ↔
      ∀ s, valuation k ((z.val - 1) s t) < 1 := by
    intro z hz
    constructor
    · intro h s
      by_cases hs : s = t
      · subst hs; rw [Matrix.sub_apply, hcol z hz s ht, sub_self, map_zero]; exact zero_lt_one
      · rw [Matrix.sub_apply, Matrix.one_apply_ne hs, sub_zero]; exact h s hs
    · intro h r hr
      simpa [Matrix.sub_apply, Matrix.one_apply_ne hr] using h r
  have hQ : ∀ z ∈ H, z ∈ A ↔ ∀ s, valuation k ((z.val - 1) s t) < 1 := by
    intro z hz
    have hzi : z⁻¹ ∈ H := H.inv_mem hz
    rw [hA, mem_conj_iff hϖ t (hH hz), hQ0 z hz, hQ0 _ hzi]
    have e := col_inv_mul_iff (hH hz) 1 t
    rw [mul_one] at e
    rw [e]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun s => ?_⟩
      have h1 := h s
      rw [Matrix.sub_apply] at h1 ⊢
      rw [← Valuation.map_neg, neg_sub, Units.val_one]; exact h1
  have hres : ∀ x y : 𝒪[k], IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y ↔
      valuation k ((x : k) - y) < 1 := fun x y => by
    have h1 := mem_maximalIdeal_iff (x - y)
    push_cast at h1
    rw [← h1]; exact Ideal.Quotient.eq
  let φ : H → (S → 𝓀[k]) := fun x r =>
    IsLocalRing.residue 𝒪[k] ⟨x.1.val r t, ((mem_KO_iff _).1 (hH x.2)).1 r t⟩
  have hφ : ∀ a b : H, φ a = φ b ↔ a⁻¹ * b ∈ A.subgroupOf H := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      hQ _ (H.mul_mem (H.inv_mem a.2) b.2), col_inv_mul_iff (hH a.2), funext_iff]
    simp only [φ, hres]
    constructor
    · intro h s
      by_cases hs : s ∈ S
      · rw [Matrix.sub_apply, ← Valuation.map_neg, neg_sub]; exact h ⟨s, hs⟩
      · rw [Matrix.sub_apply, hcol b b.2 s hs, hcol a a.2 s hs, sub_self, map_zero]; exact zero_lt_one
    · intro h r
      have := h r
      rwa [Matrix.sub_apply, ← Valuation.map_neg, neg_sub] at this
  let f : H ⧸ A.subgroupOf H → (S → 𝓀[k]) :=
    Quotient.lift φ (fun a b hab => (hφ a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hf : Function.Bijective f := by
    constructor
    · intro p q
      induction p using QuotientGroup.induction_on
      induction q using QuotientGroup.induction_on
      intro h
      exact QuotientGroup.eq.2 ((hφ _ _).1 h)
    · intro c
      choose u hu using fun r : S => IsLocalRing.residue_surjective (c r)
      let y : ι → k := fun r => if h : r ∈ S then (u ⟨r, h⟩ : k) else 0
      obtain ⟨x, hxH, hx⟩ := hel y (fun r => by
          by_cases h : r ∈ S
          · simp only [y, h, dif_pos]; exact (u _).2
          · simp only [y, h, dif_neg, not_false_eq_true]; exact zero_mem _)
        (fun r hr => by simp [y, hr])
      refine ⟨QuotientGroup.mk ⟨x, hxH⟩, ?_⟩
      funext r
      have hr : (r : ι) ≠ t := fun h => ht (h ▸ r.2)
      have e : x.val r t = u r := by
        rw [hx]; simp [y, hr, r.2]
      show IsLocalRing.residue 𝒪[k] ⟨x.val r t, _⟩ = c r
      rw [← hu r]; congr 1; exact Subtype.ext e
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun,
    Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
  rfl
end GlobalTheory.IndexCol
