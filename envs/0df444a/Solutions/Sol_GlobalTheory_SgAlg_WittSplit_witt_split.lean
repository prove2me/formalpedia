-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittSplit.witt_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:02:54.636246+00:00
-- url     : https://prove2.me/submissions/3833094c-6540-42a8-8006-83bba035ebe3

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
import Theorems.Thm_GlobalTheory_SgAlg_WittSplit_witt_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
namespace GlobalTheory.SgAlg.WittSplit
theorem _root_.solution : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ →
    (∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e) →
    ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J →
    ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' →
    ∃ g, IsUn σ J g ∧ g * X = X' := by
  intro E _ σ hQA hsplit n a J hJ X X' hX hX' hG
  obtain ⟨e, he2, he1, hef⟩ := hsplit
  have hee' : e * σ e = 0 := by linear_combination e * he1 - he2
  set I : Ideal E := Ideal.span {σ e} with hIdef
  have hmemI : ∀ z, z * σ e ∈ I := fun z => Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hmax : I.IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    refine ⟨⟨0, 1, ?_⟩, fun x y => mul_comm x y, ?_⟩
    · intro h
      have h1 : (1 : E) ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact h.symm
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
      have he0 : e = 0 := by linear_combination -e * hc + c * hee'
      have h01 : (0 : E) = 1 := by rw [← he1, he0, map_zero, add_zero]
      obtain ⟨z, hz⟩ := hQA.2.1
      haveI := subsingleton_of_zero_eq_one h01
      exact hz (Subsingleton.elim _ _)
    · intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hex : e * x ≠ 0 := by
        intro h0; apply hx; rw [Ideal.Quotient.eq_zero_iff_mem]
        have : x = x * σ e := by linear_combination h0 - x * he1
        rw [this]; exact hmemI x
      obtain ⟨y, hy⟩ := hef x hex
      refine ⟨Ideal.Quotient.mk I y, ?_⟩
      rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
      have : x * y - 1 = (x * y - 1) * σ e := by linear_combination hy - (x * y - 1) * he1
      rw [this]; exact hmemI _
  letI : Field (E ⧸ I) := Ideal.Quotient.field I
  have hpe : Ideal.Quotient.mk I e = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have : e - 1 = (-1) * σ e := by linear_combination he1
    rw [this]; exact hmemI _
  let s : E ⧸ I → E := fun f => e * (Ideal.Quotient.mk_surjective f).choose
  have hs1 : ∀ f, Ideal.Quotient.mk I (s f) = f := by
    intro f; simp only [s, map_mul, hpe, one_mul]; exact (Ideal.Quotient.mk_surjective f).choose_spec
  have hs2 : ∀ x, s (Ideal.Quotient.mk I x) = e * x := by
    intro x
    have hc := (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk I x)).choose_spec
    set y := (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk I x)).choose
    rw [Ideal.Quotient.eq] at hc
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 hc
    show e * y = e * x
    linear_combination e * hc'.symm + c * hee'
  exact witt_of_field σ hQA.1 e he2 he1 (Ideal.Quotient.mk I) s hs1 hs2 J hJ X X' hX hX' hG
end GlobalTheory.SgAlg.WittSplit
