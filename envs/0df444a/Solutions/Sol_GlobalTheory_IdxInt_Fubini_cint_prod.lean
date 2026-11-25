-- Prove2me | solution 1 for GlobalTheory.IdxInt.Fubini.cint_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:58.834745+00:00
-- url     : https://prove2.me/submissions/9b6f45de-3f9f-42bd-bab6-5448baf2d49c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubini
import Theorems.Thm_GlobalTheory_IdxInt_Fubini_relIndex_prod
import Theorems.Thm_GlobalTheory_IdxInt_Fubini_exists_fine_prod
import Theorems.Thm_GlobalTheory_IdxInt_Model_cint_eq
import Theorems.Thm_GlobalTheory_IdxInt_Model_out_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Fubini
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
namespace GlobalTheory.IdxInt.Fubini
theorem _root_.solution (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ)
    (h : Nice (A.prod A') φ) :
    (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧
      cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  obtain ⟨B, B', hB, hB', i1, i2, hF⟩ := exists_fine_prod h
  let e := QuotientAddGroup.prodEquiv B B'
  have he : ∀ p : W × W', e (QuotientAddGroup.mk p) =
      ((QuotientAddGroup.mk p.1 : W ⧸ B), (QuotientAddGroup.mk p.2 : W' ⧸ B')) := fun _ => rfl
  have hS := hF.2.2.2.image e
  have f1 : ∀ w, Fine A' (fun w' => φ (w, w')) B' := by
    intro w
    refine ⟨hB', i2, fun w' b hb => ?_, (hS.image Prod.snd).subset ?_⟩
    · have := hF.2.2.1 (w, w') (0, b) ⟨B.zero_mem, hb⟩
      simpa using this
    · rintro _ ⟨w', hw', rfl⟩
      exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  have hinv : ∀ w, ∀ b ∈ B, (fun w' => φ (w + b, w')) = fun w' => φ (w, w') := by
    intro w b hb
    funext w'
    have := hF.2.2.1 (w, w') (b, 0) ⟨hb, B'.zero_mem⟩
    simpa using this
  have f2 : Fine A (fun w => cint A' (fun w' => φ (w, w'))) B := by
    refine ⟨hB, i1, fun w b hb => by simp only [hinv w b hb], (hS.image Prod.fst).subset ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have : ∃ w', φ (w, w') ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hw
      show cint A' (fun w' => φ (w, w')) = 0
      rw [Model.cint_eq (f1 w)]
      simp [hn]
    obtain ⟨w', hw'⟩ := this
    exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  refine ⟨fun w => ⟨B', f1 w⟩, ⟨B, f2⟩, ?_⟩
  rw [Model.cint_eq hF, Model.cint_eq f2, relIndex_prod]
  simp only [fun w => Model.cint_eq (f1 w)]
  have h1 : ∀ p : (W ⧸ B) × (W' ⧸ B'), φ (e.symm p).out = φ (p.1.out, p.2.out) := by
    intro p
    have : e.symm p = QuotientAddGroup.mk (p.1.out, p.2.out) := by
      rw [Equiv.symm_apply_eq, he]
      simp
    rw [this, Model.out_mk hF.2.2.1]
  have hfin : (Function.support fun p : (W ⧸ B) × (W' ⧸ B') => φ (p.1.out, p.2.out)).Finite := by
    refine hS.subset ?_
    intro p hp
    refine ⟨_, ⟨(p.1.out, p.2.out), hp, rfl⟩, ?_⟩
    rw [he]; simp
  have h2 : (∑ᶠ c : (W × W') ⧸ B.prod B', φ c.out) =
      ∑ᶠ (a : W ⧸ B) (b : W' ⧸ B'), φ (a.out, b.out) := by
    rw [← finsum_comp_equiv e.symm, finsum_congr h1, finsum_curry _ hfin]
  rw [h2]
  simp only [div_eq_mul_inv]
  rw [← finsum_mul]
  push_cast
  rw [mul_inv]
  ring
end GlobalTheory.IdxInt.Fubini
