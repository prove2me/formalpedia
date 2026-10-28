-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.EOKO_edgeMats_of_PE
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:45:33.489984+00:00
-- url     : https://prove2.me/submissions/f4c0344f-33c6-4a5e-b8b6-797b431befe7

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunFormalOK
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_edgeMat_eq
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_good_mats
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open Matrix Finset
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (Dm Pl nestOK K rkC)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet (PE oneRun pickE)
open IntMul.Kappa.R8.Bit.Oppbank.SupG (codeBound)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunFormalOK

noncomputable instance : DecidableEq (QMat2 529) := Classical.decEq _

noncomputable def EM0 : Finset (QMat2 529) :=
  E0.image Edge.E₁ ∪ E0.image Edge.E₂

private theorem mem_E0_of_e1 (b o c : ℕ) (heq : ch0NB.e1 b o c = pickE (PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c)))) :
    pickE (PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c))) ∈ E0 := by
  have h := e1_mem b o c
  -- ch0.e1 = ch0O.e1 = ch0NB.e1
  have : ch0.e1 b o c = ch0NB.e1 b o c := by
    simp only [ch0, ch0NB, OneRunNet.toNB]
  rw [this, heq] at h; exact h

private theorem mem_E0_of_e2 (a o c : ℕ) (heq : ch0NB.e2 a o c = pickE (PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c)))) :
    pickE (PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c))) ∈ E0 := by
  have h := e2_mem a o c
  have : ch0.e2 a o c = ch0NB.e2 a o c := by
    simp only [ch0, ch0NB, OneRunNet.toNB]
  rw [this, heq] at h; exact h

private theorem mem_E0_of_ex (b : ℕ) (heq : ch0NB.ex b = pickE (PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22))) :
    pickE (PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22)) ∈ E0 := by
  have h := ex_mem b
  have : ch0.ex b = ch0NB.ex b := by simp only [ch0, ch0NB, OneRunNet.toNB]
  rw [this, heq] at h; exact h

private theorem mem_E0_of_en (a t : ℕ) (heq : ch0NB.en a t = pickE (PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484))) :
    pickE (PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484)) ∈ E0 := by
  have h := en_mem a t
  have : ch0.en a t = ch0NB.en a t := by simp only [ch0, ch0NB, OneRunNet.toNB]
  rw [this, heq] at h; exact h

private theorem mem_E0_of_ei (a : ℕ) (heq : ch0NB.ei a = pickE (PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22))) :
    pickE (PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22)) ∈ E0 := by
  have h := ei_mem a
  have : ch0.ei a = ch0NB.ei a := by simp only [ch0, ch0NB, OneRunNet.toNB]
  rw [this, heq] at h; exact h

private theorem mem_E0_of_ec (a s : ℕ) (heq : ch0NB.ec a s = pickE (PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1))) :
    pickE (PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1)) ∈ E0 := by
  have h := ec_mem a s
  have : ch0.ec a s = ch0NB.ec a s := by simp only [ch0, ch0NB, OneRunNet.toNB]
  rw [this, heq] at h; exact h

theorem solution
    (hPE :
      (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        ∃ e, PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c)) e) ∧
      (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c)) e) ∧
      (∀ b < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22) e) ∧
      (∀ a < 1771, ∀ t < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484) e) ∧
      (∀ a < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22) e) ∧
      (∀ a < 1771, ∀ s < 1771, ∃ e, PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1) e)) :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f,
      let N := q ^ f
      (∀ b < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        edgeMat N (ch0NB.e1 b o c) = redM N (pswQ (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)))) ∧
      (∀ a < 1771, ∀ o < codeBound, ∀ c < codeBound, nestOK o c = true →
        edgeMat N (ch0NB.e2 a o c) = redM N (pswQ (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)))) ∧
      (∀ b < 1771, edgeMat N (ch0NB.ex b) = redM N (pswQ (K ch0NB.S ch0NB.Si 1 (1 - Pl b)))) ∧
      (∀ a < 1771, ∀ t < 1771, edgeMat N (ch0NB.en a t) =
        redM N (pswQ (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)))) ∧
      (∀ a < 1771, edgeMat N (ch0NB.ei a) = redM N (pswQ (K ch0NB.S ch0NB.Si (1 - Pl a) 1))) ∧
      (∀ a < 1771, ∀ s < 1771, edgeMat N (ch0NB.ec a s) =
        redM N (pswQ (K ch0NB.S ch0NB.Si (Pl a) (Pl s)))) := by
  obtain ⟨h1, h2, hx, hn, hi, hc⟩ := hPE
  obtain ⟨qM, hM⟩ := good_mats EM0
  refine ⟨qM, fun q hq hlt f => ?_⟩
  let N := q ^ f
  have goodFac (e : Edge 529) (he : e ∈ E0) : GoodM N e.E₁ ∧ GoodM N e.E₂ := by
    have m1 : e.E₁ ∈ EM0 := mem_union.2 (Or.inl (mem_image.2 ⟨e, he, rfl⟩))
    have m2 : e.E₂ ∈ EM0 := mem_union.2 (Or.inr (mem_image.2 ⟨e, he, rfl⟩))
    exact ⟨fun i j => (hM q hq hlt f e.E₁ m1 i j).1,
           fun i j => (hM q hq hlt f e.E₂ m2 i j).1⟩
  refine ⟨?e1, ?e2, ?ex, ?en, ?ei, ?ec⟩
  · intro b hb o ho c hc' hnest
    have hPE' := h1 b hb o ho c hc' hnest
    have hv : b < v := by simpa [v] using hb
    have heq : ch0NB.e1 b o c =
        pickE (PE (K ch0NB.S ch0NB.Si (Dm o c) (Pl b)) (oneRun (rkC o c))) := by
      simp only [ch0NB, OneRunNet.toNB]
      change (if b < v ∧ o < OneRunNet.codeBound ∧ c < OneRunNet.codeBound then _ else _) = _
      have : OneRunNet.codeBound = codeBound := rfl
      rw [this, if_pos ⟨hv, ho, hc'⟩]; rfl
    rw [heq]
    exact edgeMat_eq (pickE_spec hPE').1 (goodFac _ (mem_E0_of_e1 b o c heq)).1
      (goodFac _ (mem_E0_of_e1 b o c heq)).2
  · intro a ha o ho c hc' hnest
    have hPE' := h2 a ha o ho c hc' hnest
    have hv : a < v := by simpa [v] using ha
    have heq : ch0NB.e2 a o c =
        pickE (PE (K ch0NB.S ch0NB.Si (Pl a) (Dm o c)) (oneRun (rkC o c))) := by
      simp only [ch0NB, OneRunNet.toNB]
      change (if a < v ∧ o < OneRunNet.codeBound ∧ c < OneRunNet.codeBound then _ else _) = _
      have : OneRunNet.codeBound = codeBound := rfl
      rw [this, if_pos ⟨hv, ho, hc'⟩]; rfl
    rw [heq]
    exact edgeMat_eq (pickE_spec hPE').1 (goodFac _ (mem_E0_of_e2 a o c heq)).1
      (goodFac _ (mem_E0_of_e2 a o c heq)).2
  · intro b hb
    have hPE' := hx b hb
    have hv : b < v := by simpa [v] using hb
    have heq : ch0NB.ex b =
        pickE (PE (K ch0NB.S ch0NB.Si 1 (1 - Pl b)) (oneRun 22)) := by
      simp only [ch0NB, OneRunNet.toNB]
      change (if b < v then _ else _) = _
      rw [if_pos hv]; rfl
    rw [heq]
    exact edgeMat_eq (pickE_spec hPE').1 (goodFac _ (mem_E0_of_ex b heq)).1
      (goodFac _ (mem_E0_of_ex b heq)).2
  · intro a ha t ht
    have hPE' := hn a ha t ht
    have hva : a < v := by simpa [v] using ha
    have hvt : t < v := by simpa [v] using ht
    have heq : ch0NB.en a t =
        pickE (PE (K ch0NB.S ch0NB.Si (1 - Pl a) (1 - Pl t)) (oneRun 484)) := by
      simp only [ch0NB, OneRunNet.toNB]
      change (if a < v ∧ t < v then _ else _) = _
      rw [if_pos ⟨hva, hvt⟩]; rfl
    rw [heq]
    exact edgeMat_eq (pickE_spec hPE').1 (goodFac _ (mem_E0_of_en a t heq)).1
      (goodFac _ (mem_E0_of_en a t heq)).2
  · intro a ha
    have hPE' := hi a ha
    have hv : a < v := by simpa [v] using ha
    have heq : ch0NB.ei a =
        pickE (PE (K ch0NB.S ch0NB.Si (1 - Pl a) 1) (oneRun 22)) := by
      simp only [ch0NB, OneRunNet.toNB]
      change (if a < v then _ else _) = _
      rw [if_pos hv]; rfl
    rw [heq]
    exact edgeMat_eq (pickE_spec hPE').1 (goodFac _ (mem_E0_of_ei a heq)).1
      (goodFac _ (mem_E0_of_ei a heq)).2
  · intro a ha s hs
    have hPE' := hc a ha s hs
    have hva : a < v := by simpa [v] using ha
    have hvs : s < v := by simpa [v] using hs
    have heq : ch0NB.ec a s =
        pickE (PE (K ch0NB.S ch0NB.Si (Pl a) (Pl s)) (oneRun 1)) := by
      simp only [ch0NB, OneRunNet.toNB]
      change (if a < v ∧ s < v then _ else _) = _
      rw [if_pos ⟨hva, hvs⟩]; rfl
    rw [heq]
    exact edgeMat_eq (pickE_spec hPE').1 (goodFac _ (mem_E0_of_ec a s heq)).1
      (goodFac _ (mem_E0_of_ec a s heq)).2
