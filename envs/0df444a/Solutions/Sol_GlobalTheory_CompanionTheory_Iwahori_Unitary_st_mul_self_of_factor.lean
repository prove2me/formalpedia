-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:14:04.575806+00:00
-- url     : https://prove2.me/submissions/6f1bc8f1-8657-4481-ac30-8c9e5aa441db

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_upper_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_lowerUni_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_lowerUni_of_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_eq_one_of_upper_lowerUni
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_st_upper
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_st_lowerUni

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Unitary
variable {E ι : Type} [Ring E] [Fintype ι]
namespace GlobalTheory.CompanionTheory.Iwahori.Unitary
theorem _root_.solution : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ (rev : ι → ι), (∀ i, rev (rev i) = i) → (∀ i j, wt i < wt j → wt (rev j) < wt (rev i)) → Function.Injective wt → ∀ (st : E → E), (∀ a b, st (a * b) = st b * st a) → st 1 = 1 → st 0 = 0 → (∀ i, st (P i) = P (rev i)) → (∀ a a' : E, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a') → (∀ b b' : E, b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b') → ∀ a a' b b' : E, a * a' = 1 → a' * a = 1 → b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b → st (a * b) * (a * b) = 1 → (a * b) * st (a * b) = 1 → st a * a = 1 ∧ st b * b = 1 := by
  intro E ι _ _ wt P hP rev hrev hord hw st hmul h1 h0 hst hU hL a a' b b' haa' ha'a hbb' hb'b ha hb hs hs'
  have ha'U : IsUpper wt P a' := hU a a' haa' ha'a ha
  have hb'Uni : IsLowerUni wt P b' := lowerUni_of_inv hP hw hb (hL b b' hbb' hb'b hb.1) hbb'
  have ha2U : IsUpper wt P (st a') := st_upper hrev hord hmul h0 hst ha'U
  have hstb : IsLowerUni wt P (st b) := st_lowerUni hrev hord hmul h0 hst hb

  have e1 : st a * st a' = 1 := by rw [← hmul, ha'a, h1]
  have e2 : st b' * st b = 1 := by rw [← hmul, hbb', h1]
  have e3 : st b * st b' = 1 := by rw [← hmul, hb'b, h1]

  have e4 : st a' * st b' = a * b := by
    have h2 : st (a * b) * (st a' * st b') = 1 := by
      rw [hmul a b, mul_assoc (st b), ← mul_assoc (st a), e1, one_mul, e3]
    calc st a' * st b' = (a * b) * st (a * b) * (st a' * st b') := by rw [hs', one_mul]
      _ = a * b := by rw [mul_assoc, h2, mul_one]
  have e5 : st a' = a * b * st b := by
    rw [← e4, mul_assoc, e2, mul_one]

  have e6 : a' * st a' = b * st b := by
    have h3 : a' * (a * b * st b) = (a' * a) * b * st b := by simp only [mul_assoc]
    rw [e5, h3, ha'a, one_mul]
  have hc : a' * st a' = 1 :=
    eq_one_of_upper_lowerUni hP hw (upper_mul hP ha'U ha2U)
      (e6 ▸ lowerUni_mul hP hw hb hstb)
  have e7 : st a' = a := by
    calc st a' = a * a' * st a' := by rw [haa', one_mul]
      _ = a := by rw [mul_assoc, hc, mul_one]
  have e8 : st b' = b := by
    have : a * st b' = a * b := by rw [← e4, e7]
    calc st b' = a' * a * st b' := by rw [ha'a, one_mul]
      _ = a' * a * b := by rw [mul_assoc, this, mul_assoc]
      _ = b := by rw [ha'a, one_mul]
  rw [e7] at e1
  rw [e8] at e3
  exact ⟨e1, e3⟩
end GlobalTheory.CompanionTheory.Iwahori.Unitary
