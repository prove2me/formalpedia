-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.EOKO_GoodM_large2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:48:12.08338+00:00
-- url     : https://prove2.me/submissions/7b71a7ad-1699-4e43-adea-220c16bdb1d3

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_good_mats
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open Matrix Finset
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG

/-! GoodM_large2 via R6 `good_mats` on finite packs of S/Si and Pc/Pl. -/

noncomputable instance : DecidableEq (Matrix (Fin 529) Pr23 ℚ) := Classical.decEq _
noncomputable instance : DecidableEq (Matrix Pr23 (Fin 529) ℚ) := Classical.decEq _
noncomputable instance : DecidableEq M23 := Classical.decEq _

noncomputable def Spack : Finset (Matrix (Fin 529) Pr23 ℚ) := {ch0NB.S}
noncomputable def Sipack : Finset (Matrix Pr23 (Fin 529) ℚ) := {ch0NB.Si}
noncomputable def Mpack : Finset M23 :=
  (range codeBound).image Pc ∪ (range 1771).image Pl

theorem solution :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f,
      GoodM (q ^ f) ch0NB.S ∧ GoodM (q ^ f) ch0NB.Si ∧
        (∀ c < codeBound, GoodM (q ^ f) (Pc c)) ∧
          (∀ b < 1771, GoodM (q ^ f) (Pl b)) := by
  obtain ⟨qS, hS⟩ := good_mats Spack
  obtain ⟨qSi, hSi⟩ := good_mats Sipack
  obtain ⟨qM, hM⟩ := good_mats Mpack
  refine ⟨qS + qSi + qM, fun q hq hlt f => ?_⟩
  have hltS : qS < q := by omega
  have hltSi : qSi < q := by omega
  have hltM : qM < q := by omega
  have gS : GoodM (q ^ f) ch0NB.S := by
    intro i j
    exact (hS q hq hltS f ch0NB.S (mem_singleton_self _) i j).1
  have gSi : GoodM (q ^ f) ch0NB.Si := by
    intro i j
    exact (hSi q hq hltSi f ch0NB.Si (mem_singleton_self _) i j).1
  have gPc : ∀ c < codeBound, GoodM (q ^ f) (Pc c) := by
    intro c hc i j
    have hmem : Pc c ∈ Mpack := by
      refine mem_union.2 (Or.inl (mem_image.2 ⟨c, mem_range.2 hc, rfl⟩))
    exact (hM q hq hltM f (Pc c) hmem i j).1
  have gPl : ∀ b < 1771, GoodM (q ^ f) (Pl b) := by
    intro b hb i j
    have hmem : Pl b ∈ Mpack := by
      refine mem_union.2 (Or.inr (mem_image.2 ⟨b, mem_range.2 hb, rfl⟩))
    exact (hM q hq hltM f (Pl b) hmem i j).1
  exact ⟨gS, gSi, gPc, gPl⟩
