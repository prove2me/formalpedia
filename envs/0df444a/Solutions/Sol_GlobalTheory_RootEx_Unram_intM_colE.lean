-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.intM_colE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:13.852086+00:00
-- url     : https://prove2.me/submissions/34ace446-2058-45b1-83db-910c03f94c4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_intM_one
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.Unram
theorem _root_.solution {p : ℕ} (hp : p + 1 ≤ c) (β : n → k) (x₀ : Matrix n n' k) (e) :
    IntM (((colE c (p + 1) β)⁻¹).val * affPt (c := c) (p + 1) x₀ e) ↔
      IntM (affPt (c := c) (p + 1) x₀ e) ∧ ∀ r, β r ∈ 𝒪[k] := by
  have hK : (∀ r, β r ∈ 𝒪[k]) → colE c (p + 1) β ∈ KO k (n ⊕ Fin c) := fun hβ => by
    have : IntM (Matrix.of fun r (i : Fin c) => if i.val + 1 = p + 1 then β r else 0) := fun r i => by
      simp only [Matrix.of_apply]
      split_ifs
      exacts [hβ r, zero_mem _]
    refine mem_KO.2 ⟨?_, ?_⟩
    · rintro (r | r) (s | s)
      exacts [intM_one r s, this r s, zero_mem _, intM_one r s]
    · rintro (r | r) (s | s)
      exacts [intM_one r s, this.neg r s, zero_mem _, intM_one r s]
  constructor
  · intro h
    have hβ : ∀ r, β r ∈ 𝒪[k] := fun r => by
      have h1 := h (Sum.inl r) (Sum.inr (Fin.castSucc ⟨p, hp⟩))
      rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr ⟨p, hp⟩)] at h1
      · have : -β r ∈ 𝒪[k] := by simpa [affPt, basePt, Free, colE, upU] using h1
        simpa using neg_mem this
      · rintro (s | s) _ hs
        · simp [affPt, basePt, Free]
        · have : s.val ≠ p := fun e => hs (by rw [Fin.ext (show s.val = (⟨p, hp⟩ : Fin c).val from e)])
          simp [colE, upU, this]
      · simp
    refine ⟨?_, hβ⟩
    have := (mem_KO.1 (hK hβ)).1.mul h
    rwa [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at this
  · rintro ⟨h, hβ⟩
    exact (mem_KO.1 (hK hβ)).2.mul h
end GlobalTheory.RootEx.Unram
