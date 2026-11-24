-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.integral_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:03:07.298436+00:00
-- url     : https://prove2.me/submissions/4aa9666a-aa69-4e26-9eb2-3dcf6b819e6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_integral_comp_blocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_ext_free
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_left_inl
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_left_inr
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_left_affPt
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_ch_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
omit [DecidableEq n']
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (A : Matrix n n k) (u : kˣ) (hu : A.det = u)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun x => Φ ((fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x)) x₀ =
      ((nabs k u ^ Fintype.card {i : Fin (c + 1) // p < i.val + 1})⁻¹ : ℝ) • opE ψ ν p Φ (A * x₀) := by
  classical
  unfold opE
  rw [← integral_comp_blocks ν
    (fun x : n × {i : Fin (c + 1) // p < i.val + 1} =>
      (⟨(Sum.inl x.1, Sum.inr x.2.1), x.2.2⟩ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}))
    ?_ A u hu (TL p A) ?_ ?_]
  · simp only [← left_affPt, ch_left]
    rfl
  · rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
    have h' := congrArg Subtype.val h
    simp only [Subtype.mk.injEq, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h' ⊢
    exact h'
  · intro e r j
    simp only [TL, left_inl]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ext_free p e (Sum.inl t) (Sum.inr j.1) j.2]
  · rintro e ⟨⟨r | r, s⟩, h⟩ hf
    · rcases s with s | s
      · exact h.elim
      · exact (hf ⟨(r, ⟨s, h⟩), rfl⟩).elim
    · simp only [TL, left_inr]
      rw [ext_free]
end GlobalTheory.RootEx.OpELevi
