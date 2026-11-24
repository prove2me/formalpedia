-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.qStructure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:14:27.453752+00:00
-- url     : https://prove2.me/submissions/631c597e-6b55-44b2-b0ea-970883cf50af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_GlobalTheory_Ex_QStr_exists_lift
import Theorems.Thm_GlobalTheory_Ex_QStr_root_over
import Theorems.Thm_GlobalTheory_Ex_QStr_ker_struct
import Theorems.Thm_GlobalTheory_Ex_QStr_orth_iff
import Theorems.Thm_GlobalTheory_T_degenerationWeilPairing_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
namespace GlobalTheory.Ex.QStr
theorem _root_.solution : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (n g : ℕ), (n : C) ≠ 0 → N.Tors n g → ∀ j : ℕ, (∀ b : N.A, ∃ γ : N.Gt, γ.b = b) ∧ (∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n ^ j = γ) ∧ (∀ y : N.X, ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) ∧ Nonempty ((powMonoidHom (n ^ j) : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin (2 * g + Module.finrank ℤ N.X) → ZMod (n ^ j))) ∧ (∀ p : N.QT (n ^ j), (∀ p' : N.QT (n ^ j), p'.1.1 = 1 → N.wp p p' = 1) ↔ ∃ p₀ : N.QT (n ^ j), N.QEq p p₀ ∧ p₀.1.1 = 1 ∧ p₀.1.2.b = 1) ∧ ∀ p : N.QT (n ^ j), (∀ p', N.wp p p' = 1) → N.QEq p 1 := by
  intro C _ _ N n g hn hT j
  have hk : ((n ^ j : ℕ) : C) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hn
  have hk0 : n ^ j ≠ 0 := fun h => hk (by rw [h, Nat.cast_zero])
  have hdiv : ∀ (i : ℕ) (x : N.A), ∃ y, y ^ n ^ i = x := by
    intro i
    induction i with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ i ih =>
      intro x
      obtain ⟨y, rfl⟩ := ih x
      obtain ⟨z, rfl⟩ := hT.div y
      exact ⟨z, by rw [pow_succ', pow_mul]⟩
  have h2 : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n ^ j = γ := fun γ => by
    obtain ⟨b, hb⟩ := hdiv j γ.b
    obtain ⟨γ', -, h⟩ := root_over N hk0 γ b hb
    exact ⟨γ', h⟩
  have h3 : ∀ y : N.X, ∃ p : N.QT (n ^ j), p.1.1.toAdd = y := fun y => by
    obtain ⟨γ, h⟩ := h2 (N.io y)
    exact ⟨⟨(Multiplicative.ofAdd y, γ), h⟩, rfl⟩
  obtain ⟨e⟩ := hT.str j
  refine ⟨exists_lift N, h2, h3, ker_struct N hk _ e, orth_iff N hk (hT.nondeg j), fun p hp => ?_⟩
  obtain ⟨p₀, hq, h1, hb⟩ := (orth_iff N hk (hT.nondeg j) p).1 fun p' _ => hp p'
  have : p₀ = 1 := by
    refine Subtype.ext (Prod.ext h1 (NumD.Gt.ext hb (funext fun χ => ?_)))
    obtain ⟨p', rfl⟩ := h3 χ
    rw [← (GlobalTheory.T.degenerationWeilPairing_properties C N _ p₀ p' p').2.2.2.2.2.1 h1 hb, ← (GlobalTheory.T.degenerationWeilPairing_properties C N _ p p₀ p').2.2.2.2.1 hq, hp p']
    rfl
  rwa [this] at hq
end GlobalTheory.Ex.QStr
