-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:36.130401+00:00
-- url     : https://prove2.me/submissions/2c9dd10a-a8d8-43b9-bacc-e93e88c19c05

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (W : ι → Prop) (p q : ι)
    (h1 : ∀ w, W w → Φ p w ∧ Φ w q) :
    Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (W x.1 ∧ x.2 = q)} =
      Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (x.1 = p ∧ W x.2)} := by
  classical
  let R : Finset (ι × ι) := Finset.univ.filter fun x => Φ x.1 x.2
  let Wf : Finset ι := Finset.univ.filter W
  let A : Finset (ι × ι) := Wf.image fun w => (w, q)
  let B : Finset (ι × ι) := Wf.image fun w => (p, w)
  have hA : A ⊆ R := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 w (Finset.mem_filter.1 hw).2).2⟩
  have hB : B ⊆ R := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (h1 w (Finset.mem_filter.1 hw).2).1⟩
  have cA : A.card = Wf.card := Finset.card_image_of_injective _ fun a b h => (Prod.ext_iff.1 h).1
  have cB : B.card = Wf.card := Finset.card_image_of_injective _ fun a b h => (Prod.ext_iff.1 h).2
  have c1 : Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (W x.1 ∧ x.2 = q)} = (R \ A).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext ⟨a, b⟩
    simp only [R, A, Wf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image,
      Prod.mk.injEq, not_exists, not_and]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, fun w hw hwa hq => h' (hwa ▸ hw) hq.symm⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, fun hW hb => h' a hW rfl hb.symm⟩
  have c2 : Nat.card {x : ι × ι // Φ x.1 x.2 ∧ ¬ (x.1 = p ∧ W x.2)} = (R \ B).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext ⟨a, b⟩
    simp only [R, B, Wf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image,
      Prod.mk.injEq, not_exists, not_and]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, fun w hw hp hwb => h' hp.symm (hwb ▸ hw)⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, fun hp hW => h' b hW hp.symm rfl⟩
  have s1 := Finset.card_sdiff_add_card_eq_card hA
  have s2 := Finset.card_sdiff_add_card_eq_card hB
  rw [c1, c2]
  omega
end GlobalTheory.CompanionTheory.RootExch
