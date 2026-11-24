-- Prove2me | solution 1 for GlobalTheory.finite_jumps_inf_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:02.679868+00:00
-- url     : https://prove2.me/submissions/37a5b3a7-dc5c-4682-a661-7b40b3d14912

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteJumpsInfFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E W : Type) [Field E] [AddCommGroup W] [Module E W]
    (D : Submodule E W) (F : ℤ → Submodule E W) (hD : Module.Finite E ↥D)
    (hF : ∀ a, F (a + 1) ≤ F a) :
    {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  have hanti : Antitone F := antitone_int_of_succ_le hF
  have hfin : ∀ a, Module.Finite E ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := D) inf_le_left
  have key : ∀ a b : ℤ, D ⊓ F (a + 1) ≠ D ⊓ F a → a < b →
      Module.finrank E ↥(D ⊓ F b) < Module.finrank E ↥(D ⊓ F a) := by
    intro a b ha hab
    haveI := hfin a
    apply Submodule.finrank_lt_finrank_of_lt
    have h1 : D ⊓ F b ≤ D ⊓ F (a + 1) := inf_le_inf_left _ (hanti (by omega))
    have h2 : D ⊓ F (a + 1) < D ⊓ F a := lt_of_le_of_ne (inf_le_inf_left _ (hF a)) ha
    exact lt_of_le_of_lt h1 h2
  refine Set.Finite.of_injOn (f := fun a => Module.finrank E ↥(D ⊓ F a))
    (t := Set.Iic (Module.finrank E ↥D)) ?_ ?_ (Set.finite_Iic _)
  · intro a _
    exact Submodule.finrank_mono inf_le_left
  · intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (key a b ha h).ne'
    · exact h
    · exact absurd hab (key b a hb h).ne
end GlobalTheory
