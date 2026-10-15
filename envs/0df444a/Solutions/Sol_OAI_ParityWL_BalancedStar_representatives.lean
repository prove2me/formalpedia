-- Prove2me | solution 1 for OAI.ParityWL.BalancedStar.representatives
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:18:53.829981+00:00
-- url     : https://prove2.me/submissions/6fbb768b-9f1d-4994-81b3-7995ef70ed4a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/BalancedBags.lean:L88-L105
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.BalancedStar.representatives. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Theorems.Thm_OAI_ParityWL_WeightedWitness_main_mass

-- ---- from OAI.Combinatorics.ParityLifts.Masses ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section Masses

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

lemma WeightedWitness.mass_eq_zero (w : WeightedWitness T F a b)
    (Y : Finset W) (u : A) (h : ∀ x ∈ Y, a x ≠ u) : w.mass Y u = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp [h x hx]

end Masses

section TemplateMass

open scoped Classical

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t}

end TemplateMass

section BoundaryTests

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

end BoundaryTests

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.BalancedBags ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section BalancedBags

open scoped Classical

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t} {b : TemplateVertex t → Bit}

lemma sum_regions {n : ℕ} (region : W → Option (Fin n)) (f : W → Bit) :
    ∑ x, f x = (∑ x ∈ regionSet region none, f x) +
      ∑ i, ∑ x ∈ regionSet region (some i), f x := by
  rw [← Finset.sum_fiberwise Finset.univ region f, Fintype.sum_option]
  rfl

lemma BalancedStar.partition_mass (w : WeightedWitness (template t) F a b)
    (s : BalancedStar w) (u : TemplateVertex t) :
    w.mass Finset.univ u = w.mass s.bag u +
      ∑ i, w.mass (regionSet s.region (some i)) u := by
  rw [s.bag_eq]
  exact sum_regions s.region (fun x => @ite Bit (a x = u)
    (Classical.propDecidable _) (w.vertex x) 0)

lemma BalancedStar.main_present (w : WeightedWitness (template t) F a (starParity t))
    (s : BalancedStar w) (ht : 0 < t) (i : Fin t) :
    ∃ x ∈ s.bag, a x = .inl i := by
  by_contra h
  push Not at h
  have hb := w.mass_eq_zero s.bag (.inl i) h
  have hz : ∀ j, w.mass (regionSet s.region (some j)) (.inl i) = 0 := by
    intro j
    exact s.zero_mass j i (fun x hx => h x (s.separator_sub j hx))
  have hm := s.partition_mass w (.inl i)
  rw [w.main_mass ht i, hb] at hm
  simp only [hz, Finset.sum_const_zero, add_zero] at hm
  exact one_ne_zero hm

lemma BalancedStar.representatives (w : WeightedWitness (template t) F a (starParity t))
    (s : BalancedStar w) (ht : 0 < t) :
    ∃ x : Fin t → W, (∀ i, a (x i) = .inl i) ∧
      s.bag = Finset.univ.image x := by
  choose x hx ha using s.main_present w ht
  have hinj : Function.Injective x := by
    intro i j he
    have hh : Sum.inl i = (Sum.inl j : TemplateVertex t) :=
      (ha i).symm.trans ((congrArg a he).trans (ha j))
    exact Sum.inl.inj hh
  refine ⟨x, ha, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hx i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact s.size

end BalancedBags

section MismatchPredicates

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t) {W : Type} {F : SimpleGraph W}
variable (φ : F →g baseGraph C)

end MismatchPredicates

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.BalancedStar.representatives := @_root_.OAI.ParityWL.BalancedStar.representatives
