-- Prove2me | solution 1 for OAI.Saxl.altWord_letter_eval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:24:58.170415+00:00
-- url     : https://prove2.me/submissions/a29b19e9-1796-4682-99d9-10c7cad5929e

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation

open OAI OAI.Saxl
open scoped TensorProduct
universe uAlpha


theorem solution {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (G : Subgroup (Equiv.Perm (Fin n))) (a w : Fin n → Fin d) :
    altWord G (φ ∘ a) (φ ∘ w) = altWord G a w := by
  classical
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change (Pi.single (φ ∘ a) (1:ℂ) : WordSpace n D) ((φ ∘ w) ∘ (g : Equiv.Perm (Fin n))) =
    (Pi.single a (1:ℂ) : WordSpace n d) (w ∘ (g : Equiv.Perm (Fin n)))
  simp only [Pi.single_apply]
  have : φ ∘ w ∘ (g : Equiv.Perm (Fin n)) = φ ∘ a ↔ w ∘ (g : Equiv.Perm (Fin n)) = a :=
    (Function.Injective.comp_left hφ).eq_iff
  rw [Function.comp_assoc]
  split_ifs <;> simp_all

