-- Prove2me | solution 1 for OAI.Saxl.altWord_fiber_relabel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:27:41.851291+00:00
-- url     : https://prove2.me/submissions/7525c51f-5314-4cb3-9ec0-561c62a83c39

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


theorem solution {n m d : ℕ} {α : Type uAlpha}
    (e : Fin n ≃ Fin m) (c : Fin m → α) (a : Fin m → Fin d) (w : Fin n → Fin d) :
    altWord (fiberGroup c) a (w ∘ e.symm) =
      altWord (fiberGroup (c ∘ e)) (a ∘ e) w := by
  classical
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply]
  symm
  refine Finset.sum_nbij' (fiberRelabel e c) (fiberRelabel e c).symm (fun _ _ => by simp)
    (fun _ _ => by simp) (fun x _ => by simp) (fun x _ => by simp) (fun g _ => ?_)
  have hs : signC ((fiberRelabel e c g : fiberGroup c) : Equiv.Perm (Fin m)) =
      signC (g : Equiv.Perm (Fin n)) := by
    simp [fiberRelabel, signC_def, Equiv.Perm.sign_permCongr]
  rw [hs]
  congr 1
  change (Pi.single (a ∘ e) (1:ℂ) : WordSpace n d) (w ∘ (g : Equiv.Perm (Fin n))) =
    (Pi.single a (1:ℂ) : WordSpace m d)
      ((w ∘ e.symm) ∘ ((fiberRelabel e c g : fiberGroup c) : Equiv.Perm (Fin m)))
  have hcomp : (w ∘ e.symm) ∘ ((fiberRelabel e c g : fiberGroup c) : Equiv.Perm (Fin m)) =
      (w ∘ (g : Equiv.Perm (Fin n))) ∘ e.symm := by
    funext x; simp [fiberRelabel, Equiv.permCongr]
  rw [hcomp]
  simp only [Pi.single_apply]
  have : (w ∘ (g : Equiv.Perm (Fin n))) ∘ e.symm = a ↔ w ∘ (g : Equiv.Perm (Fin n)) = a ∘ e := by
    constructor
    · intro h; rw [← h]; funext x; simp
    · intro h; rw [h]; funext x; simp
  split_ifs <;> simp_all

