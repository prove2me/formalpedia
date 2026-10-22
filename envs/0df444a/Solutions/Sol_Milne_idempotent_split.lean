-- Prove2me | solution 1 for Milne.idempotent_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:13:41.951784+00:00
-- url     : https://prove2.me/submissions/97abfe35-f0f8-44f6-a732-41f90edd2f27

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta
universe u v

open Milne

theorem solution (W : CorrWorld.{u, v}) (M : MotElem W) (f : W.Corr M.X M.X)
    (hf : W.cc f f = f) (hdf : W.deg f = 0) (hfe : W.cc (W.cc M.e f) M.e = f) :
    ∃ i₁ : Hom W (idemCompl W M f hf hdf hfe) M,
      ∃ i₂ : Hom W (idemImg W M f hf hdf) M,
        ∃ p₁ : Hom W M (idemCompl W M f hf hdf hfe),
          ∃ p₂ : Hom W M (idemImg W M f hf hdf),
            homComp W i₁ p₁ = idM W (idemCompl W M f hf hdf hfe)
              ∧ homComp W i₂ p₂ = idM W (idemImg W M f hf hdf)
              ∧ homComp W i₂ p₁ =
                homZero W (idemImg W M f hf hdf) (idemCompl W M f hf hdf hfe)
              ∧ homComp W i₁ p₂ =
                homZero W (idemCompl W M f hf hdf hfe) (idemImg W M f hf hdf)
              ∧ homAdd W (homComp W p₁ i₁) (homComp W p₂ i₂) = idM W M := by
  set e := M.e with he_def
  have he : W.cc e e = e := M.idem
  -- f is absorbed by e on both sides
  have hef : W.cc e f = f := by
    have : W.cc e f = W.cc e (W.cc (W.cc e f) e) := by rw [hfe]
    rw [this, ← W.cc_assoc, ← W.cc_assoc, he, hfe]
  have hfe' : W.cc f e = f := by
    have : W.cc f e = W.cc (W.cc (W.cc e f) e) e := by rw [hfe]
    rw [this, W.cc_assoc, he, hfe]
  set E := W.add e (W.neg f) with hE_def
  have hEE : W.cc E E = E := W.compl_idem e f he hf hfe
  have heE : W.cc e E = E := by
    rw [hE_def, W.cc_add_right, W.cc_neg_right, he, hef]
  have hEe : W.cc E e = E := by
    rw [hE_def, W.cc_add_left, W.cc_neg_left, he, hfe']
  have hfE : W.cc f E = W.zero M.X M.X := by
    rw [hE_def, W.cc_add_right, W.cc_neg_right, hfe', hf, W.add_neg_cancel]
  have hEf : W.cc E f = W.zero M.X M.X := by
    rw [hE_def, W.cc_add_left, W.cc_neg_left, hef, hf, W.add_neg_cancel]
  have hdE : W.deg E = 0 := (idemCompl W M f hf hdf hfe).dege
  refine ⟨⟨E, by show W.cc (W.cc E E) e = E; rw [hEE, hEe], hdE⟩,
    ⟨f, by show W.cc (W.cc f f) e = f; rw [hf, hfe'], hdf⟩,
    ⟨E, by show W.cc (W.cc e E) E = E; rw [heE, hEE], hdE⟩,
    ⟨f, by show W.cc (W.cc e f) f = f; rw [hef, hf], hdf⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext hEE
  · exact Subtype.ext hf
  · exact Subtype.ext hfE
  · exact Subtype.ext hEf
  · apply Subtype.ext
    show W.add (W.cc E E) (W.cc f f) = e
    rw [hEE, hf, hE_def, W.add_assoc, W.neg_add_cancel, W.add_zero]
