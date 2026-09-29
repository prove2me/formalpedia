-- Prove2me | solution 1 for Hatcher.fundamentalGroup_map_injective_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-14T12:44:43.418863+00:00
-- url     : https://prove2.me/submissions/b7882d03-0da3-4313-bcf8-f200313523c4

import Mathlib

open CategoryTheory ContinuousMap FundamentalGroup

theorem solution {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (r : C(X, A)) (hr : ∀ a, r (i a) = a) (a₀ : A) :
    Function.Injective (FundamentalGroup.map i a₀) := by
  have hcomp : r.comp i = ContinuousMap.id A := by ext a; exact hr a
  have hfun : (FundamentalGroupoid.map i) ⋙ (FundamentalGroupoid.map r) = 𝟭 _ := by
    rw [← FundamentalGroupoid.map_comp, hcomp, FundamentalGroupoid.map_id]
  intro γ δ h
  have hγ := CategoryTheory.Functor.congr_hom hfun γ
  have hδ := CategoryTheory.Functor.congr_hom hfun δ
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hγ hδ
  have h2 : (FundamentalGroupoid.map r).map ((FundamentalGroupoid.map i).map γ)
      = (FundamentalGroupoid.map r).map ((FundamentalGroupoid.map i).map δ) :=
    congrArg (FundamentalGroupoid.map r).map h
  rw [hγ, hδ] at h2
  rw [cancel_epi, cancel_mono] at h2
  exact h2
