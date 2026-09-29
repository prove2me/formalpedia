-- Prove2me | solution 1 for Hatcher.fundamentalGroup_map_bijective_of_retraction_homotopic_id
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-14T12:45:07.583468+00:00
-- url     : https://prove2.me/submissions/9e8ffecd-ab44-420a-8de8-3908e45a5536

import Theorems.Thm_Hatcher_fundamentalGroup_map_bijective_of_homotopyEquiv
import Mathlib

open ContinuousMap FundamentalGroup

theorem solution {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (r : C(X, A)) (hr : ∀ a, r (i a) = a)
    (H : (i.comp r).Homotopic (ContinuousMap.id X)) (a₀ : A) :
    Function.Bijective (FundamentalGroup.map i a₀) := by
  have hri : r.comp i = ContinuousMap.id A := by ext a; exact hr a
  exact Hatcher.fundamentalGroup_map_bijective_of_homotopyEquiv
    { toFun := i, invFun := r, left_inv := by rw [hri], right_inv := H } a₀
