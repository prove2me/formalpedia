-- Prove2me | solution 1 for N4Code.replace_27_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:35.284157+00:00
-- url     : https://prove2.me/submissions/b9f03ae0-a55d-465b-bd97-6147ae6fbfab

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) :
    C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 := by
  funext u
  by_cases hu1 : u = t₁
  · by_cases hu2 : u = t₂
    · exfalso
      exact htne (hu1.symm.trans hu2)
    · have ht' : ¬ t₁ = t₂ := fun h => hu2 (hu1.trans h)
      simp [replaceColumn, hu1, h3, if_neg ht']
  · by_cases hu2 : u = t₂
    · have ht' : ¬ t₁ = t₂ := fun h => hu1 (hu2.trans h.symm)
      simp [replaceColumn, hu2, h5]
    · simp [replaceColumn, hu1, hu2, hsame u hu1 hu2]
end N4Code
