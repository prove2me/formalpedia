-- Prove2me | solution 1 for LiouvilleDiffAlg.liouvilleForm_descent_logarithmic
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:56:12.872785+00:00
-- url     : https://prove2.me/submissions/27ab3b62-bca0-4e2c-9057-d062bb6c253e

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form
import Theorems.Thm_LiouvilleDiffAlg_liouvilleForm_descent_transcendental

open scoped Differential
open LiouvilleDiffAlg

theorem solution {F G : Type*} [Field F] [Field G] [Differential G]
    [Algebra F G] [CharZero G] (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K)
    (hconst : constants G ⊆ (K : Set G)) {t : G} (ht : IsLogarithmicOver K t) {h : G} (hh : h ∈ K)
    (hL : LiouvilleFormIn (IntermediateField.adjoin F (insert t (K : Set G)) : Set G) h) :
    LiouvilleFormIn (K : Set G) h :=
  liouvilleForm_descent_transcendental K hK hconst ht.1 (Or.inl ht.2) hh hL
