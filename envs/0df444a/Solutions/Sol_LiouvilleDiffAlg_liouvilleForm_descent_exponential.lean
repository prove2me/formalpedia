-- Prove2me | solution 1 for LiouvilleDiffAlg.liouvilleForm_descent_exponential
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:56:13.816733+00:00
-- url     : https://prove2.me/submissions/a1c6a9c4-ca5d-4f93-b2c6-9650eb44d050

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_Form
import Theorems.Thm_LiouvilleDiffAlg_liouvilleForm_descent_transcendental

open scoped Differential
open LiouvilleDiffAlg

theorem solution {F G : Type*} [Field F] [Field G] [Differential G]
    [Algebra F G] [CharZero G] (K : IntermediateField F G) (hK : ∀ x ∈ K, x′ ∈ K)
    (hconst : constants G ⊆ (K : Set G)) {t : G} (ht : IsExponentialOver K t) {h : G} (hh : h ∈ K)
    (hL : LiouvilleFormIn (IntermediateField.adjoin F (insert t (K : Set G)) : Set G) h) :
    LiouvilleFormIn (K : Set G) h :=
  liouvilleForm_descent_transcendental K hK hconst ht.1 (Or.inr ht.2) hh hL
