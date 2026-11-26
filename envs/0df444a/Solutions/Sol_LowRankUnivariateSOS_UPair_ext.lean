-- Prove2me | solution 1 for LowRankUnivariateSOS.UPair.ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:54:31.660543+00:00
-- url     : https://prove2.me/submissions/73ee33de-2023-4538-94ea-f30f340a3f2a

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
open scoped BigOperators
open LowRankUnivariateSOS.UPair
namespace LowRankUnivariateSOS.UPair
theorem _root_.solution {u v : UPair} (hfst : u.fst = v.fst) (hsnd : u.snd = v.snd) : u = v := by
  cases u
  cases v
  cases hfst
  cases hsnd
  rfl
end LowRankUnivariateSOS.UPair
