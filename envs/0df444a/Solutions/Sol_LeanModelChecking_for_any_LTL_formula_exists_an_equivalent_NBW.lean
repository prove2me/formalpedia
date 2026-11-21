-- Prove2me | solution 1 for LeanModelChecking.for_any_LTL_formula_exists_an_equivalent_NBW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:50:36.774961+00:00
-- url     : https://prove2.me/submissions/18f9edbe-5c94-4cbe-a2f5-85bc8c56da6e

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
public import Definitions.Def_LeanPool_LeanModelChecking_NNFABW
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWResult
public import Theorems.Thm_LeanModelChecking_ABW_toNBW_lang_eq
public import Theorems.Thm_LeanModelChecking_exists_ABW_lang_for_LTL


set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
namespace LeanModelChecking
theorem _root_.solution :
    forAnyLTLFormulaExistsAnEquivalentNBWStatement := by
  unfold forAnyLTLFormulaExistsAnEquivalentNBWStatement
  intros _ φ
  obtain ⟨Q, qfin, A, lang_eq⟩ := exists_ABW_lang_for_LTL φ
  exists A.toNBW
  constructor
  · have := qfin
    exact inferInstanceAs (Finite ((Set Q) × (Set Q)))
  · rw [lang_eq, ABW.toNBW.lang_eq]
end LeanModelChecking
