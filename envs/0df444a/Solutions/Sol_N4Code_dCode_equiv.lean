-- Prove2me | solution 1 for N4Code.dCode_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:31.784842+00:00
-- url     : https://prove2.me/submissions/fe0d3be3-e830-4702-9619-17a9502bca3b

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_min4_perm
import Theorems.Thm_N4Code_dRow_equiv

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) {ρ : Equiv (Fin 4) (Fin 4)}
    {p : Equiv (Fin n) (Fin n)} {f : Fin n → Bool}
    (h : ∀ t : Fin n, C' (p t) = rowPermute ρ (if f t then flipCol (C t) else C t))
    (y : Word n) :
    dCode C' y = dCode C (wordTransform p f y) := by
  unfold dCode
  calc
    min (dRow C' 0 y) (min (dRow C' 1 y) (min (dRow C' 2 y) (dRow C' 3 y)))
        = min (dRow C (ρ 0) (wordTransform p f y))
            (min (dRow C (ρ 1) (wordTransform p f y))
              (min (dRow C (ρ 2) (wordTransform p f y)) (dRow C (ρ 3) (wordTransform p f y)))) := by
          simp [dRow_equiv C C' h]
    _ = min (dRow C 0 (wordTransform p f y))
          (min (dRow C 1 (wordTransform p f y))
            (min (dRow C 2 (wordTransform p f y)) (dRow C 3 (wordTransform p f y)))) :=
          min4_perm (fun k => dRow C k (wordTransform p f y)) ρ
end N4Code
