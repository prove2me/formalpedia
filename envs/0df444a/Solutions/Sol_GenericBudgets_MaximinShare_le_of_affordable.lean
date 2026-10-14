-- Prove2me | solution 1 for GenericBudgets.MaximinShare.le_of_affordable
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:11:42.478112+00:00
-- url     : https://prove2.me/submissions/a6f29c79-749d-426f-95be-99b7b3133742

import Mathlib
import Definitions.Def_GenericBudgets_MaximinShare_Setting

open GenericBudgets.MaximinShare

theorem solution {m : ℕ} (w : Finset (Fin m) → ℝ) (β : ℝ)
    (p : Fin m → ℝ) (S T : Finset (Fin m))
    (hDemand : GenericBudgets.AlmostEqual.IsDemanded w β p S) (hT : GenericBudgets.AlmostEqual.price p T ≤ β) : w T ≤ w S := by
  by_contra h
  exact (not_lt_of_ge hT) (hDemand.2 T (lt_of_not_ge h))
