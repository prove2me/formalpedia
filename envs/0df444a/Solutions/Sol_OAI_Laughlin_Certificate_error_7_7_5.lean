-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_7_7_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:09:59.46627+00:00
-- url     : https://prove2.me/submissions/9e44dabe-8ece-46e0-a9b9-512621e75f50

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

theorem Y_expand (D r s : ℕ) : Y D r s =
    -(yRow D r s (rows[0]!) + (yRow D r s (rows[1]!) +
      (yRow D r s (rows[2]!) + (yRow D r s (rows[3]!) +
        (yRow D r s (rows[4]!) + (yRow D r s (rows[5]!) +
          (yRow D r s (rows[6]!) + 0))))))) / (10^14 : ℚ) := by rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_swap (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (he : t ≤ e.1 + e.2.1) (hf : t ≤ f.1 + f.2.1) :
    yEntry D r s t e f = yEntry D s r t f e := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at he hf
  have hT : q+l+(p+j-t) = p+j+(q+l-t) := by omega
  simp only [yEntry, hT, Nat.add_comm s r]
  split_ifs <;> ring_nf

private theorem sum_add {Element : Type*} (xs : List Element) (f g : Element → ℚ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_swap {Element : Type*} (xs ys : List Element)
    (f : Element → Element → ℚ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, sum_add]

theorem yRow_swap (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (h : ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1) :
    yRow D r s row = yRow D s r row := by
  unfold yRow
  rw [sum_swap]
  congr 1
  apply List.map_congr_left
  intro f hf
  congr 1
  apply List.map_congr_left
  intro e he
  exact yEntry_swap D r s row.1 e f (h e he) (h f hf)

theorem rows_valid : ∀ row ∈ rows, ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1 := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Fast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntry D r s t e f = yEntryFast D r s t e f := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp [yEntry, yEntryFast]
  split_ifs with hD hz
  · rcases hz with hz | hz <;> simp [hz]
  · push_cast
    ring
  · rfl

theorem yRow_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRow D r s row = yRowFast D r s row := by
  simp only [yRow, yRowFast, yEntry_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row072
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_7_0 : yRow 7 5 7 (rows[0]!) = (1153158553770801165 / 128 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_1 : yRow 7 5 7 (rows[1]!) = (398875219468930779 / 2097152 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_2 : yRow 7 5 7 (rows[2]!) = (-3344728266700356251085 / 8388608 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_3 : yRow 7 5 7 (rows[3]!) = (2694741498446716664085 / 2097152 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row0705007
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_0 : yRow 7 7 5 (rows[0]!) = (1153158553770801165 / 128 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[0]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row0705107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_1 : yRow 7 7 5 (rows[1]!) = (398875219468930779 / 2097152 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[1]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_1

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row0705207
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_2 : yRow 7 7 5 (rows[2]!) = (-3344728266700356251085 / 8388608 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[2]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_2

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row0705307
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_3 : yRow 7 7 5 (rows[3]!) = (2694741498446716664085 / 2097152 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[3]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_3

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row073
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_5_7_4 : yRow 7 5 7 (rows[4]!) = (-3701247860527868239965 / 33554432 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_5 : yRow 7 5 7 (rows[5]!) = (-111316765905740996833665 / 134217728 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

theorem yRow_7_5_7_6 : yRow 7 5 7 (rows[6]!) = (21601964370283224165 / 4194304 : ℚ) := by
  rw [yRow_eq_fast]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row0705407
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_4 : yRow 7 7 5 (rows[4]!) = (-3701247860527868239965 / 33554432 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[4]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_4

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row0705507
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_5 : yRow 7 7 5 (rows[5]!) = (-111316765905740996833665 / 134217728 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[5]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_5

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row0705607
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_7_7_5_6 : yRow 7 7 5 (rows[6]!) = (21601964370283224165 / 4194304 : ℚ) := by
  rw [yRow_swap 7 7 5 (rows[6]!) (rows_valid _ (by decide +kernel))]
  exact yRow_7_5_7_6

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Error07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem error_7_7_5_oai : Y 7 7 5 = (-1202717220838198373824731/13421772800000000000000 : ℚ) := by
  rw [Y_expand, yRow_7_7_5_0, yRow_7_7_5_1, yRow_7_7_5_2, yRow_7_7_5_3, yRow_7_7_5_4, yRow_7_7_5_5, yRow_7_7_5_6]
  norm_num

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_7_7_5_oai := @OAI.Laughlin.Certificate.error_7_7_5_oai
