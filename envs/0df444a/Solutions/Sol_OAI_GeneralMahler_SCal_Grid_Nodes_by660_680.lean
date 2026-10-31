-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by660_680
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:21:31.812984+00:00
-- url     : https://prove2.me/submissions/f2f11774-00ac-4f55-af3d-12354fe08a99

import Mathlib
import Definitions.Def_OAIQ026G002

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Data
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Compact certificate for §07 and table for later quadrature. -/
open Set Filter Real
namespace GeneralMahler.SCal.Grid
open Tag CJet Jet Profile Cert Cert.IV

lemma byRun (p:ℕ→Bool) (n m k:ℕ) (he:n+m=k) (h:runB p n m=true): By p n k := by
  subst k
  induction m with
  | zero=> intro i h1 h2; omega
  | succ m ih=>
    simp only [runB,Bool.and_eq_true] at h
    intro i h1 h2; by_cases H:i=n+m
    · exact H.symm ▸ h.1
    apply ih h.2 _ h1; omega
lemma byJoin {p:ℕ→Bool} {x y z:ℕ} (h:By p x y) (hh:By p y z):
    By p x z := by intro i he hz; rcases lt_or_ge i y with h'|h'; exact h i he h'; exact hh i h' hz
end GeneralMahler.SCal.Grid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run660
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by660_662 : By passesAt 660 662 := by
  apply byRun passesAt 660 2 662
  · rfl
  decide +kernel
lemma by662_665 : By passesAt 662 665 := by
  apply byRun passesAt 662 3 665
  · rfl
  decide +kernel
lemma by660_665 : By passesAt 660 665 := byJoin by660_662 by662_665
lemma by665_667 : By passesAt 665 667 := by
  apply byRun passesAt 665 2 667
  · rfl
  decide +kernel
lemma by667_670 : By passesAt 667 670 := by
  apply byRun passesAt 667 3 670
  · rfl
  decide +kernel
lemma by665_670 : By passesAt 665 670 := byJoin by665_667 by667_670
lemma by660_670 : By passesAt 660 670 := byJoin by660_665 by665_670
lemma by670_672 : By passesAt 670 672 := by
  apply byRun passesAt 670 2 672
  · rfl
  decide +kernel
lemma by672_675 : By passesAt 672 675 := by
  apply byRun passesAt 672 3 675
  · rfl
  decide +kernel
lemma by670_675 : By passesAt 670 675 := byJoin by670_672 by672_675
lemma by675_677 : By passesAt 675 677 := by
  apply byRun passesAt 675 2 677
  · rfl
  decide +kernel
lemma by677_680 : By passesAt 677 680 := by
  apply byRun passesAt 677 3 680
  · rfl
  decide +kernel
lemma by675_680 : By passesAt 675 680 := byJoin by675_677 by677_680
lemma by670_680 : By passesAt 670 680 := byJoin by670_675 by675_680
lemma by660_680_oai : By passesAt 660 680 := byJoin by660_670 by670_680
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by660_680_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by660_680_oai
