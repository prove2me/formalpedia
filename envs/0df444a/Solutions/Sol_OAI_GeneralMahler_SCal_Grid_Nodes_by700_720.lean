-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.by700_720
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:21:55.54984+00:00
-- url     : https://prove2.me/submissions/93502f13-265d-4df4-8495-017009fd40c2

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run700
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by700_702 : By passesAt 700 702 := by
  apply byRun passesAt 700 2 702
  · rfl
  decide +kernel
lemma by702_705 : By passesAt 702 705 := by
  apply byRun passesAt 702 3 705
  · rfl
  decide +kernel
lemma by700_705 : By passesAt 700 705 := byJoin by700_702 by702_705
lemma by705_707 : By passesAt 705 707 := by
  apply byRun passesAt 705 2 707
  · rfl
  decide +kernel
lemma by707_710 : By passesAt 707 710 := by
  apply byRun passesAt 707 3 710
  · rfl
  decide +kernel
lemma by705_710 : By passesAt 705 710 := byJoin by705_707 by707_710
lemma by700_710 : By passesAt 700 710 := byJoin by700_705 by705_710
lemma by710_712 : By passesAt 710 712 := by
  apply byRun passesAt 710 2 712
  · rfl
  decide +kernel
lemma by712_715 : By passesAt 712 715 := by
  apply byRun passesAt 712 3 715
  · rfl
  decide +kernel
lemma by710_715 : By passesAt 710 715 := byJoin by710_712 by712_715
lemma by715_717 : By passesAt 715 717 := by
  apply byRun passesAt 715 2 717
  · rfl
  decide +kernel
lemma by717_720 : By passesAt 717 720 := by
  apply byRun passesAt 717 3 720
  · rfl
  decide +kernel
lemma by715_720 : By passesAt 715 720 := byJoin by715_717 by717_720
lemma by710_720 : By passesAt 710 720 := byJoin by710_715 by715_720
lemma by700_720_oai : By passesAt 700 720 := byJoin by700_710 by710_720
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.by700_720_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.by700_720_oai
