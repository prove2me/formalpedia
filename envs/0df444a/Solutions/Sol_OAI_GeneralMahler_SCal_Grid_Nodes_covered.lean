-- Prove2me | solution 1 for OAI.GeneralMahler.SCal.Grid.Nodes.covered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:25:11.569107+00:00
-- url     : https://prove2.me/submissions/4b3d5143-5aba-414e-8704-c90dd3ad872b

import Mathlib
import Definitions.Def_OAIQ026G002
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by0_20
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by100_120
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by120_140
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by140_160
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by160_180
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by180_200
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by200_220
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by20_40
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by220_240
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by240_260
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by260_280
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by280_300
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by300_320
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by320_340
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by340_360
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by360_380
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by400_420
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by40_60
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by420_440
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by440_460
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by460_480
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by480_500
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by500_520
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by520_540
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by540_560
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by560_580
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by580_600
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by600_620
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by60_80
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by620_640
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by640_660
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by660_680
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by680_700
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by700_720
import Theorems.Thm_OAI_GeneralMahler_SCal_Grid_Nodes_by80_100

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
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run380
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by380_382 : By passesAt 380 382 := by
  apply byRun passesAt 380 2 382
  · rfl
  decide +kernel
lemma by382_385 : By passesAt 382 385 := by
  apply byRun passesAt 382 3 385
  · rfl
  decide +kernel
lemma by380_385 : By passesAt 380 385 := byJoin by380_382 by382_385
lemma by385_387 : By passesAt 385 387 := by
  apply byRun passesAt 385 2 387
  · rfl
  decide +kernel
lemma by387_390 : By passesAt 387 390 := by
  apply byRun passesAt 387 3 390
  · rfl
  decide +kernel
lemma by385_390 : By passesAt 385 390 := byJoin by385_387 by387_390
lemma by380_390 : By passesAt 380 390 := byJoin by380_385 by385_390
lemma by390_392 : By passesAt 390 392 := by
  apply byRun passesAt 390 2 392
  · rfl
  decide +kernel
lemma by392_395 : By passesAt 392 395 := by
  apply byRun passesAt 392 3 395
  · rfl
  decide +kernel
lemma by390_395 : By passesAt 390 395 := byJoin by390_392 by392_395
lemma by395_397 : By passesAt 395 397 := by
  apply byRun passesAt 395 2 397
  · rfl
  decide +kernel
lemma by397_400 : By passesAt 397 400 := by
  apply byRun passesAt 397 3 400
  · rfl
  decide +kernel
lemma by395_400 : By passesAt 395 400 := byJoin by395_397 by397_400
lemma by390_400 : By passesAt 390 400 := byJoin by390_395 by395_400
lemma by380_400 : By passesAt 380 400 := byJoin by380_390 by390_400
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Run720
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma by720_721 : By passesAt 720 721 := by
  apply byRun passesAt 720 1 721
  · rfl
  decide +kernel
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_AllNodes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
lemma covered_oai : By passesAt 0 721 :=
  (byJoin (byJoin (byJoin (byJoin (byJoin by0_20
    by20_40)
    (byJoin by40_60
    by60_80))
    (byJoin (byJoin by80_100
    by100_120)
    (byJoin by120_140
    (byJoin by140_160
    by160_180))))
    (byJoin (byJoin (byJoin by180_200
    by200_220)
    (byJoin by220_240
    by240_260))
    (byJoin (byJoin by260_280
    by280_300)
    (byJoin by300_320
    (byJoin by320_340
    by340_360)))))
    (byJoin (byJoin (byJoin (byJoin by360_380
    by380_400)
    (byJoin by400_420
    by420_440))
    (byJoin (byJoin by440_460
    by460_480)
    (byJoin by480_500
    (byJoin by500_520
    by520_540))))
    (byJoin (byJoin (byJoin by540_560
    by560_580)
    (byJoin by580_600
    (byJoin by600_620
    by620_640)))
    (byJoin (byJoin by640_660
    by660_680)
    (byJoin by680_700
    (byJoin by700_720
    by720_721))))))
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

theorem solution : type_of% @OAI.GeneralMahler.SCal.Grid.Nodes.covered_oai := @OAI.GeneralMahler.SCal.Grid.Nodes.covered_oai
