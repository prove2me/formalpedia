-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T08:53:23.113457+00:00
-- url     : https://prove2.me/submissions/f4a325bc-35c4-4937-9bca-b5721e71ce9b

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_11_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_13_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_15_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_17_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_1_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_3_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_17_9_7

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0101Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_1_1_0 : RowCompute.yRowIntegralFast 17 1 1 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_1_1 : RowCompute.yRowIntegralFast 17 1 1 (RowCompute.rows[1]!) =
    (521088893958091479693375586036533054660940470461781560524800000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_1_2 : RowCompute.yRowIntegralFast 17 1 1 (RowCompute.rows[2]!) =
    (45359405492204497040980209750474756516908262669750349332480000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_1_3 : RowCompute.yRowIntegralFast 17 1 1 (RowCompute.rows[3]!) =
    (59105141793997810723262336724898430982033227166521444479795200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_1_4 : RowCompute.yRowIntegralFast 17 1 1 (RowCompute.rows[4]!) =
    (-12947228377060355169714055920969653111821896728105612161843200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_1_5 : RowCompute.yRowIntegralFast 17 1 1 (RowCompute.rows[5]!) =
    (-6589794246645772148611218792489788305640712017513634060042240000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_1_6 : RowCompute.yRowIntegralFast 17 1 1 (RowCompute.rows[6]!) =
    (-11600447246221645677362435470347945023371066217008061302702080000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0103Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_1_3_0 : RowCompute.yRowIntegralFast 17 1 3 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_3_1 : RowCompute.yRowIntegralFast 17 1 3 (RowCompute.rows[1]!) =
    (45984561096036079439265806681413588156963119594830372536320000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_3_2 : RowCompute.yRowIntegralFast 17 1 3 (RowCompute.rows[2]!) =
    (2345797578852419576651155228566897170682198467272316131737600000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_3_3 : RowCompute.yRowIntegralFast 17 1 3 (RowCompute.rows[3]!) =
    (-3915024930689606974643242871513566724241844254065977353830400000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_3_4 : RowCompute.yRowIntegralFast 17 1 3 (RowCompute.rows[4]!) =
    (-914294705379240761777292315008618939167850881178736430940160000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_3_5 : RowCompute.yRowIntegralFast 17 1 3 (RowCompute.rows[5]!) =
    (2487621117479212491768492457825749969499514726017893830492160000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_3_6 : RowCompute.yRowIntegralFast 17 1 3 (RowCompute.rows[6]!) =
    (322669003133177760613883304693484827787459479723634065408000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0105Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_1_5_0 : RowCompute.yRowIntegralFast 17 1 5 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_5_1 : RowCompute.yRowIntegralFast 17 1 5 (RowCompute.rows[1]!) =
    (-27464895967020667683770763034139506218926272968451424256000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_5_2 : RowCompute.yRowIntegralFast 17 1 5 (RowCompute.rows[2]!) =
    (-3154602509753924249895406819860795503544453682887735115776000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_5_3 : RowCompute.yRowIntegralFast 17 1 5 (RowCompute.rows[3]!) =
    (21966767405517384749066483455429278484507351661370408960000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_5_4 : RowCompute.yRowIntegralFast 17 1 5 (RowCompute.rows[4]!) =
    (652596375238306284583555330472296445580074836812247125196800000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_5_5 : RowCompute.yRowIntegralFast 17 1 5 (RowCompute.rows[5]!) =
    (-942732053254492114985205754569288303976730002115602572902400000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_5_6 : RowCompute.yRowIntegralFast 17 1 5 (RowCompute.rows[6]!) =
    (-109763383670793130826984460729786463002223185813783026073600000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0107Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_1_7_0 : RowCompute.yRowIntegralFast 17 1 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_7_1 : RowCompute.yRowIntegralFast 17 1 7 (RowCompute.rows[1]!) =
    (1608822876394881515564654347735650056478444713124927897600000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_7_2 : RowCompute.yRowIntegralFast 17 1 7 (RowCompute.rows[2]!) =
    (1583016005108008508949587245842315594955425005819784069120000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_7_3 : RowCompute.yRowIntegralFast 17 1 7 (RowCompute.rows[3]!) =
    (-131846688627333990066531301316053146202158039098367934464000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_7_4 : RowCompute.yRowIntegralFast 17 1 7 (RowCompute.rows[4]!) =
    (-93201697960224639502447654978211120233843174373013533491200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_7_5 : RowCompute.yRowIntegralFast 17 1 7 (RowCompute.rows[5]!) =
    (163893551755088479693756673983847805149657355754134935961600000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_7_6 : RowCompute.yRowIntegralFast 17 1 7 (RowCompute.rows[6]!) =
    (319220171615867749194305248416608344508952213355714786099200000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0109Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_1_9_0 : RowCompute.yRowIntegralFast 17 1 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_9_1 : RowCompute.yRowIntegralFast 17 1 9 (RowCompute.rows[1]!) =
    (8081292550003471707891142348036664086738263063145280962560000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_9_2 : RowCompute.yRowIntegralFast 17 1 9 (RowCompute.rows[2]!) =
    (89307245812517032399307767822878707646990672808723139788800000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_9_3 : RowCompute.yRowIntegralFast 17 1 9 (RowCompute.rows[3]!) =
    (516195815316473576657722806975144328208269901044786900500480000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_9_4 : RowCompute.yRowIntegralFast 17 1 9 (RowCompute.rows[4]!) =
    (-137720038421176788838565023726713229952620479326974692556800000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_9_5 : RowCompute.yRowIntegralFast 17 1 9 (RowCompute.rows[5]!) =
    (505834054586899752411714157389109134684494990732672630784000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_9_6 : RowCompute.yRowIntegralFast 17 1 9 (RowCompute.rows[6]!) =
    (-323791116103049573743837062016162354812983480690569358868480000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0117Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_1_17_0 : RowCompute.yRowIntegralFast 17 1 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_17_1 : RowCompute.yRowIntegralFast 17 1 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_17_2 : RowCompute.yRowIntegralFast 17 1 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_17_3 : RowCompute.yRowIntegralFast 17 1 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_17_4 : RowCompute.yRowIntegralFast 17 1 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_17_5 : RowCompute.yRowIntegralFast 17 1 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_1_17_6 : RowCompute.yRowIntegralFast 17 1 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0303Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_3_3_0 : RowCompute.yRowIntegralFast 17 3 3 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_3_1 : RowCompute.yRowIntegralFast 17 3 3 (RowCompute.rows[1]!) =
    (4058002163763520512987303139858749301844511375114306060288000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_3_2 : RowCompute.yRowIntegralFast 17 3 3 (RowCompute.rows[2]!) =
    (121314779619313647418018805131003684275419020533745751949312000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_3_3 : RowCompute.yRowIntegralFast 17 3 3 (RowCompute.rows[3]!) =
    (157634779384596510369973279489039187296964329107117765033984000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_3_4 : RowCompute.yRowIntegralFast 17 3 3 (RowCompute.rows[4]!) =
    (665377733390785529698860567757863458501725844269834042343424000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_3_5 : RowCompute.yRowIntegralFast 17 3 3 (RowCompute.rows[5]!) =
    (-654031077367771676797803371561316752982091153890275770761216000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_3_6 : RowCompute.yRowIntegralFast 17 3 3 (RowCompute.rows[6]!) =
    (-11181708252613333381004891195543388012814224142207555731456000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0305Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_3_5_0 : RowCompute.yRowIntegralFast 17 3 5 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_5_1 : RowCompute.yRowIntegralFast 17 3 5 (RowCompute.rows[1]!) =
    (-2423696227717550116931571411156411971721858644160439910400000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_5_2 : RowCompute.yRowIntegralFast 17 3 5 (RowCompute.rows[2]!) =
    (-163142767179660274461907186003923594246877432761440922501120000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_5_3 : RowCompute.yRowIntegralFast 17 3 5 (RowCompute.rows[3]!) =
    (45714533139433234327101623419644458697157276231615339560960000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_5_4 : RowCompute.yRowIntegralFast 17 3 5 (RowCompute.rows[4]!) =
    (-225955296142664001693229646737170046711004612921729702952960000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_5_5 : RowCompute.yRowIntegralFast 17 3 5 (RowCompute.rows[5]!) =
    (225356446664393690235902322828508727999406755384421997608960000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_5_6 : RowCompute.yRowIntegralFast 17 3 5 (RowCompute.rows[6]!) =
    (682344051500195966733870286077457108972098626608881991680000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0307Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_3_7_0 : RowCompute.yRowIntegralFast 17 3 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_7_1 : RowCompute.yRowIntegralFast 17 3 7 (RowCompute.rows[1]!) =
    (141973883362463000555387693641864803077701751063539875840000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_7_2 : RowCompute.yRowIntegralFast 17 3 7 (RowCompute.rows[2]!) =
    (81866926424006806896702056646931449124681215390802929254400000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_7_3 : RowCompute.yRowIntegralFast 17 3 7 (RowCompute.rows[3]!) =
    (-10219903717638727099171803215585542729390247865402733363200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_7_4 : RowCompute.yRowIntegralFast 17 3 7 (RowCompute.rows[4]!) =
    (20338097180375892597559392291964924363953825339133573201920000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_7_5 : RowCompute.yRowIntegralFast 17 3 7 (RowCompute.rows[5]!) =
    (-50023577958264471768624793390531749012408501855564123340800000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_7_6 : RowCompute.yRowIntegralFast 17 3 7 (RowCompute.rows[6]!) =
    (-6470829473987971212448604428506525112966131900250513735680000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0309Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_3_9_0 : RowCompute.yRowIntegralFast 17 3 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_9_1 : RowCompute.yRowIntegralFast 17 3 9 (RowCompute.rows[1]!) =
    (713150280709039485474323790194093682748996222221344047104000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_9_2 : RowCompute.yRowIntegralFast 17 3 9 (RowCompute.rows[2]!) =
    (4618594946906537651348933139121759910848559633085084205056000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_9_3 : RowCompute.yRowIntegralFast 17 3 9 (RowCompute.rows[3]!) =
    (-23216148905801396037548186775498821379097804773519714680832000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_9_4 : RowCompute.yRowIntegralFast 17 3 9 (RowCompute.rows[4]!) =
    (74320387029808778204534964102918330103309621861182590681088000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_9_5 : RowCompute.yRowIntegralFast 17 3 9 (RowCompute.rows[5]!) =
    (-79458883311522274323844375201959691918603757164266321346560000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_9_6 : RowCompute.yRowIntegralFast 17 3 9 (RowCompute.rows[6]!) =
    (10276751889773700387162313319470805445689844597250842427392000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0317Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_3_17_0 : RowCompute.yRowIntegralFast 17 3 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_17_1 : RowCompute.yRowIntegralFast 17 3 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_17_2 : RowCompute.yRowIntegralFast 17 3 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_17_3 : RowCompute.yRowIntegralFast 17 3 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_17_4 : RowCompute.yRowIntegralFast 17 3 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_17_5 : RowCompute.yRowIntegralFast 17 3 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_3_17_6 : RowCompute.yRowIntegralFast 17 3 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0505Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_5_5_0 : RowCompute.yRowIntegralFast 17 5 5 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_5_1 : RowCompute.yRowIntegralFast 17 5 5 (RowCompute.rows[1]!) =
    (1447585084283017334003145334553623503426574801510072320000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_5_2 : RowCompute.yRowIntegralFast 17 5 5 (RowCompute.rows[2]!) =
    (219392579919417886730221726760970608204032844958323127091200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_5_3 : RowCompute.yRowIntegralFast 17 5 5 (RowCompute.rows[3]!) =
    (16121409317454989295291893454861124575359238790489885900800000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_5_4 : RowCompute.yRowIntegralFast 17 5 5 (RowCompute.rows[4]!) =
    (69548656044814478830020069620194361962451089475424485376000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_5_5 : RowCompute.yRowIntegralFast 17 5 5 (RowCompute.rows[5]!) =
    (-79823482440337547370222230413873700625623103328230781747200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_5_6 : RowCompute.yRowIntegralFast 17 5 5 (RowCompute.rows[6]!) =
    (-4413417354830959210114815980172187740584339964593543577600000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0507Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_5_7_0 : RowCompute.yRowIntegralFast 17 5 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_7_1 : RowCompute.yRowIntegralFast 17 5 7 (RowCompute.rows[1]!) =
    (-84795806323790194327120266688733355199392803111043072000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_7_2 : RowCompute.yRowIntegralFast 17 5 7 (RowCompute.rows[2]!) =
    (-110093732678057048860804032966714439558074189623951622144000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_7_3 : RowCompute.yRowIntegralFast 17 5 7 (RowCompute.rows[3]!) =
    (-35811525608628750033676261636918401530136713480096238796800000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_7_4 : RowCompute.yRowIntegralFast 17 5 7 (RowCompute.rows[4]!) =
    (-5044677951140174270485265802429702226737424500436185907200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_7_5 : RowCompute.yRowIntegralFast 17 5 7 (RowCompute.rows[5]!) =
    (24513130106568116756614320877392445978818598881260155699200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_7_6 : RowCompute.yRowIntegralFast 17 5 7 (RowCompute.rows[6]!) =
    (7774403711827537246847030365927967303162563468772927078400000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0509Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_5_9_0 : RowCompute.yRowIntegralFast 17 5 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_9_1 : RowCompute.yRowIntegralFast 17 5 9 (RowCompute.rows[1]!) =
    (-425938571591884613879093008638608575693150683328099123200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_9_2 : RowCompute.yRowIntegralFast 17 5 9 (RowCompute.rows[2]!) =
    (-6211035147446873288319777683194823967734924902717257154560000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_9_3 : RowCompute.yRowIntegralFast 17 5 9 (RowCompute.rows[3]!) =
    (16869245745256972939038167913029572149000106391112316354560000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_9_4 : RowCompute.yRowIntegralFast 17 5 9 (RowCompute.rows[4]!) =
    (-28264475538338458374030897710558721844710551043102159667200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_9_5 : RowCompute.yRowIntegralFast 17 5 9 (RowCompute.rows[5]!) =
    (14802659089012012972975070087473276716640317835211565957120000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_9_6 : RowCompute.yRowIntegralFast 17 5 9 (RowCompute.rows[6]!) =
    (-5862829128469766319869094548836662226432009509495814225920000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0515Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_5_15_0 : RowCompute.yRowIntegralFast 17 5 15 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_15_1 : RowCompute.yRowIntegralFast 17 5 15 (RowCompute.rows[1]!) =
    (-3908105864038403147851850022524895812684419650501476352000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_15_2 : RowCompute.yRowIntegralFast 17 5 15 (RowCompute.rows[2]!) =
    (2018897758263963709579046339032869477427590036336107795251200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_15_3 : RowCompute.yRowIntegralFast 17 5 15 (RowCompute.rows[3]!) =
    (-191690827142917713704432520065212737685343259604037507481600000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_15_4 : RowCompute.yRowIntegralFast 17 5 15 (RowCompute.rows[4]!) =
    (-162431058888238563840807913762943099176223208990616584192000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_15_5 : RowCompute.yRowIntegralFast 17 5 15 (RowCompute.rows[5]!) =
    (-567259985828809409322208169711873153767105395425682653184000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_15_6 : RowCompute.yRowIntegralFast 17 5 15 (RowCompute.rows[6]!) =
    (-7875980692400011755230164688869446919620631303303043481600000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0517Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_5_17_0 : RowCompute.yRowIntegralFast 17 5 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_17_1 : RowCompute.yRowIntegralFast 17 5 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_17_2 : RowCompute.yRowIntegralFast 17 5 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_17_3 : RowCompute.yRowIntegralFast 17 5 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_17_4 : RowCompute.yRowIntegralFast 17 5 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_17_5 : RowCompute.yRowIntegralFast 17 5 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_5_17_6 : RowCompute.yRowIntegralFast 17 5 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0707Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_7_7_0 : RowCompute.yRowIntegralFast 17 7 7 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_7_1 : RowCompute.yRowIntegralFast 17 7 7 (RowCompute.rows[1]!) =
    (4967119962874635464952808071654930383138005640753971200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_7_2 : RowCompute.yRowIntegralFast 17 7 7 (RowCompute.rows[2]!) =
    (55246307689345513506909636991627518616468505153010401280000000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_7_3 : RowCompute.yRowIntegralFast 17 7 7 (RowCompute.rows[3]!) =
    (49009567812781265622509904387793377753065413412537342361600000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_7_4 : RowCompute.yRowIntegralFast 17 7 7 (RowCompute.rows[4]!) =
    (-1724085192359156139114058938577872193032969289286339788800000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_7_5 : RowCompute.yRowIntegralFast 17 7 7 (RowCompute.rows[5]!) =
    (-11245877798374132462702392911345193032929029923539412582400000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_7_6 : RowCompute.yRowIntegralFast 17 7 7 (RowCompute.rows[6]!) =
    (-14636903330459363735044609918976419096510065853833884467200000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0709Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_7_9_0 : RowCompute.yRowIntegralFast 17 7 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_9_1 : RowCompute.yRowIntegralFast 17 7 9 (RowCompute.rows[1]!) =
    (24950384619655213594768516863562469958327301986551070720000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_9_2 : RowCompute.yRowIntegralFast 17 7 9 (RowCompute.rows[2]!) =
    (3116769233618514199112837859406295962575064533950477107200000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_9_3 : RowCompute.yRowIntegralFast 17 7 9 (RowCompute.rows[3]!) =
    (-24633533455892724645638112448616570475827721885628162375680000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_9_4 : RowCompute.yRowIntegralFast 17 7 9 (RowCompute.rows[4]!) =
    (7256180923741277419890415112689880521950200326650184335360000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_9_5 : RowCompute.yRowIntegralFast 17 7 9 (RowCompute.rows[5]!) =
    (-2899123560124938839408404963086746119930796772626886819840000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_9_6 : RowCompute.yRowIntegralFast 17 7 9 (RowCompute.rows[6]!) =
    (11084571250557766107828517857803706396751674566737133568000000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0717Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_7_17_0 : RowCompute.yRowIntegralFast 17 7 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_17_1 : RowCompute.yRowIntegralFast 17 7 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_17_2 : RowCompute.yRowIntegralFast 17 7 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_17_3 : RowCompute.yRowIntegralFast 17 7 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_17_4 : RowCompute.yRowIntegralFast 17 7 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_17_5 : RowCompute.yRowIntegralFast 17 7 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_7_17_6 : RowCompute.yRowIntegralFast 17 7 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0909Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_9_9_0 : RowCompute.yRowIntegralFast 17 9 9 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_9_1 : RowCompute.yRowIntegralFast 17 9 9 (RowCompute.rows[1]!) =
    (125328499678202595214005206914733344014844422584618975232000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_9_2 : RowCompute.yRowIntegralFast 17 9 9 (RowCompute.rows[2]!) =
    (175835288581726793816526347561198287854401935303117897728000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_9_3 : RowCompute.yRowIntegralFast 17 9 9 (RowCompute.rows[3]!) =
    (15796091926893168755870346913717816593423707133261845102592000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_9_4 : RowCompute.yRowIntegralFast 17 9 9 (RowCompute.rows[4]!) =
    (4425583649010911174137432678379056413099820517501152788480000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_9_5 : RowCompute.yRowIntegralFast 17 9 9 (RowCompute.rows[5]!) =
    (7749646617968699390620975188673046474044622593044089143296000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_9_6 : RowCompute.yRowIntegralFast 17 9 9 (RowCompute.rows[6]!) =
    (-8705885251120324880720681674096290696986899256175451176960000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0911Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_9_11_0 : RowCompute.yRowIntegralFast 17 9 11 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_11_1 : RowCompute.yRowIntegralFast 17 9 11 (RowCompute.rows[1]!) =
    (96902972650460173106547082283821673134894125981672407040000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_11_2 : RowCompute.yRowIntegralFast 17 9 11 (RowCompute.rows[2]!) =
    (-4790458906482574068015156450364217651198397525180127641600000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_11_3 : RowCompute.yRowIntegralFast 17 9 11 (RowCompute.rows[3]!) =
    (36028917721665795617296666201205248217410622950999609835520000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_11_4 : RowCompute.yRowIntegralFast 17 9 11 (RowCompute.rows[4]!) =
    (-10031428194414402277141275293311696460148525262415918530560000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_11_5 : RowCompute.yRowIntegralFast 17 9 11 (RowCompute.rows[5]!) =
    (-28094502866395583983522926513004155238050226874783964856320000000 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_11_6 : RowCompute.yRowIntegralFast 17 9 11 (RowCompute.rows[6]!) =
    (-6687997160808573297135203724958579293904815984304277422080000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0917Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_9_17_0 : RowCompute.yRowIntegralFast 17 9 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_17_1 : RowCompute.yRowIntegralFast 17 9 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_17_2 : RowCompute.yRowIntegralFast 17 9 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_17_3 : RowCompute.yRowIntegralFast 17 9 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_17_4 : RowCompute.yRowIntegralFast 17 9 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_17_5 : RowCompute.yRowIntegralFast 17 9 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_9_17_6 : RowCompute.yRowIntegralFast 17 9 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1117Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_11_17_0 : RowCompute.yRowIntegralFast 17 11 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_11_17_1 : RowCompute.yRowIntegralFast 17 11 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_11_17_2 : RowCompute.yRowIntegralFast 17 11 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_11_17_3 : RowCompute.yRowIntegralFast 17 11 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_11_17_4 : RowCompute.yRowIntegralFast 17 11 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_11_17_5 : RowCompute.yRowIntegralFast 17 11 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_11_17_6 : RowCompute.yRowIntegralFast 17 11 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1317Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_13_17_0 : RowCompute.yRowIntegralFast 17 13 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_13_17_1 : RowCompute.yRowIntegralFast 17 13 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_13_17_2 : RowCompute.yRowIntegralFast 17 13 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_13_17_3 : RowCompute.yRowIntegralFast 17 13 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_13_17_4 : RowCompute.yRowIntegralFast 17 13 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_13_17_5 : RowCompute.yRowIntegralFast 17 13 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_13_17_6 : RowCompute.yRowIntegralFast 17 13 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1517Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_15_17_0 : RowCompute.yRowIntegralFast 17 15 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_15_17_1 : RowCompute.yRowIntegralFast 17 15 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_15_17_2 : RowCompute.yRowIntegralFast 17 15 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_15_17_3 : RowCompute.yRowIntegralFast 17 15 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_15_17_4 : RowCompute.yRowIntegralFast 17 15 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_15_17_5 : RowCompute.yRowIntegralFast 17 15 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_15_17_6 : RowCompute.yRowIntegralFast 17 15 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1717Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_17_17_17_0 : RowCompute.yRowIntegralFast 17 17 17 (RowCompute.rows[0]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_17_17_1 : RowCompute.yRowIntegralFast 17 17 17 (RowCompute.rows[1]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_17_17_2 : RowCompute.yRowIntegralFast 17 17 17 (RowCompute.rows[2]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_17_17_3 : RowCompute.yRowIntegralFast 17 17 17 (RowCompute.rows[3]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_17_17_4 : RowCompute.yRowIntegralFast 17 17 17 (RowCompute.rows[4]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_17_17_5 : RowCompute.yRowIntegralFast 17 17 17 (RowCompute.rows[5]!) =
    (0 : ℤ) := by
  decide +kernel

theorem computeRow_17_17_17_6 : RowCompute.yRowIntegralFast 17 17 17 (RowCompute.rows[6]!) =
    (0 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

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
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Integral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_eq_integral (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (ht : t ≤ 16) (hT : e.1 + e.2.1 + (f.1 + f.2.1 - t) ≤ 24) :
    yEntry D r s t e f = (yEntryIntegral D r s t e f : ℚ) / arithmeticScale := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at hT
  let T := p+j+(q+l-t)
  let z : ℤ := 1-2*((p : ℤ)+(j : ℤ)+(q+l-t : ℕ))+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r : ℤ)+(s : ℤ))/2
  have hz : 0 ≤ 64+z := by dsimp [z,T]; omega
  have hexp : 65-2*((p : ℤ)+(j : ℤ)+(q+l-t : ℕ))+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r : ℤ)+(s : ℤ))/2 = 64+z := by dsimp [z]; ring
  have hp : (2 : ℚ)^((64+z).toNat) = (2 : ℚ)^64 * (2 : ℚ)^z := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hz, zpow_add₀ (by norm_num)]
    norm_num
  have hTD : T-D ≤ 24 := by dsimp [T]; omega
  have hf : ((T-D).factorial : ℚ) * ((24 : ℕ).descFactorial (24-(T-D)) : ℚ) = (Nat.factorial 24 : ℚ) := by
    have hn := Nat.factorial_mul_descFactorial (n := 24) (k := 24-(T-D)) (by omega)
    rw [Nat.sub_sub_self hTD] at hn
    exact_mod_cast hn
  dsimp [yEntry, yEntryIntegral]
  split_ifs with hd
  · change _ = _ / arithmeticScale
    rw [hexp]
    push_cast
    rw [hp]
    change _ = _ / ((2 : ℚ)^64 * (Nat.factorial 24 : ℚ))
    rw [← hf]
    have hn : ((T-D).factorial : ℚ) ≠ 0 := by positivity
    have hm : ((24 : ℕ).descFactorial (24-(T-D)) : ℚ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hf
      exact (ne_of_gt (show (0 : ℚ) < (Nat.factorial 24 : ℚ) by positivity)) hf.symm
    change _ = _ / ((2 : ℚ)^64 * (((T-D).factorial : ℚ) * ((24 : ℕ).descFactorial (24-(T-D)) : ℚ)))
    field_simp
    ring
  · simp

private theorem sum_integral {Element : Type*} (xs : List Element) (f : Element → ℤ) (c : ℚ) :
    (xs.map (fun x => (f x : ℚ)/c)).sum = ((xs.map f).sum : ℚ)/c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

theorem yRow_eq_integral (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (ht : row.1 ≤ 16)
    (hT : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24) :
    yRow D r s row = (yRowIntegral D r s row : ℚ) / arithmeticScale := by
  unfold yRow yRowIntegral
  calc
    _ = (row.2.2.map (fun e => (row.2.2.map (fun f =>
        (yEntryIntegral D r s row.1 e f : ℚ)/arithmeticScale)).sum)).sum := by
      congr 1
      apply List.map_congr_left
      intro e he
      congr 1
      apply List.map_congr_left
      intro f hf
      exact yEntry_eq_integral D r s row.1 e f ht (hT e he f hf)
    _ = _ := by simp_rw [sum_integral]

theorem rows_integral_bounds : ∀ row ∈ rows, row.1 ≤ 16 ∧
    ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24 := by
  decide +kernel

theorem source_yRow_eq_integral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegral D r s (rows[n]!) : ℚ) / arithmeticScale := by
  have hm : rows[n]! ∈ rows := by
    interval_cases n <;> decide +kernel
  exact yRow_eq_integral D r s _ (rows_integral_bounds _ hm).1 (rows_integral_bounds _ hm).2

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FastChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem U_eq_fast (c z T p : ℕ) : U c z T p = UFast c z T p := by
  simp only [U, UFast, Nat.choose_eq_fast_choose]

theorem V_eq_fast (r D T p j k : ℕ) : V r D T p j k = VFast r D T p j k := by
  simp only [V, VFast, U_eq_fast]

theorem yEntryIntegral_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntryIntegral D r s t e f = yEntryIntegralFast D r s t e f := by
  simp only [yEntryIntegral, yEntryIntegralFast, V_eq_fast]

theorem yRowIntegral_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRowIntegral D r s row = yRowIntegralFast D r s row := by
  simp only [yRowIntegral, yRowIntegralFast, yEntryIntegral_eq_fast]

theorem source_yRow_eq_fastIntegral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegralFast D r s (rows[n]!) : ℚ) / arithmeticScale := by
  rw [source_yRow_eq_integral D r s n hn, yRowIntegral_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RowBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_yRow_eq_rowCompute (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (RowCompute.yRowIntegralFast D r s (RowCompute.rows[n]!) : ℚ) / arithmeticScale := by
  exact source_yRow_eq_fastIntegral D r s n hn

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem source_error_17_1_1 : Y 17 1 1 = (-27062893468327394953193285367/419430400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 1 0 (by decide),
    source_yRow_eq_rowCompute 17 1 1 1 (by decide),
    source_yRow_eq_rowCompute 17 1 1 2 (by decide),
    source_yRow_eq_rowCompute 17 1 1 3 (by decide),
    source_yRow_eq_rowCompute 17 1 1 4 (by decide),
    source_yRow_eq_rowCompute 17 1 1 5 (by decide),
    source_yRow_eq_rowCompute 17 1 1 6 (by decide),
    computeRow_17_1_1_0, computeRow_17_1_1_1, computeRow_17_1_1_2, computeRow_17_1_1_3, computeRow_17_1_1_4, computeRow_17_1_1_5, computeRow_17_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_3 : Y 17 1 3 = (-34150355623889743675914477/104857600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 3 0 (by decide),
    source_yRow_eq_rowCompute 17 1 3 1 (by decide),
    source_yRow_eq_rowCompute 17 1 3 2 (by decide),
    source_yRow_eq_rowCompute 17 1 3 3 (by decide),
    source_yRow_eq_rowCompute 17 1 3 4 (by decide),
    source_yRow_eq_rowCompute 17 1 3 5 (by decide),
    source_yRow_eq_rowCompute 17 1 3 6 (by decide),
    computeRow_17_1_3_0, computeRow_17_1_3_1, computeRow_17_1_3_2, computeRow_17_1_3_3, computeRow_17_1_3_4, computeRow_17_1_3_5, computeRow_17_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_5 : Y 17 1 5 = (260924265129905899387586721/83886080000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 5 0 (by decide),
    source_yRow_eq_rowCompute 17 1 5 1 (by decide),
    source_yRow_eq_rowCompute 17 1 5 2 (by decide),
    source_yRow_eq_rowCompute 17 1 5 3 (by decide),
    source_yRow_eq_rowCompute 17 1 5 4 (by decide),
    source_yRow_eq_rowCompute 17 1 5 5 (by decide),
    source_yRow_eq_rowCompute 17 1 5 6 (by decide),
    computeRow_17_1_5_0, computeRow_17_1_5_1, computeRow_17_1_5_2, computeRow_17_1_5_3, computeRow_17_1_5_4, computeRow_17_1_5_5, computeRow_17_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_7 : Y 17 1 7 = (-67528457531024325424642053/41943040000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 7 0 (by decide),
    source_yRow_eq_rowCompute 17 1 7 1 (by decide),
    source_yRow_eq_rowCompute 17 1 7 2 (by decide),
    source_yRow_eq_rowCompute 17 1 7 3 (by decide),
    source_yRow_eq_rowCompute 17 1 7 4 (by decide),
    source_yRow_eq_rowCompute 17 1 7 5 (by decide),
    source_yRow_eq_rowCompute 17 1 7 6 (by decide),
    computeRow_17_1_7_0, computeRow_17_1_7_1, computeRow_17_1_7_2, computeRow_17_1_7_3, computeRow_17_1_7_4, computeRow_17_1_7_5, computeRow_17_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_9 : Y 17 1 9 = (-30137637143983305054521403/52428800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 9 0 (by decide),
    source_yRow_eq_rowCompute 17 1 9 1 (by decide),
    source_yRow_eq_rowCompute 17 1 9 2 (by decide),
    source_yRow_eq_rowCompute 17 1 9 3 (by decide),
    source_yRow_eq_rowCompute 17 1 9 4 (by decide),
    source_yRow_eq_rowCompute 17 1 9 5 (by decide),
    source_yRow_eq_rowCompute 17 1 9 6 (by decide),
    computeRow_17_1_9_0, computeRow_17_1_9_1, computeRow_17_1_9_2, computeRow_17_1_9_3, computeRow_17_1_9_4, computeRow_17_1_9_5, computeRow_17_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_17 : Y 17 1 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 17 0 (by decide),
    source_yRow_eq_rowCompute 17 1 17 1 (by decide),
    source_yRow_eq_rowCompute 17 1 17 2 (by decide),
    source_yRow_eq_rowCompute 17 1 17 3 (by decide),
    source_yRow_eq_rowCompute 17 1 17 4 (by decide),
    source_yRow_eq_rowCompute 17 1 17 5 (by decide),
    source_yRow_eq_rowCompute 17 1 17 6 (by decide),
    computeRow_17_1_17_0, computeRow_17_1_17_1, computeRow_17_1_17_2, computeRow_17_1_17_3, computeRow_17_1_17_4, computeRow_17_1_17_5, computeRow_17_1_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_3 : Y 17 3 3 = (-259433233939629173544831711/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 3 0 (by decide),
    source_yRow_eq_rowCompute 17 3 3 1 (by decide),
    source_yRow_eq_rowCompute 17 3 3 2 (by decide),
    source_yRow_eq_rowCompute 17 3 3 3 (by decide),
    source_yRow_eq_rowCompute 17 3 3 4 (by decide),
    source_yRow_eq_rowCompute 17 3 3 5 (by decide),
    source_yRow_eq_rowCompute 17 3 3 6 (by decide),
    computeRow_17_3_3_0, computeRow_17_3_3_1, computeRow_17_3_3_2, computeRow_17_3_3_3, computeRow_17_3_3_4, computeRow_17_3_3_5, computeRow_17_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_5 : Y 17 3 5 = (10972785710270109216153663/104857600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 5 0 (by decide),
    source_yRow_eq_rowCompute 17 3 5 1 (by decide),
    source_yRow_eq_rowCompute 17 3 5 2 (by decide),
    source_yRow_eq_rowCompute 17 3 5 3 (by decide),
    source_yRow_eq_rowCompute 17 3 5 4 (by decide),
    source_yRow_eq_rowCompute 17 3 5 5 (by decide),
    source_yRow_eq_rowCompute 17 3 5 6 (by decide),
    computeRow_17_3_5_0, computeRow_17_3_5_1, computeRow_17_3_5_2, computeRow_17_3_5_3, computeRow_17_3_5_4, computeRow_17_3_5_5, computeRow_17_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_7 : Y 17 3 7 = (-408068525315759942414781/13107200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 7 0 (by decide),
    source_yRow_eq_rowCompute 17 3 7 1 (by decide),
    source_yRow_eq_rowCompute 17 3 7 2 (by decide),
    source_yRow_eq_rowCompute 17 3 7 3 (by decide),
    source_yRow_eq_rowCompute 17 3 7 4 (by decide),
    source_yRow_eq_rowCompute 17 3 7 5 (by decide),
    source_yRow_eq_rowCompute 17 3 7 6 (by decide),
    computeRow_17_3_7_0, computeRow_17_3_7_1, computeRow_17_3_7_2, computeRow_17_3_7_3, computeRow_17_3_7_4, computeRow_17_3_7_5, computeRow_17_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_9 : Y 17 3 9 = (729849806595543331244547/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 9 0 (by decide),
    source_yRow_eq_rowCompute 17 3 9 1 (by decide),
    source_yRow_eq_rowCompute 17 3 9 2 (by decide),
    source_yRow_eq_rowCompute 17 3 9 3 (by decide),
    source_yRow_eq_rowCompute 17 3 9 4 (by decide),
    source_yRow_eq_rowCompute 17 3 9 5 (by decide),
    source_yRow_eq_rowCompute 17 3 9 6 (by decide),
    computeRow_17_3_9_0, computeRow_17_3_9_1, computeRow_17_3_9_2, computeRow_17_3_9_3, computeRow_17_3_9_4, computeRow_17_3_9_5, computeRow_17_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_17 : Y 17 3 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 17 0 (by decide),
    source_yRow_eq_rowCompute 17 3 17 1 (by decide),
    source_yRow_eq_rowCompute 17 3 17 2 (by decide),
    source_yRow_eq_rowCompute 17 3 17 3 (by decide),
    source_yRow_eq_rowCompute 17 3 17 4 (by decide),
    source_yRow_eq_rowCompute 17 3 17 5 (by decide),
    source_yRow_eq_rowCompute 17 3 17 6 (by decide),
    computeRow_17_3_17_0, computeRow_17_3_17_1, computeRow_17_3_17_2, computeRow_17_3_17_3, computeRow_17_3_17_4, computeRow_17_3_17_5, computeRow_17_3_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_5 : Y 17 5 5 = (-16291154585525363835188931/83886080000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 5 0 (by decide),
    source_yRow_eq_rowCompute 17 5 5 1 (by decide),
    source_yRow_eq_rowCompute 17 5 5 2 (by decide),
    source_yRow_eq_rowCompute 17 5 5 3 (by decide),
    source_yRow_eq_rowCompute 17 5 5 4 (by decide),
    source_yRow_eq_rowCompute 17 5 5 5 (by decide),
    source_yRow_eq_rowCompute 17 5 5 6 (by decide),
    computeRow_17_5_5_0, computeRow_17_5_5_1, computeRow_17_5_5_2, computeRow_17_5_5_3, computeRow_17_5_5_4, computeRow_17_5_5_5, computeRow_17_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_7 : Y 17 5 7 = (4351689332062192591003071/41943040000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 7 0 (by decide),
    source_yRow_eq_rowCompute 17 5 7 1 (by decide),
    source_yRow_eq_rowCompute 17 5 7 2 (by decide),
    source_yRow_eq_rowCompute 17 5 7 3 (by decide),
    source_yRow_eq_rowCompute 17 5 7 4 (by decide),
    source_yRow_eq_rowCompute 17 5 7 5 (by decide),
    source_yRow_eq_rowCompute 17 5 7 6 (by decide),
    computeRow_17_5_7_0, computeRow_17_5_7_1, computeRow_17_5_7_2, computeRow_17_5_7_3, computeRow_17_5_7_4, computeRow_17_5_7_5, computeRow_17_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_9 : Y 17 5 9 = (83301302217472013622717/10485760000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 9 0 (by decide),
    source_yRow_eq_rowCompute 17 5 9 1 (by decide),
    source_yRow_eq_rowCompute 17 5 9 2 (by decide),
    source_yRow_eq_rowCompute 17 5 9 3 (by decide),
    source_yRow_eq_rowCompute 17 5 9 4 (by decide),
    source_yRow_eq_rowCompute 17 5 9 5 (by decide),
    source_yRow_eq_rowCompute 17 5 9 6 (by decide),
    computeRow_17_5_9_0, computeRow_17_5_9_1, computeRow_17_5_9_2, computeRow_17_5_9_3, computeRow_17_5_9_4, computeRow_17_5_9_5, computeRow_17_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_15 : Y 17 5 15 = (-99471136192512553900431/104857600000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 15 0 (by decide),
    source_yRow_eq_rowCompute 17 5 15 1 (by decide),
    source_yRow_eq_rowCompute 17 5 15 2 (by decide),
    source_yRow_eq_rowCompute 17 5 15 3 (by decide),
    source_yRow_eq_rowCompute 17 5 15 4 (by decide),
    source_yRow_eq_rowCompute 17 5 15 5 (by decide),
    source_yRow_eq_rowCompute 17 5 15 6 (by decide),
    computeRow_17_5_15_0, computeRow_17_5_15_1, computeRow_17_5_15_2, computeRow_17_5_15_3, computeRow_17_5_15_4, computeRow_17_5_15_5, computeRow_17_5_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_17 : Y 17 5 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 17 0 (by decide),
    source_yRow_eq_rowCompute 17 5 17 1 (by decide),
    source_yRow_eq_rowCompute 17 5 17 2 (by decide),
    source_yRow_eq_rowCompute 17 5 17 3 (by decide),
    source_yRow_eq_rowCompute 17 5 17 4 (by decide),
    source_yRow_eq_rowCompute 17 5 17 5 (by decide),
    source_yRow_eq_rowCompute 17 5 17 6 (by decide),
    computeRow_17_5_17_0, computeRow_17_5_17_1, computeRow_17_5_17_2, computeRow_17_5_17_3, computeRow_17_5_17_4, computeRow_17_5_17_5, computeRow_17_5_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_7 : Y 17 7 7 = (-1404556469174930860536363/20971520000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 7 0 (by decide),
    source_yRow_eq_rowCompute 17 7 7 1 (by decide),
    source_yRow_eq_rowCompute 17 7 7 2 (by decide),
    source_yRow_eq_rowCompute 17 7 7 3 (by decide),
    source_yRow_eq_rowCompute 17 7 7 4 (by decide),
    source_yRow_eq_rowCompute 17 7 7 5 (by decide),
    source_yRow_eq_rowCompute 17 7 7 6 (by decide),
    computeRow_17_7_7_0, computeRow_17_7_7_1, computeRow_17_7_7_2, computeRow_17_7_7_3, computeRow_17_7_7_4, computeRow_17_7_7_5, computeRow_17_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_9 : Y 17 7 9 = (138574461584170298662731/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 9 0 (by decide),
    source_yRow_eq_rowCompute 17 7 9 1 (by decide),
    source_yRow_eq_rowCompute 17 7 9 2 (by decide),
    source_yRow_eq_rowCompute 17 7 9 3 (by decide),
    source_yRow_eq_rowCompute 17 7 9 4 (by decide),
    source_yRow_eq_rowCompute 17 7 9 5 (by decide),
    source_yRow_eq_rowCompute 17 7 9 6 (by decide),
    computeRow_17_7_9_0, computeRow_17_7_9_1, computeRow_17_7_9_2, computeRow_17_7_9_3, computeRow_17_7_9_4, computeRow_17_7_9_5, computeRow_17_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_17 : Y 17 7 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 17 0 (by decide),
    source_yRow_eq_rowCompute 17 7 17 1 (by decide),
    source_yRow_eq_rowCompute 17 7 17 2 (by decide),
    source_yRow_eq_rowCompute 17 7 17 3 (by decide),
    source_yRow_eq_rowCompute 17 7 17 4 (by decide),
    source_yRow_eq_rowCompute 17 7 17 5 (by decide),
    source_yRow_eq_rowCompute 17 7 17 6 (by decide),
    computeRow_17_7_17_0, computeRow_17_7_17_1, computeRow_17_7_17_2, computeRow_17_7_17_3, computeRow_17_7_17_4, computeRow_17_7_17_5, computeRow_17_7_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_9_9 : Y 17 9 9 = (-560195899211802719046699/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 9 9 0 (by decide),
    source_yRow_eq_rowCompute 17 9 9 1 (by decide),
    source_yRow_eq_rowCompute 17 9 9 2 (by decide),
    source_yRow_eq_rowCompute 17 9 9 3 (by decide),
    source_yRow_eq_rowCompute 17 9 9 4 (by decide),
    source_yRow_eq_rowCompute 17 9 9 5 (by decide),
    source_yRow_eq_rowCompute 17 9 9 6 (by decide),
    computeRow_17_9_9_0, computeRow_17_9_9_1, computeRow_17_9_9_2, computeRow_17_9_9_3, computeRow_17_9_9_4, computeRow_17_9_9_5, computeRow_17_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_9_11 : Y 17 9 11 = (1543576781120216089401/131072000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 9 11 0 (by decide),
    source_yRow_eq_rowCompute 17 9 11 1 (by decide),
    source_yRow_eq_rowCompute 17 9 11 2 (by decide),
    source_yRow_eq_rowCompute 17 9 11 3 (by decide),
    source_yRow_eq_rowCompute 17 9 11 4 (by decide),
    source_yRow_eq_rowCompute 17 9 11 5 (by decide),
    source_yRow_eq_rowCompute 17 9 11 6 (by decide),
    computeRow_17_9_11_0, computeRow_17_9_11_1, computeRow_17_9_11_2, computeRow_17_9_11_3, computeRow_17_9_11_4, computeRow_17_9_11_5, computeRow_17_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_9_17 : Y 17 9 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 9 17 0 (by decide),
    source_yRow_eq_rowCompute 17 9 17 1 (by decide),
    source_yRow_eq_rowCompute 17 9 17 2 (by decide),
    source_yRow_eq_rowCompute 17 9 17 3 (by decide),
    source_yRow_eq_rowCompute 17 9 17 4 (by decide),
    source_yRow_eq_rowCompute 17 9 17 5 (by decide),
    source_yRow_eq_rowCompute 17 9 17 6 (by decide),
    computeRow_17_9_17_0, computeRow_17_9_17_1, computeRow_17_9_17_2, computeRow_17_9_17_3, computeRow_17_9_17_4, computeRow_17_9_17_5, computeRow_17_9_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_11_17 : Y 17 11 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 11 17 0 (by decide),
    source_yRow_eq_rowCompute 17 11 17 1 (by decide),
    source_yRow_eq_rowCompute 17 11 17 2 (by decide),
    source_yRow_eq_rowCompute 17 11 17 3 (by decide),
    source_yRow_eq_rowCompute 17 11 17 4 (by decide),
    source_yRow_eq_rowCompute 17 11 17 5 (by decide),
    source_yRow_eq_rowCompute 17 11 17 6 (by decide),
    computeRow_17_11_17_0, computeRow_17_11_17_1, computeRow_17_11_17_2, computeRow_17_11_17_3, computeRow_17_11_17_4, computeRow_17_11_17_5, computeRow_17_11_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_13_17 : Y 17 13 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 13 17 0 (by decide),
    source_yRow_eq_rowCompute 17 13 17 1 (by decide),
    source_yRow_eq_rowCompute 17 13 17 2 (by decide),
    source_yRow_eq_rowCompute 17 13 17 3 (by decide),
    source_yRow_eq_rowCompute 17 13 17 4 (by decide),
    source_yRow_eq_rowCompute 17 13 17 5 (by decide),
    source_yRow_eq_rowCompute 17 13 17 6 (by decide),
    computeRow_17_13_17_0, computeRow_17_13_17_1, computeRow_17_13_17_2, computeRow_17_13_17_3, computeRow_17_13_17_4, computeRow_17_13_17_5, computeRow_17_13_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_15_17 : Y 17 15 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 15 17 0 (by decide),
    source_yRow_eq_rowCompute 17 15 17 1 (by decide),
    source_yRow_eq_rowCompute 17 15 17 2 (by decide),
    source_yRow_eq_rowCompute 17 15 17 3 (by decide),
    source_yRow_eq_rowCompute 17 15 17 4 (by decide),
    source_yRow_eq_rowCompute 17 15 17 5 (by decide),
    source_yRow_eq_rowCompute 17 15 17 6 (by decide),
    computeRow_17_15_17_0, computeRow_17_15_17_1, computeRow_17_15_17_2, computeRow_17_15_17_3, computeRow_17_15_17_4, computeRow_17_15_17_5, computeRow_17_15_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_17_17 : Y 17 17 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 17 17 0 (by decide),
    source_yRow_eq_rowCompute 17 17 17 1 (by decide),
    source_yRow_eq_rowCompute 17 17 17 2 (by decide),
    source_yRow_eq_rowCompute 17 17 17 3 (by decide),
    source_yRow_eq_rowCompute 17 17 17 4 (by decide),
    source_yRow_eq_rowCompute 17 17 17 5 (by decide),
    source_yRow_eq_rowCompute 17 17 17 6 (by decide),
    computeRow_17_17_17_0, computeRow_17_17_17_1, computeRow_17_17_17_2, computeRow_17_17_17_3, computeRow_17_17_17_4, computeRow_17_17_17_5, computeRow_17_17_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem error_17_oai : errorRational 17 = candidateY_17 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_17_1_1
  · exact source_error_17_1_3
  · exact source_error_17_1_5
  · exact source_error_17_1_7
  · exact source_error_17_1_9
  · exact source_error_17_1_11
  · exact source_error_17_1_13
  · exact source_error_17_1_15
  · exact source_error_17_1_17
  · exact source_error_17_3_1
  · exact source_error_17_3_3
  · exact source_error_17_3_5
  · exact source_error_17_3_7
  · exact source_error_17_3_9
  · exact source_error_17_3_11
  · exact source_error_17_3_13
  · exact source_error_17_3_15
  · exact source_error_17_3_17
  · exact source_error_17_5_1
  · exact source_error_17_5_3
  · exact source_error_17_5_5
  · exact source_error_17_5_7
  · exact source_error_17_5_9
  · exact source_error_17_5_11
  · exact source_error_17_5_13
  · exact source_error_17_5_15
  · exact source_error_17_5_17
  · exact source_error_17_7_1
  · exact source_error_17_7_3
  · exact source_error_17_7_5
  · exact source_error_17_7_7
  · exact source_error_17_7_9
  · exact source_error_17_7_11
  · exact source_error_17_7_13
  · exact source_error_17_7_15
  · exact source_error_17_7_17
  · exact source_error_17_9_1
  · exact source_error_17_9_3
  · exact source_error_17_9_5
  · exact source_error_17_9_7
  · exact source_error_17_9_9
  · exact source_error_17_9_11
  · exact source_error_17_9_13
  · exact source_error_17_9_15
  · exact source_error_17_9_17
  · exact source_error_17_11_1
  · exact source_error_17_11_3
  · exact source_error_17_11_5
  · exact source_error_17_11_7
  · exact source_error_17_11_9
  · exact source_error_17_11_11
  · exact source_error_17_11_13
  · exact source_error_17_11_15
  · exact source_error_17_11_17
  · exact source_error_17_13_1
  · exact source_error_17_13_3
  · exact source_error_17_13_5
  · exact source_error_17_13_7
  · exact source_error_17_13_9
  · exact source_error_17_13_11
  · exact source_error_17_13_13
  · exact source_error_17_13_15
  · exact source_error_17_13_17
  · exact source_error_17_15_1
  · exact source_error_17_15_3
  · exact source_error_17_15_5
  · exact source_error_17_15_7
  · exact source_error_17_15_9
  · exact source_error_17_15_11
  · exact source_error_17_15_13
  · exact source_error_17_15_15
  · exact source_error_17_15_17
  · exact source_error_17_17_1
  · exact source_error_17_17_3
  · exact source_error_17_17_5
  · exact source_error_17_17_7
  · exact source_error_17_17_9
  · exact source_error_17_17_11
  · exact source_error_17_17_13
  · exact source_error_17_17_15
  · exact source_error_17_17_17

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_17_oai := @OAI.Laughlin.Certificate.error_17_oai
