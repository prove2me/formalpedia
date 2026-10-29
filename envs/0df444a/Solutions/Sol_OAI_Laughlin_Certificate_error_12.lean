-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:30:45.717192+00:00
-- url     : https://prove2.me/submissions/bc93eb55-9f94-4c22-a5bd-853b5c56ec99

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_11_11_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_11_11_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_11_11_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_11_11_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_1_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_1_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_1_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_1_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_3_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_7_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_7_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_1_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_11_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_11_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_11_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_11_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_3_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_7_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_7_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_3_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_11_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_11_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_11_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_5_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_5_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_9_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_9_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_5_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_9_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_9_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_7_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_9_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_9_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_9_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_9_9_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_9_9_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_9_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_12_9_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_eq_integral

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0101Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_1_1 : RowCompute.yRowIntegralFast 12 1 1 (RowCompute.rows[1]!) =
    (671735412855409199535569770581127279414325722579206144000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_1_3 : RowCompute.yRowIntegralFast 12 1 1 (RowCompute.rows[3]!) =
    (621952235091331719841252169030111105761786130004090814464000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_1_5 : RowCompute.yRowIntegralFast 12 1 1 (RowCompute.rows[5]!) =
    (-536849342902533143347789184472491993991776940853196488704000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0103Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_3_0 : RowCompute.yRowIntegralFast 12 1 3 (RowCompute.rows[0]!) =
    (-196775512849465287080969322833699760490568941951090950144000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_3_2 : RowCompute.yRowIntegralFast 12 1 3 (RowCompute.rows[2]!) =
    (-32115184034290410885800576273756359566135299294625792000000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_3_4 : RowCompute.yRowIntegralFast 12 1 3 (RowCompute.rows[4]!) =
    (13220609787632429054836035252489220598338648344436408320000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_3_6 : RowCompute.yRowIntegralFast 12 1 3 (RowCompute.rows[6]!) =
    (-885964026515646379516617259202599300271694751733907456000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0105Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_5_1 : RowCompute.yRowIntegralFast 12 1 5 (RowCompute.rows[1]!) =
    (27152880227336574060529794889932048648912590881161216000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_5_2 : RowCompute.yRowIntegralFast 12 1 5 (RowCompute.rows[2]!) =
    (-81701130133253266665298826694859764548647358819481944064000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_5_4 : RowCompute.yRowIntegralFast 12 1 5 (RowCompute.rows[4]!) =
    (9404574524248096962307111827989443046311205597047947264000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_5_6 : RowCompute.yRowIntegralFast 12 1 5 (RowCompute.rows[6]!) =
    (-2740928281497409753778614344231166981083692847996076032000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0107Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_7_1 : RowCompute.yRowIntegralFast 12 1 7 (RowCompute.rows[1]!) =
    (113190076560567182421422818074964224678904371773177856000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_7_3 : RowCompute.yRowIntegralFast 12 1 7 (RowCompute.rows[3]!) =
    (6881890153612552789628190355270336690592553520645275648000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_7_5 : RowCompute.yRowIntegralFast 12 1 7 (RowCompute.rows[5]!) =
    (-11729501378692386743828951431230939111664691397223514112000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0109Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_9_0 : RowCompute.yRowIntegralFast 12 1 9 (RowCompute.rows[0]!) =
    (-85126299178059846133725660876598433275654095372866813952000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_9_2 : RowCompute.yRowIntegralFast 12 1 9 (RowCompute.rows[2]!) =
    (76569500257540825089332374457139565745144769910539288576000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_9_4 : RowCompute.yRowIntegralFast 12 1 9 (RowCompute.rows[4]!) =
    (-37976080224086935426247384223774357466170257593029623808000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_9_6 : RowCompute.yRowIntegralFast 12 1 9 (RowCompute.rows[6]!) =
    (7954932982287226150534871797412594538494971592696659968000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0111Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_11_0 : RowCompute.yRowIntegralFast 12 1 11 (RowCompute.rows[0]!) =
    (481077275430837001742280097786325532478131041010632884224000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_11_2 : RowCompute.yRowIntegralFast 12 1 11 (RowCompute.rows[2]!) =
    (-646879885891658974561265461577815519924820658298124500992000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_11_4 : RowCompute.yRowIntegralFast 12 1 11 (RowCompute.rows[4]!) =
    (9659498784058373310893900315128761774073041193726377984000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_1_11_6 : RowCompute.yRowIntegralFast 12 1 11 (RowCompute.rows[6]!) =
    (-6585194169279825765781974769702892036699894826110287872000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0303Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_3_0 : RowCompute.yRowIntegralFast 12 3 3 (RowCompute.rows[0]!) =
    (41461276593006872565065809524081593554664037841297735680000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_3_2 : RowCompute.yRowIntegralFast 12 3 3 (RowCompute.rows[2]!) =
    (27741311928554603283475427138454733312240567618332996403200000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_3_3 : RowCompute.yRowIntegralFast 12 3 3 (RowCompute.rows[3]!) =
    (5534656618421033148512167741476365614750868249665496678400000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_3_5 : RowCompute.yRowIntegralFast 12 3 3 (RowCompute.rows[5]!) =
    (2081983473510613031345994043401061719843303604194430156800000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0305Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_5_0 : RowCompute.yRowIntegralFast 12 3 5 (RowCompute.rows[0]!) =
    (3369441653282420359678222274909903880391084706044575744000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_5_2 : RowCompute.yRowIntegralFast 12 3 5 (RowCompute.rows[2]!) =
    (-7587337748763051255530392557297867915034674976832618496000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_5_4 : RowCompute.yRowIntegralFast 12 3 5 (RowCompute.rows[4]!) =
    (-2506182736435097915659043733293976138875453847090757632000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_5_6 : RowCompute.yRowIntegralFast 12 3 5 (RowCompute.rows[6]!) =
    (-5201898597240615551203015610576016683138731909054464000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0307Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_7_1 : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[1]!) =
    (13549803797735789813936887616698854267118994168217600000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_7_3 : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[3]!) =
    (1496715818226223856119740482170569756427532353847427072000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_7_5 : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[5]!) =
    (-4791453340420801717126374106504423598156623101793665024000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0309Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_9_0 : RowCompute.yRowIntegralFast 12 3 9 (RowCompute.rows[0]!) =
    (-60530427249738445929122741564647727375458214643171852288000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_9_2 : RowCompute.yRowIntegralFast 12 3 9 (RowCompute.rows[2]!) =
    (-964742535900692286416475407733403445584107880523287756800000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_9_4 : RowCompute.yRowIntegralFast 12 3 9 (RowCompute.rows[4]!) =
    (5978413118614617964378291397080397990191953497534811340800000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_9_6 : RowCompute.yRowIntegralFast 12 3 9 (RowCompute.rows[6]!) =
    (-549998067233687372359833945619596189813851348760998707200000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0311Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_11_1 : RowCompute.yRowIntegralFast 12 3 11 (RowCompute.rows[1]!) =
    (195809368573058066694001332733119401449655478145725235200000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_11_3 : RowCompute.yRowIntegralFast 12 3 11 (RowCompute.rows[3]!) =
    (50104797314168890396053616907118639379909721980693118976000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_3_11_5 : RowCompute.yRowIntegralFast 12 3 11 (RowCompute.rows[5]!) =
    (5278596523721062797652195527124764569421593415209975808000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0505Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_5_5_1 : RowCompute.yRowIntegralFast 12 5 5 (RowCompute.rows[1]!) =
    (33355728852078358315389433567927301785315519141773312000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_5_3 : RowCompute.yRowIntegralFast 12 5 5 (RowCompute.rows[3]!) =
    (-5862440473609337281803249894403489746947100036393074688000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_5_5 : RowCompute.yRowIntegralFast 12 5 5 (RowCompute.rows[5]!) =
    (-1143405287553199394589479945842185472440397209695944704000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0507Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_5_7_0 : RowCompute.yRowIntegralFast 12 5 7 (RowCompute.rows[0]!) =
    (12821997692782225172834197938257002209379526093618282496000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_7_2 : RowCompute.yRowIntegralFast 12 5 7 (RowCompute.rows[2]!) =
    (-6874565592331898908072178846236087299802322590765154304000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_7_4 : RowCompute.yRowIntegralFast 12 5 7 (RowCompute.rows[4]!) =
    (960874491372527866035887619418653629552545228702875648000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_7_6 : RowCompute.yRowIntegralFast 12 5 7 (RowCompute.rows[6]!) =
    (-263619729973423206390461936853866998910559847515684864000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0509Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_5_9_1 : RowCompute.yRowIntegralFast 12 5 9 (RowCompute.rows[1]!) =
    (38871762405702958022761982987709153762817791875874816000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_9_3 : RowCompute.yRowIntegralFast 12 5 9 (RowCompute.rows[3]!) =
    (5489554785388152337981369557158040616705655103874400256000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_9_5 : RowCompute.yRowIntegralFast 12 5 9 (RowCompute.rows[5]!) =
    (8374932871197537253018933623145906985718582435687432192000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0511Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_5_11_1 : RowCompute.yRowIntegralFast 12 5 11 (RowCompute.rows[1]!) =
    (-122326551937396348001019302123076594290428526312030208000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_11_3 : RowCompute.yRowIntegralFast 12 5 11 (RowCompute.rows[3]!) =
    (58600524545616945049902333948374998034393157373343563776000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_11_5 : RowCompute.yRowIntegralFast 12 5 11 (RowCompute.rows[5]!) =
    (-2981460981677534318038258611590574281490069567439896576000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_5_11_6 : RowCompute.yRowIntegralFast 12 5 11 (RowCompute.rows[6]!) =
    (1207098362015705855047642377906942393371424042541645824000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0707Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_7_7_0 : RowCompute.yRowIntegralFast 12 7 7 (RowCompute.rows[0]!) =
    (35370211749595582883277719762705927081235264737233600512000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_7_7_2 : RowCompute.yRowIntegralFast 12 7 7 (RowCompute.rows[2]!) =
    (7231373572635294930634364842516230661441722303324880896000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_7_7_4 : RowCompute.yRowIntegralFast 12 7 7 (RowCompute.rows[4]!) =
    (-972867907861073458668450582666912587753683873110687744000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_7_7_6 : RowCompute.yRowIntegralFast 12 7 7 (RowCompute.rows[6]!) =
    (-880198703516287838236617138433012622297031735785816064000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0709Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_7_9_1 : RowCompute.yRowIntegralFast 12 7 9 (RowCompute.rows[1]!) =
    (-73946735024890602795002641407505030019928441451708416000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_7_9_3 : RowCompute.yRowIntegralFast 12 7 9 (RowCompute.rows[3]!) =
    (2055898570305386876691108623567675094823890680121655296000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_7_9_5 : RowCompute.yRowIntegralFast 12 7 9 (RowCompute.rows[5]!) =
    (-2871605427232987440747193942431586527191071218607325184000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0711Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_7_11_0 : RowCompute.yRowIntegralFast 12 7 11 (RowCompute.rows[0]!) =
    (6243301823331924469480948156093515473855047359201804288000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_7_11_2 : RowCompute.yRowIntegralFast 12 7 11 (RowCompute.rows[2]!) =
    (-154969558023071117668665275862411488284417144878268416000000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_7_11_4 : RowCompute.yRowIntegralFast 12 7 11 (RowCompute.rows[4]!) =
    (5407090718951222569349027087115709753600723907971645440000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_7_11_6 : RowCompute.yRowIntegralFast 12 7 11 (RowCompute.rows[6]!) =
    (-73663307664189648292730470180827169760400142755692544000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0909Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_9_9_1 : RowCompute.yRowIntegralFast 12 9 9 (RowCompute.rows[1]!) =
    (202731616313241215871299358974085698923892384449796505600000 : ℤ) := by
  decide +kernel

theorem computeRow_12_9_9_3 : RowCompute.yRowIntegralFast 12 9 9 (RowCompute.rows[3]!) =
    (-10412793826694913331291073596729199627330590535300677632000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_9_9_5 : RowCompute.yRowIntegralFast 12 9 9 (RowCompute.rows[5]!) =
    (7257535002610642083816751457928905349466196000451959193600000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0911Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_9_11_0 : RowCompute.yRowIntegralFast 12 9 11 (RowCompute.rows[0]!) =
    (-4689675043668065755253051928400270943885634867698860032000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_9_11_2 : RowCompute.yRowIntegralFast 12 9 11 (RowCompute.rows[2]!) =
    (30591817468576946078476570520140842753620055343000190976000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_9_11_4 : RowCompute.yRowIntegralFast 12 9 11 (RowCompute.rows[4]!) =
    (-2384490262579555119141547260088483057667203622951190528000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_9_11_6 : RowCompute.yRowIntegralFast 12 9 11 (RowCompute.rows[6]!) =
    (1247979223815282825915786926562098286333444538993999872000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1111Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_11_11_1 : RowCompute.yRowIntegralFast 12 11 11 (RowCompute.rows[1]!) =
    (815827313101322000298987518736466368517566902600466432000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_11_11_3 : RowCompute.yRowIntegralFast 12 11 11 (RowCompute.rows[3]!) =
    (2764308517805148245666011112813744257710339592990551441408000000 : ℤ) := by
  decide +kernel

theorem computeRow_12_11_11_5 : RowCompute.yRowIntegralFast 12 11 11 (RowCompute.rows[5]!) =
    (135450024658382832554861380514815076967262683078504480768000000 : ℤ) := by
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

theorem Y_symm (D r s : ℕ) : Y D r s = Y D s r := by
  unfold Y
  congr 3
  apply List.map_congr_left
  intro row hr
  exact yRow_swap D r s row (rows_valid row hr)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem source_error_12_1_1 : Y 12 1 1 = (-21758497948837526814361611/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 1 0 (by decide),
    source_yRow_eq_rowCompute 12 1 1 1 (by decide),
    source_yRow_eq_rowCompute 12 1 1 2 (by decide),
    source_yRow_eq_rowCompute 12 1 1 3 (by decide),
    source_yRow_eq_rowCompute 12 1 1 4 (by decide),
    source_yRow_eq_rowCompute 12 1 1 5 (by decide),
    source_yRow_eq_rowCompute 12 1 1 6 (by decide),
    computeRow_12_1_1_0, computeRow_12_1_1_1, computeRow_12_1_1_2, computeRow_12_1_1_3, computeRow_12_1_1_4, computeRow_12_1_1_5, computeRow_12_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_3 : Y 12 1 3 = (7514500960705467759694389/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 3 0 (by decide),
    source_yRow_eq_rowCompute 12 1 3 1 (by decide),
    source_yRow_eq_rowCompute 12 1 3 2 (by decide),
    source_yRow_eq_rowCompute 12 1 3 3 (by decide),
    source_yRow_eq_rowCompute 12 1 3 4 (by decide),
    source_yRow_eq_rowCompute 12 1 3 5 (by decide),
    source_yRow_eq_rowCompute 12 1 3 6 (by decide),
    computeRow_12_1_3_0, computeRow_12_1_3_1, computeRow_12_1_3_2, computeRow_12_1_3_3, computeRow_12_1_3_4, computeRow_12_1_3_5, computeRow_12_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_5 : Y 12 1 5 = (3165688667606660909537571/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 5 0 (by decide),
    source_yRow_eq_rowCompute 12 1 5 1 (by decide),
    source_yRow_eq_rowCompute 12 1 5 2 (by decide),
    source_yRow_eq_rowCompute 12 1 5 3 (by decide),
    source_yRow_eq_rowCompute 12 1 5 4 (by decide),
    source_yRow_eq_rowCompute 12 1 5 5 (by decide),
    source_yRow_eq_rowCompute 12 1 5 6 (by decide),
    computeRow_12_1_5_0, computeRow_12_1_5_1, computeRow_12_1_5_2, computeRow_12_1_5_3, computeRow_12_1_5_4, computeRow_12_1_5_5, computeRow_12_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_7 : Y 12 1 7 = (-41707520784065633150907/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 7 0 (by decide),
    source_yRow_eq_rowCompute 12 1 7 1 (by decide),
    source_yRow_eq_rowCompute 12 1 7 2 (by decide),
    source_yRow_eq_rowCompute 12 1 7 3 (by decide),
    source_yRow_eq_rowCompute 12 1 7 4 (by decide),
    source_yRow_eq_rowCompute 12 1 7 5 (by decide),
    source_yRow_eq_rowCompute 12 1 7 6 (by decide),
    computeRow_12_1_7_0, computeRow_12_1_7_1, computeRow_12_1_7_2, computeRow_12_1_7_3, computeRow_12_1_7_4, computeRow_12_1_7_5, computeRow_12_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_9 : Y 12 1 9 = (-2287894342236011100448461/10485760000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 9 0 (by decide),
    source_yRow_eq_rowCompute 12 1 9 1 (by decide),
    source_yRow_eq_rowCompute 12 1 9 2 (by decide),
    source_yRow_eq_rowCompute 12 1 9 3 (by decide),
    source_yRow_eq_rowCompute 12 1 9 4 (by decide),
    source_yRow_eq_rowCompute 12 1 9 5 (by decide),
    source_yRow_eq_rowCompute 12 1 9 6 (by decide),
    computeRow_12_1_9_0, computeRow_12_1_9_1, computeRow_12_1_9_2, computeRow_12_1_9_3, computeRow_12_1_9_4, computeRow_12_1_9_5, computeRow_12_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_11 : Y 12 1 11 = (974459105668097994666249/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 11 0 (by decide),
    source_yRow_eq_rowCompute 12 1 11 1 (by decide),
    source_yRow_eq_rowCompute 12 1 11 2 (by decide),
    source_yRow_eq_rowCompute 12 1 11 3 (by decide),
    source_yRow_eq_rowCompute 12 1 11 4 (by decide),
    source_yRow_eq_rowCompute 12 1 11 5 (by decide),
    source_yRow_eq_rowCompute 12 1 11 6 (by decide),
    computeRow_12_1_11_0, computeRow_12_1_11_1, computeRow_12_1_11_2, computeRow_12_1_11_3, computeRow_12_1_11_4, computeRow_12_1_11_5, computeRow_12_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_3 : Y 12 3 3 = (-2755174567464265689714987/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 3 0 (by decide),
    source_yRow_eq_rowCompute 12 3 3 1 (by decide),
    source_yRow_eq_rowCompute 12 3 3 2 (by decide),
    source_yRow_eq_rowCompute 12 3 3 3 (by decide),
    source_yRow_eq_rowCompute 12 3 3 4 (by decide),
    source_yRow_eq_rowCompute 12 3 3 5 (by decide),
    source_yRow_eq_rowCompute 12 3 3 6 (by decide),
    computeRow_12_3_3_0, computeRow_12_3_3_1, computeRow_12_3_3_2, computeRow_12_3_3_3, computeRow_12_3_3_4, computeRow_12_3_3_5, computeRow_12_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_5 : Y 12 3 5 = (13005450739700130750669/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 5 0 (by decide),
    source_yRow_eq_rowCompute 12 3 5 1 (by decide),
    source_yRow_eq_rowCompute 12 3 5 2 (by decide),
    source_yRow_eq_rowCompute 12 3 5 3 (by decide),
    source_yRow_eq_rowCompute 12 3 5 4 (by decide),
    source_yRow_eq_rowCompute 12 3 5 5 (by decide),
    source_yRow_eq_rowCompute 12 3 5 6 (by decide),
    computeRow_12_3_5_0, computeRow_12_3_5_1, computeRow_12_3_5_2, computeRow_12_3_5_3, computeRow_12_3_5_4, computeRow_12_3_5_5, computeRow_12_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_7 : Y 12 3 7 = (81483121238154923538567/4194304000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 7 0 (by decide),
    source_yRow_eq_rowCompute 12 3 7 1 (by decide),
    source_yRow_eq_rowCompute 12 3 7 2 (by decide),
    source_yRow_eq_rowCompute 12 3 7 3 (by decide),
    source_yRow_eq_rowCompute 12 3 7 4 (by decide),
    source_yRow_eq_rowCompute 12 3 7 5 (by decide),
    source_yRow_eq_rowCompute 12 3 7 6 (by decide),
    computeRow_12_3_7_0, computeRow_12_3_7_1, computeRow_12_3_7_2, computeRow_12_3_7_3, computeRow_12_3_7_4, computeRow_12_3_7_5, computeRow_12_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_9 : Y 12 3 9 = (404785016635235824043973/5242880000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 9 0 (by decide),
    source_yRow_eq_rowCompute 12 3 9 1 (by decide),
    source_yRow_eq_rowCompute 12 3 9 2 (by decide),
    source_yRow_eq_rowCompute 12 3 9 3 (by decide),
    source_yRow_eq_rowCompute 12 3 9 4 (by decide),
    source_yRow_eq_rowCompute 12 3 9 5 (by decide),
    source_yRow_eq_rowCompute 12 3 9 6 (by decide),
    computeRow_12_3_9_0, computeRow_12_3_9_1, computeRow_12_3_9_2, computeRow_12_3_9_3, computeRow_12_3_9_4, computeRow_12_3_9_5, computeRow_12_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_11 : Y 12 3 11 = (6215584013984995241823/40960000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 11 0 (by decide),
    source_yRow_eq_rowCompute 12 3 11 1 (by decide),
    source_yRow_eq_rowCompute 12 3 11 2 (by decide),
    source_yRow_eq_rowCompute 12 3 11 3 (by decide),
    source_yRow_eq_rowCompute 12 3 11 4 (by decide),
    source_yRow_eq_rowCompute 12 3 11 5 (by decide),
    source_yRow_eq_rowCompute 12 3 11 6 (by decide),
    computeRow_12_3_11_0, computeRow_12_3_11_1, computeRow_12_3_11_2, computeRow_12_3_11_3, computeRow_12_3_11_4, computeRow_12_3_11_5, computeRow_12_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_5_5 : Y 12 5 5 = (46805674377515194537803/3355443200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 5 5 0 (by decide),
    source_yRow_eq_rowCompute 12 5 5 1 (by decide),
    source_yRow_eq_rowCompute 12 5 5 2 (by decide),
    source_yRow_eq_rowCompute 12 5 5 3 (by decide),
    source_yRow_eq_rowCompute 12 5 5 4 (by decide),
    source_yRow_eq_rowCompute 12 5 5 5 (by decide),
    source_yRow_eq_rowCompute 12 5 5 6 (by decide),
    computeRow_12_5_5_0, computeRow_12_5_5_1, computeRow_12_5_5_2, computeRow_12_5_5_3, computeRow_12_5_5_4, computeRow_12_5_5_5, computeRow_12_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_5_7 : Y 12 5 7 = (-41483885509932371903727/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 5 7 0 (by decide),
    source_yRow_eq_rowCompute 12 5 7 1 (by decide),
    source_yRow_eq_rowCompute 12 5 7 2 (by decide),
    source_yRow_eq_rowCompute 12 5 7 3 (by decide),
    source_yRow_eq_rowCompute 12 5 7 4 (by decide),
    source_yRow_eq_rowCompute 12 5 7 5 (by decide),
    source_yRow_eq_rowCompute 12 5 7 6 (by decide),
    computeRow_12_5_7_0, computeRow_12_5_7_1, computeRow_12_5_7_2, computeRow_12_5_7_3, computeRow_12_5_7_4, computeRow_12_5_7_5, computeRow_12_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_5_9 : Y 12 5 9 = (-10240121934522536047317/419430400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 5 9 0 (by decide),
    source_yRow_eq_rowCompute 12 5 9 1 (by decide),
    source_yRow_eq_rowCompute 12 5 9 2 (by decide),
    source_yRow_eq_rowCompute 12 5 9 3 (by decide),
    source_yRow_eq_rowCompute 12 5 9 4 (by decide),
    source_yRow_eq_rowCompute 12 5 9 5 (by decide),
    source_yRow_eq_rowCompute 12 5 9 6 (by decide),
    computeRow_12_5_9_0, computeRow_12_5_9_1, computeRow_12_5_9_2, computeRow_12_5_9_3, computeRow_12_5_9_4, computeRow_12_5_9_5, computeRow_12_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_5_11 : Y 12 5 11 = (-25627330574660171363787/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 5 11 0 (by decide),
    source_yRow_eq_rowCompute 12 5 11 1 (by decide),
    source_yRow_eq_rowCompute 12 5 11 2 (by decide),
    source_yRow_eq_rowCompute 12 5 11 3 (by decide),
    source_yRow_eq_rowCompute 12 5 11 4 (by decide),
    source_yRow_eq_rowCompute 12 5 11 5 (by decide),
    source_yRow_eq_rowCompute 12 5 11 6 (by decide),
    computeRow_12_5_11_0, computeRow_12_5_11_1, computeRow_12_5_11_2, computeRow_12_5_11_3, computeRow_12_5_11_4, computeRow_12_5_11_5, computeRow_12_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_7_7 : Y 12 7 7 = (-192219299280069275276433/4194304000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 7 7 0 (by decide),
    source_yRow_eq_rowCompute 12 7 7 1 (by decide),
    source_yRow_eq_rowCompute 12 7 7 2 (by decide),
    source_yRow_eq_rowCompute 12 7 7 3 (by decide),
    source_yRow_eq_rowCompute 12 7 7 4 (by decide),
    source_yRow_eq_rowCompute 12 7 7 5 (by decide),
    source_yRow_eq_rowCompute 12 7 7 6 (by decide),
    computeRow_12_7_7_0, computeRow_12_7_7_1, computeRow_12_7_7_2, computeRow_12_7_7_3, computeRow_12_7_7_4, computeRow_12_7_7_5, computeRow_12_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_7_9 : Y 12 7 9 = (-42262827210616968341919/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 7 9 0 (by decide),
    source_yRow_eq_rowCompute 12 7 9 1 (by decide),
    source_yRow_eq_rowCompute 12 7 9 2 (by decide),
    source_yRow_eq_rowCompute 12 7 9 3 (by decide),
    source_yRow_eq_rowCompute 12 7 9 4 (by decide),
    source_yRow_eq_rowCompute 12 7 9 5 (by decide),
    source_yRow_eq_rowCompute 12 7 9 6 (by decide),
    computeRow_12_7_9_0, computeRow_12_7_9_1, computeRow_12_7_9_2, computeRow_12_7_9_3, computeRow_12_7_9_4, computeRow_12_7_9_5, computeRow_12_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_7_11 : Y 12 7 11 = (102387833991081458685459/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 7 11 0 (by decide),
    source_yRow_eq_rowCompute 12 7 11 1 (by decide),
    source_yRow_eq_rowCompute 12 7 11 2 (by decide),
    source_yRow_eq_rowCompute 12 7 11 3 (by decide),
    source_yRow_eq_rowCompute 12 7 11 4 (by decide),
    source_yRow_eq_rowCompute 12 7 11 5 (by decide),
    source_yRow_eq_rowCompute 12 7 11 6 (by decide),
    computeRow_12_7_11_0, computeRow_12_7_11_1, computeRow_12_7_11_2, computeRow_12_7_11_3, computeRow_12_7_11_4, computeRow_12_7_11_5, computeRow_12_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_9_9 : Y 12 9 9 = (42184147125974825030859/1310720000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 9 9 0 (by decide),
    source_yRow_eq_rowCompute 12 9 9 1 (by decide),
    source_yRow_eq_rowCompute 12 9 9 2 (by decide),
    source_yRow_eq_rowCompute 12 9 9 3 (by decide),
    source_yRow_eq_rowCompute 12 9 9 4 (by decide),
    source_yRow_eq_rowCompute 12 9 9 5 (by decide),
    source_yRow_eq_rowCompute 12 9 9 6 (by decide),
    computeRow_12_9_9_0, computeRow_12_9_9_1, computeRow_12_9_9_2, computeRow_12_9_9_3, computeRow_12_9_9_4, computeRow_12_9_9_5, computeRow_12_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_9_11 : Y 12 9 11 = (18732467483584451907057/655360000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 9 11 0 (by decide),
    source_yRow_eq_rowCompute 12 9 11 1 (by decide),
    source_yRow_eq_rowCompute 12 9 11 2 (by decide),
    source_yRow_eq_rowCompute 12 9 11 3 (by decide),
    source_yRow_eq_rowCompute 12 9 11 4 (by decide),
    source_yRow_eq_rowCompute 12 9 11 5 (by decide),
    source_yRow_eq_rowCompute 12 9 11 6 (by decide),
    computeRow_12_9_11_0, computeRow_12_9_11_1, computeRow_12_9_11_2, computeRow_12_9_11_3, computeRow_12_9_11_4, computeRow_12_9_11_5, computeRow_12_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_11_11 : Y 12 11 11 = (-330567209557174956464307/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 11 11 0 (by decide),
    source_yRow_eq_rowCompute 12 11 11 1 (by decide),
    source_yRow_eq_rowCompute 12 11 11 2 (by decide),
    source_yRow_eq_rowCompute 12 11 11 3 (by decide),
    source_yRow_eq_rowCompute 12 11 11 4 (by decide),
    source_yRow_eq_rowCompute 12 11 11 5 (by decide),
    source_yRow_eq_rowCompute 12 11 11 6 (by decide),
    computeRow_12_11_11_0, computeRow_12_11_11_1, computeRow_12_11_11_2, computeRow_12_11_11_3, computeRow_12_11_11_4, computeRow_12_11_11_5, computeRow_12_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_1 : Y 12 3 1 = (7514500960705467759694389/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_3

theorem source_error_12_5_1 : Y 12 5 1 = (3165688667606660909537571/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_5

theorem source_error_12_5_3 : Y 12 5 3 = (13005450739700130750669/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_5

theorem source_error_12_7_1 : Y 12 7 1 = (-41707520784065633150907/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_7

theorem source_error_12_7_3 : Y 12 7 3 = (81483121238154923538567/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_7

theorem source_error_12_7_5 : Y 12 7 5 = (-41483885509932371903727/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_7

theorem source_error_12_9_1 : Y 12 9 1 = (-2287894342236011100448461/10485760000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_9

theorem source_error_12_9_3 : Y 12 9 3 = (404785016635235824043973/5242880000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_9

theorem source_error_12_9_5 : Y 12 9 5 = (-10240121934522536047317/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_9

theorem source_error_12_9_7 : Y 12 9 7 = (-42262827210616968341919/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_7_9

theorem source_error_12_11_1 : Y 12 11 1 = (974459105668097994666249/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_11

theorem source_error_12_11_3 : Y 12 11 3 = (6215584013984995241823/40960000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_11

theorem source_error_12_11_5 : Y 12 11 5 = (-25627330574660171363787/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_11

theorem source_error_12_11_7 : Y 12 11 7 = (102387833991081458685459/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_7_11

theorem source_error_12_11_9 : Y 12 11 9 = (18732467483584451907057/655360000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_9_11

theorem error_12_oai : errorRational 12 = candidateY_12 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_12_1_1
  · exact source_error_12_1_3
  · exact source_error_12_1_5
  · exact source_error_12_1_7
  · exact source_error_12_1_9
  · exact source_error_12_1_11
  · exact source_error_12_3_1
  · exact source_error_12_3_3
  · exact source_error_12_3_5
  · exact source_error_12_3_7
  · exact source_error_12_3_9
  · exact source_error_12_3_11
  · exact source_error_12_5_1
  · exact source_error_12_5_3
  · exact source_error_12_5_5
  · exact source_error_12_5_7
  · exact source_error_12_5_9
  · exact source_error_12_5_11
  · exact source_error_12_7_1
  · exact source_error_12_7_3
  · exact source_error_12_7_5
  · exact source_error_12_7_7
  · exact source_error_12_7_9
  · exact source_error_12_7_11
  · exact source_error_12_9_1
  · exact source_error_12_9_3
  · exact source_error_12_9_5
  · exact source_error_12_9_7
  · exact source_error_12_9_9
  · exact source_error_12_9_11
  · exact source_error_12_11_1
  · exact source_error_12_11_3
  · exact source_error_12_11_5
  · exact source_error_12_11_7
  · exact source_error_12_11_9
  · exact source_error_12_11_11

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.error_12_oai := @OAI.Laughlin.Certificate.error_12_oai
