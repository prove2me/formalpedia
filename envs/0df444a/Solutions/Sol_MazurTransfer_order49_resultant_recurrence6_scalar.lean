-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:57:13.608915+00:00
-- url     : https://prove2.me/submissions/ea5e6d4d-9bda-41b3-a058-bb5442ca8dc5

import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_normalized_scalar
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData0. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial data for the order-seven branch-zero resultant PRS

This file starts the exact primitive pseudo-remainder sequence over
`ℚ[D][X]` for the selection cofactor and the first degree-seven
division cofactor. Each generated remainder is grouped by its outer
`X` coefficient; the first quotient remains exact table data, while
the later linear quotients are forced by the leading two coefficients.
Lean recurrence certificates check the untrusted generating computation.
-/
section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

noncomputable section






theorem coefficientTerm_eq_C_mul_X_pow
    (degree : ℕ) (coefficient : ℚ) :
    coefficientTerm degree coefficient =
      C coefficient * X ^ degree := by
  exact C_mul_X_pow_eq_monomial.symm





































































































































































































































































































































































































































































































































































































































































































































































end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData6. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Step 6 data for the order-seven branch-zero resultant PRS

This serial data shard records one normalized primitive remainder and
exceptional content factor. Its linear pseudo-division quotient is
derived from leading coefficients and checked by the Lean recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

noncomputable section











def exceptionalUnit6 : Coefficient :=
  C
    (((((((26813799997641 : ℚ) * 10 ^ 36 +
      142369575613846289747847827330896388) * 10 ^ 36 +
      174087143449204393900331622823388931) * 10 ^ 36 +
      504208118624079313576123579518587434) * 10 ^ 36 +
      856069465570511249870923189965244671) * 10 ^ 36 +
      650107475862081909428552923558342334) * 10 ^ 36 +
      248809782697354987477701994402490000)

def exceptional6 : Coefficient :=
  exceptionalUnit6 *
  (parameter - 1) ^ 1 *
  (discriminantFactor) ^ 6 *
  (cmTwelve) ^ 1



end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6BlockData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: BlockData

This compatibility module re-exports the independently checked literal-data
shards for the sixth pseudo-division recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem normalizedExceptional6_eq :
    normalizedExceptional6 =
      (parameter - 1) * discriminantFactor ^ 6 * cmTwelve := by
  unfold normalizedExceptional6 normalizedExceptional6Block0 normalizedExceptional6Block1
  unfold normalizedExceptional6Block2 normalizedExceptional6Block3 discriminantFactor cmTwelve
  unfold parameter
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6NormalizedScalar. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: NormalizedScalar

This file is a checked arithmetic shard for the sixth pseudo-division
recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem normalizedScalarResidual6 :
    remainder7Coefficient1Normalized ^ 2 *
        remainder6Coefficient0Normalized =
      remainder7Coefficient0Normalized *
          (remainder7Coefficient1Normalized *
              remainder6Coefficient1Normalized -
            remainder7Coefficient0Normalized *
              remainder6Coefficient2Normalized) -
        remainder6Coefficient2Normalized ^ 2 *
          normalizedExceptional6 := by
  exact MazurTransfer.order49_resultant_recurrence6_normalized_scalar


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6ActualScalar. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: ActualScalar

This file is a checked arithmetic shard for the sixth pseudo-division
recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section





private def recurrence6Content6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (169974242287568876381639744907962243436895047572089)
  )))

private def recurrence6Content7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
      76164207728007698297318822544326745362653178990742192636567850547586675788100))
  )))

private def remainder6Coefficient0AlignedChunk0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1011392369)
  ))) * X ^ 153 +
  (Polynomial.C (show ℚ from (
    (-40522055413147560)
  ))) * X ^ 152 +
  (Polynomial.C (show ℚ from (
    (-43357899036499587396088)
  ))) * X ^ 151 +
  (Polynomial.C (show ℚ from (
    (-2933260314236696862010807052)
  ))) * X ^ 150 +
  (Polynomial.C (show ℚ from (
    (-25060547349737891843516424822013)
  ))) * X ^ 149 +
  (Polynomial.C (show ℚ from (
    (-37303409421719864169581552912054227)
  ))) * X ^ 148 +
  (Polynomial.C (show ℚ from (
    (-6664154253035422565434310513723014473)
  ))) * X ^ 147 +
  (Polynomial.C (show ℚ from (
    (8134043698377643468887670751448365521145)
  ))) * X ^ 146

private theorem remainder6Coefficient0Chunk0_normalized :
    remainder6Coefficient0Chunk0 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk0 := by
  unfold remainder6Coefficient0Chunk0 remainder6Coefficient0AlignedChunk0
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (4097015695492371739826329824989209203367262)
  ))) * X ^ 145 +
  (Polynomial.C (show ℚ from (
    (720497376836365789771706356156031624629128769)
  ))) * X ^ 144 +
  (Polynomial.C (show ℚ from (
    (51180106368914433882879910916647390729071029891)
  ))) * X ^ 143 +
  (Polynomial.C (show ℚ from (
    (1124513794129348728267163654844646077985631241883)
  ))) * X ^ 142 +
  (Polynomial.C (show ℚ from (
    (-5936880140781240810156398491591308405122099790362)
  ))) * X ^ 141 +
  (Polynomial.C (show ℚ from (
    (-225637739201328317741010866003929708465314470308722)
  ))) * X ^ 140 +
  (Polynomial.C (show ℚ from (
    (1640763020833435260328793390724491197677689490448216)
  ))) * X ^ 139 +
  (Polynomial.C (show ℚ from (
    (13830510745960661250169911443628707195581541111929709)
  ))) * X ^ 138

private theorem remainder6Coefficient0Chunk1_normalized :
    remainder6Coefficient0Chunk1 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk1 := by
  unfold remainder6Coefficient0Chunk1 remainder6Coefficient0AlignedChunk1
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-222308451621338922645283676695166015302402257964224032)
  ))) * X ^ 137 +
  (Polynomial.C (show ℚ from (
    (816990963221813020303938577140743131751025606122261243)
  ))) * X ^ 136 +
  (Polynomial.C (show ℚ from (
    (4026282148141467705170099569081456097602533694427138661)
  ))) * X ^ 135 +
  (Polynomial.C (show ℚ from (
    (-57552519342706272011320757210885952062399753522898777293)
  ))) * X ^ 134 +
  (Polynomial.C (show ℚ from (
    (283068179503719821855505984060517063926743570210527486177)
  ))) * X ^ 133 +
  (Polynomial.C (show ℚ from (
    (-577831655991145443155503224347531013768994337594877967975)
  ))) * X ^ 132 +
  (Polynomial.C (show ℚ from (
    (-1340676479236975758305973107443056024481803453846874024787)
  ))) * X ^ 131 +
  (Polynomial.C (show ℚ from (
    (14737496869073084554441130110488277083264282977945034116736)
  ))) * X ^ 130

private theorem remainder6Coefficient0Chunk2_normalized :
    remainder6Coefficient0Chunk2 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk2 := by
  unfold remainder6Coefficient0Chunk2 remainder6Coefficient0AlignedChunk2
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-55812988878064651281148901532524626925833772159512955627475)
  ))) * X ^ 129 +
  (Polynomial.C (show ℚ from (
    (101287261705211680714786891227418204256889070569152114806074)
  ))) * X ^ 128 +
  (Polynomial.C (show ℚ from (
    (130982579903240765417375702458498174726941234716845798435143)
  ))) * X ^ 127 +
  (Polynomial.C (show ℚ from (
    (-1945003450859942963112730481004571549088919809472086871202644)
  ))) * X ^ 126 +
  (Polynomial.C (show ℚ from (
    (10347453433811738528846818765759791952152581534393754863127527)
  ))) * X ^ 125 +
  (Polynomial.C (show ℚ from (
    (-44347179746999303988880195852121399298887756271258345800035365)
  ))) * X ^ 124 +
  (Polynomial.C (show ℚ from (
    (177107049544246693846855416600967564066668496291718172982442749)
  ))) * X ^ 123 +
  (Polynomial.C (show ℚ from (
    (-683948145007249207480741614259191587024219461518624069201391001)
  ))) * X ^ 122

private theorem remainder6Coefficient0Chunk3_normalized :
    remainder6Coefficient0Chunk3 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk3 := by
  unfold remainder6Coefficient0Chunk3 remainder6Coefficient0AlignedChunk3
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (2545619644684482349778253624086694121572974399965599769903315289)
  ))) * X ^ 121 +
  (Polynomial.C (show ℚ from (
    (-9024028921481459143513157150260613552446104273247394921552753269)
  ))) * X ^ 120 +
  (Polynomial.C (show ℚ from (
    (30230164930986946515501580891314415596147578805994315261142346551)
  ))) * X ^ 119 +
  (Polynomial.C (show ℚ from (
    (-95475758097507866726704886158097911054010900026621961356474800657)
  ))) * X ^ 118 +
  (Polynomial.C (show ℚ from (
    (284572048520790161747867067653159683583605123803668615266361278282)
  ))) * X ^ 117 +
  (Polynomial.C (show ℚ from (
    (-801736654814831697663473731435640246076164991577064501458818322033)
  ))) * X ^ 116 +
  (Polynomial.C (show ℚ from (
    (2134009579672437968266076458952013278406161261156561478352677566381)
  ))) * X ^ 115 +
  (Polynomial.C (show ℚ from (
    (-5340313645384165522578420825538151081303016019270165657699620124704)
  ))) * X ^ 114

private theorem remainder6Coefficient0Chunk4_normalized :
    remainder6Coefficient0Chunk4 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk4 := by
  unfold remainder6Coefficient0Chunk4 remainder6Coefficient0AlignedChunk4
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (12429560138297595750618316871422846498970026649655343782777785410577)
  ))) * X ^ 113 +
  (Polynomial.C (show ℚ from (
    (-26439403366827283330035126193717411602605103063506899647247522966940)
  ))) * X ^ 112 +
  (Polynomial.C (show ℚ from (
    (50135793353567503772334682367151217445778386018634869405431073906627)
  ))) * X ^ 111 +
  (Polynomial.C (show ℚ from (
    (-82116010063530562431376667223111858093587101561054837957666844741538)
  ))) * X ^ 110 +
  (Polynomial.C (show ℚ from (
    (113784340466023931159372435942159119116782709064237669047174751434782)
  ))) * X ^ 109 +
  (Polynomial.C (show ℚ from (
    (-151378794284688977786346268658924635999399999001512239530092701999652)
  ))) * X ^ 108 +
  (Polynomial.C (show ℚ from (
    (341926636285394821656590124076347399751475109665602989075348866655918)
  ))) * X ^ 107 +
  (Polynomial.C (show ℚ from (
    (-1377013538023343304701099922666635574441870442577548381106663394191357)
  ))) * X ^ 106

private theorem remainder6Coefficient0Chunk5_normalized :
    remainder6Coefficient0Chunk5 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk5 := by
  unfold remainder6Coefficient0Chunk5 remainder6Coefficient0AlignedChunk5
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (5416256180972067931054502273201765896117706856094036839943958091349572)
  ))) * X ^ 105 +
  (Polynomial.C (show ℚ from (
    (-17545452742618046214240102261457447190819626087925101084449011155586183)
  ))) * X ^ 104 +
  (Polynomial.C (show ℚ from (
    (46625939257369784804709730759269726034927452396474106929056969223221053)
  ))) * X ^ 103 +
  (Polynomial.C (show ℚ from (
    (-101216207450908943062709031002806485938451641746790532254608755438213005)
  ))) * X ^ 102 +
  (Polynomial.C (show ℚ from (
    (169787803235078759965615472022962309416701331772858821337714508908805445)
  ))) * X ^ 101 +
  (Polynomial.C (show ℚ from (
    (-164172175371069243083946798858660354620943731868351609635849480710691304)
  ))) * X ^ 100 +
  (Polynomial.C (show ℚ from (
    (-207198676461531209722605302324841454664279495368127177600761149689819128)
  ))) * X ^ 99 +
  (Polynomial.C (show ℚ from (
    (1678597925521666946770423760483295141388284533947356612541857443563953005)
  ))) * X ^ 98

private theorem remainder6Coefficient0Chunk6_normalized :
    remainder6Coefficient0Chunk6 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk6 := by
  unfold remainder6Coefficient0Chunk6 remainder6Coefficient0AlignedChunk6
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-5817193373733355484634679073060368933508223937618997455437257022202046937)
  ))) * X ^ 97 +
  (Polynomial.C (show ℚ from (
    (15575183430254181180266840763854538349123695565673787040826472501300325175)
  ))) * X ^ 96 +
  (Polynomial.C (show ℚ from (
    (-35958743799361079271860315284927414366121322246179992776404506055968021188)
  ))) * X ^ 95 +
  (Polynomial.C (show ℚ from (
    (74686854708838169491962329458287166626421791383227845204643700470818831188)
  ))) * X ^ 94 +
  (Polynomial.C (show ℚ from (
    (-142613186365378194328407917696411683613162442336129519185594713455470654074)
  ))) * X ^ 93 +
  (Polynomial.C (show ℚ from (
    (253556602755365319437975646475871630463966601757880207770742267625765463172)
  ))) * X ^ 92 +
  (Polynomial.C (show ℚ from (
    (-422964667520188572793516394408187459784374000947925428135008496849169275837)
  ))) * X ^ 91 +
  (Polynomial.C (show ℚ from (
    (664348043991404757737751759341033420931671374205909294849306566472229667478)
  ))) * X ^ 90

private theorem remainder6Coefficient0Chunk7_normalized :
    remainder6Coefficient0Chunk7 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk7 := by
  unfold remainder6Coefficient0Chunk7 remainder6Coefficient0AlignedChunk7
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-981346173880035163281013596250976630638245593758250177364979492027874338528)
  ))) * X ^ 89 +
  (Polynomial.C (show ℚ from (
    (1351109114410062472798262768549720862576457823721927412513916267262759157234)
  ))) * X ^ 88 +
  (Polynomial.C (show ℚ from (
    (-1690763163937098425353747003911103313706818481378191876129035947782545590108)
  ))) * X ^ 87 +
  (Polynomial.C (show ℚ from (
    (1792536932681484400828428421739275411415961378474689229100469000513173574081)
  ))) * X ^ 86 +
  (Polynomial.C (show ℚ from (
    (-1204917400611311440410714435017694629183255039111578284576236897573238542372)
  ))) * X ^ 85 +
  (Polynomial.C (show ℚ from (
    (-970686679352772456859953502598346683265853006798066131213438854300546633280)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (6399821759815699892919438927619779919695880663357279901817760188396095132030)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (-17967953562319479056600332328567053971138009773559803690769998534029800801389)
  ))) * X ^ 82

private theorem remainder6Coefficient0Chunk8_normalized :
    remainder6Coefficient0Chunk8 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk8 := by
  unfold remainder6Coefficient0Chunk8 remainder6Coefficient0AlignedChunk8
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (40337252253282015571674701187933301311140663621872424808515871928112022548988)
  ))) * X ^ 81 +
  (Polynomial.C (show ℚ from (
    (-80492923210909132715322554862368536014003821208897369311846451120968998318110)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    ((1 * 10 ^ 77 +
      48048283923981963418198740441041830233461475782619199143134761952340004213071))
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    -((2 * 10 ^ 77 +
      54966723212355820275169911415431778893476694309027362591224234808773830967451))
  ))) * X ^ 78 +
  (Polynomial.C (show ℚ from (
    ((4 * 10 ^ 77 +
      14322567044375904598794105651654387396470324235213132502861736855910763987521))
  ))) * X ^ 77 +
  (Polynomial.C (show ℚ from (
    -((6 * 10 ^ 77 +
      37845643585976983903940363733681304594372800680303068027352189921163156936848))
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    ((9 * 10 ^ 77 +
      32330309775517323513619269626911780219861871638903341293518326419523549703156))
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    -((12 * 10 ^ 77 +
      95506327055469324669707620172626555351388010166514906357964981876760610781051))
  ))) * X ^ 74

private theorem remainder6Coefficient0Chunk9_normalized :
    remainder6Coefficient0Chunk9 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk9 := by
  unfold remainder6Coefficient0Chunk9 remainder6Coefficient0AlignedChunk9
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((17 * 10 ^ 77 +
      12509308981423174148559045734317620336699095849059871863975476063725189414819))
  ))) * X ^ 73 +
  (Polynomial.C (show ℚ from (
    -((21 * 10 ^ 77 +
      54393515148750513758319881802771527392867530812501680289049294341475767428977))
  ))) * X ^ 72 +
  (Polynomial.C (show ℚ from (
    ((25 * 10 ^ 77 +
      79940045186505490211634798756486209374068017172104549890913891523742426461907))
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    -((29 * 10 ^ 77 +
      41220707790031495418525014537673251371166115301400130882612784234467806042798))
  ))) * X ^ 70 +
  (Polynomial.C (show ℚ from (
    ((31 * 10 ^ 77 +
      92147060485488360062351476665113970451975793922961423828860052581891608874441))
  ))) * X ^ 69 +
  (Polynomial.C (show ℚ from (
    -((32 * 10 ^ 77 +
      98003847329494159213609899689437300272166935870430565047032091661324257183532))
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    ((32 * 10 ^ 77 +
      43285237983489714435455849905839076149500773140475032255741232123509975260325))
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    -((30 * 10 ^ 77 +
      35411663882540188911277372933463928291555825671112130220410811610445562568935))
  ))) * X ^ 66

private theorem remainder6Coefficient0Chunk10_normalized :
    remainder6Coefficient0Chunk10 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk10 := by
  unfold remainder6Coefficient0Chunk10 remainder6Coefficient0AlignedChunk10
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((27 * 10 ^ 77 +
      03105768678533635523535841399460155729451026608005577779122340748460062607032))
  ))) * X ^ 65 +
  (Polynomial.C (show ℚ from (
    -((22 * 10 ^ 77 +
      89911919515664900278569550335607414159947655140561197842631959681397740739861))
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    ((18 * 10 ^ 77 +
      44868666275354091857720188415860894135868244701147366964087241202479965634477))
  ))) * X ^ 63 +
  (Polynomial.C (show ℚ from (
    -((14 * 10 ^ 77 +
      13081697674865031621327483674899470569511318626878716269964689502101852645569))
  ))) * X ^ 62 +
  (Polynomial.C (show ℚ from (
    ((10 * 10 ^ 77 +
      28660334170862935799631389057289175919127757056111761750980854515928970840693))
  ))) * X ^ 61 +
  (Polynomial.C (show ℚ from (
    -((7 * 10 ^ 77 +
      11394961114763764127838948606762174978698276344646419092041176614967080652490))
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    ((4 * 10 ^ 77 +
      67194691280881093107602188921976763386503147027234077372335317183313066735825))
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    -((2 * 10 ^ 77 +
      91226071424822681438978993491642365713211383776578996141797291061722346829263))
  ))) * X ^ 58

private theorem remainder6Coefficient0Chunk11_normalized :
    remainder6Coefficient0Chunk11 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk11 := by
  unfold remainder6Coefficient0Chunk11 remainder6Coefficient0AlignedChunk11
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((1 * 10 ^ 77 +
      72221305319726187974004423635930436081142334473715014951658805093295584912203))
  ))) * X ^ 57 +
  (Polynomial.C (show ℚ from (
    (-96566898707070892918891992480230488538373209191162881713133448413301144674808)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (51309255971084979629236552066002526165259121981968793745455403122078625136121)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (-25817269702525381050170855115721590876743208575406070748456327894812777284085)
  ))) * X ^ 54 +
  (Polynomial.C (show ℚ from (
    (12293404263488571815399245720967100396380869661207232141785311018865734956175)
  ))) * X ^ 53 +
  (Polynomial.C (show ℚ from (
    (-5535531165148300764096941087556367478395977897521314034829050134243956751268)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (2355193328929799673796823469373243375245270396160727785727254900653899353937)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (-946028875683670870702756021917817705294566717197833637548353323792240675677)
  ))) * X ^ 50

private theorem remainder6Coefficient0Chunk12_normalized :
    remainder6Coefficient0Chunk12 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk12 := by
  unfold remainder6Coefficient0Chunk12 remainder6Coefficient0AlignedChunk12
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (358424371257014941723911027203263248698377030210445814107859814426165650040)
  ))) * X ^ 49 +
  (Polynomial.C (show ℚ from (
    (-127962769290676924112499727689249735910659015306852475584421051166851636813)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (43004288180271341127781531973045370762557115370986631387207685626250791575)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-13589418326705664794241746609157525387101983280059762419346260406432588599)
  ))) * X ^ 46 +
  (Polynomial.C (show ℚ from (
    (4033091602968277891973759826873793594893764947604035786087347057513839932)
  ))) * X ^ 45 +
  (Polynomial.C (show ℚ from (
    (-1122734406218109102926369065616969290156733609125655144332612777271598742)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (292776335160758944506414138344481132322015103371606168441371704504445113)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-71416065383264343368784881041854645515379822727547348101512025031984824)
  ))) * X ^ 42

private theorem remainder6Coefficient0Chunk13_normalized :
    remainder6Coefficient0Chunk13 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk13 := by
  unfold remainder6Coefficient0Chunk13 remainder6Coefficient0AlignedChunk13
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (16270416454357962288785922171328893684810718871206659392540577260356521)
  ))) * X ^ 41 +
  (Polynomial.C (show ℚ from (
    (-3456564908724007688151225542452292332956752565415598341475749344857011)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (683582777734139380785549907815406681760868218662011826554399673825441)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-125617229248398279602004320980136554273041496827869743064360102562866)
  ))) * X ^ 38 +
  (Polynomial.C (show ℚ from (
    (21408305798650414593324049329374355372457082749990166919483809054562)
  ))) * X ^ 37 +
  (Polynomial.C (show ℚ from (
    (-3376782671986707868145283738173274303862985995308034390078626962660)
  ))) * X ^ 36 +
  (Polynomial.C (show ℚ from (
    (491893566350154056575952694430099216205781056310392829330682352156)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-66022168831533641230051983962421643804472664761487135445260519375)
  ))) * X ^ 34

private theorem remainder6Coefficient0Chunk14_normalized :
    remainder6Coefficient0Chunk14 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk14 := by
  unfold remainder6Coefficient0Chunk14 remainder6Coefficient0AlignedChunk14
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (8145226749138008596512827903128558287898774635124438721879583999)
  ))) * X ^ 33 +
  (Polynomial.C (show ℚ from (
    (-921282234232247460799432372736253975681094662966765982475846657)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (95273695130322564619808664047253327548653705043216432159319013)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-8982299732649508300989123416635049631840125791291956356512941)
  ))) * X ^ 30 +
  (Polynomial.C (show ℚ from (
    (769667573263612926854462469914690568294789857216115017140278)
  ))) * X ^ 29 +
  (Polynomial.C (show ℚ from (
    (-59745342497206739184820193505940909158550055465170941317012)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (4186816932242205040061182381405043904676182712005050670654)
  ))) * X ^ 27 +
  (Polynomial.C (show ℚ from (
    (-263898818659800466225069243678802303589547994627753879042)
  ))) * X ^ 26

private theorem remainder6Coefficient0Chunk15_normalized :
    remainder6Coefficient0Chunk15 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk15 := by
  unfold remainder6Coefficient0Chunk15 remainder6Coefficient0AlignedChunk15
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk16 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (14902139225924453924652503724757246239788645524329052263)
  ))) * X ^ 25 +
  (Polynomial.C (show ℚ from (
    (-750719505693191518043412629990182270715893739614035997)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (33584915373189065549564478828989276060604387390088798)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-1327719794323561787071268469332807908676569902174062)
  ))) * X ^ 22 +
  (Polynomial.C (show ℚ from (
    (46135476621855436814613621857964695522467044407161)
  ))) * X ^ 21 +
  (Polynomial.C (show ℚ from (
    (-1400815277015298383202224868350239387343808368079)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (36926109438316001477129459784970316197183426354)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-839011611373832404078412294574305045468065346)
  ))) * X ^ 18

private theorem remainder6Coefficient0Chunk16_normalized :
    remainder6Coefficient0Chunk16 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk16 := by
  unfold remainder6Coefficient0Chunk16 remainder6Coefficient0AlignedChunk16
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk17 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (16299500831440522606851699139527807858372826)
  ))) * X ^ 17 +
  (Polynomial.C (show ℚ from (
    (-268264554521812999415646039918351343842324)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (3701122614041489319460178511942838449989)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-42274215138012683952710880708186173698)
  ))) * X ^ 14 +
  (Polynomial.C (show ℚ from (
    (393789389195779512177444395511601179)
  ))) * X ^ 13 +
  (Polynomial.C (show ℚ from (
    (-2935784199256090713462122508704900)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (17084171716312780372985117783572)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-74811294898350680014206984857)
  ))) * X ^ 10

private theorem remainder6Coefficient0Chunk17_normalized :
    remainder6Coefficient0Chunk17 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk17 := by
  unfold remainder6Coefficient0Chunk17 remainder6Coefficient0AlignedChunk17
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk18 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (231350136257977388614570781)
  ))) * X ^ 9 +
  (Polynomial.C (show ℚ from (
    (-433883948126915203233533)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (186192598190668968923)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (1312767065522736660)
  ))) * X ^ 6 +
  (Polynomial.C (show ℚ from (
    (-3533679013856316)
  ))) * X ^ 5 +
  (Polynomial.C (show ℚ from (
    (4055313827456)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-2004000396)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (1452252)
  ))) * X ^ 2

private theorem remainder6Coefficient0Chunk18_normalized :
    remainder6Coefficient0Chunk18 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk18 := by
  unfold remainder6Coefficient0Chunk18 remainder6Coefficient0AlignedChunk18
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0AlignedChunk19 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (480)
  ))) * X ^ 1

private theorem remainder6Coefficient0Chunk19_normalized :
    remainder6Coefficient0Chunk19 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0AlignedChunk19 := by
  unfold remainder6Coefficient0Chunk19 remainder6Coefficient0AlignedChunk19
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient0Aligned : Coefficient :=
  remainder6Coefficient0AlignedChunk0 +
  remainder6Coefficient0AlignedChunk1 +
  remainder6Coefficient0AlignedChunk2 +
  remainder6Coefficient0AlignedChunk3 +
  remainder6Coefficient0AlignedChunk4 +
  remainder6Coefficient0AlignedChunk5 +
  remainder6Coefficient0AlignedChunk6 +
  remainder6Coefficient0AlignedChunk7 +
  remainder6Coefficient0AlignedChunk8 +
  remainder6Coefficient0AlignedChunk9 +
  remainder6Coefficient0AlignedChunk10 +
  remainder6Coefficient0AlignedChunk11 +
  remainder6Coefficient0AlignedChunk12 +
  remainder6Coefficient0AlignedChunk13 +
  remainder6Coefficient0AlignedChunk14 +
  remainder6Coefficient0AlignedChunk15 +
  remainder6Coefficient0AlignedChunk16 +
  remainder6Coefficient0AlignedChunk17 +
  remainder6Coefficient0AlignedChunk18 +
  remainder6Coefficient0AlignedChunk19

private def remainder6Coefficient0AlignedChunk0Band16 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-40522055413147560)
  ))) * X ^ 152 +
  (Polynomial.C (show ℚ from (
    (-43357899036499587396088)
  ))) * X ^ 151 +
  (Polynomial.C (show ℚ from (
    (-2933260314236696862010807052)
  ))) * X ^ 150 +
  (Polynomial.C (show ℚ from (
    (-25060547349737891843516424822013)
  ))) * X ^ 149 +
  (Polynomial.C (show ℚ from (
    (-37303409421719864169581552912054227)
  ))) * X ^ 148 +
  (Polynomial.C (show ℚ from (
    (-6664154253035422565434310513723014473)
  ))) * X ^ 147 +
  (Polynomial.C (show ℚ from (
    (8134043698377643468887670751448365521145)
  ))) * X ^ 146

private def remainder6Coefficient0AlignedChunk0Band17 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1011392369)
  ))) * X ^ 153

private theorem remainder6Coefficient0AlignedChunk0_pieces :
    remainder6Coefficient0AlignedChunk0 =
      remainder6Coefficient0AlignedChunk0Band16 +
      remainder6Coefficient0AlignedChunk0Band17
    := by
  unfold remainder6Coefficient0AlignedChunk0 remainder6Coefficient0AlignedChunk0Band16
  unfold remainder6Coefficient0AlignedChunk0Band17
  ring

private def remainder6Coefficient0AlignedChunk1Band15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (51180106368914433882879910916647390729071029891)
  ))) * X ^ 143 +
  (Polynomial.C (show ℚ from (
    (1124513794129348728267163654844646077985631241883)
  ))) * X ^ 142 +
  (Polynomial.C (show ℚ from (
    (-5936880140781240810156398491591308405122099790362)
  ))) * X ^ 141 +
  (Polynomial.C (show ℚ from (
    (-225637739201328317741010866003929708465314470308722)
  ))) * X ^ 140 +
  (Polynomial.C (show ℚ from (
    (1640763020833435260328793390724491197677689490448216)
  ))) * X ^ 139 +
  (Polynomial.C (show ℚ from (
    (13830510745960661250169911443628707195581541111929709)
  ))) * X ^ 138

private def remainder6Coefficient0AlignedChunk1Band16 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (4097015695492371739826329824989209203367262)
  ))) * X ^ 145 +
  (Polynomial.C (show ℚ from (
    (720497376836365789771706356156031624629128769)
  ))) * X ^ 144

private theorem remainder6Coefficient0AlignedChunk1_pieces :
    remainder6Coefficient0AlignedChunk1 =
      remainder6Coefficient0AlignedChunk1Band15 +
      remainder6Coefficient0AlignedChunk1Band16
    := by
  unfold remainder6Coefficient0AlignedChunk1 remainder6Coefficient0AlignedChunk1Band15
  unfold remainder6Coefficient0AlignedChunk1Band16
  ring

private def remainder6Coefficient0AlignedChunk2Band14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-57552519342706272011320757210885952062399753522898777293)
  ))) * X ^ 134 +
  (Polynomial.C (show ℚ from (
    (283068179503719821855505984060517063926743570210527486177)
  ))) * X ^ 133 +
  (Polynomial.C (show ℚ from (
    (-577831655991145443155503224347531013768994337594877967975)
  ))) * X ^ 132 +
  (Polynomial.C (show ℚ from (
    (-1340676479236975758305973107443056024481803453846874024787)
  ))) * X ^ 131 +
  (Polynomial.C (show ℚ from (
    (14737496869073084554441130110488277083264282977945034116736)
  ))) * X ^ 130

private def remainder6Coefficient0AlignedChunk2Band15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-222308451621338922645283676695166015302402257964224032)
  ))) * X ^ 137 +
  (Polynomial.C (show ℚ from (
    (816990963221813020303938577140743131751025606122261243)
  ))) * X ^ 136 +
  (Polynomial.C (show ℚ from (
    (4026282148141467705170099569081456097602533694427138661)
  ))) * X ^ 135

private theorem remainder6Coefficient0AlignedChunk2_pieces :
    remainder6Coefficient0AlignedChunk2 =
      remainder6Coefficient0AlignedChunk2Band14 +
      remainder6Coefficient0AlignedChunk2Band15
    := by
  unfold remainder6Coefficient0AlignedChunk2 remainder6Coefficient0AlignedChunk2Band14
  unfold remainder6Coefficient0AlignedChunk2Band15
  ring

private def remainder6Coefficient0AlignedChunk3Band13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (10347453433811738528846818765759791952152581534393754863127527)
  ))) * X ^ 125 +
  (Polynomial.C (show ℚ from (
    (-44347179746999303988880195852121399298887756271258345800035365)
  ))) * X ^ 124 +
  (Polynomial.C (show ℚ from (
    (177107049544246693846855416600967564066668496291718172982442749)
  ))) * X ^ 123 +
  (Polynomial.C (show ℚ from (
    (-683948145007249207480741614259191587024219461518624069201391001)
  ))) * X ^ 122

private def remainder6Coefficient0AlignedChunk3Band14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-55812988878064651281148901532524626925833772159512955627475)
  ))) * X ^ 129 +
  (Polynomial.C (show ℚ from (
    (101287261705211680714786891227418204256889070569152114806074)
  ))) * X ^ 128 +
  (Polynomial.C (show ℚ from (
    (130982579903240765417375702458498174726941234716845798435143)
  ))) * X ^ 127 +
  (Polynomial.C (show ℚ from (
    (-1945003450859942963112730481004571549088919809472086871202644)
  ))) * X ^ 126

private theorem remainder6Coefficient0AlignedChunk3_pieces :
    remainder6Coefficient0AlignedChunk3 =
      remainder6Coefficient0AlignedChunk3Band13 +
      remainder6Coefficient0AlignedChunk3Band14
    := by
  unfold remainder6Coefficient0AlignedChunk3 remainder6Coefficient0AlignedChunk3Band13
  unfold remainder6Coefficient0AlignedChunk3Band14
  ring

private def remainder6Coefficient0AlignedChunk4Band12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-801736654814831697663473731435640246076164991577064501458818322033)
  ))) * X ^ 116 +
  (Polynomial.C (show ℚ from (
    (2134009579672437968266076458952013278406161261156561478352677566381)
  ))) * X ^ 115 +
  (Polynomial.C (show ℚ from (
    (-5340313645384165522578420825538151081303016019270165657699620124704)
  ))) * X ^ 114

private def remainder6Coefficient0AlignedChunk4Band13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (2545619644684482349778253624086694121572974399965599769903315289)
  ))) * X ^ 121 +
  (Polynomial.C (show ℚ from (
    (-9024028921481459143513157150260613552446104273247394921552753269)
  ))) * X ^ 120 +
  (Polynomial.C (show ℚ from (
    (30230164930986946515501580891314415596147578805994315261142346551)
  ))) * X ^ 119 +
  (Polynomial.C (show ℚ from (
    (-95475758097507866726704886158097911054010900026621961356474800657)
  ))) * X ^ 118 +
  (Polynomial.C (show ℚ from (
    (284572048520790161747867067653159683583605123803668615266361278282)
  ))) * X ^ 117

private theorem remainder6Coefficient0AlignedChunk4_pieces :
    remainder6Coefficient0AlignedChunk4 =
      remainder6Coefficient0AlignedChunk4Band12 +
      remainder6Coefficient0AlignedChunk4Band13
    := by
  unfold remainder6Coefficient0AlignedChunk4 remainder6Coefficient0AlignedChunk4Band12
  unfold remainder6Coefficient0AlignedChunk4Band13
  ring

private def remainder6Coefficient0AlignedChunk5Band11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (341926636285394821656590124076347399751475109665602989075348866655918)
  ))) * X ^ 107 +
  (Polynomial.C (show ℚ from (
    (-1377013538023343304701099922666635574441870442577548381106663394191357)
  ))) * X ^ 106

private def remainder6Coefficient0AlignedChunk5Band12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (12429560138297595750618316871422846498970026649655343782777785410577)
  ))) * X ^ 113 +
  (Polynomial.C (show ℚ from (
    (-26439403366827283330035126193717411602605103063506899647247522966940)
  ))) * X ^ 112 +
  (Polynomial.C (show ℚ from (
    (50135793353567503772334682367151217445778386018634869405431073906627)
  ))) * X ^ 111 +
  (Polynomial.C (show ℚ from (
    (-82116010063530562431376667223111858093587101561054837957666844741538)
  ))) * X ^ 110 +
  (Polynomial.C (show ℚ from (
    (113784340466023931159372435942159119116782709064237669047174751434782)
  ))) * X ^ 109 +
  (Polynomial.C (show ℚ from (
    (-151378794284688977786346268658924635999399999001512239530092701999652)
  ))) * X ^ 108

private theorem remainder6Coefficient0AlignedChunk5_pieces :
    remainder6Coefficient0AlignedChunk5 =
      remainder6Coefficient0AlignedChunk5Band11 +
      remainder6Coefficient0AlignedChunk5Band12
    := by
  unfold remainder6Coefficient0AlignedChunk5 remainder6Coefficient0AlignedChunk5Band11
  unfold remainder6Coefficient0AlignedChunk5Band12
  ring

private def remainder6Coefficient0AlignedChunk6Band10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (1678597925521666946770423760483295141388284533947356612541857443563953005)
  ))) * X ^ 98

private def remainder6Coefficient0AlignedChunk6Band11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (5416256180972067931054502273201765896117706856094036839943958091349572)
  ))) * X ^ 105 +
  (Polynomial.C (show ℚ from (
    (-17545452742618046214240102261457447190819626087925101084449011155586183)
  ))) * X ^ 104 +
  (Polynomial.C (show ℚ from (
    (46625939257369784804709730759269726034927452396474106929056969223221053)
  ))) * X ^ 103 +
  (Polynomial.C (show ℚ from (
    (-101216207450908943062709031002806485938451641746790532254608755438213005)
  ))) * X ^ 102 +
  (Polynomial.C (show ℚ from (
    (169787803235078759965615472022962309416701331772858821337714508908805445)
  ))) * X ^ 101 +
  (Polynomial.C (show ℚ from (
    (-164172175371069243083946798858660354620943731868351609635849480710691304)
  ))) * X ^ 100 +
  (Polynomial.C (show ℚ from (
    (-207198676461531209722605302324841454664279495368127177600761149689819128)
  ))) * X ^ 99

private theorem remainder6Coefficient0AlignedChunk6_pieces :
    remainder6Coefficient0AlignedChunk6 =
      remainder6Coefficient0AlignedChunk6Band10 +
      remainder6Coefficient0AlignedChunk6Band11
    := by
  unfold remainder6Coefficient0AlignedChunk6 remainder6Coefficient0AlignedChunk6Band10
  unfold remainder6Coefficient0AlignedChunk6Band11
  ring

private def remainder6Coefficient0AlignedChunk7Band10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-5817193373733355484634679073060368933508223937618997455437257022202046937)
  ))) * X ^ 97 +
  (Polynomial.C (show ℚ from (
    (15575183430254181180266840763854538349123695565673787040826472501300325175)
  ))) * X ^ 96 +
  (Polynomial.C (show ℚ from (
    (-35958743799361079271860315284927414366121322246179992776404506055968021188)
  ))) * X ^ 95 +
  (Polynomial.C (show ℚ from (
    (74686854708838169491962329458287166626421791383227845204643700470818831188)
  ))) * X ^ 94 +
  (Polynomial.C (show ℚ from (
    (-142613186365378194328407917696411683613162442336129519185594713455470654074)
  ))) * X ^ 93 +
  (Polynomial.C (show ℚ from (
    (253556602755365319437975646475871630463966601757880207770742267625765463172)
  ))) * X ^ 92 +
  (Polynomial.C (show ℚ from (
    (-422964667520188572793516394408187459784374000947925428135008496849169275837)
  ))) * X ^ 91 +
  (Polynomial.C (show ℚ from (
    (664348043991404757737751759341033420931671374205909294849306566472229667478)
  ))) * X ^ 90

private theorem remainder6Coefficient0AlignedChunk7_pieces :
    remainder6Coefficient0AlignedChunk7 =
      remainder6Coefficient0AlignedChunk7Band10
    := by
  unfold remainder6Coefficient0AlignedChunk7 remainder6Coefficient0AlignedChunk7Band10
  ring

private def remainder6Coefficient0AlignedChunk8Band9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-981346173880035163281013596250976630638245593758250177364979492027874338528)
  ))) * X ^ 89 +
  (Polynomial.C (show ℚ from (
    (1351109114410062472798262768549720862576457823721927412513916267262759157234)
  ))) * X ^ 88 +
  (Polynomial.C (show ℚ from (
    (-1690763163937098425353747003911103313706818481378191876129035947782545590108)
  ))) * X ^ 87 +
  (Polynomial.C (show ℚ from (
    (1792536932681484400828428421739275411415961378474689229100469000513173574081)
  ))) * X ^ 86 +
  (Polynomial.C (show ℚ from (
    (-1204917400611311440410714435017694629183255039111578284576236897573238542372)
  ))) * X ^ 85 +
  (Polynomial.C (show ℚ from (
    (-970686679352772456859953502598346683265853006798066131213438854300546633280)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (6399821759815699892919438927619779919695880663357279901817760188396095132030)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (-17967953562319479056600332328567053971138009773559803690769998534029800801389)
  ))) * X ^ 82

private theorem remainder6Coefficient0AlignedChunk8_pieces :
    remainder6Coefficient0AlignedChunk8 =
      remainder6Coefficient0AlignedChunk8Band9
    := by
  unfold remainder6Coefficient0AlignedChunk8 remainder6Coefficient0AlignedChunk8Band9
  ring

private def remainder6Coefficient0AlignedChunk9Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-80492923210909132715322554862368536014003821208897369311846451120968998318110)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    ((1 * 10 ^ 77 +
      48048283923981963418198740441041830233461475782619199143134761952340004213071))
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    -((2 * 10 ^ 77 +
      54966723212355820275169911415431778893476694309027362591224234808773830967451))
  ))) * X ^ 78 +
  (Polynomial.C (show ℚ from (
    ((4 * 10 ^ 77 +
      14322567044375904598794105651654387396470324235213132502861736855910763987521))
  ))) * X ^ 77 +
  (Polynomial.C (show ℚ from (
    -((6 * 10 ^ 77 +
      37845643585976983903940363733681304594372800680303068027352189921163156936848))
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    ((9 * 10 ^ 77 +
      32330309775517323513619269626911780219861871638903341293518326419523549703156))
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    -((12 * 10 ^ 77 +
      95506327055469324669707620172626555351388010166514906357964981876760610781051))
  ))) * X ^ 74

private def remainder6Coefficient0AlignedChunk9Band9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (40337252253282015571674701187933301311140663621872424808515871928112022548988)
  ))) * X ^ 81

private theorem remainder6Coefficient0AlignedChunk9_pieces :
    remainder6Coefficient0AlignedChunk9 =
      remainder6Coefficient0AlignedChunk9Band8 +
      remainder6Coefficient0AlignedChunk9Band9
    := by
  unfold remainder6Coefficient0AlignedChunk9 remainder6Coefficient0AlignedChunk9Band8
  unfold remainder6Coefficient0AlignedChunk9Band9
  ring

private def remainder6Coefficient0AlignedChunk10Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((25 * 10 ^ 77 +
      79940045186505490211634798756486209374068017172104549890913891523742426461907))
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    -((29 * 10 ^ 77 +
      41220707790031495418525014537673251371166115301400130882612784234467806042798))
  ))) * X ^ 70 +
  (Polynomial.C (show ℚ from (
    ((31 * 10 ^ 77 +
      92147060485488360062351476665113970451975793922961423828860052581891608874441))
  ))) * X ^ 69 +
  (Polynomial.C (show ℚ from (
    -((32 * 10 ^ 77 +
      98003847329494159213609899689437300272166935870430565047032091661324257183532))
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    ((32 * 10 ^ 77 +
      43285237983489714435455849905839076149500773140475032255741232123509975260325))
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    -((30 * 10 ^ 77 +
      35411663882540188911277372933463928291555825671112130220410811610445562568935))
  ))) * X ^ 66

private def remainder6Coefficient0AlignedChunk10Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((17 * 10 ^ 77 +
      12509308981423174148559045734317620336699095849059871863975476063725189414819))
  ))) * X ^ 73 +
  (Polynomial.C (show ℚ from (
    -((21 * 10 ^ 77 +
      54393515148750513758319881802771527392867530812501680289049294341475767428977))
  ))) * X ^ 72

private theorem remainder6Coefficient0AlignedChunk10_pieces :
    remainder6Coefficient0AlignedChunk10 =
      remainder6Coefficient0AlignedChunk10Band7 +
      remainder6Coefficient0AlignedChunk10Band8
    := by
  unfold remainder6Coefficient0AlignedChunk10 remainder6Coefficient0AlignedChunk10Band7
  unfold remainder6Coefficient0AlignedChunk10Band8
  ring

private def remainder6Coefficient0AlignedChunk11Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    -((14 * 10 ^ 77 +
      13081697674865031621327483674899470569511318626878716269964689502101852645569))
  ))) * X ^ 62 +
  (Polynomial.C (show ℚ from (
    ((10 * 10 ^ 77 +
      28660334170862935799631389057289175919127757056111761750980854515928970840693))
  ))) * X ^ 61 +
  (Polynomial.C (show ℚ from (
    -((7 * 10 ^ 77 +
      11394961114763764127838948606762174978698276344646419092041176614967080652490))
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    ((4 * 10 ^ 77 +
      67194691280881093107602188921976763386503147027234077372335317183313066735825))
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    -((2 * 10 ^ 77 +
      91226071424822681438978993491642365713211383776578996141797291061722346829263))
  ))) * X ^ 58

private def remainder6Coefficient0AlignedChunk11Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((27 * 10 ^ 77 +
      03105768678533635523535841399460155729451026608005577779122340748460062607032))
  ))) * X ^ 65 +
  (Polynomial.C (show ℚ from (
    -((22 * 10 ^ 77 +
      89911919515664900278569550335607414159947655140561197842631959681397740739861))
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    ((18 * 10 ^ 77 +
      44868666275354091857720188415860894135868244701147366964087241202479965634477))
  ))) * X ^ 63

private theorem remainder6Coefficient0AlignedChunk11_pieces :
    remainder6Coefficient0AlignedChunk11 =
      remainder6Coefficient0AlignedChunk11Band6 +
      remainder6Coefficient0AlignedChunk11Band7
    := by
  unfold remainder6Coefficient0AlignedChunk11 remainder6Coefficient0AlignedChunk11Band6
  unfold remainder6Coefficient0AlignedChunk11Band7
  ring

private def remainder6Coefficient0AlignedChunk12Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (12293404263488571815399245720967100396380869661207232141785311018865734956175)
  ))) * X ^ 53 +
  (Polynomial.C (show ℚ from (
    (-5535531165148300764096941087556367478395977897521314034829050134243956751268)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (2355193328929799673796823469373243375245270396160727785727254900653899353937)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (-946028875683670870702756021917817705294566717197833637548353323792240675677)
  ))) * X ^ 50

private def remainder6Coefficient0AlignedChunk12Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((1 * 10 ^ 77 +
      72221305319726187974004423635930436081142334473715014951658805093295584912203))
  ))) * X ^ 57 +
  (Polynomial.C (show ℚ from (
    (-96566898707070892918891992480230488538373209191162881713133448413301144674808)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (51309255971084979629236552066002526165259121981968793745455403122078625136121)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (-25817269702525381050170855115721590876743208575406070748456327894812777284085)
  ))) * X ^ 54

private theorem remainder6Coefficient0AlignedChunk12_pieces :
    remainder6Coefficient0AlignedChunk12 =
      remainder6Coefficient0AlignedChunk12Band5 +
      remainder6Coefficient0AlignedChunk12Band6
    := by
  unfold remainder6Coefficient0AlignedChunk12 remainder6Coefficient0AlignedChunk12Band5
  unfold remainder6Coefficient0AlignedChunk12Band6
  ring

private def remainder6Coefficient0AlignedChunk13Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1122734406218109102926369065616969290156733609125655144332612777271598742)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (292776335160758944506414138344481132322015103371606168441371704504445113)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-71416065383264343368784881041854645515379822727547348101512025031984824)
  ))) * X ^ 42

private def remainder6Coefficient0AlignedChunk13Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (358424371257014941723911027203263248698377030210445814107859814426165650040)
  ))) * X ^ 49 +
  (Polynomial.C (show ℚ from (
    (-127962769290676924112499727689249735910659015306852475584421051166851636813)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (43004288180271341127781531973045370762557115370986631387207685626250791575)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-13589418326705664794241746609157525387101983280059762419346260406432588599)
  ))) * X ^ 46 +
  (Polynomial.C (show ℚ from (
    (4033091602968277891973759826873793594893764947604035786087347057513839932)
  ))) * X ^ 45

private theorem remainder6Coefficient0AlignedChunk13_pieces :
    remainder6Coefficient0AlignedChunk13 =
      remainder6Coefficient0AlignedChunk13Band4 +
      remainder6Coefficient0AlignedChunk13Band5
    := by
  unfold remainder6Coefficient0AlignedChunk13 remainder6Coefficient0AlignedChunk13Band4
  unfold remainder6Coefficient0AlignedChunk13Band5
  ring

private def remainder6Coefficient0AlignedChunk14Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (491893566350154056575952694430099216205781056310392829330682352156)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-66022168831533641230051983962421643804472664761487135445260519375)
  ))) * X ^ 34

private def remainder6Coefficient0AlignedChunk14Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (16270416454357962288785922171328893684810718871206659392540577260356521)
  ))) * X ^ 41 +
  (Polynomial.C (show ℚ from (
    (-3456564908724007688151225542452292332956752565415598341475749344857011)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (683582777734139380785549907815406681760868218662011826554399673825441)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-125617229248398279602004320980136554273041496827869743064360102562866)
  ))) * X ^ 38 +
  (Polynomial.C (show ℚ from (
    (21408305798650414593324049329374355372457082749990166919483809054562)
  ))) * X ^ 37 +
  (Polynomial.C (show ℚ from (
    (-3376782671986707868145283738173274303862985995308034390078626962660)
  ))) * X ^ 36

private theorem remainder6Coefficient0AlignedChunk14_pieces :
    remainder6Coefficient0AlignedChunk14 =
      remainder6Coefficient0AlignedChunk14Band3 +
      remainder6Coefficient0AlignedChunk14Band4
    := by
  unfold remainder6Coefficient0AlignedChunk14 remainder6Coefficient0AlignedChunk14Band3
  unfold remainder6Coefficient0AlignedChunk14Band4
  ring

private def remainder6Coefficient0AlignedChunk15Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-263898818659800466225069243678802303589547994627753879042)
  ))) * X ^ 26

private def remainder6Coefficient0AlignedChunk15Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (8145226749138008596512827903128558287898774635124438721879583999)
  ))) * X ^ 33 +
  (Polynomial.C (show ℚ from (
    (-921282234232247460799432372736253975681094662966765982475846657)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (95273695130322564619808664047253327548653705043216432159319013)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-8982299732649508300989123416635049631840125791291956356512941)
  ))) * X ^ 30 +
  (Polynomial.C (show ℚ from (
    (769667573263612926854462469914690568294789857216115017140278)
  ))) * X ^ 29 +
  (Polynomial.C (show ℚ from (
    (-59745342497206739184820193505940909158550055465170941317012)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (4186816932242205040061182381405043904676182712005050670654)
  ))) * X ^ 27

private theorem remainder6Coefficient0AlignedChunk15_pieces :
    remainder6Coefficient0AlignedChunk15 =
      remainder6Coefficient0AlignedChunk15Band2 +
      remainder6Coefficient0AlignedChunk15Band3
    := by
  unfold remainder6Coefficient0AlignedChunk15 remainder6Coefficient0AlignedChunk15Band2
  unfold remainder6Coefficient0AlignedChunk15Band3
  ring

private def remainder6Coefficient0AlignedChunk16Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (14902139225924453924652503724757246239788645524329052263)
  ))) * X ^ 25 +
  (Polynomial.C (show ℚ from (
    (-750719505693191518043412629990182270715893739614035997)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (33584915373189065549564478828989276060604387390088798)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-1327719794323561787071268469332807908676569902174062)
  ))) * X ^ 22 +
  (Polynomial.C (show ℚ from (
    (46135476621855436814613621857964695522467044407161)
  ))) * X ^ 21 +
  (Polynomial.C (show ℚ from (
    (-1400815277015298383202224868350239387343808368079)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (36926109438316001477129459784970316197183426354)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-839011611373832404078412294574305045468065346)
  ))) * X ^ 18

private theorem remainder6Coefficient0AlignedChunk16_pieces :
    remainder6Coefficient0AlignedChunk16 =
      remainder6Coefficient0AlignedChunk16Band2
    := by
  unfold remainder6Coefficient0AlignedChunk16 remainder6Coefficient0AlignedChunk16Band2
  ring

private def remainder6Coefficient0AlignedChunk17Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (16299500831440522606851699139527807858372826)
  ))) * X ^ 17 +
  (Polynomial.C (show ℚ from (
    (-268264554521812999415646039918351343842324)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (3701122614041489319460178511942838449989)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-42274215138012683952710880708186173698)
  ))) * X ^ 14 +
  (Polynomial.C (show ℚ from (
    (393789389195779512177444395511601179)
  ))) * X ^ 13 +
  (Polynomial.C (show ℚ from (
    (-2935784199256090713462122508704900)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (17084171716312780372985117783572)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-74811294898350680014206984857)
  ))) * X ^ 10

private theorem remainder6Coefficient0AlignedChunk17_pieces :
    remainder6Coefficient0AlignedChunk17 =
      remainder6Coefficient0AlignedChunk17Band1
    := by
  unfold remainder6Coefficient0AlignedChunk17 remainder6Coefficient0AlignedChunk17Band1
  ring

private def remainder6Coefficient0AlignedChunk18Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-433883948126915203233533)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (186192598190668968923)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (1312767065522736660)
  ))) * X ^ 6 +
  (Polynomial.C (show ℚ from (
    (-3533679013856316)
  ))) * X ^ 5 +
  (Polynomial.C (show ℚ from (
    (4055313827456)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-2004000396)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (1452252)
  ))) * X ^ 2

private def remainder6Coefficient0AlignedChunk18Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (231350136257977388614570781)
  ))) * X ^ 9

private theorem remainder6Coefficient0AlignedChunk18_pieces :
    remainder6Coefficient0AlignedChunk18 =
      remainder6Coefficient0AlignedChunk18Band0 +
      remainder6Coefficient0AlignedChunk18Band1
    := by
  unfold remainder6Coefficient0AlignedChunk18 remainder6Coefficient0AlignedChunk18Band0
  unfold remainder6Coefficient0AlignedChunk18Band1
  ring

private def remainder6Coefficient0AlignedChunk19Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (480)
  ))) * X ^ 1

private theorem remainder6Coefficient0AlignedChunk19_pieces :
    remainder6Coefficient0AlignedChunk19 =
      remainder6Coefficient0AlignedChunk19Band0
    := by
  unfold remainder6Coefficient0AlignedChunk19 remainder6Coefficient0AlignedChunk19Band0
  ring

private theorem remainder6Coefficient0AlignedBand0_eq :
    remainder6Coefficient0NormalizedBlock0 =
      remainder6Coefficient0AlignedChunk18Band0 +
      remainder6Coefficient0AlignedChunk19Band0
    := by
  unfold remainder6Coefficient0NormalizedBlock0 remainder6Coefficient0AlignedChunk18Band0
  unfold remainder6Coefficient0AlignedChunk19Band0
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand1_eq :
    remainder6Coefficient0NormalizedBlock1 =
      remainder6Coefficient0AlignedChunk17Band1 +
      remainder6Coefficient0AlignedChunk18Band1
    := by
  unfold remainder6Coefficient0NormalizedBlock1 remainder6Coefficient0AlignedChunk17Band1
  unfold remainder6Coefficient0AlignedChunk18Band1
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand2_eq :
    remainder6Coefficient0NormalizedBlock2 =
      remainder6Coefficient0AlignedChunk15Band2 +
      remainder6Coefficient0AlignedChunk16Band2
    := by
  unfold remainder6Coefficient0NormalizedBlock2 remainder6Coefficient0AlignedChunk15Band2
  unfold remainder6Coefficient0AlignedChunk16Band2
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand3_eq :
    remainder6Coefficient0NormalizedBlock3 =
      remainder6Coefficient0AlignedChunk14Band3 +
      remainder6Coefficient0AlignedChunk15Band3
    := by
  unfold remainder6Coefficient0NormalizedBlock3 remainder6Coefficient0AlignedChunk14Band3
  unfold remainder6Coefficient0AlignedChunk15Band3
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand4_eq :
    remainder6Coefficient0NormalizedBlock4 =
      remainder6Coefficient0AlignedChunk13Band4 +
      remainder6Coefficient0AlignedChunk14Band4
    := by
  unfold remainder6Coefficient0NormalizedBlock4 remainder6Coefficient0AlignedChunk13Band4
  unfold remainder6Coefficient0AlignedChunk14Band4
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand5_eq :
    remainder6Coefficient0NormalizedBlock5 =
      remainder6Coefficient0AlignedChunk12Band5 +
      remainder6Coefficient0AlignedChunk13Band5
    := by
  unfold remainder6Coefficient0NormalizedBlock5 remainder6Coefficient0AlignedChunk12Band5
  unfold remainder6Coefficient0AlignedChunk13Band5
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand6_eq :
    remainder6Coefficient0NormalizedBlock6 =
      remainder6Coefficient0AlignedChunk11Band6 +
      remainder6Coefficient0AlignedChunk12Band6
    := by
  unfold remainder6Coefficient0NormalizedBlock6 remainder6Coefficient0AlignedChunk11Band6
  unfold remainder6Coefficient0AlignedChunk12Band6
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand7_eq :
    remainder6Coefficient0NormalizedBlock7 =
      remainder6Coefficient0AlignedChunk10Band7 +
      remainder6Coefficient0AlignedChunk11Band7
    := by
  unfold remainder6Coefficient0NormalizedBlock7 remainder6Coefficient0AlignedChunk10Band7
  unfold remainder6Coefficient0AlignedChunk11Band7
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand8_eq :
    remainder6Coefficient0NormalizedBlock8 =
      remainder6Coefficient0AlignedChunk9Band8 +
      remainder6Coefficient0AlignedChunk10Band8
    := by
  unfold remainder6Coefficient0NormalizedBlock8 remainder6Coefficient0AlignedChunk9Band8
  unfold remainder6Coefficient0AlignedChunk10Band8
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand9_eq :
    remainder6Coefficient0NormalizedBlock9 =
      remainder6Coefficient0AlignedChunk8Band9 +
      remainder6Coefficient0AlignedChunk9Band9
    := by
  unfold remainder6Coefficient0NormalizedBlock9 remainder6Coefficient0AlignedChunk8Band9
  unfold remainder6Coefficient0AlignedChunk9Band9
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand10_eq :
    remainder6Coefficient0NormalizedBlock10 =
      remainder6Coefficient0AlignedChunk6Band10 +
      remainder6Coefficient0AlignedChunk7Band10
    := by
  unfold remainder6Coefficient0NormalizedBlock10 remainder6Coefficient0AlignedChunk6Band10
  unfold remainder6Coefficient0AlignedChunk7Band10
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand11_eq :
    remainder6Coefficient0NormalizedBlock11 =
      remainder6Coefficient0AlignedChunk5Band11 +
      remainder6Coefficient0AlignedChunk6Band11
    := by
  unfold remainder6Coefficient0NormalizedBlock11 remainder6Coefficient0AlignedChunk5Band11
  unfold remainder6Coefficient0AlignedChunk6Band11
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand12_eq :
    remainder6Coefficient0NormalizedBlock12 =
      remainder6Coefficient0AlignedChunk4Band12 +
      remainder6Coefficient0AlignedChunk5Band12
    := by
  unfold remainder6Coefficient0NormalizedBlock12 remainder6Coefficient0AlignedChunk4Band12
  unfold remainder6Coefficient0AlignedChunk5Band12
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand13_eq :
    remainder6Coefficient0NormalizedBlock13 =
      remainder6Coefficient0AlignedChunk3Band13 +
      remainder6Coefficient0AlignedChunk4Band13
    := by
  unfold remainder6Coefficient0NormalizedBlock13 remainder6Coefficient0AlignedChunk3Band13
  unfold remainder6Coefficient0AlignedChunk4Band13
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand14_eq :
    remainder6Coefficient0NormalizedBlock14 =
      remainder6Coefficient0AlignedChunk2Band14 +
      remainder6Coefficient0AlignedChunk3Band14
    := by
  unfold remainder6Coefficient0NormalizedBlock14 remainder6Coefficient0AlignedChunk2Band14
  unfold remainder6Coefficient0AlignedChunk3Band14
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand15_eq :
    remainder6Coefficient0NormalizedBlock15 =
      remainder6Coefficient0AlignedChunk1Band15 +
      remainder6Coefficient0AlignedChunk2Band15
    := by
  unfold remainder6Coefficient0NormalizedBlock15 remainder6Coefficient0AlignedChunk1Band15
  unfold remainder6Coefficient0AlignedChunk2Band15
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand16_eq :
    remainder6Coefficient0NormalizedBlock16 =
      remainder6Coefficient0AlignedChunk0Band16 +
      remainder6Coefficient0AlignedChunk1Band16
    := by
  unfold remainder6Coefficient0NormalizedBlock16 remainder6Coefficient0AlignedChunk0Band16
  unfold remainder6Coefficient0AlignedChunk1Band16
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0AlignedBand17_eq :
    remainder6Coefficient0NormalizedBlock17 =
      remainder6Coefficient0AlignedChunk0Band17
    := by
  unfold remainder6Coefficient0NormalizedBlock17 remainder6Coefficient0AlignedChunk0Band17
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient0Aligned_eq :
    remainder6Coefficient0Aligned = remainder6Coefficient0Normalized := by
  unfold remainder6Coefficient0Aligned remainder6Coefficient0Normalized
  rw [remainder6Coefficient0AlignedChunk0_pieces]
  rw [remainder6Coefficient0AlignedChunk1_pieces]
  rw [remainder6Coefficient0AlignedChunk2_pieces]
  rw [remainder6Coefficient0AlignedChunk3_pieces]
  rw [remainder6Coefficient0AlignedChunk4_pieces]
  rw [remainder6Coefficient0AlignedChunk5_pieces]
  rw [remainder6Coefficient0AlignedChunk6_pieces]
  rw [remainder6Coefficient0AlignedChunk7_pieces]
  rw [remainder6Coefficient0AlignedChunk8_pieces]
  rw [remainder6Coefficient0AlignedChunk9_pieces]
  rw [remainder6Coefficient0AlignedChunk10_pieces]
  rw [remainder6Coefficient0AlignedChunk11_pieces]
  rw [remainder6Coefficient0AlignedChunk12_pieces]
  rw [remainder6Coefficient0AlignedChunk13_pieces]
  rw [remainder6Coefficient0AlignedChunk14_pieces]
  rw [remainder6Coefficient0AlignedChunk15_pieces]
  rw [remainder6Coefficient0AlignedChunk16_pieces]
  rw [remainder6Coefficient0AlignedChunk17_pieces]
  rw [remainder6Coefficient0AlignedChunk18_pieces]
  rw [remainder6Coefficient0AlignedChunk19_pieces]
  rw [remainder6Coefficient0AlignedBand0_eq]
  rw [remainder6Coefficient0AlignedBand1_eq]
  rw [remainder6Coefficient0AlignedBand2_eq]
  rw [remainder6Coefficient0AlignedBand3_eq]
  rw [remainder6Coefficient0AlignedBand4_eq]
  rw [remainder6Coefficient0AlignedBand5_eq]
  rw [remainder6Coefficient0AlignedBand6_eq]
  rw [remainder6Coefficient0AlignedBand7_eq]
  rw [remainder6Coefficient0AlignedBand8_eq]
  rw [remainder6Coefficient0AlignedBand9_eq]
  rw [remainder6Coefficient0AlignedBand10_eq]
  rw [remainder6Coefficient0AlignedBand11_eq]
  rw [remainder6Coefficient0AlignedBand12_eq]
  rw [remainder6Coefficient0AlignedBand13_eq]
  rw [remainder6Coefficient0AlignedBand14_eq]
  rw [remainder6Coefficient0AlignedBand15_eq]
  rw [remainder6Coefficient0AlignedBand16_eq]
  rw [remainder6Coefficient0AlignedBand17_eq]
  ring

private theorem remainder6Coefficient0_eq_normalized :
    remainder6Coefficient0 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient0Normalized := by
  unfold remainder6Coefficient0 remainder6Coefficient0Block0 remainder6Coefficient0Block1
  rw [remainder6Coefficient0Chunk0_normalized]
  rw [remainder6Coefficient0Chunk1_normalized]
  rw [remainder6Coefficient0Chunk2_normalized]
  rw [remainder6Coefficient0Chunk3_normalized]
  rw [remainder6Coefficient0Chunk4_normalized]
  rw [remainder6Coefficient0Chunk5_normalized]
  rw [remainder6Coefficient0Chunk6_normalized]
  rw [remainder6Coefficient0Chunk7_normalized]
  rw [remainder6Coefficient0Chunk8_normalized]
  rw [remainder6Coefficient0Chunk9_normalized]
  rw [remainder6Coefficient0Chunk10_normalized]
  rw [remainder6Coefficient0Chunk11_normalized]
  rw [remainder6Coefficient0Chunk12_normalized]
  rw [remainder6Coefficient0Chunk13_normalized]
  rw [remainder6Coefficient0Chunk14_normalized]
  rw [remainder6Coefficient0Chunk15_normalized]
  rw [remainder6Coefficient0Chunk16_normalized]
  rw [remainder6Coefficient0Chunk17_normalized]
  rw [remainder6Coefficient0Chunk18_normalized]
  rw [remainder6Coefficient0Chunk19_normalized]
  rw [← remainder6Coefficient0Aligned_eq]
  unfold remainder6Coefficient0Aligned
  ring

private def remainder6Coefficient1AlignedChunk0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-32646364799)
  ))) * X ^ 149 +
  (Polynomial.C (show ℚ from (
    (-829291943502580567)
  ))) * X ^ 148 +
  (Polynomial.C (show ℚ from (
    (-628604454920783810227725)
  ))) * X ^ 147 +
  (Polynomial.C (show ℚ from (
    (-34615682827583525581641673048)
  ))) * X ^ 146 +
  (Polynomial.C (show ℚ from (
    (-255407535557399504723708573446909)
  ))) * X ^ 145 +
  (Polynomial.C (show ℚ from (
    (-337816829558560164731485066764570870)
  ))) * X ^ 144 +
  (Polynomial.C (show ℚ from (
    (-42784289162313052366077575615132899364)
  ))) * X ^ 143 +
  (Polynomial.C (show ℚ from (
    (77084809344741549843247386578211442014282)
  ))) * X ^ 142

private theorem remainder6Coefficient1Chunk0_normalized :
    remainder6Coefficient1Chunk0 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk0 := by
  unfold remainder6Coefficient1Chunk0 remainder6Coefficient1AlignedChunk0
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (34949069033454074023778121133192842625763867)
  ))) * X ^ 141 +
  (Polynomial.C (show ℚ from (
    (5657430280123554890146698443878643800128661481)
  ))) * X ^ 140 +
  (Polynomial.C (show ℚ from (
    (353831302943268531855241498453338113093049086118)
  ))) * X ^ 139 +
  (Polynomial.C (show ℚ from (
    (5295141873444018010528034933196118339963209523560)
  ))) * X ^ 138 +
  (Polynomial.C (show ℚ from (
    (-87349397999608465201590647724288903422050929669497)
  ))) * X ^ 137 +
  (Polynomial.C (show ℚ from (
    (-688749478297181782627572843413758934012754816881756)
  ))) * X ^ 136 +
  (Polynomial.C (show ℚ from (
    (15345184409244925588514528848807055958775804758572292)
  ))) * X ^ 135 +
  (Polynomial.C (show ℚ from (
    (-54949067767501893960984114471359101552623944378328882)
  ))) * X ^ 134

private theorem remainder6Coefficient1Chunk1_normalized :
    remainder6Coefficient1Chunk1 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk1 := by
  unfold remainder6Coefficient1Chunk1 remainder6Coefficient1AlignedChunk1
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-550012141652107742509116564062696719661341522188387546)
  ))) * X ^ 133 +
  (Polynomial.C (show ℚ from (
    (6820900389471520015141789453874300271257889393955115823)
  ))) * X ^ 132 +
  (Polynomial.C (show ℚ from (
    (-29975870781557738367952396965788291429074763707262194573)
  ))) * X ^ 131 +
  (Polynomial.C (show ℚ from (
    (15227511935352454413795665070520310916743161734788593665)
  ))) * X ^ 130 +
  (Polynomial.C (show ℚ from (
    (560220059289602656379710811202092389133057700183853101979)
  ))) * X ^ 129 +
  (Polynomial.C (show ℚ from (
    (-3578794873675906688169008207442118323281076638174100131586)
  ))) * X ^ 128 +
  (Polynomial.C (show ℚ from (
    (11619791320327420063395181493202615583647006197132931072613)
  ))) * X ^ 127 +
  (Polynomial.C (show ℚ from (
    (-16847669313701150440380224201114550344122965770374520620081)
  ))) * X ^ 126

private theorem remainder6Coefficient1Chunk2_normalized :
    remainder6Coefficient1Chunk2 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk2 := by
  unfold remainder6Coefficient1Chunk2 remainder6Coefficient1AlignedChunk2
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-36795884605893568421107838325663973923189645334593183163561)
  ))) * X ^ 125 +
  (Polynomial.C (show ℚ from (
    (320703290100936593595979067606184122213518382925609025953687)
  ))) * X ^ 124 +
  (Polynomial.C (show ℚ from (
    (-1167392838856886266590968474642159876945825779253025125452961)
  ))) * X ^ 123 +
  (Polynomial.C (show ℚ from (
    (3058300018192459208124641338740551528082892728782222545872794)
  ))) * X ^ 122 +
  (Polynomial.C (show ℚ from (
    (-7158405833160305959124086944040792396505498010888790998181469)
  ))) * X ^ 121 +
  (Polynomial.C (show ℚ from (
    (20064259046021939233201158419951357449863234790687973388714563)
  ))) * X ^ 120 +
  (Polynomial.C (show ℚ from (
    (-76811717942789493762969731613441022103512933807660763449852796)
  ))) * X ^ 119 +
  (Polynomial.C (show ℚ from (
    (325781642331751289198860219147812876921388281463088345184029281)
  ))) * X ^ 118

private theorem remainder6Coefficient1Chunk3_normalized :
    remainder6Coefficient1Chunk3 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk3 := by
  unfold remainder6Coefficient1Chunk3 remainder6Coefficient1AlignedChunk3
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1292167493651053931930417523074880279040239280035567209685386183)
  ))) * X ^ 117 +
  (Polynomial.C (show ℚ from (
    (4586391485975044371173360845666909512293425014692696647491108446)
  ))) * X ^ 116 +
  (Polynomial.C (show ℚ from (
    (-14525957674526859027049516783135707089573085687685440039344631743)
  ))) * X ^ 115 +
  (Polynomial.C (show ℚ from (
    (40972032536222324135246421266859106956992220589587034604395230794)
  ))) * X ^ 114 +
  (Polynomial.C (show ℚ from (
    (-101208137235814392737782240456237161437126591617167346795810708727)
  ))) * X ^ 113 +
  (Polynomial.C (show ℚ from (
    (208299135501040602931989347713131733754535134262297933140788073248)
  ))) * X ^ 112 +
  (Polynomial.C (show ℚ from (
    (-306317708056453712416430157790503340029530587330436762208453096027)
  ))) * X ^ 111 +
  (Polynomial.C (show ℚ from (
    (79066895090843790771810602430748116062234014103793327778390719268)
  ))) * X ^ 110

private theorem remainder6Coefficient1Chunk4_normalized :
    remainder6Coefficient1Chunk4 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk4 := by
  unfold remainder6Coefficient1Chunk4 remainder6Coefficient1AlignedChunk4
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (1361839444475994305256684761856258907366832517461470347540034770523)
  ))) * X ^ 109 +
  (Polynomial.C (show ℚ from (
    (-5266628262613552467751701931599097804853507812602951022137077532246)
  ))) * X ^ 108 +
  (Polynomial.C (show ℚ from (
    (9679782543230701849534536280061816149344457715815040165936710410879)
  ))) * X ^ 107 +
  (Polynomial.C (show ℚ from (
    (5078562991219035694412459571489722304882424194536298956753495328949)
  ))) * X ^ 106 +
  (Polynomial.C (show ℚ from (
    (-114296699021103594561170706790928474782581762972760749760195352466294)
  ))) * X ^ 105 +
  (Polynomial.C (show ℚ from (
    (510962782062498120438050847624515628640164354450215912698356180077116)
  ))) * X ^ 104 +
  (Polynomial.C (show ℚ from (
    (-1514258174521396413243747486690349085094461830833368890466131151267297)
  ))) * X ^ 103 +
  (Polynomial.C (show ℚ from (
    (3192699187012670083136030675801181043266131311313232109270171160853643)
  ))) * X ^ 102

private theorem remainder6Coefficient1Chunk5_normalized :
    remainder6Coefficient1Chunk5 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk5 := by
  unfold remainder6Coefficient1Chunk5 remainder6Coefficient1AlignedChunk5
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-3680662862888424541338312046612503014550617679450964928522812502833969)
  ))) * X ^ 101 +
  (Polynomial.C (show ℚ from (
    (-5767212949237432423750797818634281511982432144698592691236840862804664)
  ))) * X ^ 100 +
  (Polynomial.C (show ℚ from (
    (52188785806971160040365933102123305324874396735897714817956942976590820)
  ))) * X ^ 99 +
  (Polynomial.C (show ℚ from (
    (-202406453838347613755062476461338090241680518876739817079789698403347205)
  ))) * X ^ 98 +
  (Polynomial.C (show ℚ from (
    (595414155467326252149412440520095318971452175379082518914143415725485847)
  ))) * X ^ 97 +
  (Polynomial.C (show ℚ from (
    (-1476956683205358756515243135524802883776096838285262203533692269792350404)
  ))) * X ^ 96 +
  (Polynomial.C (show ℚ from (
    (3208368793046764133270132699287388779655531164347764414141194511135167914)
  ))) * X ^ 95 +
  (Polynomial.C (show ℚ from (
    (-6194188420304178967976399679870947335293403491515397350939159891405856314)
  ))) * X ^ 94

private theorem remainder6Coefficient1Chunk6_normalized :
    remainder6Coefficient1Chunk6 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk6 := by
  unfold remainder6Coefficient1Chunk6 remainder6Coefficient1AlignedChunk6
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (10648127401628743433040622866630128366972237867115528095669957273940608455)
  ))) * X ^ 93 +
  (Polynomial.C (show ℚ from (
    (-16118315776932703342985654798249282756581745036276230917139746518460391012)
  ))) * X ^ 92 +
  (Polynomial.C (show ℚ from (
    (20752340592239391289171629893765927190583484320972108170334078416283250957)
  ))) * X ^ 91 +
  (Polynomial.C (show ℚ from (
    (-20425123301791903508084023287307768952044757984571641977496110172681710774)
  ))) * X ^ 90 +
  (Polynomial.C (show ℚ from (
    (8072102445789057794764730166899922617448999921899400473984438581641551506)
  ))) * X ^ 89 +
  (Polynomial.C (show ℚ from (
    (26184561133108978782685726633962502193815495576303107693435569395861044647)
  ))) * X ^ 88 +
  (Polynomial.C (show ℚ from (
    (-93334208560511380242369054037508321606940968655584380427987897636070224386)
  ))) * X ^ 87 +
  (Polynomial.C (show ℚ from (
    (201304539349675641512158042538733780844999176589046936969183686054556470822)
  ))) * X ^ 86

private theorem remainder6Coefficient1Chunk7_normalized :
    remainder6Coefficient1Chunk7 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk7 := by
  unfold remainder6Coefficient1Chunk7 remainder6Coefficient1AlignedChunk7
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-347276377651067159257707635441236811435629855018596152612894362953739285405)
  ))) * X ^ 85 +
  (Polynomial.C (show ℚ from (
    (504961395290265913355211704472768898607591895503985383009870893225150926585)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (-604111191378376555965203799092787763338440432357669357553365294022881408014)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (497516681623659343481162060557099257388171759656874674308977979595009607081)
  ))) * X ^ 82 +
  (Polynomial.C (show ℚ from (
    (91246490511293030876261308691543357744702656490978704395707013799069138165)
  ))) * X ^ 81 +
  (Polynomial.C (show ℚ from (
    (-1645868888744962279039938270406952810535730737155107401659299406109508450510)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    (4961829106475810091830405638018925185649708851756873794402126220222392758041)
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    (-11263158740395500032971760536186077534702568417686380943454146040458065263612)
  ))) * X ^ 78

private theorem remainder6Coefficient1Chunk8_normalized :
    remainder6Coefficient1Chunk8 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk8 := by
  unfold remainder6Coefficient1Chunk8 remainder6Coefficient1AlignedChunk8
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (22292795500726545495650622561731256977009194742684949932744295944202436541354)
  ))) * X ^ 77 +
  (Polynomial.C (show ℚ from (
    (-40309742970330971594224055758703850739190216794408059888847006869392685825135)
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    (67908540117832763268077164550841107146559375432026411755103928077605177950537)
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    -((1 * 10 ^ 77 +
      07589168603139865655688742267818826830033825579883803410398850845647593330054))
  ))) * X ^ 74 +
  (Polynomial.C (show ℚ from (
    ((1 * 10 ^ 77 +
      61065349015230913098066109961856557698126639322772003005328983998638313605711))
  ))) * X ^ 73 +
  (Polynomial.C (show ℚ from (
    -((2 * 10 ^ 77 +
      28406292696161748032539526604229462632624739479461906214693181681686189108618))
  ))) * X ^ 72 +
  (Polynomial.C (show ℚ from (
    ((3 * 10 ^ 77 +
      07233067522820703296322519912028089389638087912173019133488292540718835322894))
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    -((3 * 10 ^ 77 +
      92279629173000675191914937585966021658258688416609549337162695153908502446971))
  ))) * X ^ 70

private theorem remainder6Coefficient1Chunk9_normalized :
    remainder6Coefficient1Chunk9 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk9 := by
  unfold remainder6Coefficient1Chunk9 remainder6Coefficient1AlignedChunk9
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((4 * 10 ^ 77 +
      75616100751156912344550906524715535752936527176209405420405130688849497285240))
  ))) * X ^ 69 +
  (Polynomial.C (show ℚ from (
    -((5 * 10 ^ 77 +
      47681347692086270200453896149500023441935170606155287187213250852618245463016))
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    ((5 * 10 ^ 77 +
      99007526771983622024961041933915911771397927643746673326268953484884302582286))
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    -((6 * 10 ^ 77 +
      22233801090290864506752235931225966878422570340865785942839186123450095481502))
  ))) * X ^ 66 +
  (Polynomial.C (show ℚ from (
    ((6 * 10 ^ 77 +
      13828247482595396108180681635662466319376220268531706400037507829754795026160))
  ))) * X ^ 65 +
  (Polynomial.C (show ℚ from (
    -((5 * 10 ^ 77 +
      74967002780227207653441635486140364429502612670087192369412177004107996437651))
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    ((5 * 10 ^ 77 +
      11271018973226403084610152716471651023882845672525092523337251433164613472134))
  ))) * X ^ 63 +
  (Polynomial.C (show ℚ from (
    -((4 * 10 ^ 77 +
      31480460952442785738727149776611962491416978088718780656676911574972820469505))
  ))) * X ^ 62

private theorem remainder6Coefficient1Chunk10_normalized :
    remainder6Coefficient1Chunk10 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk10 := by
  unfold remainder6Coefficient1Chunk10 remainder6Coefficient1AlignedChunk10
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((3 * 10 ^ 77 +
      45496095358789815994917357654442111080116949740623572010968033682030448701773))
  ))) * X ^ 61 +
  (Polynomial.C (show ℚ from (
    -((2 * 10 ^ 77 +
      62390877255729292069734956317813131383914643905288376187845000126644970771387))
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    ((1 * 10 ^ 77 +
      88934231556768969666288601567887177442548881947838227624041174300786609885302))
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    -((1 * 10 ^ 77 +
      28926658191238374402982674492799646460971807484734212775272012237975629511571))
  ))) * X ^ 58 +
  (Polynomial.C (show ℚ from (
    (83337319728219309353643709160132439581903449184925822360356202401648277586365)
  ))) * X ^ 57 +
  (Polynomial.C (show ℚ from (
    (-51000676833058058847830888650529857441731564106454302984740150060668386548203)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (29532933062310640398559105041362012812279013283098162628070558176406046372994)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (-16172052832881799815811386572291649978653870364345077102585740015073912224369)
  ))) * X ^ 54

private theorem remainder6Coefficient1Chunk11_normalized :
    remainder6Coefficient1Chunk11 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk11 := by
  unfold remainder6Coefficient1Chunk11 remainder6Coefficient1AlignedChunk11
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (8368809122909134402785809926929710898277317876890997314008582369321799855095)
  ))) * X ^ 53 +
  (Polynomial.C (show ℚ from (
    (-4089701237372603393942115697413109871407476089294002478996340396255361965250)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (1885883645306065345407734368248235176392763118022379681753891716901473739523)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (-819926761071557491986684525143537722436650270723188189798615064990178876392)
  ))) * X ^ 50 +
  (Polynomial.C (show ℚ from (
    (335805587962875496779215631487887125521203974641673770671045382165563378343)
  ))) * X ^ 49 +
  (Polynomial.C (show ℚ from (
    (-129432242807956872685946883712150135121504532736337488536363020096864747409)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (46902894713552276776052343106383943913544634619089326315424396567118706858)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-15962131725836457790242810983832890091298454344481989735046647367116899202)
  ))) * X ^ 46

private theorem remainder6Coefficient1Chunk12_normalized :
    remainder6Coefficient1Chunk12 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk12 := by
  unfold remainder6Coefficient1Chunk12 remainder6Coefficient1AlignedChunk12
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (5095851787694845478251494884234271688780572292005832692277220333991379951)
  ))) * X ^ 45 +
  (Polynomial.C (show ℚ from (
    (-1524212555728526308411052904731082188282472256986120069587052004500756912)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (426590673955389292953077613175553826683975608599631076782262583982886926)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-111561116078604215175217757404884963949565948743368649753898161356194783)
  ))) * X ^ 42 +
  (Polynomial.C (show ℚ from (
    (27221449081976767004247883582769350178570635018704977554298927581867886)
  ))) * X ^ 41 +
  (Polynomial.C (show ℚ from (
    (-6187690045191682851887943566660818296162879904499330805342986730320337)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (1308114267436696918172142435212814692538146167470957147386344421877266)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-256744046667862068846674877548849556955561278081750059859069979729416)
  ))) * X ^ 38

private theorem remainder6Coefficient1Chunk13_normalized :
    remainder6Coefficient1Chunk13 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk13 := by
  unfold remainder6Coefficient1Chunk13 remainder6Coefficient1AlignedChunk13
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (46696581412966801563821061078959037032378265543083741355001841208071)
  ))) * X ^ 37 +
  (Polynomial.C (show ℚ from (
    (-7854971716047596331840317568446269343944541014517362983168032009836)
  ))) * X ^ 36 +
  (Polynomial.C (show ℚ from (
    (1219477313588973843646241530545233572499228465774236050691984357830)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-174346932582108762891968048727212785377842539175139539224841479002)
  ))) * X ^ 34 +
  (Polynomial.C (show ℚ from (
    (22900897877104644196077073265838987871672546090864259256652998994)
  ))) * X ^ 33 +
  (Polynomial.C (show ℚ from (
    (-2756863799354424063565863604580708006505044319002548471425329438)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (303365904414424253444528813714061121114166275681051234455363332)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-30430118864130425748703910565756316113335609827206507214801102)
  ))) * X ^ 30

private theorem remainder6Coefficient1Chunk14_normalized :
    remainder6Coefficient1Chunk14 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk14 := by
  unfold remainder6Coefficient1Chunk14 remainder6Coefficient1AlignedChunk14
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (2774280384586168834757757415451387202835509943822045435320506)
  ))) * X ^ 29 +
  (Polynomial.C (show ℚ from (
    (-229167447164589387170273929889102413618684761215622480147728)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (17095112018455109258051668393162863828761984749719538924471)
  ))) * X ^ 27 +
  (Polynomial.C (show ℚ from (
    (-1147556166996901742301857460789324836050067004988125662529)
  ))) * X ^ 26 +
  (Polynomial.C (show ℚ from (
    (69059116807592080504075449248445120103923356823058379852)
  ))) * X ^ 25 +
  (Polynomial.C (show ℚ from (
    (-3710719600962041005883293073209742318481852818671524723)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (177254644824833186419455642547377542466564273550239548)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-7492037580113858564025716984583179466893737124276699)
  ))) * X ^ 22

private theorem remainder6Coefficient1Chunk15_normalized :
    remainder6Coefficient1Chunk15 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk15 := by
  unfold remainder6Coefficient1Chunk15 remainder6Coefficient1AlignedChunk15
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk16 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (278772498713203553010397733936946226452121600310440)
  ))) * X ^ 21 +
  (Polynomial.C (show ℚ from (
    (-9080860764762484244413752157954192816831801335856)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (257375873092856585517599096584639078635147703574)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-6304031064275710298920670199834042939195399665)
  ))) * X ^ 18 +
  (Polynomial.C (show ℚ from (
    (132425533854943997858641366080658058464271265)
  ))) * X ^ 17 +
  (Polynomial.C (show ℚ from (
    (-2365296933549129088286913765011294686806132)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (35568751424021237027745312927425496360840)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-445160742552088933159288853832453337332)
  ))) * X ^ 14

private theorem remainder6Coefficient1Chunk16_normalized :
    remainder6Coefficient1Chunk16 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk16 := by
  unfold remainder6Coefficient1Chunk16 remainder6Coefficient1AlignedChunk16
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk17 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (4573692275562316018834947468906919588)
  ))) * X ^ 13 +
  (Polynomial.C (show ℚ from (
    (-37930404038831438701292987496857940)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (248440952223035694061850285297952)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-1246737004206718197903556045010)
  ))) * X ^ 10 +
  (Polynomial.C (show ℚ from (
    (4566186685707920356612547512)
  ))) * X ^ 9 +
  (Polynomial.C (show ℚ from (
    (-11060624912306014584153124)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (12641698329565160961087)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (14683509676476842482)
  ))) * X ^ 6

private theorem remainder6Coefficient1Chunk17_normalized :
    remainder6Coefficient1Chunk17 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk17 := by
  unfold remainder6Coefficient1Chunk17 remainder6Coefficient1AlignedChunk17
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1AlignedChunk18 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-80002118437425346)
  ))) * X ^ 5 +
  (Polynomial.C (show ℚ from (
    (127461111936338)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-100865550084)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (39681278)
  ))) * X ^ 2 +
  (Polynomial.C (show ℚ from (
    (-7256)
  ))) * X ^ 1

private theorem remainder6Coefficient1Chunk18_normalized :
    remainder6Coefficient1Chunk18 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1AlignedChunk18 := by
  unfold remainder6Coefficient1Chunk18 remainder6Coefficient1AlignedChunk18
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient1Aligned : Coefficient :=
  remainder6Coefficient1AlignedChunk0 +
  remainder6Coefficient1AlignedChunk1 +
  remainder6Coefficient1AlignedChunk2 +
  remainder6Coefficient1AlignedChunk3 +
  remainder6Coefficient1AlignedChunk4 +
  remainder6Coefficient1AlignedChunk5 +
  remainder6Coefficient1AlignedChunk6 +
  remainder6Coefficient1AlignedChunk7 +
  remainder6Coefficient1AlignedChunk8 +
  remainder6Coefficient1AlignedChunk9 +
  remainder6Coefficient1AlignedChunk10 +
  remainder6Coefficient1AlignedChunk11 +
  remainder6Coefficient1AlignedChunk12 +
  remainder6Coefficient1AlignedChunk13 +
  remainder6Coefficient1AlignedChunk14 +
  remainder6Coefficient1AlignedChunk15 +
  remainder6Coefficient1AlignedChunk16 +
  remainder6Coefficient1AlignedChunk17 +
  remainder6Coefficient1AlignedChunk18

private def remainder6Coefficient1AlignedChunk0Band15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-42784289162313052366077575615132899364)
  ))) * X ^ 143 +
  (Polynomial.C (show ℚ from (
    (77084809344741549843247386578211442014282)
  ))) * X ^ 142

private def remainder6Coefficient1AlignedChunk0Band16 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-32646364799)
  ))) * X ^ 149 +
  (Polynomial.C (show ℚ from (
    (-829291943502580567)
  ))) * X ^ 148 +
  (Polynomial.C (show ℚ from (
    (-628604454920783810227725)
  ))) * X ^ 147 +
  (Polynomial.C (show ℚ from (
    (-34615682827583525581641673048)
  ))) * X ^ 146 +
  (Polynomial.C (show ℚ from (
    (-255407535557399504723708573446909)
  ))) * X ^ 145 +
  (Polynomial.C (show ℚ from (
    (-337816829558560164731485066764570870)
  ))) * X ^ 144

private theorem remainder6Coefficient1AlignedChunk0_pieces :
    remainder6Coefficient1AlignedChunk0 =
      remainder6Coefficient1AlignedChunk0Band15 +
      remainder6Coefficient1AlignedChunk0Band16
    := by
  unfold remainder6Coefficient1AlignedChunk0 remainder6Coefficient1AlignedChunk0Band15
  unfold remainder6Coefficient1AlignedChunk0Band16
  ring

private def remainder6Coefficient1AlignedChunk1Band14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-54949067767501893960984114471359101552623944378328882)
  ))) * X ^ 134

private def remainder6Coefficient1AlignedChunk1Band15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (34949069033454074023778121133192842625763867)
  ))) * X ^ 141 +
  (Polynomial.C (show ℚ from (
    (5657430280123554890146698443878643800128661481)
  ))) * X ^ 140 +
  (Polynomial.C (show ℚ from (
    (353831302943268531855241498453338113093049086118)
  ))) * X ^ 139 +
  (Polynomial.C (show ℚ from (
    (5295141873444018010528034933196118339963209523560)
  ))) * X ^ 138 +
  (Polynomial.C (show ℚ from (
    (-87349397999608465201590647724288903422050929669497)
  ))) * X ^ 137 +
  (Polynomial.C (show ℚ from (
    (-688749478297181782627572843413758934012754816881756)
  ))) * X ^ 136 +
  (Polynomial.C (show ℚ from (
    (15345184409244925588514528848807055958775804758572292)
  ))) * X ^ 135

private theorem remainder6Coefficient1AlignedChunk1_pieces :
    remainder6Coefficient1AlignedChunk1 =
      remainder6Coefficient1AlignedChunk1Band14 +
      remainder6Coefficient1AlignedChunk1Band15
    := by
  unfold remainder6Coefficient1AlignedChunk1 remainder6Coefficient1AlignedChunk1Band14
  unfold remainder6Coefficient1AlignedChunk1Band15
  ring

private def remainder6Coefficient1AlignedChunk2Band14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-550012141652107742509116564062696719661341522188387546)
  ))) * X ^ 133 +
  (Polynomial.C (show ℚ from (
    (6820900389471520015141789453874300271257889393955115823)
  ))) * X ^ 132 +
  (Polynomial.C (show ℚ from (
    (-29975870781557738367952396965788291429074763707262194573)
  ))) * X ^ 131 +
  (Polynomial.C (show ℚ from (
    (15227511935352454413795665070520310916743161734788593665)
  ))) * X ^ 130 +
  (Polynomial.C (show ℚ from (
    (560220059289602656379710811202092389133057700183853101979)
  ))) * X ^ 129 +
  (Polynomial.C (show ℚ from (
    (-3578794873675906688169008207442118323281076638174100131586)
  ))) * X ^ 128 +
  (Polynomial.C (show ℚ from (
    (11619791320327420063395181493202615583647006197132931072613)
  ))) * X ^ 127 +
  (Polynomial.C (show ℚ from (
    (-16847669313701150440380224201114550344122965770374520620081)
  ))) * X ^ 126

private theorem remainder6Coefficient1AlignedChunk2_pieces :
    remainder6Coefficient1AlignedChunk2 =
      remainder6Coefficient1AlignedChunk2Band14
    := by
  unfold remainder6Coefficient1AlignedChunk2 remainder6Coefficient1AlignedChunk2Band14
  ring

private def remainder6Coefficient1AlignedChunk3Band13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-36795884605893568421107838325663973923189645334593183163561)
  ))) * X ^ 125 +
  (Polynomial.C (show ℚ from (
    (320703290100936593595979067606184122213518382925609025953687)
  ))) * X ^ 124 +
  (Polynomial.C (show ℚ from (
    (-1167392838856886266590968474642159876945825779253025125452961)
  ))) * X ^ 123 +
  (Polynomial.C (show ℚ from (
    (3058300018192459208124641338740551528082892728782222545872794)
  ))) * X ^ 122 +
  (Polynomial.C (show ℚ from (
    (-7158405833160305959124086944040792396505498010888790998181469)
  ))) * X ^ 121 +
  (Polynomial.C (show ℚ from (
    (20064259046021939233201158419951357449863234790687973388714563)
  ))) * X ^ 120 +
  (Polynomial.C (show ℚ from (
    (-76811717942789493762969731613441022103512933807660763449852796)
  ))) * X ^ 119 +
  (Polynomial.C (show ℚ from (
    (325781642331751289198860219147812876921388281463088345184029281)
  ))) * X ^ 118

private theorem remainder6Coefficient1AlignedChunk3_pieces :
    remainder6Coefficient1AlignedChunk3 =
      remainder6Coefficient1AlignedChunk3Band13
    := by
  unfold remainder6Coefficient1AlignedChunk3 remainder6Coefficient1AlignedChunk3Band13
  ring

private def remainder6Coefficient1AlignedChunk4Band12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (4586391485975044371173360845666909512293425014692696647491108446)
  ))) * X ^ 116 +
  (Polynomial.C (show ℚ from (
    (-14525957674526859027049516783135707089573085687685440039344631743)
  ))) * X ^ 115 +
  (Polynomial.C (show ℚ from (
    (40972032536222324135246421266859106956992220589587034604395230794)
  ))) * X ^ 114 +
  (Polynomial.C (show ℚ from (
    (-101208137235814392737782240456237161437126591617167346795810708727)
  ))) * X ^ 113 +
  (Polynomial.C (show ℚ from (
    (208299135501040602931989347713131733754535134262297933140788073248)
  ))) * X ^ 112 +
  (Polynomial.C (show ℚ from (
    (-306317708056453712416430157790503340029530587330436762208453096027)
  ))) * X ^ 111 +
  (Polynomial.C (show ℚ from (
    (79066895090843790771810602430748116062234014103793327778390719268)
  ))) * X ^ 110

private def remainder6Coefficient1AlignedChunk4Band13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1292167493651053931930417523074880279040239280035567209685386183)
  ))) * X ^ 117

private theorem remainder6Coefficient1AlignedChunk4_pieces :
    remainder6Coefficient1AlignedChunk4 =
      remainder6Coefficient1AlignedChunk4Band12 +
      remainder6Coefficient1AlignedChunk4Band13
    := by
  unfold remainder6Coefficient1AlignedChunk4 remainder6Coefficient1AlignedChunk4Band12
  unfold remainder6Coefficient1AlignedChunk4Band13
  ring

private def remainder6Coefficient1AlignedChunk5Band11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (9679782543230701849534536280061816149344457715815040165936710410879)
  ))) * X ^ 107 +
  (Polynomial.C (show ℚ from (
    (5078562991219035694412459571489722304882424194536298956753495328949)
  ))) * X ^ 106 +
  (Polynomial.C (show ℚ from (
    (-114296699021103594561170706790928474782581762972760749760195352466294)
  ))) * X ^ 105 +
  (Polynomial.C (show ℚ from (
    (510962782062498120438050847624515628640164354450215912698356180077116)
  ))) * X ^ 104 +
  (Polynomial.C (show ℚ from (
    (-1514258174521396413243747486690349085094461830833368890466131151267297)
  ))) * X ^ 103 +
  (Polynomial.C (show ℚ from (
    (3192699187012670083136030675801181043266131311313232109270171160853643)
  ))) * X ^ 102

private def remainder6Coefficient1AlignedChunk5Band12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (1361839444475994305256684761856258907366832517461470347540034770523)
  ))) * X ^ 109 +
  (Polynomial.C (show ℚ from (
    (-5266628262613552467751701931599097804853507812602951022137077532246)
  ))) * X ^ 108

private theorem remainder6Coefficient1AlignedChunk5_pieces :
    remainder6Coefficient1AlignedChunk5 =
      remainder6Coefficient1AlignedChunk5Band11 +
      remainder6Coefficient1AlignedChunk5Band12
    := by
  unfold remainder6Coefficient1AlignedChunk5 remainder6Coefficient1AlignedChunk5Band11
  unfold remainder6Coefficient1AlignedChunk5Band12
  ring

private def remainder6Coefficient1AlignedChunk6Band10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-202406453838347613755062476461338090241680518876739817079789698403347205)
  ))) * X ^ 98 +
  (Polynomial.C (show ℚ from (
    (595414155467326252149412440520095318971452175379082518914143415725485847)
  ))) * X ^ 97 +
  (Polynomial.C (show ℚ from (
    (-1476956683205358756515243135524802883776096838285262203533692269792350404)
  ))) * X ^ 96 +
  (Polynomial.C (show ℚ from (
    (3208368793046764133270132699287388779655531164347764414141194511135167914)
  ))) * X ^ 95 +
  (Polynomial.C (show ℚ from (
    (-6194188420304178967976399679870947335293403491515397350939159891405856314)
  ))) * X ^ 94

private def remainder6Coefficient1AlignedChunk6Band11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-3680662862888424541338312046612503014550617679450964928522812502833969)
  ))) * X ^ 101 +
  (Polynomial.C (show ℚ from (
    (-5767212949237432423750797818634281511982432144698592691236840862804664)
  ))) * X ^ 100 +
  (Polynomial.C (show ℚ from (
    (52188785806971160040365933102123305324874396735897714817956942976590820)
  ))) * X ^ 99

private theorem remainder6Coefficient1AlignedChunk6_pieces :
    remainder6Coefficient1AlignedChunk6 =
      remainder6Coefficient1AlignedChunk6Band10 +
      remainder6Coefficient1AlignedChunk6Band11
    := by
  unfold remainder6Coefficient1AlignedChunk6 remainder6Coefficient1AlignedChunk6Band10
  unfold remainder6Coefficient1AlignedChunk6Band11
  ring

private def remainder6Coefficient1AlignedChunk7Band9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (8072102445789057794764730166899922617448999921899400473984438581641551506)
  ))) * X ^ 89 +
  (Polynomial.C (show ℚ from (
    (26184561133108978782685726633962502193815495576303107693435569395861044647)
  ))) * X ^ 88 +
  (Polynomial.C (show ℚ from (
    (-93334208560511380242369054037508321606940968655584380427987897636070224386)
  ))) * X ^ 87 +
  (Polynomial.C (show ℚ from (
    (201304539349675641512158042538733780844999176589046936969183686054556470822)
  ))) * X ^ 86

private def remainder6Coefficient1AlignedChunk7Band10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (10648127401628743433040622866630128366972237867115528095669957273940608455)
  ))) * X ^ 93 +
  (Polynomial.C (show ℚ from (
    (-16118315776932703342985654798249282756581745036276230917139746518460391012)
  ))) * X ^ 92 +
  (Polynomial.C (show ℚ from (
    (20752340592239391289171629893765927190583484320972108170334078416283250957)
  ))) * X ^ 91 +
  (Polynomial.C (show ℚ from (
    (-20425123301791903508084023287307768952044757984571641977496110172681710774)
  ))) * X ^ 90

private theorem remainder6Coefficient1AlignedChunk7_pieces :
    remainder6Coefficient1AlignedChunk7 =
      remainder6Coefficient1AlignedChunk7Band9 +
      remainder6Coefficient1AlignedChunk7Band10
    := by
  unfold remainder6Coefficient1AlignedChunk7 remainder6Coefficient1AlignedChunk7Band9
  unfold remainder6Coefficient1AlignedChunk7Band10
  ring

private def remainder6Coefficient1AlignedChunk8Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1645868888744962279039938270406952810535730737155107401659299406109508450510)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    (4961829106475810091830405638018925185649708851756873794402126220222392758041)
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    (-11263158740395500032971760536186077534702568417686380943454146040458065263612)
  ))) * X ^ 78

private def remainder6Coefficient1AlignedChunk8Band9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-347276377651067159257707635441236811435629855018596152612894362953739285405)
  ))) * X ^ 85 +
  (Polynomial.C (show ℚ from (
    (504961395290265913355211704472768898607591895503985383009870893225150926585)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (-604111191378376555965203799092787763338440432357669357553365294022881408014)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (497516681623659343481162060557099257388171759656874674308977979595009607081)
  ))) * X ^ 82 +
  (Polynomial.C (show ℚ from (
    (91246490511293030876261308691543357744702656490978704395707013799069138165)
  ))) * X ^ 81

private theorem remainder6Coefficient1AlignedChunk8_pieces :
    remainder6Coefficient1AlignedChunk8 =
      remainder6Coefficient1AlignedChunk8Band8 +
      remainder6Coefficient1AlignedChunk8Band9
    := by
  unfold remainder6Coefficient1AlignedChunk8 remainder6Coefficient1AlignedChunk8Band8
  unfold remainder6Coefficient1AlignedChunk8Band9
  ring

private def remainder6Coefficient1AlignedChunk9Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((3 * 10 ^ 77 +
      07233067522820703296322519912028089389638087912173019133488292540718835322894))
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    -((3 * 10 ^ 77 +
      92279629173000675191914937585966021658258688416609549337162695153908502446971))
  ))) * X ^ 70

private def remainder6Coefficient1AlignedChunk9Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (22292795500726545495650622561731256977009194742684949932744295944202436541354)
  ))) * X ^ 77 +
  (Polynomial.C (show ℚ from (
    (-40309742970330971594224055758703850739190216794408059888847006869392685825135)
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    (67908540117832763268077164550841107146559375432026411755103928077605177950537)
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    -((1 * 10 ^ 77 +
      07589168603139865655688742267818826830033825579883803410398850845647593330054))
  ))) * X ^ 74 +
  (Polynomial.C (show ℚ from (
    ((1 * 10 ^ 77 +
      61065349015230913098066109961856557698126639322772003005328983998638313605711))
  ))) * X ^ 73 +
  (Polynomial.C (show ℚ from (
    -((2 * 10 ^ 77 +
      28406292696161748032539526604229462632624739479461906214693181681686189108618))
  ))) * X ^ 72

private theorem remainder6Coefficient1AlignedChunk9_pieces :
    remainder6Coefficient1AlignedChunk9 =
      remainder6Coefficient1AlignedChunk9Band7 +
      remainder6Coefficient1AlignedChunk9Band8
    := by
  unfold remainder6Coefficient1AlignedChunk9 remainder6Coefficient1AlignedChunk9Band7
  unfold remainder6Coefficient1AlignedChunk9Band8
  ring

private def remainder6Coefficient1AlignedChunk10Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    -((4 * 10 ^ 77 +
      31480460952442785738727149776611962491416978088718780656676911574972820469505))
  ))) * X ^ 62

private def remainder6Coefficient1AlignedChunk10Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((4 * 10 ^ 77 +
      75616100751156912344550906524715535752936527176209405420405130688849497285240))
  ))) * X ^ 69 +
  (Polynomial.C (show ℚ from (
    -((5 * 10 ^ 77 +
      47681347692086270200453896149500023441935170606155287187213250852618245463016))
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    ((5 * 10 ^ 77 +
      99007526771983622024961041933915911771397927643746673326268953484884302582286))
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    -((6 * 10 ^ 77 +
      22233801090290864506752235931225966878422570340865785942839186123450095481502))
  ))) * X ^ 66 +
  (Polynomial.C (show ℚ from (
    ((6 * 10 ^ 77 +
      13828247482595396108180681635662466319376220268531706400037507829754795026160))
  ))) * X ^ 65 +
  (Polynomial.C (show ℚ from (
    -((5 * 10 ^ 77 +
      74967002780227207653441635486140364429502612670087192369412177004107996437651))
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    ((5 * 10 ^ 77 +
      11271018973226403084610152716471651023882845672525092523337251433164613472134))
  ))) * X ^ 63

private theorem remainder6Coefficient1AlignedChunk10_pieces :
    remainder6Coefficient1AlignedChunk10 =
      remainder6Coefficient1AlignedChunk10Band6 +
      remainder6Coefficient1AlignedChunk10Band7
    := by
  unfold remainder6Coefficient1AlignedChunk10 remainder6Coefficient1AlignedChunk10Band6
  unfold remainder6Coefficient1AlignedChunk10Band7
  ring

private def remainder6Coefficient1AlignedChunk11Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    ((3 * 10 ^ 77 +
      45496095358789815994917357654442111080116949740623572010968033682030448701773))
  ))) * X ^ 61 +
  (Polynomial.C (show ℚ from (
    -((2 * 10 ^ 77 +
      62390877255729292069734956317813131383914643905288376187845000126644970771387))
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    ((1 * 10 ^ 77 +
      88934231556768969666288601567887177442548881947838227624041174300786609885302))
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    -((1 * 10 ^ 77 +
      28926658191238374402982674492799646460971807484734212775272012237975629511571))
  ))) * X ^ 58 +
  (Polynomial.C (show ℚ from (
    (83337319728219309353643709160132439581903449184925822360356202401648277586365)
  ))) * X ^ 57 +
  (Polynomial.C (show ℚ from (
    (-51000676833058058847830888650529857441731564106454302984740150060668386548203)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (29532933062310640398559105041362012812279013283098162628070558176406046372994)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (-16172052832881799815811386572291649978653870364345077102585740015073912224369)
  ))) * X ^ 54

private theorem remainder6Coefficient1AlignedChunk11_pieces :
    remainder6Coefficient1AlignedChunk11 =
      remainder6Coefficient1AlignedChunk11Band6
    := by
  unfold remainder6Coefficient1AlignedChunk11 remainder6Coefficient1AlignedChunk11Band6
  ring

private def remainder6Coefficient1AlignedChunk12Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (8368809122909134402785809926929710898277317876890997314008582369321799855095)
  ))) * X ^ 53 +
  (Polynomial.C (show ℚ from (
    (-4089701237372603393942115697413109871407476089294002478996340396255361965250)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (1885883645306065345407734368248235176392763118022379681753891716901473739523)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (-819926761071557491986684525143537722436650270723188189798615064990178876392)
  ))) * X ^ 50 +
  (Polynomial.C (show ℚ from (
    (335805587962875496779215631487887125521203974641673770671045382165563378343)
  ))) * X ^ 49 +
  (Polynomial.C (show ℚ from (
    (-129432242807956872685946883712150135121504532736337488536363020096864747409)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (46902894713552276776052343106383943913544634619089326315424396567118706858)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-15962131725836457790242810983832890091298454344481989735046647367116899202)
  ))) * X ^ 46

private theorem remainder6Coefficient1AlignedChunk12_pieces :
    remainder6Coefficient1AlignedChunk12 =
      remainder6Coefficient1AlignedChunk12Band5
    := by
  unfold remainder6Coefficient1AlignedChunk12 remainder6Coefficient1AlignedChunk12Band5
  ring

private def remainder6Coefficient1AlignedChunk13Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1524212555728526308411052904731082188282472256986120069587052004500756912)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (426590673955389292953077613175553826683975608599631076782262583982886926)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-111561116078604215175217757404884963949565948743368649753898161356194783)
  ))) * X ^ 42 +
  (Polynomial.C (show ℚ from (
    (27221449081976767004247883582769350178570635018704977554298927581867886)
  ))) * X ^ 41 +
  (Polynomial.C (show ℚ from (
    (-6187690045191682851887943566660818296162879904499330805342986730320337)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (1308114267436696918172142435212814692538146167470957147386344421877266)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-256744046667862068846674877548849556955561278081750059859069979729416)
  ))) * X ^ 38

private def remainder6Coefficient1AlignedChunk13Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (5095851787694845478251494884234271688780572292005832692277220333991379951)
  ))) * X ^ 45

private theorem remainder6Coefficient1AlignedChunk13_pieces :
    remainder6Coefficient1AlignedChunk13 =
      remainder6Coefficient1AlignedChunk13Band4 +
      remainder6Coefficient1AlignedChunk13Band5
    := by
  unfold remainder6Coefficient1AlignedChunk13 remainder6Coefficient1AlignedChunk13Band4
  unfold remainder6Coefficient1AlignedChunk13Band5
  ring

private def remainder6Coefficient1AlignedChunk14Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (1219477313588973843646241530545233572499228465774236050691984357830)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-174346932582108762891968048727212785377842539175139539224841479002)
  ))) * X ^ 34 +
  (Polynomial.C (show ℚ from (
    (22900897877104644196077073265838987871672546090864259256652998994)
  ))) * X ^ 33 +
  (Polynomial.C (show ℚ from (
    (-2756863799354424063565863604580708006505044319002548471425329438)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (303365904414424253444528813714061121114166275681051234455363332)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-30430118864130425748703910565756316113335609827206507214801102)
  ))) * X ^ 30

private def remainder6Coefficient1AlignedChunk14Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (46696581412966801563821061078959037032378265543083741355001841208071)
  ))) * X ^ 37 +
  (Polynomial.C (show ℚ from (
    (-7854971716047596331840317568446269343944541014517362983168032009836)
  ))) * X ^ 36

private theorem remainder6Coefficient1AlignedChunk14_pieces :
    remainder6Coefficient1AlignedChunk14 =
      remainder6Coefficient1AlignedChunk14Band3 +
      remainder6Coefficient1AlignedChunk14Band4
    := by
  unfold remainder6Coefficient1AlignedChunk14 remainder6Coefficient1AlignedChunk14Band3
  unfold remainder6Coefficient1AlignedChunk14Band4
  ring

private def remainder6Coefficient1AlignedChunk15Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1147556166996901742301857460789324836050067004988125662529)
  ))) * X ^ 26 +
  (Polynomial.C (show ℚ from (
    (69059116807592080504075449248445120103923356823058379852)
  ))) * X ^ 25 +
  (Polynomial.C (show ℚ from (
    (-3710719600962041005883293073209742318481852818671524723)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (177254644824833186419455642547377542466564273550239548)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-7492037580113858564025716984583179466893737124276699)
  ))) * X ^ 22

private def remainder6Coefficient1AlignedChunk15Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (2774280384586168834757757415451387202835509943822045435320506)
  ))) * X ^ 29 +
  (Polynomial.C (show ℚ from (
    (-229167447164589387170273929889102413618684761215622480147728)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (17095112018455109258051668393162863828761984749719538924471)
  ))) * X ^ 27

private theorem remainder6Coefficient1AlignedChunk15_pieces :
    remainder6Coefficient1AlignedChunk15 =
      remainder6Coefficient1AlignedChunk15Band2 +
      remainder6Coefficient1AlignedChunk15Band3
    := by
  unfold remainder6Coefficient1AlignedChunk15 remainder6Coefficient1AlignedChunk15Band2
  unfold remainder6Coefficient1AlignedChunk15Band3
  ring

private def remainder6Coefficient1AlignedChunk16Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (132425533854943997858641366080658058464271265)
  ))) * X ^ 17 +
  (Polynomial.C (show ℚ from (
    (-2365296933549129088286913765011294686806132)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (35568751424021237027745312927425496360840)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-445160742552088933159288853832453337332)
  ))) * X ^ 14

private def remainder6Coefficient1AlignedChunk16Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (278772498713203553010397733936946226452121600310440)
  ))) * X ^ 21 +
  (Polynomial.C (show ℚ from (
    (-9080860764762484244413752157954192816831801335856)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (257375873092856585517599096584639078635147703574)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-6304031064275710298920670199834042939195399665)
  ))) * X ^ 18

private theorem remainder6Coefficient1AlignedChunk16_pieces :
    remainder6Coefficient1AlignedChunk16 =
      remainder6Coefficient1AlignedChunk16Band1 +
      remainder6Coefficient1AlignedChunk16Band2
    := by
  unfold remainder6Coefficient1AlignedChunk16 remainder6Coefficient1AlignedChunk16Band1
  unfold remainder6Coefficient1AlignedChunk16Band2
  ring

private def remainder6Coefficient1AlignedChunk17Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-11060624912306014584153124)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (12641698329565160961087)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (14683509676476842482)
  ))) * X ^ 6

private def remainder6Coefficient1AlignedChunk17Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (4573692275562316018834947468906919588)
  ))) * X ^ 13 +
  (Polynomial.C (show ℚ from (
    (-37930404038831438701292987496857940)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (248440952223035694061850285297952)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-1246737004206718197903556045010)
  ))) * X ^ 10 +
  (Polynomial.C (show ℚ from (
    (4566186685707920356612547512)
  ))) * X ^ 9

private theorem remainder6Coefficient1AlignedChunk17_pieces :
    remainder6Coefficient1AlignedChunk17 =
      remainder6Coefficient1AlignedChunk17Band0 +
      remainder6Coefficient1AlignedChunk17Band1
    := by
  unfold remainder6Coefficient1AlignedChunk17 remainder6Coefficient1AlignedChunk17Band0
  unfold remainder6Coefficient1AlignedChunk17Band1
  ring

private def remainder6Coefficient1AlignedChunk18Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-80002118437425346)
  ))) * X ^ 5 +
  (Polynomial.C (show ℚ from (
    (127461111936338)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-100865550084)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (39681278)
  ))) * X ^ 2 +
  (Polynomial.C (show ℚ from (
    (-7256)
  ))) * X ^ 1

private theorem remainder6Coefficient1AlignedChunk18_pieces :
    remainder6Coefficient1AlignedChunk18 =
      remainder6Coefficient1AlignedChunk18Band0
    := by
  unfold remainder6Coefficient1AlignedChunk18 remainder6Coefficient1AlignedChunk18Band0
  ring

private theorem remainder6Coefficient1AlignedBand0_eq :
    remainder6Coefficient1NormalizedBlock0 =
      remainder6Coefficient1AlignedChunk17Band0 +
      remainder6Coefficient1AlignedChunk18Band0
    := by
  unfold remainder6Coefficient1NormalizedBlock0 remainder6Coefficient1AlignedChunk17Band0
  unfold remainder6Coefficient1AlignedChunk18Band0
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand1_eq :
    remainder6Coefficient1NormalizedBlock1 =
      remainder6Coefficient1AlignedChunk16Band1 +
      remainder6Coefficient1AlignedChunk17Band1
    := by
  unfold remainder6Coefficient1NormalizedBlock1 remainder6Coefficient1AlignedChunk16Band1
  unfold remainder6Coefficient1AlignedChunk17Band1
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand2_eq :
    remainder6Coefficient1NormalizedBlock2 =
      remainder6Coefficient1AlignedChunk15Band2 +
      remainder6Coefficient1AlignedChunk16Band2
    := by
  unfold remainder6Coefficient1NormalizedBlock2 remainder6Coefficient1AlignedChunk15Band2
  unfold remainder6Coefficient1AlignedChunk16Band2
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand3_eq :
    remainder6Coefficient1NormalizedBlock3 =
      remainder6Coefficient1AlignedChunk14Band3 +
      remainder6Coefficient1AlignedChunk15Band3
    := by
  unfold remainder6Coefficient1NormalizedBlock3 remainder6Coefficient1AlignedChunk14Band3
  unfold remainder6Coefficient1AlignedChunk15Band3
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand4_eq :
    remainder6Coefficient1NormalizedBlock4 =
      remainder6Coefficient1AlignedChunk13Band4 +
      remainder6Coefficient1AlignedChunk14Band4
    := by
  unfold remainder6Coefficient1NormalizedBlock4 remainder6Coefficient1AlignedChunk13Band4
  unfold remainder6Coefficient1AlignedChunk14Band4
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand5_eq :
    remainder6Coefficient1NormalizedBlock5 =
      remainder6Coefficient1AlignedChunk12Band5 +
      remainder6Coefficient1AlignedChunk13Band5
    := by
  unfold remainder6Coefficient1NormalizedBlock5 remainder6Coefficient1AlignedChunk12Band5
  unfold remainder6Coefficient1AlignedChunk13Band5
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand6_eq :
    remainder6Coefficient1NormalizedBlock6 =
      remainder6Coefficient1AlignedChunk10Band6 +
      remainder6Coefficient1AlignedChunk11Band6
    := by
  unfold remainder6Coefficient1NormalizedBlock6 remainder6Coefficient1AlignedChunk10Band6
  unfold remainder6Coefficient1AlignedChunk11Band6
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand7_eq :
    remainder6Coefficient1NormalizedBlock7 =
      remainder6Coefficient1AlignedChunk9Band7 +
      remainder6Coefficient1AlignedChunk10Band7
    := by
  unfold remainder6Coefficient1NormalizedBlock7 remainder6Coefficient1AlignedChunk9Band7
  unfold remainder6Coefficient1AlignedChunk10Band7
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand8_eq :
    remainder6Coefficient1NormalizedBlock8 =
      remainder6Coefficient1AlignedChunk8Band8 +
      remainder6Coefficient1AlignedChunk9Band8
    := by
  unfold remainder6Coefficient1NormalizedBlock8 remainder6Coefficient1AlignedChunk8Band8
  unfold remainder6Coefficient1AlignedChunk9Band8
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand9_eq :
    remainder6Coefficient1NormalizedBlock9 =
      remainder6Coefficient1AlignedChunk7Band9 +
      remainder6Coefficient1AlignedChunk8Band9
    := by
  unfold remainder6Coefficient1NormalizedBlock9 remainder6Coefficient1AlignedChunk7Band9
  unfold remainder6Coefficient1AlignedChunk8Band9
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand10_eq :
    remainder6Coefficient1NormalizedBlock10 =
      remainder6Coefficient1AlignedChunk6Band10 +
      remainder6Coefficient1AlignedChunk7Band10
    := by
  unfold remainder6Coefficient1NormalizedBlock10 remainder6Coefficient1AlignedChunk6Band10
  unfold remainder6Coefficient1AlignedChunk7Band10
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand11_eq :
    remainder6Coefficient1NormalizedBlock11 =
      remainder6Coefficient1AlignedChunk5Band11 +
      remainder6Coefficient1AlignedChunk6Band11
    := by
  unfold remainder6Coefficient1NormalizedBlock11 remainder6Coefficient1AlignedChunk5Band11
  unfold remainder6Coefficient1AlignedChunk6Band11
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand12_eq :
    remainder6Coefficient1NormalizedBlock12 =
      remainder6Coefficient1AlignedChunk4Band12 +
      remainder6Coefficient1AlignedChunk5Band12
    := by
  unfold remainder6Coefficient1NormalizedBlock12 remainder6Coefficient1AlignedChunk4Band12
  unfold remainder6Coefficient1AlignedChunk5Band12
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand13_eq :
    remainder6Coefficient1NormalizedBlock13 =
      remainder6Coefficient1AlignedChunk3Band13 +
      remainder6Coefficient1AlignedChunk4Band13
    := by
  unfold remainder6Coefficient1NormalizedBlock13 remainder6Coefficient1AlignedChunk3Band13
  unfold remainder6Coefficient1AlignedChunk4Band13
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand14_eq :
    remainder6Coefficient1NormalizedBlock14 =
      remainder6Coefficient1AlignedChunk1Band14 +
      remainder6Coefficient1AlignedChunk2Band14
    := by
  unfold remainder6Coefficient1NormalizedBlock14 remainder6Coefficient1AlignedChunk1Band14
  unfold remainder6Coefficient1AlignedChunk2Band14
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand15_eq :
    remainder6Coefficient1NormalizedBlock15 =
      remainder6Coefficient1AlignedChunk0Band15 +
      remainder6Coefficient1AlignedChunk1Band15
    := by
  unfold remainder6Coefficient1NormalizedBlock15 remainder6Coefficient1AlignedChunk0Band15
  unfold remainder6Coefficient1AlignedChunk1Band15
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1AlignedBand16_eq :
    remainder6Coefficient1NormalizedBlock16 =
      remainder6Coefficient1AlignedChunk0Band16
    := by
  unfold remainder6Coefficient1NormalizedBlock16 remainder6Coefficient1AlignedChunk0Band16
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient1Aligned_eq :
    remainder6Coefficient1Aligned = remainder6Coefficient1Normalized := by
  unfold remainder6Coefficient1Aligned remainder6Coefficient1Normalized
  rw [remainder6Coefficient1AlignedChunk0_pieces]
  rw [remainder6Coefficient1AlignedChunk1_pieces]
  rw [remainder6Coefficient1AlignedChunk2_pieces]
  rw [remainder6Coefficient1AlignedChunk3_pieces]
  rw [remainder6Coefficient1AlignedChunk4_pieces]
  rw [remainder6Coefficient1AlignedChunk5_pieces]
  rw [remainder6Coefficient1AlignedChunk6_pieces]
  rw [remainder6Coefficient1AlignedChunk7_pieces]
  rw [remainder6Coefficient1AlignedChunk8_pieces]
  rw [remainder6Coefficient1AlignedChunk9_pieces]
  rw [remainder6Coefficient1AlignedChunk10_pieces]
  rw [remainder6Coefficient1AlignedChunk11_pieces]
  rw [remainder6Coefficient1AlignedChunk12_pieces]
  rw [remainder6Coefficient1AlignedChunk13_pieces]
  rw [remainder6Coefficient1AlignedChunk14_pieces]
  rw [remainder6Coefficient1AlignedChunk15_pieces]
  rw [remainder6Coefficient1AlignedChunk16_pieces]
  rw [remainder6Coefficient1AlignedChunk17_pieces]
  rw [remainder6Coefficient1AlignedChunk18_pieces]
  rw [remainder6Coefficient1AlignedBand0_eq]
  rw [remainder6Coefficient1AlignedBand1_eq]
  rw [remainder6Coefficient1AlignedBand2_eq]
  rw [remainder6Coefficient1AlignedBand3_eq]
  rw [remainder6Coefficient1AlignedBand4_eq]
  rw [remainder6Coefficient1AlignedBand5_eq]
  rw [remainder6Coefficient1AlignedBand6_eq]
  rw [remainder6Coefficient1AlignedBand7_eq]
  rw [remainder6Coefficient1AlignedBand8_eq]
  rw [remainder6Coefficient1AlignedBand9_eq]
  rw [remainder6Coefficient1AlignedBand10_eq]
  rw [remainder6Coefficient1AlignedBand11_eq]
  rw [remainder6Coefficient1AlignedBand12_eq]
  rw [remainder6Coefficient1AlignedBand13_eq]
  rw [remainder6Coefficient1AlignedBand14_eq]
  rw [remainder6Coefficient1AlignedBand15_eq]
  rw [remainder6Coefficient1AlignedBand16_eq]
  ring

private theorem remainder6Coefficient1_eq_normalized :
    remainder6Coefficient1 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient1Normalized := by
  unfold remainder6Coefficient1 remainder6Coefficient1Block0 remainder6Coefficient1Block1
  rw [remainder6Coefficient1Chunk0_normalized]
  rw [remainder6Coefficient1Chunk1_normalized]
  rw [remainder6Coefficient1Chunk2_normalized]
  rw [remainder6Coefficient1Chunk3_normalized]
  rw [remainder6Coefficient1Chunk4_normalized]
  rw [remainder6Coefficient1Chunk5_normalized]
  rw [remainder6Coefficient1Chunk6_normalized]
  rw [remainder6Coefficient1Chunk7_normalized]
  rw [remainder6Coefficient1Chunk8_normalized]
  rw [remainder6Coefficient1Chunk9_normalized]
  rw [remainder6Coefficient1Chunk10_normalized]
  rw [remainder6Coefficient1Chunk11_normalized]
  rw [remainder6Coefficient1Chunk12_normalized]
  rw [remainder6Coefficient1Chunk13_normalized]
  rw [remainder6Coefficient1Chunk14_normalized]
  rw [remainder6Coefficient1Chunk15_normalized]
  rw [remainder6Coefficient1Chunk16_normalized]
  rw [remainder6Coefficient1Chunk17_normalized]
  rw [remainder6Coefficient1Chunk18_normalized]
  rw [← remainder6Coefficient1Aligned_eq]
  unfold remainder6Coefficient1Aligned
  ring

private def remainder6Coefficient2AlignedChunk0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-315940498887)
  ))) * X ^ 145 +
  (Polynomial.C (show ℚ from (
    (-4546261986553142511)
  ))) * X ^ 144 +
  (Polynomial.C (show ℚ from (
    (-2461177433625470012366301)
  ))) * X ^ 143 +
  (Polynomial.C (show ℚ from (
    (-108446004021335705563995602593)
  ))) * X ^ 142 +
  (Polynomial.C (show ℚ from (
    (-679622836647796301925103373653272)
  ))) * X ^ 141 +
  (Polynomial.C (show ℚ from (
    (-781997401037853628110156674924513602)
  ))) * X ^ 140 +
  (Polynomial.C (show ℚ from (
    (-51222721668122847810043521100620447938)
  ))) * X ^ 139 +
  (Polynomial.C (show ℚ from (
    (187346906381980229194703126609479794476830)
  ))) * X ^ 138

private theorem remainder6Coefficient2Chunk0_normalized :
    remainder6Coefficient2Chunk0 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk0 := by
  unfold remainder6Coefficient2Chunk0 remainder6Coefficient2AlignedChunk0
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (75554646756090902505803659677007006176780048)
  ))) * X ^ 137 +
  (Polynomial.C (show ℚ from (
    (11083058231813325753534541998899310552463098843)
  ))) * X ^ 136 +
  (Polynomial.C (show ℚ from (
    (591008386365947537000114344954823635360971745906)
  ))) * X ^ 135 +
  (Polynomial.C (show ℚ from (
    (4331405697715076878606821875174121432228690553959)
  ))) * X ^ 134 +
  (Polynomial.C (show ℚ from (
    (-184173494402039652927556577787312030154064443690921)
  ))) * X ^ 133 +
  (Polynomial.C (show ℚ from (
    (533503248610561927308547472040764598809311788260629)
  ))) * X ^ 132 +
  (Polynomial.C (show ℚ from (
    (16492777912746110872253767570361497450564016602383889)
  ))) * X ^ 131 +
  (Polynomial.C (show ℚ from (
    (-195594830294760904912883832037913859582322201300968410)
  ))) * X ^ 130

private theorem remainder6Coefficient2Chunk1_normalized :
    remainder6Coefficient2Chunk1 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk1 := by
  unfold remainder6Coefficient2Chunk1 remainder6Coefficient2AlignedChunk1
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (861568319493486277313581758166988781134493166589879363)
  ))) * X ^ 129 +
  (Polynomial.C (show ℚ from (
    (323528728657827882997252662855770962975995612972083350)
  ))) * X ^ 128 +
  (Polynomial.C (show ℚ from (
    (-25483034877747311987278361252673057010092628005243118701)
  ))) * X ^ 127 +
  (Polynomial.C (show ℚ from (
    (155684269321619547732468191234796906329716308101652097255)
  ))) * X ^ 126 +
  (Polynomial.C (show ℚ from (
    (-476000959642518193691194899440321029398768605889796046632)
  ))) * X ^ 125 +
  (Polynomial.C (show ℚ from (
    (324088692659975022719056641484161964385641286947987974525)
  ))) * X ^ 124 +
  (Polynomial.C (show ℚ from (
    (4882484666422195286022942314032170123073413014156033421842)
  ))) * X ^ 123 +
  (Polynomial.C (show ℚ from (
    (-33892399271717625504990669656689046133811256075925855627505)
  ))) * X ^ 122

private theorem remainder6Coefficient2Chunk2_normalized :
    remainder6Coefficient2Chunk2 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk2 := by
  unfold remainder6Coefficient2Chunk2 remainder6Coefficient2AlignedChunk2
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (156955995605037260008826373638773287299386205296625576137480)
  ))) * X ^ 121 +
  (Polynomial.C (show ℚ from (
    (-667454621193513040472930650973150052062507424938546363984603)
  ))) * X ^ 120 +
  (Polynomial.C (show ℚ from (
    (2902231953813294269257723383065309943415760342747389261453518)
  ))) * X ^ 119 +
  (Polynomial.C (show ℚ from (
    (-12842189377860157420475819125854223848043326262653085184513954)
  ))) * X ^ 118 +
  (Polynomial.C (show ℚ from (
    (55337461318206169427991435619705519513791299960550277448332040)
  ))) * X ^ 117 +
  (Polynomial.C (show ℚ from (
    (-225116790240450019253437471817001522749965274226119911148709071)
  ))) * X ^ 116 +
  (Polynomial.C (show ℚ from (
    (854247556660789637063204143460183268851029218501962502844716050)
  ))) * X ^ 115 +
  (Polynomial.C (show ℚ from (
    (-3017820519501414118979390700298643824719871727421466764431652761)
  ))) * X ^ 114

private theorem remainder6Coefficient2Chunk3_normalized :
    remainder6Coefficient2Chunk3 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk3 := by
  unfold remainder6Coefficient2Chunk3 remainder6Coefficient2AlignedChunk3
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (9941138365525315152460231980761724687042321112559789013783990483)
  ))) * X ^ 113 +
  (Polynomial.C (show ℚ from (
    (-30611049352049747174288255916170790582375922413099782945674908933)
  ))) * X ^ 112 +
  (Polynomial.C (show ℚ from (
    (88341769269098873646246177622815759794873943768880528264728932084)
  ))) * X ^ 111 +
  (Polynomial.C (show ℚ from (
    (-239687225839803095964234683858511192865317528750830970591142136266)
  ))) * X ^ 110 +
  (Polynomial.C (show ℚ from (
    (613907926807779137977175922695974937659896561790087831945649856214)
  ))) * X ^ 109 +
  (Polynomial.C (show ℚ from (
    (-1492387759583358590386188782019477671298160995931872813895358122239)
  ))) * X ^ 108 +
  (Polynomial.C (show ℚ from (
    (3463341911687113218033152743936869691101937426647141264887846855107)
  ))) * X ^ 107 +
  (Polynomial.C (show ℚ from (
    (-7698641985646935195079739978106428239633764916984276272068174170149)
  ))) * X ^ 106

private theorem remainder6Coefficient2Chunk4_normalized :
    remainder6Coefficient2Chunk4 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk4 := by
  unfold remainder6Coefficient2Chunk4 remainder6Coefficient2AlignedChunk4
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (16328026263217025364926310372318107168234568138178910588114092993850)
  ))) * X ^ 105 +
  (Polynomial.C (show ℚ from (
    (-32467338422691874874010847322591943856934239447269368175295467391668)
  ))) * X ^ 104 +
  (Polynomial.C (show ℚ from (
    (58147785621425925683947656961169717573141616918159838155382090441528)
  ))) * X ^ 103 +
  (Polynomial.C (show ℚ from (
    (-85750182884605883896009055211771807732494622146578579745434189102691)
  ))) * X ^ 102 +
  (Polynomial.C (show ℚ from (
    (76153292683654570027564573922069393111938251628575806345614229896770)
  ))) * X ^ 101 +
  (Polynomial.C (show ℚ from (
    (76973016944077055984976897757854942749547457638069850579673058183832)
  ))) * X ^ 100 +
  (Polynomial.C (show ℚ from (
    (-560213934976663414978907941119988428069349063298299953694111138970854)
  ))) * X ^ 99 +
  (Polynomial.C (show ℚ from (
    (1487241384429296246696038225936419695519235592122859474472320612921002)
  ))) * X ^ 98

private theorem remainder6Coefficient2Chunk5_normalized :
    remainder6Coefficient2Chunk5 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk5 := by
  unfold remainder6Coefficient2Chunk5 remainder6Coefficient2AlignedChunk5
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-2220269855050717808326966892800118966461589840112900617253334441222671)
  ))) * X ^ 97 +
  (Polynomial.C (show ℚ from (
    (-495869070092099641915349928922168288575164704499595254492954208327568)
  ))) * X ^ 96 +
  (Polynomial.C (show ℚ from (
    (16450152573856272387602165629460215596539851426757448495407429891942018)
  ))) * X ^ 95 +
  (Polynomial.C (show ℚ from (
    (-68433066731608761332151397480507741270876208164133060229712850018568164)
  ))) * X ^ 94 +
  (Polynomial.C (show ℚ from (
    (200136743417203466127334624978217097053950573006438870897819104415145047)
  ))) * X ^ 93 +
  (Polynomial.C (show ℚ from (
    (-480956459637295324109250327805953128650527621201512889047877740050288996)
  ))) * X ^ 92 +
  (Polynomial.C (show ℚ from (
    (998415945677749997639863635497783625642074473958794969581875682915641887)
  ))) * X ^ 91 +
  (Polynomial.C (show ℚ from (
    (-1825283987394403183884872310673072778685610687146927466659745189705127416)
  ))) * X ^ 90

private theorem remainder6Coefficient2Chunk6_normalized :
    remainder6Coefficient2Chunk6 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk6 := by
  unfold remainder6Coefficient2Chunk6 remainder6Coefficient2AlignedChunk6
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (2950491940447942140683992315334703316536083324643928795604318672950054368)
  ))) * X ^ 89 +
  (Polynomial.C (show ℚ from (
    (-4175765985388794432504656581484234535746304996690838243731278970162782513)
  ))) * X ^ 88 +
  (Polynomial.C (show ℚ from (
    (5004971590320248884444499447598341324018933932496148922329168908181607965)
  ))) * X ^ 87 +
  (Polynomial.C (show ℚ from (
    (-4584043912235803898008078956160506560023475113036811842445110238847670521)
  ))) * X ^ 86 +
  (Polynomial.C (show ℚ from (
    (1770891393350891870186191864565556017000328190282521112358949835688384152)
  ))) * X ^ 85 +
  (Polynomial.C (show ℚ from (
    (4589664670545191450873431699137664140769364216555794468410806049205706641)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (-15143919020181494216803740374423506366019157086434133427155517853363743887)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (29255683232251168203546379794185426658245505766998288030485726460522711783)
  ))) * X ^ 82

private theorem remainder6Coefficient2Chunk7_normalized :
    remainder6Coefficient2Chunk7 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk7 := by
  unfold remainder6Coefficient2Chunk7 remainder6Coefficient2AlignedChunk7
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-43968518932560674349333910310572830855198132345908480291712859680761145307)
  ))) * X ^ 81 +
  (Polynomial.C (show ℚ from (
    (52592014038040954003608254688107041146295446128908741878873888305215715229)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    (-42619020380078390045819363755105148219805220934440147514267642092666631148)
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    (-7469556728112728725583485882770756593674562588566738924510467412024134139)
  ))) * X ^ 78 +
  (Polynomial.C (show ℚ from (
    (132853107833967934326103755267337125216460561350639073810705259135347337857)
  ))) * X ^ 77 +
  (Polynomial.C (show ℚ from (
    (-388201367839280427496471342738371531989009666953097516787830518430691395936)
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    (853167342105014044078973953975308899665692045132777983805033284208897376507)
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    (-1634359348729489030969588443518164653677146083727512516502833661070409296878)
  ))) * X ^ 74

private theorem remainder6Coefficient2Chunk8_normalized :
    remainder6Coefficient2Chunk8 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk8 := by
  unfold remainder6Coefficient2Chunk8 remainder6Coefficient2AlignedChunk8
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (2859238233819039389913178039209596898909553016190601118377305297208156819561)
  ))) * X ^ 73 +
  (Polynomial.C (show ℚ from (
    (-4657442894716196302657454051225033621427287388144250440198514632378232453960)
  ))) * X ^ 72 +
  (Polynomial.C (show ℚ from (
    (7127645942880844599409401305160067789519433704582581116148394750134666963171)
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    (-10293507352399904282059322437428419604148188605194679171943904769462898729333)
  ))) * X ^ 70 +
  (Polynomial.C (show ℚ from (
    (14059393426463223593946685355881517519492524745381709284215536828663355312756)
  ))) * X ^ 69 +
  (Polynomial.C (show ℚ from (
    (-18182286858062303297531215528681962920312875927551206358193759174834869303099)
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    (22276946618089426743022302029602904238112159287537176023224590353675742996271)
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    (-25864283673987277749290170335716698911724476290632260662688609329163680026745)
  ))) * X ^ 66

private theorem remainder6Coefficient2Chunk9_normalized :
    remainder6Coefficient2Chunk9 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk9 := by
  unfold remainder6Coefficient2Chunk9 remainder6Coefficient2AlignedChunk9
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (28458822259403448889074882196128810791341505266416173864177944440580777910068)
  ))) * X ^ 65 +
  (Polynomial.C (show ℚ from (
    (-29674867557679708289501470268489174245505588238427534941011092212695608481365)
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    (29319980919626898249757570126203368952748775669186620640859415396292356902696)
  ))) * X ^ 63 +
  (Polynomial.C (show ℚ from (
    (-27444825910053106174479504451124321216424730876989066265821741605865438145137)
  ))) * X ^ 62 +
  (Polynomial.C (show ℚ from (
    (24331738207822110104164850114798909252323725290252525291505755297054919685905)
  ))) * X ^ 61 +
  (Polynomial.C (show ℚ from (
    (-20425500377864597864614178964109596003719179330282793286198023975018841536826)
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    (16229621549011680347638872947077081162324862855567208237257559283324442725894)
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    (-12201354402513224268443248908035922952801640966348517011976295820834004496272)
  ))) * X ^ 58

private theorem remainder6Coefficient2Chunk10_normalized :
    remainder6Coefficient2Chunk10 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk10 := by
  unfold remainder6Coefficient2Chunk10 remainder6Coefficient2AlignedChunk10
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (8675175704502810005056451020992564158793676595192802876134472101780120505581)
  ))) * X ^ 57 +
  (Polynomial.C (show ℚ from (
    (-5830481717436139188317407431750895890290170664608816231867081357236807638081)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (3702118370506027212413184046033707581927114714099211294382890382098601865447)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (-2219513121535030164270397780679264356970392489509421053042722075040153528177)
  ))) * X ^ 54 +
  (Polynomial.C (show ℚ from (
    (1255584941527704452746120684107279804519088262460645735236845129919743970239)
  ))) * X ^ 53 +
  (Polynomial.C (show ℚ from (
    (-669748603999325958464597097086970924093349062038484944347254406246608352273)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (336610382954046870247800430609973056814614100156783614251088171941839303403)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (-159272680085665554005412039868340008540313742102294464018272462502083319687)
  ))) * X ^ 50

private theorem remainder6Coefficient2Chunk11_normalized :
    remainder6Coefficient2Chunk11 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk11 := by
  unfold remainder6Coefficient2Chunk11 remainder6Coefficient2AlignedChunk11
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (70888517113836029101576065940369409531584445615282962939146396016145781328)
  ))) * X ^ 49 +
  (Polynomial.C (show ℚ from (
    (-29650206849699537964032698507245513296851606331347863252387776115847583316)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (11643025766926562122844406228154118105804936001207007154181082690380887666)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-4287764319632802774818404967705164533580476016140897841109412721486110451)
  ))) * X ^ 46 +
  (Polynomial.C (show ℚ from (
    (1479223768525695267592548312069830549695338278071574379291993015701877127)
  ))) * X ^ 45 +
  (Polynomial.C (show ℚ from (
    (-477479700939294940512691747416735765410275055349521383765613870503638413)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (144026353634990108295950572197513651797712126200702663275366921671474518)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-40542392880417114577827595217658727606296695805101361776225317999217069)
  ))) * X ^ 42

private theorem remainder6Coefficient2Chunk12_normalized :
    remainder6Coefficient2Chunk12 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk12 := by
  unfold remainder6Coefficient2Chunk12 remainder6Coefficient2AlignedChunk12
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (10634972873675307031983824481469065295138060418731329479412671695351331)
  ))) * X ^ 41 +
  (Polynomial.C (show ℚ from (
    (-2595765894942786989133718632757646669187271864081570841784158142739798)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (588573769496079445172517403154243371285995384632417134578830221752204)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-123767440340893257820464894377312306375992236174199351256584600826497)
  ))) * X ^ 38 +
  (Polynomial.C (show ℚ from (
    (24093711764446404639083968795437264738722231948853016334347723344608)
  ))) * X ^ 37 +
  (Polynomial.C (show ℚ from (
    (-4333812672091614152071693198914448727981015618394225383520385030545)
  ))) * X ^ 36 +
  (Polynomial.C (show ℚ from (
    (718846789678887512634375406703198906074033426219391471364325124452)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-109719477140794198875804753073087276758841812036497929336081139014)
  ))) * X ^ 34

private theorem remainder6Coefficient2Chunk13_normalized :
    remainder6Coefficient2Chunk13 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk13 := by
  unfold remainder6Coefficient2Chunk13 remainder6Coefficient2AlignedChunk13
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (15375938023292737443314781690066611953593395774740798451247935996)
  ))) * X ^ 33 +
  (Polynomial.C (show ℚ from (
    (-1973712993822071474949706404738701900439752945304094416663486397)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (231486617206828337106932024113874406982323652912997734728976640)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-24741106940614472916780882365929799271623350295582017599970463)
  ))) * X ^ 30 +
  (Polynomial.C (show ℚ from (
    (2402965298590593182281477972401731407270671244975704494283858)
  ))) * X ^ 29 +
  (Polynomial.C (show ℚ from (
    (-211456483156951782480574431898617407886197741043647614921858)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (16806182195916905765842794014671909484794622698826126455197)
  ))) * X ^ 27 +
  (Polynomial.C (show ℚ from (
    (-1202354195785995779654082890523225913149444782850165542138)
  ))) * X ^ 26

private theorem remainder6Coefficient2Chunk14_normalized :
    remainder6Coefficient2Chunk14 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk14 := by
  unfold remainder6Coefficient2Chunk14 remainder6Coefficient2AlignedChunk14
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (77153095304890737077668942243599703935246104175737125136)
  ))) * X ^ 25 +
  (Polynomial.C (show ℚ from (
    (-4423477744390859918217499644647603281157049011995581072)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (225668609643543268674369015601646240443689114451262043)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-10198589028139998496331355912344511811566429595809490)
  ))) * X ^ 22 +
  (Polynomial.C (show ℚ from (
    (406322822601229085427412664995322862376622971469458)
  ))) * X ^ 21 +
  (Polynomial.C (show ℚ from (
    (-14196253238687956318636993602484934021750025160256)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (432445741976415113013625151760023859974380847594)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-11411972561018474511482830968748711674910782454)
  ))) * X ^ 18

private theorem remainder6Coefficient2Chunk15_normalized :
    remainder6Coefficient2Chunk15 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk15 := by
  unfold remainder6Coefficient2Chunk15 remainder6Coefficient2AlignedChunk15
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk16 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (259032095835806047471680291963523258316846281)
  ))) * X ^ 17 +
  (Polynomial.C (show ℚ from (
    (-5016571911267970568378770056010879664388722)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (82134255318488324259813898544644342782820)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-1124806688485678268671566174938350959972)
  ))) * X ^ 14 +
  (Polynomial.C (show ℚ from (
    (12723539027204902930750785028377793824)
  ))) * X ^ 13 +
  (Polynomial.C (show ℚ from (
    (-117085969791173174953432256005946158)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (859911591767474862236853619189470)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-4912615674644929106442104887993)
  ))) * X ^ 10

private theorem remainder6Coefficient2Chunk16_normalized :
    remainder6Coefficient2Chunk16 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk16 := by
  unfold remainder6Coefficient2Chunk16 remainder6Coefficient2AlignedChunk16
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk17 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (21010651248469401769408684890)
  ))) * X ^ 9 +
  (Polynomial.C (show ℚ from (
    (-62791036209878831071617902)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (110032602948153855002974)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (-23402482118936566492)
  ))) * X ^ 6 +
  (Polynomial.C (show ℚ from (
    (-380092333559739692)
  ))) * X ^ 5 +
  (Polynomial.C (show ℚ from (
    (895631651061428)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-952873933548)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (615854540)
  ))) * X ^ 2

private theorem remainder6Coefficient2Chunk17_normalized :
    remainder6Coefficient2Chunk17 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk17 := by
  unfold remainder6Coefficient2Chunk17 remainder6Coefficient2AlignedChunk17
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2AlignedChunk18 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (50452)
  ))) * X ^ 1 +
  (Polynomial.C (show ℚ from (
    (64)
  ))) * X ^ 0

private theorem remainder6Coefficient2Chunk18_normalized :
    remainder6Coefficient2Chunk18 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2AlignedChunk18 := by
  unfold remainder6Coefficient2Chunk18 remainder6Coefficient2AlignedChunk18
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder6Coefficient2Aligned : Coefficient :=
  remainder6Coefficient2AlignedChunk0 +
  remainder6Coefficient2AlignedChunk1 +
  remainder6Coefficient2AlignedChunk2 +
  remainder6Coefficient2AlignedChunk3 +
  remainder6Coefficient2AlignedChunk4 +
  remainder6Coefficient2AlignedChunk5 +
  remainder6Coefficient2AlignedChunk6 +
  remainder6Coefficient2AlignedChunk7 +
  remainder6Coefficient2AlignedChunk8 +
  remainder6Coefficient2AlignedChunk9 +
  remainder6Coefficient2AlignedChunk10 +
  remainder6Coefficient2AlignedChunk11 +
  remainder6Coefficient2AlignedChunk12 +
  remainder6Coefficient2AlignedChunk13 +
  remainder6Coefficient2AlignedChunk14 +
  remainder6Coefficient2AlignedChunk15 +
  remainder6Coefficient2AlignedChunk16 +
  remainder6Coefficient2AlignedChunk17 +
  remainder6Coefficient2AlignedChunk18

private def remainder6Coefficient2AlignedChunk0Band15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-2461177433625470012366301)
  ))) * X ^ 143 +
  (Polynomial.C (show ℚ from (
    (-108446004021335705563995602593)
  ))) * X ^ 142 +
  (Polynomial.C (show ℚ from (
    (-679622836647796301925103373653272)
  ))) * X ^ 141 +
  (Polynomial.C (show ℚ from (
    (-781997401037853628110156674924513602)
  ))) * X ^ 140 +
  (Polynomial.C (show ℚ from (
    (-51222721668122847810043521100620447938)
  ))) * X ^ 139 +
  (Polynomial.C (show ℚ from (
    (187346906381980229194703126609479794476830)
  ))) * X ^ 138

private def remainder6Coefficient2AlignedChunk0Band16 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-315940498887)
  ))) * X ^ 145 +
  (Polynomial.C (show ℚ from (
    (-4546261986553142511)
  ))) * X ^ 144

private theorem remainder6Coefficient2AlignedChunk0_pieces :
    remainder6Coefficient2AlignedChunk0 =
      remainder6Coefficient2AlignedChunk0Band15 +
      remainder6Coefficient2AlignedChunk0Band16
    := by
  unfold remainder6Coefficient2AlignedChunk0 remainder6Coefficient2AlignedChunk0Band15
  unfold remainder6Coefficient2AlignedChunk0Band16
  ring

private def remainder6Coefficient2AlignedChunk1Band14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (4331405697715076878606821875174121432228690553959)
  ))) * X ^ 134 +
  (Polynomial.C (show ℚ from (
    (-184173494402039652927556577787312030154064443690921)
  ))) * X ^ 133 +
  (Polynomial.C (show ℚ from (
    (533503248610561927308547472040764598809311788260629)
  ))) * X ^ 132 +
  (Polynomial.C (show ℚ from (
    (16492777912746110872253767570361497450564016602383889)
  ))) * X ^ 131 +
  (Polynomial.C (show ℚ from (
    (-195594830294760904912883832037913859582322201300968410)
  ))) * X ^ 130

private def remainder6Coefficient2AlignedChunk1Band15 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (75554646756090902505803659677007006176780048)
  ))) * X ^ 137 +
  (Polynomial.C (show ℚ from (
    (11083058231813325753534541998899310552463098843)
  ))) * X ^ 136 +
  (Polynomial.C (show ℚ from (
    (591008386365947537000114344954823635360971745906)
  ))) * X ^ 135

private theorem remainder6Coefficient2AlignedChunk1_pieces :
    remainder6Coefficient2AlignedChunk1 =
      remainder6Coefficient2AlignedChunk1Band14 +
      remainder6Coefficient2AlignedChunk1Band15
    := by
  unfold remainder6Coefficient2AlignedChunk1 remainder6Coefficient2AlignedChunk1Band14
  unfold remainder6Coefficient2AlignedChunk1Band15
  ring

private def remainder6Coefficient2AlignedChunk2Band13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-476000959642518193691194899440321029398768605889796046632)
  ))) * X ^ 125 +
  (Polynomial.C (show ℚ from (
    (324088692659975022719056641484161964385641286947987974525)
  ))) * X ^ 124 +
  (Polynomial.C (show ℚ from (
    (4882484666422195286022942314032170123073413014156033421842)
  ))) * X ^ 123 +
  (Polynomial.C (show ℚ from (
    (-33892399271717625504990669656689046133811256075925855627505)
  ))) * X ^ 122

private def remainder6Coefficient2AlignedChunk2Band14 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (861568319493486277313581758166988781134493166589879363)
  ))) * X ^ 129 +
  (Polynomial.C (show ℚ from (
    (323528728657827882997252662855770962975995612972083350)
  ))) * X ^ 128 +
  (Polynomial.C (show ℚ from (
    (-25483034877747311987278361252673057010092628005243118701)
  ))) * X ^ 127 +
  (Polynomial.C (show ℚ from (
    (155684269321619547732468191234796906329716308101652097255)
  ))) * X ^ 126

private theorem remainder6Coefficient2AlignedChunk2_pieces :
    remainder6Coefficient2AlignedChunk2 =
      remainder6Coefficient2AlignedChunk2Band13 +
      remainder6Coefficient2AlignedChunk2Band14
    := by
  unfold remainder6Coefficient2AlignedChunk2 remainder6Coefficient2AlignedChunk2Band13
  unfold remainder6Coefficient2AlignedChunk2Band14
  ring

private def remainder6Coefficient2AlignedChunk3Band12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-225116790240450019253437471817001522749965274226119911148709071)
  ))) * X ^ 116 +
  (Polynomial.C (show ℚ from (
    (854247556660789637063204143460183268851029218501962502844716050)
  ))) * X ^ 115 +
  (Polynomial.C (show ℚ from (
    (-3017820519501414118979390700298643824719871727421466764431652761)
  ))) * X ^ 114

private def remainder6Coefficient2AlignedChunk3Band13 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (156955995605037260008826373638773287299386205296625576137480)
  ))) * X ^ 121 +
  (Polynomial.C (show ℚ from (
    (-667454621193513040472930650973150052062507424938546363984603)
  ))) * X ^ 120 +
  (Polynomial.C (show ℚ from (
    (2902231953813294269257723383065309943415760342747389261453518)
  ))) * X ^ 119 +
  (Polynomial.C (show ℚ from (
    (-12842189377860157420475819125854223848043326262653085184513954)
  ))) * X ^ 118 +
  (Polynomial.C (show ℚ from (
    (55337461318206169427991435619705519513791299960550277448332040)
  ))) * X ^ 117

private theorem remainder6Coefficient2AlignedChunk3_pieces :
    remainder6Coefficient2AlignedChunk3 =
      remainder6Coefficient2AlignedChunk3Band12 +
      remainder6Coefficient2AlignedChunk3Band13
    := by
  unfold remainder6Coefficient2AlignedChunk3 remainder6Coefficient2AlignedChunk3Band12
  unfold remainder6Coefficient2AlignedChunk3Band13
  ring

private def remainder6Coefficient2AlignedChunk4Band11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (3463341911687113218033152743936869691101937426647141264887846855107)
  ))) * X ^ 107 +
  (Polynomial.C (show ℚ from (
    (-7698641985646935195079739978106428239633764916984276272068174170149)
  ))) * X ^ 106

private def remainder6Coefficient2AlignedChunk4Band12 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (9941138365525315152460231980761724687042321112559789013783990483)
  ))) * X ^ 113 +
  (Polynomial.C (show ℚ from (
    (-30611049352049747174288255916170790582375922413099782945674908933)
  ))) * X ^ 112 +
  (Polynomial.C (show ℚ from (
    (88341769269098873646246177622815759794873943768880528264728932084)
  ))) * X ^ 111 +
  (Polynomial.C (show ℚ from (
    (-239687225839803095964234683858511192865317528750830970591142136266)
  ))) * X ^ 110 +
  (Polynomial.C (show ℚ from (
    (613907926807779137977175922695974937659896561790087831945649856214)
  ))) * X ^ 109 +
  (Polynomial.C (show ℚ from (
    (-1492387759583358590386188782019477671298160995931872813895358122239)
  ))) * X ^ 108

private theorem remainder6Coefficient2AlignedChunk4_pieces :
    remainder6Coefficient2AlignedChunk4 =
      remainder6Coefficient2AlignedChunk4Band11 +
      remainder6Coefficient2AlignedChunk4Band12
    := by
  unfold remainder6Coefficient2AlignedChunk4 remainder6Coefficient2AlignedChunk4Band11
  unfold remainder6Coefficient2AlignedChunk4Band12
  ring

private def remainder6Coefficient2AlignedChunk5Band10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (1487241384429296246696038225936419695519235592122859474472320612921002)
  ))) * X ^ 98

private def remainder6Coefficient2AlignedChunk5Band11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (16328026263217025364926310372318107168234568138178910588114092993850)
  ))) * X ^ 105 +
  (Polynomial.C (show ℚ from (
    (-32467338422691874874010847322591943856934239447269368175295467391668)
  ))) * X ^ 104 +
  (Polynomial.C (show ℚ from (
    (58147785621425925683947656961169717573141616918159838155382090441528)
  ))) * X ^ 103 +
  (Polynomial.C (show ℚ from (
    (-85750182884605883896009055211771807732494622146578579745434189102691)
  ))) * X ^ 102 +
  (Polynomial.C (show ℚ from (
    (76153292683654570027564573922069393111938251628575806345614229896770)
  ))) * X ^ 101 +
  (Polynomial.C (show ℚ from (
    (76973016944077055984976897757854942749547457638069850579673058183832)
  ))) * X ^ 100 +
  (Polynomial.C (show ℚ from (
    (-560213934976663414978907941119988428069349063298299953694111138970854)
  ))) * X ^ 99

private theorem remainder6Coefficient2AlignedChunk5_pieces :
    remainder6Coefficient2AlignedChunk5 =
      remainder6Coefficient2AlignedChunk5Band10 +
      remainder6Coefficient2AlignedChunk5Band11
    := by
  unfold remainder6Coefficient2AlignedChunk5 remainder6Coefficient2AlignedChunk5Band10
  unfold remainder6Coefficient2AlignedChunk5Band11
  ring

private def remainder6Coefficient2AlignedChunk6Band10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-2220269855050717808326966892800118966461589840112900617253334441222671)
  ))) * X ^ 97 +
  (Polynomial.C (show ℚ from (
    (-495869070092099641915349928922168288575164704499595254492954208327568)
  ))) * X ^ 96 +
  (Polynomial.C (show ℚ from (
    (16450152573856272387602165629460215596539851426757448495407429891942018)
  ))) * X ^ 95 +
  (Polynomial.C (show ℚ from (
    (-68433066731608761332151397480507741270876208164133060229712850018568164)
  ))) * X ^ 94 +
  (Polynomial.C (show ℚ from (
    (200136743417203466127334624978217097053950573006438870897819104415145047)
  ))) * X ^ 93 +
  (Polynomial.C (show ℚ from (
    (-480956459637295324109250327805953128650527621201512889047877740050288996)
  ))) * X ^ 92 +
  (Polynomial.C (show ℚ from (
    (998415945677749997639863635497783625642074473958794969581875682915641887)
  ))) * X ^ 91 +
  (Polynomial.C (show ℚ from (
    (-1825283987394403183884872310673072778685610687146927466659745189705127416)
  ))) * X ^ 90

private theorem remainder6Coefficient2AlignedChunk6_pieces :
    remainder6Coefficient2AlignedChunk6 =
      remainder6Coefficient2AlignedChunk6Band10
    := by
  unfold remainder6Coefficient2AlignedChunk6 remainder6Coefficient2AlignedChunk6Band10
  ring

private def remainder6Coefficient2AlignedChunk7Band9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (2950491940447942140683992315334703316536083324643928795604318672950054368)
  ))) * X ^ 89 +
  (Polynomial.C (show ℚ from (
    (-4175765985388794432504656581484234535746304996690838243731278970162782513)
  ))) * X ^ 88 +
  (Polynomial.C (show ℚ from (
    (5004971590320248884444499447598341324018933932496148922329168908181607965)
  ))) * X ^ 87 +
  (Polynomial.C (show ℚ from (
    (-4584043912235803898008078956160506560023475113036811842445110238847670521)
  ))) * X ^ 86 +
  (Polynomial.C (show ℚ from (
    (1770891393350891870186191864565556017000328190282521112358949835688384152)
  ))) * X ^ 85 +
  (Polynomial.C (show ℚ from (
    (4589664670545191450873431699137664140769364216555794468410806049205706641)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (-15143919020181494216803740374423506366019157086434133427155517853363743887)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (29255683232251168203546379794185426658245505766998288030485726460522711783)
  ))) * X ^ 82

private theorem remainder6Coefficient2AlignedChunk7_pieces :
    remainder6Coefficient2AlignedChunk7 =
      remainder6Coefficient2AlignedChunk7Band9
    := by
  unfold remainder6Coefficient2AlignedChunk7 remainder6Coefficient2AlignedChunk7Band9
  ring

private def remainder6Coefficient2AlignedChunk8Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (52592014038040954003608254688107041146295446128908741878873888305215715229)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    (-42619020380078390045819363755105148219805220934440147514267642092666631148)
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    (-7469556728112728725583485882770756593674562588566738924510467412024134139)
  ))) * X ^ 78 +
  (Polynomial.C (show ℚ from (
    (132853107833967934326103755267337125216460561350639073810705259135347337857)
  ))) * X ^ 77 +
  (Polynomial.C (show ℚ from (
    (-388201367839280427496471342738371531989009666953097516787830518430691395936)
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    (853167342105014044078973953975308899665692045132777983805033284208897376507)
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    (-1634359348729489030969588443518164653677146083727512516502833661070409296878)
  ))) * X ^ 74

private def remainder6Coefficient2AlignedChunk8Band9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-43968518932560674349333910310572830855198132345908480291712859680761145307)
  ))) * X ^ 81

private theorem remainder6Coefficient2AlignedChunk8_pieces :
    remainder6Coefficient2AlignedChunk8 =
      remainder6Coefficient2AlignedChunk8Band8 +
      remainder6Coefficient2AlignedChunk8Band9
    := by
  unfold remainder6Coefficient2AlignedChunk8 remainder6Coefficient2AlignedChunk8Band8
  unfold remainder6Coefficient2AlignedChunk8Band9
  ring

private def remainder6Coefficient2AlignedChunk9Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (7127645942880844599409401305160067789519433704582581116148394750134666963171)
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    (-10293507352399904282059322437428419604148188605194679171943904769462898729333)
  ))) * X ^ 70 +
  (Polynomial.C (show ℚ from (
    (14059393426463223593946685355881517519492524745381709284215536828663355312756)
  ))) * X ^ 69 +
  (Polynomial.C (show ℚ from (
    (-18182286858062303297531215528681962920312875927551206358193759174834869303099)
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    (22276946618089426743022302029602904238112159287537176023224590353675742996271)
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    (-25864283673987277749290170335716698911724476290632260662688609329163680026745)
  ))) * X ^ 66

private def remainder6Coefficient2AlignedChunk9Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (2859238233819039389913178039209596898909553016190601118377305297208156819561)
  ))) * X ^ 73 +
  (Polynomial.C (show ℚ from (
    (-4657442894716196302657454051225033621427287388144250440198514632378232453960)
  ))) * X ^ 72

private theorem remainder6Coefficient2AlignedChunk9_pieces :
    remainder6Coefficient2AlignedChunk9 =
      remainder6Coefficient2AlignedChunk9Band7 +
      remainder6Coefficient2AlignedChunk9Band8
    := by
  unfold remainder6Coefficient2AlignedChunk9 remainder6Coefficient2AlignedChunk9Band7
  unfold remainder6Coefficient2AlignedChunk9Band8
  ring

private def remainder6Coefficient2AlignedChunk10Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-27444825910053106174479504451124321216424730876989066265821741605865438145137)
  ))) * X ^ 62 +
  (Polynomial.C (show ℚ from (
    (24331738207822110104164850114798909252323725290252525291505755297054919685905)
  ))) * X ^ 61 +
  (Polynomial.C (show ℚ from (
    (-20425500377864597864614178964109596003719179330282793286198023975018841536826)
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    (16229621549011680347638872947077081162324862855567208237257559283324442725894)
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    (-12201354402513224268443248908035922952801640966348517011976295820834004496272)
  ))) * X ^ 58

private def remainder6Coefficient2AlignedChunk10Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (28458822259403448889074882196128810791341505266416173864177944440580777910068)
  ))) * X ^ 65 +
  (Polynomial.C (show ℚ from (
    (-29674867557679708289501470268489174245505588238427534941011092212695608481365)
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    (29319980919626898249757570126203368952748775669186620640859415396292356902696)
  ))) * X ^ 63

private theorem remainder6Coefficient2AlignedChunk10_pieces :
    remainder6Coefficient2AlignedChunk10 =
      remainder6Coefficient2AlignedChunk10Band6 +
      remainder6Coefficient2AlignedChunk10Band7
    := by
  unfold remainder6Coefficient2AlignedChunk10 remainder6Coefficient2AlignedChunk10Band6
  unfold remainder6Coefficient2AlignedChunk10Band7
  ring

private def remainder6Coefficient2AlignedChunk11Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (1255584941527704452746120684107279804519088262460645735236845129919743970239)
  ))) * X ^ 53 +
  (Polynomial.C (show ℚ from (
    (-669748603999325958464597097086970924093349062038484944347254406246608352273)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (336610382954046870247800430609973056814614100156783614251088171941839303403)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (-159272680085665554005412039868340008540313742102294464018272462502083319687)
  ))) * X ^ 50

private def remainder6Coefficient2AlignedChunk11Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (8675175704502810005056451020992564158793676595192802876134472101780120505581)
  ))) * X ^ 57 +
  (Polynomial.C (show ℚ from (
    (-5830481717436139188317407431750895890290170664608816231867081357236807638081)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (3702118370506027212413184046033707581927114714099211294382890382098601865447)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (-2219513121535030164270397780679264356970392489509421053042722075040153528177)
  ))) * X ^ 54

private theorem remainder6Coefficient2AlignedChunk11_pieces :
    remainder6Coefficient2AlignedChunk11 =
      remainder6Coefficient2AlignedChunk11Band5 +
      remainder6Coefficient2AlignedChunk11Band6
    := by
  unfold remainder6Coefficient2AlignedChunk11 remainder6Coefficient2AlignedChunk11Band5
  unfold remainder6Coefficient2AlignedChunk11Band6
  ring

private def remainder6Coefficient2AlignedChunk12Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-477479700939294940512691747416735765410275055349521383765613870503638413)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (144026353634990108295950572197513651797712126200702663275366921671474518)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-40542392880417114577827595217658727606296695805101361776225317999217069)
  ))) * X ^ 42

private def remainder6Coefficient2AlignedChunk12Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (70888517113836029101576065940369409531584445615282962939146396016145781328)
  ))) * X ^ 49 +
  (Polynomial.C (show ℚ from (
    (-29650206849699537964032698507245513296851606331347863252387776115847583316)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (11643025766926562122844406228154118105804936001207007154181082690380887666)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-4287764319632802774818404967705164533580476016140897841109412721486110451)
  ))) * X ^ 46 +
  (Polynomial.C (show ℚ from (
    (1479223768525695267592548312069830549695338278071574379291993015701877127)
  ))) * X ^ 45

private theorem remainder6Coefficient2AlignedChunk12_pieces :
    remainder6Coefficient2AlignedChunk12 =
      remainder6Coefficient2AlignedChunk12Band4 +
      remainder6Coefficient2AlignedChunk12Band5
    := by
  unfold remainder6Coefficient2AlignedChunk12 remainder6Coefficient2AlignedChunk12Band4
  unfold remainder6Coefficient2AlignedChunk12Band5
  ring

private def remainder6Coefficient2AlignedChunk13Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (718846789678887512634375406703198906074033426219391471364325124452)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-109719477140794198875804753073087276758841812036497929336081139014)
  ))) * X ^ 34

private def remainder6Coefficient2AlignedChunk13Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (10634972873675307031983824481469065295138060418731329479412671695351331)
  ))) * X ^ 41 +
  (Polynomial.C (show ℚ from (
    (-2595765894942786989133718632757646669187271864081570841784158142739798)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (588573769496079445172517403154243371285995384632417134578830221752204)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-123767440340893257820464894377312306375992236174199351256584600826497)
  ))) * X ^ 38 +
  (Polynomial.C (show ℚ from (
    (24093711764446404639083968795437264738722231948853016334347723344608)
  ))) * X ^ 37 +
  (Polynomial.C (show ℚ from (
    (-4333812672091614152071693198914448727981015618394225383520385030545)
  ))) * X ^ 36

private theorem remainder6Coefficient2AlignedChunk13_pieces :
    remainder6Coefficient2AlignedChunk13 =
      remainder6Coefficient2AlignedChunk13Band3 +
      remainder6Coefficient2AlignedChunk13Band4
    := by
  unfold remainder6Coefficient2AlignedChunk13 remainder6Coefficient2AlignedChunk13Band3
  unfold remainder6Coefficient2AlignedChunk13Band4
  ring

private def remainder6Coefficient2AlignedChunk14Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1202354195785995779654082890523225913149444782850165542138)
  ))) * X ^ 26

private def remainder6Coefficient2AlignedChunk14Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (15375938023292737443314781690066611953593395774740798451247935996)
  ))) * X ^ 33 +
  (Polynomial.C (show ℚ from (
    (-1973712993822071474949706404738701900439752945304094416663486397)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (231486617206828337106932024113874406982323652912997734728976640)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-24741106940614472916780882365929799271623350295582017599970463)
  ))) * X ^ 30 +
  (Polynomial.C (show ℚ from (
    (2402965298590593182281477972401731407270671244975704494283858)
  ))) * X ^ 29 +
  (Polynomial.C (show ℚ from (
    (-211456483156951782480574431898617407886197741043647614921858)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (16806182195916905765842794014671909484794622698826126455197)
  ))) * X ^ 27

private theorem remainder6Coefficient2AlignedChunk14_pieces :
    remainder6Coefficient2AlignedChunk14 =
      remainder6Coefficient2AlignedChunk14Band2 +
      remainder6Coefficient2AlignedChunk14Band3
    := by
  unfold remainder6Coefficient2AlignedChunk14 remainder6Coefficient2AlignedChunk14Band2
  unfold remainder6Coefficient2AlignedChunk14Band3
  ring

private def remainder6Coefficient2AlignedChunk15Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (77153095304890737077668942243599703935246104175737125136)
  ))) * X ^ 25 +
  (Polynomial.C (show ℚ from (
    (-4423477744390859918217499644647603281157049011995581072)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (225668609643543268674369015601646240443689114451262043)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-10198589028139998496331355912344511811566429595809490)
  ))) * X ^ 22 +
  (Polynomial.C (show ℚ from (
    (406322822601229085427412664995322862376622971469458)
  ))) * X ^ 21 +
  (Polynomial.C (show ℚ from (
    (-14196253238687956318636993602484934021750025160256)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (432445741976415113013625151760023859974380847594)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-11411972561018474511482830968748711674910782454)
  ))) * X ^ 18

private theorem remainder6Coefficient2AlignedChunk15_pieces :
    remainder6Coefficient2AlignedChunk15 =
      remainder6Coefficient2AlignedChunk15Band2
    := by
  unfold remainder6Coefficient2AlignedChunk15 remainder6Coefficient2AlignedChunk15Band2
  ring

private def remainder6Coefficient2AlignedChunk16Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (259032095835806047471680291963523258316846281)
  ))) * X ^ 17 +
  (Polynomial.C (show ℚ from (
    (-5016571911267970568378770056010879664388722)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (82134255318488324259813898544644342782820)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-1124806688485678268671566174938350959972)
  ))) * X ^ 14 +
  (Polynomial.C (show ℚ from (
    (12723539027204902930750785028377793824)
  ))) * X ^ 13 +
  (Polynomial.C (show ℚ from (
    (-117085969791173174953432256005946158)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (859911591767474862236853619189470)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-4912615674644929106442104887993)
  ))) * X ^ 10

private theorem remainder6Coefficient2AlignedChunk16_pieces :
    remainder6Coefficient2AlignedChunk16 =
      remainder6Coefficient2AlignedChunk16Band1
    := by
  unfold remainder6Coefficient2AlignedChunk16 remainder6Coefficient2AlignedChunk16Band1
  ring

private def remainder6Coefficient2AlignedChunk17Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-62791036209878831071617902)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (110032602948153855002974)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (-23402482118936566492)
  ))) * X ^ 6 +
  (Polynomial.C (show ℚ from (
    (-380092333559739692)
  ))) * X ^ 5 +
  (Polynomial.C (show ℚ from (
    (895631651061428)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-952873933548)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (615854540)
  ))) * X ^ 2

private def remainder6Coefficient2AlignedChunk17Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (21010651248469401769408684890)
  ))) * X ^ 9

private theorem remainder6Coefficient2AlignedChunk17_pieces :
    remainder6Coefficient2AlignedChunk17 =
      remainder6Coefficient2AlignedChunk17Band0 +
      remainder6Coefficient2AlignedChunk17Band1
    := by
  unfold remainder6Coefficient2AlignedChunk17 remainder6Coefficient2AlignedChunk17Band0
  unfold remainder6Coefficient2AlignedChunk17Band1
  ring

private def remainder6Coefficient2AlignedChunk18Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (50452)
  ))) * X ^ 1 +
  (Polynomial.C (show ℚ from (
    (64)
  ))) * X ^ 0

private theorem remainder6Coefficient2AlignedChunk18_pieces :
    remainder6Coefficient2AlignedChunk18 =
      remainder6Coefficient2AlignedChunk18Band0
    := by
  unfold remainder6Coefficient2AlignedChunk18 remainder6Coefficient2AlignedChunk18Band0
  ring

private theorem remainder6Coefficient2AlignedBand0_eq :
    remainder6Coefficient2NormalizedBlock0 =
      remainder6Coefficient2AlignedChunk17Band0 +
      remainder6Coefficient2AlignedChunk18Band0
    := by
  unfold remainder6Coefficient2NormalizedBlock0 remainder6Coefficient2AlignedChunk17Band0
  unfold remainder6Coefficient2AlignedChunk18Band0
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand1_eq :
    remainder6Coefficient2NormalizedBlock1 =
      remainder6Coefficient2AlignedChunk16Band1 +
      remainder6Coefficient2AlignedChunk17Band1
    := by
  unfold remainder6Coefficient2NormalizedBlock1 remainder6Coefficient2AlignedChunk16Band1
  unfold remainder6Coefficient2AlignedChunk17Band1
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand2_eq :
    remainder6Coefficient2NormalizedBlock2 =
      remainder6Coefficient2AlignedChunk14Band2 +
      remainder6Coefficient2AlignedChunk15Band2
    := by
  unfold remainder6Coefficient2NormalizedBlock2 remainder6Coefficient2AlignedChunk14Band2
  unfold remainder6Coefficient2AlignedChunk15Band2
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand3_eq :
    remainder6Coefficient2NormalizedBlock3 =
      remainder6Coefficient2AlignedChunk13Band3 +
      remainder6Coefficient2AlignedChunk14Band3
    := by
  unfold remainder6Coefficient2NormalizedBlock3 remainder6Coefficient2AlignedChunk13Band3
  unfold remainder6Coefficient2AlignedChunk14Band3
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand4_eq :
    remainder6Coefficient2NormalizedBlock4 =
      remainder6Coefficient2AlignedChunk12Band4 +
      remainder6Coefficient2AlignedChunk13Band4
    := by
  unfold remainder6Coefficient2NormalizedBlock4 remainder6Coefficient2AlignedChunk12Band4
  unfold remainder6Coefficient2AlignedChunk13Band4
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand5_eq :
    remainder6Coefficient2NormalizedBlock5 =
      remainder6Coefficient2AlignedChunk11Band5 +
      remainder6Coefficient2AlignedChunk12Band5
    := by
  unfold remainder6Coefficient2NormalizedBlock5 remainder6Coefficient2AlignedChunk11Band5
  unfold remainder6Coefficient2AlignedChunk12Band5
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand6_eq :
    remainder6Coefficient2NormalizedBlock6 =
      remainder6Coefficient2AlignedChunk10Band6 +
      remainder6Coefficient2AlignedChunk11Band6
    := by
  unfold remainder6Coefficient2NormalizedBlock6 remainder6Coefficient2AlignedChunk10Band6
  unfold remainder6Coefficient2AlignedChunk11Band6
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand7_eq :
    remainder6Coefficient2NormalizedBlock7 =
      remainder6Coefficient2AlignedChunk9Band7 +
      remainder6Coefficient2AlignedChunk10Band7
    := by
  unfold remainder6Coefficient2NormalizedBlock7 remainder6Coefficient2AlignedChunk9Band7
  unfold remainder6Coefficient2AlignedChunk10Band7
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand8_eq :
    remainder6Coefficient2NormalizedBlock8 =
      remainder6Coefficient2AlignedChunk8Band8 +
      remainder6Coefficient2AlignedChunk9Band8
    := by
  unfold remainder6Coefficient2NormalizedBlock8 remainder6Coefficient2AlignedChunk8Band8
  unfold remainder6Coefficient2AlignedChunk9Band8
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand9_eq :
    remainder6Coefficient2NormalizedBlock9 =
      remainder6Coefficient2AlignedChunk7Band9 +
      remainder6Coefficient2AlignedChunk8Band9
    := by
  unfold remainder6Coefficient2NormalizedBlock9 remainder6Coefficient2AlignedChunk7Band9
  unfold remainder6Coefficient2AlignedChunk8Band9
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand10_eq :
    remainder6Coefficient2NormalizedBlock10 =
      remainder6Coefficient2AlignedChunk5Band10 +
      remainder6Coefficient2AlignedChunk6Band10
    := by
  unfold remainder6Coefficient2NormalizedBlock10 remainder6Coefficient2AlignedChunk5Band10
  unfold remainder6Coefficient2AlignedChunk6Band10
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand11_eq :
    remainder6Coefficient2NormalizedBlock11 =
      remainder6Coefficient2AlignedChunk4Band11 +
      remainder6Coefficient2AlignedChunk5Band11
    := by
  unfold remainder6Coefficient2NormalizedBlock11 remainder6Coefficient2AlignedChunk4Band11
  unfold remainder6Coefficient2AlignedChunk5Band11
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand12_eq :
    remainder6Coefficient2NormalizedBlock12 =
      remainder6Coefficient2AlignedChunk3Band12 +
      remainder6Coefficient2AlignedChunk4Band12
    := by
  unfold remainder6Coefficient2NormalizedBlock12 remainder6Coefficient2AlignedChunk3Band12
  unfold remainder6Coefficient2AlignedChunk4Band12
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand13_eq :
    remainder6Coefficient2NormalizedBlock13 =
      remainder6Coefficient2AlignedChunk2Band13 +
      remainder6Coefficient2AlignedChunk3Band13
    := by
  unfold remainder6Coefficient2NormalizedBlock13 remainder6Coefficient2AlignedChunk2Band13
  unfold remainder6Coefficient2AlignedChunk3Band13
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand14_eq :
    remainder6Coefficient2NormalizedBlock14 =
      remainder6Coefficient2AlignedChunk1Band14 +
      remainder6Coefficient2AlignedChunk2Band14
    := by
  unfold remainder6Coefficient2NormalizedBlock14 remainder6Coefficient2AlignedChunk1Band14
  unfold remainder6Coefficient2AlignedChunk2Band14
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand15_eq :
    remainder6Coefficient2NormalizedBlock15 =
      remainder6Coefficient2AlignedChunk0Band15 +
      remainder6Coefficient2AlignedChunk1Band15
    := by
  unfold remainder6Coefficient2NormalizedBlock15 remainder6Coefficient2AlignedChunk0Band15
  unfold remainder6Coefficient2AlignedChunk1Band15
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2AlignedBand16_eq :
    remainder6Coefficient2NormalizedBlock16 =
      remainder6Coefficient2AlignedChunk0Band16
    := by
  unfold remainder6Coefficient2NormalizedBlock16 remainder6Coefficient2AlignedChunk0Band16
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder6Coefficient2Aligned_eq :
    remainder6Coefficient2Aligned = remainder6Coefficient2Normalized := by
  unfold remainder6Coefficient2Aligned remainder6Coefficient2Normalized
  rw [remainder6Coefficient2AlignedChunk0_pieces]
  rw [remainder6Coefficient2AlignedChunk1_pieces]
  rw [remainder6Coefficient2AlignedChunk2_pieces]
  rw [remainder6Coefficient2AlignedChunk3_pieces]
  rw [remainder6Coefficient2AlignedChunk4_pieces]
  rw [remainder6Coefficient2AlignedChunk5_pieces]
  rw [remainder6Coefficient2AlignedChunk6_pieces]
  rw [remainder6Coefficient2AlignedChunk7_pieces]
  rw [remainder6Coefficient2AlignedChunk8_pieces]
  rw [remainder6Coefficient2AlignedChunk9_pieces]
  rw [remainder6Coefficient2AlignedChunk10_pieces]
  rw [remainder6Coefficient2AlignedChunk11_pieces]
  rw [remainder6Coefficient2AlignedChunk12_pieces]
  rw [remainder6Coefficient2AlignedChunk13_pieces]
  rw [remainder6Coefficient2AlignedChunk14_pieces]
  rw [remainder6Coefficient2AlignedChunk15_pieces]
  rw [remainder6Coefficient2AlignedChunk16_pieces]
  rw [remainder6Coefficient2AlignedChunk17_pieces]
  rw [remainder6Coefficient2AlignedChunk18_pieces]
  rw [remainder6Coefficient2AlignedBand0_eq]
  rw [remainder6Coefficient2AlignedBand1_eq]
  rw [remainder6Coefficient2AlignedBand2_eq]
  rw [remainder6Coefficient2AlignedBand3_eq]
  rw [remainder6Coefficient2AlignedBand4_eq]
  rw [remainder6Coefficient2AlignedBand5_eq]
  rw [remainder6Coefficient2AlignedBand6_eq]
  rw [remainder6Coefficient2AlignedBand7_eq]
  rw [remainder6Coefficient2AlignedBand8_eq]
  rw [remainder6Coefficient2AlignedBand9_eq]
  rw [remainder6Coefficient2AlignedBand10_eq]
  rw [remainder6Coefficient2AlignedBand11_eq]
  rw [remainder6Coefficient2AlignedBand12_eq]
  rw [remainder6Coefficient2AlignedBand13_eq]
  rw [remainder6Coefficient2AlignedBand14_eq]
  rw [remainder6Coefficient2AlignedBand15_eq]
  rw [remainder6Coefficient2AlignedBand16_eq]
  ring

private theorem remainder6Coefficient2_eq_normalized :
    remainder6Coefficient2 =
      (Polynomial.C (show ℚ from (
        (169974242287568876381639744907962243436895047572089)
      ))) * remainder6Coefficient2Normalized := by
  unfold remainder6Coefficient2 remainder6Coefficient2Block0 remainder6Coefficient2Block1
  rw [remainder6Coefficient2Chunk0_normalized]
  rw [remainder6Coefficient2Chunk1_normalized]
  rw [remainder6Coefficient2Chunk2_normalized]
  rw [remainder6Coefficient2Chunk3_normalized]
  rw [remainder6Coefficient2Chunk4_normalized]
  rw [remainder6Coefficient2Chunk5_normalized]
  rw [remainder6Coefficient2Chunk6_normalized]
  rw [remainder6Coefficient2Chunk7_normalized]
  rw [remainder6Coefficient2Chunk8_normalized]
  rw [remainder6Coefficient2Chunk9_normalized]
  rw [remainder6Coefficient2Chunk10_normalized]
  rw [remainder6Coefficient2Chunk11_normalized]
  rw [remainder6Coefficient2Chunk12_normalized]
  rw [remainder6Coefficient2Chunk13_normalized]
  rw [remainder6Coefficient2Chunk14_normalized]
  rw [remainder6Coefficient2Chunk15_normalized]
  rw [remainder6Coefficient2Chunk16_normalized]
  rw [remainder6Coefficient2Chunk17_normalized]
  rw [remainder6Coefficient2Chunk18_normalized]
  rw [← remainder6Coefficient2Aligned_eq]
  unfold remainder6Coefficient2Aligned
  ring

private def remainder7Coefficient0AlignedChunk0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1373177)
  ))) * X ^ 88 +
  (Polynomial.C (show ℚ from (
    (7716019197590)
  ))) * X ^ 87 +
  (Polynomial.C (show ℚ from (
    (-254122828595791380)
  ))) * X ^ 86 +
  (Polynomial.C (show ℚ from (
    (352825297716938520389)
  ))) * X ^ 85 +
  (Polynomial.C (show ℚ from (
    (-68322672811486813538134)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (-29670803770937401458178037)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (1695634561545085828928429959)
  ))) * X ^ 82 +
  (Polynomial.C (show ℚ from (
    (10477660306845060360644614411)
  ))) * X ^ 81

private theorem remainder7Coefficient0Chunk0_normalized :
    remainder7Coefficient0Chunk0 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk0 := by
  unfold remainder7Coefficient0Chunk0 remainder7Coefficient0AlignedChunk0
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-233809468652868163119944421292)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    (678489421943766528502281920693)
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    (2800596961661308463725888014538)
  ))) * X ^ 78 +
  (Polynomial.C (show ℚ from (
    (-1690461676274005694192406860044)
  ))) * X ^ 77 +
  (Polynomial.C (show ℚ from (
    (-226517164352505937025888890648132)
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    (1485737405210102463359773355253829)
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    (-2086994444234866319936135987406512)
  ))) * X ^ 74 +
  (Polynomial.C (show ℚ from (
    (-26000289674995471447788103119901955)
  ))) * X ^ 73

private theorem remainder7Coefficient0Chunk1_normalized :
    remainder7Coefficient0Chunk1 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk1 := by
  unfold remainder7Coefficient0Chunk1 remainder7Coefficient0AlignedChunk1
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (218894204664051951539040184986346788)
  ))) * X ^ 72 +
  (Polynomial.C (show ℚ from (
    (-961466319519087161260232994674903056)
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    (2830930383432473315760941870986302161)
  ))) * X ^ 70 +
  (Polynomial.C (show ℚ from (
    (-5427576367215037642541262805143958935)
  ))) * X ^ 69 +
  (Polynomial.C (show ℚ from (
    (3211794323129787088548195310230896362)
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    (24153677813389305383296276003473599084)
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    (-128629631816552098080409543822463733076)
  ))) * X ^ 66 +
  (Polynomial.C (show ℚ from (
    (416068241098783298139826059772715972545)
  ))) * X ^ 65

private theorem remainder7Coefficient0Chunk2_normalized :
    remainder7Coefficient0Chunk2 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk2 := by
  unfold remainder7Coefficient0Chunk2 remainder7Coefficient0AlignedChunk2
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1066037352037016856178458863183107205926)
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    (2335831244776793483990325240761008323748)
  ))) * X ^ 63 +
  (Polynomial.C (show ℚ from (
    (-4540210251637860205418195208535959220457)
  ))) * X ^ 62 +
  (Polynomial.C (show ℚ from (
    (8020728833161320862272448650228520526353)
  ))) * X ^ 61 +
  (Polynomial.C (show ℚ from (
    (-13125585342895065323015505974155898743873)
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    (20081815084119263569869152713467142627251)
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    (-28116807336188339469274532844730261231727)
  ))) * X ^ 58 +
  (Polynomial.C (show ℚ from (
    (32151263824530259001168664020939017680127)
  ))) * X ^ 57

private theorem remainder7Coefficient0Chunk3_normalized :
    remainder7Coefficient0Chunk3 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk3 := by
  unfold remainder7Coefficient0Chunk3 remainder7Coefficient0AlignedChunk3
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-14612706868881853986394265337600927556755)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (-67380991694742094705117483305623591789028)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (285882514703211166069038330824051165490866)
  ))) * X ^ 54 +
  (Polynomial.C (show ℚ from (
    (-689805149901965499466416196598290020166421)
  ))) * X ^ 53 +
  (Polynomial.C (show ℚ from (
    (1092170484437400110960352058629148818138479)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (-534143116053057852097455352543494165083863)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (-3729824296188067750273254807062069436215272)
  ))) * X ^ 50 +
  (Polynomial.C (show ℚ from (
    (17700169061522660189499102186315044486474827)
  ))) * X ^ 49

private theorem remainder7Coefficient0Chunk4_normalized :
    remainder7Coefficient0Chunk4 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk4 := by
  unfold remainder7Coefficient0Chunk4 remainder7Coefficient0AlignedChunk4
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-52086281024110934641435460965761482450406920)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (122652044579047292743206731445877024903400454)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-247931127489997908271728783701994098558255119)
  ))) * X ^ 46 +
  (Polynomial.C (show ℚ from (
    (443215089295371384649849220586239071917610698)
  ))) * X ^ 45 +
  (Polynomial.C (show ℚ from (
    (-711478550793202947751427266058338063067197463)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (1034595796885930676778990985442042308045175966)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-1370160821449111692312275718228845931926790368)
  ))) * X ^ 42 +
  (Polynomial.C (show ℚ from (
    (1658321517687828179764713747902787094831125137)
  ))) * X ^ 41

private theorem remainder7Coefficient0Chunk5_normalized :
    remainder7Coefficient0Chunk5 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk5 := by
  unfold remainder7Coefficient0Chunk5 remainder7Coefficient0AlignedChunk5
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1838543763697284624542406371963205519213556988)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (1870211159854321962625418178664357635797851048)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-1747508005908918766412712216686078774424424543)
  ))) * X ^ 38 +
  (Polynomial.C (show ℚ from (
    (1501124952938616812848246064742538914564641382)
  ))) * X ^ 37 +
  (Polynomial.C (show ℚ from (
    (-1186122364197847931683150194684841344610647396)
  ))) * X ^ 36 +
  (Polynomial.C (show ℚ from (
    (862391488846560387333515684369669044341536458)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-577018899215940779803918682841427827021671298)
  ))) * X ^ 34 +
  (Polynomial.C (show ℚ from (
    (355242326417656138647222508446703098349275513)
  ))) * X ^ 33

private theorem remainder7Coefficient0Chunk6_normalized :
    remainder7Coefficient0Chunk6 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk6 := by
  unfold remainder7Coefficient0Chunk6 remainder7Coefficient0AlignedChunk6
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-201149336333637983269308633595075627200536031)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (104671779285539508841465109229183895024140162)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-49996156526202268267729366709162218100152069)
  ))) * X ^ 30 +
  (Polynomial.C (show ℚ from (
    (21883304069025970813438678085572738889797357)
  ))) * X ^ 29 +
  (Polynomial.C (show ℚ from (
    (-8757940462674464428902157135441901655258855)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (3195937483586069513045331428253808319854892)
  ))) * X ^ 27 +
  (Polynomial.C (show ℚ from (
    (-1059821813351123995437782690938017621994262)
  ))) * X ^ 26 +
  (Polynomial.C (show ℚ from (
    (318100514287678210266838214311394262596857)
  ))) * X ^ 25

private theorem remainder7Coefficient0Chunk7_normalized :
    remainder7Coefficient0Chunk7 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk7 := by
  unfold remainder7Coefficient0Chunk7 remainder7Coefficient0AlignedChunk7
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-86014820568180252736039213140083924088236)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (20842873986610681140892828902007118034755)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-4499126544234494083041051537115487295346)
  ))) * X ^ 22 +
  (Polynomial.C (show ℚ from (
    (859414478191869075907985295334854659472)
  ))) * X ^ 21 +
  (Polynomial.C (show ℚ from (
    (-144210532219628122684973806217761779988)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (21087030829891853780743217513687964908)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-2663411680601368953497104489708664294)
  ))) * X ^ 18 +
  (Polynomial.C (show ℚ from (
    (287810023914401096857118184919994725)
  ))) * X ^ 17

private theorem remainder7Coefficient0Chunk8_normalized :
    remainder7Coefficient0Chunk8 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk8 := by
  unfold remainder7Coefficient0Chunk8 remainder7Coefficient0AlignedChunk8
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-26332671950695705534455714527045079)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (2016873124552149953013235502507296)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-127719584918819410375213819410722)
  ))) * X ^ 14 +
  (Polynomial.C (show ℚ from (
    (6595392129393813821923055995899)
  ))) * X ^ 13 +
  (Polynomial.C (show ℚ from (
    (-273429978220577115661169958211)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (8936687611683702163442626373)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-225263605566952659060625772)
  ))) * X ^ 10 +
  (Polynomial.C (show ℚ from (
    (4259153362292864437123282)
  ))) * X ^ 9

private theorem remainder7Coefficient0Chunk9_normalized :
    remainder7Coefficient0Chunk9 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk9 := by
  unfold remainder7Coefficient0Chunk9 remainder7Coefficient0AlignedChunk9
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-58196452614666749655173)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (544320982080656937619)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (-3182605184356885091)
  ))) * X ^ 6 +
  (Polynomial.C (show ℚ from (
    (9485918923583347)
  ))) * X ^ 5 +
  (Polynomial.C (show ℚ from (
    (-3343254232256)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-43971211448)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (54890212)
  ))) * X ^ 2 +
  (Polynomial.C (show ℚ from (
    (16176)
  ))) * X ^ 1

private theorem remainder7Coefficient0Chunk10_normalized :
    remainder7Coefficient0Chunk10 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk10 := by
  unfold remainder7Coefficient0Chunk10 remainder7Coefficient0AlignedChunk10
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0AlignedChunk11 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-8)
  ))) * X ^ 0

private theorem remainder7Coefficient0Chunk11_normalized :
    remainder7Coefficient0Chunk11 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0AlignedChunk11 := by
  unfold remainder7Coefficient0Chunk11 remainder7Coefficient0AlignedChunk11
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient0Aligned : Coefficient :=
  remainder7Coefficient0AlignedChunk0 +
  remainder7Coefficient0AlignedChunk1 +
  remainder7Coefficient0AlignedChunk2 +
  remainder7Coefficient0AlignedChunk3 +
  remainder7Coefficient0AlignedChunk4 +
  remainder7Coefficient0AlignedChunk5 +
  remainder7Coefficient0AlignedChunk6 +
  remainder7Coefficient0AlignedChunk7 +
  remainder7Coefficient0AlignedChunk8 +
  remainder7Coefficient0AlignedChunk9 +
  remainder7Coefficient0AlignedChunk10 +
  remainder7Coefficient0AlignedChunk11

private def remainder7Coefficient0AlignedChunk0Band9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1373177)
  ))) * X ^ 88 +
  (Polynomial.C (show ℚ from (
    (7716019197590)
  ))) * X ^ 87 +
  (Polynomial.C (show ℚ from (
    (-254122828595791380)
  ))) * X ^ 86 +
  (Polynomial.C (show ℚ from (
    (352825297716938520389)
  ))) * X ^ 85 +
  (Polynomial.C (show ℚ from (
    (-68322672811486813538134)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (-29670803770937401458178037)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (1695634561545085828928429959)
  ))) * X ^ 82 +
  (Polynomial.C (show ℚ from (
    (10477660306845060360644614411)
  ))) * X ^ 81

private theorem remainder7Coefficient0AlignedChunk0_pieces :
    remainder7Coefficient0AlignedChunk0 =
      remainder7Coefficient0AlignedChunk0Band9
    := by
  unfold remainder7Coefficient0AlignedChunk0 remainder7Coefficient0AlignedChunk0Band9
  ring

private def remainder7Coefficient0AlignedChunk1Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-233809468652868163119944421292)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    (678489421943766528502281920693)
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    (2800596961661308463725888014538)
  ))) * X ^ 78 +
  (Polynomial.C (show ℚ from (
    (-1690461676274005694192406860044)
  ))) * X ^ 77 +
  (Polynomial.C (show ℚ from (
    (-226517164352505937025888890648132)
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    (1485737405210102463359773355253829)
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    (-2086994444234866319936135987406512)
  ))) * X ^ 74 +
  (Polynomial.C (show ℚ from (
    (-26000289674995471447788103119901955)
  ))) * X ^ 73

private theorem remainder7Coefficient0AlignedChunk1_pieces :
    remainder7Coefficient0AlignedChunk1 =
      remainder7Coefficient0AlignedChunk1Band8
    := by
  unfold remainder7Coefficient0AlignedChunk1 remainder7Coefficient0AlignedChunk1Band8
  ring

private def remainder7Coefficient0AlignedChunk2Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-961466319519087161260232994674903056)
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    (2830930383432473315760941870986302161)
  ))) * X ^ 70 +
  (Polynomial.C (show ℚ from (
    (-5427576367215037642541262805143958935)
  ))) * X ^ 69 +
  (Polynomial.C (show ℚ from (
    (3211794323129787088548195310230896362)
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    (24153677813389305383296276003473599084)
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    (-128629631816552098080409543822463733076)
  ))) * X ^ 66 +
  (Polynomial.C (show ℚ from (
    (416068241098783298139826059772715972545)
  ))) * X ^ 65

private def remainder7Coefficient0AlignedChunk2Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (218894204664051951539040184986346788)
  ))) * X ^ 72

private theorem remainder7Coefficient0AlignedChunk2_pieces :
    remainder7Coefficient0AlignedChunk2 =
      remainder7Coefficient0AlignedChunk2Band7 +
      remainder7Coefficient0AlignedChunk2Band8
    := by
  unfold remainder7Coefficient0AlignedChunk2 remainder7Coefficient0AlignedChunk2Band7
  unfold remainder7Coefficient0AlignedChunk2Band8
  ring

private def remainder7Coefficient0AlignedChunk3Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-4540210251637860205418195208535959220457)
  ))) * X ^ 62 +
  (Polynomial.C (show ℚ from (
    (8020728833161320862272448650228520526353)
  ))) * X ^ 61 +
  (Polynomial.C (show ℚ from (
    (-13125585342895065323015505974155898743873)
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    (20081815084119263569869152713467142627251)
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    (-28116807336188339469274532844730261231727)
  ))) * X ^ 58 +
  (Polynomial.C (show ℚ from (
    (32151263824530259001168664020939017680127)
  ))) * X ^ 57

private def remainder7Coefficient0AlignedChunk3Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1066037352037016856178458863183107205926)
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    (2335831244776793483990325240761008323748)
  ))) * X ^ 63

private theorem remainder7Coefficient0AlignedChunk3_pieces :
    remainder7Coefficient0AlignedChunk3 =
      remainder7Coefficient0AlignedChunk3Band6 +
      remainder7Coefficient0AlignedChunk3Band7
    := by
  unfold remainder7Coefficient0AlignedChunk3 remainder7Coefficient0AlignedChunk3Band6
  unfold remainder7Coefficient0AlignedChunk3Band7
  ring

private def remainder7Coefficient0AlignedChunk4Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-689805149901965499466416196598290020166421)
  ))) * X ^ 53 +
  (Polynomial.C (show ℚ from (
    (1092170484437400110960352058629148818138479)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (-534143116053057852097455352543494165083863)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (-3729824296188067750273254807062069436215272)
  ))) * X ^ 50 +
  (Polynomial.C (show ℚ from (
    (17700169061522660189499102186315044486474827)
  ))) * X ^ 49

private def remainder7Coefficient0AlignedChunk4Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-14612706868881853986394265337600927556755)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (-67380991694742094705117483305623591789028)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (285882514703211166069038330824051165490866)
  ))) * X ^ 54

private theorem remainder7Coefficient0AlignedChunk4_pieces :
    remainder7Coefficient0AlignedChunk4 =
      remainder7Coefficient0AlignedChunk4Band5 +
      remainder7Coefficient0AlignedChunk4Band6
    := by
  unfold remainder7Coefficient0AlignedChunk4 remainder7Coefficient0AlignedChunk4Band5
  unfold remainder7Coefficient0AlignedChunk4Band6
  ring

private def remainder7Coefficient0AlignedChunk5Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-711478550793202947751427266058338063067197463)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (1034595796885930676778990985442042308045175966)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-1370160821449111692312275718228845931926790368)
  ))) * X ^ 42 +
  (Polynomial.C (show ℚ from (
    (1658321517687828179764713747902787094831125137)
  ))) * X ^ 41

private def remainder7Coefficient0AlignedChunk5Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-52086281024110934641435460965761482450406920)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (122652044579047292743206731445877024903400454)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-247931127489997908271728783701994098558255119)
  ))) * X ^ 46 +
  (Polynomial.C (show ℚ from (
    (443215089295371384649849220586239071917610698)
  ))) * X ^ 45

private theorem remainder7Coefficient0AlignedChunk5_pieces :
    remainder7Coefficient0AlignedChunk5 =
      remainder7Coefficient0AlignedChunk5Band4 +
      remainder7Coefficient0AlignedChunk5Band5
    := by
  unfold remainder7Coefficient0AlignedChunk5 remainder7Coefficient0AlignedChunk5Band4
  unfold remainder7Coefficient0AlignedChunk5Band5
  ring

private def remainder7Coefficient0AlignedChunk6Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (862391488846560387333515684369669044341536458)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-577018899215940779803918682841427827021671298)
  ))) * X ^ 34 +
  (Polynomial.C (show ℚ from (
    (355242326417656138647222508446703098349275513)
  ))) * X ^ 33

private def remainder7Coefficient0AlignedChunk6Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1838543763697284624542406371963205519213556988)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (1870211159854321962625418178664357635797851048)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-1747508005908918766412712216686078774424424543)
  ))) * X ^ 38 +
  (Polynomial.C (show ℚ from (
    (1501124952938616812848246064742538914564641382)
  ))) * X ^ 37 +
  (Polynomial.C (show ℚ from (
    (-1186122364197847931683150194684841344610647396)
  ))) * X ^ 36

private theorem remainder7Coefficient0AlignedChunk6_pieces :
    remainder7Coefficient0AlignedChunk6 =
      remainder7Coefficient0AlignedChunk6Band3 +
      remainder7Coefficient0AlignedChunk6Band4
    := by
  unfold remainder7Coefficient0AlignedChunk6 remainder7Coefficient0AlignedChunk6Band3
  unfold remainder7Coefficient0AlignedChunk6Band4
  ring

private def remainder7Coefficient0AlignedChunk7Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-1059821813351123995437782690938017621994262)
  ))) * X ^ 26 +
  (Polynomial.C (show ℚ from (
    (318100514287678210266838214311394262596857)
  ))) * X ^ 25

private def remainder7Coefficient0AlignedChunk7Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-201149336333637983269308633595075627200536031)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (104671779285539508841465109229183895024140162)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-49996156526202268267729366709162218100152069)
  ))) * X ^ 30 +
  (Polynomial.C (show ℚ from (
    (21883304069025970813438678085572738889797357)
  ))) * X ^ 29 +
  (Polynomial.C (show ℚ from (
    (-8757940462674464428902157135441901655258855)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (3195937483586069513045331428253808319854892)
  ))) * X ^ 27

private theorem remainder7Coefficient0AlignedChunk7_pieces :
    remainder7Coefficient0AlignedChunk7 =
      remainder7Coefficient0AlignedChunk7Band2 +
      remainder7Coefficient0AlignedChunk7Band3
    := by
  unfold remainder7Coefficient0AlignedChunk7 remainder7Coefficient0AlignedChunk7Band2
  unfold remainder7Coefficient0AlignedChunk7Band3
  ring

private def remainder7Coefficient0AlignedChunk8Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (287810023914401096857118184919994725)
  ))) * X ^ 17

private def remainder7Coefficient0AlignedChunk8Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-86014820568180252736039213140083924088236)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (20842873986610681140892828902007118034755)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-4499126544234494083041051537115487295346)
  ))) * X ^ 22 +
  (Polynomial.C (show ℚ from (
    (859414478191869075907985295334854659472)
  ))) * X ^ 21 +
  (Polynomial.C (show ℚ from (
    (-144210532219628122684973806217761779988)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (21087030829891853780743217513687964908)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-2663411680601368953497104489708664294)
  ))) * X ^ 18

private theorem remainder7Coefficient0AlignedChunk8_pieces :
    remainder7Coefficient0AlignedChunk8 =
      remainder7Coefficient0AlignedChunk8Band1 +
      remainder7Coefficient0AlignedChunk8Band2
    := by
  unfold remainder7Coefficient0AlignedChunk8 remainder7Coefficient0AlignedChunk8Band1
  unfold remainder7Coefficient0AlignedChunk8Band2
  ring

private def remainder7Coefficient0AlignedChunk9Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-26332671950695705534455714527045079)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (2016873124552149953013235502507296)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-127719584918819410375213819410722)
  ))) * X ^ 14 +
  (Polynomial.C (show ℚ from (
    (6595392129393813821923055995899)
  ))) * X ^ 13 +
  (Polynomial.C (show ℚ from (
    (-273429978220577115661169958211)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (8936687611683702163442626373)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-225263605566952659060625772)
  ))) * X ^ 10 +
  (Polynomial.C (show ℚ from (
    (4259153362292864437123282)
  ))) * X ^ 9

private theorem remainder7Coefficient0AlignedChunk9_pieces :
    remainder7Coefficient0AlignedChunk9 =
      remainder7Coefficient0AlignedChunk9Band1
    := by
  unfold remainder7Coefficient0AlignedChunk9 remainder7Coefficient0AlignedChunk9Band1
  ring

private def remainder7Coefficient0AlignedChunk10Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-58196452614666749655173)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (544320982080656937619)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (-3182605184356885091)
  ))) * X ^ 6 +
  (Polynomial.C (show ℚ from (
    (9485918923583347)
  ))) * X ^ 5 +
  (Polynomial.C (show ℚ from (
    (-3343254232256)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-43971211448)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (54890212)
  ))) * X ^ 2 +
  (Polynomial.C (show ℚ from (
    (16176)
  ))) * X ^ 1

private theorem remainder7Coefficient0AlignedChunk10_pieces :
    remainder7Coefficient0AlignedChunk10 =
      remainder7Coefficient0AlignedChunk10Band0
    := by
  unfold remainder7Coefficient0AlignedChunk10 remainder7Coefficient0AlignedChunk10Band0
  ring

private def remainder7Coefficient0AlignedChunk11Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-8)
  ))) * X ^ 0

private theorem remainder7Coefficient0AlignedChunk11_pieces :
    remainder7Coefficient0AlignedChunk11 =
      remainder7Coefficient0AlignedChunk11Band0
    := by
  unfold remainder7Coefficient0AlignedChunk11 remainder7Coefficient0AlignedChunk11Band0
  ring

private theorem remainder7Coefficient0AlignedBand0_eq :
    remainder7Coefficient0NormalizedBlock0 =
      remainder7Coefficient0AlignedChunk10Band0 +
      remainder7Coefficient0AlignedChunk11Band0
    := by
  unfold remainder7Coefficient0NormalizedBlock0 remainder7Coefficient0AlignedChunk10Band0
  unfold remainder7Coefficient0AlignedChunk11Band0
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand1_eq :
    remainder7Coefficient0NormalizedBlock1 =
      remainder7Coefficient0AlignedChunk8Band1 +
      remainder7Coefficient0AlignedChunk9Band1
    := by
  unfold remainder7Coefficient0NormalizedBlock1 remainder7Coefficient0AlignedChunk8Band1
  unfold remainder7Coefficient0AlignedChunk9Band1
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand2_eq :
    remainder7Coefficient0NormalizedBlock2 =
      remainder7Coefficient0AlignedChunk7Band2 +
      remainder7Coefficient0AlignedChunk8Band2
    := by
  unfold remainder7Coefficient0NormalizedBlock2 remainder7Coefficient0AlignedChunk7Band2
  unfold remainder7Coefficient0AlignedChunk8Band2
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand3_eq :
    remainder7Coefficient0NormalizedBlock3 =
      remainder7Coefficient0AlignedChunk6Band3 +
      remainder7Coefficient0AlignedChunk7Band3
    := by
  unfold remainder7Coefficient0NormalizedBlock3 remainder7Coefficient0AlignedChunk6Band3
  unfold remainder7Coefficient0AlignedChunk7Band3
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand4_eq :
    remainder7Coefficient0NormalizedBlock4 =
      remainder7Coefficient0AlignedChunk5Band4 +
      remainder7Coefficient0AlignedChunk6Band4
    := by
  unfold remainder7Coefficient0NormalizedBlock4 remainder7Coefficient0AlignedChunk5Band4
  unfold remainder7Coefficient0AlignedChunk6Band4
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand5_eq :
    remainder7Coefficient0NormalizedBlock5 =
      remainder7Coefficient0AlignedChunk4Band5 +
      remainder7Coefficient0AlignedChunk5Band5
    := by
  unfold remainder7Coefficient0NormalizedBlock5 remainder7Coefficient0AlignedChunk4Band5
  unfold remainder7Coefficient0AlignedChunk5Band5
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand6_eq :
    remainder7Coefficient0NormalizedBlock6 =
      remainder7Coefficient0AlignedChunk3Band6 +
      remainder7Coefficient0AlignedChunk4Band6
    := by
  unfold remainder7Coefficient0NormalizedBlock6 remainder7Coefficient0AlignedChunk3Band6
  unfold remainder7Coefficient0AlignedChunk4Band6
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand7_eq :
    remainder7Coefficient0NormalizedBlock7 =
      remainder7Coefficient0AlignedChunk2Band7 +
      remainder7Coefficient0AlignedChunk3Band7
    := by
  unfold remainder7Coefficient0NormalizedBlock7 remainder7Coefficient0AlignedChunk2Band7
  unfold remainder7Coefficient0AlignedChunk3Band7
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand8_eq :
    remainder7Coefficient0NormalizedBlock8 =
      remainder7Coefficient0AlignedChunk1Band8 +
      remainder7Coefficient0AlignedChunk2Band8
    := by
  unfold remainder7Coefficient0NormalizedBlock8 remainder7Coefficient0AlignedChunk1Band8
  unfold remainder7Coefficient0AlignedChunk2Band8
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0AlignedBand9_eq :
    remainder7Coefficient0NormalizedBlock9 =
      remainder7Coefficient0AlignedChunk0Band9
    := by
  unfold remainder7Coefficient0NormalizedBlock9 remainder7Coefficient0AlignedChunk0Band9
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient0Aligned_eq :
    remainder7Coefficient0Aligned = remainder7Coefficient0Normalized := by
  unfold remainder7Coefficient0Aligned remainder7Coefficient0Normalized
  rw [remainder7Coefficient0AlignedChunk0_pieces]
  rw [remainder7Coefficient0AlignedChunk1_pieces]
  rw [remainder7Coefficient0AlignedChunk2_pieces]
  rw [remainder7Coefficient0AlignedChunk3_pieces]
  rw [remainder7Coefficient0AlignedChunk4_pieces]
  rw [remainder7Coefficient0AlignedChunk5_pieces]
  rw [remainder7Coefficient0AlignedChunk6_pieces]
  rw [remainder7Coefficient0AlignedChunk7_pieces]
  rw [remainder7Coefficient0AlignedChunk8_pieces]
  rw [remainder7Coefficient0AlignedChunk9_pieces]
  rw [remainder7Coefficient0AlignedChunk10_pieces]
  rw [remainder7Coefficient0AlignedChunk11_pieces]
  rw [remainder7Coefficient0AlignedBand0_eq]
  rw [remainder7Coefficient0AlignedBand1_eq]
  rw [remainder7Coefficient0AlignedBand2_eq]
  rw [remainder7Coefficient0AlignedBand3_eq]
  rw [remainder7Coefficient0AlignedBand4_eq]
  rw [remainder7Coefficient0AlignedBand5_eq]
  rw [remainder7Coefficient0AlignedBand6_eq]
  rw [remainder7Coefficient0AlignedBand7_eq]
  rw [remainder7Coefficient0AlignedBand8_eq]
  rw [remainder7Coefficient0AlignedBand9_eq]
  ring

private theorem remainder7Coefficient0_eq_normalized :
    remainder7Coefficient0 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient0Normalized := by
  unfold remainder7Coefficient0 remainder7Coefficient0Block0
  rw [remainder7Coefficient0Chunk0_normalized]
  rw [remainder7Coefficient0Chunk1_normalized]
  rw [remainder7Coefficient0Chunk2_normalized]
  rw [remainder7Coefficient0Chunk3_normalized]
  rw [remainder7Coefficient0Chunk4_normalized]
  rw [remainder7Coefficient0Chunk5_normalized]
  rw [remainder7Coefficient0Chunk6_normalized]
  rw [remainder7Coefficient0Chunk7_normalized]
  rw [remainder7Coefficient0Chunk8_normalized]
  rw [remainder7Coefficient0Chunk9_normalized]
  rw [remainder7Coefficient0Chunk10_normalized]
  rw [remainder7Coefficient0Chunk11_normalized]
  rw [← remainder7Coefficient0Aligned_eq]
  unfold remainder7Coefficient0Aligned
  ring

private def remainder7Coefficient1AlignedChunk0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-23069201)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (60434660344933)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (-1422671437485610522)
  ))) * X ^ 82 +
  (Polynomial.C (show ℚ from (
    (1722235163684153982521)
  ))) * X ^ 81 +
  (Polynomial.C (show ℚ from (
    (-302783529996476591247136)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    (-135442515618776769100312909)
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    (8810638856519263889915976312)
  ))) * X ^ 78 +
  (Polynomial.C (show ℚ from (
    (-61061238808946806887114581598)
  ))) * X ^ 77

private theorem remainder7Coefficient1Chunk0_normalized :
    remainder7Coefficient1Chunk0 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk0 := by
  unfold remainder7Coefficient1Chunk0 remainder7Coefficient1AlignedChunk0
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (33942948959254832851312831621)
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    (78149547963546810914228595719)
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    (8685744567638681761977985259999)
  ))) * X ^ 74 +
  (Polynomial.C (show ℚ from (
    (-41678446269648527140240647875527)
  ))) * X ^ 73 +
  (Polynomial.C (show ℚ from (
    (-290372329273266516382793506938769)
  ))) * X ^ 72 +
  (Polynomial.C (show ℚ from (
    (4205829835287603026790095705715890)
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    (-23129876039104876349323575018325935)
  ))) * X ^ 70 +
  (Polynomial.C (show ℚ from (
    (66597629994619763482877138294655478)
  ))) * X ^ 69

private theorem remainder7Coefficient1Chunk1_normalized :
    remainder7Coefficient1Chunk1 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk1 := by
  unfold remainder7Coefficient1Chunk1 remainder7Coefficient1AlignedChunk1
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-19293026016932959831329131870517654)
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    (-861302495575760332906857829397951750)
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    (5245346440092702796340378825396793093)
  ))) * X ^ 66 +
  (Polynomial.C (show ℚ from (
    (-19984618290499381694085505393715780836)
  ))) * X ^ 65 +
  (Polynomial.C (show ℚ from (
    (58169030201845705727183658342487534134)
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    (-137122462938061019838569480925074865927)
  ))) * X ^ 63 +
  (Polynomial.C (show ℚ from (
    (265162405627102369754603044478660081853)
  ))) * X ^ 62 +
  (Polynomial.C (show ℚ from (
    (-409069424531728695369242869347868646592)
  ))) * X ^ 61

private theorem remainder7Coefficient1Chunk2_normalized :
    remainder7Coefficient1Chunk2 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk2 := by
  unfold remainder7Coefficient1Chunk2 remainder7Coefficient1AlignedChunk2
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (441267654667535139226336832475525937427)
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    (-85297241202895640412928933320271771895)
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    (-1095046781367419033580458345411011854478)
  ))) * X ^ 58 +
  (Polynomial.C (show ℚ from (
    (3604527182103299750262699003099223771651)
  ))) * X ^ 57 +
  (Polynomial.C (show ℚ from (
    (-7780572314545453402533430076013474646184)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (13365891959528995592400118133160125995040)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (-18690156317740598066882556613479625683765)
  ))) * X ^ 54 +
  (Polynomial.C (show ℚ from (
    (18948338326664669416447986691408775563783)
  ))) * X ^ 53

private theorem remainder7Coefficient1Chunk3_normalized :
    remainder7Coefficient1Chunk3 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk3 := by
  unfold remainder7Coefficient1Chunk3 remainder7Coefficient1AlignedChunk3
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-3183164955044598188900414638539451069461)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (-48258477529684853584267152176622849273146)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (157758354464495298707407299484365794205630)
  ))) * X ^ 50 +
  (Polynomial.C (show ℚ from (
    (-317379579889177341877310517777175984739678)
  ))) * X ^ 49 +
  (Polynomial.C (show ℚ from (
    (400899584896082079353056310883427517412232)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (842385070206877486124388258873514039217)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-1801985321585168664951411670207289045350036)
  ))) * X ^ 46 +
  (Polynomial.C (show ℚ from (
    (6596233663718766255287405909531948942448862)
  ))) * X ^ 45

private theorem remainder7Coefficient1Chunk4_normalized :
    remainder7Coefficient1Chunk4 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk4 := by
  unfold remainder7Coefficient1Chunk4 remainder7Coefficient1AlignedChunk4
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-16579401828389686175687769990216490386209878)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (33992832408098864847723980280590744802922121)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-60031730907139204563095458788837091686442275)
  ))) * X ^ 42 +
  (Polynomial.C (show ℚ from (
    (93547455212030670858945867809704833952184577)
  ))) * X ^ 41 +
  (Polynomial.C (show ℚ from (
    (-130270630852449759796793911534770749359429299)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (163319836424486826436349768091178753810746930)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-185198533512948406699887817129641801833325653)
  ))) * X ^ 38 +
  (Polynomial.C (show ℚ from (
    (190548789932272551877113293102639206050270627)
  ))) * X ^ 37

private theorem remainder7Coefficient1Chunk5_normalized :
    remainder7Coefficient1Chunk5 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk5 := by
  unfold remainder7Coefficient1Chunk5 remainder7Coefficient1AlignedChunk5
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-178284183352468228350319260024924123447536435)
  ))) * X ^ 36 +
  (Polynomial.C (show ℚ from (
    (151940831112277194585874105988525813057754994)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-118096225473730937043268933728327429094289687)
  ))) * X ^ 34 +
  (Polynomial.C (show ℚ from (
    (83793063668450327637674888512066894217449835)
  ))) * X ^ 33 +
  (Polynomial.C (show ℚ from (
    (-54309708888104016005869256155969876910376868)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (32165859683349457881910730456527621430660781)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-17407864508940912780454862049081434273349626)
  ))) * X ^ 30 +
  (Polynomial.C (show ℚ from (
    (8604011895338556065047395906268863454417173)
  ))) * X ^ 29

private theorem remainder7Coefficient1Chunk6_normalized :
    remainder7Coefficient1Chunk6 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk6 := by
  unfold remainder7Coefficient1Chunk6 remainder7Coefficient1AlignedChunk6
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-3879436806341771398220567072621557175369320)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (1592709349472522201624669920675552838076693)
  ))) * X ^ 27 +
  (Polynomial.C (show ℚ from (
    (-593785809130706467161180491816849481863710)
  ))) * X ^ 26 +
  (Polynomial.C (show ℚ from (
    (200301943056479705189493465483568561358680)
  ))) * X ^ 25 +
  (Polynomial.C (show ℚ from (
    (-60861991253592234860817619555346074612845)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (16568327233659725644781306213084896713306)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-4016053336107501738211620485829251303910)
  ))) * X ^ 22 +
  (Polynomial.C (show ℚ from (
    (860815052805763151334678044354436287402)
  ))) * X ^ 21

private theorem remainder7Coefficient1Chunk7_normalized :
    remainder7Coefficient1Chunk7 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk7 := by
  unfold remainder7Coefficient1Chunk7 remainder7Coefficient1AlignedChunk7
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-161929648721431238160211112427866448281)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (26515741044666563914745264416591392341)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-3746683934624751590852631585434030611)
  ))) * X ^ 18 +
  (Polynomial.C (show ℚ from (
    (452596528051799217191983711368623270)
  ))) * X ^ 17 +
  (Polynomial.C (show ℚ from (
    (-46279213770323558467791143457614008)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (3963334997760617625464647263051635)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-281035522793071061852521976273989)
  ))) * X ^ 14 +
  (Polynomial.C (show ℚ from (
    (16294558509994103603448409777580)
  ))) * X ^ 13

private theorem remainder7Coefficient1Chunk8_normalized :
    remainder7Coefficient1Chunk8 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk8 := by
  unfold remainder7Coefficient1Chunk8 remainder7Coefficient1AlignedChunk8
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-761762485869081095031692575950)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (28255259898427147151787211123)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-815765723095046917914520128)
  ))) * X ^ 10 +
  (Polynomial.C (show ℚ from (
    (17902635620459510523959055)
  ))) * X ^ 9 +
  (Polynomial.C (show ℚ from (
    (-289572258578312944342472)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (3307638793991226591408)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (-24994504970363441478)
  ))) * X ^ 6 +
  (Polynomial.C (show ℚ from (
    (110878040446702865)
  ))) * X ^ 5

private theorem remainder7Coefficient1Chunk9_normalized :
    remainder7Coefficient1Chunk9 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk9 := by
  unfold remainder7Coefficient1Chunk9 remainder7Coefficient1AlignedChunk9
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1AlignedChunk10 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-205237286886744)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-215435605770)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (1129274370)
  ))) * X ^ 2 +
  (Polynomial.C (show ℚ from (
    (-610064)
  ))) * X ^ 1 +
  (Polynomial.C (show ℚ from (
    (-162)
  ))) * X ^ 0

private theorem remainder7Coefficient1Chunk10_normalized :
    remainder7Coefficient1Chunk10 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1AlignedChunk10 := by
  unfold remainder7Coefficient1Chunk10 remainder7Coefficient1AlignedChunk10
  simp only [coefficientTerm_eq_C_mul_X_pow, mul_add, ← mul_assoc, ← C_mul]
  norm_num

private def remainder7Coefficient1Aligned : Coefficient :=
  remainder7Coefficient1AlignedChunk0 +
  remainder7Coefficient1AlignedChunk1 +
  remainder7Coefficient1AlignedChunk2 +
  remainder7Coefficient1AlignedChunk3 +
  remainder7Coefficient1AlignedChunk4 +
  remainder7Coefficient1AlignedChunk5 +
  remainder7Coefficient1AlignedChunk6 +
  remainder7Coefficient1AlignedChunk7 +
  remainder7Coefficient1AlignedChunk8 +
  remainder7Coefficient1AlignedChunk9 +
  remainder7Coefficient1AlignedChunk10

private def remainder7Coefficient1AlignedChunk0Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-302783529996476591247136)
  ))) * X ^ 80 +
  (Polynomial.C (show ℚ from (
    (-135442515618776769100312909)
  ))) * X ^ 79 +
  (Polynomial.C (show ℚ from (
    (8810638856519263889915976312)
  ))) * X ^ 78 +
  (Polynomial.C (show ℚ from (
    (-61061238808946806887114581598)
  ))) * X ^ 77

private def remainder7Coefficient1AlignedChunk0Band9 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-23069201)
  ))) * X ^ 84 +
  (Polynomial.C (show ℚ from (
    (60434660344933)
  ))) * X ^ 83 +
  (Polynomial.C (show ℚ from (
    (-1422671437485610522)
  ))) * X ^ 82 +
  (Polynomial.C (show ℚ from (
    (1722235163684153982521)
  ))) * X ^ 81

private theorem remainder7Coefficient1AlignedChunk0_pieces :
    remainder7Coefficient1AlignedChunk0 =
      remainder7Coefficient1AlignedChunk0Band8 +
      remainder7Coefficient1AlignedChunk0Band9
    := by
  unfold remainder7Coefficient1AlignedChunk0 remainder7Coefficient1AlignedChunk0Band8
  unfold remainder7Coefficient1AlignedChunk0Band9
  ring

private def remainder7Coefficient1AlignedChunk1Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (4205829835287603026790095705715890)
  ))) * X ^ 71 +
  (Polynomial.C (show ℚ from (
    (-23129876039104876349323575018325935)
  ))) * X ^ 70 +
  (Polynomial.C (show ℚ from (
    (66597629994619763482877138294655478)
  ))) * X ^ 69

private def remainder7Coefficient1AlignedChunk1Band8 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (33942948959254832851312831621)
  ))) * X ^ 76 +
  (Polynomial.C (show ℚ from (
    (78149547963546810914228595719)
  ))) * X ^ 75 +
  (Polynomial.C (show ℚ from (
    (8685744567638681761977985259999)
  ))) * X ^ 74 +
  (Polynomial.C (show ℚ from (
    (-41678446269648527140240647875527)
  ))) * X ^ 73 +
  (Polynomial.C (show ℚ from (
    (-290372329273266516382793506938769)
  ))) * X ^ 72

private theorem remainder7Coefficient1AlignedChunk1_pieces :
    remainder7Coefficient1AlignedChunk1 =
      remainder7Coefficient1AlignedChunk1Band7 +
      remainder7Coefficient1AlignedChunk1Band8
    := by
  unfold remainder7Coefficient1AlignedChunk1 remainder7Coefficient1AlignedChunk1Band7
  unfold remainder7Coefficient1AlignedChunk1Band8
  ring

private def remainder7Coefficient1AlignedChunk2Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (265162405627102369754603044478660081853)
  ))) * X ^ 62 +
  (Polynomial.C (show ℚ from (
    (-409069424531728695369242869347868646592)
  ))) * X ^ 61

private def remainder7Coefficient1AlignedChunk2Band7 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-19293026016932959831329131870517654)
  ))) * X ^ 68 +
  (Polynomial.C (show ℚ from (
    (-861302495575760332906857829397951750)
  ))) * X ^ 67 +
  (Polynomial.C (show ℚ from (
    (5245346440092702796340378825396793093)
  ))) * X ^ 66 +
  (Polynomial.C (show ℚ from (
    (-19984618290499381694085505393715780836)
  ))) * X ^ 65 +
  (Polynomial.C (show ℚ from (
    (58169030201845705727183658342487534134)
  ))) * X ^ 64 +
  (Polynomial.C (show ℚ from (
    (-137122462938061019838569480925074865927)
  ))) * X ^ 63

private theorem remainder7Coefficient1AlignedChunk2_pieces :
    remainder7Coefficient1AlignedChunk2 =
      remainder7Coefficient1AlignedChunk2Band6 +
      remainder7Coefficient1AlignedChunk2Band7
    := by
  unfold remainder7Coefficient1AlignedChunk2 remainder7Coefficient1AlignedChunk2Band6
  unfold remainder7Coefficient1AlignedChunk2Band7
  ring

private def remainder7Coefficient1AlignedChunk3Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (18948338326664669416447986691408775563783)
  ))) * X ^ 53

private def remainder7Coefficient1AlignedChunk3Band6 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (441267654667535139226336832475525937427)
  ))) * X ^ 60 +
  (Polynomial.C (show ℚ from (
    (-85297241202895640412928933320271771895)
  ))) * X ^ 59 +
  (Polynomial.C (show ℚ from (
    (-1095046781367419033580458345411011854478)
  ))) * X ^ 58 +
  (Polynomial.C (show ℚ from (
    (3604527182103299750262699003099223771651)
  ))) * X ^ 57 +
  (Polynomial.C (show ℚ from (
    (-7780572314545453402533430076013474646184)
  ))) * X ^ 56 +
  (Polynomial.C (show ℚ from (
    (13365891959528995592400118133160125995040)
  ))) * X ^ 55 +
  (Polynomial.C (show ℚ from (
    (-18690156317740598066882556613479625683765)
  ))) * X ^ 54

private theorem remainder7Coefficient1AlignedChunk3_pieces :
    remainder7Coefficient1AlignedChunk3 =
      remainder7Coefficient1AlignedChunk3Band5 +
      remainder7Coefficient1AlignedChunk3Band6
    := by
  unfold remainder7Coefficient1AlignedChunk3 remainder7Coefficient1AlignedChunk3Band5
  unfold remainder7Coefficient1AlignedChunk3Band6
  ring

private def remainder7Coefficient1AlignedChunk4Band5 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-3183164955044598188900414638539451069461)
  ))) * X ^ 52 +
  (Polynomial.C (show ℚ from (
    (-48258477529684853584267152176622849273146)
  ))) * X ^ 51 +
  (Polynomial.C (show ℚ from (
    (157758354464495298707407299484365794205630)
  ))) * X ^ 50 +
  (Polynomial.C (show ℚ from (
    (-317379579889177341877310517777175984739678)
  ))) * X ^ 49 +
  (Polynomial.C (show ℚ from (
    (400899584896082079353056310883427517412232)
  ))) * X ^ 48 +
  (Polynomial.C (show ℚ from (
    (842385070206877486124388258873514039217)
  ))) * X ^ 47 +
  (Polynomial.C (show ℚ from (
    (-1801985321585168664951411670207289045350036)
  ))) * X ^ 46 +
  (Polynomial.C (show ℚ from (
    (6596233663718766255287405909531948942448862)
  ))) * X ^ 45

private theorem remainder7Coefficient1AlignedChunk4_pieces :
    remainder7Coefficient1AlignedChunk4 =
      remainder7Coefficient1AlignedChunk4Band5
    := by
  unfold remainder7Coefficient1AlignedChunk4 remainder7Coefficient1AlignedChunk4Band5
  ring

private def remainder7Coefficient1AlignedChunk5Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-16579401828389686175687769990216490386209878)
  ))) * X ^ 44 +
  (Polynomial.C (show ℚ from (
    (33992832408098864847723980280590744802922121)
  ))) * X ^ 43 +
  (Polynomial.C (show ℚ from (
    (-60031730907139204563095458788837091686442275)
  ))) * X ^ 42 +
  (Polynomial.C (show ℚ from (
    (93547455212030670858945867809704833952184577)
  ))) * X ^ 41 +
  (Polynomial.C (show ℚ from (
    (-130270630852449759796793911534770749359429299)
  ))) * X ^ 40 +
  (Polynomial.C (show ℚ from (
    (163319836424486826436349768091178753810746930)
  ))) * X ^ 39 +
  (Polynomial.C (show ℚ from (
    (-185198533512948406699887817129641801833325653)
  ))) * X ^ 38 +
  (Polynomial.C (show ℚ from (
    (190548789932272551877113293102639206050270627)
  ))) * X ^ 37

private theorem remainder7Coefficient1AlignedChunk5_pieces :
    remainder7Coefficient1AlignedChunk5 =
      remainder7Coefficient1AlignedChunk5Band4
    := by
  unfold remainder7Coefficient1AlignedChunk5 remainder7Coefficient1AlignedChunk5Band4
  ring

private def remainder7Coefficient1AlignedChunk6Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (151940831112277194585874105988525813057754994)
  ))) * X ^ 35 +
  (Polynomial.C (show ℚ from (
    (-118096225473730937043268933728327429094289687)
  ))) * X ^ 34 +
  (Polynomial.C (show ℚ from (
    (83793063668450327637674888512066894217449835)
  ))) * X ^ 33 +
  (Polynomial.C (show ℚ from (
    (-54309708888104016005869256155969876910376868)
  ))) * X ^ 32 +
  (Polynomial.C (show ℚ from (
    (32165859683349457881910730456527621430660781)
  ))) * X ^ 31 +
  (Polynomial.C (show ℚ from (
    (-17407864508940912780454862049081434273349626)
  ))) * X ^ 30 +
  (Polynomial.C (show ℚ from (
    (8604011895338556065047395906268863454417173)
  ))) * X ^ 29

private def remainder7Coefficient1AlignedChunk6Band4 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-178284183352468228350319260024924123447536435)
  ))) * X ^ 36

private theorem remainder7Coefficient1AlignedChunk6_pieces :
    remainder7Coefficient1AlignedChunk6 =
      remainder7Coefficient1AlignedChunk6Band3 +
      remainder7Coefficient1AlignedChunk6Band4
    := by
  unfold remainder7Coefficient1AlignedChunk6 remainder7Coefficient1AlignedChunk6Band3
  unfold remainder7Coefficient1AlignedChunk6Band4
  ring

private def remainder7Coefficient1AlignedChunk7Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-593785809130706467161180491816849481863710)
  ))) * X ^ 26 +
  (Polynomial.C (show ℚ from (
    (200301943056479705189493465483568561358680)
  ))) * X ^ 25 +
  (Polynomial.C (show ℚ from (
    (-60861991253592234860817619555346074612845)
  ))) * X ^ 24 +
  (Polynomial.C (show ℚ from (
    (16568327233659725644781306213084896713306)
  ))) * X ^ 23 +
  (Polynomial.C (show ℚ from (
    (-4016053336107501738211620485829251303910)
  ))) * X ^ 22 +
  (Polynomial.C (show ℚ from (
    (860815052805763151334678044354436287402)
  ))) * X ^ 21

private def remainder7Coefficient1AlignedChunk7Band3 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-3879436806341771398220567072621557175369320)
  ))) * X ^ 28 +
  (Polynomial.C (show ℚ from (
    (1592709349472522201624669920675552838076693)
  ))) * X ^ 27

private theorem remainder7Coefficient1AlignedChunk7_pieces :
    remainder7Coefficient1AlignedChunk7 =
      remainder7Coefficient1AlignedChunk7Band2 +
      remainder7Coefficient1AlignedChunk7Band3
    := by
  unfold remainder7Coefficient1AlignedChunk7 remainder7Coefficient1AlignedChunk7Band2
  unfold remainder7Coefficient1AlignedChunk7Band3
  ring

private def remainder7Coefficient1AlignedChunk8Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (452596528051799217191983711368623270)
  ))) * X ^ 17 +
  (Polynomial.C (show ℚ from (
    (-46279213770323558467791143457614008)
  ))) * X ^ 16 +
  (Polynomial.C (show ℚ from (
    (3963334997760617625464647263051635)
  ))) * X ^ 15 +
  (Polynomial.C (show ℚ from (
    (-281035522793071061852521976273989)
  ))) * X ^ 14 +
  (Polynomial.C (show ℚ from (
    (16294558509994103603448409777580)
  ))) * X ^ 13

private def remainder7Coefficient1AlignedChunk8Band2 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-161929648721431238160211112427866448281)
  ))) * X ^ 20 +
  (Polynomial.C (show ℚ from (
    (26515741044666563914745264416591392341)
  ))) * X ^ 19 +
  (Polynomial.C (show ℚ from (
    (-3746683934624751590852631585434030611)
  ))) * X ^ 18

private theorem remainder7Coefficient1AlignedChunk8_pieces :
    remainder7Coefficient1AlignedChunk8 =
      remainder7Coefficient1AlignedChunk8Band1 +
      remainder7Coefficient1AlignedChunk8Band2
    := by
  unfold remainder7Coefficient1AlignedChunk8 remainder7Coefficient1AlignedChunk8Band1
  unfold remainder7Coefficient1AlignedChunk8Band2
  ring

private def remainder7Coefficient1AlignedChunk9Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-289572258578312944342472)
  ))) * X ^ 8 +
  (Polynomial.C (show ℚ from (
    (3307638793991226591408)
  ))) * X ^ 7 +
  (Polynomial.C (show ℚ from (
    (-24994504970363441478)
  ))) * X ^ 6 +
  (Polynomial.C (show ℚ from (
    (110878040446702865)
  ))) * X ^ 5

private def remainder7Coefficient1AlignedChunk9Band1 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-761762485869081095031692575950)
  ))) * X ^ 12 +
  (Polynomial.C (show ℚ from (
    (28255259898427147151787211123)
  ))) * X ^ 11 +
  (Polynomial.C (show ℚ from (
    (-815765723095046917914520128)
  ))) * X ^ 10 +
  (Polynomial.C (show ℚ from (
    (17902635620459510523959055)
  ))) * X ^ 9

private theorem remainder7Coefficient1AlignedChunk9_pieces :
    remainder7Coefficient1AlignedChunk9 =
      remainder7Coefficient1AlignedChunk9Band0 +
      remainder7Coefficient1AlignedChunk9Band1
    := by
  unfold remainder7Coefficient1AlignedChunk9 remainder7Coefficient1AlignedChunk9Band0
  unfold remainder7Coefficient1AlignedChunk9Band1
  ring

private def remainder7Coefficient1AlignedChunk10Band0 : Coefficient :=
  (Polynomial.C (show ℚ from (
    (-205237286886744)
  ))) * X ^ 4 +
  (Polynomial.C (show ℚ from (
    (-215435605770)
  ))) * X ^ 3 +
  (Polynomial.C (show ℚ from (
    (1129274370)
  ))) * X ^ 2 +
  (Polynomial.C (show ℚ from (
    (-610064)
  ))) * X ^ 1 +
  (Polynomial.C (show ℚ from (
    (-162)
  ))) * X ^ 0

private theorem remainder7Coefficient1AlignedChunk10_pieces :
    remainder7Coefficient1AlignedChunk10 =
      remainder7Coefficient1AlignedChunk10Band0
    := by
  unfold remainder7Coefficient1AlignedChunk10 remainder7Coefficient1AlignedChunk10Band0
  ring

private theorem remainder7Coefficient1AlignedBand0_eq :
    remainder7Coefficient1NormalizedBlock0 =
      remainder7Coefficient1AlignedChunk9Band0 +
      remainder7Coefficient1AlignedChunk10Band0
    := by
  unfold remainder7Coefficient1NormalizedBlock0 remainder7Coefficient1AlignedChunk9Band0
  unfold remainder7Coefficient1AlignedChunk10Band0
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand1_eq :
    remainder7Coefficient1NormalizedBlock1 =
      remainder7Coefficient1AlignedChunk8Band1 +
      remainder7Coefficient1AlignedChunk9Band1
    := by
  unfold remainder7Coefficient1NormalizedBlock1 remainder7Coefficient1AlignedChunk8Band1
  unfold remainder7Coefficient1AlignedChunk9Band1
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand2_eq :
    remainder7Coefficient1NormalizedBlock2 =
      remainder7Coefficient1AlignedChunk7Band2 +
      remainder7Coefficient1AlignedChunk8Band2
    := by
  unfold remainder7Coefficient1NormalizedBlock2 remainder7Coefficient1AlignedChunk7Band2
  unfold remainder7Coefficient1AlignedChunk8Band2
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand3_eq :
    remainder7Coefficient1NormalizedBlock3 =
      remainder7Coefficient1AlignedChunk6Band3 +
      remainder7Coefficient1AlignedChunk7Band3
    := by
  unfold remainder7Coefficient1NormalizedBlock3 remainder7Coefficient1AlignedChunk6Band3
  unfold remainder7Coefficient1AlignedChunk7Band3
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand4_eq :
    remainder7Coefficient1NormalizedBlock4 =
      remainder7Coefficient1AlignedChunk5Band4 +
      remainder7Coefficient1AlignedChunk6Band4
    := by
  unfold remainder7Coefficient1NormalizedBlock4 remainder7Coefficient1AlignedChunk5Band4
  unfold remainder7Coefficient1AlignedChunk6Band4
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand5_eq :
    remainder7Coefficient1NormalizedBlock5 =
      remainder7Coefficient1AlignedChunk3Band5 +
      remainder7Coefficient1AlignedChunk4Band5
    := by
  unfold remainder7Coefficient1NormalizedBlock5 remainder7Coefficient1AlignedChunk3Band5
  unfold remainder7Coefficient1AlignedChunk4Band5
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand6_eq :
    remainder7Coefficient1NormalizedBlock6 =
      remainder7Coefficient1AlignedChunk2Band6 +
      remainder7Coefficient1AlignedChunk3Band6
    := by
  unfold remainder7Coefficient1NormalizedBlock6 remainder7Coefficient1AlignedChunk2Band6
  unfold remainder7Coefficient1AlignedChunk3Band6
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand7_eq :
    remainder7Coefficient1NormalizedBlock7 =
      remainder7Coefficient1AlignedChunk1Band7 +
      remainder7Coefficient1AlignedChunk2Band7
    := by
  unfold remainder7Coefficient1NormalizedBlock7 remainder7Coefficient1AlignedChunk1Band7
  unfold remainder7Coefficient1AlignedChunk2Band7
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand8_eq :
    remainder7Coefficient1NormalizedBlock8 =
      remainder7Coefficient1AlignedChunk0Band8 +
      remainder7Coefficient1AlignedChunk1Band8
    := by
  unfold remainder7Coefficient1NormalizedBlock8 remainder7Coefficient1AlignedChunk0Band8
  unfold remainder7Coefficient1AlignedChunk1Band8
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1AlignedBand9_eq :
    remainder7Coefficient1NormalizedBlock9 =
      remainder7Coefficient1AlignedChunk0Band9
    := by
  unfold remainder7Coefficient1NormalizedBlock9 remainder7Coefficient1AlignedChunk0Band9
  norm_num [map_neg, map_ofNat]
  ring

private theorem remainder7Coefficient1Aligned_eq :
    remainder7Coefficient1Aligned = remainder7Coefficient1Normalized := by
  unfold remainder7Coefficient1Aligned remainder7Coefficient1Normalized
  rw [remainder7Coefficient1AlignedChunk0_pieces]
  rw [remainder7Coefficient1AlignedChunk1_pieces]
  rw [remainder7Coefficient1AlignedChunk2_pieces]
  rw [remainder7Coefficient1AlignedChunk3_pieces]
  rw [remainder7Coefficient1AlignedChunk4_pieces]
  rw [remainder7Coefficient1AlignedChunk5_pieces]
  rw [remainder7Coefficient1AlignedChunk6_pieces]
  rw [remainder7Coefficient1AlignedChunk7_pieces]
  rw [remainder7Coefficient1AlignedChunk8_pieces]
  rw [remainder7Coefficient1AlignedChunk9_pieces]
  rw [remainder7Coefficient1AlignedChunk10_pieces]
  rw [remainder7Coefficient1AlignedBand0_eq]
  rw [remainder7Coefficient1AlignedBand1_eq]
  rw [remainder7Coefficient1AlignedBand2_eq]
  rw [remainder7Coefficient1AlignedBand3_eq]
  rw [remainder7Coefficient1AlignedBand4_eq]
  rw [remainder7Coefficient1AlignedBand5_eq]
  rw [remainder7Coefficient1AlignedBand6_eq]
  rw [remainder7Coefficient1AlignedBand7_eq]
  rw [remainder7Coefficient1AlignedBand8_eq]
  rw [remainder7Coefficient1AlignedBand9_eq]
  ring

private theorem remainder7Coefficient1_eq_normalized :
    remainder7Coefficient1 =
      (Polynomial.C (show ℚ from (
        ((675104091044445478638539502879522303153057994244818592059896109 * 10 ^ 77 +
          76164207728007698297318822544326745362653178990742192636567850547586675788100))
      ))) * remainder7Coefficient1Normalized := by
  unfold remainder7Coefficient1 remainder7Coefficient1Block0
  rw [remainder7Coefficient1Chunk0_normalized]
  rw [remainder7Coefficient1Chunk1_normalized]
  rw [remainder7Coefficient1Chunk2_normalized]
  rw [remainder7Coefficient1Chunk3_normalized]
  rw [remainder7Coefficient1Chunk4_normalized]
  rw [remainder7Coefficient1Chunk5_normalized]
  rw [remainder7Coefficient1Chunk6_normalized]
  rw [remainder7Coefficient1Chunk7_normalized]
  rw [remainder7Coefficient1Chunk8_normalized]
  rw [remainder7Coefficient1Chunk9_normalized]
  rw [remainder7Coefficient1Chunk10_normalized]
  rw [← remainder7Coefficient1Aligned_eq]
  unfold remainder7Coefficient1Aligned
  ring

private theorem recurrence6Content_relation :
    recurrence6Content7 ^ 2 =
      recurrence6Content6 * exceptionalUnit6 := by
  unfold recurrence6Content7 recurrence6Content6 exceptionalUnit6
  simp only [← C_mul, ← C_pow]
  norm_num

private theorem exceptional6_eq_normalized :
    exceptional6 =
      exceptionalUnit6 * normalizedExceptional6 := by
  rw [normalizedExceptional6_eq]
  unfold exceptional6
  ring

theorem scalarResidual6 :
    remainder7Coefficient1 ^ 2 * remainder6Coefficient0 =
      remainder7Coefficient0 *
          (remainder7Coefficient1 * remainder6Coefficient1 -
            remainder7Coefficient0 * remainder6Coefficient2) -
        remainder6Coefficient2 ^ 2 * exceptional6 := by
  rw [remainder6Coefficient0_eq_normalized]
  rw [remainder6Coefficient1_eq_normalized]
  rw [remainder6Coefficient2_eq_normalized]
  rw [remainder7Coefficient0_eq_normalized]
  rw [remainder7Coefficient1_eq_normalized]
  rw [exceptional6_eq_normalized]
  calc
    (recurrence6Content7 * remainder7Coefficient1Normalized) ^ 2 *
          (recurrence6Content6 * remainder6Coefficient0Normalized) =
        recurrence6Content6 * recurrence6Content7 ^ 2 *
          (remainder7Coefficient1Normalized ^ 2 *
            remainder6Coefficient0Normalized) := by ring
    _ = recurrence6Content6 * recurrence6Content7 ^ 2 *
          (remainder7Coefficient0Normalized *
              (remainder7Coefficient1Normalized *
                  remainder6Coefficient1Normalized -
                remainder7Coefficient0Normalized *
                  remainder6Coefficient2Normalized) -
            remainder6Coefficient2Normalized ^ 2 *
              normalizedExceptional6) := by
          rw [normalizedScalarResidual6]
    _ = (recurrence6Content7 * remainder7Coefficient0Normalized) *
          ((recurrence6Content7 * remainder7Coefficient1Normalized) *
              (recurrence6Content6 * remainder6Coefficient1Normalized) -
            (recurrence6Content7 * remainder7Coefficient0Normalized) *
              (recurrence6Content6 * remainder6Coefficient2Normalized)) -
        (recurrence6Content6 * remainder6Coefficient2Normalized) ^ 2 *
          (exceptionalUnit6 * normalizedExceptional6) := by
            have contentScale :
                recurrence6Content6 ^ 2 * exceptionalUnit6 =
                  recurrence6Content6 * recurrence6Content7 ^ 2 := by
              calc
                recurrence6Content6 ^ 2 * exceptionalUnit6 =
                    recurrence6Content6 *
                      (recurrence6Content6 * exceptionalUnit6) := by ring
                _ = recurrence6Content6 *
                    recurrence6Content7 ^ 2 := by
                      rw [← recurrence6Content_relation]
            linear_combination
              (remainder6Coefficient2Normalized ^ 2 *
                normalizedExceptional6) * contentScale

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

open Polynomial
open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution :
remainder7Coefficient1 ^ 2 * remainder6Coefficient0 =
  remainder7Coefficient0 * (remainder7Coefficient1 * remainder6Coefficient1 -
    remainder7Coefficient0 * remainder6Coefficient2) -
  remainder6Coefficient2 ^ 2 * ((C
    (((((((26813799997641 : ℚ) * 10 ^ 36 +
      142369575613846289747847827330896388) * 10 ^ 36 +
      174087143449204393900331622823388931) * 10 ^ 36 +
      504208118624079313576123579518587434) * 10 ^ 36 +
      856069465570511249870923189965244671) * 10 ^ 36 +
      650107475862081909428552923558342334) * 10 ^ 36 +
      248809782697354987477701994402490000)) *
  (parameter - 1) ^ 1 *
  (discriminantFactor) ^ 6 *
  (cmTwelve) ^ 1) := by
  exact scalarResidual6

#print axioms solution
