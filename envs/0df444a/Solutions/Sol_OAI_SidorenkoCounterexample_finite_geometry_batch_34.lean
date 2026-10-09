-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_34
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:39:53.450748+00:00
-- url     : https://prove2.me/submissions/e12476aa-8022-432f-9a79-09831398fcb4

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_1038]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_1039]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_1040]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_1041]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_1042]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_1043]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_1044]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_1045]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_1046]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_1047]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_1048]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_1049]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_1050]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_1051]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_1052]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_1053]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_1054]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_1055]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_1056]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_1057]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_1058]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_1072]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_1074]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_1075]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_1076]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_1077]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_1078]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_1079]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_1080]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_1081]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_1082]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_1083]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_1084]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_1085]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_1086]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_1087]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_1088]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_1089]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_1090]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_1091]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_1092]
  [p41 : OAI.SidorenkoCounterexample.ProofCertificate_1093]
  [p42 : OAI.SidorenkoCounterexample.ProofCertificate_1094]
  [p43 : OAI.SidorenkoCounterexample.ProofCertificate_1095]
  [p44 : OAI.SidorenkoCounterexample.ProofCertificate_1096]
  [p45 : OAI.SidorenkoCounterexample.ProofCertificate_1097]
  [p46 : OAI.SidorenkoCounterexample.ProofCertificate_1098]
  [p47 : OAI.SidorenkoCounterexample.ProofCertificate_1099]
  [p48 : OAI.SidorenkoCounterexample.ProofCertificate_1100]
  [p49 : OAI.SidorenkoCounterexample.ProofCertificate_1101]
  [p50 : OAI.SidorenkoCounterexample.ProofCertificate_1102]
  [p51 : OAI.SidorenkoCounterexample.ProofCertificate_1103]
  [p52 : OAI.SidorenkoCounterexample.ProofCertificate_1104]
  [p53 : OAI.SidorenkoCounterexample.ProofCertificate_1105]
  [p54 : OAI.SidorenkoCounterexample.ProofCertificate_1106]
  [p55 : OAI.SidorenkoCounterexample.ProofCertificate_1107]
  [p56 : OAI.SidorenkoCounterexample.ProofCertificate_1108]
  [p57 : OAI.SidorenkoCounterexample.ProofCertificate_1109]
  [p58 : OAI.SidorenkoCounterexample.ProofCertificate_1110]
  [p59 : OAI.SidorenkoCounterexample.ProofCertificate_1111]
  [p60 : OAI.SidorenkoCounterexample.ProofCertificate_1112]
  [p61 : OAI.SidorenkoCounterexample.ProofCertificate_1113]
  [p62 : OAI.SidorenkoCounterexample.ProofCertificate_1114]
  [p63 : OAI.SidorenkoCounterexample.ProofCertificate_1115]
  [p64 : OAI.SidorenkoCounterexample.ProofCertificate_1116]
  [p65 : OAI.SidorenkoCounterexample.ProofCertificate_1117]
  [p66 : OAI.SidorenkoCounterexample.ProofCertificate_1118]
  [p67 : OAI.SidorenkoCounterexample.ProofCertificate_1119]
  [p68 : OAI.SidorenkoCounterexample.ProofCertificate_1120]
  [p69 : OAI.SidorenkoCounterexample.ProofCertificate_1121]
  [p70 : OAI.SidorenkoCounterexample.ProofCertificate_1122]
  [p71 : OAI.SidorenkoCounterexample.ProofCertificate_1123]
  [p72 : OAI.SidorenkoCounterexample.ProofCertificate_1124]
  [p73 : OAI.SidorenkoCounterexample.ProofCertificate_1125]
  [p74 : OAI.SidorenkoCounterexample.ProofCertificate_1126]
  [p75 : OAI.SidorenkoCounterexample.ProofCertificate_1127]
  [p76 : OAI.SidorenkoCounterexample.ProofCertificate_1128]
  [p77 : OAI.SidorenkoCounterexample.ProofCertificate_1129]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
lemma certificate_proof_1130 : pairCorners (cornerPairL (18,2)) ∩ pairCorners (cornerPairR (18,2))={(18,2)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1130 : OAI.SidorenkoCounterexample.ProofCertificate_1130 := by
  constructor
  exact @certificate_proof_1130 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1131 : pairCorners (cornerPairL (19,0)) ∩ pairCorners (cornerPairR (19,0))={(19,0)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1131 : OAI.SidorenkoCounterexample.ProofCertificate_1131 := by
  constructor
  exact @certificate_proof_1131 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1132 : pairCorners (cornerPairL (19,1)) ∩ pairCorners (cornerPairR (19,1))={(19,1)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1132 : OAI.SidorenkoCounterexample.ProofCertificate_1132 := by
  constructor
  exact @certificate_proof_1132 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1133 : pairCorners (cornerPairL (19,2)) ∩ pairCorners (cornerPairR (19,2))={(19,2)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1133 : OAI.SidorenkoCounterexample.ProofCertificate_1133 := by
  constructor
  exact @certificate_proof_1133 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1134 : pairCorners (cornerPairL (20,0)) ∩ pairCorners (cornerPairR (20,0))={(20,0)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1134 : OAI.SidorenkoCounterexample.ProofCertificate_1134 := by
  constructor
  exact @certificate_proof_1134 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1135 : pairCorners (cornerPairL (20,1)) ∩ pairCorners (cornerPairR (20,1))={(20,1)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1135 : OAI.SidorenkoCounterexample.ProofCertificate_1135 := by
  constructor
  exact @certificate_proof_1135 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1136 : pairCorners (cornerPairL (20,2)) ∩ pairCorners (cornerPairR (20,2))={(20,2)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1136 : OAI.SidorenkoCounterexample.ProofCertificate_1136 := by
  constructor
  exact @certificate_proof_1136 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1137 : pairCorners (cornerPairL (21,0)) ∩ pairCorners (cornerPairR (21,0))={(21,0)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1137 : OAI.SidorenkoCounterexample.ProofCertificate_1137 := by
  constructor
  exact @certificate_proof_1137 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1138 : pairCorners (cornerPairL (21,1)) ∩ pairCorners (cornerPairR (21,1))={(21,1)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1138 : OAI.SidorenkoCounterexample.ProofCertificate_1138 := by
  constructor
  exact @certificate_proof_1138 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1139 : pairCorners (cornerPairL (21,2)) ∩ pairCorners (cornerPairR (21,2))={(21,2)} := by
  simp only [pairCorners_table]
  decide

private instance certificate_instance_1139 : OAI.SidorenkoCounterexample.ProofCertificate_1139 := by
  constructor
  exact @certificate_proof_1139 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

theorem certificate_proof_1140 (k : ActCorner) : pairCorners (cornerPairL k) ∩ pairCorners (cornerPairR k)={k} := by
  rcases k with ⟨j,k⟩
  fin_cases j <;> fin_cases k
  · exact pairCorners_inter_0_0
  · exact pairCorners_inter_0_1
  · exact pairCorners_inter_0_2
  · exact pairCorners_inter_1_0
  · exact pairCorners_inter_1_1
  · exact pairCorners_inter_1_2
  · exact pairCorners_inter_2_0
  · exact pairCorners_inter_2_1
  · exact pairCorners_inter_2_2
  · exact pairCorners_inter_3_0
  · exact pairCorners_inter_3_1
  · exact pairCorners_inter_3_2
  · exact pairCorners_inter_4_0
  · exact pairCorners_inter_4_1
  · exact pairCorners_inter_4_2
  · exact pairCorners_inter_5_0
  · exact pairCorners_inter_5_1
  · exact pairCorners_inter_5_2
  · exact pairCorners_inter_6_0
  · exact pairCorners_inter_6_1
  · exact pairCorners_inter_6_2
  · exact pairCorners_inter_7_0
  · exact pairCorners_inter_7_1
  · exact pairCorners_inter_7_2
  · exact pairCorners_inter_8_0
  · exact pairCorners_inter_8_1
  · exact pairCorners_inter_8_2
  · exact pairCorners_inter_9_0
  · exact pairCorners_inter_9_1
  · exact pairCorners_inter_9_2
  · exact pairCorners_inter_10_0
  · exact pairCorners_inter_10_1
  · exact pairCorners_inter_10_2
  · exact pairCorners_inter_11_0
  · exact pairCorners_inter_11_1
  · exact pairCorners_inter_11_2
  · exact pairCorners_inter_12_0
  · exact pairCorners_inter_12_1
  · exact pairCorners_inter_12_2
  · exact pairCorners_inter_13_0
  · exact pairCorners_inter_13_1
  · exact pairCorners_inter_13_2
  · exact pairCorners_inter_14_0
  · exact pairCorners_inter_14_1
  · exact pairCorners_inter_14_2
  · exact pairCorners_inter_15_0
  · exact pairCorners_inter_15_1
  · exact pairCorners_inter_15_2
  · exact pairCorners_inter_16_0
  · exact pairCorners_inter_16_1
  · exact pairCorners_inter_16_2
  · exact pairCorners_inter_17_0
  · exact pairCorners_inter_17_1
  · exact pairCorners_inter_17_2
  · exact pairCorners_inter_18_0
  · exact pairCorners_inter_18_1
  · exact pairCorners_inter_18_2
  · exact pairCorners_inter_19_0
  · exact pairCorners_inter_19_1
  · exact pairCorners_inter_19_2
  · exact pairCorners_inter_20_0
  · exact pairCorners_inter_20_1
  · exact pairCorners_inter_20_2
  · exact pairCorners_inter_21_0
  · exact pairCorners_inter_21_1
  · exact pairCorners_inter_21_2

private instance certificate_instance_1140 : OAI.SidorenkoCounterexample.ProofCertificate_1140 := by
  constructor
  intro q0
  exact @certificate_proof_1140 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

theorem certificate_proof_1141 (e : Fin 33) : (pairCorners e).card=4 := by
  rw [pairCorners_table]
  have ht : ∀ e,(pairCornerTable e).card=4 := by decide
  exact ht e

private instance certificate_instance_1141 : OAI.SidorenkoCounterexample.ProofCertificate_1141 := by
  constructor
  intro q0
  exact @certificate_proof_1141 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

theorem certificate_proof_1142 (k : ActCorner) : k∈pairCorners (cornerPairL k) := (pairCorners_mem _ _).mpr (Or.inl rfl)

private instance certificate_instance_1142 : OAI.SidorenkoCounterexample.ProofCertificate_1142 := by
  constructor
  intro q0
  exact @certificate_proof_1142 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

theorem certificate_proof_1143 (k : ActCorner) : k∈pairCorners (cornerPairR k) := (pairCorners_mem _ _).mpr (Or.inr rfl)

private instance certificate_instance_1143 : OAI.SidorenkoCounterexample.ProofCertificate_1143 := by
  constructor
  intro q0
  exact @certificate_proof_1143 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

theorem certificate_proof_1144 (k : ActCorner) : cornerGamma k≠∅ := by
  intro he
  have he : pairCorners (cornerPairL k)=pairCorners (cornerPairR k) := Finset.symmDiff_eq_empty.mp he
  have hi := pairCorners_inter k
  rw [he,Finset.inter_self] at hi
  have hc := pairCorners_card (cornerPairR k)
  rw [hi] at hc
  simp at hc

private instance certificate_instance_1144 : OAI.SidorenkoCounterexample.ProofCertificate_1144 := by
  constructor
  intro q0
  exact @certificate_proof_1144 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

theorem certificate_proof_1145 (k : ActCorner) : ¬cornerMax k⊆cornerGamma k := by
  intro h
  have hk := h (Finset.mem_union_left _ (cornerPairL_mem k))
  have hn : k∉cornerGamma k := by
    simp only [cornerGamma,Finset.mem_symmDiff,cornerPairL_mem,cornerPairR_mem,not_true_eq_false,and_false,or_self,not_false_eq_true]
  exact hn hk

private instance certificate_instance_1145 : OAI.SidorenkoCounterexample.ProofCertificate_1145 := by
  constructor
  intro q0
  exact @certificate_proof_1145 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1146 : cornerMax (2,0) ∩ cornerMax (2,1) ∩ cornerMax (3,0) ∩ cornerMax (3,1)=pairCorners 0 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1146 : OAI.SidorenkoCounterexample.ProofCertificate_1146 := by
  constructor
  exact @certificate_proof_1146 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1147 (k : ActCorner) : (∀ b∈pairCorners 0,k∈cornerMax b) ↔ k∈pairCorners 0 := by
  have h := Finset.ext_iff.mp supportIntersect_0 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_0] at h ⊢
  change (∀ b∈{(2,0),(2,1),(3,0),(3,1)},k∈cornerMax b) ↔ k∈pairCornerTable 0
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1147 : OAI.SidorenkoCounterexample.ProofCertificate_1147 := by
  constructor
  intro q0
  exact @certificate_proof_1147 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1148 : cornerMax (0,0) ∩ cornerMax (0,2) ∩ cornerMax (2,0) ∩ cornerMax (2,2)=pairCorners 1 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1148 : OAI.SidorenkoCounterexample.ProofCertificate_1148 := by
  constructor
  exact @certificate_proof_1148 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1149 (k : ActCorner) : (∀ b∈pairCorners 1,k∈cornerMax b) ↔ k∈pairCorners 1 := by
  have h := Finset.ext_iff.mp supportIntersect_1 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_1] at h ⊢
  change (∀ b∈{(0,0),(0,2),(2,0),(2,2)},k∈cornerMax b) ↔ k∈pairCornerTable 1
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1149 : OAI.SidorenkoCounterexample.ProofCertificate_1149 := by
  constructor
  intro q0
  exact @certificate_proof_1149 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1150 : cornerMax (2,1) ∩ cornerMax (2,2) ∩ cornerMax (8,0) ∩ cornerMax (8,1)=pairCorners 2 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1150 : OAI.SidorenkoCounterexample.ProofCertificate_1150 := by
  constructor
  exact @certificate_proof_1150 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1151 (k : ActCorner) : (∀ b∈pairCorners 2,k∈cornerMax b) ↔ k∈pairCorners 2 := by
  have h := Finset.ext_iff.mp supportIntersect_2 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_2] at h ⊢
  change (∀ b∈{(2,1),(2,2),(8,0),(8,1)},k∈cornerMax b) ↔ k∈pairCornerTable 2
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1151 : OAI.SidorenkoCounterexample.ProofCertificate_1151 := by
  constructor
  intro q0
  exact @certificate_proof_1151 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1152 : cornerMax (1,0) ∩ cornerMax (1,2) ∩ cornerMax (3,0) ∩ cornerMax (3,2)=pairCorners 3 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1152 : OAI.SidorenkoCounterexample.ProofCertificate_1152 := by
  constructor
  exact @certificate_proof_1152 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1153 (k : ActCorner) : (∀ b∈pairCorners 3,k∈cornerMax b) ↔ k∈pairCorners 3 := by
  have h := Finset.ext_iff.mp supportIntersect_3 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_3] at h ⊢
  change (∀ b∈{(1,0),(1,2),(3,0),(3,2)},k∈cornerMax b) ↔ k∈pairCornerTable 3
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1153 : OAI.SidorenkoCounterexample.ProofCertificate_1153 := by
  constructor
  intro q0
  exact @certificate_proof_1153 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1154 : cornerMax (3,1) ∩ cornerMax (3,2) ∩ cornerMax (9,0) ∩ cornerMax (9,2)=pairCorners 4 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1154 : OAI.SidorenkoCounterexample.ProofCertificate_1154 := by
  constructor
  exact @certificate_proof_1154 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1155 (k : ActCorner) : (∀ b∈pairCorners 4,k∈cornerMax b) ↔ k∈pairCorners 4 := by
  have h := Finset.ext_iff.mp supportIntersect_4 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_4] at h ⊢
  change (∀ b∈{(3,1),(3,2),(9,0),(9,2)},k∈cornerMax b) ↔ k∈pairCornerTable 4
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1155 : OAI.SidorenkoCounterexample.ProofCertificate_1155 := by
  constructor
  intro q0
  exact @certificate_proof_1155 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1156 : cornerMax (0,0) ∩ cornerMax (0,1) ∩ cornerMax (1,0) ∩ cornerMax (1,1)=pairCorners 5 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1156 : OAI.SidorenkoCounterexample.ProofCertificate_1156 := by
  constructor
  exact @certificate_proof_1156 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1157 (k : ActCorner) : (∀ b∈pairCorners 5,k∈cornerMax b) ↔ k∈pairCorners 5 := by
  have h := Finset.ext_iff.mp supportIntersect_5 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_5] at h ⊢
  change (∀ b∈{(0,0),(0,1),(1,0),(1,1)},k∈cornerMax b) ↔ k∈pairCornerTable 5
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1157 : OAI.SidorenkoCounterexample.ProofCertificate_1157 := by
  constructor
  intro q0
  exact @certificate_proof_1157 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1158 : cornerMax (0,1) ∩ cornerMax (0,2) ∩ cornerMax (4,0) ∩ cornerMax (4,1)=pairCorners 6 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1158 : OAI.SidorenkoCounterexample.ProofCertificate_1158 := by
  constructor
  exact @certificate_proof_1158 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1159 (k : ActCorner) : (∀ b∈pairCorners 6,k∈cornerMax b) ↔ k∈pairCorners 6 := by
  have h := Finset.ext_iff.mp supportIntersect_6 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_6] at h ⊢
  change (∀ b∈{(0,1),(0,2),(4,0),(4,1)},k∈cornerMax b) ↔ k∈pairCornerTable 6
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1159 : OAI.SidorenkoCounterexample.ProofCertificate_1159 := by
  constructor
  intro q0
  exact @certificate_proof_1159 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1160 : cornerMax (8,0) ∩ cornerMax (8,2) ∩ cornerMax (9,0) ∩ cornerMax (9,1)=pairCorners 7 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1160 : OAI.SidorenkoCounterexample.ProofCertificate_1160 := by
  constructor
  exact @certificate_proof_1160 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1161 (k : ActCorner) : (∀ b∈pairCorners 7,k∈cornerMax b) ↔ k∈pairCorners 7 := by
  have h := Finset.ext_iff.mp supportIntersect_7 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_7] at h ⊢
  change (∀ b∈{(8,0),(8,2),(9,0),(9,1)},k∈cornerMax b) ↔ k∈pairCornerTable 7
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1161 : OAI.SidorenkoCounterexample.ProofCertificate_1161 := by
  constructor
  intro q0
  exact @certificate_proof_1161 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1162 : cornerMax (8,1) ∩ cornerMax (8,2) ∩ cornerMax (10,0) ∩ cornerMax (10,1)=pairCorners 8 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1162 : OAI.SidorenkoCounterexample.ProofCertificate_1162 := by
  constructor
  exact @certificate_proof_1162 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1163 (k : ActCorner) : (∀ b∈pairCorners 8,k∈cornerMax b) ↔ k∈pairCorners 8 := by
  have h := Finset.ext_iff.mp supportIntersect_8 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_8] at h ⊢
  change (∀ b∈{(8,1),(8,2),(10,0),(10,1)},k∈cornerMax b) ↔ k∈pairCornerTable 8
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1163 : OAI.SidorenkoCounterexample.ProofCertificate_1163 := by
  constructor
  intro q0
  exact @certificate_proof_1163 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1164 : cornerMax (1,1) ∩ cornerMax (1,2) ∩ cornerMax (7,0) ∩ cornerMax (7,1)=pairCorners 9 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1164 : OAI.SidorenkoCounterexample.ProofCertificate_1164 := by
  constructor
  exact @certificate_proof_1164 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1165 (k : ActCorner) : (∀ b∈pairCorners 9,k∈cornerMax b) ↔ k∈pairCorners 9 := by
  have h := Finset.ext_iff.mp supportIntersect_9 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_9] at h ⊢
  change (∀ b∈{(1,1),(1,2),(7,0),(7,1)},k∈cornerMax b) ↔ k∈pairCornerTable 9
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1165 : OAI.SidorenkoCounterexample.ProofCertificate_1165 := by
  constructor
  intro q0
  exact @certificate_proof_1165 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1166 : cornerMax (9,1) ∩ cornerMax (9,2) ∩ cornerMax (12,0) ∩ cornerMax (12,2)=pairCorners 10 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1166 : OAI.SidorenkoCounterexample.ProofCertificate_1166 := by
  constructor
  exact @certificate_proof_1166 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1167 (k : ActCorner) : (∀ b∈pairCorners 10,k∈cornerMax b) ↔ k∈pairCorners 10 := by
  have h := Finset.ext_iff.mp supportIntersect_10 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_10] at h ⊢
  change (∀ b∈{(9,1),(9,2),(12,0),(12,2)},k∈cornerMax b) ↔ k∈pairCornerTable 10
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1167 : OAI.SidorenkoCounterexample.ProofCertificate_1167 := by
  constructor
  intro q0
  exact @certificate_proof_1167 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1168 : cornerMax (4,0) ∩ cornerMax (4,2) ∩ cornerMax (5,0) ∩ cornerMax (5,2)=pairCorners 11 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1168 : OAI.SidorenkoCounterexample.ProofCertificate_1168 := by
  constructor
  exact @certificate_proof_1168 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1169 (k : ActCorner) : (∀ b∈pairCorners 11,k∈cornerMax b) ↔ k∈pairCorners 11 := by
  have h := Finset.ext_iff.mp supportIntersect_11 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_11] at h ⊢
  change (∀ b∈{(4,0),(4,2),(5,0),(5,2)},k∈cornerMax b) ↔ k∈pairCornerTable 11
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1169 : OAI.SidorenkoCounterexample.ProofCertificate_1169 := by
  constructor
  intro q0
  exact @certificate_proof_1169 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1170 : cornerMax (4,1) ∩ cornerMax (4,2) ∩ cornerMax (11,0) ∩ cornerMax (11,1)=pairCorners 12 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1170 : OAI.SidorenkoCounterexample.ProofCertificate_1170 := by
  constructor
  exact @certificate_proof_1170 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1171 (k : ActCorner) : (∀ b∈pairCorners 12,k∈cornerMax b) ↔ k∈pairCorners 12 := by
  have h := Finset.ext_iff.mp supportIntersect_12 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_12] at h ⊢
  change (∀ b∈{(4,1),(4,2),(11,0),(11,1)},k∈cornerMax b) ↔ k∈pairCornerTable 12
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1171 : OAI.SidorenkoCounterexample.ProofCertificate_1171 := by
  constructor
  intro q0
  exact @certificate_proof_1171 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1172 : cornerMax (10,0) ∩ cornerMax (10,2) ∩ cornerMax (11,0) ∩ cornerMax (11,2)=pairCorners 13 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1172 : OAI.SidorenkoCounterexample.ProofCertificate_1172 := by
  constructor
  exact @certificate_proof_1172 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1173 (k : ActCorner) : (∀ b∈pairCorners 13,k∈cornerMax b) ↔ k∈pairCorners 13 := by
  have h := Finset.ext_iff.mp supportIntersect_13 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_13] at h ⊢
  change (∀ b∈{(10,0),(10,2),(11,0),(11,2)},k∈cornerMax b) ↔ k∈pairCornerTable 13
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1173 : OAI.SidorenkoCounterexample.ProofCertificate_1173 := by
  constructor
  intro q0
  exact @certificate_proof_1173 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1174 : cornerMax (10,1) ∩ cornerMax (10,2) ∩ cornerMax (13,0) ∩ cornerMax (13,2)=pairCorners 14 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1174 : OAI.SidorenkoCounterexample.ProofCertificate_1174 := by
  constructor
  exact @certificate_proof_1174 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1175 (k : ActCorner) : (∀ b∈pairCorners 14,k∈cornerMax b) ↔ k∈pairCorners 14 := by
  have h := Finset.ext_iff.mp supportIntersect_14 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_14] at h ⊢
  change (∀ b∈{(10,1),(10,2),(13,0),(13,2)},k∈cornerMax b) ↔ k∈pairCornerTable 14
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1175 : OAI.SidorenkoCounterexample.ProofCertificate_1175 := by
  constructor
  intro q0
  exact @certificate_proof_1175 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1176 : cornerMax (6,0) ∩ cornerMax (6,2) ∩ cornerMax (7,0) ∩ cornerMax (7,2)=pairCorners 15 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1176 : OAI.SidorenkoCounterexample.ProofCertificate_1176 := by
  constructor
  exact @certificate_proof_1176 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1177 (k : ActCorner) : (∀ b∈pairCorners 15,k∈cornerMax b) ↔ k∈pairCorners 15 := by
  have h := Finset.ext_iff.mp supportIntersect_15 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_15] at h ⊢
  change (∀ b∈{(6,0),(6,2),(7,0),(7,2)},k∈cornerMax b) ↔ k∈pairCornerTable 15
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1177 : OAI.SidorenkoCounterexample.ProofCertificate_1177 := by
  constructor
  intro q0
  exact @certificate_proof_1177 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1178 : cornerMax (7,1) ∩ cornerMax (7,2) ∩ cornerMax (21,1) ∩ cornerMax (21,2)=pairCorners 16 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1178 : OAI.SidorenkoCounterexample.ProofCertificate_1178 := by
  constructor
  exact @certificate_proof_1178 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1179 (k : ActCorner) : (∀ b∈pairCorners 16,k∈cornerMax b) ↔ k∈pairCorners 16 := by
  have h := Finset.ext_iff.mp supportIntersect_16 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_16] at h ⊢
  change (∀ b∈{(7,1),(7,2),(21,1),(21,2)},k∈cornerMax b) ↔ k∈pairCornerTable 16
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1179 : OAI.SidorenkoCounterexample.ProofCertificate_1179 := by
  constructor
  intro q0
  exact @certificate_proof_1179 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1180 : cornerMax (12,0) ∩ cornerMax (12,1) ∩ cornerMax (13,0) ∩ cornerMax (13,1)=pairCorners 17 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1180 : OAI.SidorenkoCounterexample.ProofCertificate_1180 := by
  constructor
  exact @certificate_proof_1180 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1181 (k : ActCorner) : (∀ b∈pairCorners 17,k∈cornerMax b) ↔ k∈pairCorners 17 := by
  have h := Finset.ext_iff.mp supportIntersect_17 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_17] at h ⊢
  change (∀ b∈{(12,0),(12,1),(13,0),(13,1)},k∈cornerMax b) ↔ k∈pairCornerTable 17
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1181 : OAI.SidorenkoCounterexample.ProofCertificate_1181 := by
  constructor
  intro q0
  exact @certificate_proof_1181 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1182 : cornerMax (12,1) ∩ cornerMax (12,2) ∩ cornerMax (21,0) ∩ cornerMax (21,1)=pairCorners 18 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1182 : OAI.SidorenkoCounterexample.ProofCertificate_1182 := by
  constructor
  exact @certificate_proof_1182 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1183 (k : ActCorner) : (∀ b∈pairCorners 18,k∈cornerMax b) ↔ k∈pairCorners 18 := by
  have h := Finset.ext_iff.mp supportIntersect_18 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_18] at h ⊢
  change (∀ b∈{(12,1),(12,2),(21,0),(21,1)},k∈cornerMax b) ↔ k∈pairCornerTable 18
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1183 : OAI.SidorenkoCounterexample.ProofCertificate_1183 := by
  constructor
  intro q0
  exact @certificate_proof_1183 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1184 : cornerMax (5,0) ∩ cornerMax (5,1) ∩ cornerMax (6,0) ∩ cornerMax (6,1)=pairCorners 19 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1184 : OAI.SidorenkoCounterexample.ProofCertificate_1184 := by
  constructor
  exact @certificate_proof_1184 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

lemma certificate_proof_1185 (k : ActCorner) : (∀ b∈pairCorners 19,k∈cornerMax b) ↔ k∈pairCorners 19 := by
  have h := Finset.ext_iff.mp supportIntersect_19 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_19] at h ⊢
  change (∀ b∈{(5,0),(5,1),(6,0),(6,1)},k∈cornerMax b) ↔ k∈pairCornerTable 19
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1185 : OAI.SidorenkoCounterexample.ProofCertificate_1185 := by
  constructor
  intro q0
  exact @certificate_proof_1185 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77 q0

lemma certificate_proof_1186 : cornerMax (5,1) ∩ cornerMax (5,2) ∩ cornerMax (16,1) ∩ cornerMax (16,2)=pairCorners 20 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1186 : OAI.SidorenkoCounterexample.ProofCertificate_1186 := by
  constructor
  exact @certificate_proof_1186 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69 p70 p71 p72 p73 p74 p75 p76 p77

end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_1130 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1131 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1132 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1133 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1134 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1135 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1136 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1137 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1138 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1139 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1140 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1141 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1142 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1143 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1144 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1145 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1146 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1147 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1148 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1149 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1150 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1151 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1152 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1153 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1154 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1155 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1156 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1157 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1158 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1159 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1160 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1161 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1162 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1163 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1164 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1165 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1166 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1167 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1168 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1169 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1170 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1171 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1172 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1173 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1174 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1175 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1176 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1177 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1178 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1179 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1180 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1181 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1182 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1183 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1184 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1185 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1186 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

