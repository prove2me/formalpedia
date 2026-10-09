-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_35
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:39:54.730022+00:00
-- url     : https://prove2.me/submissions/7f99b7c3-54c6-4c44-b87a-ac1b70c28372

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0375]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0378]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0379]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0380]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0656]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0657]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0659]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0925]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_1022]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_1025]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_1029]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_1034]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_1035]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_1036]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_1037]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_1038]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_1059]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_1060]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_1061]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_1062]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_1063]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_1064]
  [p22 : OAI.SidorenkoCounterexample.ProofCertificate_1065]
  [p23 : OAI.SidorenkoCounterexample.ProofCertificate_1066]
  [p24 : OAI.SidorenkoCounterexample.ProofCertificate_1067]
  [p25 : OAI.SidorenkoCounterexample.ProofCertificate_1068]
  [p26 : OAI.SidorenkoCounterexample.ProofCertificate_1069]
  [p27 : OAI.SidorenkoCounterexample.ProofCertificate_1070]
  [p28 : OAI.SidorenkoCounterexample.ProofCertificate_1071]
  [p29 : OAI.SidorenkoCounterexample.ProofCertificate_1072]
  [p30 : OAI.SidorenkoCounterexample.ProofCertificate_1140]
  [p31 : OAI.SidorenkoCounterexample.ProofCertificate_1141]
  [p32 : OAI.SidorenkoCounterexample.ProofCertificate_1144]
  [p33 : OAI.SidorenkoCounterexample.ProofCertificate_1145]
  [p34 : OAI.SidorenkoCounterexample.ProofCertificate_1147]
  [p35 : OAI.SidorenkoCounterexample.ProofCertificate_1149]
  [p36 : OAI.SidorenkoCounterexample.ProofCertificate_1151]
  [p37 : OAI.SidorenkoCounterexample.ProofCertificate_1153]
  [p38 : OAI.SidorenkoCounterexample.ProofCertificate_1155]
  [p39 : OAI.SidorenkoCounterexample.ProofCertificate_1157]
  [p40 : OAI.SidorenkoCounterexample.ProofCertificate_1159]
  [p41 : OAI.SidorenkoCounterexample.ProofCertificate_1161]
  [p42 : OAI.SidorenkoCounterexample.ProofCertificate_1163]
  [p43 : OAI.SidorenkoCounterexample.ProofCertificate_1165]
  [p44 : OAI.SidorenkoCounterexample.ProofCertificate_1167]
  [p45 : OAI.SidorenkoCounterexample.ProofCertificate_1169]
  [p46 : OAI.SidorenkoCounterexample.ProofCertificate_1171]
  [p47 : OAI.SidorenkoCounterexample.ProofCertificate_1173]
  [p48 : OAI.SidorenkoCounterexample.ProofCertificate_1175]
  [p49 : OAI.SidorenkoCounterexample.ProofCertificate_1177]
  [p50 : OAI.SidorenkoCounterexample.ProofCertificate_1179]
  [p51 : OAI.SidorenkoCounterexample.ProofCertificate_1181]
  [p52 : OAI.SidorenkoCounterexample.ProofCertificate_1183]
  [p53 : OAI.SidorenkoCounterexample.ProofCertificate_1185]
  [p54 : OAI.SidorenkoCounterexample.ProofCertificate_1186]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
lemma certificate_proof_1187 (k : ActCorner) : (∀ b∈pairCorners 20,k∈cornerMax b) ↔ k∈pairCorners 20 := by
  have h := Finset.ext_iff.mp supportIntersect_20 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_20] at h ⊢
  change (∀ b∈{(5,1),(5,2),(16,1),(16,2)},k∈cornerMax b) ↔ k∈pairCornerTable 20
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1187 : OAI.SidorenkoCounterexample.ProofCertificate_1187 := by
  constructor
  intro q0
  exact @certificate_proof_1187 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1188 : cornerMax (11,1) ∩ cornerMax (11,2) ∩ cornerMax (17,1) ∩ cornerMax (17,2)=pairCorners 21 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1188 : OAI.SidorenkoCounterexample.ProofCertificate_1188 := by
  constructor
  exact @certificate_proof_1188 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1189 (k : ActCorner) : (∀ b∈pairCorners 21,k∈cornerMax b) ↔ k∈pairCorners 21 := by
  have h := Finset.ext_iff.mp supportIntersect_21 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_21] at h ⊢
  change (∀ b∈{(11,1),(11,2),(17,1),(17,2)},k∈cornerMax b) ↔ k∈pairCornerTable 21
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1189 : OAI.SidorenkoCounterexample.ProofCertificate_1189 := by
  constructor
  intro q0
  exact @certificate_proof_1189 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1190 : cornerMax (13,1) ∩ cornerMax (13,2) ∩ cornerMax (19,1) ∩ cornerMax (19,2)=pairCorners 22 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1190 : OAI.SidorenkoCounterexample.ProofCertificate_1190 := by
  constructor
  exact @certificate_proof_1190 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1191 (k : ActCorner) : (∀ b∈pairCorners 22,k∈cornerMax b) ↔ k∈pairCorners 22 := by
  have h := Finset.ext_iff.mp supportIntersect_22 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_22] at h ⊢
  change (∀ b∈{(13,1),(13,2),(19,1),(19,2)},k∈cornerMax b) ↔ k∈pairCornerTable 22
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1191 : OAI.SidorenkoCounterexample.ProofCertificate_1191 := by
  constructor
  intro q0
  exact @certificate_proof_1191 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1192 : cornerMax (6,1) ∩ cornerMax (6,2) ∩ cornerMax (18,1) ∩ cornerMax (18,2)=pairCorners 23 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1192 : OAI.SidorenkoCounterexample.ProofCertificate_1192 := by
  constructor
  exact @certificate_proof_1192 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1193 (k : ActCorner) : (∀ b∈pairCorners 23,k∈cornerMax b) ↔ k∈pairCorners 23 := by
  have h := Finset.ext_iff.mp supportIntersect_23 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_23] at h ⊢
  change (∀ b∈{(6,1),(6,2),(18,1),(18,2)},k∈cornerMax b) ↔ k∈pairCornerTable 23
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1193 : OAI.SidorenkoCounterexample.ProofCertificate_1193 := by
  constructor
  intro q0
  exact @certificate_proof_1193 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1194 : cornerMax (20,1) ∩ cornerMax (20,2) ∩ cornerMax (21,0) ∩ cornerMax (21,2)=pairCorners 24 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1194 : OAI.SidorenkoCounterexample.ProofCertificate_1194 := by
  constructor
  exact @certificate_proof_1194 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1195 (k : ActCorner) : (∀ b∈pairCorners 24,k∈cornerMax b) ↔ k∈pairCorners 24 := by
  have h := Finset.ext_iff.mp supportIntersect_24 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_24] at h ⊢
  change (∀ b∈{(20,1),(20,2),(21,0),(21,2)},k∈cornerMax b) ↔ k∈pairCornerTable 24
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1195 : OAI.SidorenkoCounterexample.ProofCertificate_1195 := by
  constructor
  intro q0
  exact @certificate_proof_1195 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1196 : cornerMax (14,0) ∩ cornerMax (14,2) ∩ cornerMax (16,0) ∩ cornerMax (16,1)=pairCorners 25 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1196 : OAI.SidorenkoCounterexample.ProofCertificate_1196 := by
  constructor
  exact @certificate_proof_1196 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1197 (k : ActCorner) : (∀ b∈pairCorners 25,k∈cornerMax b) ↔ k∈pairCorners 25 := by
  have h := Finset.ext_iff.mp supportIntersect_25 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_25] at h ⊢
  change (∀ b∈{(14,0),(14,2),(16,0),(16,1)},k∈cornerMax b) ↔ k∈pairCornerTable 25
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1197 : OAI.SidorenkoCounterexample.ProofCertificate_1197 := by
  constructor
  intro q0
  exact @certificate_proof_1197 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1198 : cornerMax (16,0) ∩ cornerMax (16,2) ∩ cornerMax (17,0) ∩ cornerMax (17,1)=pairCorners 26 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1198 : OAI.SidorenkoCounterexample.ProofCertificate_1198 := by
  constructor
  exact @certificate_proof_1198 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1199 (k : ActCorner) : (∀ b∈pairCorners 26,k∈cornerMax b) ↔ k∈pairCorners 26 := by
  have h := Finset.ext_iff.mp supportIntersect_26 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_26] at h ⊢
  change (∀ b∈{(16,0),(16,2),(17,0),(17,1)},k∈cornerMax b) ↔ k∈pairCornerTable 26
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1199 : OAI.SidorenkoCounterexample.ProofCertificate_1199 := by
  constructor
  intro q0
  exact @certificate_proof_1199 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1200 : cornerMax (15,0) ∩ cornerMax (15,2) ∩ cornerMax (17,0) ∩ cornerMax (17,2)=pairCorners 27 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1200 : OAI.SidorenkoCounterexample.ProofCertificate_1200 := by
  constructor
  exact @certificate_proof_1200 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1201 (k : ActCorner) : (∀ b∈pairCorners 27,k∈cornerMax b) ↔ k∈pairCorners 27 := by
  have h := Finset.ext_iff.mp supportIntersect_27 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_27] at h ⊢
  change (∀ b∈{(15,0),(15,2),(17,0),(17,2)},k∈cornerMax b) ↔ k∈pairCornerTable 27
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1201 : OAI.SidorenkoCounterexample.ProofCertificate_1201 := by
  constructor
  intro q0
  exact @certificate_proof_1201 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1202 : cornerMax (19,0) ∩ cornerMax (19,1) ∩ cornerMax (20,0) ∩ cornerMax (20,1)=pairCorners 28 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1202 : OAI.SidorenkoCounterexample.ProofCertificate_1202 := by
  constructor
  exact @certificate_proof_1202 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1203 (k : ActCorner) : (∀ b∈pairCorners 28,k∈cornerMax b) ↔ k∈pairCorners 28 := by
  have h := Finset.ext_iff.mp supportIntersect_28 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_28] at h ⊢
  change (∀ b∈{(19,0),(19,1),(20,0),(20,1)},k∈cornerMax b) ↔ k∈pairCornerTable 28
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1203 : OAI.SidorenkoCounterexample.ProofCertificate_1203 := by
  constructor
  intro q0
  exact @certificate_proof_1203 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1204 : cornerMax (15,1) ∩ cornerMax (15,2) ∩ cornerMax (19,0) ∩ cornerMax (19,2)=pairCorners 29 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1204 : OAI.SidorenkoCounterexample.ProofCertificate_1204 := by
  constructor
  exact @certificate_proof_1204 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1205 (k : ActCorner) : (∀ b∈pairCorners 29,k∈cornerMax b) ↔ k∈pairCorners 29 := by
  have h := Finset.ext_iff.mp supportIntersect_29 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_29] at h ⊢
  change (∀ b∈{(15,1),(15,2),(19,0),(19,2)},k∈cornerMax b) ↔ k∈pairCornerTable 29
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1205 : OAI.SidorenkoCounterexample.ProofCertificate_1205 := by
  constructor
  intro q0
  exact @certificate_proof_1205 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1206 : cornerMax (14,1) ∩ cornerMax (14,2) ∩ cornerMax (18,0) ∩ cornerMax (18,1)=pairCorners 30 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1206 : OAI.SidorenkoCounterexample.ProofCertificate_1206 := by
  constructor
  exact @certificate_proof_1206 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1207 (k : ActCorner) : (∀ b∈pairCorners 30,k∈cornerMax b) ↔ k∈pairCorners 30 := by
  have h := Finset.ext_iff.mp supportIntersect_30 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_30] at h ⊢
  change (∀ b∈{(14,1),(14,2),(18,0),(18,1)},k∈cornerMax b) ↔ k∈pairCornerTable 30
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1207 : OAI.SidorenkoCounterexample.ProofCertificate_1207 := by
  constructor
  intro q0
  exact @certificate_proof_1207 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1208 : cornerMax (18,0) ∩ cornerMax (18,2) ∩ cornerMax (20,0) ∩ cornerMax (20,2)=pairCorners 31 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1208 : OAI.SidorenkoCounterexample.ProofCertificate_1208 := by
  constructor
  exact @certificate_proof_1208 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1209 (k : ActCorner) : (∀ b∈pairCorners 31,k∈cornerMax b) ↔ k∈pairCorners 31 := by
  have h := Finset.ext_iff.mp supportIntersect_31 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_31] at h ⊢
  change (∀ b∈{(18,0),(18,2),(20,0),(20,2)},k∈cornerMax b) ↔ k∈pairCornerTable 31
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1209 : OAI.SidorenkoCounterexample.ProofCertificate_1209 := by
  constructor
  intro q0
  exact @certificate_proof_1209 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1210 : cornerMax (14,0) ∩ cornerMax (14,1) ∩ cornerMax (15,0) ∩ cornerMax (15,1)=pairCorners 32 := by
  simp only [cornerMax,pairCorners_table]
  decide

private instance certificate_instance_1210 : OAI.SidorenkoCounterexample.ProofCertificate_1210 := by
  constructor
  exact @certificate_proof_1210 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1211 (k : ActCorner) : (∀ b∈pairCorners 32,k∈cornerMax b) ↔ k∈pairCorners 32 := by
  have h := Finset.ext_iff.mp supportIntersect_32 k
  simp only [Finset.mem_inter] at h
  rw [pairCorners_table_32] at h ⊢
  change (∀ b∈{(14,0),(14,1),(15,0),(15,1)},k∈cornerMax b) ↔ k∈pairCornerTable 32
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  tauto

private instance certificate_instance_1211 : OAI.SidorenkoCounterexample.ProofCertificate_1211 := by
  constructor
  intro q0
  exact @certificate_proof_1211 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

theorem certificate_proof_1212 (e : Fin 33) (k : ActCorner) : (∀ b∈pairCorners e,k∈cornerMax b) ↔ k∈pairCorners e := by
  fin_cases e
  · exact corner_support_0 k
  · exact corner_support_1 k
  · exact corner_support_2 k
  · exact corner_support_3 k
  · exact corner_support_4 k
  · exact corner_support_5 k
  · exact corner_support_6 k
  · exact corner_support_7 k
  · exact corner_support_8 k
  · exact corner_support_9 k
  · exact corner_support_10 k
  · exact corner_support_11 k
  · exact corner_support_12 k
  · exact corner_support_13 k
  · exact corner_support_14 k
  · exact corner_support_15 k
  · exact corner_support_16 k
  · exact corner_support_17 k
  · exact corner_support_18 k
  · exact corner_support_19 k
  · exact corner_support_20 k
  · exact corner_support_21 k
  · exact corner_support_22 k
  · exact corner_support_23 k
  · exact corner_support_24 k
  · exact corner_support_25 k
  · exact corner_support_26 k
  · exact corner_support_27 k
  · exact corner_support_28 k
  · exact corner_support_29 k
  · exact corner_support_30 k
  · exact corner_support_31 k
  · exact corner_support_32 k

private instance certificate_instance_1212 : OAI.SidorenkoCounterexample.ProofCertificate_1212 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1212 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1

theorem certificate_proof_1213 (k : ActCorner) : cornerGamma k⊆cornerMax k :=
  Finset.symmDiff_subset_union

private instance certificate_instance_1213 : OAI.SidorenkoCounterexample.ProofCertificate_1213 := by
  constructor
  intro q0
  exact @certificate_proof_1213 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1214 (k : ActCorner) : |cornerSigma k|=1 := by unfold cornerSigma; split <;> norm_num

private instance certificate_instance_1214 : OAI.SidorenkoCounterexample.ProofCertificate_1214 := by
  constructor
  intro q0
  exact @certificate_proof_1214 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1215 (k : ActCorner) (α : Finset ActCorner) (hα : α≠∅) :
    (cornerLaw k).mean (activationPhi α)=0 :=
  baseActivation_zero _ _ _ _ (cornerGamma_sub k) _ _ hα

private instance certificate_instance_1215 : OAI.SidorenkoCounterexample.ProofCertificate_1215 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 q0 q1 q2
  exact @certificate_proof_1215 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2

lemma certificate_proof_1216 (k : ActCorner) (α β : Finset ActCorner) :
    activationMoment (cornerLaw k) α β=
    (1/2)*(if α∪β⊆cornerMax k then (if α=β then 1 else 0)+(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0)+
    (1/2)*(if α∪β⊆cornerGamma k then (if α=β then 1 else 0)-(cornerSigma k/2)*(if α ∆ β=cornerGamma k then 1 else 0) else 0) :=
  baseActivation_moment ..

private instance certificate_instance_1216 : OAI.SidorenkoCounterexample.ProofCertificate_1216 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 q0 q1 q2
  exact @certificate_proof_1216 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2

lemma certificate_proof_1217 (k : ActCorner) (α β : Finset ActCorner)
    (h : activationMoment (cornerLaw k) α β≠0) : α∪β⊆cornerMax k := by
  by_contra hn
  have hn' : ¬α∪β⊆cornerGamma k := fun h => hn (h.trans (cornerGamma_sub k))
  rw [cornerLaw_moment] at h
  simp only [hn,hn',ite_false,mul_zero,add_zero,ne_self_iff_false] at h

private instance certificate_instance_1217 : OAI.SidorenkoCounterexample.ProofCertificate_1217 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 q0 q1 q2 q3
  exact @certificate_proof_1217 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3

lemma certificate_proof_1218 (k : ActCorner) (α β : Finset ActCorner)
    (hd : Disjoint α β) (hn : α∪β≠∅) : activationMoment (cornerLaw k) α β=0 :=
  activationMoment_disjoint _ (cornerLaw_zero k) α β hd hn

private instance certificate_instance_1218 : OAI.SidorenkoCounterexample.ProofCertificate_1218 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 q0 q1 q2 q3 q4
  exact @certificate_proof_1218 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3 q4

lemma certificate_proof_1219 (k : ActCorner) :
    activationMoment (cornerLaw k) (pairCorners (cornerPairL k)) (pairCorners (cornerPairR k))=cornerSigma k/4 := by
  have hn : pairCorners (cornerPairL k)≠pairCorners (cornerPairR k) := by
    intro h
    have hi := pairCorners_inter k
    rw [h,Finset.inter_self] at hi
    have hc := pairCorners_card (cornerPairR k)
    rw [hi] at hc
    simp at hc
  rw [cornerLaw_moment]
  change (1/2)*(if cornerMax k⊆cornerMax k then (if _ then 1 else 0)+(cornerSigma k/2)*(if cornerGamma k=cornerGamma k then 1 else 0) else 0)+
    (1/2)*(if cornerMax k⊆cornerGamma k then (if _ then 1 else 0)-(cornerSigma k/2)*(if cornerGamma k=cornerGamma k then 1 else 0) else 0)=_
  simp only [le_refl,ite_true,hn,ite_false,cornerMax_not_sub,mul_one,zero_add,mul_zero,add_zero]
  ring

private instance certificate_instance_1219 : OAI.SidorenkoCounterexample.ProofCertificate_1219 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 q0
  exact @certificate_proof_1219 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section Coefficients
variable {K : Type} [Fintype K] [DecidableEq K]
lemma certificate_proof_1220 (α : Fin 33 → Finset K) : α∈nonemptyLabels ↔ ∀ e,α e≠∅ := by
  simp only [nonemptyLabels,Finset.mem_filter,Finset.mem_univ,true_and]

private instance certificate_instance_1220 : OAI.SidorenkoCounterexample.ProofCertificate_1220 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1220 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3

omit [Fintype K] [DecidableEq K] in
lemma certificate_proof_1221 (A : ActCorner → Finset K → Finset K → ℝ) (α : Fin 33 → Finset K)
    (h : labelProduct A α≠0) (k : ActCorner) : A k (α (cornerPairL k)) (α (cornerPairR k))≠0 :=
  (Finset.prod_ne_zero_iff.mp h) k (Finset.mem_univ k)

private instance certificate_instance_1221 : OAI.SidorenkoCounterexample.ProofCertificate_1221 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1221 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3 q4

lemma certificate_proof_1222 (P : Fin 33 → Prop) (hs : ∀ j p q,P (facePair j p) ↔ P (facePair j q)) :
    ∀ e,P e ↔ P 0 := by
  have hstep (e : Fin 33) : P e ↔ P (pairParent e) := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    simpa only [hi,hk] using hs (pairBridge e) i k
  have hmain : ∀ m,∀ e : Fin 33,e.val=m → (P e ↔ P 0) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro e hem
      by_cases he : e=0
      · subst e; rfl
      · exact (hstep e).trans (ih _ (by simpa only [hem] using pairParent_lt e he) _ rfl)
  intro e; exact hmain e.val e rfl

private instance certificate_instance_1222 : OAI.SidorenkoCounterexample.ProofCertificate_1222 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_1222 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2

lemma certificate_proof_1223 (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) (α : Fin 33 → Finset K)
    (h : labelProduct (fun k => activationMoment (p k)) α≠0) :
    (∀ e,α e=∅) ∨ (∀ e,α e≠∅) := by
  have hs (k : ActCorner) : α (cornerPairL k)=∅ ↔ α (cornerPairR k)=∅ := by
    have hn := labelProduct_nonzero _ _ h k
    constructor
    · intro he
      by_contra hr
      rw [he,activationMoment] at hn
      simp only [activationPhi_empty,one_mul] at hn
      exact hn (hp k _ hr)
    · intro he
      by_contra hl
      rw [he,activationMoment] at hn
      simp only [activationPhi_empty,mul_one] at hn
      exact hn (hp k _ hl)
  have hf (j : Fin 22) (a b : Fin 3) : α (facePair j a)=∅ ↔ α (facePair j b)=∅ := by
    have h0 := hs (j,0); have h1 := hs (j,1); have h2 := hs (j,2)
    change (α (facePair j 0)=∅ ↔ α (facePair j 1)=∅) at h0
    change (α (facePair j 0)=∅ ↔ α (facePair j 2)=∅) at h1
    change (α (facePair j 1)=∅ ↔ α (facePair j 2)=∅) at h2
    fin_cases a <;> fin_cases b <;> tauto
  have ht := empty_propagation (fun e => α e=∅) hf
  by_cases hz : α 0=∅
  · exact Or.inl (fun e => (ht e).mpr hz)
  · exact Or.inr (fun e he => hz ((ht e).mp he))

private instance certificate_instance_1223 : OAI.SidorenkoCounterexample.ProofCertificate_1223 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1223 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3 q4 q5 q6

lemma certificate_proof_1224 (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) :
    (∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α)=
      1+activeCoefficient (fun k => activationMoment (p k)) := by
  classical
  let z : Fin 33 → Finset K := fun _ => ∅
  have hz : z∉(nonemptyLabels : Finset (Fin 33 → Finset K)) := by simp [nonemptyLabels,z]
  have hi : (insert z nonemptyLabels : Finset (Fin 33 → Finset K))⊆Finset.univ := Finset.subset_univ _
  have he := Finset.sum_subset hi (f := labelProduct (fun k => activationMoment (p k)))
  rw [←he,Finset.sum_insert hz]
  · simp [labelProduct,z,activeCoefficient]
  · intro α _ hα
    by_contra hn
    rcases labelProduct_empty_dichotomy p hp α hn with h|h
    · have : α=z := funext h
      exact hα (by simp [this])
    · exact hα (Finset.mem_insert_of_mem (by simpa [nonemptyLabels] using h))

private instance certificate_instance_1224 : OAI.SidorenkoCounterexample.ProofCertificate_1224 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_1224 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3 q4

lemma certificate_proof_1225 (A : ActCorner → Finset K → Finset K → ℝ)
    (α₀ : Fin 33 → Finset K) (h₀ : ∀ e,α₀ e≠∅)
    (hu : ∀ α,(∀ e,α e≠∅) → labelProduct A α≠0 → α=α₀) :
    activeCoefficient A=labelProduct A α₀ := by
  unfold activeCoefficient
  apply Finset.sum_eq_single α₀
  · intro α hα hne
    by_contra hn
    exact hne (hu α ((mem_nonemptyLabels α).mp hα) hn)
  · intro hn; exact (hn ((mem_nonemptyLabels α₀).mpr h₀)).elim

private instance certificate_instance_1225 : OAI.SidorenkoCounterexample.ProofCertificate_1225 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_1225 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3 q4 q5 q6

end Coefficients
lemma certificate_proof_1226 (α : Fin 33 → Finset ActCorner) (hne : ∀ e,α e≠∅)
    (h : labelProduct (fun k => activationMoment (cornerLaw k)) α≠0) : α=pairCorners := by
  have hl (k : ActCorner) := labelProduct_nonzero _ _ h k
  have hsub (e : Fin 33) : α e⊆pairCorners e := by
    intro k hk
    apply (corner_support e k).mp
    intro b hb
    have hs := cornerLaw_support b _ _ (hl b)
    rcases (pairCorners_mem b e).mp hb with hb|hb
    · exact hs (Finset.mem_union_left _ (by simpa only [hb] using hk))
    · exact hs (Finset.mem_union_right _ (by simpa only [hb] using hk))
  have hmem (k : ActCorner) : k∈α (cornerPairL k) ∧ k∈α (cornerPairR k) := by
    have hd : ¬Disjoint (α (cornerPairL k)) (α (cornerPairR k)) := by
      intro hd
      apply hl k
      exact cornerLaw_disjoint k _ _ hd (fun he => hne _ ((Finset.union_eq_empty.mp he).1))
    obtain ⟨b,hbl,hbr⟩ := Finset.not_disjoint_iff.mp hd
    have hb : b∈pairCorners (cornerPairL k) ∩ pairCorners (cornerPairR k) :=
      Finset.mem_inter.mpr ⟨hsub _ hbl,hsub _ hbr⟩
    rw [pairCorners_inter,Finset.mem_singleton] at hb
    simpa only [hb] using And.intro hbl hbr
  funext e
  apply Finset.Subset.antisymm (hsub e)
  intro k hk
  rcases (pairCorners_mem k e).mp hk with hk|hk
  · simpa only [hk] using (hmem k).1
  · simpa only [hk] using (hmem k).2

private instance certificate_instance_1226 : OAI.SidorenkoCounterexample.ProofCertificate_1226 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6 q0 q1 q2
  exact @certificate_proof_1226 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2

lemma certificate_proof_1227 : labelProduct (fun k => activationMoment (cornerLaw k)) pairCorners= -(1/4:ℝ)^66 := by
  unfold labelProduct
  simp_rw [cornerLaw_value,div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  have hs : (∏ k : ActCorner,cornerSigma k)= -1 := by
    rw [Finset.prod_eq_single (0,0)]
    · simp [cornerSigma]
    · intro b _ hb; simp [cornerSigma,hb]
    · simp
  rw [hs]
  simp [Fintype.card_prod]

private instance certificate_instance_1227 : OAI.SidorenkoCounterexample.ProofCertificate_1227 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6
  exact @certificate_proof_1227 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

lemma certificate_proof_1228 (e : Fin 33) : pairCorners e≠∅ := by
  intro he
  have := pairCorners_card e
  rw [he] at this
  simp at this

private instance certificate_instance_1228 : OAI.SidorenkoCounterexample.ProofCertificate_1228 := by
  constructor
  intro q0
  exact @certificate_proof_1228 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0

lemma certificate_proof_1229 : activeCoefficient (fun k => activationMoment (cornerLaw k))= -(1/4:ℝ)^66 := by
  rw [activeCoefficient_unique _ pairCorners pairCorners_nonempty identity_labels_forced]
  exact identity_labelProduct

private instance certificate_instance_1229 : OAI.SidorenkoCounterexample.ProofCertificate_1229 := by
  constructor
  intro c0 c1 c2 c3 c4 c5 c6
  exact @certificate_proof_1229 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type} [Fintype K] [DecidableEq K]
omit [Fintype K] in
lemma certificate_proof_1230 (α : Finset K) (z : Activation K) :
    activationPhi α z=∏ k∈α,activationEntry z k := by
  unfold activationPhi
  by_cases h : α⊆z.1
  · simp only [h,ite_true,boolMonomial]
    apply Finset.prod_congr rfl; intro k hk
    simp only [activationEntry,h hk,ite_true]
  · rw [if_neg h]
    obtain ⟨k,hk,hz⟩ := Finset.not_subset.mp h
    symm; apply Finset.prod_eq_zero hk
    simp only [activationEntry,hz,ite_false]

private instance certificate_instance_1230 : OAI.SidorenkoCounterexample.ProofCertificate_1230 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1230 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3

omit [Fintype K] in
lemma certificate_proof_1231 (z : Activation K) (k : K) : |activationEntry z k|≤1 := by
  unfold activationEntry; split <;> simp

private instance certificate_instance_1231 : OAI.SidorenkoCounterexample.ProofCertificate_1231 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_1231 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3

lemma certificate_proof_1232 (a b : ℝ) : uniformMean (fun η : Bool => (1+boolSign η*a)*(1+boolSign η*b))=1+a*b := by
  simp [uniformMean,Fintype.card_bool,boolSign]
  ring

private instance certificate_instance_1232 : OAI.SidorenkoCounterexample.ProofCertificate_1232 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1232 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1

omit [DecidableEq K] in
lemma certificate_proof_1233 {I : Type} [Fintype I] [DecidableEq I] (f : I → K → ℝ) :
    (∏ i,∏ k,(1+f i k))=∑ α : I → Finset K,∏ i,∏ k∈α i,f i k := by
  simp_rw [Finset.prod_one_add,Finset.powerset_univ]
  exact Fintype.prod_sum _

private instance certificate_instance_1233 : OAI.SidorenkoCounterexample.ProofCertificate_1233 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_1233 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1 q2 q3 q4 q5

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
theorem certificate_proof_1234 : ∀ e b,facePair (pairFace e b) (faceSlot e b)=e := by decide

private instance certificate_instance_1234 : OAI.SidorenkoCounterexample.ProofCertificate_1234 := by
  constructor
  intro q0 q1
  exact @certificate_proof_1234 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 q0 q1

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section
variable {I L A : Type} [Fintype I] [DecidableEq I] [Fintype L] [Fintype A]
end
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type} [Fintype K] [DecidableEq K]
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Expansion
variable {K : Type} [Fintype K] [DecidableEq K]
end Expansion
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Fubini
variable {I J K A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]
end Fubini
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Filter
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_1187 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1188 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1189 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1190 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1191 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1192 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1193 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1194 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1195 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1196 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1197 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1198 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1199 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1200 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1201 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1202 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1203 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1204 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1205 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1206 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1207 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1208 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1209 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1210 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1211 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1212 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1213 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1214 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1215 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1216 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1217 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1218 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1219 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1220 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1221 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1222 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1223 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1224 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1225 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1226 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1227 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1228 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1229 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1230 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1231 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1232 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1233 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_1234 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

