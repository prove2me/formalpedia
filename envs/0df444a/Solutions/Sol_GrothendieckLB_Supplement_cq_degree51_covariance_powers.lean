-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_degree51_covariance_powers
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:03:55.833128+00:00
-- url     : https://prove2.me/submissions/0d74866d-3ad4-46df-a3fd-aede54bbc6a1

import Definitions.Def_GrothendieckLB_Supplement_cqDegree51Tables
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
set_option Elab.async false
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 200000000
private theorem rhoStep {n p : Nat} {x xs y}
    (h : rhoPowers n p=xs) (hx : entry #[] xs p=x) (hy : rhoNext n x=y) :
    rhoPowers n (p+1) = xs.push y := by
  simp only [rhoPowers,h,hx,hy]
private noncomputable def rs0 := #[CQDegree51.r0.toArray]
private noncomputable def rs1 := rs0.push CQDegree51.r1.toArray
private noncomputable def rs2 := rs1.push CQDegree51.r2.toArray
private noncomputable def rs3 := rs2.push CQDegree51.r3.toArray
private noncomputable def rs4 := rs3.push CQDegree51.r4.toArray
private noncomputable def rs5 := rs4.push CQDegree51.r5.toArray
private noncomputable def rs6 := rs5.push CQDegree51.r6.toArray
private noncomputable def rs7 := rs6.push CQDegree51.r7.toArray
private noncomputable def rs8 := rs7.push CQDegree51.r8.toArray
private noncomputable def rs9 := rs8.push CQDegree51.r9.toArray
private noncomputable def rs10 := rs9.push CQDegree51.r10.toArray
private noncomputable def rs11 := rs10.push CQDegree51.r11.toArray
private noncomputable def rs12 := rs11.push CQDegree51.r12.toArray
private noncomputable def rs13 := rs12.push CQDegree51.r13.toArray
private noncomputable def rs14 := rs13.push CQDegree51.r14.toArray
private noncomputable def rs15 := rs14.push CQDegree51.r15.toArray
private noncomputable def rs16 := rs15.push CQDegree51.r16.toArray
private noncomputable def rs17 := rs16.push CQDegree51.r17.toArray
private noncomputable def rs18 := rs17.push CQDegree51.r18.toArray
private noncomputable def rs19 := rs18.push CQDegree51.r19.toArray
private noncomputable def rs20 := rs19.push CQDegree51.r20.toArray
private noncomputable def rs21 := rs20.push CQDegree51.r21.toArray
private noncomputable def rs22 := rs21.push CQDegree51.r22.toArray
private noncomputable def rs23 := rs22.push CQDegree51.r23.toArray
private noncomputable def rs24 := rs23.push CQDegree51.r24.toArray
private noncomputable def rs25 := rs24.push CQDegree51.r25.toArray
private noncomputable def rs26 := rs25.push CQDegree51.r26.toArray
private noncomputable def rs27 := rs26.push CQDegree51.r27.toArray
private noncomputable def rs28 := rs27.push CQDegree51.r28.toArray
private noncomputable def rs29 := rs28.push CQDegree51.r29.toArray
private noncomputable def rs30 := rs29.push CQDegree51.r30.toArray
private noncomputable def rs31 := rs30.push CQDegree51.r31.toArray
private noncomputable def rs32 := rs31.push CQDegree51.r32.toArray
private noncomputable def rs33 := rs32.push CQDegree51.r33.toArray
private noncomputable def rs34 := rs33.push CQDegree51.r34.toArray
private noncomputable def rs35 := rs34.push CQDegree51.r35.toArray
private noncomputable def rs36 := rs35.push CQDegree51.r36.toArray
private noncomputable def rs37 := rs36.push CQDegree51.r37.toArray
private noncomputable def rs38 := rs37.push CQDegree51.r38.toArray
private noncomputable def rs39 := rs38.push CQDegree51.r39.toArray
private noncomputable def rs40 := rs39.push CQDegree51.r40.toArray
private noncomputable def rs41 := rs40.push CQDegree51.r41.toArray
private noncomputable def rs42 := rs41.push CQDegree51.r42.toArray
private noncomputable def rs43 := rs42.push CQDegree51.r43.toArray
private noncomputable def rs44 := rs43.push CQDegree51.r44.toArray
private noncomputable def rs45 := rs44.push CQDegree51.r45.toArray
private noncomputable def rs46 := rs45.push CQDegree51.r46.toArray
private noncomputable def rs47 := rs46.push CQDegree51.r47.toArray
private noncomputable def rs48 := rs47.push CQDegree51.r48.toArray
private noncomputable def rs49 := rs48.push CQDegree51.r49.toArray
private noncomputable def rs50 := rs49.push CQDegree51.r50.toArray
private noncomputable def rs51 := rs50.push CQDegree51.r51.toArray
private theorem rbase : rhoPowers 51 0=rs0 := by decide +kernel
private theorem h1 : rhoPowers 51 1=rs1 := by
  apply rhoStep (x:=CQDegree51.r0.toArray) rbase
  · rfl
  · decide +kernel
private theorem h2 : rhoPowers 51 2=rs2 := by
  apply rhoStep (x:=CQDegree51.r1.toArray) h1
  · rfl
  · decide +kernel
private theorem h3 : rhoPowers 51 3=rs3 := by
  apply rhoStep (x:=CQDegree51.r2.toArray) h2
  · rfl
  · decide +kernel
private theorem h4 : rhoPowers 51 4=rs4 := by
  apply rhoStep (x:=CQDegree51.r3.toArray) h3
  · rfl
  · decide +kernel
private theorem h5 : rhoPowers 51 5=rs5 := by
  apply rhoStep (x:=CQDegree51.r4.toArray) h4
  · rfl
  · decide +kernel
private theorem h6 : rhoPowers 51 6=rs6 := by
  apply rhoStep (x:=CQDegree51.r5.toArray) h5
  · rfl
  · decide +kernel
private theorem h7 : rhoPowers 51 7=rs7 := by
  apply rhoStep (x:=CQDegree51.r6.toArray) h6
  · rfl
  · decide +kernel
private theorem h8 : rhoPowers 51 8=rs8 := by
  apply rhoStep (x:=CQDegree51.r7.toArray) h7
  · rfl
  · decide +kernel
private theorem h9 : rhoPowers 51 9=rs9 := by
  apply rhoStep (x:=CQDegree51.r8.toArray) h8
  · rfl
  · decide +kernel
private theorem h10 : rhoPowers 51 10=rs10 := by
  apply rhoStep (x:=CQDegree51.r9.toArray) h9
  · rfl
  · decide +kernel
private theorem h11 : rhoPowers 51 11=rs11 := by
  apply rhoStep (x:=CQDegree51.r10.toArray) h10
  · rfl
  · decide +kernel
private theorem h12 : rhoPowers 51 12=rs12 := by
  apply rhoStep (x:=CQDegree51.r11.toArray) h11
  · rfl
  · decide +kernel
private theorem h13 : rhoPowers 51 13=rs13 := by
  apply rhoStep (x:=CQDegree51.r12.toArray) h12
  · rfl
  · decide +kernel
private theorem h14 : rhoPowers 51 14=rs14 := by
  apply rhoStep (x:=CQDegree51.r13.toArray) h13
  · rfl
  · decide +kernel
private theorem h15 : rhoPowers 51 15=rs15 := by
  apply rhoStep (x:=CQDegree51.r14.toArray) h14
  · rfl
  · decide +kernel
private theorem h16 : rhoPowers 51 16=rs16 := by
  apply rhoStep (x:=CQDegree51.r15.toArray) h15
  · rfl
  · decide +kernel
private theorem h17 : rhoPowers 51 17=rs17 := by
  apply rhoStep (x:=CQDegree51.r16.toArray) h16
  · rfl
  · decide +kernel
private theorem h18 : rhoPowers 51 18=rs18 := by
  apply rhoStep (x:=CQDegree51.r17.toArray) h17
  · rfl
  · decide +kernel
private theorem h19 : rhoPowers 51 19=rs19 := by
  apply rhoStep (x:=CQDegree51.r18.toArray) h18
  · rfl
  · decide +kernel
private theorem h20 : rhoPowers 51 20=rs20 := by
  apply rhoStep (x:=CQDegree51.r19.toArray) h19
  · rfl
  · decide +kernel
private theorem h21 : rhoPowers 51 21=rs21 := by
  apply rhoStep (x:=CQDegree51.r20.toArray) h20
  · rfl
  · decide +kernel
private theorem h22 : rhoPowers 51 22=rs22 := by
  apply rhoStep (x:=CQDegree51.r21.toArray) h21
  · rfl
  · decide +kernel
private theorem h23 : rhoPowers 51 23=rs23 := by
  apply rhoStep (x:=CQDegree51.r22.toArray) h22
  · rfl
  · decide +kernel
private theorem h24 : rhoPowers 51 24=rs24 := by
  apply rhoStep (x:=CQDegree51.r23.toArray) h23
  · rfl
  · decide +kernel
private theorem h25 : rhoPowers 51 25=rs25 := by
  apply rhoStep (x:=CQDegree51.r24.toArray) h24
  · rfl
  · decide +kernel
private theorem h26 : rhoPowers 51 26=rs26 := by
  apply rhoStep (x:=CQDegree51.r25.toArray) h25
  · rfl
  · decide +kernel
private theorem h27 : rhoPowers 51 27=rs27 := by
  apply rhoStep (x:=CQDegree51.r26.toArray) h26
  · rfl
  · decide +kernel
private theorem h28 : rhoPowers 51 28=rs28 := by
  apply rhoStep (x:=CQDegree51.r27.toArray) h27
  · rfl
  · decide +kernel
private theorem h29 : rhoPowers 51 29=rs29 := by
  apply rhoStep (x:=CQDegree51.r28.toArray) h28
  · rfl
  · decide +kernel
private theorem h30 : rhoPowers 51 30=rs30 := by
  apply rhoStep (x:=CQDegree51.r29.toArray) h29
  · rfl
  · decide +kernel
private theorem h31 : rhoPowers 51 31=rs31 := by
  apply rhoStep (x:=CQDegree51.r30.toArray) h30
  · rfl
  · decide +kernel
private theorem h32 : rhoPowers 51 32=rs32 := by
  apply rhoStep (x:=CQDegree51.r31.toArray) h31
  · rfl
  · decide +kernel
private theorem h33 : rhoPowers 51 33=rs33 := by
  apply rhoStep (x:=CQDegree51.r32.toArray) h32
  · rfl
  · decide +kernel
private theorem h34 : rhoPowers 51 34=rs34 := by
  apply rhoStep (x:=CQDegree51.r33.toArray) h33
  · rfl
  · decide +kernel
private theorem h35 : rhoPowers 51 35=rs35 := by
  apply rhoStep (x:=CQDegree51.r34.toArray) h34
  · rfl
  · decide +kernel
private theorem h36 : rhoPowers 51 36=rs36 := by
  apply rhoStep (x:=CQDegree51.r35.toArray) h35
  · rfl
  · decide +kernel
private theorem h37 : rhoPowers 51 37=rs37 := by
  apply rhoStep (x:=CQDegree51.r36.toArray) h36
  · rfl
  · decide +kernel
private theorem h38 : rhoPowers 51 38=rs38 := by
  apply rhoStep (x:=CQDegree51.r37.toArray) h37
  · rfl
  · decide +kernel
private theorem h39 : rhoPowers 51 39=rs39 := by
  apply rhoStep (x:=CQDegree51.r38.toArray) h38
  · rfl
  · decide +kernel
private theorem h40 : rhoPowers 51 40=rs40 := by
  apply rhoStep (x:=CQDegree51.r39.toArray) h39
  · rfl
  · decide +kernel
private theorem h41 : rhoPowers 51 41=rs41 := by
  apply rhoStep (x:=CQDegree51.r40.toArray) h40
  · rfl
  · decide +kernel
private theorem h42 : rhoPowers 51 42=rs42 := by
  apply rhoStep (x:=CQDegree51.r41.toArray) h41
  · rfl
  · decide +kernel
private theorem h43 : rhoPowers 51 43=rs43 := by
  apply rhoStep (x:=CQDegree51.r42.toArray) h42
  · rfl
  · decide +kernel
private theorem h44 : rhoPowers 51 44=rs44 := by
  apply rhoStep (x:=CQDegree51.r43.toArray) h43
  · rfl
  · decide +kernel
private theorem h45 : rhoPowers 51 45=rs45 := by
  apply rhoStep (x:=CQDegree51.r44.toArray) h44
  · rfl
  · decide +kernel
private theorem h46 : rhoPowers 51 46=rs46 := by
  apply rhoStep (x:=CQDegree51.r45.toArray) h45
  · rfl
  · decide +kernel
private theorem h47 : rhoPowers 51 47=rs47 := by
  apply rhoStep (x:=CQDegree51.r46.toArray) h46
  · rfl
  · decide +kernel
private theorem h48 : rhoPowers 51 48=rs48 := by
  apply rhoStep (x:=CQDegree51.r47.toArray) h47
  · rfl
  · decide +kernel
private theorem h49 : rhoPowers 51 49=rs49 := by
  apply rhoStep (x:=CQDegree51.r48.toArray) h48
  · rfl
  · decide +kernel
private theorem h50 : rhoPowers 51 50=rs50 := by
  apply rhoStep (x:=CQDegree51.r49.toArray) h49
  · rfl
  · decide +kernel
private theorem h51 : rhoPowers 51 51=rs51 := by
  apply rhoStep (x:=CQDegree51.r50.toArray) h50
  · rfl
  · decide +kernel
theorem solution : rhoPowers 51 51 = CQDegree51.powers := h51
