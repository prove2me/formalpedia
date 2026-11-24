-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_cache_rel
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:40:45.645717+00:00
-- url     : https://prove2.me/submissions/b167a792-3afa-44f4-8e72-1ad47780e452

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace SymmetricSexticResidual.LocalResidueQ5
open SymmetricSexticResidual.Q5WeightsData SymmetricSexticResidual.LocalResidueData PolynomialEncoding.KroneckerCheck
open PolynomialEncoding.PolyOps hiding dotW dotW_rel dotW_len

section CacheRelProof
variable {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
lemma evalACache_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
    (hS : R S1 S2) (hQ : R Q1 Q2) : ACacheRel R (evalACache o1 S1 Q1) (evalACache o2 S2 Q2) := by
  unfold evalACache
  refine letB_rel (hR.rel_mul hS hS) fun hS2 =>
    letB_rel (hR.rel_mul hS hQ) fun hSQ =>
    letB_rel (hR.rel_mul hQ hQ) fun hQ2 =>
    letB_rel (hR.rel_mul hS2 hS) fun hS3 =>
    letB_rel (hR.rel_mul hQ2 hQ) fun hQ3 =>
    letB_rel (hR.rel_sub hS (hR.rel_mul (hR.rel_ofInt 3) hQ)) fun hSm3Q =>
    letB_rel (hR.rel_mul hSm3Q hSm3Q) fun hSm3Q2 =>
    letB_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 5) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hA5 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-175)) (hR.rel_mul hA5 (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 5) hS) (hR.rel_mul (hR.rel_ofInt 3) hQ)))) fun hca0 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 7) (hR.rel_add (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 143) hS2) (hR.rel_mul (hR.rel_ofInt 552) hSQ)) (hR.rel_mul (hR.rel_ofInt 468) hQ2))) fun hca1 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-28)) hSm3Q2) fun hca2 =>
    letB_rel (.cons hca0 (.cons hca1 (.cons hca2 .nil)) : URel R _ _) fun hca =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 1050) (hR.rel_mul hS hA5)) fun hcb0 =>
    letB_rel (hR.rel_add (hR.rel_add (hR.rel_mul (hR.rel_ofInt 21) (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-92)) hS2) (hR.rel_mul (hR.rel_ofInt 312) hSQ)) (hR.rel_mul (hR.rel_ofInt 198) hQ2))) (hR.rel_mul (hR.rel_ofInt 810) hQ)) (hR.rel_ofInt 810)) fun hcb1 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 84) hSm3Q2) fun hcb2 =>
    letB_rel (.cons hcb0 (.cons hcb1 (.cons hcb2 .nil)) : URel R _ _) fun hcb =>
    letB_rel (uNeg_rel hR hca) fun hb =>
    letB_rel (.cons (hR.rel_sub hcb0 (hR.rel_mul (hR.rel_ofInt 3) (hR.rel_neg hca0)))
        (.cons (hR.rel_sub hcb1 (hR.rel_mul (hR.rel_ofInt 3) (hR.rel_neg hca1))) .nil) : URel R _ _) fun ham3b =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 5) hcb) (uSc_rel hR (hR.rel_ofInt 9) hb)) fun ha5m9b =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 15) hcb) (uSc_rel hR (hR.rel_ofInt 9) hb)) fun ha15m9b =>
    letB_rel (uMul_rel hR hcb hcb) fun haa =>
    letB_rel (uMul_rel hR hcb hb) fun hab =>
    letB_rel (uMul_rel hR hb hb) fun hbb =>
    letB_rel (uMul_rel hR ham3b ham3b) fun ham3b2 =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt (-25)) (uMul_rel hR ha5m9b ha15m9b))
        (uShift_rel hR (uAdd_rel hR (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 429) haa) (uSc_rel hR (hR.rel_ofInt 1656) hab)) (uSc_rel hR (hR.rel_ofInt 1404) hbb))))
        (uShift_rel hR (uShift_rel hR (uSc_rel hR (hR.rel_ofInt (-12)) ham3b2)))) fun hA2 =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt 50) (uMul_rel hR hcb ha5m9b))
        (uShift_rel hR (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt (-92)) haa) (uSc_rel hR (hR.rel_ofInt 312) hab)) (uSc_rel hR (hR.rel_ofInt 198) hbb))))
        (uShift_rel hR (uShift_rel hR (uSc_rel hR (hR.rel_ofInt 4) ham3b2)))) fun hB2 =>
    letB_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 15) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hS15m9Q =>
    letB_rel (uAdd_rel hR (uSc_rel hR hS hb) (uSc_rel hR hQ hcb)) fun hsbqa =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt (-25)) (uAdd_rel hR (uSc_rel hR hS15m9Q ha5m9b) (uSc_rel hR hA5 ha15m9b)))
        (uShift_rel hR (uAdd_rel hR (uSub_rel hR (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 858) hS) hcb) (uSc_rel hR (hR.rel_ofInt 1656) hsbqa))
          (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 2808) hQ) hb))))
        (uShift_rel hR (uShift_rel hR (uSc_rel hR (hR.rel_mul (hR.rel_ofInt (-24)) hSm3Q) ham3b)))) fun hA1 =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt 350) (uSub_rel hR (uSc_rel hR (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 10) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) hcb)
        (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 9) hS) hb)))
        (uShift_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt 7) (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_mul (hR.rel_ofInt (-184)) hS) hcb)
          (uSc_rel hR (hR.rel_ofInt 312) hsbqa)) (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 396) hQ) hb))) (uSc_rel hR (hR.rel_ofInt 270) hb))))
        (uShift_rel hR (uShift_rel hR (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 56) hSm3Q) ham3b)))) fun hB1 =>
    letB_rel (uSc_rel hR (hR.rel_ofInt 567) (uSub_rel hR (uMul_rel hR hA2 hB1) (uSc_rel hR (hR.rel_ofInt 7) (uMul_rel hR hA1 hB2)))) fun hD21 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 189) (uMul_rel hR hA2 hcb)) (uSc_rel hR (hR.rel_ofInt 1701) (uMul_rel hR hca hB2))) fun hD20 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 189) (uMul_rel hR hA1 hcb)) (uSc_rel hR (hR.rel_ofInt 243) (uMul_rel hR hca hB1))) fun hD10 =>
    letB_rel (uAdd_rel hR (uSub_rel hR (uMul_rel hR haa hD10) (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 2) hS) (uMul_rel hR hcb hD20))) (uSc_rel hR hS2 hD21)) fun hm0 =>
    letB_rel (uAdd_rel hR (uSub_rel hR (uMul_rel hR hab hD10) (uMul_rel hR hsbqa hD20)) (uSc_rel hR hSQ hD21)) fun hm1 =>
    letB_rel (uAdd_rel hR (uSub_rel hR (uMul_rel hR hbb hD10) (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 2) hQ) (uMul_rel hR hb hD20))) (uSc_rel hR hQ2 hD21)) fun hm2 =>
    letB_rel (uSub_rel hR (uSc_rel hR hS hD21) (uMul_rel hR hcb hD20)) fun hm4 =>
    letB_rel (uSub_rel hR (uSc_rel hR hQ hD21) (uMul_rel hR hb hD20)) fun hm6 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 5) hm0) (uSc_rel hR (hR.rel_ofInt 9) hm1)) fun hl01 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 5) hm1) (uSc_rel hR (hR.rel_ofInt 9) hm2)) fun hl12 =>
    letB_rel (uSub_rel hR (uSc_rel hR (hR.rel_ofInt 5) hm4) (uSc_rel hR (hR.rel_ofInt 9) hm6)) fun hl46 =>
    letB_rel (uSc_rel hR (hR.rel_ofInt (-100 * 968178750)) hl46) fun hAY2b =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-175)) (hR.rel_mul hS (hR.rel_mul hA5 hA5))) fun hBv0 =>
    letB_rel (hR.rel_sub (hR.rel_add (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 143) hS3) (hR.rel_mul (hR.rel_ofInt 828) (hR.rel_mul hS2 hQ)))
        (hR.rel_mul (hR.rel_ofInt 1404) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt 594) hQ3)) fun hBv1S =>
    letB_rel (hR.rel_add (hR.rel_add (hR.rel_mul (hR.rel_ofInt 7) hBv1S) (hR.rel_mul (hR.rel_ofInt 1215) hQ2)) (hR.rel_mul (hR.rel_ofInt 2430) hQ)) fun hBv1 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-28)) (hR.rel_mul hSm3Q2 hSm3Q)) fun hBv2 =>
    ⟨hca, hcb,
      uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hl01) (uSc_rel hR (hR.rel_ofInt _) hl12)) (uSc_rel hR (hR.rel_ofInt _) hl46),
      uSc_rel hR (hR.rel_ofInt _) hl46,
      uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm4) (uSc_rel hR (hR.rel_ofInt _) hm6)) (uSc_rel hR (hR.rel_ofInt _) hD21),
      uAdd_rel hR (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm4) (uSc_rel hR (hR.rel_ofInt _) hm6)) (uSc_rel hR (hR.rel_ofInt _) hD21)) (uSc_rel hR (hR.rel_ofInt _) hD21),
      uSc_rel hR (hR.rel_ofInt _) hD21,
      uSc_rel hR (hR.rel_ofInt _) hAY2b, uSc_rel hR (hR.rel_ofInt _) hAY2b,
      uAdd_rel hR (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hl01) (uSc_rel hR (hR.rel_ofInt _) hl12)) (uSc_rel hR (hR.rel_ofInt _) hl46))
        (uShift_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm0) (uSc_rel hR (hR.rel_ofInt _) hm6)) (uSc_rel hR (hR.rel_ofInt _) hD21)))
          (uSc_rel hR (hR.rel_ofInt _) (uSub_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm1) (uSc_rel hR (hR.rel_ofInt _) hm6)) (uSc_rel hR (hR.rel_ofInt _) hD21))))),
      uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hl46)
        (uShift_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) (uSc_rel hR (hR.rel_ofInt _) hD21)) (uSc_rel hR (hR.rel_ofInt _) (uSc_rel hR (hR.rel_ofInt _) hD21)))),
      uShift_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm4) (uSc_rel hR (hR.rel_ofInt _) hD21)),
      uShift_rel hR (uAdd_rel hR (uAdd_rel hR (uSc_rel hR (hR.rel_ofInt _) hm4) (uSc_rel hR (hR.rel_ofInt _) hD21)) (uSc_rel hR (hR.rel_ofInt _) hD21)),
      uShift_rel hR (uSc_rel hR (hR.rel_ofInt _) hD21),
      .cons hBv0 (.cons hBv1 (.cons hBv2 .nil))⟩

lemma evalGeomSQ_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
    (hS : R S1 S2) (hQ : R Q1 Q2) : GeomSQRel R (evalGeomSQ o1 S1 Q1) (evalGeomSQ o2 S2 Q2) := by
  unfold evalGeomSQ
  refine letB_rel (hR.rel_mul hS hS) fun hS2 =>
    letB_rel (hR.rel_mul hS hQ) fun hSQ =>
    letB_rel (hR.rel_mul hQ hQ) fun hQ2 =>
    letB_rel (hR.rel_mul hS2 hS) fun hS3 =>
    letB_rel (hR.rel_mul hS2 hS2) fun hS4 =>
    letB_rel (hR.rel_mul hQ2 hQ) fun hQ3 =>
    letB_rel (hR.rel_mul hQ2 hQ2) fun hQ4 =>
    letB_rel (hR.rel_sub hS (hR.rel_mul (hR.rel_ofInt 3) hQ)) fun hSm3Q =>
    letB_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 5) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hA5 =>
    letB_rel (hR.rel_sub (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-2)) hS3) (hR.rel_mul (hR.rel_ofInt 6) (hR.rel_mul hS2 hQ)))
        (hR.rel_mul (hR.rel_ofInt 3) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt 2) hQ3)) fun hpS =>
    letB_rel (hR.rel_add (hR.rel_add (hR.rel_mul (hR.rel_ofInt 7) hpS) (hR.rel_mul (hR.rel_ofInt 5) hQ2)) (hR.rel_mul (hR.rel_ofInt 10) hQ)) fun hH0 =>
    letB_rel (.cons (.cons (hR.rel_add (hR.rel_neg hS) (hR.rel_mul (hR.rel_ofInt 2) hQ)) .nil) (.cons (.cons (hR.rel_ofInt 1) .nil) .nil) : BRel R _ _) fun hu3 =>
    letB_rel (bivMul_rel hR hu3 hu3) fun hu3_2 =>
    letB_rel (bivConst_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 25) hS) (hR.rel_mul (hR.rel_ofInt 45) hQ))) fun hLX0 =>
    letB_rel (.cons (.cons (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 45) hQ) (hR.rel_mul (hR.rel_ofInt 25) hS)) .nil) (.cons (.cons (hR.rel_ofInt 27) .nil) .nil) : BRel R _ _) fun hLX1 =>
    letB_rel (.cons hLX0 (.cons hLX1 .nil) : UBRel R _ _) fun hLX =>
    letB_rel (.cons (bivConst_rel (hR.rel_ofInt 25)) (.cons (bivConst_rel (hR.rel_ofInt (-25))) .nil) : UBRel R _ _) fun hdLX0 =>
    letB_rel (.cons (bivConst_rel (hR.rel_ofInt (-45))) (.cons (bivConst_rel (hR.rel_ofInt 45)) .nil) : UBRel R _ _) fun hdLX1 =>
    letB_rel (.cons .nil (.cons (bivConst_rel (hR.rel_ofInt 27)) .nil) : UBRel R _ _) fun hdLX3 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 2) hS) fun hS2x =>
    ⟨hH0, hS2,
      bivAdd_rel hR (bivConst_rel (hR.rel_sub (hR.rel_mul hS hQ2) (hR.rel_mul (hR.rel_ofInt 4) hQ3)))
        (bivAdd_rel hR (bivSc_rel hR (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 18) hSQ) (hR.rel_mul (hR.rel_ofInt 4) hS2)) hu3)
          (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-27)) hS) hu3_2)),
      bivAdd_rel hR (bivConst_rel (hR.rel_sub (hR.rel_add hQ2 (hR.rel_mul (hR.rel_ofInt 4) hS2)) (hR.rel_mul (hR.rel_ofInt 18) hSQ)))
        (bivAdd_rel hR (bivSc_rel hR (hR.rel_add (hR.rel_mul (hR.rel_ofInt 46) hS) (hR.rel_mul (hR.rel_ofInt 18) hQ)) hu3)
          (bivSc_rel hR (hR.rel_ofInt (-27)) hu3_2)),
      bivAdd_rel hR (bivConst_rel (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-8)) hS2) (hR.rel_mul (hR.rel_ofInt 38) hSQ)) (hR.rel_mul (hR.rel_ofInt 12) hQ2)))
        (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-90)) hS) hu3),
      bivAdd_rel hR (bivConst_rel (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-4)) hS2) (hR.rel_mul (hR.rel_ofInt 18) hSQ)))
        (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-54)) hS) hu3),
      .cons (.cons (hR.rel_mul (hR.rel_ofInt 7) (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-6)) hS2) (hR.rel_mul (hR.rel_ofInt 12) hSQ)) (hR.rel_mul (hR.rel_ofInt 3) hQ2))) .nil)
        (.cons .nil (.cons (.cons (hR.rel_ofInt 21) .nil) .nil)),
      .cons (.cons (hR.rel_add (hR.rel_add (hR.rel_mul (hR.rel_ofInt 7) (hR.rel_sub (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 6) hS2) (hR.rel_mul (hR.rel_ofInt 6) hSQ)) (hR.rel_mul (hR.rel_ofInt 6) hQ2))) (hR.rel_mul (hR.rel_ofInt 10) hQ)) (hR.rel_ofInt 10)) .nil) .nil,
      .cons .nil (.cons (.cons (hR.rel_mul (hR.rel_ofInt 42) hS) .nil) .nil),
      hLX, hdLX0, hdLX1, hdLX3,
      ubAdd_rel hR (ubSc_rel hR hS2x hdLX0) hLX, ubSc_rel hR hS2x hdLX1, ubSc_rel hR hS2x hdLX3,
      .cons (hR.rel_mul (hR.rel_ofInt 25) (hR.rel_mul hS (hR.rel_mul hA5 hA5))) (.cons (hR.rel_mul (hR.rel_ofInt (-4)) (hR.rel_mul (hR.rel_mul hSm3Q hSm3Q) hSm3Q)) .nil),
      .cons (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add
          (hR.rel_mul (hR.rel_ofInt _) hS4) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS3 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ2))) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ3)))
          (hR.rel_mul (hR.rel_ofInt _) hQ4)) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt _) hQ3))
          (hR.rel_mul (hR.rel_ofInt _) hS2)) (hR.rel_mul (hR.rel_ofInt _) hSQ)) (hR.rel_mul (hR.rel_ofInt _) hQ2))
        (.cons (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add
          (hR.rel_mul (hR.rel_ofInt _) hS4) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS3 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ2))) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ3)))
          (hR.rel_mul (hR.rel_ofInt _) hQ4)) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt _) hQ3))
          (hR.rel_mul (hR.rel_ofInt _) hS2)) (hR.rel_mul (hR.rel_ofInt _) hSQ)) (hR.rel_mul (hR.rel_ofInt _) hQ2)) .nil),
      .cons (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add (hR.rel_add
          (hR.rel_mul (hR.rel_ofInt _) hS3) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt _) hQ3))
          (hR.rel_mul (hR.rel_ofInt _) hSQ)) (hR.rel_mul (hR.rel_ofInt _) hQ2))
          (hR.rel_mul (hR.rel_ofInt _) hS)) (hR.rel_mul (hR.rel_ofInt _) hQ))
        (.cons (hR.rel_add (hR.rel_add (hR.rel_add
          (hR.rel_mul (hR.rel_ofInt _) hS3) (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS2 hQ)))
          (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hS hQ2))) (hR.rel_mul (hR.rel_ofInt _) hQ3)) .nil)⟩

lemma evalSQCache_rel (hR : PolyOpsRel o1 o2 R) {S1 Q1 : α} {S2 Q2 : β}
    (hS : R S1 S2) (hQ : R Q1 Q2) : SQCacheRel R (evalSQCache o1 S1 Q1) (evalSQCache o2 S2 Q2) := by
  unfold evalSQCache
  refine letB_rel (powList_rel hR hS 30 (hR.rel_ofInt 1)) fun hpS =>
    letB_rel (powList_rel hR hQ 37 (hR.rel_ofInt 1)) fun hpQ =>
    letB_rel (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-5)) hS) (hR.rel_mul (hR.rel_ofInt 9) hQ)) fun hf2 =>
    letB_rel (hR.rel_add (hR.rel_neg hS) (hR.rel_mul (hR.rel_ofInt 3) hQ)) fun hf3 =>
    letB_rel (hR.rel_add (hR.rel_add (hR.rel_ofInt (-45)) (hR.rel_mul (hR.rel_ofInt (-77)) hS)) (hR.rel_mul (hR.rel_ofInt 210) hQ)) fun hf4 =>
    letB_rel (hR.rel_mul hf2 hf2) fun hf2_2 =>
    letB_rel (hR.rel_mul hf2_2 hf2_2) fun hf2_4 =>
    letB_rel (hR.rel_mul hf2_4 hf2_2) fun hf2_6 =>
    letB_rel (hR.rel_mul hf2_6 hf2) fun hf2_7 =>
    letB_rel (hR.rel_mul (hR.rel_mul hf3 hf3) hf3) fun hf3_3 =>
    letB_rel (hR.rel_mul hf3_3 hf3_3) fun hf3_6 =>
    letB_rel (hR.rel_mul hf3_6 hf3_3) fun hf3_9 =>
    letB_rel (hR.rel_mul hf3_9 hf3_3) fun hf3_12 =>
    letB_rel (hR.rel_mul hf3_12 hf3) fun hf3_13 =>
    letB_rel (hR.rel_mul hf4 hf4) fun hf4_2 =>
    letB_rel (hR.rel_mul hf3_13 hf4_2) fun hd0 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_2) hf3_13) hf4_2) fun hd1 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_4) hf3_13) hf4_2) fun hd2 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_6) hf3_13) hf4_2) fun hd3 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_13) hf4_2) fun hd4 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_12) hf4_2) fun hd8 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_9) hf4_2) fun hd9 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_6) hf4_2) fun hd10 =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul hS hf2_7) hf3_3) hf4) fun hd11 =>
    letB_rel (hR.rel_mul hS hf2_7) fun hd12 =>
    letB_rel (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd0 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd1 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd2 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd3 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd4 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd8 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd9 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd10 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd11 (evalExpr2_rel hR hS hQ hpS hpQ _)))
      (.cons (hR.rel_mul (hR.rel_ofInt _) (hR.rel_mul hd12 (evalExpr2_rel hR hS hQ hpS hpQ _))) .nil)))))))))))) : URel R _ _) fun hW =>
    letB_rel (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul (hR.rel_mul hQ hS) hf2_7) hf3_13) (hR.rel_pow 4 (evalExpr2_rel hR hS hQ hpS hpQ fac_5))) (evalExpr2_rel hR hS hQ hpS hpQ fac_6)) fun hD =>
    letB_rel (evalACache_rel hR hS hQ) fun hac =>
    letB_rel (evalGeomSQ_rel hR hS hQ) fun hgsq =>
    ⟨hW, hD, hac, hgsq,
      dotW_rel hR (uTail_rel hac.A0U_t0) hW 1, dotW_rel hR (uTail_rel hac.A0U_t1) hW 1,
      dotW_rel hR hac.A0V_t0 hW 0, dotW_rel hR hac.A0V_t1 hW 0, dotW_rel hR hac.A0V_t2 hW 0,
      dotW_rel hR hac.A0V_t0 hW 1, dotW_rel hR hac.A0V_t1 hW 1, dotW_rel hR hac.A0V_t2 hW 1,
      dotW_rel hR (uMul_rel hR hac.A0V_t0 hac.Bv_SQ) hW 0, dotW_rel hR (uMul_rel hR hac.A0V_t1 hac.Bv_SQ) hW 0,
      dotW_rel hR (uMul_rel hR hac.A0V_t2 hac.Bv_SQ) hW 0,
      dotW_rel hR hac.AY2_t0 hW 0, dotW_rel hR hac.AY2_t1 hW 0,
      dotW_rel hR hac.AY3_t0 hW 1, dotW_rel hR hac.AY3_t1 hW 1,
      dotW_rel hR hac.AX2_t0 hW 0, dotW_rel hR hac.AX2_t1 hW 0, dotW_rel hR hac.AX2_t2 hW 0,
      .cons (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) .nil))))))
        (.cons (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) (.cons (evalExpr3PolyT_rel hR hS hQ hpS hpQ _) .nil))))) .nil)⟩

lemma evalGeomT_rel (hR : PolyOpsRel o1 o2 R) {S1 T1 : α} {S2 T2 : β}
    {ca1 ca2 cb1 cb2} {g1 : GeomSQ α} {g2 : GeomSQ β}
    (hS : R S1 S2) (hca : URel R ca1 ca2) (hcb : URel R cb1 cb2) (hg : GeomSQRel R g1 g2) (hT : R T1 T2) :
    GeomTRel R (evalGeomT o1 S1 ca1 cb1 g1 T1) (evalGeomT o2 S2 ca2 cb2 g2 T2) := by
  unfold evalGeomT
  refine letB_rel (hR.rel_mul hT hT) fun hT2 =>
    letB_rel (hR.rel_mul hT2 hT) fun hT3 =>
    letB_rel (hR.rel_sub (hR.rel_sub (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-2)) hT3) (hR.rel_mul (hR.rel_ofInt 6) hT2)) (hR.rel_mul (hR.rel_ofInt 3) hT)) (hR.rel_ofInt 2)) fun hpT =>
    letB_rel (hR.rel_add hg.H0_7_SQ (hR.rel_mul (hR.rel_ofInt 7) hpT)) fun hH0 =>
    letB_rel (hR.rel_mul hH0 hH0) fun hH02 =>
    letB_rel (hR.rel_sub hT (hR.rel_ofInt 3)) fun hTm3 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-4)) (hR.rel_mul (hR.rel_mul hTm3 hTm3) hTm3)) fun hAv0 =>
    letB_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 5) hT) (hR.rel_ofInt 9)) fun hT59 =>
    letB_rel (hR.rel_mul hT (hR.rel_mul hT59 hT59)) fun hCv0i =>
    letB_rel (hR.rel_mul (hR.rel_ofInt (-25)) hCv0i) fun hCv0 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 7) (hR.rel_sub (hR.rel_add (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 143) hT3) (hR.rel_mul (hR.rel_ofInt 828) hT2)) (hR.rel_mul (hR.rel_ofInt 1404) hT)) (hR.rel_ofInt 594))) fun hBv1T =>
    letB_rel (.cons (.cons (hR.rel_add (hR.rel_neg hT) (hR.rel_ofInt 2)) (.cons (hR.rel_ofInt 1) .nil)) .nil : BRel R _ _) fun hv3 =>
    letB_rel (bivMul_rel hR hv3 hv3) fun hv3_2 =>
    letB_rel (bivAdd_rel hR (bivConst_rel (hR.rel_sub hT (hR.rel_ofInt 4)))
        (bivAdd_rel hR (bivSc_rel hR (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 18) hT) (hR.rel_mul (hR.rel_ofInt 4) hT2)) hv3)
          (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-27)) hT) hv3_2))) fun hDY2 =>
    letB_rel (bivAdd_rel hR (bivConst_rel (hR.rel_add (hR.rel_mul (hR.rel_ofInt (-4)) hT2) (hR.rel_mul (hR.rel_ofInt 18) hT)))
        (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt (-54)) hT) hv3)) fun hdDY2 =>
    letB_rel (hR.rel_mul hS hT) fun hST =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 2) hST) fun hST2 =>
    letB_rel (bivSc_rel hR hST (bivMul_rel hR hg.DX2 hDY2)) fun hW2 =>
    letB_rel (.cons (.cons hR.rel_zero (.cons (hR.rel_mul (hR.rel_ofInt 42) hT) .nil)) .nil : BRel R _ _) fun hdF54 =>
    letB_rel (bivConst_rel (hR.rel_sub (hR.rel_mul (hR.rel_ofInt 25) hT) (hR.rel_ofInt 45))) fun hLY0 =>
    letB_rel (.cons (.cons (hR.rel_sub (hR.rel_ofInt 45) (hR.rel_mul (hR.rel_ofInt 25) hT)) (.cons (hR.rel_ofInt 27) .nil)) .nil : BRel R _ _) fun hLY1 =>
    letB_rel (bivConst_rel (hR.rel_mul (hR.rel_ofInt 54) hT)) fun hPY41 =>
    letB_rel (ubSub_rel hR (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY0 hg.dLX_0)) (ubSc_rel hR hT (ubBmul_rel hR hLY0 hg.LX_27))) fun hbr00 =>
    letB_rel (ubSub_rel hR (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY1 hg.dLX_0)) (ubSc_rel hR hT (ubBmul_rel hR hLY1 hg.LX_27))) fun hbr10 =>
    letB_rel (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY0 hg.dLX_1)) fun hbr01 =>
    letB_rel (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY1 hg.dLX_1)) fun hbr11 =>
    letB_rel (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY0 hg.dLX_3)) fun hbr03 =>
    letB_rel (ubSc_rel hR (hR.rel_neg hST2) (ubBmul_rel hR hLY1 hg.dLX_3)) fun hbr13 =>
    letB_rel (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 27) hST2) hg.LX_27) fun hbr14 =>
    letB_rel (ubSc_rel hR hST (ubAdd_rel hR (ubBmul_rel hR hg.dF5_3 (ubNeg_rel hR (ubBmul_rel hR hPY41 hg.PX_0))) (ubBmul_rel hR hg.dF5_0 (ubBmul_rel hR hPY41 hg.PX_3)))) fun hom0 =>
    letB_rel (ubSc_rel hR hST (ubAdd_rel hR (ubBmul_rel hR hg.dF5_3 (ubNeg_rel hR (ubBmul_rel hR hPY41 hg.PX_1))) (ubBmul_rel hR hg.dF5_1 (ubBmul_rel hR hPY41 hg.PX_3)))) fun hom1 =>
    letB_rel (ubSc_rel hR hST (ubSub_rel hR (ubBmul_rel hR hg.dF5_3 (ubBmul_rel hR hdDY2 hbr00)) (ubBmul_rel hR hg.dF5_0 (ubBmul_rel hR hdDY2 hbr03)))) fun hdYF00 =>
    letB_rel (ubSc_rel hR hST (ubSub_rel hR (ubBmul_rel hR hg.dF5_3 (ubBmul_rel hR hdDY2 hbr01)) (ubBmul_rel hR hg.dF5_1 (ubBmul_rel hR hdDY2 hbr03)))) fun hdYF01 =>
    letB_rel (ubSc_rel hR hST (ubSub_rel hR (ubBmul_rel hR hg.dF5_3 (ubBmul_rel hR hdDY2 hbr10)) (ubBmul_rel hR hg.dF5_0 (ubBmul_rel hR hdDY2 hbr13)))) fun hdYF10 =>
    letB_rel (ubSc_rel hR hST (ubSub_rel hR (ubBmul_rel hR hg.dF5_3 (ubBmul_rel hR hdDY2 hbr11)) (ubBmul_rel hR hg.dF5_1 (ubBmul_rel hR hdDY2 hbr13)))) fun hdYF11 =>
    letB_rel (ubSc_rel hR hST (ubBmul_rel hR hdF54 (ubSub_rel hR (ubBmul_rel hR hg.dDX2_dS hbr03) (ubBmul_rel hR hg.dDX2_dx hbr00)))) fun hdXF00 =>
    letB_rel (ubSc_rel hR hST (ubBmul_rel hR hdF54 (ubSub_rel hR (ubBmul_rel hR hg.dDX2_dQ hbr03) (ubBmul_rel hR hg.dDX2_dx hbr01)))) fun hdXF01 =>
    letB_rel (ubBmul_rel hR hg.DX2 hdYF00) fun hQX00 =>
    letB_rel (ubBmul_rel hR hg.DX2 hdYF01) fun hQX01 =>
    letB_rel (ubBmul_rel hR hg.DX2 (ubSub_rel hR hdYF10 (ubBmul_rel hR hDY2 hom0))) fun hQX10 =>
    letB_rel (ubBmul_rel hR hg.DX2 (ubSub_rel hR hdYF11 (ubBmul_rel hR hDY2 hom1))) fun hQX11 =>
    letB_rel (ubNeg_rel hR (ubBmul_rel hR hDY2 hdXF00)) fun hQY00 =>
    letB_rel (ubNeg_rel hR (ubBmul_rel hR hDY2 hdXF01)) fun hQY01 =>
    letB_rel (ubSc_rel hR (hR.rel_ofInt 2) (ubBmul_rel hR hW2 (ubBmul_rel hR hdF54 hbr03))) fun hEB0 =>
    letB_rel (ubSc_rel hR (hR.rel_ofInt 2) (ubBmul_rel hR hW2 (ubSub_rel hR (ubBmul_rel hR hdF54 hbr13) (ubBmul_rel hR hg.dF5_3 hbr14)))) fun hEB1 =>
    letB_rel (Ra := fun p q => BRel R p.1 q.1 ∧ UBRel R p.2 q.2)
      (ubSynDiv1Rem_rel hR (ubSub_rel hR (ubMulU_rel hR hcb hQX00) (ubMulU_rel hR hca hQX01))) fun hdiv0 =>
    letB_rel (Ra := fun p q => BRel R p.1 q.1 ∧ UBRel R p.2 q.2)
      (ubSynDiv1Rem_rel hR (ubSub_rel hR (ubMulU_rel hR hcb hQX10) (ubMulU_rel hR hca hQX11))) fun hdiv1 =>
    letB_rel (ubSub_rel hR (ubMulU_rel hR hcb hQY00) (ubMulU_rel hR hca hQY01)) fun hQYd0 =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 4) (hR.rel_mul hg.S2 hT2)) fun hc4 =>
    letB_rel (.cons (.cons (.cons (hR.rel_mul hc4 (list_getD_rel hR hg.qC_63 0)) .nil) (.cons (.cons (hR.rel_mul hc4 (list_getD_rel hR hg.qEx_63 0)) .nil) .nil))
        (.cons (.cons (.cons (hR.rel_mul hc4 (list_getD_rel hR hg.qC_63 1)) .nil) (.cons (.cons (hR.rel_mul hc4 (list_getD_rel hR hg.qEx_63 1)) .nil) .nil)) .nil) : UBRel R _ _) fun hqE =>
    letB_rel (ubBmul_rel hR hDY2 hqE) fun hDYqE =>
    letB_rel (ubAdd_rel hR (ubNeg_rel hR hQYd0) (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 189) hCv0) (ubShift_rel hDYqE))) fun hqY0 =>
    ⟨hH0, hH02, hAv0, hCv0i, hCv0, hBv1T, hDY2, hdiv0.1, hdiv1.1, hdiv0.2, hdiv1.2, hqY0, hDYqE,
      ubAdd_rel hR (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt (-9)) hH0) hdiv0.2) (ubSc_rel hR (hR.rel_ofInt 63) (ubMulU_rel hR hg.qC_63 hEB0)),
      ubAdd_rel hR (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 9) hH0) (ubMulU_rel hR hg.A1_1_27 hqY0))
        (ubShift_rel (ubAdd_rel hR
          (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 9) hH0) (ubSub_rel hR (ubSc_rel hR hAv0 hdiv0.2) (ubSc_rel hR hCv0 hdiv1.2)))
          (ubSc_rel hR (hR.rel_ofInt 63) (ubMulU_rel hR hg.qC_63 (ubSub_rel hR (ubSc_rel hR hCv0 hEB1) (ubSc_rel hR hAv0 hEB0)))))),
      ubSub_rel hR (ubAdd_rel hR (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt (-1701)) hH0) (ubMulU_rel hR hg.A1_1_27 hDYqE))
        (ubSc_rel hR (hR.rel_mul (hR.rel_ofInt 9) hH0) hdiv1.2)) (ubSc_rel hR (hR.rel_ofInt 63) (ubMulU_rel hR hg.qC_63 hEB1))⟩

lemma evalBTot_rel (hR : PolyOpsRel o1 o2 R) {c1 : SQCache α} {c2 : SQCache β}
    {g1 : GeomT α} {g2 : GeomT β} {T1 : α} {T2 : β}
    (hc : SQCacheRel R c1 c2) (hg : GeomTRel R g1 g2) (hT : R T1 T2) :
    BRel R (evalBTot o1 c1 g1 T1) (evalBTot o2 c2 g2 T2) := by
  unfold evalBTot
  refine letB_rel (hR.rel_mul hT hT) fun hT2 =>
    letB_rel (uAdd_rel hR hc.d_A0U_t0 (uSc_rel hR hT hc.d_A0U_t1)) fun hdU =>
    letB_rel (uAdd_rel hR (uAdd_rel hR hc.d_A0V_t0 (uSc_rel hR hT hc.d_A0V_t1)) (uSc_rel hR hT2 hc.d_A0V_t2)) fun hdV =>
    letB_rel (uAdd_rel hR (uAdd_rel hR hc.d_A0V_U_t0 (uSc_rel hR hT hc.d_A0V_U_t1)) (uSc_rel hR hT2 hc.d_A0V_U_t2)) fun hdVU =>
    letB_rel (uAdd_rel hR (uAdd_rel hR (uAdd_rel hR hc.d_A0VBv_t0 (uSc_rel hR hT hc.d_A0VBv_t1)) (uSc_rel hR hT2 hc.d_A0VBv_t2)) (uSc_rel hR hg.Bv1_T_1701 hdVU)) fun hdVB =>
    letB_rel (uAdd_rel hR hc.d_AY2_t0 (uSc_rel hR hT hc.d_AY2_t1)) fun hdY2 =>
    letB_rel (uAdd_rel hR hc.d_AY3_t0 (uSc_rel hR hT hc.d_AY3_t1)) fun hdY3 =>
    letB_rel (uAdd_rel hR (uAdd_rel hR hc.d_AX2_t0 (uSc_rel hR hT hc.d_AX2_t1)) (uSc_rel hR hT2 hc.d_AX2_t2)) fun hdX2 =>
    bivAdd_rel hR (bivAdd_rel hR (bivAdd_rel hR
        (combineBivDot_rel hR (ubSub_rel hR hg.q1_0_div_sc hg.q1_2_div_sc) (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 7) hg.Cv0_243) hdU))
        (combineBivDot_rel hR hg.DY2_qE_63 (uSc_rel hR (hR.rel_mul (hR.rel_ofInt 45927) (hR.rel_mul hg.Cv0_243 hg.H0_7_2)) hdY3)))
        (combineBivDot_rel hR hg.q1_1_sc (uSc_rel hR (hR.rel_ofInt 7) hdV)))
      (bivAdd_rel hR (bivSc_rel hR (hR.rel_mul (hR.rel_ofInt 243) hg.H0_7_2)
        (bivAdd_rel hR (combineBivDot_rel hR hg.qY_0_321489 hdY2) (combineBivDot_rel hR hg.qX_0_sc hdX2)))
        (bivNeg_rel hR (combineBivDot_rel hR hg.q1_0_div_sc hdVB)))

lemma evalTStep_rel (hR : PolyOpsRel o1 o2 R) {S1 T1 : α} {S2 T2 : β}
    {c1 : SQCache α} {c2 : SQCache β}
    (hS : R S1 S2) (hc : SQCacheRel R c1 c2) (hT : R T1 T2) :
    BRel R (evalTStep o1 S1 c1 T1) (evalTStep o2 S2 c2 T2) := by
  unfold evalTStep
  refine letB_rel (evalGeomT_rel hR hS hc.ac.ca_p hc.ac.cb_p hc.gsq hT) fun hgt =>
    letB_rel (evalBTot_rel hR hc hgt hT) fun hB =>
    letB_rel (hR.rel_mul (hR.rel_ofInt 21) hS) fun hs21 =>
    letB_rel (hR.rel_neg (hR.rel_mul (hR.rel_ofInt 21) hT)) fun ht21 =>
    letB_rel (hR.rel_neg hgt.H0_7) fun hnh0 =>
    letB_rel (bivRedOnce_rel hR hs21 ht21 hnh0 (bivRedOnce_rel hR hs21 ht21 hnh0 hB)) fun hlhs =>
    letB_rel (hR.rel_mul (hR.rel_ofInt C_RHS_int) (hR.rel_mul (hR.rel_mul hs21 hs21) (hR.rel_mul hgt.Cv0_int hc.D_div_L2))) fun hrsc =>
    letB_rel ?_ fun hrraw =>
    bivSub_rel hR hlhs (bivSc_rel hR hrsc hrraw)
  have hmap : ∀ {l1 l2}, List.Forall₂ (List.Forall₂ (URel R)) l1 l2 →
      BRel R (l1.map fun row => row.map fun p => uEval o1 p T1)
        (l2.map fun row => row.map fun p => uEval o2 p T2) := by
    intro l1 l2 hl
    induction hl with
    | nil => exact .nil
    | cons hrow _ ih =>
        refine .cons ?_ ih
        induction hrow with
        | nil => exact .nil
        | cons hp _ ihp => exact .cons (uEval_rel hR hT hp) ihp
  exact hmap hc.RQ5_T

end CacheRelProof
end SymmetricSexticResidual.LocalResidueQ5

theorem solution :
    (∀ {α β : Type} {o1 : PolynomialEncoding.KroneckerCheck.PolyOps α} {o2 : PolynomialEncoding.KroneckerCheck.PolyOps β}
      {R : α → β → Prop}, PolynomialEncoding.KroneckerCheck.PolyOpsRel o1 o2 R →
      ∀ {S1 Q1 : α} {S2 Q2 : β}, R S1 S2 → R Q1 Q2 →
      SymmetricSexticResidual.LocalResidueQ5.ACacheRel R
        (SymmetricSexticResidual.LocalResidueQ5.evalACache o1 S1 Q1)
        (SymmetricSexticResidual.LocalResidueQ5.evalACache o2 S2 Q2)) ∧
    (∀ {α β : Type} {o1 : PolynomialEncoding.KroneckerCheck.PolyOps α} {o2 : PolynomialEncoding.KroneckerCheck.PolyOps β}
      {R : α → β → Prop}, PolynomialEncoding.KroneckerCheck.PolyOpsRel o1 o2 R →
      ∀ {S1 Q1 : α} {S2 Q2 : β}, R S1 S2 → R Q1 Q2 →
      SymmetricSexticResidual.LocalResidueQ5.GeomSQRel R
        (SymmetricSexticResidual.LocalResidueQ5.evalGeomSQ o1 S1 Q1)
        (SymmetricSexticResidual.LocalResidueQ5.evalGeomSQ o2 S2 Q2)) ∧
    (∀ {α β : Type} {o1 : PolynomialEncoding.KroneckerCheck.PolyOps α} {o2 : PolynomialEncoding.KroneckerCheck.PolyOps β}
      {R : α → β → Prop}, PolynomialEncoding.KroneckerCheck.PolyOpsRel o1 o2 R →
      ∀ {S1 Q1 : α} {S2 Q2 : β}, R S1 S2 → R Q1 Q2 →
      SymmetricSexticResidual.LocalResidueQ5.SQCacheRel R
        (SymmetricSexticResidual.LocalResidueQ5.evalSQCache o1 S1 Q1)
        (SymmetricSexticResidual.LocalResidueQ5.evalSQCache o2 S2 Q2)) ∧
    (∀ {α β : Type} {o1 : PolynomialEncoding.KroneckerCheck.PolyOps α} {o2 : PolynomialEncoding.KroneckerCheck.PolyOps β}
      {R : α → β → Prop}, PolynomialEncoding.KroneckerCheck.PolyOpsRel o1 o2 R →
      ∀ {S1 T1 : α} {S2 T2 : β}
        {ca1 : PolynomialEncoding.PolyOps.UPoly α} {ca2 : PolynomialEncoding.PolyOps.UPoly β}
        {cb1 : PolynomialEncoding.PolyOps.UPoly α} {cb2 : PolynomialEncoding.PolyOps.UPoly β}
        {g1 : SymmetricSexticResidual.LocalResidueQ5.GeomSQ α} {g2 : SymmetricSexticResidual.LocalResidueQ5.GeomSQ β},
      R S1 S2 → PolynomialEncoding.PolyOps.URel R ca1 ca2 → PolynomialEncoding.PolyOps.URel R cb1 cb2 →
      SymmetricSexticResidual.LocalResidueQ5.GeomSQRel R g1 g2 → R T1 T2 →
      SymmetricSexticResidual.LocalResidueQ5.GeomTRel R
        (SymmetricSexticResidual.LocalResidueQ5.evalGeomT o1 S1 ca1 cb1 g1 T1)
        (SymmetricSexticResidual.LocalResidueQ5.evalGeomT o2 S2 ca2 cb2 g2 T2)) ∧
    (∀ {α β : Type} {o1 : PolynomialEncoding.KroneckerCheck.PolyOps α} {o2 : PolynomialEncoding.KroneckerCheck.PolyOps β}
      {R : α → β → Prop}, PolynomialEncoding.KroneckerCheck.PolyOpsRel o1 o2 R →
      ∀ {S1 T1 : α} {S2 T2 : β}
        {c1 : SymmetricSexticResidual.LocalResidueQ5.SQCache α} {c2 : SymmetricSexticResidual.LocalResidueQ5.SQCache β},
      R S1 S2 → SymmetricSexticResidual.LocalResidueQ5.SQCacheRel R c1 c2 → R T1 T2 →
      PolynomialEncoding.PolyOps.BRel R
        (SymmetricSexticResidual.LocalResidueQ5.evalTStep o1 S1 c1 T1)
        (SymmetricSexticResidual.LocalResidueQ5.evalTStep o2 S2 c2 T2)) :=
  ⟨SymmetricSexticResidual.LocalResidueQ5.evalACache_rel,
   SymmetricSexticResidual.LocalResidueQ5.evalGeomSQ_rel,
   SymmetricSexticResidual.LocalResidueQ5.evalSQCache_rel,
   SymmetricSexticResidual.LocalResidueQ5.evalGeomT_rel,
   SymmetricSexticResidual.LocalResidueQ5.evalTStep_rel⟩
