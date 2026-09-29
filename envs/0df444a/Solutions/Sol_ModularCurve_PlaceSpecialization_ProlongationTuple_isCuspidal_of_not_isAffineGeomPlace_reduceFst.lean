-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/72031acb-4078-5046-a9e5-4649df71758a

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_isIntegral_adjoin_mk_coeffMap
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst.ModularCurve ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand jq ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffMap_id coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence jGeomGen jNGeomGen IsAffineGeomPlace coeffMap_qExpand isIntegral_adjoin_mk_coeffMap"
p2m_open "ModularCurve"

namespace W3s

local notation "𝕂" => AlgebraicClosure ℚ

p2m_open "Polynomial ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

theorem isIntegral_adjoin_jGeomGen_jNGeomGen (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IsIntegral (Algebra.adjoin K ({jGeomGen K N} : Set (modularFunctionFieldC K N))) (jNGeomGen K N) := by
  have hz : jqNModC K N = ((Polynomial.X : Polynomial (Polynomial K)).map
      (Polynomial.aeval (jqModC K)).toRingHom).eval (jqNModC K N) := by
    rw [Polynomial.map_X, Polynomial.eval_X]
  have hmem : coeffMap (RingHom.id K) (jqNModC K N) ∈ modularFunctionFieldC K N := by
    rw [coeffMap_id]; exact jqNModC_mem K N
  have h := ModularCurve.isIntegral_adjoin_mk_coeffMap (RingHom.id K) N Polynomial.X (jqNModC K N) hz hmem
  have e : (⟨coeffMap (RingHom.id K) (jqNModC K N), hmem⟩ : modularFunctionFieldC K N) = jNGeomGen K N :=
    Subtype.ext (coeffMap_id _)
  rw [e] at h
  exact h

theorem jNGeomGen_mem_of_jGeomGen_mem {K : Type*} [Field K] {N : ℕ} [NeZero N]
    (v : Place K (modularFunctionFieldC K N)) (hj : jGeomGen K N ∈ v.toValuationSubring) :
    jNGeomGen K N ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_adjoin_jGeomGen_jNGeomGen K N)

theorem isAffineGeomPlace_of_jGeomGen_mem {K : Type*} [Field K] {N : ℕ} [NeZero N]
    (v : Place K (modularFunctionFieldC K N)) (hj : jGeomGen K N ∈ v.toValuationSubring) :
    IsAffineGeomPlace K N v :=
  ⟨hj, jNGeomGen_mem_of_jGeomGen_mem v hj⟩

section Packet

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring 𝕂}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral 𝕂 N q}
  {hβ : HeckeBetaBarIntegral 𝕂 N q}

noncomputable def jBarN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (modularFunctionField_le_full N (jq_mem N))⟩

theorem mem_of_ord_sub_algebraMap_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (g : F) (c : K)
    (h : 0 < v.ord (g - algebraMap K F c)) : g ∈ v.toValuationSubring := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' _
  have hdm : g - algebraMap K F c ∈ v.toValuationSubring := by
    by_cases h0 : g - algebraMap K F c = 0
    · rw [h0]; exact zero_mem _
    · exact v.mem_of_ord_nonneg h0 h.le
  have := add_mem hdm hcm
  rwa [sub_add_cancel] at this

theorem isAffineGeomPlace_sp_of_ord_pos (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place 𝕂 (modularFunctionFieldBar N)) (a : A)
    (h : 0 < w.ord (jBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂))) :
    IsAffineGeomPlace k N (P.sp w) :=
  isAffineGeomPlace_of_jGeomGen_mem _
    (mem_of_ord_sub_algebraMap_pos (P.sp w) (jGeomGen k N) (red a) (P.d0_j w a h))

theorem heckeAlphaBar_jBarN : heckeAlphaBar 𝕂 N q (jBarN N) = jFun N q :=
  Subtype.ext (coe_heckeAlphaBar N q _)

theorem heckeBetaBar_jBarN : heckeBetaBar 𝕂 N q (jBarN N) = jQFun N q := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand 𝕂 q (coeffEmb 𝕂 jq) = coeffEmb 𝕂 (qExpand ℚ q jq)
  rw [coeffEmb, ModularCurve.coeffMap_qExpand]

theorem isCuspidal_of_not_isAffineGeomPlace_reduceFst' (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place 𝕂 (modularFunctionFieldBar (N * q))) (hV : ¬ IsAffineGeomPlace k N (P.reduceFst V)) :
    IsCuspidal P V := by
  intro a
  by_contra h
  push Not at h
  apply hV

  have e : jFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂)
      = heckeAlphaBar 𝕂 N q (jBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂)) := by
    rw [map_sub, heckeAlphaBar_jBarN, AlgHom.commutes]
  rw [e, Place.ord_restrictAlong (heckeAlphaBar 𝕂 N q) hα] at h
  exact isAffineGeomPlace_sp_of_ord_pos P _ a (pos_of_mul_pos_right h (by exact_mod_cast Nat.zero_le _))

theorem isCuspidal'_of_not_isAffineGeomPlace_reduceSnd' (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place 𝕂 (modularFunctionFieldBar (N * q))) (hV : ¬ IsAffineGeomPlace k N (P.reduceSnd V)) :
    IsCuspidal' P V := by
  intro a
  by_contra h
  push Not at h
  apply hV
  have e : jQFun N q - algebraMap 𝕂 (modularFunctionFieldBar (N * q)) (a : 𝕂)
      = heckeBetaBar 𝕂 N q (jBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂)) := by
    rw [map_sub, heckeBetaBar_jBarN, AlgHom.commutes]
  rw [e, Place.ord_restrictAlong (heckeBetaBar 𝕂 N q) hβ] at h
  exact isAffineGeomPlace_sp_of_ord_pos P _ a (pos_of_mul_pos_right h (by exact_mod_cast Nat.zero_le _))

end Packet

end W3s

end ModularCurve

open ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : ¬ IsAffineGeomPlace k N (P.reduceFst V)) :
    ProlongationTuple.IsCuspidal P V :=
  ModularCurve.W3s.isCuspidal_of_not_isAffineGeomPlace_reduceFst' P V hV

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst (solution)
