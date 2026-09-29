-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a9c38e93-1f29-5f55-8150-85c928e4a380

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar jq ModularPolynomialData jq_mem modularFunctionField_le_full coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence jGeomGen"
namespace OrdPosN
p2m_open "ModularCurve"

local notation "𝕂" => AlgebraicClosure ℚ

p2m_open "ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]

noncomputable def jBarN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (modularFunctionField_le_full N (jq_mem N))⟩

theorem heckeAlphaBar_jBarN : heckeAlphaBar 𝕂 N q (jBarN N) = jFun N q :=
  Subtype.ext (coe_heckeAlphaBar N q _)

theorem ord_restrictAlong_pos {F F' : Type*} [Field F] [Field F'] [Algebra 𝕂 F] [Algebra 𝕂 F']
    (φ : F →ₐ[𝕂] F') (hφ : φ.toRingHom.IsIntegral) (Q : Place 𝕂 F') (f : F)
    (h : 0 < Q.ord (φ f)) : 0 < (Q.restrictAlong φ hφ).ord f := by
  rw [Place.ord_restrictAlong φ hφ] at h
  have he : (0 : ℤ) < (Place.ramificationIndexAlong φ Q : ℤ) := by
    exact_mod_cast Place.one_le_ramificationIndexAlong φ hφ Q
  exact pos_of_mul_pos_right h he.le

end ModularCurve.OrdPosN

open ModularCurve.OrdPosN ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (j₀ : A)
    (hQ : 0 < Q.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (j₀ : AlgebraicClosure ℚ))) :
    0 < (P.reduceFst Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red j₀)) := by
  set w := Q.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα with hw
  have e : ProlongationTuple.jFun N q
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (j₀ : AlgebraicClosure ℚ)
      = heckeAlphaBar (AlgebraicClosure ℚ) N q
          (jBarN N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (j₀ : AlgebraicClosure ℚ)) := by
    rw [map_sub, heckeAlphaBar_jBarN, AlgHom.commutes]
  rw [e] at hQ
  have hw' := ord_restrictAlong_pos _ hα Q _ hQ
  exact P.d0_j w j₀ hw'

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos (solution)
