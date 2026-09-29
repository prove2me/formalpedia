-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.depthDual_eq_zero_of_isGoodDiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f880fa03-606e-5d38-ad64-24ab843a3566

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_depthDual_eq_zero_of_isGoodDiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_depthDual_eq_zero_of_isGoodDiv.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.depthDiv PlaceSpecialization.depthDual modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence fst_mem_of_mem_nodePairsOfPlaces"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "depthDiv depthDual reduceFst IsStrictFst IsStrictSnd IsGoodDiv sndDiv"
namespace TGoodN
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
  (g : SemilinearAut k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))

theorem depthDiv_apply_eq_zero_of_forall_ne (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) (h : ∀ V ∈ D.support, P.reduceFst V ≠ w) :
    P.depthDiv depth D w = 0 := by
  classical
  unfold PlaceSpecialization.depthDiv
  rw [Finsupp.sum_apply]
  exact Finset.sum_eq_zero fun V hV => by simp only [Finsupp.single_apply, if_neg (h V hV)]

theorem depthDual_eq_zero_of_forall_reduceFst_not_mem (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hD : ∀ V ∈ D.support, P.reduceFst V ∉ W) : P.depthDual g W depth D = 0 := by
  unfold PlaceSpecialization.depthDual
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [depthDiv_apply_eq_zero_of_forall_ne depth D _ (fun V hV heq => hD V hV ?_), zero_smul]
  rw [heq]
  exact fst_mem_of_mem_nodePairsOfPlaces s.2

theorem reduceFst_not_mem_of_isStrict (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hW : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (hV : P.IsStrictFst V ∨ P.IsStrictSnd V) : P.reduceFst V ∉ W := by
  intro hm
  rcases hV with ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact h2 (hW _ hm)
  · apply h2
    apply frobOnPlacesGeomLevel_injective k N data hKr
    have h3 := hW _ hm
    rw [h1] at h3
    exact h3

end ModularCurve.PlaceSpecialization.TGoodN

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (g : SemilinearAut k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hgood : P.IsGoodDiv D) :
    P.depthDual g W depth D = 0 := by
  exact ModularCurve.PlaceSpecialization.TGoodN.depthDual_eq_zero_of_forall_reduceFst_not_mem depth g W D
    fun V hV => ModularCurve.PlaceSpecialization.TGoodN.reduceFst_not_mem_of_isStrict W P hW (hgood V hV)

end

end S_ModularCurve_PlaceSpecialization_depthDual_eq_zero_of_isGoodDiv
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_depthDual_eq_zero_of_isGoodDiv (solution)
