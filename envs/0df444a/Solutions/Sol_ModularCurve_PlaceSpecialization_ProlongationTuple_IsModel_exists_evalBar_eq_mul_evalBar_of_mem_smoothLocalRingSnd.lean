-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6992213d-827e-561f-8ded-add3922744ab

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Definitions.Def_MDivRepresents
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jNFun_sub_jNQFun_sub
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_evalBar_eq_mul_evalBar_of_mem_integersSnd_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsCentreOf IsAffineGeomPlace PlaceSpecialization.jNQFun PlaceSpecialization.evalBar PlaceSpecialization.IsSndTriple"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple reduceSnd IsStrictSnd jNQFun evalBar IsSndTriple exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd ProlongationTuple.exists_evalBar_eq_mul_evalBar_of_mem_integersSnd_of_isIntegral"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

namespace HartogsRootSnd

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem red_eq_zero_iff (R : ProlongationTuple P) (c : A) : red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by
  rw [← R.redBar_residue c, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]

theorem evalBar_mul (c : Option (Fin 2) → modularFunctionFieldBar (N * q)) (H s : MvPolynomial (Option (Fin 2)) A) :
    PlaceSpecialization.evalBar N q c (H * s) = PlaceSpecialization.evalBar N q c H * PlaceSpecialization.evalBar N q c s :=
  MvPolynomial.eval₂_mul _ _

theorem jFun_mem_integers₂ (R : ProlongationTuple P) (hqN : ¬ q ∣ N) : ProlongationTuple.jFun N q ∈ R.R₂.integers := by
  obtain ⟨-, h₂, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN 0
  simpa using h₂

theorem jQFun_mem_integers₂ (R : ProlongationTuple P) (hqN : ¬ q ∣ N) : ProlongationTuple.jQFun N q ∈ R.R₂.integers := by
  obtain ⟨-, -, -, h₄, -⟩ := R.residue_jFun_sub_jQFun_sub hqN 0
  simpa using h₄

theorem jNQFun_mem_integers₂ (R : ProlongationTuple P) (hqN : ¬ q ∣ N) : PlaceSpecialization.jNQFun N q ∈ R.R₂.integers := by
  obtain ⟨-, -, -, h₄, -⟩ := R.residue_jNFun_sub_jNQFun_sub hqN 0
  simpa using h₄

theorem algebraMap_mem_integers₂ (R : ProlongationTuple P) (a : A) :
    algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
  (R.R₂.algebraMap_mem_iff _).mpr a.2

theorem evalBar_mem_integers₂ (R : ProlongationTuple P) (hqN : ¬ q ∣ N) {v : Place k (modularFunctionFieldC k N)} {c₀ : k}
    {z y₁ y₂ : modularFunctionFieldBar (N * q)} (htr : PlaceSpecialization.IsSndTriple (q := q) v c₀ z y₁ y₂)
    (H : MvPolynomial (Option (Fin 2)) A) :
    PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) H ∈ R.R₂.integers := by
  have hz : z ∈ R.R₂.integers ∧ y₁ ∈ R.R₂.integers ∧ y₂ ∈ R.R₂.integers := by
    rcases htr with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩
    · exact ⟨jQFun_mem_integers₂ R hqN, jNQFun_mem_integers₂ R hqN, jFun_mem_integers₂ R hqN⟩
    · exact ⟨jNQFun_mem_integers₂ R hqN, jQFun_mem_integers₂ R hqN, jFun_mem_integers₂ R hqN⟩
  unfold PlaceSpecialization.evalBar
  induction H using MvPolynomial.induction_on with
  | C a => simpa using algebraMap_mem_integers₂ R a
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p i hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    refine mul_mem hp ?_
    rcases i with _ | i
    · exact hz.1
    · fin_cases i
      · exact hz.2.1
      · exact hz.2.2

end HartogsRootSnd

end ModularCurve.PlaceSpecialization

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd.ModularCurve.PlaceSpecialization in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q)
    (haff : IsAffineGeomPlace k N (P.reduceSnd Q))
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q)
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u : A) (w : Fin 2 → A)
    (htr : PlaceSpecialization.IsSndTriple (q := q) (P.reduceSnd Q) (red u) z y₁ y₂)
    (hu : 0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)))
    (hw : ∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j : AlgebraicClosure ℚ)))
    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ∈ R.smoothLocalRingSnd (P.reduceSnd Q)) :
    ∃ p s : MvPolynomial (Option (Fin 2)) A,
      PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) p =
        f * PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) s ∧
      red (MvPolynomial.eval (fun o => Option.elim o u w) s) ≠ 0  := by
  have hker := HartogsRootSnd.red_eq_zero_iff R
  have hf₂ : f ∈ R.R₂.integers := R.mem_integers_of_mem_smoothLocalRingSnd hf
  have hfW : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictSnd W → P.reduceSnd W = P.reduceSnd Q → f ∈ W.toValuationSubring :=
    fun W hW hv => R.mem_toValuationSubring_of_mem_smoothLocalRingSnd hf hW hv
  obtain ⟨H, hHred, hHint⟩ :=
    exists_red_eval_ne_zero_and_isIntegral_mul_evalBar_of_forall_isStrictSnd P hqN hker Q hQ hsm hgen
      z y₁ y₂ u w htr hu hw f hfW
  obtain ⟨p, s, hps, hs⟩ :=
    ProlongationTuple.exists_evalBar_eq_mul_evalBar_of_mem_integersSnd_of_isIntegral P hqN R Q hQ hsm hgen
      z y₁ y₂ u w htr hu hw _ (mul_mem hf₂ (HartogsRootSnd.evalBar_mem_integers₂ R hqN htr H)) hHint
  refine ⟨p, H * s, ?_, ?_⟩
  · rw [hps, HartogsRootSnd.evalBar_mul, mul_assoc]
  · rw [map_mul, map_mul]
    exact mul_ne_zero hHred hs

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd (solution)
