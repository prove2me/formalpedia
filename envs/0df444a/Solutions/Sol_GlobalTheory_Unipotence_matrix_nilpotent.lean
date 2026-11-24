-- Prove2me | solution 1 for GlobalTheory.Unipotence.matrix_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:25.649543+00:00
-- url     : https://prove2.me/submissions/aca9f953-00cd-496d-9539-6d869753f930

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Theorems.Thm_GlobalTheory_Unipotence_pow_card_eq_zero
import Theorems.Thm_GlobalTheory_Unipotence_root_of_unity
import Theorems.Thm_GlobalTheory_Unipotence_eq_zero_of_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.Unipotence
open Polynomial
namespace GlobalTheory.Unipotence
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] (h3 : 3 ≤ l) {n : Type} [Fintype n]
    [DecidableEq n] (Y P : Matrix n n ℤ_[l]) (hA : IsUnit (1 + l • Y)) (hP : IsUnit P)
    (q : ℕ) (hq : 2 ≤ q) (h : P * (1 + l • Y) = (1 + l • Y) ^ q * P) : IsNilpotent Y := by
  let K := AlgebraicClosure ℚ_[l]
  have hinj : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  let f : Matrix n n ℤ_[l] →+* Matrix n n K := (algebraMap ℤ_[l] K).mapMatrix
  have hf : Function.Injective f := Matrix.map_injective hinj
  rw [← IsNilpotent.map_iff hf]
  apply pow_card_eq_zero
  intro μ hμ
  have hint : IsIntegral ℤ_[l] μ := by
    refine ⟨Y.charpoly, Y.charpoly_monic, ?_⟩
    have := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
    rw [show f Y = Y.map (algebraMap ℤ_[l] K) from rfl, Matrix.charpoly_map] at this
    rw [← Polynomial.eval_map]
    exact this
  have hspec : 1 + l • μ ∈ spectrum K (f (1 + l • Y)) := by
    have := spectrum.subset_polynomial_aeval (f Y) (1 + l • (X : K[X])) ⟨μ, hμ, rfl⟩
    simpa using this
  obtain ⟨m, hm, hx⟩ := root_of_unity (f (1 + l • Y)) (hA.map f) (hP.map f).unit q hq
    (by rw [IsUnit.unit_spec, ← map_mul, h, map_mul, map_pow]) _ hspec
  exact eq_zero_of_integral l h3 μ hint m hm hx
end GlobalTheory.Unipotence
