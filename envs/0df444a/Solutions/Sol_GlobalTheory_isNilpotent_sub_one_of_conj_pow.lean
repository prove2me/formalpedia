-- Prove2me | solution 1 for GlobalTheory.isNilpotent_sub_one_of_conj_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:34.952796+00:00
-- url     : https://prove2.me/submissions/d037e010-6482-49af-b28c-d530d7d8e256

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Theorems.Thm_GlobalTheory_Unipotence_matrix_nilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (S Φ : T ≃ₗ[ℤ_[l]] T) (q : ℕ), 2 ≤ q → Φ * S = S ^ q * Φ → (∀ x, ∃ y, S x - x = l • y) → IsNilpotent ((S : T →ₗ[ℤ_[l]] T) - 1) := by
  intro l _ h3 T _ _ _ _ S Φ q hq h hS
  classical
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose y hy using hS
  let Y : Module.End ℤ_[l] T := b.constr ℤ_[l] (fun i => y (b i))
  have hSY : (S : T →ₗ[ℤ_[l]] T) = 1 + l • Y := by
    apply b.ext
    intro i
    simp only [Y, LinearMap.add_apply, LinearMap.smul_apply, Module.Basis.constr_basis,
      Module.End.one_apply, LinearEquiv.coe_coe, ← hy]
    abel
  let g : (T ≃ₗ[ℤ_[l]] T) →* Module.End ℤ_[l] T := LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hgS : g S = 1 + l • Y := hSY
  let e := LinearMap.toMatrixAlgEquiv b
  have heS : e (g S) = 1 + l • e Y := by rw [hgS, map_add, map_one, map_nsmul]
  have hN : IsNilpotent (e Y) := by
    refine Unipotence.matrix_nilpotent l h3 (e Y) (e (g Φ)) ?_ (((Group.isUnit Φ).map g).map e) q hq ?_
    · rw [← heS]; exact ((Group.isUnit S).map g).map e
    · rw [← heS, ← map_mul, ← map_mul, h, map_mul, map_mul, map_pow, map_pow]
  rw [IsNilpotent.map_iff (f := e) e.injective] at hN
  rw [hSY, add_sub_cancel_left]
  exact hN.smul l
end GlobalTheory
