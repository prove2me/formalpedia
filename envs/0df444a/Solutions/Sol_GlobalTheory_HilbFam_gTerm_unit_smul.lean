-- Prove2me | solution 1 for GlobalTheory.HilbFam.gTerm_unit_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:30:18.431642+00:00
-- url     : https://prove2.me/submissions/fcd1bbee-d92b-42de-9305-1bda147b6bdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSummandUnitSmul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_prod_emb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem coord_unit_smul {F : Type} [Field F]
    (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (ε : (𝓞 F)ˣ) (x : Fin 2 → F) (τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.HilbFam.coord b a (ε • x) τ =
      (τ ((ε : 𝓞 F) : F) : ℂ) * _root_.GlobalTheory.HilbFam.coord b a x τ := by
  have hsmul : ∀ j, (ε • x) j = ((ε : 𝓞 F) : F) * x j := fun j => rfl
  simp only [_root_.GlobalTheory.HilbFam.coord, hsmul, map_mul, Complex.ofReal_mul]
  ring
end GlobalTheory.HilbFam
end

set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
set_option autoImplicit false
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
namespace _root_.GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (σ : ℂ) (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ)
    (ε : (𝓞 F)ˣ) (x : Fin 2 → F), Even k → _root_.GlobalTheory.HilbFam.gTerm k σ b a (ε • x) = _root_.GlobalTheory.HilbFam.gTerm k σ b a x := by
  intro F _ _ _ k σ b a ε x hk
  have hprod : ∏ τ, _root_.GlobalTheory.HilbFam.coord b a (ε • x) τ =
      ((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℂ) * ∏ τ, _root_.GlobalTheory.HilbFam.coord b a x τ := by
    simp only [coord_unit_smul, Finset.prod_mul_distrib]
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb]
  have hN : Algebra.norm ℚ ((ε : 𝓞 F) : F) = 1 ∨ Algebra.norm ℚ ((ε : 𝓞 F) : F) = -1 :=
    abs_eq (zero_le_one) |>.mp (NumberField.Units.norm F ε)
  unfold _root_.GlobalTheory.HilbFam.gTerm
  rw [hprod]
  rcases hN with hN | hN <;> simp [hN, hk.neg_pow]
end _root_.GlobalTheory.HilbFam
end GlobalTheory.HilbFam
