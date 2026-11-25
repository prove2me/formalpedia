-- Prove2me | solution 1 for GlobalTheory.Cyc.finrank_Ks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:37:17.010203+00:00
-- url     : https://prove2.me/submissions/09d1f732-97fe-47a6-b68e-181f3d1d62de

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective
import Theorems.Thm_GlobalTheory_Cyc_minpoly_unramifiedSubfield_eq_cyclotomic
import Theorems.Thm_GlobalTheory_Cyc_exists_primitiveRoot_Om
import Theorems.Thm_GlobalTheory_Cyc_Ks_eq_restrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) :
    Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1)) := by
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ]
  have h1 : Module.finrank ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯) = (l - 1) * l ^ (j - 1) := by
    rw [IntermediateField.adjoin.finrank hint, minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ,
      natDegree_cyclotomic, Nat.totient_prime_pow hlp hj, mul_comm]
  rw [← h1]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯)).symm
end GlobalTheory.Cyc
