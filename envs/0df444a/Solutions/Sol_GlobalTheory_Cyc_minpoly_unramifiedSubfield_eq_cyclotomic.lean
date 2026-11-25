-- Prove2me | solution 1 for GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:27:02.135975+00:00
-- url     : https://prove2.me/submissions/79a29b71-9b35-48a4-89c6-85c8652491d0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective
import Theorems.Thm_GlobalTheory_Cyc_aeval_ne_zero_of_norm_eq
import Theorems.Thm_GlobalTheory_T_norm_primitiveRoot_primePow_sub_one_padicComplex


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
theorem _root_.solution (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) : minpoly ↥(K0 K) ζ = cyclotomic (l ^ j) ↥(K0 K) := by
  have hlp : l.Prime := Fact.out
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  have hroot : aeval ζ (cyclotomic (l ^ j) ↥(K0 K)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hpos
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _)
    (minpoly.dvd _ _ hroot)
  rw [natDegree_cyclotomic]
  by_contra hlt
  push_neg at hlt
  refine aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 (minpoly ↥(K0 K) ζ)) ?_ ?_ ?_
  · intro h
    exact minpoly.ne_zero hint (taylor_injective 1 (by rw [h, map_zero]))
  · rwa [natDegree_taylor]
  · rw [taylor_apply, aeval_comp]
    simp
end GlobalTheory.Cyc
