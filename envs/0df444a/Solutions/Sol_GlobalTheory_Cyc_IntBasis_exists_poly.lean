-- Prove2me | solution 1 for GlobalTheory.Cyc.IntBasis.exists_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:56.311047+00:00
-- url     : https://prove2.me/submissions/6d86c4d0-43c7-49a7-b40e-6a82da8bd507

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.IntBasis
theorem _root_.solution (K : FinExt l) (i : ℕ) (hi : 2 ≤ i) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ i))
    (x : Om l) (hx : x ∈ Ks K i) :
    ∃ p : (↥(Ks K (i - 1)))[X], p.natDegree < l ∧ aeval ζ p = x := by
  have hlp : l.Prime := Fact.out
  have hl0 : l ≠ 0 := hlp.ne_zero
  have hζl : ζ ^ l ∈ Ks K (i - 1) := by
    unfold Ks
    apply (le_sup_right : IntermediateField.adjoin ℚ_[l] _ ≤ K0 K ⊔ _)
    apply IntermediateField.subset_adjoin
    show (ζ ^ l) ^ l ^ (i - 1) = 1
    rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ i)]
    exact hζ.pow_eq_one
  set F := Ks K (i - 1) with hF
  set p0 : (↥F)[X] := X ^ l - C ⟨ζ ^ l, hζl⟩ with hp0
  have hmon : p0.Monic := monic_X_pow_sub_C _ hl0
  have hroot : aeval ζ p0 = 0 := by
    simp [hp0]
  have hint : IsIntegral F ζ := ⟨p0, hmon, by rw [← aeval_def]; exact hroot⟩
  have hdeg : (minpoly F ζ).natDegree ≤ l := by
    have h1 := natDegree_le_natDegree (minpoly.min F ζ hmon hroot)
    have h2 : p0.natDegree = l := natDegree_X_pow_sub_C
    omega
  have hle : Ks K i ≤ (IntermediateField.adjoin F {ζ}).restrictScalars ℚ_[l] := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    unfold Ks
    apply sup_le
    · exact le_sup_left.trans (le_sup_left : F ≤ F ⊔ _)
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have : NeZero (l ^ i) := ⟨pow_ne_zero _ hl0⟩
      obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
      exact pow_mem ((le_sup_right : IntermediateField.adjoin ℚ_[l] {ζ} ≤ F ⊔ _)
        (IntermediateField.subset_adjoin _ _ (Set.mem_singleton ζ))) k
  have hxF : x ∈ IntermediateField.adjoin F {ζ} :=
    (IntermediateField.mem_restrictScalars ℚ_[l]).1 (hle hx)
  obtain ⟨f, hfdeg, hf⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval ⟨x, hxF⟩
  refine ⟨f, lt_of_lt_of_le hfdeg hdeg, ?_⟩
  have := congrArg (fun y : IntermediateField.adjoin F {ζ} => (y : Om l)) hf
  simp only [IntermediateField.adjoin.powerBasis_gen] at this
  rw [← IntermediateField.aeval_coe, IntermediateField.AdjoinSimple.coe_gen] at this
  exact this.symm
end GlobalTheory.Cyc.IntBasis
