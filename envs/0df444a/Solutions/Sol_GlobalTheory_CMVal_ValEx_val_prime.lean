-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.val_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:37.559517+00:00
-- url     : https://prove2.me/submissions/2d56ef02-d134-4182-bfdd-dd908f5d312c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hd : ¬ (l : ℤ) ∣ discr E) (w : HeightOneSpectrum (𝓞 E))
    (hw : (l : 𝓞 E) ∈ w.asIdeal) : w.valuation E (l : E) = WithZero.exp (-1 : ℤ) := by
  have hP := w.isPrime
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd _ hP (by simpa using hw)
  have hov : w.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hw)
  have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hl0 : (l : 𝓞 E) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap]; simpa using hl.ne_zero
  have h1 := Ideal.ramificationIdx_eq_one w.asIdeal ℤ
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne, hmap] at h1
  have e : (l : E) = algebraMap (𝓞 E) E l := by simp
  rw [e, HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_eq_exp_neg_multiplicity hl0]
  have := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors w.irreducible
    (b := Ideal.span {(l : 𝓞 E)}) (by simpa using hl.ne_zero)
  rw [normalize_eq, h1] at this
  rw [multiplicity_eq_of_emultiplicity_eq_some this]; rfl
end GlobalTheory.CMVal.ValEx
