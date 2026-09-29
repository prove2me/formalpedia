-- Prove2me | solution 1 for ModularCurve.hasLowerLevelTorsion_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1a24f7e4-07c2-5949-8a8f-1aa51b385198

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasLowerLevelTorsion_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

open MvPolynomial in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hin : HeckeInputsAll (N₀ * p)) (hcomm : HeckeOperatorsCommuteBar (N₀ * p))
    (hinN : HeckeInputsAll N₀) (hcommN : HeckeOperatorsCommuteBar N₀)
    (S : Finset Nat.Primes) (hS : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ p → ℓ ∈ S)
    (𝔪 : Ideal HeckeAlg)
    (x : JZero (N₀ * p))
    (hx𝔪 : letI := heckeModuleBar (N₀ * p); x ∈ heckeTorsion (JZero (N₀ * p)) 𝔪)
    (hx : degeneracyPushforwardPair N₀ p 0 x ≠ 0 ∨ degeneracyPushforwardPair N₀ p 1 x ≠ 0) :
    letI := heckeModuleBar N₀
    HasLowerLevelTorsion S 𝔪 (JZero N₀) := by
  letI hM : Module HeckeAlg (JZero (N₀ * p)) := heckeModuleBar (N₀ * p)
  letI hM₀ : Module HeckeAlg (JZero N₀) := heckeModuleBar N₀
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, degeneracyPushforwardPair N₀ p i x ≠ 0 :=
    hx.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
  have hxt : ∀ t ∈ 𝔪, t • x = 0 := (mem_heckeTorsion_iff (JZero (N₀ * p)) 𝔪 x).mp hx𝔪
  refine ⟨degeneracyPushforwardPair N₀ p i x, hi, ?_, ?_⟩
  · intro n hn
    have h := hxt _ hn
    rw [Nat.cast_smul_eq_nsmul] at h ⊢
    rw [← map_nsmul, h, map_zero]
  · intro ℓ hℓ b hb
    have hℓp : ¬ (ℓ : ℕ) ∣ p := fun h => hℓ (hS ℓ h)
    have h := hxt _ hb
    rw [sub_smul, heckeModuleBar_heckeGen_smul hcomm, heckeModuleBar_C_smul] at h
    rw [sub_smul, heckeModuleBar_heckeGen_smul hcommN, heckeModuleBar_C_smul,
      ← degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd N₀ p hin hinN ℓ hℓp i x, ← map_zsmul, ← map_sub, h, map_zero]

end S_ModularCurve_hasLowerLevelTorsion_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero
end P2MW
export P2MW.S_ModularCurve_hasLowerLevelTorsion_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero (solution)
