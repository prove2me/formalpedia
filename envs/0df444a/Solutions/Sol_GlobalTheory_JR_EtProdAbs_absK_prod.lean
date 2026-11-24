-- Prove2me | solution 1 for GlobalTheory.JR.EtProdAbs.absK_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:41.605906+00:00
-- url     : https://prove2.me/submissions/3b1cf214-c101-41e9-91a0-b5da136b73df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplitting
import Theorems.Thm_GlobalTheory_JR_EtProdAbs_distribHaarChar_prod
import Theorems.Thm_GlobalTheory_JR_EtMeas_absK_unit
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_transport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtProdAbs
namespace GlobalTheory.JR.EtProdAbs
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  intro F E _ _ _ _ U A A₁ A₂ eK t
  have := U.ultraF; have := U.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.K
  by_cases ht : IsUnit t
  · let u : A.Kˣ := ht.unit
    let v : (A₁.K × A₂.K)ˣ := Units.map (eK : A.K →* A₁.K × A₂.K) u
    let e' : A.K ≃ₜ+ A₁.K × A₂.K :=
      { eK.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap eK.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap eK.symm.toLinearMap }
    have h1 : distribHaarChar (A₁.K × A₂.K) v = distribHaarChar A.K u :=
      ModuleNorm.distribHaarChar_transport e' u v (fun x => by
        change eK ((u : A.K) * x) = eK (u : A.K) * eK x
        rw [map_mul])
    rw [distribHaarChar_prod] at h1
    have ht' : t = (u : A.K) := (IsUnit.unit_spec ht).symm
    have e1 : (eK t).1 = ((Units.map (RingHom.fst A₁.K A₂.K : A₁.K × A₂.K →* A₁.K) v : A₁.Kˣ) : A₁.K) := by
      rw [ht']; rfl
    have e2 : (eK t).2 = ((Units.map (RingHom.snd A₁.K A₂.K : A₁.K × A₂.K →* A₂.K) v : A₂.Kˣ) : A₂.K) := by
      rw [ht']; rfl
    rw [e1, e2, ht', EtMeas.absK_unit, EtMeas.absK_unit, EtMeas.absK_unit, ← h1]
    push_cast
    rfl
  · have h0 : A.absK t = 0 := by simp [Et.absK, ht]
    have hn : ¬ IsUnit (eK t) := fun h => ht ((isUnit_map_iff eK t).1 h)
    rw [Prod.isUnit_iff, not_and_or] at hn
    rw [h0]
    rcases hn with hn | hn
    · have : A₁.absK (eK t).1 = 0 := by simp [Et.absK, hn]
      rw [this, zero_mul]
    · have : A₂.absK (eK t).2 = 0 := by simp [Et.absK, hn]
      rw [this, mul_zero]
end GlobalTheory.JR.EtProdAbs
