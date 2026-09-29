-- Prove2me | solution 1 for NumberField.InfPlaceDecomp.exists_equiv_sigma_quotient_decomp_above
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/19ab76a6-9576-59ea-8671-283c604d4def

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfPlaceDecomp_exists_equiv_sigma_quotient_decomp_above

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation IsDedekindDomain NumberField NumberField.LevelArith"
open scoped Classical NumberField.LevelArith NumberField.PlaceTransport NumberField Pointwise

namespace OrbitStabInf

open NumberField.InfinitePlace

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

noncomputable def fiberEquivOrbit (v : NumberField.InfinitePlace E) :
    {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v} ≃
      ↥(MulAction.orbit (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v)) :=
  Equiv.subtypeEquivRight fun w => by
    rw [NumberField.InfinitePlace.mem_orbit_iff, NumberField.ArchIdele.comap_above]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

noncomputable def e : NumberField.InfinitePlace K ≃
    Σ v : NumberField.InfinitePlace E, (K ≃ₐ[E] K) ⧸ MulAction.stabilizer (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v) :=
  (Equiv.sigmaFiberEquiv (fun w : NumberField.InfinitePlace K => w.comap (algebraMap E K))).symm.trans
    (Equiv.sigmaCongrRight fun v =>
      (fiberEquivOrbit E K v).trans (MulAction.orbitEquivQuotientStabilizer (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v)))

lemma e_symm_mk (v : NumberField.InfinitePlace E) (g : K ≃ₐ[E] K) :
    (e E K).symm ⟨v, (g : (K ≃ₐ[E] K) ⧸ MulAction.stabilizer (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v))⟩ =
      g • NumberField.ArchIdele.above E K v := rfl

lemma e_symm_smul (σ : K ≃ₐ[E] K)
    (y : Σ v : NumberField.InfinitePlace E, (K ≃ₐ[E] K) ⧸ MulAction.stabilizer (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v)) :
    (e E K).symm (σ • y) = σ • (e E K).symm y := by
  obtain ⟨v, c⟩ := y
  induction c using QuotientGroup.induction_on with
  | H g =>
    show (e E K).symm ⟨v, ((σ * g : K ≃ₐ[E] K) : (K ≃ₐ[E] K) ⧸ _)⟩ = σ • (e E K).symm ⟨v, (g : (K ≃ₐ[E] K) ⧸ _)⟩
    rw [e_symm_mk, e_symm_mk, mul_smul]

end OrbitStabInf

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K] :
    ∃ e : NumberField.InfinitePlace K ≃
        Σ v : NumberField.InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v),
      ∀ (σ : K ≃ₐ[E] K) (w : NumberField.InfinitePlace K), e (σ • w) = σ • e w :=
  ⟨OrbitStabInf.e E K, fun σ w => by
    rw [Equiv.apply_eq_iff_eq_symm_apply, OrbitStabInf.e_symm_smul, Equiv.symm_apply_apply]⟩

end S_NumberField_InfPlaceDecomp_exists_equiv_sigma_quotient_decomp_above
end P2MW
export P2MW.S_NumberField_InfPlaceDecomp_exists_equiv_sigma_quotient_decomp_above (solution)
