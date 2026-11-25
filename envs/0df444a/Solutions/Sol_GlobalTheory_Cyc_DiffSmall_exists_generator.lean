-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:25:52.316804+00:00
-- url     : https://prove2.me/submissions/d4e4dff7-07b9-4eb6-ace9-01bd62e33df3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_Formalism_L2_Pj_AvAlg_exists_adjoin_eq_top
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_faithful
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_isLocalHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] E] :
    ∃ x ∈ E, ‖x‖ ≤ 1 ∧ ∀ z ∈ E, ‖z‖ ≤ 1 → ∃ p : ℤ_[l][X], aeval x p = z := by
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] E
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] E
  have : Finite (IsLocalRing.ResidueField ℤ_[l]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := l)).toEquiv.symm
  obtain ⟨θ, hθ⟩ : ∃ θ : integralClosure ℤ_[l] E, Algebra.adjoin ℤ_[l] {θ} = ⊤ :=
    Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top (FaithfulSMul.algebraMap_injective _ _)
  refine ⟨((θ : E) : Om l), (θ : E).2, (mem_integralClosure_padicInt_iff E _).1 θ.2, fun z hz hn => ?_⟩
  have hm : (⟨⟨z, hz⟩, (mem_integralClosure_padicInt_iff E _).2 hn⟩ : integralClosure ℤ_[l] E) ∈
      Algebra.adjoin ℤ_[l] {θ} := by rw [hθ]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
  obtain ⟨p, hp⟩ := hm
  refine ⟨p, ?_⟩
  let φ : integralClosure ℤ_[l] E →ₐ[ℤ_[l]] Om l :=
    (E.val.restrictScalars ℤ_[l]).comp (integralClosure ℤ_[l] E).val
  have := congrArg φ hp
  rw [show (aeval θ).toRingHom p = aeval θ p from rfl, ← aeval_algHom_apply] at this
  exact this
end GlobalTheory.Cyc.DiffSmall
