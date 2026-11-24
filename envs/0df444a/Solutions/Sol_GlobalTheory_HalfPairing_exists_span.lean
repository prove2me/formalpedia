-- Prove2me | solution 1 for GlobalTheory.HalfPairing.exists_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:56.520276+00:00
-- url     : https://prove2.me/submissions/17e05688-8b04-4050-8e5d-380aea7d2606

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HalvesFreeAndAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HalfPairing
namespace GlobalTheory.HalfPairing
theorem _root_.solution {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) : ∃ x : Fin r → Q, Submodule.span R (Set.range x) = ⊤ := by
  refine ⟨fun b => e.symm (Pi.single b 1), eq_top_iff.2 fun q _ => ?_⟩
  have h : q = ∑ b, e.symm (Pi.single b (e q b)) := by
    rw [← map_sum, Finset.univ_sum_single, e.symm_apply_apply]
  rw [h]
  refine Submodule.sum_mem _ fun b _ => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e q b)
  have : (Pi.single b (e q b) : Fin r → R ⧸ I) = a • Pi.single b 1 := by
    rw [← Pi.single_smul, ← ha, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
end GlobalTheory.HalfPairing
