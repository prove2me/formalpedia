-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.exists_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:43:30.254488+00:00
-- url     : https://prove2.me/submissions/f248e718-af5f-4109-bc03-ee87c464b826

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_exists_average
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_exists_average
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_smoothRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CollapseCompare
theorem _root_.solution {H : Type} [Group H] (ρ : Representation ℂ G V) (hρ : IsSmoothRep ρ)
    (π : Representation ℂ H V) (hcomm : ∀ g h w, π h (ρ g w) = ρ g (π h w)) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module ℂ P) (π' : Representation ℂ G P) (θ : P →ₗ[ℂ] V →ₗ[ℂ] V) (φ : P),
      IsSmoothRep π' ∧ (∀ g h T w, θ (π' g T) (ρ g (π h w)) = π h (θ T w)) ∧
        ∀ w, (∀ g ∈ K, ρ g w = w) → θ φ w = w := by
  obtain ⟨e, he1, he2, he3⟩ := exists_average ρ hρ K hK
  let τ := Representation.linHom ρ (Representation.trivial ℂ G V)
  let U : Submodule ℂ (V →ₗ[ℂ] V) :=
    { carrier := {T | ∀ h w, T (π h w) = π h (T w)}
      add_mem' := fun ha hb h w => by simp [ha h w, hb h w]
      zero_mem' := fun h w => by simp
      smul_mem' := fun z T hT h w => by simp [hT h w] }
  have hτ : ∀ g T w, τ g T w = T (ρ g⁻¹ w) := fun _ _ _ => rfl
  let τU := PRep.sub τ U fun g T hT h w => by rw [hτ, hτ, ← hcomm, hT]
  let eU : U := ⟨e, fun h w => (he3 (π h) (fun g w => hcomm g h w) w).symm⟩
  have heU : eU ∈ PRep.smoothPart τU :=
    SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset (hKo.mem_nhds (one_mem _)) fun g hg =>
      Subtype.ext (LinearMap.ext fun w => he1 g⁻¹ (inv_mem hg) w))
  refine ⟨PRep.smoothPart τU, Submodule.addCommGroup _, Submodule.module _, PRep.smoothRep τU,
    U.subtype ∘ₗ (PRep.smoothPart τU).subtype, ⟨eU, heU⟩, SmGL.isSmooth_smoothRep _, fun g h T w => ?_, he2⟩
  refine Eq.trans ?_ (T.1.2 h w)
  change T.1.1 (ρ g⁻¹ (ρ g (π h w))) = _
  rw [← Module.End.mul_apply (ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
end GlobalTheory.CollapseCompare
