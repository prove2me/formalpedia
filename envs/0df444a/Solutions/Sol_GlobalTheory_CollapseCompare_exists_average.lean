-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.exists_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:55.115802+00:00
-- url     : https://prove2.me/submissions/feb0ff21-32b1-4cf2-88ab-8c491fbbf87f

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp_of_intertwining
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
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
theorem _root_.solution (ρ : Representation ℂ G V) (hρ : IsSmoothRep ρ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) :
    ∃ e : V →ₗ[ℂ] V, (∀ g ∈ K, ∀ w, e (ρ g w) = e w) ∧ (∀ w, (∀ g ∈ K, ρ g w = w) → e w = w) ∧
      ∀ j : V →ₗ[ℂ] V, (∀ g w, j (ρ g w) = ρ g (j w)) → ∀ w, j (e w) = e (j w) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  borelize ↥K
  let η : Measure K := (Measure.haar : Measure K).inv
  have hne : ((η.real Set.univ : ℝ) : ℂ) ≠ 0 := by
    have : η.real Set.univ ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(isOpen_univ.measure_pos η Set.univ_nonempty).ne', measure_ne_top _ _⟩
    exact_mod_cast this
  let ρK : Representation ℂ K V := ρ.comp K.subtype
  have hs : PRep.IsSmooth ρK := fun v => (hρ v).preimage continuous_subtype_val
  let f : K → ℂ := fun _ => ((η.real Set.univ : ℝ) : ℂ)⁻¹
  have hf : IsLocallyConstant f := IsLocallyConstant.const _
  have hc : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  refine ⟨OpTrace.smoothOp ρK η f, fun g hg w => ?_, fun w hw => ?_, fun j hj w => ?_⟩
  · refine OpTrace.eq_of_forall_dual fun l => ?_
    rw [hs.map_smoothOp hf hc, hs.map_smoothOp hf hc,
      ← integral_mul_right_eq_self (μ := η) (fun x => f x • l (ρK x w)) ⟨g, hg⟩]
    congr 1
    funext x
    simp [ρK, f]
  · refine OpTrace.eq_of_forall_dual fun l => ?_
    rw [hs.map_smoothOp hf hc]
    have : (fun x : K => f x • l (ρK x w)) = fun _ => ((η.real Set.univ : ℝ) : ℂ)⁻¹ * l w :=
      funext fun x => by rw [show ρK x w = w from hw x x.2]; rfl
    rw [this, integral_const, Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · exact hs.map_smoothOp_of_intertwining hs hf hc j (fun g v => hj g v) w
end GlobalTheory.CollapseCompare
