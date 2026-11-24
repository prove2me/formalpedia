-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.Adapted.prX_cjJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:00.140927+00:00
-- url     : https://prove2.me/submissions/61ad38e4-ef1a-48a1-8e3e-7c61efd0995b

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
import Theorems.Thm_GlobalTheory_CollapseCompare_Adapted_mem_N
import Theorems.Thm_GlobalTheory_CollapseCompare_Adapted_inv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_StepData_mem_Cgrp
import Theorems.Thm_GlobalTheory_StepData_mem_prX
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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CollapseCompare
namespace Adapted
theorem _root_.solution {t : GL (n ⊕ Fin c) k} (ht : Adapted t) (J : Subgroup (GL (n ⊕ Fin c) k)) :
    prX (Cgrp (cjJ t J) 1) = prX (Cgrp J 1) := by
  have hR : ∀ u ∈ N k n c 1, ∀ g : GL n k, u * embX c g ∈ R k n c 1 := fun u hu g =>
    mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩)
  have e : ∀ u (g : GL n k), t * (u * embX c g) * t⁻¹ = t * u * t⁻¹ * embX c g := fun u g => by
    conv_rhs => rw [← ht.comm g]
    group
  ext g
  simp only [mem_prX, mem_Cgrp, inv_one, one_mul, mul_one]
  constructor
  · rintro ⟨u, hu, -, h⟩
    exact ⟨_, ht.mem_N.2 hu, hR _ (ht.mem_N.2 hu) g, e u g ▸ h⟩
  · rintro ⟨u, hu, -, h⟩
    refine ⟨_, ht.inv.mem_N.2 hu, hR _ (ht.inv.mem_N.2 hu) g, ?_⟩
    change t * _ * t⁻¹ ∈ J
    rw [e]
    simpa [mul_assoc] using h
end Adapted
end GlobalTheory.CollapseCompare
