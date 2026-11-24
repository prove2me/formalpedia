-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Par.parJ_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:52:01.264649+00:00
-- url     : https://prove2.me/submissions/f065fa07-5309-46ca-a35d-2d6464c8a38b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isCompact_GLint
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isOpen_parJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Par
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Par
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
    LF O ϖ nrm q → ∀ r c : ℕ, ∃ J : Subgroup (GL (Fin (r + c)) F),
      (J : Set (GL (Fin (r + c)) F)) = parJ O ϖ r c ∧ IsOpen (parJ O ϖ r c) ∧
      IsCompact (parJ O ϖ r c) ∧ ∃ μ : Measure (GL (Fin (r + c)) F), μ.IsMulLeftInvariant ∧
        μ (parJ O ϖ r c) = 1 := by
  intro F _ _ _ _ O ϖ nrm q h r c
  have ho : IsOpen (parJ O ϖ r c) := isOpen_parJ h r c
  have hc : IsCompact (parJ O ϖ r c) :=
    (isCompact_GLint h (r + c)).of_isClosed_subset
      ((parSub O ϖ r c).isClosed_of_isOpen ho) fun k hk => hk.1
  refine ⟨parSub O ϖ r c, rfl, ho, hc, ?_⟩
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin (r + c)) F) :=
    ⟨⟨parJ O ϖ r c, hc⟩, ⟨1, by
      rw [ho.interior_eq]
      exact one_mem_parJ⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩
end GlobalTheory.CompanionTheory.QL.Par
