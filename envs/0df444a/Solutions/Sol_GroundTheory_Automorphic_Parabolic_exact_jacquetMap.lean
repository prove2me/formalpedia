-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exact_jacquetMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:25.495058+00:00
-- url     : https://prove2.me/submissions/72dce0b1-42a7-4dca-bfc1-082e92eb09bd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_comp_subtype
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_compactOpen_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_exact_coinvariantsMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V)
variable {π} {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ (GL (Fin n) F) V'}
  {V'' : Type*} [AddCommGroup V''] [Module ℂ V''] {π'' : Representation ℂ (GL (Fin n) F) V''}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ' : IsSmooth π') (hπ'' : IsSmooth π'')
    (f : Representation.IntertwiningMap π π') (g : Representation.IntertwiningMap π' π'')
    (hfg : Function.Exact f g) :
    Function.Exact (jacquetMap F n β f) (jacquetMap F n β g) := by
  have : LocallyCompactSpace (unipotentRadical F n β) :=
    isClosed_unipotentRadical.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact exact_coinvariantsMap exists_compactOpen_unipotentRadical
    (isSmooth_comp_subtype hπ' _) (isSmooth_comp_subtype hπ'' _)
    (restrictN F n β f) (restrictN F n β g) hfg
end GroundTheory.Automorphic.Parabolic
