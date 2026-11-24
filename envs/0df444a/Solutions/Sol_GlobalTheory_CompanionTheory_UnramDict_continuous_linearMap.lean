-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.continuous_linearMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:11.065376+00:00
-- url     : https://prove2.me/submissions/7ab2e326-1bdc-439f-92d8-95306988f7db

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_t2Space_isNonarchimedeanLocalField_singleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]
namespace GlobalTheory.CompanionTheory.UnramDict
theorem _root_.solution [FiniteDimensional k E] [ContinuousSMul k E] (f : E →ₗ[k] E) :
    Continuous f := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  haveI := t2Space_isNonarchimedeanLocalField_singleBlock E
  exact f.continuous_of_finiteDimensional
end GlobalTheory.CompanionTheory.UnramDict
