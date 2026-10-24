-- Prove2me | solution 1 for OAI.SplitTangent.integrability_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:38:10.015537+00:00
-- url     : https://prove2.me/submissions/ec167804-912b-419f-8959-1d1f6562c4ff

import Mathlib
import Definitions.Def_SplitTangentIntegrability
import Definitions.Def_OAIQWST002
import Theorems.Thm_OAI_SplitTangent_RationalFamily_integrable_both_of_submersive
import Theorems.Thm_OAI_SplitTangent_RationallyConnected_exists_submersive_familyAlternative

section
-- module Solutions.OAIQW_SplitTangent.RationalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Variation. -/

noncomputable section
open Set Filter Topology IsManifold
open scoped ContDiff Manifold
universe u
namespace SplitTangent
open AnalyticZeroCover RationalParameters



theorem TangentSplitting.integrable_of_rationallyConnected {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] [ConnectedSpace X.Carrier] (e : ProjectiveEmbedding X)
    (hRC : RationallyConnected e) (hdim : 2≤X.dim) (S : TangentSplitting X) :
    Integrable X S.first ∧ Integrable X S.second := by
  obtain ⟨T,hT,G,hs⟩ := hRC.exists_submersive_familyAlternative e (by omega)
  let := hT
  exact G.integrable_both_of_submersive e S hs

end SplitTangent

namespace SplitTangent


theorem integrability_main_oai : IntegrabilityStatement.{u} := by
  intro X hconn hcompact hdim e hRC S
  let := hconn
  let := hcompact
  exact S.integrable_of_rationallyConnected e hRC hdim
end SplitTangent

end

end OAI
end

theorem solution.{u} : type_of% @OAI.SplitTangent.integrability_main_oai.{u} := @OAI.SplitTangent.integrability_main_oai.{u}
