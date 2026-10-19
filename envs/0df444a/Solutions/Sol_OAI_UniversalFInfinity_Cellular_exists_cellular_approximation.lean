-- Prove2me | solution 1 for OAI.UniversalFInfinity.Cellular.exists_cellular_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:51:19.452228+00:00
-- url     : https://prove2.me/submissions/94dba3b6-af2f-45c2-92c9-463140a5c1ae

import Mathlib
import Definitions.Def_OAIQWUFI004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace UniversalFInfinity.Cellular

open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]
variable {K : Type v} [MetricSpace K] [CompactSpace K]

theorem exists_cellular_approximation_oai (d : ℕ) (f : C(K,X)) (hf : ∀ x,f x ∈ C)
    (hdim : dimH (Set.univ : Set K) < d) :
    ∃ (g : C(K,Skeleton C d)) (H : f.Homotopy ((skeletonInclusion d).comp g)),
      ∀ t x, f x ∈ Skeleton C d → H (t,x) = f x := by
  exact exists_cellular_approximation_bundle d f hf hdim
end UniversalFInfinity.Cellular

open scoped TensorProduct

end

end OAI
end

theorem solution : type_of% @OAI.UniversalFInfinity.Cellular.exists_cellular_approximation_oai := @OAI.UniversalFInfinity.Cellular.exists_cellular_approximation_oai
