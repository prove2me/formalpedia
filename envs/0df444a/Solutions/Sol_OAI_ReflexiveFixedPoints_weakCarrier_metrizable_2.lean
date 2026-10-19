-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.weakCarrier_metrizable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:07:51.355417+00:00
-- url     : https://prove2.me/submissions/b4a9b76a-0983-4cd7-b001-2a7428354d7e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/WeakMetric.lean:L92-L119
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.weakCarrier_metrizable. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Theorems.Thm_OAI_ReflexiveFixedPoints_pairNormingFunctional_separates

-- ---- from OAI.Analysis.Nonexpansive.WeakMetric ----
namespace OAI

/-!
# Metrizability of norm-separable weakly compact sets

For a dense sequence in the norm carrier, choose a norming functional for
each pairwise difference. These countably many functionals separate the
points of the set. Their evaluations embed the compact weak carrier into
a countable product of real lines. No separability of the ambient space,
or of its entire dual, is assumed.
-/

noncomputable section

open Set TopologicalSpace NormedSpace
open scoped Pointwise

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual weak topology on a norm-separable weakly compact set is
metrizable. The empty set and zero ambient space are included. -/
theorem weakCarrier_metrizable {K : Set X} (hsep : IsSeparable K)
    (hcompact : WeaklyCompact K) : MetrizableSpace (WeakCarrier K) := by
  classical
  let : CompactSpace (WeakCarrier K) := hcompact.compactSpace
  by_cases hne : K.Nonempty
  · let : Nonempty K := hne.to_subtype
    let : SeparableSpace K := hsep.separableSpace
    obtain ⟨z, hz⟩ := exists_dense_seq K
    let e : WeakCarrier K → (ℕ × ℕ) → ℝ :=
      fun a ij => pairNormingFunctional z ij ((normToWeak K).symm a)
    have he : Continuous e := by
      apply continuous_pi
      intro ij
      exact (WeakBilin.eval_continuous (topDualPairing ℝ X).flip
        (pairNormingFunctional z ij)).comp continuous_subtype_val
    have hinj : Function.Injective e := by
      intro a b hab
      apply (normToWeak K).symm.injective
      exact pairNormingFunctional_separates z hz hab
    let : MetrizableSpace ((ℕ × ℕ) → ℝ) := UniformSpace.metrizableSpace
    exact (he.isClosedEmbedding hinj).isEmbedding.metrizableSpace
  · have hinj : Function.Injective (fun _ : WeakCarrier K => (0 : ℝ)) := by
      intro a b _
      exact (hne ⟨(toWeakSpace ℝ X).symm a, a.property⟩).elim
    exact ((continuous_const : Continuous (fun _ : WeakCarrier K => (0 : ℝ))).isClosedEmbedding
      hinj).isEmbedding.metrizableSpace

end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace NormedSpace
open scoped Pointwise


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.weakCarrier_metrizable.{u} := @_root_.OAI.ReflexiveFixedPoints.weakCarrier_metrizable.{u}
