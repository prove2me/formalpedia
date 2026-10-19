-- Prove2me | solution 2 for OAI.KervaireStrong.StrongTendsto.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:33:56.846992+00:00
-- url     : https://prove2.me/submissions/b2a3cb9a-ea13-4bce-9136-c40c0b01edda

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/StrongLimits.lean:L89-L103
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireStrong.StrongTendsto.nonneg. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits

-- ---- from OAI.GroupTheory.Kervaire.StrongLimits ----
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace KervaireStrong
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
open scoped ComplexOrder

/-- The positive cone is strongly closed, even on an uncountable Hilbert space. -/
theorem StrongTendsto.nonneg {T : ι → Operator K} {S : Operator K} [l.NeBot]
    (h : StrongTendsto T l S) (hp : ∀ i, 0 ≤ T i) : 0 ≤ S := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply (ContinuousLinearMap.isPositive_iff_complex S).mpr
  intro ξ
  have ht := Filter.Tendsto.inner (𝕜 := ℂ) (h ξ) (tendsto_const_nhds (x := ξ))
  have hi (i) := Complex.nonneg_iff.mp
    (((ContinuousLinearMap.nonneg_iff_isPositive _).mp (hp i)).inner_nonneg_left ξ)
  have hre : 0 ≤ (inner ℂ (S ξ) ξ).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp ht) (Eventually.of_forall fun i => (hi i).1)
  have him : (inner ℂ (S ξ) ξ).im = 0 :=
    tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp ht)
      (tendsto_const_nhds.congr fun i => (hi i).2)
  exact ⟨Complex.ext rfl (by simpa using him.symm), hre⟩

end KervaireStrong

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireStrong
open Filter
open scoped Topology
open scoped ComplexOrder


theorem solution : type_of% @_root_.OAI.KervaireStrong.StrongTendsto.nonneg := @_root_.OAI.KervaireStrong.StrongTendsto.nonneg
