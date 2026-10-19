-- Prove2me | solution 1 for OAI.KervaireSpectral.exists_strongLimit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:36:54.1736+00:00
-- url     : https://prove2.me/submissions/c59e4b90-fcf3-4c07-ba2c-13c1bde85f9d

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralMeasures.lean:L208-L228
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.exists_strongLimit. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Theorems.Thm_OAI_KervaireSpectral_cauchySeq_calculus

-- ---- from OAI.GroupTheory.Kervaire.SpectralMeasures ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- A uniformly bounded convergent continuous approximation defines a bounded
operator, without a separability restriction on the Hilbert space. -/
theorem exists_strongLimit (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : spectrum ℂ U → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) :
    ∃ T : Operator H, (∀ ξ, Tendsto (fun n => cfcHom hU (f n) ξ) atTop (𝓝 (T ξ))) ∧
      ‖T‖ ≤ C := by
  have hc := fun ξ => cauchySeq_calculus U f g C hC hb ht ξ
  choose T hT using fun ξ => cauchySeq_tendsto_of_complete (hc ξ)
  have hnorm : ∀ n, ‖cfcHom hU (f n)‖ ≤ C := by
    intro n
    rw [norm_cfcHom U (f n) hU]
    exact ((f n).norm_le hC).mpr (hb n)
  let L : Operator H := ContinuousLinearMap.ofTendstoOfBoundedRange T
    (fun n => cfcHom hU (f n)) (tendsto_pi_nhds.mpr hT)
    (isBounded_iff_forall_norm_le.mpr ⟨C, by rintro _ ⟨n, rfl⟩; exact hnorm n⟩)
  refine ⟨L, hT, ContinuousLinearMap.opNorm_le_bound L hC fun ξ => ?_⟩
  apply le_of_tendsto (hT ξ).norm
  exact Eventually.of_forall fun n =>
    (cfcHom hU (f n)).le_of_opNorm_le (hnorm n) ξ

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.KervaireSpectral.exists_strongLimit := @_root_.OAI.KervaireSpectral.exists_strongLimit
