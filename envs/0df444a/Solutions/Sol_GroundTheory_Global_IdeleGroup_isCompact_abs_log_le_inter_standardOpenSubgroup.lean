-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isCompact_abs_log_le_inter_standardOpenSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:10:26.872673+00:00
-- url     : https://prove2.me/submissions/52d10a3b-ef90-43ea-8139-5ea5fb821824

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isCompact_infinite_abs_log_le
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isCompact_finite_units_integral
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (M : ℝ) :
    IsCompact {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : 𝔸[K]).1 w‖| ≤ M) ∧
      x ∈ standardOpenSubgroup K} := by
  let e := prodEquiv K
  have hc : IsCompact (e ⁻¹'
      ({y : (InfiniteAdeleRing K)ˣ |
        ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} ×ˢ
      {f : (FiniteAdeleRing (𝓞 K) K)ˣ | ∀ v : HeightOneSpectrum (𝓞 K),
        (f : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
          ((f⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
            v.adicCompletionIntegers K})) :=
    e.toHomeomorph.isCompact_preimage.2
      ((isCompact_infinite_abs_log_le K M).prod (isCompact_finite_units_integral K))
  convert hc using 1
  ext x
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, (mem_standardOpenSubgroup K).1 h2⟩,
    fun ⟨h1, h2⟩ ↦ ⟨h1, (mem_standardOpenSubgroup K).2 h2⟩⟩
end GroundTheory.Global.IdeleGroup
