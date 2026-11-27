-- Prove2me | solution 1 for GroundTheory.Global.map_inertia_decompositionMulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:46:30.403056+00:00
-- url     : https://prove2.me/submissions/43eb8cce-2605-47c3-9661-dc18d8433681

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia
import Theorems.Thm_GroundTheory_Global_mem_inertia_iff_decompositionToLocal_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution :
    ((w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)).map
        (decompositionMulEquiv v w).toMonoidHom =
      lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 := by
  ext τ
  obtain ⟨σ, rfl⟩ := (decompositionMulEquiv v w).surjective τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ', hσ', h⟩
    rw [← h]
    exact (mem_inertia_iff_decompositionToLocal_mem v w σ').1 (Subgroup.mem_subgroupOf.1 hσ')
  · intro h
    exact ⟨σ, Subgroup.mem_subgroupOf.2 ((mem_inertia_iff_decompositionToLocal_mem v w σ).2 h),
      rfl⟩
end GroundTheory.Global
