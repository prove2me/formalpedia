-- Prove2me | solution 1 for GlobalTheory.LatPair.VolStep.isCompact_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:38.224189+00:00
-- url     : https://prove2.me/submissions/5450fbdf-e647-481e-9e65-afc73f4e4e96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlagVolumeOpenFiniteNonzero
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.VolStep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LatPair.VolStep
theorem _root_.solution {n : Type} [Fintype n] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsCompact (L : Set (n → k)) := by
  classical
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h0 : IsCompact (stdLat k n : Set (n → k)) := by
    have := isCompact_univ_pi fun _ : n => isCompact_int k
    convert this using 1
    ext x
    simp only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]
  have h1 := h0.image (f := fun x : n → k => g.val *ᵥ x) (continuous_const.matrix_mulVec continuous_id)
  convert h1 using 1
  ext x
  simp only [SetLike.mem_coe, mem_smul_iff, Set.mem_image]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    show g • (g⁻¹ • x) = x
    simp
  · rintro ⟨y, hy, rfl⟩
    show g⁻¹ • (g • y) ∈ _
    simpa using hy
end GlobalTheory.LatPair.VolStep
