-- Prove2me | solution 1 for GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:17.682669+00:00
-- url     : https://prove2.me/submissions/e5a63d01-a611-4efc-a626-bb8a096c979a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MatMapTmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLeMaximalIdealPowSmulOfDirected
import Theorems.Thm_GlobalTheory_Chevalley_isArtinian_quotient_smul_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Chevalley
namespace GlobalTheory.Chevalley
theorem _root_.solution (B M ι : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M] (K : ι → Submodule B M)
    [Nonempty ι] (hK : Directed (· ≥ ·) K) (k : ℕ) :
    ∃ i, ∀ j, K i ≤ K j ⊔ maximalIdeal B ^ k • (⊤ : Submodule B M) := by
  set P := maximalIdeal B ^ k • (⊤ : Submodule B M)
  haveI := isArtinian_quotient_smul_top B M k
  obtain ⟨_, ⟨i, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal
    (Set.range fun i ↦ (K i).map P.mkQ) (Set.range_nonempty _)
  refine ⟨i, fun j ↦ ?_⟩
  obtain ⟨l, hli, hlj⟩ := hK i j
  have hle : (K l).map P.mkQ ≤ (K i).map P.mkQ := Submodule.map_mono hli
  have heq : (K l).map P.mkQ = (K i).map P.mkQ := by
    by_contra hne
    exact hmin _ ⟨l, rfl⟩ (lt_of_le_of_ne hle hne)
  have h2 : (K i).map P.mkQ ≤ (K j).map P.mkQ := heq ▸ Submodule.map_mono hlj
  have h3 := Submodule.comap_mono (f := P.mkQ) h2
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ] at h3
  exact le_sup_right.trans (h3.trans (by rw [sup_comm]))
end GlobalTheory.Chevalley
