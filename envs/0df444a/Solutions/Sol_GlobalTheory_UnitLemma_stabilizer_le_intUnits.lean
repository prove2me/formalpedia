-- Prove2me | solution 1 for GlobalTheory.UnitLemma.stabilizer_le_intUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:53.353751+00:00
-- url     : https://prove2.me/submissions/8c26dd97-0a9d-47af-9dbd-da30704da7fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticeLeIntegralUnitsSubgroup
import Theorems.Thm_GlobalTheory_UnitLemma_isIntegral_of_mul_mem_lat
import Theorems.Thm_GlobalTheory_UnitLemma_stLat_smul_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
namespace GlobalTheory.UnitLemma
theorem _root_.solution (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (g : A) (L : stLat O E g) : MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  intro t ht
  have key : ∀ s : Aˣ, s • L = L → ∀ y ∈ (L : Submodule O A), (s : A) * y ∈ (L : Submodule O A) := by
    intro s hs y hy
    have he : mulLat O (s : A) (L : Submodule O A) = L := by
      rw [← stLat_smul_val, hs]
    rw [← he]
    exact ⟨y, hy, rfl⟩
  have ht' : t⁻¹ ∈ MulAction.stabilizer Aˣ L := inv_mem ht
  exact ⟨isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t ht),
    isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t⁻¹ ht')⟩
end GlobalTheory.UnitLemma
