-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSKType.kset_subset_ujset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:15.300567+00:00
-- url     : https://prove2.me/submissions/3d028bc8-e551-4be3-acf7-72b933659d56

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KsetSubsetUjset
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSKType
open CompanionTheory.D.DSIC PI.UpqRep
namespace GlobalTheory.CompanionTheory.DSKType
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨h1, h2⟩ := hg
  have h3 : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 h1)
  show inUJ ε g
  unfold inUJ
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]
end GlobalTheory.CompanionTheory.DSKType
