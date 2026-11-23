-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.cre_ann_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:28.416966+00:00
-- url     : https://prove2.me/submissions/85c2731b-abea-4da1-9cab-4f8b8ed4939f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
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
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {Z : Type} [AddCommGroup Z] [Module ℂ Z]
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution (i : NC ε) (x : Ch ε Z) (A : Finset (NC ε)) :
    (cre i (ann i x)) A = if i ∈ A then x A else 0 := by
  by_cases h : i ∈ A
  · have e : sg i (A.erase i) = sg i A := by
      unfold sg
      congr 2
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨fun hh => by rw [hh] at h2; exact lt_irrefl _ h2, h1⟩, h2⟩
    have e2 : sg i A * sg i A = 1 := by
      unfold sg
      rw [← mul_pow]; simp
    simp [cre, ann, h, e, Finset.insert_erase h, smul_smul, e2]
  · simp [cre, h]
end GlobalTheory.CompanionTheory.DSICKoszul
