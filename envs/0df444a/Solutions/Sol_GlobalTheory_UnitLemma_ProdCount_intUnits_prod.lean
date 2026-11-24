-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.intUnits_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:29.142171+00:00
-- url     : https://prove2.me/submissions/6f218ccc-2ac6-4c84-a202-773f9d66e56e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_isIntegral_prod_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [Algebra O A₁] [CommRing A₂] [Algebra O A₂]
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution (t : (A₁ × A₂)ˣ) :
    t ∈ intUnits O (A₁ × A₂) ↔
      (MulEquiv.prodUnits t).1 ∈ intUnits O A₁ ∧ (MulEquiv.prodUnits t).2 ∈ intUnits O A₂ := by
  change (IsIntegral O (t : A₁ × A₂) ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂)) ↔
    (IsIntegral O (t : A₁ × A₂).1 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).1) ∧
    (IsIntegral O (t : A₁ × A₂).2 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).2)
  rw [isIntegral_prod_iff, isIntegral_prod_iff]
  tauto
end GlobalTheory.UnitLemma.ProdCount
