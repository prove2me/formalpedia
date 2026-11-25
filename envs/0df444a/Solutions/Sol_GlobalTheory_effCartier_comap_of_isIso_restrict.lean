-- Prove2me | solution 1 for GlobalTheory.effCartier_comap_of_isIso_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:05:50.01685+00:00
-- url     : https://prove2.me/submissions/41484101-cdec-458a-81a1-d51cd6f89983

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EffCartierComapOfIsIsoRestrictOpen
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  intro Y Y' s I U hiso hE
  have h1 : FinalTheorems.EffCartier ((I.comap s).comap (s ⁻¹ᵁ U).ι) :=
    effCartier_comap_of_isOpenImmersion' _ _ hE
  have h2 := effCartier_comap_of_isOpenImmersion' _ (inv (s ∣_ U)) h1
  have key : inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι ≫ s = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc, key] at h2
  exact h2
end GlobalTheory
