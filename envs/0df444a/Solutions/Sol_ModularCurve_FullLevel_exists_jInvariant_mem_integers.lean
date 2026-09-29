-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_jInvariant_mem_integers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/048a9f10-243c-5ec4-958f-4e827fcf2e39

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_jInvariant_mem_integers

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_exists_jInvariant_mem_integers.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_jInvariant_mem_integers.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset coeff_jq_neg_one coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqModC_rat map_jqModC jqModC_eq_map_intCast jqModC_mem_intFormRatiosC"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "levelH fieldBar"
namespace JInv
p2m_open "ModularCurve.FullLevel ModularCurve"

private theorem coeffMap_jqModC' {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) :
    coeffMap f (jqModC S) = jqModC T :=
  map_jqModC f

private theorem coeff_jqModC_neg_one' (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have hZ : (jqModC ℤ).coeff (-1) = 1 := by
    have h := coeff_jq_neg_one
    rw [← jqModC_rat, jqModC_eq_map_intCast ℚ, HahnSeries.map_coeff, eq_intCast] at h
    exact_mod_cast h
  rw [jqModC_eq_map_intCast K, HahnSeries.map_coeff, hZ, map_one]

private theorem jqModC_mem_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) :
    jqModC (AlgebraicClosure ℚ) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := by
  have h1 : jqModC ℚ ∈ (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ)) :=
    intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  have h2 := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) h1
  have h3 : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  rwa [h3] at h2

end ModularCurve.FullLevel.JInv

open ModularCurve.FullLevel.JInv in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (R : RegularProlongation A (fieldBar q M')
      (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))))
    (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y) :
    ∃ (j : fieldBar q M') (hj : j ∈ R.integers),
      (j : LaurentSeries (AlgebraicClosure ℚ)) ∈
        laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) ∧
      ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)).coeff (-1) ≠ 0 ∧
      ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) ∈
        qExpFunctionFieldC (ResidueField A) (Gamma0 M') := by
  have hyA : coeffMap A.subtype (jqModC A) ∈ fieldBar q M' := by
    rw [coeffMap_jqModC']; exact jqModC_mem_laurentBaseChange _
  obtain ⟨hj, hres⟩ := hpin (jqModC A) hyA
  refine ⟨⟨coeffMap A.subtype (jqModC A), hyA⟩, hj, ?_, ?_, ?_⟩
  · change coeffMap A.subtype (jqModC A) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))
    rw [coeffMap_jqModC']; exact jqModC_mem_laurentBaseChange _
  · rw [hres, coeffMap_jqModC', coeff_jqModC_neg_one']; exact one_ne_zero
  · rw [hres, coeffMap_jqModC']
    exact intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC _ _)

end S_ModularCurve_FullLevel_exists_jInvariant_mem_integers
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_jInvariant_mem_integers (solution)
