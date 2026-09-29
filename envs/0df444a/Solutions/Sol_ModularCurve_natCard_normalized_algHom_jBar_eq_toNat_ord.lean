-- Prove2me | solution 1 for ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/727c0497-d736-5074-a299-2a91db87d09d

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_exists_finset_ord_jBar_sub_pos
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_order_eq_ord
import Theorems.Thm_ModularCurve_natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord
import Theorems.Thm_LaurentSeries_exists_algHom_comp_map_eq_single
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.LaurentSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord.ModularCurve"

private theorem finrankAdjoinJBar (N : ℕ) [NeZero N] :
    Module.finrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) = dedekindPsi N := by
  have hcm : IntermediateField.comap (modularFunctionFieldBar N).val
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))} :
            Set (LaurentSeries (AlgebraicClosure ℚ))))
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)) := by
    rw [← IntermediateField.lift_adjoin_simple]
    exact IntermediateField.comap_map (modularFunctionFieldBar N).val _
  have h1 := IntermediateField.finrank_comap
    (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))} :
        Set (LaurentSeries (AlgebraicClosure ℚ))))
    (modularFunctionFieldBar N).val
  rw [hcm, IntermediateField.fieldRange_val] at h1
  have h2 : IntermediateField.relfinrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))} :
          Set (LaurentSeries (AlgebraicClosure ℚ))))
      (modularFunctionFieldBar N) = dedekindPsi N := by
    rw [← ModularCurve.relfinrank_full_eq_dedekindPsi N,
      ← ModularCurve.relfinrank_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N]
  rw [← h2]
  exact h1

namespace ModularCurve p2m_export "ModularCurve" "dedekindPsi jBar modularFunctionFieldBar sum_ord_jBar_sub_eq_dedekindPsi exists_finset_ord_jBar_sub_pos deg_eq_one_modularFunctionFieldBar dedekindPsi_pos natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      Nat.card {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
        ∃ g : ℚ, 0 < g ∧ ∀ x, (w.ord x : ℚ) * g = (ψ x).order} =
      (w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat := by
  haveI : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) :=
    Module.finite_of_finrank_pos (by
      rw [finrankAdjoinJBar]
      exact ModularCurve.dedekindPsi_pos N (NeZero.ne N))
  have hFINRANK := finrankAdjoinJBar N

  have hPEO2 := ModularCurve.natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord N j₀
  obtain ⟨S, hS⟩ := ModularCurve.exists_finset_ord_jBar_sub_pos N j₀
  have hdeg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.deg = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar N
  have hsum := ModularCurve.sum_ord_jBar_sub_eq_dedekindPsi N j₀ hdeg S hS
  rw [← hFINRANK] at hsum

  exact hPEO2 S hS hsum (fun w hw => by
    obtain ⟨φ, hφ⟩ := AlgebraicCurve.Place.exists_algHom_laurentSeries_order_eq_ord w (hdeg w)
    have hf : 0 < (φ (jBar N -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).order := by
      rw [hφ]; exact hw
    obtain ⟨φ', hφ', hφ'f⟩ := LaurentSeries.exists_algHom_comp_map_eq_single φ _ hf
    refine ⟨φ', ?_, fun x => by rw [hφ', hφ]⟩
    rw [hφ'f, hφ, Int.toNat_of_nonneg hw.le])

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord.ModularCurve in

theorem solution (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      Nat.card {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
        ∃ g : ℚ, 0 < g ∧ ∀ x, (w.ord x : ℚ) * g = (ψ x).order} =
      (w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat :=
  ModularCurve.natCard_normalized_algHom_jBar_eq_toNat_ord N j₀

#print axioms solution

end S_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord
end P2MW
export P2MW.S_ModularCurve_natCard_normalized_algHom_jBar_eq_toNat_ord (solution)
