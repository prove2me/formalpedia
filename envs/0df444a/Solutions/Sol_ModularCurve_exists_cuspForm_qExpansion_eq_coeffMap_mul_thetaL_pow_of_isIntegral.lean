-- Prove2me | solution 1 for ModularCurve.exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/aaea5d3d-15d7-53ac-a57f-7b8bdc8050c5

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

open ModularCurve HahnSeries

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace LMapGlue

variable (N : ℕ) [NeZero N]

theorem ringHom_rat_eq (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    ι₀.comp (algebraMap ℚ (AlgebraicClosure ℚ)) = algebraMap ℚ ℂ :=
  Subsingleton.elim _ _

theorem coeffMap_coeffEmb' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (z : LaurentSeries ℚ) :
    coeffMap ι₀ (coeffEmb (AlgebraicClosure ℚ) z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap, ringHom_rat_eq]

theorem coeffMap_algebraMap' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    coeffMap ι₀ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) =
      algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_laurentBaseChange_complex (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
    coeffMap ι₀ x ∈ laurentBaseChange ℂ (modularFunctionFieldFull N) := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange ℂ (modularFunctionFieldFull N)).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange ℂ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

noncomputable def phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) : modularFunctionFieldBar N →+* LaurentSeries ℂ :=
  (coeffMap ι₀).comp (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toSubfield.subtype

theorem phi_apply (ι₀ : AlgebraicClosure ℚ →+* ℂ) (x : modularFunctionFieldBar N) :
    phi N ι₀ x = coeffMap ι₀ (x : LaurentSeries (AlgebraicClosure ℚ)) := rfl

theorem phi_algebraMap (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    phi N ι₀ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) =
      algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [phi_apply]
  exact coeffMap_algebraMap' ι₀ c

theorem phi_jBar (ι₀ : AlgebraicClosure ℚ →+* ℂ) : phi N ι₀ (jBar N) = coeffEmb ℂ jq := by
  rw [phi_apply]
  exact coeffMap_coeffEmb' ι₀ jq

theorem isIntegral_phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) (a : modularFunctionFieldBar N)
    {y : modularFunctionFieldBar N}
    (hy : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (modularFunctionFieldBar N))) y) :
    IsIntegral (Algebra.adjoin ℂ ({phi N ι₀ a} : Set (LaurentSeries ℂ))) (phi N ι₀ y) := by
  have hmem : ∀ r : modularFunctionFieldBar N,
      r ∈ Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (modularFunctionFieldBar N)) →
      phi N ι₀ r ∈ Algebra.adjoin ℂ ({phi N ι₀ a} : Set (LaurentSeries ℂ)) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
        rw [Set.mem_singleton_iff] at hr
        subst hr
        exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap c =>
        rw [phi_algebraMap]
        exact Subalgebra.algebraMap_mem _ _
    | add r s _ _ hr hs => rw [map_add]; exact add_mem hr hs
    | mul r s _ _ hr hs => rw [map_mul]; exact mul_mem hr hs
  let ψ : Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (modularFunctionFieldBar N)) →+*
      Algebra.adjoin ℂ ({phi N ι₀ a} : Set (LaurentSeries ℂ)) :=
    ((phi N ι₀).comp (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (modularFunctionFieldBar N))).val.toRingHom).codRestrict
      (Algebra.adjoin ℂ ({phi N ι₀ a} : Set (LaurentSeries ℂ))) (fun r => hmem r r.2)
  refine IsIntegral.map_of_comp_eq ψ (phi N ι₀) ?_ hy
  ext r
  rfl

end LMapGlue

end

open LMapGlue in
theorem solution (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m)
    (ι₀ : AlgebraicClosure ℚ →+* ℂ) (x : ↥(ModularCurve.modularFunctionFieldBar N))
    (h₁ : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({ModularCurve.jBar N} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
      (x ^ 6 * ModularCurve.jBar N ^ (4 * m) *
        (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (3 * m)))
    (h₂ : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.jBar N)⁻¹} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
      (x ^ (2 * ModularCurve.dedekindPsi N) * ModularCurve.jBar N ^ (m * ModularCurve.dedekindPsi N + 1) *
        (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (m * ModularCurve.dedekindPsi N))) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) =
        ModularCurve.coeffMap ι₀ ((x : ↥(ModularCurve.modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) *
          ModularCurve.thetaL ℂ (ModularCurve.coeffEmb ℂ ModularCurve.jq) ^ m := by
  classical
  have hXmem : phi N ι₀ x ∈ laurentBaseChange ℂ (modularFunctionFieldFull N) :=
    coeffMap_mem_laurentBaseChange_complex N ι₀ x.2
  have hJ : phi N ι₀ (jBar N) = coeffEmb ℂ jq := phi_jBar N ι₀
  have h1728 : phi N ι₀ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728) =
      algebraMap ℂ (LaurentSeries ℂ) 1728 := by
    rw [phi_algebraMap, map_ofNat]
  have h₁' := isIntegral_phi N ι₀ (jBar N) h₁
  have h₂' := isIntegral_phi N ι₀ ((jBar N)⁻¹) h₂
  rw [map_inv₀, hJ] at h₂'
  rw [hJ] at h₁'
  simp only [map_mul, map_pow, map_sub, hJ, h1728] at h₁' h₂'
  obtain ⟨f, hf⟩ := ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral N m hm (phi N ι₀ x) hXmem
    (dedekindPsi N) h₁' h₂'
  exact ⟨f, by rw [hf, phi_apply]⟩

end S_ModularCurve_exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral
end P2MW
export P2MW.S_ModularCurve_exists_cuspForm_qExpansion_eq_coeffMap_mul_thetaL_pow_of_isIntegral (solution)
