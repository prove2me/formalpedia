-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.gMat_mem_minusculeSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:17:38.147269+00:00
-- url     : https://prove2.me/submissions/0fc70032-a486-496e-b2e1-94c7ea5d2eaf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
import Theorems.Thm_GroundTheory_Automorphic_Spherical_cMat_mem
import Theorems.Thm_GroundTheory_Automorphic_Spherical_unipC_mem_unipotent
import Theorems.Thm_GroundTheory_Automorphic_Spherical_gMat_apply
import Theorems.Thm_GroundTheory_Automorphic_Spherical_gMat_inv_apply
import Theorems.Thm_GroundTheory_Automorphic_Spherical_lamS_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Spherical_lamS_le_one
import Theorems.Thm_GroundTheory_Automorphic_Spherical_sum_lamS
import Theorems.Thm_GroundTheory_Automorphic_Spherical_zpow_mem_of_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_coe_torusPow
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Spherical_prod_zpow_uniformizer
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra
open ValuativeRel (valuation)
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
local notation "π" => (GLnLocal.uniformizer F : F)
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    gMat S c ∈ minusculeSet F n S.card := by
  refine ⟨fun i j => ?_, fun i j => ?_, ?_⟩
  · rw [gMat_apply]
    refine Subring.mul_mem _ (Subring.add_mem _ ?_ (cMat_mem c i j))
      (zpow_mem_of_nonneg (lamS_nonneg S j))
    rw [Matrix.one_apply]
    split_ifs
    · exact (𝒪[F]).one_mem
    · exact (𝒪[F]).zero_mem
  · rw [gMat_inv_apply, ← mul_assoc, ← zpow_one_add₀ (Cartan.uniformizer_ne_zero F)]
    by_cases h : i ∈ S ∧ j ∉ S ∧ i < j
    · have hi : lamS S i = 1 := if_pos h.1
      rw [hi, add_neg_cancel, zpow_zero, one_mul]
      exact Subring.sub_mem _ (by rw [Matrix.one_apply_ne (ne_of_lt h.2.2)]; exact (𝒪[F]).zero_mem)
        (cMat_mem c i j)
    · rw [cMat_apply_of_not c h, sub_zero]
      refine Subring.mul_mem _ (zpow_mem_of_nonneg (by linarith [lamS_le_one S i])) ?_
      rw [Matrix.one_apply]
      split_ifs
      · exact (𝒪[F]).one_mem
      · exact (𝒪[F]).zero_mem
  · change valuation F (((unipC S c : GL (Fin n) F) * (torusPow F n (lamS S) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F)).det = _
    rw [det_mul, coe_torusPow, det_diagonal, prod_zpow_uniformizer, sum_lamS,
      det_of_isUpperTriangular (unipC_mem_unipotent S c).1]
    simp only [(unipC_mem_unipotent S c).2, Finset.prod_const_one, one_mul, map_zpow₀, zpow_natCast,
      map_pow]
end GroundTheory.Automorphic.Spherical
