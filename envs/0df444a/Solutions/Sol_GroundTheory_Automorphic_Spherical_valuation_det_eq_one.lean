-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.valuation_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:23.489397+00:00
-- url     : https://prove2.me/submissions/0de6276f-0743-4462-a174-21dedbc999a3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Theorems.Thm_GroundTheory_Automorphic_Spherical_det_mem_of_forall_mem
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
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
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    valuation F (k : Matrix (Fin n) (Fin n) F).det = 1 := by
  have h1 := det_mem_of_forall_mem ((mem_integralGL_iff F n).1 hk).1
  have h2 := det_mem_of_forall_mem ((mem_integralGL_iff F n).1 hk).2
  have hu : IsUnit (⟨_, h1⟩ : 𝒪[F]) := IsUnit.of_mul_eq_one (⟨_, h2⟩ : 𝒪[F]) (Subtype.ext (by
    simp only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]
    rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]))
  exact (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.1 hu
end GroundTheory.Automorphic.Spherical
