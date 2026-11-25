-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.mem_integralGL_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:38.336344+00:00
-- url     : https://prove2.me/submissions/da4b5a90-14f7-49c2-b987-7402377d53ab

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
import Theorems.Thm_GroundTheory_Automorphic_Spherical_det_mem_of_forall_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {g : GL (Fin n) F} (h₁ : ∀ i j, g i j ∈ 𝒪[F])
    (h₂ : valuation F (g : Matrix (Fin n) (Fin n) F).det = 1) : g ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  refine ⟨h₁, fun i j => ?_⟩
  have hinv : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F)⁻¹ := Matrix.coe_units_inv g
  change ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]
  rw [hinv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine Subring.mul_mem _ ?_ ?_
  · change valuation F _ ≤ 1
    rw [map_inv₀, h₂, inv_one]
  · rw [adjugate_apply]
    refine det_mem_of_forall_mem fun a b => ?_
    rw [updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact (𝒪[F]).one_mem
      · exact (𝒪[F]).zero_mem
    · exact h₁ _ _
end GroundTheory.Automorphic.Spherical
