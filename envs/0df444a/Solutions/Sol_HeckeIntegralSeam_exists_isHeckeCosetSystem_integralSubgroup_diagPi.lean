-- Prove2me | solution 1 for HeckeIntegralSeam.exists_isHeckeCosetSystem_integralSubgroup_diagPi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/be1e81d7-e1a4-569e-9b5f-831f8f4aac0f

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Theorems.Thm_LocalGL2_finite_image_integralSubgroup_mul_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi

set_option autoImplicit false

open scoped Pointwise
open LocalGL2 HeckeIntegralSeam

namespace CosetExists

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι κ : Type*}
    {reps : ι → G} (h : IsHeckeCosetSystem U g reps) (e : κ ≃ ι) :
    IsHeckeCosetSystem U g (reps ∘ e) := by
  refine ⟨fun k => h.mem_doubleCoset (e k), fun x hx => ?_, fun k k' hkk' => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  · exact e.injective (h.mk_injective hkk')

end CosetExists

open CosetExists in
theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (hϖ0 : algebraMap R K ϖ ≠ 0) :
    ∃ (n : ℕ) (rT : Fin n → GL (Fin 2) K),
      HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup R K) (LocalGL2.diagPi ϖ hϖ0) rT := by
  classical
  have hfin := LocalGL2.finite_image_integralSubgroup_mul_singleton (R := R) (K := K) hϖ (diagPi ϖ hϖ0)
  have hsys := canonical_isHeckeCosetSystem hfin
  refine ⟨hfin.toFinset.card, _, isHeckeCosetSystem_comp_equiv hsys hfin.toFinset.equivFin.symm⟩

end S_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi
end P2MW
export P2MW.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi (solution)
