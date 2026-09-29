-- Prove2me | solution 1 for ModularCurve.exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7d78f797-a7e8-5320-88ad-97d0827ad8fe

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_ModularCurve_exists_coeffEmb_basis_of_forall_coeffMap_mem
import Theorems.Thm_ModularCurve_IsModPFormFn_of_coeffMap_algebraMap
import Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem
set_option autoImplicit false

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (m : ℕ)
    (V : Submodule L (LaurentSeries L)) [FiniteDimensional L V]
    (hV : ∀ (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries L), x ∈ V → ModularCurve.coeffMap (σ : L →+* L) x ∈ V)
    (hVF : ∀ x ∈ V, x ∈ ModularCurve.laurentBaseChange L F₀)
    (hVB : ∀ x ∈ V, ModularCurve.IsModPFormFn L m x) :
    ∃ (n : ℕ) (Y : Fin n → LaurentSeries ℚ),
      (∀ i, Y i ∈ F₀) ∧ (∀ i, ModularCurve.IsModPFormFn ℚ m (Y i)) ∧ LinearIndependent ℚ Y ∧
      LinearIndependent L (fun i => ModularCurve.coeffEmb L (Y i)) ∧
      Submodule.span L (Set.range fun i => ModularCurve.coeffEmb L (Y i)) = V := by
  classical
  obtain ⟨n, Y, hli, hspan⟩ := ModularCurve.exists_coeffEmb_basis_of_forall_coeffMap_mem L V hV
  have hmemV : ∀ i, ModularCurve.coeffEmb L (Y i) ∈ V := fun i => by
    have h : ModularCurve.coeffEmb L (Y i) ∈ Submodule.span L (Set.range fun i => ModularCurve.coeffEmb L (Y i)) :=
      Submodule.subset_span ⟨i, rfl⟩
    rwa [hspan] at h
  refine ⟨n, Y, fun i => ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange L F₀ (Y i) (hVF _ (hmemV i)),
    fun i => ModularCurve.IsModPFormFn.of_coeffMap_algebraMap (K₀ := ℚ) (K := L) m (Y i) (hVB _ (hmemV i)), ?_, hli, hspan⟩

  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg i
  have h := congrArg (ModularCurve.coeffEmb L) hg
  rw [map_sum, map_zero] at h
  have h' : ∑ j, (algebraMap ℚ L (g j)) • ModularCurve.coeffEmb L (Y j) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext k
    simp only [ModularCurve.coeffEmb_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul]
  have h0 := hli _ h' i
  exact (map_eq_zero_iff _ (algebraMap ℚ L).injective).mp h0

end S_ModularCurve_exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem
end P2MW
export P2MW.S_ModularCurve_exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem (solution)
