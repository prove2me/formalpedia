-- Prove2me | solution 1 for NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/84280b43-9f71-5983-a27d-a30d0148b369

import Mathlib
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel

namespace HstdL1

variable {F : Type} [Field F] [NumberField F]

theorem finEmbed_localEmbed_mem_levelOne {N : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v k) ∈ levelOne (𝓞 F) F N := by
  have hN0 : N ≠ ⊥ := fun h => hv (h ▸ dvd_zero _)
  have hb : idealBound (𝓞 F) N v = 1 := idealBound_eq_one_of_not_dvd hN0 hv
  obtain ⟨y, rfl⟩ := hk
  have hint : ∀ (y : GL (Fin 2) (v.adicCompletionIntegers F)) (i j : Fin 2),
      ((Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) y :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    intro y i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ((y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F)) i j).2
  have hloc : ∀ (y : GL (Fin 2) (v.adicCompletionIntegers F)), AdelicDock.IsLocalLevelOne (𝓞 F) F v N
      ((Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) y :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
    intro y
    refine ⟨hint y, ?_, ?_⟩
    · rw [hb]; exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (hint y 1 0)
    · rw [hb]; exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (sub_mem (hint y 1 1) (one_mem _))
  rw [AdelicDock.finEmbed_mem_levelOne_iff, AdelicDock.localEmbed_mem_finiteLevelOne_iff, AdelicDock.mem_localLevelOne_iff,
    ← map_inv]
  exact ⟨hloc y, hloc y⁻¹⟩

theorem finEmbed_mem_finiteAdelicGL2Subgroup (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    AdelicDock.finEmbed (𝓞 F) F g ∈ finiteAdelicGL2Subgroup F :=
  (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed _ _ _)

end HstdL1

open HstdL1 in
theorem solution
    (L : Type) [Field L] [NumberField L]
    (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ N → v ∈ S) :
    ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L), u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧ u₂ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        (heckeGen (𝓞 L) L w)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L w * u₂ := by
  refine NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
    L (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) N S hN ?_
  intro v hv k hk
  exact ⟨finEmbed_localEmbed_mem_levelOne hv hk, finEmbed_mem_finiteAdelicGL2Subgroup _⟩

#print axioms solution

end S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne
end P2MW
export P2MW.S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne (solution)
