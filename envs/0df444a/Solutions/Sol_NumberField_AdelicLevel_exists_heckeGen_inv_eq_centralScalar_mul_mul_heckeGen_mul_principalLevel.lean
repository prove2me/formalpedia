-- Prove2me | solution 1 for NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_principalLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a604e871-163a-55df-81e7-edf503351aca

import Mathlib
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_principalLevel

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel

namespace HstdPrin

variable {F : Type} [Field F] [NumberField F]

theorem eq_one_of_components (g : AdelicGL2 (𝓞 F) F) (h₁ : glArch (𝓞 F) F g = 1)
    (h₂ : ∀ v : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) : g = 1 := by
  apply Units.ext
  rw [Units.val_one]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [map_one]
    ext i j
    have e := congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing F) => (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
    simp only [glArch_apply, Units.val_one] at e
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact e
  · refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun v => ?_
    rw [map_one, map_one]
    ext i j : 1
    have e := congrArg (fun x : GL (Fin 2) (v.adicCompletion F) => (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) (h₂ v)
    simp only [finComponent_apply, glFin_apply, Units.val_one] at e
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact e

theorem eq_of_components (g₁ g₂ : AdelicGL2 (𝓞 F) F) (h₁ : glArch (𝓞 F) F g₁ = glArch (𝓞 F) F g₂)
    (h₂ : ∀ v : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F v (glFin (𝓞 F) F g₁) = finComponent (𝓞 F) F v (glFin (𝓞 F) F g₂)) :
    g₁ = g₂ := by
  rw [← mul_inv_eq_one]
  refine eq_one_of_components _ ?_ fun v => ?_
  · rw [map_mul, map_inv, h₁, mul_inv_cancel]
  · rw [map_mul, map_inv, map_mul, map_inv, h₂ v, mul_inv_cancel]

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

noncomputable def antidiagInt (v : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (v.adicCompletionIntegers F) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

noncomputable def antidiag (v : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (v.adicCompletion F) :=
  Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (antidiagInt v)

theorem antidiag_mem (v : HeightOneSpectrum (𝓞 F)) :
    antidiag v ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F) := ⟨antidiagInt v, rfl⟩

theorem antidiag_apply (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    ((antidiag v : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j = !![(0 : v.adicCompletion F), 1; 1, 0] i j := by
  show algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F)) i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem finComponent_weyl (v : HeightOneSpectrum (𝓞 F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (weyl (𝓞 F) F)) = antidiag v :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    rw [finComponent_apply, glFin_apply, antidiag_apply]
    fin_cases i <;> fin_cases j <;> rfl

theorem weyl_conj_finEmbed_localEmbed (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (v.adicCompletion F)) :
    weyl (𝓞 F) F * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v ((antidiag v)⁻¹ * k * antidiag v)) *
        (weyl (𝓞 F) F)⁻¹ =
      AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v k) := by
  refine eq_of_components _ _ ?_ fun v' => ?_
  · rw [map_mul, map_mul, map_inv, AdelicDock.glArch_finEmbed, AdelicDock.glArch_finEmbed, mul_one, mul_inv_cancel]
  · rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, AdelicDock.glFin_finEmbed, AdelicDock.glFin_finEmbed,
      finComponent_weyl]
    by_cases hv : v' = v
    · subst hv
      rw [AdelicDock.finComponent_localEmbed_self, AdelicDock.finComponent_localEmbed_self]
      group
    · rw [AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hv, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hv,
        mul_one, mul_inv_cancel]

theorem finEmbed_localEmbed_mem_principalLevel {N : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v k) ∈ principalLevel (𝓞 F) F N := by
  refine ⟨finEmbed_localEmbed_mem_levelOne hv hk, ?_⟩
  refine Subgroup.mem_map.mpr ⟨AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v ((antidiag v)⁻¹ * k * antidiag v)),
    finEmbed_localEmbed_mem_levelOne hv (mul_mem (mul_mem (inv_mem (antidiag_mem v)) hk) (antidiag_mem v)), ?_⟩
  show weyl (𝓞 F) F * _ * (weyl (𝓞 F) F)⁻¹ = _
  exact weyl_conj_finEmbed_localEmbed v k

end HstdPrin

open HstdPrin in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) :
    ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 K) K), u₁ ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ u₂ ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
        (heckeGen (𝓞 K) K w)⁻¹ = centralScalar (𝓞 K) K z * u₁ * heckeGen (𝓞 K) K w * u₂ := by
  refine NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
    K (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) N S hN ?_
  intro v hv k hk
  exact ⟨finEmbed_localEmbed_mem_principalLevel hv hk, finEmbed_mem_finiteAdelicGL2Subgroup _⟩

#print axioms solution

end S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_principalLevel
end P2MW
export P2MW.S_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_principalLevel (solution)
