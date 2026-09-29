-- Prove2me | solution 1 for NumberField.AdelicLevel.conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d8e72099-5d61-5fa6-9d2b-15f07ae147f1

import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

namespace LevelNormal

variable {K : Type} [Field K] [NumberField K]

local notation "𝔸f" => FiniteAdeleRing (𝓞 K) K
local notation "Gf" => GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)

structure IsPrincipalMatrix (N : Ideal (𝓞 K)) (m : Matrix (Fin 2) (Fin 2) 𝔸f) : Prop where
  integral : ∀ i j, m i j ∈ integralFiniteAdeles (𝓞 K) K
  cong : ∀ i j, m i j - (1 : Matrix (Fin 2) (Fin 2) 𝔸f) i j ∈ idealBall (𝓞 K) K N

variable {N : Ideal (𝓞 K)}

theorem IsPrincipalMatrix.toIsLevelOneMatrix {m : Matrix (Fin 2) (Fin 2) 𝔸f} (h : IsPrincipalMatrix N m) :
    IsLevelOneMatrix (𝓞 K) K N m := by
  refine ⟨⟨h.integral, ?_⟩, ?_⟩
  · have := h.cong 1 0
    rwa [Matrix.one_apply_ne (by decide), sub_zero] at this
  · have := h.cong 1 1
    rwa [Matrix.one_apply_eq] at this

theorem weyl_inv : (weyl (𝓞 K) K)⁻¹ = weyl (𝓞 K) K := Units.ext rfl

theorem weyl_conj_apply (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) (Fin.rev i) (Fin.rev j) := by
  rw [weyl_inv]
  simp only [Units.val_mul, weyl, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

theorem glFin_apply' (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) 𝔸f) i j = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 :=
  rfl

theorem glFin_weyl_conj_apply (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K) : Matrix (Fin 2) (Fin 2) 𝔸f) i j =
      (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) 𝔸f) (Fin.rev i) (Fin.rev j) := by
  rw [glFin_apply', glFin_apply', weyl_conj_apply]

theorem IsPrincipalMatrix.flip {g : AdelicGL2 (𝓞 K) K}
    (h : IsPrincipalMatrix N (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) 𝔸f)) :
    IsPrincipalMatrix N (glFin (𝓞 K) K ((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K) : Matrix (Fin 2) (Fin 2) 𝔸f) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_weyl_conj_apply]; exact h.integral _ _
  · rw [glFin_weyl_conj_apply]
    have h1 : (1 : Matrix (Fin 2) (Fin 2) 𝔸f) i j = (1 : Matrix (Fin 2) (Fin 2) 𝔸f) (Fin.rev i) (Fin.rev j) := by
      fin_cases i <;> fin_cases j <;> rfl
    rw [h1]; exact h.cong _ _

theorem lower_of_mem_levelOne {g : AdelicGL2 (𝓞 K) K} (h : g ∈ levelOne (𝓞 K) K N) :
    (∀ i j, (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) 𝔸f) i j ∈ integralFiniteAdeles (𝓞 K) K) ∧
    (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 ∈ idealBall (𝓞 K) K N ∧
    (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 - 1 ∈ idealBall (𝓞 K) K N := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h
  exact ⟨h.1.integral, h.1.lowerLeft, h.1.lowerRight⟩

theorem isPrincipalMatrix_of_mem {g : AdelicGL2 (𝓞 K) K} (h : g ∈ principalLevel (𝓞 K) K N) :
    IsPrincipalMatrix N (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) 𝔸f) := by
  rw [mem_principalLevel_iff] at h
  obtain ⟨h1, ⟨g', hg', hconj⟩⟩ := h
  have hg'eq : g' = (weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K := by
    have : weyl (𝓞 K) K * g' * (weyl (𝓞 K) K)⁻¹ = g := hconj
    rw [← this]; group
  obtain ⟨hint, h10, h11⟩ := lower_of_mem_levelOne h1
  obtain ⟨-, h10', h11'⟩ := lower_of_mem_levelOne hg'
  rw [hg'eq, glFin_weyl_conj_apply] at h10' h11'
  refine ⟨hint, fun i j => ?_⟩
  fin_cases i <;> fin_cases j
  · simpa [Matrix.one_apply_eq] using h11'
  · simpa using h10'
  · simpa using h10
  · simpa [Matrix.one_apply_eq] using h11

theorem mem_of_isPrincipalMatrix {g : AdelicGL2 (𝓞 K) K}
    (h : IsPrincipalMatrix N (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) 𝔸f))
    (h' : IsPrincipalMatrix N (glFin (𝓞 K) K g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸f)) :
    g ∈ principalLevel (𝓞 K) K N := by
  have hlev : ∀ x : AdelicGL2 (𝓞 K) K,
      IsPrincipalMatrix N (glFin (𝓞 K) K x : Matrix (Fin 2) (Fin 2) 𝔸f) →
      IsPrincipalMatrix N (glFin (𝓞 K) K x⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸f) → x ∈ levelOne (𝓞 K) K N := by
    intro x hx hx'
    rw [mem_levelOne_iff, mem_finiteLevelOne_iff, ← map_inv]
    exact ⟨hx.toIsLevelOneMatrix, hx'.toIsLevelOneMatrix⟩
  rw [mem_principalLevel_iff]
  refine ⟨hlev g h h', ⟨(weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K, hlev _ h.flip ?_, ?_⟩⟩
  · have : ((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K)⁻¹ = (weyl (𝓞 K) K)⁻¹ * g⁻¹ * weyl (𝓞 K) K := by
      group
    rw [this]; exact h'.flip
  · show weyl (𝓞 K) K * ((weyl (𝓞 K) K)⁻¹ * g * weyl (𝓞 K) K) * (weyl (𝓞 K) K)⁻¹ = g
    group

theorem IsPrincipalMatrix.conj {m A B : Matrix (Fin 2) (Fin 2) 𝔸f} (h : IsPrincipalMatrix N m)
    (hA : ∀ i j, A i j ∈ integralFiniteAdeles (𝓞 K) K) (hB : ∀ i j, B i j ∈ integralFiniteAdeles (𝓞 K) K)
    (hAB : A * B = 1) : IsPrincipalMatrix N (A * m * B) := by
  have hint : ∀ (X Y : Matrix (Fin 2) (Fin 2) 𝔸f), (∀ i j, X i j ∈ integralFiniteAdeles (𝓞 K) K) →
      (∀ i j, Y i j ∈ integralFiniteAdeles (𝓞 K) K) → ∀ i j, (X * Y) i j ∈ integralFiniteAdeles (𝓞 K) K := by
    intro X Y hX hY i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hX i 0) (hY 0 j))
      (mul_mem_integralFiniteAdeles (hX i 1) (hY 1 j))
  have hballL : ∀ (X Y : Matrix (Fin 2) (Fin 2) 𝔸f), (∀ i j, X i j ∈ integralFiniteAdeles (𝓞 K) K) →
      (∀ i j, Y i j ∈ idealBall (𝓞 K) K N) → ∀ i j, (X * Y) i j ∈ idealBall (𝓞 K) K N := by
    intro X Y hX hY i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_idealBall (mul_mem_idealBall_left (hX i 0) (hY 0 j)) (mul_mem_idealBall_left (hX i 1) (hY 1 j))
  have hballR : ∀ (X Y : Matrix (Fin 2) (Fin 2) 𝔸f), (∀ i j, X i j ∈ idealBall (𝓞 K) K N) →
      (∀ i j, Y i j ∈ integralFiniteAdeles (𝓞 K) K) → ∀ i j, (X * Y) i j ∈ idealBall (𝓞 K) K N := by
    intro X Y hX hY i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_idealBall (mul_mem_idealBall_right (hX i 0) (hY 0 j)) (mul_mem_idealBall_right (hX i 1) (hY 1 j))
  refine ⟨hint _ _ (hint _ _ hA h.integral) hB, fun i j => ?_⟩
  have key : A * m * B - 1 = A * (m - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  have : (A * m * B) i j - (1 : Matrix (Fin 2) (Fin 2) 𝔸f) i j = (A * (m - 1) * B) i j := by
    rw [← key]; rfl
  rw [this]
  exact hballR _ _ (hballL _ _ hA (fun i j => h.cong i j)) hB i j

end LevelNormal

open LevelNormal in
theorem solution
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K))
    (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ AutomorphicForm.adelicMaximalCompact K)
    (u : AdelicGL2 (𝓞 K) K)
    (hu : u ∈ principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) :
    k * u * k⁻¹ ∈ principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K := by
  obtain ⟨huP, huF⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨hkint, -⟩ := AutomorphicForm.mem_adelicMaximalCompact_iff.mp hk
  obtain ⟨hA, hA'⟩ := mem_finiteIntegralGL2_iff.mp hkint

  have hkk : (glFin (𝓞 K) K k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) *
      (glFin (𝓞 K) K k⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hA'' : ∀ i j, (glFin (𝓞 K) K k⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈
      integralFiniteAdeles (𝓞 K) K := by
    intro i j; rw [map_inv]; exact hA' i j
  have hP := isPrincipalMatrix_of_mem huP
  have hP' := isPrincipalMatrix_of_mem ((principalLevel (𝓞 K) K N).inv_mem huP)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · refine mem_of_isPrincipalMatrix ?_ ?_
    · rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
      exact hP.conj hA hA'' hkk
    · have : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
      rw [this, map_mul, map_mul, Units.val_mul, Units.val_mul]
      exact hP'.conj hA hA'' hkk
  · rw [AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff] at huF ⊢
    rw [map_mul, map_mul, huF, mul_one, map_inv, mul_inv_cancel]

end S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact
end P2MW
export P2MW.S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact (solution)
