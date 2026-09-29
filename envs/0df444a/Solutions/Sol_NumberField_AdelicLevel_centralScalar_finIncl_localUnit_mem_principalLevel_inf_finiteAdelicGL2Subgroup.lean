-- Prove2me | solution 1 for NumberField.AdelicLevel.centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5bd4215a-e337-509e-a848-bd7e0108bb50

import Mathlib.NumberTheory.NumberField.AdeleRing
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ N)
    (t : (v.adicCompletion K)ˣ) (ht : Valued.v (t : v.adicCompletion K) = 1) :
    AutomorphicForm.centralScalar (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) ∈
      principalLevel (𝓞 K) K N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K := by
  classical
  have hN : N ≠ ⊥ := by
    rintro rfl
    exact hv (dvd_zero _)

  set z : (AdeleRing (𝓞 K) K)ˣ := Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t) with hz
  set c := AutomorphicForm.centralScalar (𝓞 K) K z with hc
  have hcij : ∀ i j : Fin 2, ((c : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) =
      if i = j then (z : AdeleRing (𝓞 K) K) else 0 := by
    intro i j
    simp [c, AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply]
  have hcinv : ∀ i j : Fin 2, (((c⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) =
      if i = j then ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) else 0 := by
    intro i j
    have : c⁻¹ = AutomorphicForm.centralScalar (𝓞 K) K z⁻¹ := by simp [c]
    rw [this]
    simp [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply]

  have hz2 : (z : AdeleRing (𝓞 K) K).2 = (localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) := rfl
  have hz1 : (z : AdeleRing (𝓞 K) K).1 = 1 := rfl
  have hzi2 : ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 =
      (localUnit (𝓞 K) K v t⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    rw [← map_inv, ← map_inv]; rfl
  have hti : Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
  have hint : ∀ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 →
      ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)
        ∈ integralFiniteAdeles (𝓞 K) K := by
    intro s hs w
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, hs]
    · rw [localUnit_apply_of_ne (𝓞 K) K v s hw]; exact one_mem _
  have hball : ∀ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 →
      ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) - 1
        ∈ idealBall (𝓞 K) K N := by
    intro s hs w
    by_cases hw : w = v
    · subst hw
      rw [coe_sub_apply, localUnit_apply_self, coe_one_apply, idealBound_eq_one_of_not_dvd hN hv]
      refine (Valuation.map_sub _ _ _).trans ?_
      rw [hs, Valuation.map_one, max_self]
    · rw [coe_sub_apply, localUnit_apply_of_ne (𝓞 K) K v s hw, coe_one_apply, sub_self, map_zero]
      exact zero_le'

  have key : ∀ (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) (s : (v.adicCompletion K)ˣ),
      Valued.v (s : v.adicCompletion K) = 1 →
      (∀ i j : Fin 2, m i j = if i = j then
        ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v s) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
        else 0) →
      IsLevelOneMatrix (𝓞 K) K N (fun i j => (m i j).2) := by
    intro m s hs hm
    have e : ∀ i j : Fin 2, (m i j).2 = if i = j then
        ((localUnit (𝓞 K) K v s : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) else 0 := by
      intro i j; rw [hm i j]; split_ifs <;> rfl
    refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
    · rw [e]; split_ifs
      · exact hint s hs
      · exact zero_mem_integralFiniteAdeles
    · show (m 1 0).2 ∈ _
      rw [e, if_neg (by decide)]; exact zero_mem_idealBall N
    · show (m 1 1).2 - 1 ∈ _
      rw [e, if_pos rfl]; exact hball s hs
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  ·
    have hlev : c ∈ levelOne (𝓞 K) K N := by
      rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
      refine ⟨?_, ?_⟩
      · have := key (c : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) t ht hcij
        exact this
      · rw [← map_inv]
        have hm' : ∀ i j : Fin 2, (((c⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2)
            (AdeleRing (𝓞 K) K)) i j) = if i = j then
            ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t⁻¹) : (AdeleRing (𝓞 K) K)ˣ) :
              AdeleRing (𝓞 K) K) else 0 := by
          intro i j; rw [hcinv i j, ← map_inv, ← map_inv]
        exact key _ t⁻¹ hti hm'
    rw [mem_principalLevel_iff]
    refine ⟨hlev, ⟨c, hlev, ?_⟩⟩

    show weyl (𝓞 K) K * c * (weyl (𝓞 K) K)⁻¹ = c
    have hcomm : weyl (𝓞 K) K * c = c * weyl (𝓞 K) K := by
      apply Units.ext
      ext i j
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hcij]
      fin_cases i <;> fin_cases j <;> simp [weyl]
    rw [hcomm, mul_inv_cancel_right]
  ·
    show glArch (𝓞 K) K c = 1
    apply Units.ext
    ext i j
    rw [glArch_apply, hcij]
    split_ifs with h
    · subst h; rw [hz1]; simp
    · rw [Units.val_one, Matrix.one_apply_ne h]; rfl

end S_NumberField_AdelicLevel_centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup
end P2MW
export P2MW.S_NumberField_AdelicLevel_centralScalar_finIncl_localUnit_mem_principalLevel_inf_finiteAdelicGL2Subgroup (solution)
