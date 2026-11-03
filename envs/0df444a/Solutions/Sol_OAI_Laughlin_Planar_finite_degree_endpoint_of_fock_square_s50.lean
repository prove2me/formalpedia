-- Prove2me | solution 1 for OAI.Laughlin.Planar.finite_degree_endpoint_of_fock_square_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:03:04.16768+00:00
-- url     : https://prove2.me/submissions/f917c394-3a19-4844-8135-ae0c9ecbf936

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_fockInclusion_normSq_s50
import Theorems.Thm_OAI_Laughlin_Fock_pairCreate_pair_adjoint_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceFockEnergy_fockInclusion_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceFockHamiltonian_fockInclusion_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FactorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter

theorem modeFactor_sq_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range x, (1/1 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) 0 1 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x) := by
    filter_upwards [eventually_ge_atTop x] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : (Q : ℝ)^x = ∏ _i ∈ Finset.range x, (Q : ℝ) := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ Q)]
      congr 1 <;> ring
  simpa using hp.congr' he

theorem pairFactor_inv_sq_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2).descFactorial p : ℝ)/((2 : ℝ)*Q)^p)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range p,
      ((-(2+(i : ℝ))+2*(Q : ℝ))/(0+2*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range p, (2/2 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(2+(i : ℝ))) 0 2 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range p,
      ((-(2+(i : ℝ))+2*(Q : ℝ))/(0+2*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => ((2*Q-2).descFactorial p : ℝ)/((2 : ℝ)*Q)^p) := by
    filter_upwards [eventually_ge_atTop (p+2)] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : ((2 : ℝ)*Q)^p = ∏ _i ∈ Finset.range p, (2 : ℝ)*Q := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q)]
      push_cast
      congr 1 <;> ring
  simpa using hp.congr' he

theorem modeFactor_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => modeFactor Q x) atTop (𝓝 1) := by
  simpa [modeFactor] using (modeFactor_sq_tendsto x).sqrt

theorem pairFactor_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => pairFactor Q p) atTop (𝓝 1) := by
  have h := ((pairFactor_inv_sq_tendsto p).inv₀ (by norm_num)).sqrt
  simpa [pairFactor, inv_div] using h

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Planar
open Fock Filter
open scoped BigOperators Topology Matrix

theorem sphereCoefficient_tendsto (p i j : ℕ) :
    Tendsto (fun Q => sphereCoefficient Q p i j) atTop (𝓝 (planarCoefficient p i j)) := by
  have h := ((((modeFactor_tendsto i).mul (modeFactor_tendsto j)).mul
    (pairFactor_tendsto p)).mul_const (pairLimitCoefficient p i j)).div_const (Real.sqrt 2)
  simpa only [one_mul,sphereCoefficient,planarCoefficient,Nat.cast_ofNat,Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

theorem spherePairMatrix_tendsto (L p : ℕ) (A B : Occupations L) :
    Tendsto (fun Q => spherePairMatrix L Q p A B) atTop
      (𝓝 (planarPairMatrix L p A B)) := by
  unfold spherePairMatrix planarPairMatrix pairMatrix
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (sphereCoefficient_tendsto p i.val j.val).mul_const _

theorem sphereHamiltonian_tendsto (L : ℕ) (A B : Occupations L) :
    Tendsto (fun Q => sphereHamiltonian L Q A B) atTop (𝓝 (planarHamiltonian L A B)) := by
  simp only [sphereHamiltonian,planarHamiltonian,Matrix.sum_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply tendsto_finsetSum
  intro p hp
  apply tendsto_finsetSum
  intro C hC
  exact ((spherePairMatrix_tendsto L p C A).star).mul (spherePairMatrix_tendsto L p C B)

theorem sphere_pairEnergy_tendsto (L : ℕ) (x : Occupations L → ℂ) :
    Tendsto (fun Q => pairEnergy L (spherePairMatrix L Q) x) atTop
      (𝓝 (pairEnergy L (planarPairMatrix L) x)) := by
  unfold pairEnergy
  apply tendsto_finsetSum
  intro p hp
  apply tendsto_finsetSum
  intro A hA
  apply Filter.Tendsto.pow
  apply Filter.Tendsto.norm
  simp only [Matrix.mulVec,dotProduct]
  apply tendsto_finsetSum
  intro B hB
  exact (spherePairMatrix_tendsto L p A B).mul_const (x B)

theorem sphere_squareNorm_tendsto (L : ℕ) (x : Occupations L → ℂ) :
    Tendsto (fun Q => squareNorm L (sphereHamiltonian L Q) x) atTop
      (𝓝 (squareNorm L (planarHamiltonian L) x)) := by
  unfold squareNorm
  apply tendsto_finsetSum
  intro A hA
  apply Filter.Tendsto.pow
  apply Filter.Tendsto.norm
  simp only [Matrix.mulVec,dotProduct]
  apply tendsto_finsetSum
  intro B hB
  exact (sphereHamiltonian_tendsto L A B).mul_const (x B)

theorem endpoint_of_sphere_blocks (L : ℕ) (γstar : ℝ) (hγstar : 0 < γstar)
    (x : Occupations L → ℂ)
    (hSphere : ∀ γ : ℝ, 0 < γ → γ < γstar → ∀ᶠ Q : ℕ in atTop,
      γ * pairEnergy L (spherePairMatrix L Q) x ≤ squareNorm L (sphereHamiltonian L Q) x) :
    γstar * pairEnergy L (planarPairMatrix L) x ≤ squareNorm L (planarHamiltonian L) x := by
  have hGap (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < γstar) :
      γ * pairEnergy L (planarPairMatrix L) x ≤ squareNorm L (planarHamiltonian L) x :=
    le_of_tendsto_of_tendsto ((sphere_pairEnergy_tendsto L x).const_mul γ)
      (sphere_squareNorm_tendsto L x) (hSphere γ hγ hγ')
  by_contra hn
  have hlt : squareNorm L (planarHamiltonian L) x <
      γstar * pairEnergy L (planarPairMatrix L) x := lt_of_not_ge hn
  have hE : 0 < pairEnergy L (planarPairMatrix L) x := by
    have hS : 0 ≤ squareNorm L (planarHamiltonian L) x :=
      Finset.sum_nonneg (fun A hA => sq_nonneg _)
    nlinarith
  obtain ⟨γ,hγ,hγ'⟩ := exists_between (div_lt_iff₀ hE |>.mpr hlt)
  have hS : 0 ≤ squareNorm L (planarHamiltonian L) x :=
    Finset.sum_nonneg (fun A hA => sq_nonneg _)
  have hγpos : 0 < γ := lt_of_le_of_lt (div_nonneg hS hE.le) hγ
  have hc := hGap γ hγpos hγ'
  have hd := (div_lt_iff₀ hE).mp hγ
  linarith

end Laughlin.Planar

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Planar
open Fock Filter
open scoped BigOperators Topology Matrix

theorem pairMatrix_toMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    pairMatrix L c = LinearMap.toMatrix (occupationBasis L) (occupationBasis L) (pairEnd L c) := by
  ext A B
  simp only [pairMatrix,LinearMap.toMatrix_apply,pairEnd,LinearMap.sum_apply,
    LinearMap.smul_apply,Module.End.mul_apply,map_sum,Finsupp.finsetSum_apply,
    map_smul,Finsupp.smul_apply,smul_eq_mul]

theorem occupationInner_basis_left (L : ℕ) (A : Occupations L) (x : Space L) :
    occupationInner L (occupationBasis L A) x = (occupationBasis L).repr x A := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem occupationInner_basis_right (L : ℕ) (A : Occupations L) (x : Space L) :
    occupationInner L x (occupationBasis L A) = star ((occupationBasis L).repr x A) := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem pairCreateMatrix_toMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    (pairMatrix L c)ᴴ =
      LinearMap.toMatrix (occupationBasis L) (occupationBasis L) (pairCreateEnd L c) := by
  rw [pairMatrix_toMatrix]
  ext A B
  simp only [Matrix.conjTranspose_apply,LinearMap.toMatrix_apply]
  have h := pairCreate_pair_adjoint_s50 L c (occupationBasis L B) (occupationBasis L A)
  rw [occupationInner_basis_left,occupationInner_basis_right] at h
  simpa only [star_star] using (congrArg star h).symm

theorem sphereHamiltonian_toMatrix (L Q : ℕ) :
    sphereHamiltonian L Q = LinearMap.toMatrix (occupationBasis L) (occupationBasis L)
      (restrictedSphereHamiltonian L Q) := by
  unfold sphereHamiltonian restrictedSphereHamiltonian
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [LinearMap.toMatrix_mul]
  change (pairMatrix L _)ᴴ * pairMatrix L _ = _
  rw [pairCreateMatrix_toMatrix,pairMatrix_toMatrix]
  rfl

theorem sphere_pairEnergy_eq (L Q : ℕ) (x : Space L) :
    pairEnergy L (spherePairMatrix L Q) (fun A => (occupationBasis L).repr x A) =
      restrictedSphereEnergy L Q x := by
  unfold pairEnergy restrictedSphereEnergy
  apply Finset.sum_congr rfl
  intro p hp
  change (∑ A, ‖(pairMatrix L _ *ᵥ fun B => (occupationBasis L).repr x B) A‖^2) = _
  rw [pairMatrix_toMatrix,LinearMap.toMatrix_mulVec_repr]
  rfl

theorem sphere_squareNorm_eq (L Q : ℕ) (x : Space L) :
    squareNorm L (sphereHamiltonian L Q) (fun A => (occupationBasis L).repr x A) =
      occupationNormSq L (restrictedSphereHamiltonian L Q x) := by
  rw [squareNorm,sphereHamiltonian_toMatrix,LinearMap.toMatrix_mulVec_repr]
  rfl

theorem finite_degree_endpoint_of_fock_square_s50_oai (γstar : ℝ) (hγstar : 0 < γstar)
    (hSphere : ∀ γ : ℝ, 0 < γ → γ < γstar → ∀ᶠ Q : ℕ in atTop,
      ∀ x : Space Q, γ * sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x))
    (L : ℕ) (x : Space L) (hx : DegreeAtMost L L x) :
    γstar * pairEnergy L (planarPairMatrix L) (fun A => (occupationBasis L).repr x A) ≤
      squareNorm L (planarHamiltonian L) (fun A => (occupationBasis L).repr x A) := by
  apply endpoint_of_sphere_blocks L γstar hγstar
  intro γ hγ hγstar'
  filter_upwards [hSphere γ hγ hγstar',eventually_ge_atTop (L+2)] with Q hs hQ
  have h := hs (fockInclusion L Q (by omega) x)
  rw [sourceFockEnergy_fockInclusion_s50 L Q hQ x hx,
    sourceFockHamiltonian_fockInclusion_s50 L Q hQ x hx,fockInclusion_normSq_s50] at h
  simpa only [sphere_pairEnergy_eq,sphere_squareNorm_eq] using h

end Laughlin.Planar

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Planar.finite_degree_endpoint_of_fock_square_s50_oai := @OAI.Laughlin.Planar.finite_degree_endpoint_of_fock_square_s50_oai
