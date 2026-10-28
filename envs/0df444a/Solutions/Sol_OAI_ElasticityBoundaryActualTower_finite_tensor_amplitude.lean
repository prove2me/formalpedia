-- Prove2me | solution 1 for OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:07:21.01028+00:00
-- url     : https://prove2.me/submissions/3729a363-1af1-4e11-9ca2-8008caba96a3

import Mathlib
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityBoundaryMVTower_triangular_amplitudes

section
-- module Solutions.OAIQ6_Elast.Compat
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundarySymbols
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Coefficientwise linear differential operators in a genuine finite
parameter polynomial. Used to construct, not postulate, Taylor transport
coefficients of the physical boundary layer. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryParameter
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

lemma coeffMap_X_mul (T : A →ₗ[ℂ] B) (q : Polynomial A) :
    coeffMap T (Polynomial.X*q)=Polynomial.X*coeffMap T q := by
  apply Polynomial.ext
  intro n
  cases n <;> simp [coeffMap_coeff, Polynomial.coeff_X_mul]

lemma coeffMap_monomial_one_mul (T : A →ₗ[ℂ] B) (n : ℕ) (q : Polynomial A) :
    coeffMap T (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*coeffMap T q := by
  rw [Polynomial.monomial_one_right_eq_X_pow, Polynomial.monomial_one_right_eq_X_pow]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc, coeffMap_X_mul, ih, ← mul_assoc, ← pow_succ']

lemma eval_coeffMap (T : A →ₗ[ℂ] B) (q : Polynomial A) (c : ℂ) :
    (coeffMap T q).eval (algebraMap ℂ B c)=T (q.eval (algebraMap ℂ A c)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial n a =>
      rw [coeffMap_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial]
      simp only [← map_pow]
      rw [mul_comm, ← Algebra.smul_def, mul_comm a, ← Algebra.smul_def, T.map_smul]

lemma D_expansion (δ : ℝ) (j : Fin 3) : D δ j = E₀ j+(δ:ℂ) • E₁ j := by
  fin_cases j <;> simp [D,E₀,E₁]

lemma PD_apply (j : Fin 3) (q : Polynomial MP) :
    PD j q=coeffMap (E₀ j) q+Polynomial.X*coeffMap (E₁ j) q := rfl

lemma eval_PD (j : Fin 3) (q : Polynomial MP) (δ : ℝ) :
    (PD j q).eval (C (δ:ℂ)) = D δ j (q.eval (C (δ:ℂ))) := by
  rw [PD_apply, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  have hC : C (δ:ℂ) = algebraMap ℂ MP (δ:ℂ) := rfl
  rw [hC, eval_coeffMap, eval_coeffMap, D_expansion]
  change _ = E₀ j (q.eval (algebraMap ℂ MP (δ:ℂ))) +
    (δ:ℂ) • E₁ j (q.eval (algebraMap ℂ MP (δ:ℂ)))
  rw [Algebra.smul_def]

lemma PD_monomial_one_mul (j : Fin 3) (n : ℕ) (q : Polynomial MP) :
    PD j (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*PD j q := by
  rw [PD_apply, coeffMap_monomial_one_mul, coeffMap_monomial_one_mul, PD_apply]
  ring

end ElasticityBoundaryParameter

end
end
section
/-! The normal inverse on literal multivariable polynomial amplitudes.  No
identification of formal symbols with physical derivatives is assumed: the
normal operator here consists of the actual formal partial derivatives, whose
evaluations agree with the corresponding Fréchet derivatives. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryMVNormal
open MvPolynomial ElasticityBoundarySymbol ElasticityBoundaryMVCalculus
lemma lap_apply (p : MP) : lap p=pderiv 2 (pderiv 2 p)-(2:ℂ) • pderiv 2 p := by
  simp [lap, d]

lemma normal_apply (l m : ℂ) (p : W) : normal l m p =
    ![m • lap (p 0) - (l+m) • p 0 + (Complex.I*(l+m)) • shift (p 2),
      m • lap (p 1), (Complex.I*(l+m)) • shift (p 0) +
        (l+2*m) • lap (p 2) + (l+m) • p 2] := by funext i; fin_cases i <;> rfl

end ElasticityBoundaryMVNormal

end
end
section
/-! Actual second derivatives and the literal frozen elasticity operator on
boundary profiles. The coefficients below act on physical tensor indices. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryLayerOperator
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryProfile ElasticityBoundaryMVNormal

lemma principal_apply (a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → MP) (δ : ℝ) (p : W) (i : Fin 3) :
    principal a δ p i = ∑ α, ∑ j, ∑ β, a i α j β * D δ α (D δ β (p j)) := by
  simp [principal, LinearMap.sum_apply]

lemma D_zero (j : Fin 3) (p : MP) :
    D 0 j p = ![Complex.I • p, 0, pderiv 2 p-p] j := by
  fin_cases j <;> simp [D]

/-- The leading operator in the high-frequency construction is precisely the
normal operator for which a zero-boundary inverse was proved. -/
theorem principal_leading_is_normal (l m : ℂ) :
    principal (fun i α j β => C (elasticityTensor l m i α j β)) 0 = normal l m := by
  apply LinearMap.ext
  intro p
  funext i
  rw [principal_apply, normal_apply]
  have hI : (C Complex.I : MP)^2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have h2 : C (2:ℂ) = (2:MP) := map_natCast C 2
  fin_cases i <;>
    simp [Fin.sum_univ_three, elasticityTensor, D_zero, lap_apply, shift_apply, map_sub,
      smul_eq_C_mul, map_add, map_mul,
      smul_sub, h2] <;> ring_nf <;> simp only [hI] <;> ring

end ElasticityBoundaryLayerOperator

end
end
section
/-! The finite-parameter differential operator of the actual Taylor-expanded
divergence tensor. No leading normal operator is stipulated. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryTensorSeries
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

lemma pack_coeff (q : Fin 3 → Polynomial MP) (n : ℕ) (i : Fin 3) :
    (pack q).coeff n i = (q i).coeff n := by
  simp [pack, LinearMap.sum_apply, Polynomial.finsetSum_coeff, coeffMap_coeff,
    Pi.single_apply]

lemma unpack_pack (q : Fin 3 → Polynomial MP) (i : Fin 3) : unpack i (pack q)=q i := by
  apply Polynomial.ext
  intro n
  exact pack_coeff q n i

lemma pack_unpack (q : Polynomial W) : pack (fun i => unpack i q)=q := by
  ext n i
  simp [pack_coeff,unpack]

lemma eval_unpack (q : Polynomial W) (δ : ℝ) (i : Fin 3) :
    (unpack i q).eval (C (δ:ℂ))=(q.eval (algebraMap ℂ W (δ:ℂ))) i := by
  have h := eval_coeffMap (A := W) (B := MP) (LinearMap.proj i) q (δ:ℂ)
  change _ = (q.eval (algebraMap ℂ W (δ:ℂ))) i at h
  exact h

lemma pack_monomial_mul (n : ℕ) (q : Fin 3 → Polynomial MP) :
    pack (fun i => Polynomial.monomial n 1*q i)=Polynomial.monomial n 1*pack q := by
  simp only [pack, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    coeffMap_monomial_one_mul, Finset.mul_sum]

lemma unpack_operator (a : Tensor) (b : Lower) (q : Polynomial W) (i : Fin 3) :
    unpack i (operator a b q) =
      (∑ α, ∑ j, ∑ β, a i α j β * PD α (PD β (unpack j q))) +
      Polynomial.X^2 * (∑ j, ∑ β, b i j β * PD β (unpack j q)) := by
  simp only [operator, LinearMap.comp_apply, unpack_pack, LinearMap.pi_apply,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]

/-- Evaluation reproduces the actual scaled principal part and the delta^2
lower-order coefficient-gradient part of a divergence-form operator. -/
theorem eval_operator (a : Tensor) (b : Lower) (q : Polynomial W) (δ : ℝ) (i : Fin 3) :
    (operator a b q).eval (algebraMap ℂ W (δ:ℂ)) i =
      principal (fun i α j β => (a i α j β).eval (C (δ:ℂ))) δ
        (q.eval (algebraMap ℂ W (δ:ℂ))) i +
      (δ:ℂ)^2 • (∑ j, ∑ β, (b i j β).eval (C (δ:ℂ)) *
        D δ β ((q.eval (algebraMap ℂ W (δ:ℂ))) j)) := by
  rw [← eval_unpack, unpack_operator]
  simp only [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, eval_PD, eval_unpack, principal_apply,
    smul_eq_C_mul, map_pow]

lemma unpack_monomial_mul (i : Fin 3) (n : ℕ) (q : Polynomial W) :
    unpack i (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*unpack i q := by
  unfold unpack
  exact coeffMap_monomial_one_mul (A := W) (B := MP) (LinearMap.proj i) n q

lemma unpack_operator_monomial_mul (a : Tensor) (b : Lower) (n : ℕ)
    (q : Polynomial W) (i : Fin 3) :
    unpack i (operator a b (Polynomial.monomial n 1*q)) =
      Polynomial.monomial n 1*unpack i (operator a b q) := by
  rw [unpack_operator, unpack_operator]
  simp only [unpack_monomial_mul, PD_monomial_one_mul]
  have hm (c p : Polynomial MP) : c*(Polynomial.monomial n 1*p)=
      Polynomial.monomial n 1*(c*p) := mul_left_comm _ _ _
  simp_rw [hm, ← Finset.mul_sum]
  rw [hm, ← mul_add]

lemma operator_monomial_mul (a : Tensor) (b : Lower) (n : ℕ) (q : Polynomial W) :
    operator a b (Polynomial.monomial n 1*q)=Polynomial.monomial n 1*operator a b q := by
  rw [← pack_unpack (operator a b (Polynomial.monomial n 1*q))]
  simp_rw [unpack_operator_monomial_mul]
  rw [pack_monomial_mul, pack_unpack]

lemma coefficient_apply (a : Tensor) (b : Lower) (k : ℕ) (p : W) :
    coefficient a b k p = (operator a b (Polynomial.C p)).coeff k := rfl

/-- Its leading coefficient is exactly the proved normal operator whenever
its actual tensor at the base point is the isotropic physical tensor. -/
theorem coefficient_zero (a : Tensor) (b : Lower) (l m : ℂ)
    (ha : ∀ i α j β, (a i α j β).coeff 0=C (elasticityTensor l m i α j β)) :
    coefficient a b 0=normal l m := by
  apply LinearMap.ext
  intro p
  funext i
  rw [coefficient_apply, Polynomial.coeff_zero_eq_eval_zero]
  have h := eval_operator a b (Polynomial.C p) 0 i
  simp only [Complex.ofReal_zero, map_zero, Polynomial.eval_C,
    zero_pow (by norm_num : (2:ℕ)≠0), zero_smul, add_zero] at h
  simp_rw [← Polynomial.coeff_zero_eq_eval_zero, ha] at h
  rw [principal_leading_is_normal] at h
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using h

end ElasticityBoundaryTensorSeries

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Corrected amplitudes for the literal Taylor tensor differential operator.
The operator coefficients are computed, rather than a formal sequence assumed. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryActualTower
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryTensorSeries ElasticityBoundaryMVTower ElasticityBoundaryTaylorPolynomial

lemma operator_monomial (a : Tensor) (b : Lower) (n : ℕ) (p : W) :
    operator a b (Polynomial.monomial n p)=
      Polynomial.X^n*operator a b (Polynomial.C p) := by
  have h : Polynomial.monomial n p = Polynomial.monomial n 1*Polynomial.C p := by
    rw [Polynomial.monomial_mul_C, one_mul]
  rw [h, operator_monomial_mul, Polynomial.monomial_one_right_eq_X_pow]

lemma coefficient_operator_amplitude (a : Tensor) (b : Lower) (p : ℕ → W)
    {N d : ℕ} (hd : d≤N) :
    (operator a b (amplitude p N)).coeff d =
      ∑ k ∈ Finset.range (d+1), coefficient a b k (p (d-k)) := by
  simp only [amplitude, map_sum, operator_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow_mul', ← coefficient_apply]
  have hsub : (∑ n ∈ Finset.range (N+1), if n≤d then coefficient a b (d-n) (p n) else 0) =
      ∑ n ∈ Finset.range (d+1), coefficient a b (d-n) (p n) := by
    rw [← Finset.sum_subset (Finset.range_mono (show d+1≤N+1 by omega))
      (f := fun n => if n≤d then coefficient a b (d-n) (p n) else 0)]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [ite_eq_left (by simp only [Finset.mem_range] at hn; omega)]
    · intro n _ hn
      rw [ite_eq_right (by simp only [Finset.mem_range] at hn; omega)]
  rw [hsub, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  congr 2
  omega

/-- A true finite polynomial family cancels the literal tensor operator to
any requested order. This is not an assumption about an unknown symbol. -/
theorem finite_tensor_amplitude_oai (a : Tensor) (b : Lower) (l m : ℂ)
    (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha : ∀ i α j β, (a i α j β).coeff 0=C (ElasticityBoundaryLayerOperator.elasticityTensor l m i α j β))
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ (p : ℕ → W) (R : Polynomial W), p 0=p₀ ∧
      (∀ n, 0<n → boundary (p n)=0) ∧
      operator a b (amplitude p N)=Polynomial.X^(N+1)*R := by
  obtain ⟨p,hp0,hb,hc⟩ := triangular_amplitudes l m hm he hp (coefficient a b)
    (coefficient_zero a b l m ha) p₀ h₀
  have hd : Polynomial.X^(N+1) ∣ operator a b (amplitude p N) := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    rw [coefficient_operator_amplitude a b p (by omega), hc]
  obtain ⟨R,hR⟩ := hd
  exact ⟨p,R,hp0,hb,hR⟩

end ElasticityBoundaryActualTower

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude_oai := @OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude_oai
