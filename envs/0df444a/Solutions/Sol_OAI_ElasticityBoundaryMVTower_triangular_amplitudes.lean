-- Prove2me | solution 1 for OAI.ElasticityBoundaryMVTower.triangular_amplitudes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:49:41.544467+00:00
-- url     : https://prove2.me/submissions/9200e17e-dba0-496e-b8c9-43b988ebb5cb

import Mathlib
import Definitions.Def_OAIQ6El004

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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
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
/-!
Polynomial-amplitude inversion for the frozen physical half-space operator.
This is the arbitrary-order normal ODE used in a boundary-layer construction:
every exp(-t)-polynomial forcing has an exp(-t)-polynomial solution with
zero boundary value. No pseudodifferential solvability is assumed.
-/
noncomputable section
open Polynomial
namespace ElasticityBoundarySymbol

lemma polynomial_derivative_surjective : Function.Surjective (Polynomial.derivative : P →ₗ[ℂ] P) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hq
      exact ⟨u+v, by rw [map_add, hu, hv]⟩
  | monomial n a =>
      refine ⟨monomial (n+1) (a / (n+1)), ?_⟩
      rw [derivative_monomial_succ, div_mul_cancel₀]
      exact Nat.cast_add_one_ne_zero n

/-- Although differentiation is nilpotent only degree by degree, each nonzero
scalar shift is onto the whole space of finite polynomials. -/
lemma shiftedDerivative_surjective (c : ℂ) (hc : c≠0) :
    Function.Surjective (shiftedDerivative c) := by
  have hm : ∀ n : ℕ, ∀ a : ℂ, ∃ q : P, shiftedDerivative c q=monomial n a := by
    intro n
    induction n with
    | zero =>
        intro a
        refine ⟨C (-a/c), ?_⟩
        simp only [shiftedDerivative_apply, derivative_C, zero_sub, smul_C]
        rw [← map_neg, monomial_zero_left]
        congr 1
        simp only [smul_eq_mul, neg_div, mul_neg, neg_neg]
        exact mul_div_cancel₀ a hc
    | succ n ih =>
        intro a
        obtain ⟨q, hq⟩ := ih (a * (n+1))
        let p : P := monomial (n+1) a
        have hd : derivative p=monomial n (a*(n+1)) := derivative_monomial_succ a n
        refine ⟨c⁻¹ • (q-p), ?_⟩
        rw [map_smul, map_sub, hq, ← hd, shiftedDerivative_apply]
        rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hq
      exact ⟨u+v, by rw [map_add, hu, hv]⟩
  | monomial n a => exact hm n a

lemma laplaceAmplitude_apply (p : P) :
    laplaceAmplitude p=derivative (derivative p)-(2 : ℂ) • derivative p := by
  simp [laplaceAmplitude, shiftedDerivative]

lemma laplaceAmplitude_surjective : Function.Surjective laplaceAmplitude :=
  polynomial_derivative_surjective.comp (shiftedDerivative_surjective 2 two_ne_zero)

lemma polynomial_adjugate_identity (l m : ℂ) (p : Fin 3 → P) :
    polynomialPhysical l m (polynomialAdjugate l m p) =
      fun i => (m*(l+2*m)) • laplaceAmplitude (laplaceAmplitude (p i)) := by
  funext i
  fin_cases i <;> simp [polynomialPhysical, polynomialAdjugate,
    laplaceAmplitude_apply, smul_add, smul_sub, smul_smul]
  all_goals match_scalars
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals ring

/-- No exceptional polynomial degree occurs in the normal recurrence. -/
theorem polynomialPhysical_surjective (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) :
    Function.Surjective (polynomialPhysical l m) := by
  intro p
  have hq : ∀ i : Fin 3, ∃ q : P,
      laplaceAmplitude (laplaceAmplitude q)=(m*(l+2*m))⁻¹ • p i := by
    intro i
    exact (laplaceAmplitude_surjective.comp laplaceAmplitude_surjective) _
  choose q hq using hq
  refine ⟨polynomialAdjugate l m q, ?_⟩
  rw [polynomial_adjugate_identity]
  funext i
  rw [hq, smul_smul, mul_inv_cancel₀ (mul_ne_zero hm he), one_smul]

end ElasticityBoundarySymbol

end
end
section
/-! Zero-Dirichlet inversion, with a literal exponential-polynomial ODE
interpretation. This is the normal component of the boundary quasimode
recursion, not a replacement for variable-coefficient boundary localization. -/
noncomputable section
open Polynomial
namespace ElasticityBoundarySymbol

lemma homogeneousPolynomial_physical (l m : ℂ) (hp : l+3*m≠0) (f : F) :
    polynomialPhysical l m (homogeneousPolynomial l m f) = 0 := by
  have hp' : m*3+l≠0 := by convert hp using 1; ring
  have hp'' : l+m*3≠0 := by simpa only [mul_comm] using hp
  funext i
  apply Polynomial.funext
  intro z
  fin_cases i <;>
    simp [polynomialPhysical, homogeneousPolynomial, laplaceAmplitude_apply,
      shiftedDerivative_apply, slope, smul_eq_C_mul]
  all_goals field_simp [hp, hp']
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals field_simp [hp'']
  all_goals ring

lemma polynomialPhysical_sub (l m : ℂ) (p q : Fin 3 → P) :
    polynomialPhysical l m (p-q) = polynomialPhysical l m p - polynomialPhysical l m q := by
  funext i
  fin_cases i <;> simp [polynomialPhysical, smul_sub] <;> abel

/-- Every polynomial forcing has a decaying-polynomial solution with exactly
zero Dirichlet data. No exceptional normal order is excluded. -/
theorem polynomialPhysical_zero_boundary_surjective (l m : ℂ)
    (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0) (p : Fin 3 → P) :
    ∃ q : Fin 3 → P, polynomialPhysical l m q = p ∧ ∀ i, (q i).eval 0 = 0 := by
  obtain ⟨q, hq⟩ := polynomialPhysical_surjective l m hm he p
  let f : F := fun i => (q i).eval 0
  refine ⟨q-homogeneousPolynomial l m f, ?_, ?_⟩
  · rw [polynomialPhysical_sub, hq, homogeneousPolynomial_physical l m hp, sub_zero]
  · intro i
    simp [f]

end ElasticityBoundarySymbol

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

lemma d_lift (p : P) : d (lift p)=lift (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
      simp only [d_apply, lift, Polynomial.aeval_monomial, algebraMap_eq,
        Polynomial.derivative_monomial, pderiv_C_mul, pderiv_pow, pderiv_X_self, mul_one,
        map_mul, map_natCast]
      ring

lemma pderiv_lift (p : P) : pderiv 2 (lift p)=lift (Polynomial.derivative p) := d_lift p

lemma lap_lift (p : P) : lap (lift p)=lift (laplaceAmplitude p) := by
  change d (d (lift p)-(2:ℂ) • lift p)=_
  rw [map_sub, map_smul, d_lift, d_lift, laplaceAmplitude_apply, map_sub, map_smul]

lemma normal_lift (l m : ℂ) (p : Fin 3 → P) :
    normal l m (fun i => lift (p i)) = fun i => lift (polynomialPhysical l m p i) := by
  funext i
  fin_cases i <;>
    simp [normal_apply, polynomialPhysical, lap_lift, pderiv_lift]

lemma shift_mul {b : MP} (hb : pderiv 2 b=0) (p : MP) :
    shift (b*p)=b*shift p := by simp only [shift_apply, pderiv_mul, hb, zero_mul, zero_add]; ring
lemma lap_mul {b : MP} (hb : pderiv 2 b=0) (p : MP) : lap (b*p)=b*lap p := by
  simp only [lap_apply, pderiv_mul, hb, zero_mul, zero_add, smul_eq_C_mul]
  ring
lemma normal_mul (l m : ℂ) {b : MP} (hb : pderiv 2 b=0) (p : W) :
    normal l m (fun i => b*p i) = fun i => b*normal l m p i := by
  funext i
  fin_cases i <;> simp [normal_apply, shift_mul hb, lap_mul hb, smul_eq_C_mul] <;> ring

lemma boundary_lift (p : P) : boundaryRing (lift p)=C (p.eval 0) := by
  induction p using Polynomial.induction_on with
  | C c => simp [lift, boundaryRing]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | monomial n c _ => simp [lift, boundaryRing]

lemma monomial_split (a : Fin 3 →₀ ℕ) (c : ℂ) :
    monomial (a.erase 2) 1 * lift (Polynomial.monomial (a 2) c) = monomial a c := by
  simp only [lift, Polynomial.aeval_monomial, algebraMap_eq, C_mul_X_pow_eq_monomial,
    monomial_mul_monomial, one_mul, Finsupp.erase_add_single]

lemma normal_zeroBoundary_surjective (l m : ℂ) (hm : m≠0)
    (he : l+2*m≠0) (hp : l+3*m≠0) :
    Function.Surjective ((normal l m).comp (LinearMap.ker boundary).subtype) := by
  let R := LinearMap.range ((normal l m).comp (LinearMap.ker boundary).subtype)
  have hmono (i : Fin 3) (a : Fin 3 →₀ ℕ) (c : ℂ) : Pi.single i (monomial a c) ∈ R := by
    let p : Fin 3 → P := Pi.single i (Polynomial.monomial (a 2) c)
    obtain ⟨q,hq,hb⟩ := polynomialPhysical_zero_boundary_surjective l m hm he hp p
    let b : MP := monomial (a.erase 2) 1
    have hbd : pderiv 2 b=0 := by simp [b]
    let v : W := fun j => b*lift (q j)
    have hv : v ∈ LinearMap.ker boundary := by
      change boundary v=0
      funext j
      simp [v, boundary_lift, hb]
    refine ⟨⟨v,hv⟩, ?_⟩
    change normal l m v = Pi.single i (monomial a c)
    rw [show v=(fun j => b*lift (q j)) from rfl, normal_mul l m hbd, normal_lift, hq]
    funext j
    by_cases hj : j=i
    · subst j
      simpa [p,b] using monomial_split a c
    · simp [p,hj]
  have hsingle (i : Fin 3) (p : MP) : Pi.single i p ∈ R := by
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq => simpa only [Pi.single_add] using R.add_mem hp hq
    | monomial a c => exact hmono i a c
  intro p
  have hsum : (∑ i, Pi.single i (p i)) ∈ R := R.sum_mem (fun i _ => hsingle i (p i))
  have heq : (∑ i, Pi.single i (p i)) = p := by
    funext j; simp [Pi.single_apply]
  rw [heq] at hsum
  exact hsum

/-- A literal multivariable-polynomial right inverse with zero boundary values. -/
theorem exists_inverse (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0) :
    ∃ S : W →ₗ[ℂ] W, (normal l m).comp S=LinearMap.id ∧ boundary.comp S=0 := by
  obtain ⟨S,hS⟩ := ((normal l m).comp (LinearMap.ker boundary).subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (normal_zeroBoundary_surjective l m hm he hp))
  refine ⟨(LinearMap.ker boundary).subtype.comp S,hS,?_⟩
  apply LinearMap.ext
  intro p
  exact (S p).property

end ElasticityBoundaryMVNormal

end
end
section
/-! Finite-order polynomial amplitudes with an exact high-order residual
factor, for use in actual smooth boundary profiles. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryMVTower
open ElasticityBoundaryMVNormal

/-- Successive coefficients of a triangular polynomial-amplitude equation.
The zeroth coefficient is prescribed; all positive coefficients have zero
physical boundary values. -/
theorem triangular_amplitudes_oai (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (A : ℕ → (W →ₗ[ℂ] W)) (hA : A 0=normal l m)
    (p₀ : W) (h₀ : normal l m p₀=0) :
    ∃ p : ℕ → W, p 0=p₀ ∧
      (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ n, ∑ k ∈ Finset.range (n+1), A k (p (n-k))=0 := by
  obtain ⟨S, hS, hB⟩ := exists_inverse l m hm he hp
  let p : ℕ → W := Nat.strongRec fun n prev =>
    if hn : n=0 then p₀ else -S (∑ k : Fin n,
      A (k.val+1) (prev (n-(k.val+1)) (by omega)))
  have hrec (n : ℕ) : p n = if hn : n=0 then p₀ else -S (∑ k : Fin n,
      A (k.val+1) (p (n-(k.val+1)))) := by
    conv_lhs => unfold p; rw [Nat.strongRec_eq]
  have hzero : p 0=p₀ := by rw [hrec]; simp
  refine ⟨p, hzero, ?_, ?_⟩
  · intro n hn
    rw [hrec, dite_eq_right (by omega), map_neg]
    have hb := LinearMap.congr_fun hB (∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))))
    simpa using congrArg Neg.neg hb
  · intro n
    have hsum : (∑ k ∈ Finset.range (n+1), A k (p (n-k))) =
        A 0 (p n) + ∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))) := by
      rw [Finset.sum_range_succ']
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [Nat.sub_zero]
      exact add_comm _ _
    rw [hsum, hA]
    by_cases hn : n=0
    · subst n
      simpa [hzero] using h₀
    · rw [hrec, dite_eq_right hn, map_neg]
      have hs := LinearMap.congr_fun hS (∑ k : Fin n, A (k.val+1) (p (n-(k.val+1))))
      change normal l m (S _) = _ at hs
      rw [hs, LinearMap.id_apply, neg_add_cancel]

end ElasticityBoundaryMVTower

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryMVTower.triangular_amplitudes_oai := @OAI.ElasticityBoundaryMVTower.triangular_amplitudes_oai
