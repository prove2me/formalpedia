-- Prove2me | solution 1 for OAI.ComplexCancellation.AffineModification.extract
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:18:30.494137+00:00
-- url     : https://prove2.me/submissions/b28a90b5-806f-46a7-b4d3-31b49d2630d6

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/HomogeneousExtraction.lean:L62-L116
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.AffineModification.extract. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_derivation_zero_of_generators
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_monomial
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_negative
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_odd
import Theorems.Thm_OAI_ComplexCancellation_LND_cancel_factor_locallyNilpotent
import Theorems.Thm_OAI_ComplexCancellation_LND_cancel_factor_square_zero
import Theorems.Thm_OAI_ComplexCancellation_LND_kernel_factorially_closed

-- ---- from OAI.Algebra.AffineCancellation.FactorDerivation ----
namespace OAI

noncomputable section

namespace ComplexCancellation.FactorDerivation
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [IsDomain R]
  [Algebra k S] [Algebra k R]
variable (f : S →ₐ[k] R) (hf : Function.Injective f)
  (D : Derivation k R R) (c : R) (hc : c ≠ 0)
  (h : ∀ s : S, ∃ t : S, D (f s)=c*f t)
lemma apply_spec (s : S) : D (f s)=c*f (derivation f hf D c hc h s) := specification f D c h s
end ComplexCancellation.FactorDerivation

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Orbit ----
namespace OAI

noncomputable section

/-! Orbit polynomials and exponentiation of locally nilpotent derivations. -/
namespace ComplexCancellation.LND
open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

lemma orbit_injective (D : Derivation k R R) (hD : LocallyNilpotent D) :
    Function.Injective (orbit D hD) := by
  intro r s hes
  simpa using congrArg (fun p : R[X] => p.coeff 0) hes

lemma orbit_constant_iff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    orbit D hD r = C r ↔ D r = 0 := by
  constructor
  · intro h
    simpa using congrArg (fun p : R[X] => p.coeff 1) h
  · intro h
    ext n
    cases n with
    | zero => simp
    | succ n => simp [Function.iterate_succ_apply, h]

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Kernel ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

lemma inv_factorial_succ (n : ℕ) :
    ((n + 1 : ℕ) : k) * ((n + 1).factorial : k)⁻¹ = (n.factorial : k)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  have hn : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

lemma derivative_orbit (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).derivative = orbit D hD (D r) := by
  ext n
  rw [Polynomial.coeff_derivative, orbit_coeff, orbit_coeff,
    ← Function.iterate_succ_apply]
  rw [mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    inv_factorial_succ]

end ComplexCancellation.LND
namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R] [IsDomain R]

lemma fixed_of_dvd (D : Derivation k R R) (hD : LocallyNilpotent D)
    {r : R} (hr : r ∣ D r) : D r = 0 := by
  obtain ⟨s, hs⟩ := hr
  have hdvd : orbit D hD r ∣ (orbit D hD r).derivative := by
    rw [derivative_orbit, hs, orbit_mul]
    exact dvd_mul_right _ _
  have hz := Polynomial.dvd_derivative_iff.mp hdvd
  rw [derivative_orbit] at hz
  apply orbit_injective D hD
  change orbitHom D hD (D r) = orbitHom D hD 0
  rw [map_zero]
  exact hz

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Order ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

omit [CharZero k] [IsDomain R] in
lemma orbit_ne_zero (D : Derivation k R R) (hD : LocallyNilpotent D) {r : R} (hr : r ≠ 0) :
    orbit D hD r ≠ 0 := by
  intro h
  apply hr
  simpa using congrArg (fun f : R[X] => f.coeff 0) h

lemma order_mul (D : Derivation k R R) (hD : LocallyNilpotent D) {r s : R}
    (hr : r ≠ 0) (hs : s ≠ 0) : order D hD (r*s) = order D hD r + order D hD s := by
  exact (congrArg natDegree (orbit_mul D hD r s)).trans
    (natDegree_mul (orbit_ne_zero D hD hr) (orbit_ne_zero D hD hs))

omit [CharZero k] [IsDomain R] in
lemma order_zero_iff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    order D hD r = 0 ↔ D r = 0 := by
  rw [← orbit_constant_iff D hD r]
  constructor
  · intro hr
    simpa using eq_C_of_natDegree_eq_zero hr
  · intro h
    simp only [order, h, natDegree_C]

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R S : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [CommRing S] [Algebra k S] [Algebra k R]
end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Modification ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] [IsDomain R] (v : R)

lemma isDomain (hv : v ≠ 0) : IsDomain (T R v) :=
  Function.Injective.isDomain (embedding R v) (embedding_injective R v hv)

end ComplexCancellation.AffineModification

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ModificationGrading ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] (v : R)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
lemma degree_cases (e : ℤ) :
    (∃ n : ℕ, e=-(n+1:ℤ)) ∨ (∃ n : ℕ, e=2*(n:ℤ)) ∨ (∃ n : ℕ, e=2*(n:ℤ)+1) := by
  by_cases hn : e < 0
  · exact Or.inl ⟨(-e-1).toNat,by omega⟩
  · by_cases hm : e%2=0
    · exact Or.inr (Or.inl ⟨(e/2).toNat,by omega⟩)
    · exact Or.inr (Or.inr ⟨(e/2).toNat,by omega⟩)
lemma degree_even_of_not_τ_dvd {r : T R v} {e : ℤ} (hr : r ∈ pieces R v e)
    (h : ¬τ R v ∣ r) : ∃ n : ℕ, e=2*(n:ℤ) := by
  rcases degree_cases e with ⟨n,hen⟩ | he | ⟨n,hen⟩
  · exfalso
    apply h
    rw [hen] at hr
    have hr' : r ∈ pieces R v (-((n+1:ℕ):ℤ)) := by simpa using hr
    obtain ⟨s,rfl⟩ := piece_negative R v (n+1) hr'
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega : n+1 ≠ 0)) _
  · exact he
  · exfalso
    apply h
    rw [hen] at hr
    obtain ⟨s,rfl⟩ := piece_odd R v n hr
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
lemma coefficient_mem (r : R) : algebraMap R (T R v) r ∈ pieces R v 0 :=
  ⟨C r,isWeightedHomogeneous_C _ _,(π R v).commutes r⟩
lemma τ_mem : τ R v ∈ pieces R v (-1) := ⟨X 0,isWeightedHomogeneous_X R weight 0,rfl⟩
end ComplexCancellation.AffineModification

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Extraction ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
variable (v : R) (hv : v ≠ 0)
lemma coefficient_injective : Function.Injective (algebraMap R (T R v)) := by
  apply Function.Injective.of_comp (f := embedding R v)
  intro r s he
  change embedding R v (algebraMap R (T R v) r)=embedding R v (algebraMap R (T R v) s) at he
  rw [AlgHom.commutes,AlgHom.commutes] at he
  exact ((RatFunc.C_injective).comp (IsFractionRing.injective R (F R))) he
lemma τ_nonzero : τ R v ≠ 0 := by
  intro h
  have he := congrArg (embedding R v) h
  have he' : (RatFunc.X : K R)=0 := by
    simpa [τ,eval,values] using he
  exact RatFunc.X_ne_zero he'
include hv in
lemma V_nonzero : V R v ≠ 0 := by
  intro h
  have he := equation R v
  rw [h,mul_zero] at he
  exact hv ((coefficient_injective v) (he.symm.trans (map_zero _).symm))

omit [CharZero k] in
lemma coefficientHom_injective : Function.Injective (coefficientHom (k := k) v) :=
  coefficient_injective v

omit [CharZero k] [IsDomain R] in
lemma euler_monomial (H : Derivation k R R) (hH : H v=2*v) (i h : ℕ) :
    euler v H hH (τ R v^i*V R v^h)=(2*h:ℕ)*(τ R v^i*V R v^h) := by
  simp only [Derivation.leibniz,Derivation.leibniz_pow,euler_τ,euler_V,
    smul_eq_mul,mul_zero,add_zero,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  by_cases hh : h=0
  · subst h; simp
  · have he : V R v^(h-1)*V R v=V R v^h := by rw [← pow_succ]; congr 1; omega
    calc
      _ = (2*(h : T R v))*(τ R v^i*(V R v^(h-1)*V R v)) := by ring
      _ = _ := by rw [he]

end ComplexCancellation.AffineModification

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.HomogeneousExtraction ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
variable (v : R) (hv : v ≠ 0)
include hv

omit [CharZero k] in
lemma euler_factor (H : Derivation k R R) (hH : H v=2*v)
    (D : Derivation k (T R v) (T R v))
    (hcomm : ∀ z, euler v H hH (D z)=D (euler v H hH z))
    (E : Derivation k R R) (c : T R v) (hc : c ≠ 0) (n : ℕ)
    (hcn : euler v H hH c=n • c)
    (hspec : ∀ r, D (coefficientHom (k := k) v r)=c*coefficientHom (k := k) v (E r)) :
    ∀ r, H (E r)-E (H r)=-(n • E r) := by
  let := isDomain R v hv
  intro r
  apply coefficientHom_injective (k := k) v
  apply mul_left_cancel₀ hc
  have he := hcomm (coefficientHom (k := k) v r)
  rw [hspec,euler_coefficient,hspec,Derivation.leibniz,euler_coefficient,hcn] at he
  simp only [map_sub,map_neg,smul_eq_mul,nsmul_eq_mul,map_mul,map_natCast] at he ⊢
  linear_combination he

lemma fixed_τ_of_fixed_v (D : Derivation k (T R v) (T R v))
    (hD : LND.LocallyNilpotent D) (h : D (coefficientHom (k := k) v v)=0) : D (τ R v)=0 := by
  let := isDomain R v hv
  have hnτ := τ_nonzero v
  have hnV := V_nonzero v hv
  apply (LND.kernel_factorially_closed D hD hnτ (mul_ne_zero hnτ hnV) _).1
  have he : τ R v*(τ R v*V R v)=coefficientHom (k := k) v v := by
    change τ R v*(τ R v*V R v)=algebraMap R (T R v) v
    simpa only [pow_two,mul_assoc] using equation R v
  rwa [he]

lemma coefficient_order (D : Derivation k (T R v) (T R v))
    (hD : LND.LocallyNilpotent D) (hV : D (V R v)=0) :
    LND.order D hD (coefficientHom (k := k) v v)=2*LND.order D hD (τ R v) := by
  let := isDomain R v hv
  have h₀ := (LND.order_zero_iff D hD (V R v)).mpr hV
  change LND.order D hD (algebraMap R (T R v) v)=_
  rw [← equation R v,pow_two,
    LND.order_mul D hD (mul_ne_zero (τ_nonzero v) (τ_nonzero v)) (V_nonzero v hv),
    LND.order_mul D hD (τ_nonzero v) (τ_nonzero v),h₀]
  omega

lemma order_monomial_fixed_V (D : Derivation k (T R v) (T R v))
    (hD : LND.LocallyNilpotent D) (hV : D (V R v)=0) (n : ℕ) :
    LND.order D hD (τ R v*V R v^n)=LND.order D hD (τ R v) := by
  let := isDomain R v hv
  rw [LND.order_mul D hD (τ_nonzero v) (pow_ne_zero _ (V_nonzero v hv))]
  have he : D (V R v^n)=0 := by simp [Derivation.leibniz_pow,hV]
  rw [(LND.order_zero_iff D hD _).mpr he,add_zero]

/-- Extraction of a coefficient derivation without assuming invariance of the coefficient ring. -/
theorem extract (H : Derivation k R R) (hH : H v=2*v)
    (D : Derivation k (T R v) (T R v)) (hD : LND.LocallyNilpotent D) (hDn : D ≠ 0)
    (j : ℤ) (hshift : ∀ e r, r ∈ pieces R v e → D r ∈ pieces R v (e+j))
    (hcomm : ∀ z, euler v H hH (D z)=D (euler v H hH z))
    (hV : D (V R v)=0) :
    ∃ (E : Derivation k R R) (n : ℕ), E ≠ 0 ∧ LND.LocallyNilpotent E ∧
      (∀ r, H (E r)-E (H r)=-(n • E r)) ∧ E (E v)=0 := by
  let := isDomain R v hv
  let f := coefficientHom (k := k) v
  have hf : Function.Injective f := coefficientHom_injective v
  have hcoeff (r : R) : D (f r) ∈ pieces R v j := by
    simpa only [zero_add] using hshift 0 (f r) (coefficient_mem R v r)
  by_cases ht : D (τ R v)=0
  · obtain ⟨i,h,hpiece⟩ := piece_monomial R v j
    let c := τ R v^i*V R v^h
    have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (τ_nonzero v)) (pow_ne_zero _ (V_nonzero v hv))
    have hspec : ∀ r : R, ∃ s : R, D (f r)=c*f s := fun r => hpiece _ (hcoeff r)
    let E := FactorDerivation.derivation f hf D c hc hspec
    have he (r : R) : D (f r)=c*f (E r) := FactorDerivation.apply_spec f hf D c hc hspec r
    have hEv : E v=0 := by
      apply hf
      apply mul_left_cancel₀ hc
      rw [map_zero,mul_zero,← he]
      change D (algebraMap R (T R v) v)=0
      rw [← equation R v]
      simp [Derivation.leibniz,Derivation.leibniz_pow,ht,hV]
    refine ⟨E,2*h,?_,LND.cancel_factor_locallyNilpotent f hf D hD E hc he,?_,?_⟩
    · intro hE
      apply hDn
      apply derivation_zero_of_generators v D _ ht hV
      intro r
      rw [he,hE,Derivation.zero_apply,map_zero,mul_zero]
    · apply euler_factor v hv H hH D hcomm E c hc (2*h) _ he
      simpa only [nsmul_eq_mul] using euler_monomial v H hH i h
    · rw [hEv,map_zero]
  · have hnt : ¬τ R v ∣ D (τ R v) := fun he => ht (LND.fixed_of_dvd D hD he)
    obtain ⟨l,hl⟩ := degree_even_of_not_τ_dvd R v (hshift (-1) _ (τ_mem R v)) hnt
    have hj : j=2*(l:ℤ)+1 := by omega
    have hspec : ∀ r : R, ∃ s : R, D (f r)=(τ R v*V R v^(l+1))*f s := by
      intro r
      exact piece_odd R v l (hj ▸ hcoeff r)
    let c := τ R v*V R v^(l+1)
    have hc : c ≠ 0 := mul_ne_zero (τ_nonzero v) (pow_ne_zero _ (V_nonzero v hv))
    let E := FactorDerivation.derivation f hf D c hc hspec
    have he (r : R) : D (f r)=c*f (E r) := FactorDerivation.apply_spec f hf D c hc hspec r
    refine ⟨E,2*(l+1),?_,LND.cancel_factor_locallyNilpotent f hf D hD E hc he,?_,?_⟩
    · intro hE
      apply ht
      apply fixed_τ_of_fixed_v v hv D hD
      rw [he,hE,Derivation.zero_apply,map_zero,mul_zero]
    · apply euler_factor v hv H hH D hcomm E c hc (2*(l+1)) _ he
      simpa only [pow_one,nsmul_eq_mul] using euler_monomial v H hH 1 (l+1)
    · apply LND.cancel_factor_square_zero f hf D hD E hc he v
      rw [coefficient_order v hv D hD hV,order_monomial_fixed_V v hv D hD hV]
end ComplexCancellation.AffineModification

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.AffineModification
open MvPolynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.AffineModification.extract := @_root_.OAI.ComplexCancellation.AffineModification.extract
