-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.isDomain_and_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/98bd42aa-11c1-5b8c-8a0d-c8f6132e0b09

import Mathlib
import Definitions.Def_MvPolynomial_CrossingQuotient
import Theorems.Thm_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top
import Theorems.Thm_LaurentPolynomial_uniqueFactorizationMonoid
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_isDomain_and_isIntegrallyClosed

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

open scoped Polynomial LaurentPolynomial

namespace SENORMAL

universe u

variable {W : Type u} [CommRing W] (t : W)

noncomputable def gen₁ : Fin 2 → W[T;T⁻¹] :=
  ![LaurentPolynomial.T 1, LaurentPolynomial.C t * LaurentPolynomial.T (-1)]

noncomputable def gen₂ : Fin 2 → W[T;T⁻¹] :=
  ![LaurentPolynomial.C t * LaurentPolynomial.T 1, LaurentPolynomial.T (-1)]

theorem gen₁_zero : gen₁ t 0 = LaurentPolynomial.T 1 := rfl
theorem gen₁_one : gen₁ t 1 = LaurentPolynomial.C t * LaurentPolynomial.T (-1) := rfl
theorem gen₂_zero : gen₂ t 0 = LaurentPolynomial.C t * LaurentPolynomial.T 1 := rfl
theorem gen₂_one : gen₂ t 1 = LaurentPolynomial.T (-1) := rfl

theorem T_one_mul_T_neg_one :
    (LaurentPolynomial.T 1 : W[T;T⁻¹]) * LaurentPolynomial.T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]; rfl

theorem rel₁ : (LaurentPolynomial.T 1 : W[T;T⁻¹]) * (LaurentPolynomial.C t * LaurentPolynomial.T (-1))
    = LaurentPolynomial.C t := by
  rw [mul_left_comm, T_one_mul_T_neg_one, mul_one]

theorem rel₂ : (LaurentPolynomial.C t * LaurentPolynomial.T 1 : W[T;T⁻¹]) * LaurentPolynomial.T (-1)
    = LaurentPolynomial.C t := by
  rw [mul_assoc, T_one_mul_T_neg_one, mul_one]

theorem aeval_gen₁_rel : aeval (gen₁ t) (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C, gen₁_zero, gen₁_one, rel₁,
    ← LaurentPolynomial.C_eq_algebraMap, sub_self]

theorem aeval_gen₂_rel : aeval (gen₂ t) (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C, gen₂_zero, gen₂_one, rel₂,
    ← LaurentPolynomial.C_eq_algebraMap, sub_self]

noncomputable def φ₁ : CrossingQuotient W t →ₐ[W] W[T;T⁻¹] :=
  Ideal.Quotient.liftₐ _ (aeval (gen₁ t)) (fun p hp => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, aeval_gen₁_rel, mul_zero])

noncomputable def φ₂ : CrossingQuotient W t →ₐ[W] W[T;T⁻¹] :=
  Ideal.Quotient.liftₐ _ (aeval (gen₂ t)) (fun p hp => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, aeval_gen₂_rel, mul_zero])

theorem φ₁_mk (p : MvPolynomial (Fin 2) W) : φ₁ t (mk t p) = aeval (gen₁ t) p := rfl
theorem φ₂_mk (p : MvPolynomial (Fin 2) W) : φ₂ t (mk t p) = aeval (gen₂ t) p := rfl

theorem φ₁_monomial (n : ℤ) :
    φ₁ t (monomial t n) = LaurentPolynomial.C (t ^ (-n).toNat) * LaurentPolynomial.T n := by
  rcases le_or_gt 0 n with h | h
  · rw [monomial_of_nonneg t h, map_pow, φ₁_mk, aeval_X, gen₁_zero, LaurentPolynomial.T_pow,
      mul_one, Int.toNat_of_nonneg h, Int.toNat_of_nonpos (neg_nonpos.mpr h), pow_zero, map_one,
      one_mul]
  · rw [monomial_of_neg t h, map_pow, φ₁_mk, aeval_X, gen₁_one, mul_pow, ← map_pow,
      LaurentPolynomial.T_pow, mul_neg_one, Int.toNat_of_nonneg (by omega : 0 ≤ -n), neg_neg]

theorem φ₁_repr (c : ℤ →₀ W) :
    φ₁ t (c.sum fun n r => r • monomial t n)
      = c.sum fun n r => AddMonoidAlgebra.single n (r * t ^ (-n).toNat) := by
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun n _ => ?_
  rw [map_smul, φ₁_monomial, LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul,
    LaurentPolynomial.single_eq_C_mul_T]

theorem coeff_φ₁_repr (c : ℤ →₀ W) (m : ℤ) :
    (φ₁ t (c.sum fun n r => r • monomial t n)).coeff m = c m * t ^ (-m).toNat := by
  rw [φ₁_repr, AddMonoidAlgebra.coeff_finsuppSum, Finsupp.sum_apply, Finsupp.sum,
    Finset.sum_eq_single m]
  · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro n _ hn
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hn]
  · intro hm
    rw [Finsupp.notMem_support_iff.mp hm, zero_mul, AddMonoidAlgebra.single_zero,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem exists_repr (a : CrossingQuotient W t) :
    ∃ c : ℤ →₀ W, (c.sum fun n r => r • monomial t n) = a := by
  have h := (MvPolynomial.CrossingQuotient.linearIndependent_monomial_and_span_eq_top t).2
  have ha : a ∈ Submodule.span W (Set.range (monomial t)) := by rw [h]; trivial
  exact Finsupp.mem_span_range_iff_exists_finsupp.mp ha

theorem φ₁_injective [IsDomain W] (ht : t ≠ 0) : Function.Injective (φ₁ t) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨c, rfl⟩ := exists_repr t a
  suffices hc : c = 0 by rw [hc, Finsupp.sum_zero_index]
  ext m
  have hm := coeff_φ₁_repr t c m
  rw [ha] at hm
  change (0 : W) = c m * t ^ (-m).toNat at hm
  rcases mul_eq_zero.mp hm.symm with h0 | h0
  · exact h0
  · exact absurd h0 (pow_ne_zero _ ht)

theorem mem_range_φ₁ [IsDomain W] (ht : t ≠ 0) (ℓ : W[T;T⁻¹])
    (h : ∀ m : ℤ, m < 0 → t ^ (-m).toNat ∣ ℓ.coeff m) :
    ∃ a, φ₁ t a = ℓ := by
  classical
  have h' : ∀ m : ℤ, ∃ d : W, ℓ.coeff m = d * t ^ (-m).toNat := by
    intro m
    rcases lt_or_ge m 0 with hm | hm
    · obtain ⟨d, hd⟩ := h m hm
      exact ⟨d, by rw [hd, mul_comm]⟩
    · exact ⟨ℓ.coeff m, by rw [Int.toNat_of_nonpos (neg_nonpos.mpr hm), pow_zero, mul_one]⟩
  choose d hd using h'
  have hsupp : ∀ m, d m ≠ 0 → m ∈ ℓ.coeff.support := by
    intro m hm
    rw [Finsupp.mem_support_iff, hd]
    exact mul_ne_zero hm (pow_ne_zero _ ht)
  let c : ℤ →₀ W := Finsupp.onFinset _ d hsupp
  refine ⟨c.sum fun n r => r • monomial t n, ?_⟩
  refine LaurentPolynomial.ext fun m => ?_
  rw [coeff_φ₁_repr, Finsupp.onFinset_apply, ← hd]

section chart

local notation "F" => FractionRing W[T;T⁻¹]
local notation "ι" => algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹])

theorem ι_injective : Function.Injective ι := IsFractionRing.injective _ _

variable [IsDomain W]

omit [IsDomain W] in
theorem C_mul_T_ne_zero (ht : t ≠ 0) (n : ℤ) : (LaurentPolynomial.C t * LaurentPolynomial.T n : W[T;T⁻¹]) ≠ 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact AddMonoidAlgebra.single_ne_zero.mpr ht

noncomputable def tTinv (ht : t ≠ 0) : (FractionRing W[T;T⁻¹])ˣ :=
  Units.mk0 (ι (LaurentPolynomial.C t * LaurentPolynomial.T (-1)))
    ((map_ne_zero_iff _ (ι_injective (W := W))).mpr (C_mul_T_ne_zero t ht (-1)))

theorem tTinv_val (ht : t ≠ 0) : (tTinv t ht : F) = ι (LaurentPolynomial.C t * LaurentPolynomial.T (-1)) := rfl

noncomputable def θ (ht : t ≠ 0) : W[T;T⁻¹] →+* FractionRing W[T;T⁻¹] :=
  LaurentPolynomial.eval₂ ((algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹])).comp LaurentPolynomial.C)
    (tTinv t ht)⁻¹

theorem θ_C (ht : t ≠ 0) (r : W) : θ t ht (LaurentPolynomial.C r) = ι (LaurentPolynomial.C r) := by
  rw [θ, LaurentPolynomial.eval₂_C, RingHom.comp_apply]

theorem θ_T (ht : t ≠ 0) (n : ℤ) : θ t ht (LaurentPolynomial.T n) = (((tTinv t ht)⁻¹ ^ n : (FractionRing W[T;T⁻¹])ˣ) : F) := by
  rw [θ, LaurentPolynomial.eval₂_T]

theorem θ_T_neg_one (ht : t ≠ 0) : θ t ht (LaurentPolynomial.T (-1)) = ι (LaurentPolynomial.C t * LaurentPolynomial.T (-1)) := by
  rw [θ_T, zpow_neg_one, inv_inv, tTinv_val]

theorem ι_T_one (ht : t ≠ 0) : ι (LaurentPolynomial.T 1) = ι (LaurentPolynomial.C t) * (((tTinv t ht)⁻¹ : (FractionRing W[T;T⁻¹])ˣ) : F) := by
  rw [Units.val_inv_eq_inv_val, tTinv_val, eq_mul_inv_iff_mul_eq₀
    ((map_ne_zero_iff _ (ι_injective (W := W))).mpr (C_mul_T_ne_zero t ht (-1))), ← map_mul, rel₁]

theorem θ_C_mul_T_one (ht : t ≠ 0) : θ t ht (LaurentPolynomial.C t * LaurentPolynomial.T 1) = ι (LaurentPolynomial.T 1) := by
  rw [map_mul, θ_C, θ_T, zpow_one, ι_T_one]

theorem θ_comp_φ₂ (ht : t ≠ 0) : (θ t ht).comp (φ₂ t : CrossingQuotient W t →+* W[T;T⁻¹])
    = (algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹])).comp (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹]) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change θ t ht (φ₂ t (mk t (C r))) = ι (φ₁ t (mk t (C r)))
    rw [φ₁_mk, φ₂_mk, MvPolynomial.algHom_C, MvPolynomial.algHom_C,
      ← LaurentPolynomial.C_eq_algebraMap, θ_C]
  · intro i
    change θ t ht (φ₂ t (mk t (X i))) = ι (φ₁ t (mk t (X i)))
    rw [φ₁_mk, φ₂_mk, aeval_X, aeval_X]
    fin_cases i
    · exact θ_C_mul_T_one t ht
    · exact θ_T_neg_one t ht

theorem θ_toLaurent (ht : t ≠ 0) (p : W[X]) :
    θ t ht (Polynomial.toLaurent p)
      = Polynomial.eval₂ ((algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹])).comp LaurentPolynomial.C)
          (((tTinv t ht)⁻¹ : (FractionRing W[T;T⁻¹])ˣ) : F) p := by
  rw [θ, LaurentPolynomial.eval₂_toLaurent]

omit [IsDomain W] in
theorem ι_toLaurent (p : W[X]) :
    ι (Polynomial.toLaurent p)
      = Polynomial.eval₂ ((algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹])).comp LaurentPolynomial.C)
          (ι (LaurentPolynomial.T 1)) p := by
  change ((algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹])).comp Polynomial.toLaurent) p
    = (Polynomial.eval₂RingHom _ _) p
  congr 1
  apply Polynomial.ringHom_ext'
  · ext r
    simp [Polynomial.toLaurent_C]
  · simp [Polynomial.toLaurent_X]

theorem θ_toLaurent_comp (ht : t ≠ 0) (p : W[X]) :
    θ t ht (Polynomial.toLaurent (p.comp (Polynomial.C t * Polynomial.X))) = ι (Polynomial.toLaurent p) := by
  rw [θ_toLaurent, Polynomial.eval₂_comp, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    RingHom.comp_apply, ← ι_T_one, ι_toLaurent]

theorem θ_toLaurent_mul_pow (ht : t ≠ 0) (p : W[X]) :
    θ t ht (Polynomial.toLaurent p) * ι (LaurentPolynomial.C t) ^ p.natDegree
      = ι (Polynomial.toLaurent (p.scaleRoots t)) := by
  rw [ι_toLaurent, ι_T_one, θ_toLaurent, mul_comm]
  have := Polynomial.scaleRoots_eval₂_mul_of_commute (p := p)
    ((algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹])).comp LaurentPolynomial.C)
    (((tTinv t ht)⁻¹ : (FractionRing W[T;T⁻¹])ˣ) : F) t (Commute.all _ _) (fun _ _ => Commute.all _ _)
  rw [RingHom.comp_apply] at this
  exact this.symm

theorem θ_injective (ht : t ≠ 0) : Function.Injective (θ t ht) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  have h1 : θ t ht (Polynomial.toLaurent p) = 0 := by rw [hp, map_mul, hf, zero_mul]
  have h2 : ι (Polynomial.toLaurent (p.scaleRoots t)) = 0 := by
    rw [← θ_toLaurent_mul_pow t ht, h1, zero_mul]
  have h3 : p.scaleRoots t = 0 := by
    rw [map_eq_zero_iff _ (ι_injective (W := W)), Polynomial.toLaurent_eq_zero] at h2
    exact h2
  have h4 : p = 0 := by
    by_contra h
    exact Polynomial.scaleRoots_ne_zero h t h3
  rw [h4, map_zero] at hp
  exact (LaurentPolynomial.isUnit_T n).mul_left_eq_zero.mp hp.symm

theorem exists_θ_div (ht : t ≠ 0) (g : W[T;T⁻¹]) :
    ∃ a b : W[T;T⁻¹], θ t ht b ≠ 0 ∧ ι g = θ t ht a / θ t ht b := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow g
  refine ⟨Polynomial.toLaurent (p.comp (Polynomial.C t * Polynomial.X)),
    Polynomial.toLaurent ((Polynomial.X ^ n).comp (Polynomial.C t * Polynomial.X)), ?_, ?_⟩
  · rw [θ_toLaurent_comp, Polynomial.toLaurent_X_pow, map_ne_zero_iff _ (ι_injective (W := W))]
    exact (LaurentPolynomial.isUnit_T (R := W) n).ne_zero
  · rw [θ_toLaurent_comp, θ_toLaurent_comp, Polynomial.toLaurent_X_pow, hp, map_mul,
      mul_div_cancel_right₀]
    rw [map_ne_zero_iff _ (ι_injective (W := W))]
    exact (LaurentPolynomial.isUnit_T (R := W) n).ne_zero

theorem θ_surj (ht : t ≠ 0) (z : FractionRing W[T;T⁻¹]) : ∃ a b : W[T;T⁻¹], z = θ t ht a / θ t ht b := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := W[T;T⁻¹]) z
  obtain ⟨a₁, b₁, hb₁, h₁⟩ := exists_θ_div t ht x
  obtain ⟨a₂, b₂, hb₂, h₂⟩ := exists_θ_div t ht y
  refine ⟨a₁ * b₂, b₁ * a₂, ?_⟩
  rw [h₁, h₂, map_mul, map_mul]
  have ha₂ : θ t ht a₂ ≠ 0 := by
    intro h
    rw [h, zero_div, map_eq_zero_iff _ (ι_injective (W := W))] at h₂
    exact nonZeroDivisors.ne_zero hy h₂
  field_simp

end chart

theorem mem_range_of_isIntegralElem {L K : Type*} [CommRing L] [IsIntegrallyClosed L] [Field K]
    (θ : L →+* K) (hinj : Function.Injective θ) (hsurj : ∀ z : K, ∃ a b : L, z = θ a / θ b)
    {z : K} (hz : θ.IsIntegralElem z) : z ∈ θ.range := by
  letI : Algebra L K := θ.toAlgebra
  haveI : FaithfulSMul L K := (faithfulSMul_iff_algebraMap_injective L K).mpr hinj
  haveI : IsFractionRing L K := IsFractionRing.of_field L K hsurj
  exact IsIntegrallyClosed.isIntegral_iff.mp hz

theorem isIntegrallyClosed_laurent [IsDomain W] [UniqueFactorizationMonoid W] :
    IsIntegrallyClosed W[T;T⁻¹] := by
  haveI := LaurentPolynomial.uniqueFactorizationMonoid W
  letI : GCDMonoid W[T;T⁻¹] := UniqueFactorizationMonoid.toGCDMonoid _
  infer_instance

section closedIn

variable [IsDomain W]

omit [IsDomain W] in

theorem coeff_toLaurent_mul_single (q : W[X]) (k : ℤ) (s : W) (m : ℤ) :
    (Polynomial.toLaurent q * AddMonoidAlgebra.single k s : W[T;T⁻¹]).coeff m
      = (if 0 ≤ m - k then q.coeff (m - k).toNat else 0) * s := by
  have := AddMonoidAlgebra.coeff_mul_single_eq_coeff_mul (x := Polynomial.toLaurent q) (r := s)
    (m := k) (m₁ := m) (m₂ := m - k) (fun m' _ => by constructor <;> intro h <;> omega)
  refine this.trans ?_
  congr 1
  rw [LaurentPolynomial.coeff_toLaurent]
  split_ifs with h
  · have hm : Nat.castEmbedding (R := ℤ) (m - k).toNat = m - k := Int.toNat_of_nonneg h
    conv_lhs => rw [← hm]
    rw [Finsupp.mapDomain_apply Nat.castEmbedding.injective, Polynomial.toFinsupp_apply]
  · apply Finsupp.mapDomain_notin_range
    rintro ⟨i, hi⟩
    apply h
    rw [← hi]
    exact Int.natCast_nonneg i

theorem dvd_coeff_of_eq (ht : t ≠ 0) (ℓ g : W[T;T⁻¹])
    (h : algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹]) ℓ = θ t ht g) (m : ℤ) (hm : m < 0) :
    t ^ (-m).toNat ∣ ℓ.coeff m := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow g
  have hg : g = Polynomial.toLaurent p * LaurentPolynomial.T (-(n : ℤ)) := by
    rw [hp, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, mul_one]
  have key : ℓ * LaurentPolynomial.C t ^ p.natDegree
      = Polynomial.toLaurent (p.scaleRoots t) * (LaurentPolynomial.C t * LaurentPolynomial.T (-1)) ^ n := by
    apply ι_injective (W := W)
    have hTn : LaurentPolynomial.T (-(n : ℤ)) = (LaurentPolynomial.T (-1) : W[T;T⁻¹]) ^ n := by
      rw [LaurentPolynomial.T_pow, mul_neg_one]
    rw [map_mul, map_pow, h, hg, map_mul, mul_right_comm, θ_toLaurent_mul_pow, hTn, map_pow,
      θ_T_neg_one, ← map_pow, ← map_mul]
  have hL : (ℓ * LaurentPolynomial.C t ^ p.natDegree : W[T;T⁻¹]).coeff m
      = ℓ.coeff m * t ^ p.natDegree := by
    rw [← map_pow, ← LaurentPolynomial.single_eq_C]
    exact AddMonoidAlgebra.coeff_mul_single_zero ℓ _ m
  have hR : (Polynomial.toLaurent (p.scaleRoots t) *
        (LaurentPolynomial.C t * LaurentPolynomial.T (-1)) ^ n : W[T;T⁻¹]).coeff m
      = (if 0 ≤ m + n then (p.scaleRoots t).coeff (m + n).toNat else 0) * t ^ n := by
    rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow, mul_neg_one, ← LaurentPolynomial.single_eq_C_mul_T,
      coeff_toLaurent_mul_single, sub_neg_eq_add]
  have hcoef := congrArg (fun f : W[T;T⁻¹] => f.coeff m) key
  rw [hL, hR] at hcoef
  have htN : (t ^ p.natDegree : W) ≠ 0 := pow_ne_zero _ ht
  split_ifs at hcoef with hmn
  · rw [Polynomial.coeff_scaleRoots] at hcoef
    rcases le_or_gt (m + n).toNat p.natDegree with hi | hi
    · refine ⟨p.coeff (m + n).toNat, mul_right_cancel₀ htN ?_⟩
      rw [hcoef]
      have e : p.natDegree - (m + n).toNat + n = (-m).toNat + p.natDegree := by omega
      rw [mul_assoc, ← pow_add, e, pow_add]
      ring
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul, zero_mul] at hcoef
      rw [(mul_eq_zero.mp hcoef).resolve_right htN]
      exact dvd_zero _
  · rw [zero_mul] at hcoef
    rw [(mul_eq_zero.mp hcoef).resolve_right htN]
    exact dvd_zero _

theorem exists_φ₁_eq_of_isIntegralElem [UniqueFactorizationMonoid W] (ht : t ≠ 0) (ℓ : W[T;T⁻¹])
    (hℓ : (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹]).IsIntegralElem ℓ) : ∃ a, φ₁ t a = ℓ := by
  obtain ⟨p, hp, hpℓ⟩ := hℓ
  have hint : (θ t ht).IsIntegralElem (algebraMap W[T;T⁻¹] (FractionRing W[T;T⁻¹]) ℓ) := by
    refine ⟨p.map (φ₂ t : CrossingQuotient W t →+* W[T;T⁻¹]), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, θ_comp_φ₂, ← Polynomial.hom_eval₂, hpℓ, map_zero]
  haveI := isIntegrallyClosed_laurent (W := W)
  obtain ⟨g, hg⟩ := mem_range_of_isIntegralElem (θ t ht) (θ_injective t ht) (θ_surj t ht) hint
  exact mem_range_φ₁ t ht ℓ (fun m hm => dvd_coeff_of_eq t ht ℓ g hg.symm m hm)

end closedIn

private theorem _root_.SENORMAL.isDomain [IsDomain W] (ht : t ≠ 0) : IsDomain (CrossingQuotient W t) :=
  (φ₁_injective t ht).isDomain (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹])

p2m_export "SENORMAL" "isDomain"
theorem isIntegrallyClosed [IsDomain W] [UniqueFactorizationMonoid W] (ht : t ≠ 0) :
    IsIntegrallyClosed (CrossingQuotient W t) := by
  letI : Algebra (CrossingQuotient W t) W[T;T⁻¹] := (φ₁ t : CrossingQuotient W t →+* W[T;T⁻¹]).toAlgebra
  haveI : FaithfulSMul (CrossingQuotient W t) W[T;T⁻¹] :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (φ₁_injective t ht)
  haveI : IsIntegrallyClosed W[T;T⁻¹] := isIntegrallyClosed_laurent
  haveI : IsIntegrallyClosedIn (CrossingQuotient W t) W[T;T⁻¹] := by
    refine isIntegrallyClosedIn_iff.mpr ⟨φ₁_injective t ht, fun {ℓ} hℓ => ?_⟩
    exact exists_φ₁_eq_of_isIntegralElem t ht ℓ hℓ
  exact IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
    (R := CrossingQuotient W t) (S := W[T;T⁻¹])

end SENORMAL

theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [UniqueFactorizationMonoid W] (t : W) (ht : t ≠ 0) :
    IsDomain (MvPolynomial.CrossingQuotient W t) ∧
      IsIntegrallyClosed (MvPolynomial.CrossingQuotient W t) :=
  ⟨SENORMAL.isDomain t ht, SENORMAL.isIntegrallyClosed t ht⟩

end S_MvPolynomial_CrossingQuotient_isDomain_and_isIntegrallyClosed
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_isDomain_and_isIntegrallyClosed (solution)
