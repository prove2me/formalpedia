-- Prove2me | solution 1 for OAI.QuarticPowerFree.quartic_generic_threshold_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T15:13:09.248638+00:00
-- url     : https://prove2.me/submissions/a6d61b71-0fdb-4c7e-b0ce-eef0717ff510

import Mathlib
import Definitions.Def_OAIB3Qp000

section
-- module Solutions.OAIB3_Qpf.PowerFree_HilbertSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open scoped BigOperators

open scoped BigOperators
open MvPolynomial

theorem mem_weightedMonomials {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ) :
    a ∈ weightedMonomials ω T ↔ monomialWeight ω a ≤ T := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ?_,ha⟩
    intro i
    change a i ≤ ⌊T/ω i⌋₊
    apply Nat.le_floor
    apply (le_div_iff₀ (hω i)).mpr
    have hi := Finset.single_le_sum
      (fun j _ => mul_nonneg (hω j).le (Nat.cast_nonneg (a j))) (Finset.mem_univ i)
    simpa only [mul_comm (a i : ℝ)] using hi.trans ha

end

open scoped BigOperators
open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedHypersurfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open MvPolynomial
open scoped BigOperators

theorem weightedLift_monomial {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) :
    weightedLift w (monomial m r) =
      Polynomial.C (monomial m r) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  simp only [weightedLift, eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, ← map_pow, Finset.prod_mul_distrib,
    ← map_prod]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [monomial_eq, Finsupp.prod]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]

theorem weightedLift_coeff {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) (t : ℕ) :
    (weightedLift w p).coeff t = weightedHomogeneousComponent w t p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [weightedLift_monomial, Polynomial.coeff_C_mul_X_pow]
    ext s
    by_cases hs : m = s
    · subst s
      split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial, eq_comm]
    · split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial]
  | add p q hp hq => simp [map_add, Polynomial.coeff_add, hp, hq]

theorem weightedLift_eval_one {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) : (weightedLift w p).eval 1 = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r => simp [weightedLift_monomial]
  | add p q hp hq => simp [map_add, hp, hq]

theorem weightedLift_injective {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    Function.Injective (weightedLift (R := R) w) := by
  intro p q h
  simpa only [weightedLift_eval_one] using congrArg (Polynomial.eval 1) h

theorem weightedLift_natDegree {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) :
    (weightedLift w p).natDegree = weightedTotalDegree w p := by
  classical
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro t ht
    rw [weightedLift_coeff]
    exact weightedHomogeneousComponent_eq_zero t p ht
  · unfold weightedTotalDegree
    apply Finset.sup_le
    intro m hm
    have hc : (weightedLift w p).coeff (Finsupp.weight w m) ≠ 0 := by
      rw [weightedLift_coeff]
      intro he
      have h := congrArg (fun polynomial => polynomial.coeff m) he
      simp [coeff_weightedHomogeneousComponent, mem_support_iff.mp hm] at h
    exact Polynomial.le_natDegree_of_ne_zero hc

theorem weightedTotalDegree_mul_exact {σ R : Type*} [CommSemiring R] [IsDomain R]
    (w : σ → ℕ) (p q : MvPolynomial σ R) (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedTotalDegree w (p * q) = weightedTotalDegree w p + weightedTotalDegree w q := by
  rw [← weightedLift_natDegree, map_mul, Polynomial.natDegree_mul]
  · rw [weightedLift_natDegree, weightedLift_natDegree]
  · intro h
    apply hp
    apply weightedLift_injective w
    simpa using h
  · intro h
    apply hq
    apply weightedLift_injective w
    simpa using h

theorem weightedSpace_finite {σ K : Type*} [Finite σ] [CommSemiring K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (T : ℕ) :
    Module.Finite K (weightedSpace (K := K) w T) := by
  have := (Finsupp.finite_of_nat_weight_le w hw T).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K _)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_SurfaceCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical

theorem weightedSpace_map_le_weightedFunctions {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (w : Fin n → ℕ) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 < ω i) (L : ℝ) (hL : 0 < L)
    (hw : ∀ i, (w i : ℝ) = L*ω i) (T : ℝ) (hT : 0 ≤ T) :
    (weightedSpace w ⌊L*T⌋₊).map (Ideal.Quotient.mkₐ K I).toLinearMap ≤
      weightedFunctions I ω T := by
  classical
  rintro y ⟨p,hp,rfl⟩
  have hs : ∀ a ∈ p.support, monomialWeight ω a ≤ T := by
    intro a ha
    have hh : Finsupp.weight w a ≤ ⌊L*T⌋₊ :=
      hp ha
    have he : (Finsupp.weight w a : ℝ) = L*monomialWeight ω a := by
      rw [Finsupp.weight_eq_sum]
      simp only [Nat.cast_sum,monomialWeight,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [nsmul_eq_mul,Nat.cast_mul,hw]
      norm_cast
      ring
    have hhN : (Finsupp.weight w a : ℝ) ≤ (⌊L*T⌋₊:ℕ) := by exact_mod_cast hh
    have hh' : (Finsupp.weight w a : ℝ) ≤ L*T :=
      hhN.trans (Nat.floor_le (mul_nonneg hL.le hT))
    rw [he] at hh'
    exact (mul_le_mul_iff_right₀ hL).mp hh'
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  have hm : Ideal.Quotient.mk I (monomial a (1:K)) ∈ weightedFunctions I ω T :=
    Submodule.subset_span ⟨a,(mem_weightedMonomials ω hω T a).mpr (hs a ha),rfl⟩
  have he : monomial a (p.coeff a) = (p.coeff a) • monomial a (1:K) := by
    rw [smul_monomial,smul_eq_mul,mul_one]
  rw [he]
  simpa using (weightedFunctions I ω T).smul_mem (p.coeff a) hm

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial MonomialOrder
open scoped MonomialOrder

theorem pair_ideal_isPrime {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    (Ideal.span (Set.range (pairRelation k q))).IsPrime := by
  rw [pair_ideal_eq_ker k q hq]
  exact RingHom.ker_isPrime _

theorem pairNormalBasis_apply {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0)
    (m : {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) :
    pairNormalBasis k q hq m = Ideal.Quotient.mk _ (monomial m.val 1) := by
  simp only [pairNormalBasis, Module.Basis.map_apply, pairNormalEquiv,
    LinearEquiv.ofBijective_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  congr 1
  ext d
  change (((AddMonoidAlgebra.supportedEquivFinsupp _).symm
    (Finsupp.single m (1:R))) : MvPolynomial (Fin n ⊕ Fin n) R).coeff d = _
  simp only [AddMonoidAlgebra.supportedEquivFinsupp, LinearEquiv.symm_trans_apply]
  change (((Finsupp.supportedEquivFinsupp (R := R) {m | PairNormal k m}).symm
    (Finsupp.single m (1:R))) : (((Fin n ⊕ Fin n) →₀ ℕ) →₀ R)) d = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

theorem aevalTower_monomial_homogeneous {σ K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (L : R →ₐ[K] Polynomial S) (g : σ → S) (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) (e : ℕ) (hr : L r = Polynomial.monomial e (f r)) :
    MvPolynomial.aevalTower L (fun i => Polynomial.monomial (w i) (g i)) (monomial m r) =
      Polynomial.monomial (e + Finsupp.weight w m)
        (MvPolynomial.aevalTower f g (monomial m r)) := by
  classical
  change eval₂ L.toRingHom _ (monomial m r) = Polynomial.monomial _
    (eval₂ f.toRingHom g (monomial m r))
  rw [eval₂_monomial, eval₂_monomial]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [hr]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, Finsupp.prod, mul_pow,
    ← map_pow, Finset.prod_mul_distrib, ← map_prod]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
  have hw : (∑ i ∈ m.support, w i * m i) = Finsupp.weight w m := by
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]
  rw [hw, pow_add, map_mul]
  ring

theorem pairScale_monomial {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i))
    (m : (Fin n ⊕ Fin n) →₀ ℕ) (r : R) (e : ℕ)
    (hr : L r = Polynomial.monomial e r) :
    pairScale k A B q L hq (Ideal.Quotient.mk _ (monomial m r)) =
      Polynomial.monomial (e+Finsupp.weight (Sum.elim (fun _ => A) (fun _ => B)) m)
        (Ideal.Quotient.mk _ (monomial m r)) := by
  change pairScalePre k A B q L (monomial m r) = _
  have hs := aevalTower_monomial_homogeneous (pairCoeffs (K := K) k q)
    ((Polynomial.mapAlgHom (pairCoeffs (K := K) k q)).comp L)
    (fun i : Fin n ⊕ Fin n => Ideal.Quotient.mk _ (X i))
    (Sum.elim (fun _ => A) (fun _ => B)) m r e
    (by simp [hr])
  have he : MvPolynomial.aevalTower (pairCoeffs (K := K) k q)
      (fun i : Fin n ⊕ Fin n => Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mkₐ K _ := by
    apply MvPolynomial.algHom_ext'
    · ext r
      simp [pairCoeffs]
    · intro i
      simp
  simpa only [pairScalePre, he, Ideal.Quotient.mkₐ_eq_mk] using hs

theorem pairNormalBasis_smul {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0)
    (m : {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) (r : R) :
    r • pairNormalBasis k q hq m = Ideal.Quotient.mk _ (monomial m.val r) := by
  rw [pairNormalBasis_apply]
  have hh := map_smul (Ideal.Quotient.mkₐ R (Ideal.span (Set.range (pairRelation k q)))) r
    (monomial m.val 1)
  simpa [MvPolynomial.smul_monomial, smul_eq_mul] using hh.symm

theorem pairBasis_homogeneous {n : ℕ} {ι K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (hnq : ∀ i, q i ≠ 0)
    (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i))
    (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (i : ι × {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}) :
    pairScale k A B q L hq ((b.smulTower (pairNormalBasis k q hnq)) i) =
      Polynomial.monomial (w i.1 +
        Finsupp.weight (Sum.elim (fun _ => A) (fun _ => B)) i.2.val)
        ((b.smulTower (pairNormalBasis k q hnq)) i) := by
  simp only [Module.Basis.smulTower_apply, pairNormalBasis_smul]
  exact pairScale_monomial k A B q L hq i.2.val (b i.1) (w i.1) (hb i.1)

theorem normPair_weightedLift_monomial {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) :
    normPair_weightedLift w (monomial m r) =
      Polynomial.C (monomial m r) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  simp only [normPair_weightedLift, eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, ← map_pow, Finset.prod_mul_distrib,
    ← map_prod]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [monomial_eq, Finsupp.prod]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]

theorem weightedScale_monomial {σ K : Type*} [Field K] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : K) :
    weightedScale w (MvPolynomial.monomial m r) =
      Polynomial.monomial (Finsupp.weight w m) (MvPolynomial.monomial m r) := by
  exact (normPair_weightedLift_monomial w m r).trans Polynomial.C_mul_X_pow_eq_monomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

theorem normPair_finrank_of_exact {K L M N : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K M]
    (g : L →ₗ[K] M) (f : M →ₗ[K] N) (hg : Function.Injective g)
    (he : LinearMap.range g = LinearMap.ker f) :
    Module.finrank K (LinearMap.range f) + Module.finrank K L = Module.finrank K M := by
  rw [← LinearMap.finrank_range_of_inj hg, he]
  exact f.finrank_range_add_finrank_ker

theorem normPair_filtered_principal_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (F G : Submodule K R)
    [Module.Finite K F] (c : R) (hc : c ≠ 0)
    (hdegree : ∀ x : R, c * x ∈ F ↔ x ∈ G) :
    Module.finrank K (F.map (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) +
      Module.finrank K G = Module.finrank K F := by
  let f := (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap.domRestrict F
  let g : G →ₗ[K] F :=
    { toFun := fun x => ⟨c * x.val, (hdegree x.val).mpr x.property⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp }
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact mul_left_cancel₀ hc (congrArg Subtype.val h)
  have he : LinearMap.range g = LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (Ideal.Quotient.mk (Ideal.span {c})) (c * y.val) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton.mpr ⟨y.val, rfl⟩
    · intro hx
      have hmem : x.val ∈ Ideal.span {c} := Ideal.Quotient.eq_zero_iff_mem.mp hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
      refine ⟨⟨y, (hdegree y).mp (hy ▸ x.property)⟩, ?_⟩
      apply Subtype.ext
      exact hy.symm
  have hr : LinearMap.range f = F.map (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact normPair_finrank_of_exact g f hg he

theorem mem_homogeneousSpace {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (T : ℕ) (x : R) :
    x ∈ homogeneousSpace L T ↔ L x = Polynomial.monomial T x := Iff.rfl

theorem homogeneous_principal_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R) (E T : ℕ)
    [Module.Finite K (homogeneousSpace L (E+T))]
    (c : R) (hc : c ≠ 0) (hC : L c = Polynomial.monomial E c) :
    Module.finrank K ((homogeneousSpace L (E+T)).map
      (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) +
      Module.finrank K (homogeneousSpace L T) =
      Module.finrank K (homogeneousSpace L (E+T)) := by
  apply normPair_filtered_principal_finrank _ _ c hc
  intro x
  simp only [mem_homogeneousSpace, map_mul, hC]
  rw [← Polynomial.monomial_mul_monomial]
  have hp : Polynomial.monomial E c ≠ 0 := by simpa using hc
  exact ⟨fun h => mul_left_cancel₀ hp h, fun h => congrArg _ h⟩

open scoped BigOperators

theorem homogeneous_coord {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (x : R) (t : ℕ) (i : ι) :
    b.repr ((L x).coeff t) i = if w i = t then b.repr x i else 0 := by
  classical
  let f := (b.coord i).comp (((Polynomial.lcoeff R t).restrictScalars K).comp L.toLinearMap)
  have hf : f = if w i = t then b.coord i else 0 := by
    apply b.ext
    intro j
    simp only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, Polynomial.lcoeff_apply, hb, Polynomial.coeff_monomial]
    by_cases hij : i = j
    · subst j
      split_ifs <;> simp_all [Module.Basis.coord_apply]
    · have hji : j ≠ i := Ne.symm hij
      split_ifs <;> simp_all [Module.Basis.coord_apply]
  have hh := LinearMap.congr_fun hf x
  by_cases hi : w i = t
  · simpa [f, hi, Module.Basis.coord_apply] using hh
  · simpa [f, hi, Module.Basis.coord_apply] using hh

theorem homogeneousSpace_eq_basis_span {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i)) (T : ℕ) :
    homogeneousSpace L T = Submodule.span K (b '' {i | w i = T}) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [b.mem_span_image]
    intro i hi
    have hc := homogeneous_coord L b w hb x (w i) i
    rw [(mem_homogeneousSpace L T x).mp hx, Polynomial.coeff_monomial] at hc
    simp only [ite_true] at hc
    by_contra hn
    have hn' : w i ≠ T := hn
    rw [ite_eq_right (Ne.symm hn')] at hc
    simp only [map_zero, Finsupp.zero_apply] at hc
    exact (Finsupp.mem_support_iff.mp hi) hc.symm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact (hb i).trans (by rw [hi])

theorem homogeneousSpace_finrank {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i)) (T : ℕ)
    [Fintype {i // w i = T}] :
    Module.finrank K (homogeneousSpace L T) = Fintype.card {i // w i = T} := by
  rw [homogeneousSpace_eq_basis_span L b w hb T]
  have hs : b '' {i | w i = T} = Set.range (fun i : {i // w i = T} => b i.val) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  rw [hs]
  exact finrank_span_eq_card (b.linearIndependent.comp
    (fun i : {i // w i = T} => i.val) Subtype.val_injective)

theorem homogeneousSpace_finite {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i)) (T : ℕ)
    [Finite {i // w i = T}] : Module.Finite K (homogeneousSpace L T) := by
  classical
  rw [homogeneousSpace_eq_basis_span L b w hb T]
  have hs : b '' {i | w i = T} = Set.range (fun i : {i // w i = T} => b i.val) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  rw [hs]
  exact Module.Finite.span_of_finite K (Set.finite_range _)

open scoped BigOperators

private theorem normPair_card_antidiagonalTuple (h N : ℕ) :
    (Finset.Nat.antidiagonalTuple h N).card = h.multichoose N := by
  classical
  have hc := Finset.card_finsuppAntidiag_nat_eq_multichoose
    (s := (Finset.univ : Finset (Fin h))) N
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [← hc]
  apply Finset.card_bij (fun x _ => Finsupp.equivFunOnFinite.symm x)
  · intro x hx
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨by simpa [Finsupp.sum_fintype] using Finset.Nat.mem_antidiagonalTuple.mp hx,
      Finset.subset_univ _⟩
  · intro x _ y _ he
    exact Finsupp.equivFunOnFinite.symm.injective he
  · intro x hx
    refine ⟨Finsupp.equivFunOnFinite x, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [Finsupp.sum_fintype] using (Finset.mem_finsuppAntidiag'.mp hx).1

theorem normPair_card_simplexTuple (h N : ℕ) :
    (normPair_simplexTuple h N).card = (N+h).choose h := by
  classical
  rw [normPair_simplexTuple, Finset.card_biUnion]
  · simp_rw [normPair_card_antidiagonalTuple]
    exact Nat.sum_range_multichoose N h
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.Nat.mem_antidiagonalTuple.mp hi).symm.trans
      (Finset.Nat.mem_antidiagonalTuple.mp hj))

theorem mem_weightedTuple {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i)
    (T : ℕ) (x : Fin h → ℕ) :
    x ∈ weightedTuple w T ↔ ∑ i, w i*x i ≤ T := by
  classical
  simp only [weightedTuple, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hx
    refine ⟨fun i => ?_, hx⟩
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (w j*x j))
      (Finset.mem_univ i)
    have hixi : x i ≤ w i*x i := by nlinarith [hw i]
    omega

private theorem tuple_divmod_injective {h : ℕ} (m : Fin h → ℕ) :
    Function.Injective (fun x => (tupleQuot m x, tupleRem m x)) := by
  intro x y he
  have hq := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  funext i
  have hqi := congrFun hq i
  have hri := congrFun hr i
  dsimp [tupleQuot, tupleRem] at hqi hri
  have hx := Nat.mod_add_div (x i) (m i)
  have hy := Nat.mod_add_div (y i) (m i)
  rw [hqi, hri] at hx
  omega

theorem weightedTuple_upper {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) :
    (weightedTuple w T).card ≤ (normPair_simplexTuple h (T/L)).card * ∏ i, m i := by
  classical
  let R := Fintype.piFinset (fun i => Finset.range (m i))
  let f := fun x => (tupleQuot m x, tupleRem m x)
  have hin (x : Fin h → ℕ) (hx : x ∈ weightedTuple w T) :
      f x ∈ (normPair_simplexTuple h (T/L)) ×ˢ R := by
    apply Finset.mem_product.mpr
    refine ⟨(normPair_mem_simplexTuple _).mpr ?_, ?_⟩
    · apply (Nat.le_div_iff_mul_le hL).mpr
      calc
        (∑ i, tupleQuot m x i)*L = ∑ i, w i*(m i*(x i/m i)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          dsimp [tupleQuot]
          rw [← hprod i]
          ring
        _ ≤ ∑ i, w i*x i := Finset.sum_le_sum (fun i _ =>
          Nat.mul_le_mul_left (w i) (Nat.mul_div_le (x i) (m i)))
        _ ≤ T := (mem_weightedTuple w hw T x).mp hx
    · simp [R, f, tupleRem, Nat.mod_lt _ (hm _)]
  have hc := Finset.card_le_card_of_injOn f hin
    (fun _ _ _ _ he => tuple_divmod_injective m he)
  simpa [R, Finset.card_product, Fintype.card_piFinset] using hc

theorem weightedTuple_lower {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) (hT : h ≤ T/L) :
    (normPair_simplexTuple h (T/L-h)).card * ∏ i, m i ≤ (weightedTuple w T).card := by
  classical
  let R := Fintype.piFinset (fun i => Finset.range (m i))
  let f : (Fin h → ℕ) × (Fin h → ℕ) → (Fin h → ℕ) :=
    fun x i => m i*x.1 i+x.2 i
  have hh (x : (Fin h → ℕ) × (Fin h → ℕ))
      (hx : x ∈ (normPair_simplexTuple h (T/L-h)) ×ˢ R) :
      (∑ i, x.1 i ≤ T/L-h) ∧ ∀ i, x.2 i < m i := by
    rcases Finset.mem_product.mp hx with ⟨hq, hr⟩
    exact ⟨(normPair_mem_simplexTuple _).mp hq, by simpa [R] using hr⟩
  have hin (x : (Fin h → ℕ) × (Fin h → ℕ))
      (hx : x ∈ (normPair_simplexTuple h (T/L-h)) ×ˢ R) : f x ∈ weightedTuple w T := by
    apply (mem_weightedTuple w hw T _).mpr
    obtain ⟨hxq, hxr⟩ := hh x hx
    calc
      (∑ i, w i*(f x i)) = L*(∑ i, x.1 i) + ∑ i, w i*x.2 i := by
        simp only [f, mul_add, ← mul_assoc, hprod, Finset.sum_add_distrib,
          Finset.mul_sum]
      _ ≤ L*(T/L-h) + h*L := by
        apply Nat.add_le_add (Nat.mul_le_mul_left L hxq)
        calc
          ∑ i, w i*x.2 i ≤ ∑ _i : Fin h, L := Finset.sum_le_sum (fun i _ => by
            rw [← hprod i]; exact Nat.mul_le_mul_left _ (hxr i).le)
          _ = h*L := by simp
      _ = L*(T/L) := by rw [Nat.mul_sub_left_distrib, Nat.mul_comm h L,
        Nat.sub_add_cancel (Nat.mul_le_mul_left L hT)]
      _ ≤ T := Nat.mul_div_le T L
  have hi : Set.InjOn f ↑((normPair_simplexTuple h (T/L-h)) ×ˢ R) := by
    intro x hx y hy he
    obtain ⟨_, hxr⟩ := hh x hx
    obtain ⟨_, hyr⟩ := hh y hy
    have hq : x.1 = y.1 := by
      funext i
      have hd := congrArg (fun v => v i / m i) he
      simpa [f, Nat.mul_add_div (hm i), Nat.div_eq_of_lt (hxr i),
        Nat.div_eq_of_lt (hyr i)] using hd
    apply Prod.ext hq
    funext i
    have hd := congrFun he i
    dsimp [f] at hd
    rw [hq] at hd
    omega
  have hc := Finset.card_le_card_of_injOn f hin hi
  simpa [R, Finset.card_product, Fintype.card_piFinset] using hc

theorem simplexTuple_power_bounds (h N : ℕ) :
    N^h ≤ h.factorial*(normPair_simplexTuple h N).card ∧
    h.factorial*(normPair_simplexTuple h N).card ≤ (N+h)^h := by
  rw [normPair_card_simplexTuple, ← Nat.descFactorial_eq_factorial_mul_choose]
  refine ⟨?_, Nat.descFactorial_le_pow _ _⟩
  have he : N+h+1-h = N+1 := by omega
  exact (Nat.pow_le_pow_left (by omega : N ≤ N+1) h).trans
    (he ▸ Nat.pow_sub_le_descFactorial (N+h) h)

theorem prod_weight_comultiples {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hprod : ∀ i, w i*m i = L) :
    (∏ i, w i)*(∏ i, m i) = L^h := by
  rw [← Finset.prod_mul_distrib]
  simp_rw [hprod]
  simp

theorem weightedTuple_power_bounds {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) (hT : h ≤ T/L) :
    (L*(T/L-h))^h ≤ h.factorial*(∏ i, w i)*(weightedTuple w T).card ∧
    h.factorial*(∏ i, w i)*(weightedTuple w T).card ≤ (L*(T/L+h))^h := by
  have hu := weightedTuple_upper w m L hw hm hL hprod T
  have hl := weightedTuple_lower w m L hw hm hprod T hT
  have hpu := (simplexTuple_power_bounds h (T/L)).2
  have hpl := (simplexTuple_power_bounds h (T/L-h)).1
  have hp := prod_weight_comultiples w m L hprod
  constructor
  · calc
      (L*(T/L-h))^h = (∏ i, w i)*(∏ i, m i)*(T/L-h)^h := by rw [mul_pow, hp]
      _ ≤ (∏ i, w i)*(∏ i, m i)*(h.factorial*(normPair_simplexTuple h (T/L-h)).card) :=
        Nat.mul_le_mul_left _ hpl
      _ = (h.factorial*(∏ i, w i))*
          ((normPair_simplexTuple h (T/L-h)).card*(∏ i, m i)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hl
  · calc
      h.factorial*(∏ i, w i)*(weightedTuple w T).card ≤
          h.factorial*(∏ i, w i)*((normPair_simplexTuple h (T/L)).card*(∏ i, m i)) :=
        Nat.mul_le_mul_left _ hu
      _ = (∏ i, w i)*(∏ i, m i)*(h.factorial*(normPair_simplexTuple h (T/L)).card) := by ring
      _ ≤ (∏ i, w i)*(∏ i, m i)*(T/L+h)^h := Nat.mul_le_mul_left _ hpu
      _ = (L*(T/L+h))^h := by rw [mul_pow, hp]

private theorem nearby_power_error (h : ℕ) {x y c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) (hd : |y-x| ≤ c) :
    |y^h-x^h| ≤ c*h*(c+1)^(h-1)*(x+1)^(h-1) := by
  have hmax : max |y| |x| ≤ (c+1)*(x+1) := by
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    apply max_le
    · have hi := (abs_le.mp hd).2
      nlinarith
    · nlinarith
  calc
    |y^h-x^h| ≤ |y-x| * h * max |y| |x| ^ (h-1) := abs_pow_sub_pow_le y x h
    _ ≤ c*h*((c+1)*(x+1))^(h-1) := by gcongr
    _ = c*h*(c+1)^(h-1)*(x+1)^(h-1) := by rw [mul_pow]; ring

theorem weightedTuple_volume_error_with_scale {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, h*L ≤ T →
      |((weightedTuple w T).card : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  let c : ℝ := (h+1:ℕ)*L
  let s : ℝ := (h.factorial*(∏ i, w i) : ℕ)
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos h) (Finset.prod_pos (fun i _ => hw i))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c*h*(c+1)^(h-1)/s, by positivity, fun T hT => ?_⟩
  have hq : h ≤ T/L := (Nat.le_div_iff_mul_le hL).mpr hT
  obtain ⟨hl, hu⟩ := weightedTuple_power_bounds w m L hw hm hL hprod T hq
  have hl' : ((L*(T/L-h):ℕ):ℝ)^h ≤ s*(weightedTuple w T).card := by dsimp [s]; exact_mod_cast hl
  have hu' : s*(weightedTuple w T).card ≤ ((L*(T/L+h):ℕ):ℝ)^h := by dsimp [s]; exact_mod_cast hu
  have hnl : L*(T/L-h) ≤ T := by
    calc L*(T/L-h) ≤ L*(T/L) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
         _ ≤ T := Nat.mul_div_le T L
  have hnr : T < L*(T/L-h)+(h+1)*L := by
    have he : L*(T/L-h)+h*L = L*(T/L) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_comm h L,
        Nat.sub_add_cancel (Nat.mul_le_mul_left L hq)]
    have hr := Nat.mod_lt T hL
    have ht := Nat.mod_add_div T L
    nlinarith
  have hup : L*(T/L+h) ≤ T+(h+1)*L := by
    have ht := Nat.mul_div_le T L
    nlinarith
  have hdown : T ≤ L*(T/L+h)+(h+1)*L := by
    have ht := Nat.mod_add_div T L
    have hr := Nat.mod_lt T hL
    nlinarith
  have hnl' : ((L*(T/L-h):ℕ):ℝ) ≤ (T:ℝ) := by exact_mod_cast hnl
  have hnr' : (T:ℝ) < ((L*(T/L-h):ℕ):ℝ)+c := by dsimp [c]; exact_mod_cast hnr
  have hup' : ((L*(T/L+h):ℕ):ℝ) ≤ (T:ℝ)+c := by dsimp [c]; exact_mod_cast hup
  have hdown' : (T:ℝ) ≤ ((L*(T/L+h):ℕ):ℝ)+c := by dsimp [c]; exact_mod_cast hdown
  have hdl : |((L*(T/L-h):ℕ):ℝ)-(T:ℝ)| ≤ c := by
    apply abs_le.mpr
    constructor <;> linarith
  have hdu : |((L*(T/L+h):ℕ):ℝ)-(T:ℝ)| ≤ c := by
    apply abs_le.mpr
    constructor <;> linarith
  have el := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _) hc hdl
  have eu := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _) hc hdu
  have he : |s*(weightedTuple w T).card-(T:ℝ)^h| ≤
      c*h*(c+1)^(h-1)*((T:ℝ)+1)^(h-1) := by
    apply abs_le.mpr
    have hel := (abs_le.mp el).1
    have heu := (abs_le.mp eu).2
    constructor <;> linarith
  change |(weightedTuple w T).card-(T:ℝ)^h/s| ≤ _
  calc
    |(weightedTuple w T).card-(T:ℝ)^h/s| =
        |s*(weightedTuple w T).card-(T:ℝ)^h|/s := by
      rw [← abs_of_pos hs, ← abs_div]
      congr 1
      rw [abs_of_pos hs]
      field_simp
    _ ≤ (c*h*(c+1)^(h-1)*((T:ℝ)+1)^(h-1))/s :=
      div_le_div_of_nonneg_right he hs.le
    _ = _ := by ring

theorem weightedTuple_volume_error {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((weightedTuple w T).card : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  classical
  let L := ∏ i, w i
  let m := fun i => ∏ j ∈ Finset.univ.erase i, w j
  have hL : 0 < L := Finset.prod_pos (fun i _ => hw i)
  have hm : ∀ i, 0 < m i := fun _ => Finset.prod_pos (fun i _ => hw i)
  have hprod : ∀ i, w i*m i = L := fun i =>
    Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  obtain ⟨C, hC, herror⟩ := weightedTuple_volume_error_with_scale w m L hw hm hL hprod
  let e := fun T : ℕ => |((weightedTuple w T).card : ℝ) -
    (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)|
  let S := ∑ T ∈ Finset.range (h*L), e T
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C+S, by linarith, fun T => ?_⟩
  by_cases ht : h*L ≤ T
  · exact (herror T ht).trans (mul_le_mul_of_nonneg_right (by linarith)
      (by positivity))
  · have he : e T ≤ S := Finset.single_le_sum (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
    have hfactor : 1 ≤ ((T:ℝ)+1)^(h-1) := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
    change e T ≤ _
    calc e T ≤ C+S := by linarith
         _ ≤ (C+S)*((T:ℝ)+1)^(h-1) := le_mul_of_one_le_right (by linarith) hfactor

theorem shiftedTuple_volume_error {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i)
    (e : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |(shiftedTupleCount w e T : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  obtain ⟨C, hC, herror⟩ := weightedTuple_volume_error w hw
  let s : ℝ := (h.factorial*(∏ i, w i) : ℕ)
  let B : ℝ := (e:ℝ)*h*((e:ℝ)+1)^(h-1)/s
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos h) (Finset.prod_pos (fun i _ => hw i))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨C+B+(e:ℝ)^h/s, by positivity, fun T => ?_⟩
  have ht0 : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hf : 1 ≤ ((T:ℝ)+1)^(h-1) := one_le_pow₀ (by linarith)
  by_cases heT : e ≤ T
  · rw [shiftedTupleCount, ite_eq_left heT]
    have hnat : ((T-e:ℕ):ℝ) ≤ (T:ℝ) := by exact_mod_cast Nat.sub_le T e
    have hdiff : |((T-e:ℕ):ℝ)-(T:ℝ)| ≤ (e:ℝ) := by
      rw [Nat.cast_sub heT]
      have : (T:ℝ)-(e:ℝ)-(T:ℝ) = -(e:ℝ) := by ring
      rw [this, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    have he := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _)
      (Nat.cast_nonneg e) hdiff
    have he' : |((T-e:ℕ):ℝ)^h/s-(T:ℝ)^h/s| ≤ B*((T:ℝ)+1)^(h-1) := by
      rw [← sub_div, abs_div, abs_of_pos hs]
      calc
        |((T-e:ℕ):ℝ)^h-(T:ℝ)^h|/s ≤
            ((e:ℝ)*h*((e:ℝ)+1)^(h-1)*((T:ℝ)+1)^(h-1))/s :=
          div_le_div_of_nonneg_right he hs.le
        _ = _ := by dsimp [B]; ring
    have hbase : |((weightedTuple w (T-e)).card : ℝ)-((T-e:ℕ):ℝ)^h/s| ≤
        C*((T:ℝ)+1)^(h-1) := by
      exact (herror (T-e)).trans (by gcongr)
    change |((weightedTuple w (T-e)).card : ℝ)-(T:ℝ)^h/s| ≤ _
    calc
      _ ≤ |((weightedTuple w (T-e)).card : ℝ)-((T-e:ℕ):ℝ)^h/s| +
          |((T-e:ℕ):ℝ)^h/s-(T:ℝ)^h/s| := abs_sub_le _ _ _
      _ ≤ (C+B)*((T:ℝ)+1)^(h-1) := by nlinarith [hbase, he']
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · rw [shiftedTupleCount, ite_eq_right heT, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
    change (T:ℝ)^h/s ≤ _
    have he : (T:ℝ) ≤ (e:ℝ) := by exact_mod_cast (by omega : T ≤ e)
    calc
      (T:ℝ)^h/s ≤ (e:ℝ)^h/s := by gcongr
      _ ≤ C+B+(e:ℝ)^h/s := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hf

theorem sectorPoint_normal {u v : ℕ} (c : PairSector u v) (x : ℕ) :
    (sectorPoint c x).1 < u ∨ (sectorPoint c x).2 < v := by
  cases c with
  | inl r => exact Or.inl r.isLt
  | inr r => exact Or.inr r.isLt

theorem sectorPoint_injective {u v : ℕ} :
    Function.Injective (fun p : PairSector u v × ℕ => sectorPoint p.1 p.2) := by
  rintro ⟨c,x⟩ ⟨d,y⟩ he
  cases c with
  | inl r =>
    cases d with
    | inl s =>
      simp only [sectorPoint, Prod.mk.injEq] at he
      exact Prod.ext (congrArg Sum.inl (Fin.ext he.1)) he.2
    | inr s =>
      have he' := congrArg Prod.fst he
      dsimp [sectorPoint] at he'
      have := r.isLt
      omega
  | inr r =>
    cases d with
    | inl s =>
      have he' := congrArg Prod.fst he
      dsimp [sectorPoint] at he'
      have := s.isLt
      omega
    | inr s =>
      simp only [sectorPoint, Prod.mk.injEq] at he
      exact Prod.ext (congrArg Sum.inr (Fin.ext he.2)) (Nat.add_left_cancel he.1)

theorem sectorPoint_surjective {u v : ℕ} (p : ℕ × ℕ)
    (hp : p.1 < u ∨ p.2 < v) :
    ∃ c : PairSector u v, ∃ x : ℕ, sectorPoint c x = p := by
  by_cases h : p.1 < u
  · exact ⟨Sum.inl ⟨p.1,h⟩, p.2, rfl⟩
  · have h' : p.2 < v := hp.resolve_left h
    refine ⟨Sum.inr ⟨p.2,h'⟩, p.1-u, ?_⟩
    exact Prod.ext (by dsimp [sectorPoint]; omega) rfl

theorem sector_weight_identity (A B : ℕ) {u v : ℕ} (c : PairSector u v) (x : ℕ) :
    A*(sectorPoint c x).1+B*(sectorPoint c x).2 =
      sectorShift A B c + sectorWeight A B c*x := by
  cases c with
  | inl r => rfl
  | inr r => simp only [sectorPoint, sectorShift, sectorWeight]; ring

theorem sectorWeight_pos {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    {u v : ℕ} (c : PairSector u v) : 0 < sectorWeight A B c := by
  cases c <;> assumption

theorem mem_normalPairTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ) (p : Fin h → ℕ × ℕ) :
    p ∈ normalPairTuples A B u v T ↔
      (∀ i, (p i).1 < u i ∨ (p i).2 < v i) ∧
        ∑ i, (A*(p i).1+B*(p i).2) ≤ T := by
  classical
  simp only [normalPairTuples, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hp
    refine ⟨fun i => ?_, hp⟩
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Nat.zero_le (A*(p j).1+B*(p j).2)) (Finset.mem_univ i)
    have ha : (p i).1 ≤ A*(p i).1 := by nlinarith
    have hb : (p i).2 ≤ B*(p i).2 := by nlinarith
    constructor <;> omega

theorem mem_sectorTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ)
    (p : Σ _c : (i : Fin h) → PairSector (u i) (v i), Fin h → ℕ) :
    p ∈ sectorTuples A B u v T ↔
      (∑ i, sectorShift A B (p.1 i)) +
        (∑ i, sectorWeight A B (p.1 i)*p.2 i) ≤ T := by
  classical
  simp only [sectorTuples, Finset.mem_sigma, Finset.mem_univ, true_and]
  split_ifs with ht
  · rw [mem_weightedTuple _ (fun _ => sectorWeight_pos hA hB _)]; omega
  · simp only [Finset.notMem_empty, false_iff]; omega

theorem card_normalPairTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ) :
    (normalPairTuples A B u v T).card =
      ∑ c : (i : Fin h) → PairSector (u i) (v i),
        shiftedTupleCount (fun i => sectorWeight A B (c i))
          (∑ i, sectorShift A B (c i)) T := by
  classical
  have hc : (sectorTuples A B u v T).card = (normalPairTuples A B u v T).card := by
    apply Finset.card_bij (fun p _ => fun i => sectorPoint (p.1 i) (p.2 i))
    · intro p hp
      apply (mem_normalPairTuples hA hB u v T _).mpr
      refine ⟨fun i => sectorPoint_normal _ _, ?_⟩
      simp_rw [sector_weight_identity, Finset.sum_add_distrib]
      exact (mem_sectorTuples hA hB u v T p).mp hp
    · intro p _ q _ hpq
      have he (i : Fin h) : (p.1 i, p.2 i) = (q.1 i, q.2 i) :=
        sectorPoint_injective (congrFun hpq i)
      have hc : p.1 = q.1 := funext (fun i => congrArg Prod.fst (he i))
      have hx : p.2 = q.2 := funext (fun i => congrArg Prod.snd (he i))
      cases p; cases q; dsimp at hc hx; cases hc; cases hx; rfl
    · intro p hp
      obtain ⟨hn, ht⟩ := (mem_normalPairTuples hA hB u v T p).mp hp
      choose c x hx using (fun i => sectorPoint_surjective (p i) (hn i))
      refine ⟨⟨c,x⟩, (mem_sectorTuples hA hB u v T _).mpr ?_, funext hx⟩
      simpa only [← Finset.sum_add_distrib, ← sector_weight_identity, hx] using ht
  rw [← hc]
  simp only [sectorTuples, Finset.card_sigma, shiftedTupleCount]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

theorem normalPairTuples_volume_error {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((normalPairTuples A B u v T).card : ℝ) -
        (T:ℝ)^h * (∑ c : (i : Fin h) → PairSector (u i) (v i),
          1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ))| ≤
        C*((T:ℝ)+1)^(h-1) := by
  classical
  have he (c : (i : Fin h) → PairSector (u i) (v i)) :=
    shiftedTuple_volume_error (fun i => sectorWeight A B (c i))
      (fun _ => sectorWeight_pos hA hB _) (∑ i, sectorShift A B (c i))
  choose C hC herr using he
  refine ⟨∑ c, C c, Finset.sum_nonneg (fun c _ => hC c), fun T => ?_⟩
  rw [card_normalPairTuples hA hB, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, |(shiftedTupleCount (fun i => sectorWeight A B (c i))
        (∑ i, sectorShift A B (c i)) T : ℝ) -
        (T:ℝ)^h*(1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, C c*((T:ℝ)+1)^(h-1) := Finset.sum_le_sum (fun c _ => by
      simpa only [mul_one_div] using herr c T)
    _ = _ := by rw [Finset.sum_mul]

private theorem sector_reciprocal_sum (A B u v : ℕ) :
    (∑ c : PairSector u v, 1/(sectorWeight A B c : ℝ)) = (u:ℝ)/B+(v:ℝ)/A := by
  change (∑ c : Fin u ⊕ Fin v, 1/(sectorWeight A B c : ℝ)) = _
  rw [Fintype.sum_sum_type]
  simp [sectorWeight, nsmul_eq_mul, div_eq_mul_inv]

private theorem sector_coefficient {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    (∑ c : (i : Fin h) → PairSector (u i) (v i),
      1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ)) =
      (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)) /
        ((h.factorial:ℝ)*(A:ℝ)^h*(B:ℝ)^h) := by
  classical
  have ha : (A:ℝ) ≠ 0 := by positivity
  have hb : (B:ℝ) ≠ 0 := by positivity
  calc
    _ = (∑ c : (i : Fin h) → PairSector (u i) (v i),
        ∏ i, 1/(sectorWeight A B (c i) : ℝ))/(h.factorial:ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      simp [Nat.cast_mul, Nat.cast_prod, div_eq_mul_inv, Finset.prod_inv_distrib, mul_comm]
    _ = (∏ i, ∑ c : PairSector (u i) (v i),
        1/(sectorWeight A B c : ℝ))/(h.factorial:ℝ) := by
      rw [Fintype.prod_sum]
    _ = (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)/((A:ℝ)*B))/(h.factorial:ℝ) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [sector_reciprocal_sum]
      field_simp
    _ = _ := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
      rw [div_div]
      congr 1
      ring

theorem normalPairTuples_hilbert_error {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((normalPairTuples A B u v T).card : ℝ) -
        (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)) /
          ((h.factorial:ℝ)*(A:ℝ)^h*(B:ℝ)^h)*(T:ℝ)^h| ≤
        C*((T:ℝ)+1)^(h-1) := by
  obtain ⟨C,hC,herror⟩ := normalPairTuples_volume_error hA hB u v
  refine ⟨C,hC,fun T => ?_⟩
  simpa only [sector_coefficient hA hB, mul_comm] using herror T

theorem pairTranslate_weight {h : ℕ} (A B u v : ℕ) (p : Fin (h+1) → ℕ × ℕ) :
    ∑ i, (A*(pairTranslate u v p i).1+B*(pairTranslate u v p i).2) =
      (∑ i, (A*(p i).1+B*(p i).2)) + A*u+B*v := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [pairTranslate, Fin.cons_zero, Fin.cons_succ]
  ring

theorem pairTranslate_injective {h : ℕ} (u v : ℕ) :
    Function.Injective (pairTranslate (h := h) u v) := by
  intro p q he
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h0 := congrFun he 0
    simp only [pairTranslate, Fin.cons_zero, Prod.mk.injEq] at h0
    exact Prod.ext (Nat.add_right_cancel h0.1) (Nat.add_right_cancel h0.2)
  · exact congrFun he j.succ

theorem ambientPairTuples_card_cut {h A B k T : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : ℕ) :
    (ambientPairTuples h A B k T).card =
      (normalPairTuples A B (Fin.cons u (fun _ : Fin h => k))
        (Fin.cons v (fun _ : Fin h => 1)) T).card +
      if A*u+B*v ≤ T then (ambientPairTuples h A B k (T-(A*u+B*v))).card else 0 := by
  classical
  let s := ambientPairTuples h A B k T
  let P := fun p : Fin (h+1) → ℕ × ℕ => u ≤ (p 0).1 ∧ v ≤ (p 0).2
  have hn : s.filter (fun p => ¬ P p) =
      normalPairTuples A B (Fin.cons u (fun _ : Fin h => k))
        (Fin.cons v (fun _ : Fin h => 1)) T := by
    ext p
    rw [Finset.mem_filter, mem_normalPairTuples hA hB]
    change (p ∈ ambientPairTuples h A B k T ∧ _) ↔ _
    rw [mem_ambientPairTuples hA hB]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Nat.lt_one_iff]
    dsimp [P]
    simp only [not_and_or, not_le]
    tauto
  have hr : (s.filter P).card =
      if A*u+B*v ≤ T then (ambientPairTuples h A B k (T-(A*u+B*v))).card else 0 := by
    by_cases he : A*u+B*v ≤ T
    · rw [ite_eq_left he]
      symm
      apply Finset.card_bij (fun p _ => pairTranslate u v p)
      · intro p hp
        obtain ⟨hpN,hpT⟩ := (mem_ambientPairTuples hA hB p).mp hp
        apply Finset.mem_filter.mpr
        constructor
        · apply (mem_ambientPairTuples hA hB _).mpr
          refine ⟨by simpa only [pairTranslate, Fin.cons_succ] using hpN, ?_⟩
          rw [pairTranslate_weight]
          omega
        · simp only [P, pairTranslate, Fin.cons_zero]
          exact ⟨Nat.le_add_left _ _, Nat.le_add_left _ _⟩
      · intro p _ q _ heq
        exact pairTranslate_injective u v heq
      · intro p hp
        obtain ⟨hpS,hpP⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpN,hpT⟩ := (mem_ambientPairTuples hA hB p).mp hpS
        let q : Fin (h+1) → ℕ × ℕ := Fin.cons ((p 0).1-u,(p 0).2-v) (fun i : Fin h => p i.succ)
        have hqp : pairTranslate u v q = p := by
          funext i
          refine Fin.cases ?_ (fun _ => rfl) i
          exact Prod.ext (Nat.sub_add_cancel hpP.1) (Nat.sub_add_cancel hpP.2)
        refine ⟨q, (mem_ambientPairTuples hA hB q).mpr ⟨?_,?_⟩, hqp⟩
        · simpa only [q, Fin.cons_succ] using hpN
        · have hw := pairTranslate_weight A B u v q
          rw [hqp] at hw
          omega
    · rw [ite_eq_right he, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpS,hpP⟩ := Finset.mem_filter.mp hp
      obtain ⟨_,hpT⟩ := (mem_ambientPairTuples hA hB p).mp hpS
      have h0 := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
        Nat.zero_le (A*(p i).1+B*(p i).2)) (Finset.mem_univ (0 : Fin (h+1)))
      have hA' := Nat.mul_le_mul_left A hpP.1
      have hB' := Nat.mul_le_mul_left B hpP.2
      omega
  have hc := Finset.card_filter_add_card_filter_not (s := s) P
  rw [hn, hr] at hc
  exact hc.symm.trans (Nat.add_comm _ _)

theorem pairFilteredDifference_hilbert_error {h A B k : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((ambientPairTuples h A B k T).card -
          (if A*u+B*v ≤ T then (ambientPairTuples h A B k (T-(A*u+B*v))).card else 0) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
          (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+1)| ≤
        C*((T:ℝ)+1)^h := by
  obtain ⟨C,hC,herror⟩ := normalPairTuples_hilbert_error hA hB
    (Fin.cons u (fun _ : Fin h => k)) (Fin.cons v (fun _ : Fin h => 1))
  refine ⟨C,hC,fun T => ?_⟩
  have hc := ambientPairTuples_card_cut (h := h) (k := k) (T := T) hA hB u v
  have hc' : ((ambientPairTuples h A B k T).card:ℝ) -
      (if A*u+B*v ≤ T then ((ambientPairTuples h A B k (T-(A*u+B*v))).card:ℝ) else 0) =
      ((normalPairTuples A B (Fin.cons u (fun _ : Fin h => k))
        (Fin.cons v (fun _ : Fin h => 1)) T).card : ℝ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) hc
    push_cast at hh
    linarith
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [hc']
  have hp : (∏ i : Fin (h+1),
      (((Fin.cons (α := fun _ : Fin (h+1) => ℕ) u (fun _ : Fin h => k) i) : ℝ)*A+
        ((Fin.cons (α := fun _ : Fin (h+1) => ℕ) v (fun _ : Fin h => 1) i) : ℝ)*B)) =
      ((A*u+B*v:ℕ):ℝ)*((k*A+B:ℕ):ℝ)^h := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_one, one_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_mul]
    ring
  simpa only [hp, Nat.add_sub_cancel] using herror T

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open scoped BigOperators

theorem pairConeBasis_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (i : PairBasisIndex n k) :
    pairConeScale k A B θ (pairConeBasis k A B hB θ i) =
      Polynomial.monomial (pairBasisWeight A B i) (pairConeBasis k A B hB θ i) := by
  apply pairBasis_homogeneous
  intro m
  exact weightedScale_monomial (triplePairWeights A B) m 1

theorem pairCone_finite {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K) (T : ℕ) :
    Module.Finite K (homogeneousSpace (pairConeScale k A B θ) T) := by
  classical
  let := Fintype.ofEquiv _ (pairBasisWeightEquiv (n := n) (k := k) hA hB T).symm
  exact homogeneousSpace_finite _ (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) T

theorem pairCone_finrank {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K) (T : ℕ) :
    Module.finrank K (homogeneousSpace (pairConeScale k A B θ) T) =
      (ambientPairTuples n A B k T).card := by
  classical
  let := Fintype.ofEquiv _ (pairBasisWeightEquiv (n := n) (k := k) hA hB T).symm
  rw [homogeneousSpace_finrank _ (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) T]
  exact (Fintype.card_congr (pairBasisWeightEquiv hA hB T)).trans (Fintype.card_coe _)

open MvPolynomial

theorem pairMap_eq_zero_iff_dvd {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (k : ℕ) (q : Fin n → R) (f : R →+* S)
    (hq : ∀ i, q i ≠ 0) (hFq : ∀ i, f (q i) ≠ 0)
    (t : R) (ht : ∀ r, f r = 0 ↔ t ∣ r) (x : PairRing k q) :
    pairMap k q f x = 0 ↔ pairCoeffMap k q t ∣ x := by
  classical
  obtain ⟨p,hp⟩ := (pair_normal_quotient_bijective k q hq).2 x
  change Ideal.Quotient.mk _ p.val = x at hp
  subst x
  constructor
  · intro hx
    have hn : ∀ m ∈ (MvPolynomial.map f p.val).support, PairNormal k m :=
      fun m hm => p.property (MvPolynomial.support_map_subset _ _ hm)
    have hz : MvPolynomial.map f p.val = 0 := by
      apply pairLaurentMap_normal_injective k (fun i => f (q i)) hFq _ hn
      have hh : MvPolynomial.map f p.val ∈
          Ideal.span (Set.range (pairRelation k (fun i => f (q i)))) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hx
      rwa [pair_ideal_eq_ker k _ hFq] at hh
    obtain ⟨r,hr⟩ := (MvPolynomial.C_dvd_iff_map_hom_eq_zero f t ht p.val).mpr hz
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    change Ideal.Quotient.mk _ p.val =
      Ideal.Quotient.mk _ (C t) * Ideal.Quotient.mk _ r
    rw [← map_mul, hr]
  · rintro ⟨r,hr⟩
    rw [hr, map_mul]
    have hft : f t = 0 := (ht t).mpr dvd_rfl
    suffices pairMap k q f (pairCoeffMap k q t) = 0 by rw [this, zero_mul]
    change Ideal.Quotient.mk _ (MvPolynomial.map f (C t)) = 0
    simp [hft]

theorem pairCoeff_span_isPrime {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (k : ℕ) (q : Fin n → R) (f : R →+* S)
    (hq : ∀ i, q i ≠ 0) (hFq : ∀ i, f (q i) ≠ 0)
    (t : R) (ht : ∀ r, f r = 0 ↔ t ∣ r) :
    (Ideal.span {pairCoeffMap k q t}).IsPrime := by
  let : (Ideal.span (Set.range (pairRelation k (fun i => f (q i))))).IsPrime :=
    pair_ideal_isPrime k _ hFq
  have he : Ideal.span {pairCoeffMap k q t} = RingHom.ker (pairMap k q f) := by
    ext x
    simp only [Ideal.mem_span_singleton, RingHom.mem_ker]
    exact (pairMap_eq_zero_iff_dvd k q f hq hFq t ht x).symm
  rw [he]
  exact RingHom.ker_isPrime _

theorem pairCoeffMap_injective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Function.Injective (pairCoeffMap k q) := by
  intro r s h
  have hm : C (r-s) ∈ Ideal.span (Set.range (pairRelation k q)) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change pairCoeffMap k q (r-s) = 0
    rw [map_sub,h,sub_self]
  rw [pair_ideal_eq_ker k q hq] at hm
  have hh : pairLaurentMap k q (C (r-s)) = 0 := hm
  simpa [pairLaurentMap, AddMonoidAlgebra.single_eq_zero, sub_eq_zero] using hh

open Classical

theorem X_dvd_sub_eraseVariable {σ R : Type*} [CommRing R]
    (i : σ) (p : MvPolynomial σ R) : X i ∣ p - eraseVariable i p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hp hq
  | mul_X p j hp =>
    rw [map_mul, eraseVariable_X]
    by_cases hj : j = i
    · simp only [hj, ite_true, mul_zero, sub_zero]
      exact dvd_mul_left _ _
    · simpa only [ite_eq_right hj, ← sub_mul] using dvd_mul_of_dvd_left hp (X j)

theorem eraseVariable_eq_zero_iff {σ R : Type*} [CommRing R]
    (i : σ) (p : MvPolynomial σ R) : eraseVariable i p = 0 ↔ X i ∣ p := by
  classical
  constructor
  · intro h
    simpa [h] using X_dvd_sub_eraseVariable i p
  · rintro ⟨r,rfl⟩
    simp

theorem dvd_of_dvd_prime_mul {R : Type*} [CommRing R] [IsDomain R]
    {a c x : R} (ha : Prime a) (hc : ¬ a ∣ c) (h : c ∣ a * x) : c ∣ x := by
  obtain ⟨y, hy⟩ := h
  have hay : a ∣ y := (ha.dvd_or_dvd (show a ∣ c * y by rw [← hy]; exact dvd_mul_right _ _)).resolve_left hc
  obtain ⟨z, rfl⟩ := hay
  refine ⟨z, ?_⟩
  apply mul_left_cancel₀ ha.ne_zero
  calc
    a * x = c * (a * z) := hy
    _ = a * (c * z) := by ring

theorem dvd_of_dvd_coordinate_mul {R : Type*} [CommRing R] [IsDomain R]
    (s : Set R) {c x a : R} (hp : ∀ a ∈ s, Prime a)
    (hc : ∀ a ∈ s, ¬ a ∣ c) (ha : a ∈ Submonoid.closure s) (h : c ∣ a * x) :
    c ∣ x := by
  suffices hh : ∀ x, c ∣ a * x → c ∣ x from hh x h
  clear h x
  induction ha using Submonoid.closure_induction with
  | mem a ha => exact fun _ h => dvd_of_dvd_prime_mul (hp _ ha) (hc _ ha) h
  | one => simp
  | mul a b ha hb ihA ihB =>
    intro x h
    exact ihB x (ihA (b * x) (by simpa [mul_assoc] using h))

theorem principal_under_map_coordinates {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (s : Set R) [IsLocalization (Submonoid.closure s) S]
    (c : R) (hp : ∀ a ∈ s, Prime a) (hc : ∀ a ∈ s, ¬ a ∣ c) :
    Ideal.comap (algebraMap R S) ((Ideal.span {c}).map (algebraMap R S)) =
      Ideal.span {c} := by
  ext x
  rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.closure s), Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact dvd_of_dvd_coordinate_mul s hp hc ha (Ideal.mem_span_singleton.mp hax)
  · intro h
    exact ⟨1, (Submonoid.closure s).one_mem, by simpa [Ideal.mem_span_singleton] using h⟩

theorem principal_isPrime_of_localization_coordinates {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (s : Set R) [IsLocalization (Submonoid.closure s) S]
    (c : R) (hp : ∀ a ∈ s, Prime a) (hc : ∀ a ∈ s, ¬ a ∣ c)
    (hlocal : ((Ideal.span {c}).map (algebraMap R S)).IsPrime) :
    (Ideal.span {c}).IsPrime := by
  rw [← principal_under_map_coordinates (S := S) s c hp hc]
  have : ((Ideal.span {c}).map (algebraMap R S)).IsPrime := hlocal
  exact Ideal.comap_isPrime _ _

theorem principal_saturated_power {R : Type*} [CommRing R] [IsDomain R]
    {c t x : R} (ht : Prime t) (hc : ¬ t ∣ c) (n : ℕ) (h : c ∣ t ^ n * x) : c ∣ x := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply dvd_of_dvd_prime_mul ht hc
    simpa [pow_succ, mul_comm t, mul_assoc] using h

theorem saturated_quotient_localization_injective {R : Type*} [CommRing R] [IsDomain R]
    {c t : R} (ht : Prime t) (hc : ¬ t ∣ c) :
    Function.Injective (algebraMap (R ⧸ Ideal.span {c})
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) t))) := by
  apply IsLocalization.injective (M := Submonoid.powers (Ideal.Quotient.mk (Ideal.span {c}) t))
  rintro s ⟨n, rfl⟩
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply principal_saturated_power ht hc n
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul, map_pow] using hx

theorem homogeneous_dehomogenization_kernel {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {c t x : R} {E T : ℕ} (ht : Prime t) (hc : ¬ t ∣ c)
    (hT : L t = Polynomial.monomial 1 t)
    (hC : L c = Polynomial.monomial E c)
    (hX : L x = Polynomial.monomial T x) :
    x ∈ Ideal.span {c} ⊔ Ideal.span {t-1} ↔ x ∈ Ideal.span {c} := by
  constructor
  · intro hx
    let Q := R ⧸ Ideal.span {c}
    let S := Localization.Away (Ideal.Quotient.mk (Ideal.span {c}) t)
    let q : R →+* Q := Ideal.Quotient.mk (Ideal.span {c})
    let a : R →+* S := (algebraMap Q S).comp q
    let z : S := IsLocalization.Away.invSelf (q t)
    let ev : R →+* S := (Polynomial.eval₂RingHom a z).comp L.toRingHom
    have hq : q c = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have hevC : ev c = 0 := by
      change Polynomial.eval₂ a z (L c) = 0
      rw [hC, Polynomial.eval₂_monomial]
      have ha : a c = 0 := by change (algebraMap Q S) (q c) = 0; simp [hq]
      simp [ha]
    have hevT : ev (t-1) = 0 := by
      rw [map_sub, map_one, sub_eq_zero]
      change Polynomial.eval₂ a z (L t) = 1
      rw [hT, Polynomial.eval₂_monomial, pow_one]
      exact IsLocalization.Away.mul_invSelf (q t)
    have hker : Ideal.span {c} ⊔ Ideal.span {t-1} ≤ RingHom.ker ev := by
      apply sup_le
      · exact Ideal.span_le.mpr (by rintro _ rfl; exact hevC)
      · exact Ideal.span_le.mpr (by rintro _ rfl; exact hevT)
    have hh : a x * z^T = 0 := by
      have h := hker hx
      change Polynomial.eval₂ a z (L x) = 0 at h
      rwa [hX, Polynomial.eval₂_monomial] at h
    have hz : a t * z = 1 := IsLocalization.Away.mul_invSelf (q t)
    have ha : a x = 0 := by
      have he := congrArg (fun y : S => y * (a t)^T) hh
      have hz' : z*a t = 1 := by rwa [mul_comm] at hz
      simpa only [mul_assoc, ← mul_pow, hz', one_pow, mul_one, zero_mul] using he
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply saturated_quotient_localization_injective ht hc
    change a x = (algebraMap Q S) 0
    simpa using ha
  · intro hx
    exact (show Ideal.span {c} ≤ Ideal.span {c} ⊔ Ideal.span {t-1} from le_sup_left) hx

theorem homogeneous_dehomogenization_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {c t : R} {E T : ℕ} [Module.Finite K (homogeneousSpace L T)]
    (ht : Prime t) (hc : ¬ t ∣ c)
    (hT : L t = Polynomial.monomial 1 t)
    (hC : L c = Polynomial.monomial E c) :
    Module.finrank K ((homogeneousSpace L T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {c} ⊔ Ideal.span {t-1})).toLinearMap) =
    Module.finrank K ((homogeneousSpace L T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) := by
  let F := homogeneousSpace L T
  let f := (Ideal.Quotient.mkₐ K (Ideal.span {c} ⊔ Ideal.span {t-1})).toLinearMap.domRestrict F
  let g := (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap.domRestrict F
  have he : LinearMap.ker f = LinearMap.ker g := by
    ext x
    change Ideal.Quotient.mk _ x.val = 0 ↔ Ideal.Quotient.mk _ x.val = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem]
    exact homogeneous_dehomogenization_kernel L ht hc hT hC x.property
  have h := f.finrank_range_add_finrank_ker.trans g.finrank_range_add_finrank_ker.symm
  rw [he] at h
  have hh := Nat.add_right_cancel h
  change Module.finrank K (LinearMap.range ((Ideal.Quotient.mkₐ K
    (Ideal.span {c} ⊔ Ideal.span {t-1})).toLinearMap.domRestrict F)) =
    Module.finrank K (LinearMap.range ((Ideal.Quotient.mkₐ K
      (Ideal.span {c})).toLinearMap.domRestrict F)) at hh
  rw [LinearMap.range_domRestrict, LinearMap.range_domRestrict] at hh
  exact hh

theorem pairCone_t_prime {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) :
    Prime (pairCoeffMap k (pairConeQ k A B θ) (X 2)) := by
  have hq := pairConeQ_ne_zero k A B hB θ
  have hQ : k*A+B ≠ 0 := by omega
  have hf : ∀ i, eraseVariable (R := K) (2 : Fin 3) (pairConeQ k A B θ i) ≠ 0 := by
    intro i
    simp only [pairConeQ, map_add, map_mul, map_pow, eraseVariable_X,
      eraseVariable_C, show (0:Fin 3) ≠ 2 by decide, show (1:Fin 3) ≠ 2 by decide,
      ite_false, ite_true, zero_pow hQ, mul_zero, add_zero]
    exact mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) (X_ne_zero _)
  have ht : pairCoeffMap k (pairConeQ k A B θ) (X 2) ≠ 0 := by
    intro hz
    exact X_ne_zero (R := K) (2 : Fin 3)
      ((pairCoeffMap_injective k _ hq) (hz.trans (map_zero _).symm))
  apply (Ideal.span_singleton_prime ht).mp
  exact pairCoeff_span_isPrime k _ (eraseVariable (R := K) (2:Fin 3)) hq hf (X 2)
    (eraseVariable_eq_zero_iff _)

theorem pairScale_coeff {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i)) (r : R) :
    pairScale k A B q L hq (pairCoeffMap k q r) =
      Polynomial.map (pairCoeffMap k q) (L r) := by
  change pairScalePre k A B q L (C r) = _
  simp only [pairScalePre, MvPolynomial.aevalTower_C, AlgHom.comp_apply]
  rfl

theorem pairCone_t_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :
    pairConeScale k A B θ (pairCoeffMap k (pairConeQ k A B θ) (X 2)) =
      Polynomial.monomial 1 (pairCoeffMap k (pairConeQ k A B θ) (X 2)) := by
  simp only [pairConeScale, pairScale_coeff, weightedScale_X, triplePairWeights,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Polynomial.map_monomial]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_HomogeneousLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

theorem basis_homogeneous_lift {ι K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (t : R) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1) (r : R) :
    ∃ D : ℕ, ∃ c : R, L c = Polynomial.monomial D c ∧ φ c = φ r := by
  classical
  let s := (b.repr r).support
  let D := s.sup w
  let c := ∑ i ∈ s, (b.repr r i) • (b i * t^(D-w i))
  have hw : ∀ i ∈ s, w i ≤ D := fun i hi => Finset.le_sup hi
  refine ⟨D,c,?_,?_⟩
  · dsimp only [c]
    simp only [map_sum,map_smul,map_mul,map_pow,hb,ht]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.monomial_pow,one_mul,Polynomial.monomial_mul_monomial,
      Nat.add_sub_of_le (hw i hi),Polynomial.smul_monomial]
  · dsimp only [c]
    simp only [map_sum,map_smul,map_mul,map_pow,hφ,one_pow,mul_one]
    simpa only [s,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul] using congrArg φ (b.linearCombination_repr r)

theorem homogeneous_division {K R : Type*} [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] (L : R →ₐ[K] Polynomial R) {a x : R} {E D : ℕ}
    (ha : a ≠ 0) (hA : L a = Polynomial.monomial E a)
    (hD : L (a*x) = Polynomial.monomial D (a*x)) (hED : E ≤ D) :
    L x = Polynomial.monomial (D-E) x := by
  have he : Polynomial.monomial E a * L x =
      Polynomial.monomial E a * Polynomial.monomial (D-E) x := by
    rw [Polynomial.monomial_mul_monomial,Nat.add_sub_of_le hED,← hD,map_mul,hA]
  exact mul_left_cancel₀ (by simpa using ha) he

end

section

theorem minimal_homogeneous_lift {ι K R S : Type*} [Field K] [CommRing R]
    [IsDomain R] [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (t : R) (ht0 : t ≠ 0) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1) (r : R) (hr : φ r ≠ 0) :
    ∃ D : ℕ, ∃ c : R, L c = Polynomial.monomial D c ∧
      φ c = φ r ∧ c ≠ 0 ∧ ¬ t ∣ c := by
  classical
  have hex := basis_homogeneous_lift L b w hb t ht φ hφ r
  let D := Nat.find hex
  obtain ⟨c,hc,hcr⟩ := Nat.find_spec hex
  have hc0 : c ≠ 0 := by
    intro h
    apply hr
    rw [← hcr,h,map_zero]
  refine ⟨D,c,hc,hcr,hc0,?_⟩
  rintro ⟨x,hx⟩
  have hDpos : 0 < D := by
    by_contra h
    have hD : D = 0 := by omega
    have he := congrArg (fun p : Polynomial R => p.coeff 0) hc
    change (L c).coeff 0 = (Polynomial.monomial D c).coeff 0 at he
    have hzero : (L c).coeff 0 = 0 := by
      rw [hx,map_mul,ht]
      simp [Polynomial.mul_coeff_zero]
    have he' : (0 : R) = c := by simpa only [hD,hzero,Polynomial.coeff_monomial_same] using he
    exact hc0 he'.symm
  have hdegree : L x = Polynomial.monomial (D-1) x :=
    homogeneous_division L ht0 ht (hx ▸ hc) hDpos
  have hxr : φ x = φ r := by
    rw [hx,map_mul,hφ,one_mul] at hcr
    exact hcr
  have hh : D ≤ D-1 := Nat.find_min' hex ⟨x,hdegree,hxr⟩
  omega

open scoped BigOperators

theorem pairCone_t_dvd_basis {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (i : PairBasisIndex n k)
    (hi : 0 < i.1 2) :
    pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣
      pairConeBasis k A B hB θ i := by
  have hd : (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K) ∣
      MvPolynomial.monomial i.1 1 := MvPolynomial.X_dvd_monomial.mpr (Or.inr (Nat.ne_of_gt hi))
  obtain ⟨v,hv⟩ := hd
  refine ⟨Ideal.Quotient.mk _ (MvPolynomial.monomial i.2.val v), ?_⟩
  simp only [pairConeBasis, Module.Basis.smulTower_apply, pairNormalBasis_smul]
  change Ideal.Quotient.mk _ (MvPolynomial.monomial i.2.val (MvPolynomial.monomial i.1 (1 : K))) = _
  rw [hv]
  change _ = Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) K)) * _
  rw [← map_mul,MvPolynomial.C_mul_monomial]

theorem pairCone_homogeneous_degree {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (c : PairCone k A B θ) (D : ℕ)
    (hC : pairConeScale k A B θ c = Polynomial.monomial D c)
    (hinfty : ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c) :
    ∃ u v : ℕ, D = A*u+B*v := by
  classical
  let b := pairConeBasis k A B hB θ
  let t := pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)
  have hi : ∃ i, b.repr c i ≠ 0 ∧ ¬ t ∣ b i := by
    by_contra! hh
    apply hinfty
    rw [← b.linearCombination_repr c,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Finset.dvd_sum
    intro i hi
    obtain ⟨v,hv⟩ := hh i (Finsupp.mem_support_iff.mp hi)
    refine ⟨(b.repr c) i • v, ?_⟩
    rw [hv,mul_smul_comm]
  obtain ⟨i,hi,hnd⟩ := hi
  have ht0 : i.1 2 = 0 := by
    by_contra hh
    exact hnd (pairCone_t_dvd_basis k A B hB θ i (Nat.pos_of_ne_zero hh))
  have hw : pairBasisWeight A B i = D := by
    have hc := homogeneous_coord (pairConeScale k A B θ) b (pairBasisWeight A B)
      (pairConeBasis_homogeneous k A B hB θ) c D i
    rw [hC,Polynomial.coeff_monomial_same] at hc
    by_contra hh
    simp only [hh,ite_false] at hc
    exact hi hc
  refine ⟨∑ j, (pairIndexToTuple i j).1, ∑ j, (pairIndexToTuple i j).2, ?_⟩
  rw [← hw,pairBasisWeight_eq,ht0,zero_add,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.mul_sum]

theorem pairCone_minimal_lift {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (r : PairCone k A B θ)
    (hr : Ideal.Quotient.mk
      (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ≠ 0) :
    ∃ u v : ℕ, ∃ c : PairCone k A B θ,
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c ∧
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) c =
      Ideal.Quotient.mk
        (Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1}) r ∧
      c ≠ 0 ∧ ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c := by
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  let t := pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)
  let I : Ideal (PairCone k A B θ) := Ideal.span {t-1}
  let φ : PairCone k A B θ →ₐ[K] (PairCone k A B θ) ⧸ I := Ideal.Quotient.mkₐ K I
  have ht : φ t = 1 := by
    have h : φ (t-1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_sub,map_one,sub_eq_zero] using h
  obtain ⟨D,c,hc,hcr,hc0,hct⟩ := minimal_homogeneous_lift (K := K)
    (R := PairCone k A B θ) (S := (PairCone k A B θ) ⧸ I)
    (pairConeScale k A B θ) (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) t (pairCone_t_prime k A B hB θ).ne_zero
    (pairCone_t_homogeneous k A B θ) φ ht r (show φ r ≠ 0 from hr)
  obtain ⟨u,v,hD⟩ := pairCone_homogeneous_degree k A B hB θ c D hc hct
  exact ⟨u,v,c,hD ▸ hc,hcr,hc0,hct⟩

end

theorem connected_homogeneous_isUnit {ι K R : Type*} [Field K] [CommRing R]
    [Algebra K R] (L : R →ₐ[K] Polynomial R)
    (b : Module.Basis ι K R) (w : ι → ℕ) (i0 : ι)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (hw : ∀ i, w i = 0 → i = i0) (hb0 : b i0 = 1)
    (c : R) (hc : L c = Polynomial.monomial 0 c) (hc0 : c ≠ 0) : IsUnit c := by
  classical
  have hs : b.repr c = Finsupp.single i0 (b.repr c i0) := by
    ext i
    by_cases hi : i = i0
    · subst i
      simp
    · have hw0 : w i ≠ 0 := fun h => hi (hw i h)
      have hh := homogeneous_coord L b w hb c 0 i
      rw [hc,Polynomial.coeff_monomial_same,ite_eq_right hw0] at hh
      simp [hi,hh]
  have he : c = algebraMap K R (b.repr c i0) := by
    calc
      c = Finsupp.linearCombination K b (b.repr c) := (b.linearCombination_repr c).symm
      _ = algebraMap K R (b.repr c i0) := by
        rw [hs,Finsupp.linearCombination_single,hb0,← Algebra.algebraMap_eq_smul_one]
        simp
  have ha : b.repr c i0 ≠ 0 := by
    intro h
    exact hc0 (by simpa only [h,map_zero] using he)
  rw [he]
  exact (isUnit_iff_ne_zero.mpr ha).map (algebraMap K R)

open scoped BigOperators

theorem pairBasisWeight_zero {n k A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (i : PairBasisIndex n k) (hi : pairBasisWeight A B i = 0) :
    i = (0,⟨0,by simp [PairNormal]⟩) := by
  rw [pairBasisWeight_eq] at hi
  have ht : i.1 2 = 0 := by omega
  have hs : ∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2) = 0 := by omega
  have hj (j : Fin (n+1)) :
      (pairIndexToTuple i j).1 = 0 ∧ (pairIndexToTuple i j).2 = 0 := by
    have he : A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2 ≤ 0 := by
      calc
        _ ≤ ∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
        _ = 0 := hs
    have ha : A*(pairIndexToTuple i j).1 = 0 := by omega
    have hb : B*(pairIndexToTuple i j).2 = 0 := by omega
    exact ⟨(Nat.mul_eq_zero.mp ha).resolve_left (Nat.ne_of_gt hA),
      (Nat.mul_eq_zero.mp hb).resolve_left (Nat.ne_of_gt hB)⟩
  apply Prod.ext
  · ext j
    fin_cases j
    · exact (hj 0).1
    · exact (hj 0).2
    · exact ht
  · apply Subtype.ext
    ext j
    cases j with
    | inl j => exact (hj j.succ).1
    | inr j => exact (hj j.succ).2

theorem pairCone_degree_zero_isUnit {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (θ : Fin n → K)
    (c : PairCone k A B θ) (hc0 : c ≠ 0)
    (hc : pairConeScale k A B θ c = Polynomial.monomial 0 c) : IsUnit c := by
  let i0 : PairBasisIndex n k := (0,⟨0,by simp [PairNormal]⟩)
  have hb0 : pairConeBasis k A B hB θ i0 = 1 := by
    simp only [pairConeBasis, Module.Basis.smulTower_apply,pairNormalBasis_smul]
    change Ideal.Quotient.mk _ (MvPolynomial.monomial 0
      (MvPolynomial.monomial 0 (1 : K))) = (1 : PairCone k A B θ)
    simp
  exact connected_homogeneous_isUnit (pairConeScale k A B θ)
    (pairConeBasis k A B hB θ) (pairBasisWeight A B) i0
    (pairConeBasis_homogeneous k A B hB θ) (fun i hi => pairBasisWeight_zero hA hB i hi)
    hb0 c hc hc0

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_BoundedLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

theorem basis_homogeneous_lift_at_degree {ι K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (t : R) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1) (r : R) (D : ℕ)
    (hD : ∀ i ∈ (b.repr r).support, w i ≤ D) :
    ∃ c : R, L c = Polynomial.monomial D c ∧ φ c = φ r := by
  classical
  let s := (b.repr r).support
  let c := ∑ i ∈ s, (b.repr r i) • (b i * t^(D-w i))
  refine ⟨c,?_,?_⟩
  · dsimp only [c]
    simp only [map_sum,map_smul,map_mul,map_pow,hb,ht]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.monomial_pow,one_mul,Polynomial.monomial_mul_monomial,
      Nat.add_sub_of_le (hD i hi),Polynomial.smul_monomial]
  · dsimp only [c]
    simp only [map_sum,map_smul,map_mul,map_pow,hφ,one_pow,mul_one]
    simpa only [s,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul]
      using congrArg φ (b.linearCombination_repr r)

end

section

theorem pairCone_cut_hilbert_uniform {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (u v : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Fin n → K) (c : PairCone k A B θ), c ≠ 0 →
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c →
      ∀ T : ℕ, A*u+B*v ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale k A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
          (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
        C*((T:ℝ)+1)^n := by
  obtain ⟨C,hC0,herror⟩ := pairFilteredDifference_hilbert_error (h := n) (k := k) hA hB u v
  refine ⟨C,hC0,fun θ c hc hC T hT => ?_⟩
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  let := pairCone_finite k A B hA hB θ (A*u+B*v+(T-(A*u+B*v)))
  have he := homogeneous_principal_finrank (pairConeScale k A B θ)
    (A*u+B*v) (T-(A*u+B*v)) c hc hC
  rw [Nat.add_sub_of_le hT, pairCone_finrank k A B hA hB θ,
    pairCone_finrank k A B hA hB θ] at he
  have he' := congrArg (Nat.cast : ℕ → ℝ) he
  push_cast at he'
  have h := herror T
  simp only [ite_eq_left hT] at h
  rw [← he', add_sub_cancel_right] at h
  exact h

theorem pairAffine_cut_hilbert_uniform {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hA : 0 < A) (hB : 0 < B) (u v : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : Fin n → K) (c : PairCone k A B θ), c ≠ 0 →
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c →
      ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c →
      ∀ T : ℕ, A*u+B*v ≤ T →
      |(Module.finrank K ((homogeneousSpace (pairConeScale k A B θ) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {c} ⊔
         Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)-1})).toLinearMap) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
          (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
        C*((T:ℝ)+1)^n := by
  obtain ⟨C,hC0,herror⟩ := pairCone_cut_hilbert_uniform (n := n) (K := K) k A B hA hB u v
  refine ⟨C,hC0,fun θ c hc hC hinfty T hT => ?_⟩
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  let := pairCone_finite k A B hA hB θ T
  rw [homogeneous_dehomogenization_finrank (pairConeScale k A B θ)
    (pairCone_t_prime k A B hB θ) hinfty (pairCone_t_homogeneous k A B θ) hC]
  exact herror θ c hc hC T hT

open scoped BigOperators

lemma monomial_eq_univ_prod {σ R : Type*} [Fintype σ] [CommSemiring R]
    (m : σ →₀ ℕ) (r : R) : MvPolynomial.monomial m r =
      MvPolynomial.C r * ∏ j, MvPolynomial.X j ^ m j := by
  rw [MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun j => pow_zero _)

end

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_QuarticPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

lemma pairConeBasis_map {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (i : PairBasisIndex n k) :
    φ (pairConeBasis k A B hB θ i) =
      MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
        (MvPolynomial.monomial (pairABExponent i) (1 : K)) := by
  classical
  simp only [pairConeBasis,Module.Basis.smulTower_apply,pairNormalBasis_smul]
  change φ (Ideal.Quotient.mk _ (MvPolynomial.monomial i.2.val (MvPolynomial.monomial i.1 (1 : K)))) = _
  simp only [monomial_eq_univ_prod,map_mul,map_prod,map_pow,map_one,one_mul,
    MvPolynomial.aeval_X]
  have ht' : φ (Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.X 2))) = 1 := ht
  simp only [Fintype.prod_sum_type]
  simp [Fin.prod_univ_succ,ht',pairABExponent,pairConeA,pairConeB,pairIndexToTuple,pairCoeffMap]
  ring

lemma pairConePolynomial_eval {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (c : PairCone k A B θ) :
    MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
      (pairConePolynomial k A B hB θ c) = φ c := by
  classical
  let b := pairConeBasis k A B hB θ
  have he (i : PairBasisIndex n k) (r : K) :
      MvPolynomial.monomial (pairABExponent i) r =
        r • MvPolynomial.monomial (pairABExponent i) (1 : K) := by
    simp [MvPolynomial.smul_monomial]
  have heval (i : PairBasisIndex n k) (r : K) :
      MvPolynomial.aeval (Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ))
        (MvPolynomial.monomial (pairABExponent i) r) = r • φ (b i) := by
    rw [he,map_smul,← pairConeBasis_map k A B hB θ φ ht]
  simp only [pairConePolynomial,Finsupp.sum,map_sum,heval]
  simpa only [b,Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul] using
    congrArg φ (b.linearCombination_repr c)

lemma pairConePolynomial_weight {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (c : PairCone k A B θ) (D : ℕ)
    (hc : pairConeScale k A B θ c = Polynomial.monomial D c) :
    ∀ m ∈ (pairConePolynomial k A B hB θ c).support,
      A * (∑ i, m (Sum.inl i)) + B * (∑ j, m (Sum.inr j)) ≤ D := by
  classical
  let b := pairConeBasis k A B hB θ
  have hcoord (i : PairBasisIndex n k) (hi : i ∈ (b.repr c).support) :
      pairBasisWeight A B i = D := by
    have h := homogeneous_coord (pairConeScale k A B θ) b (pairBasisWeight A B)
      (pairConeBasis_homogeneous k A B hB θ) c D i
    simp only [hc,Polynomial.coeff_monomial,ite_true] at h
    by_contra hn
    rw [ite_eq_right hn] at h
    exact (Finsupp.mem_support_iff.mp hi) h
  intro m hm
  have hmem := MvPolynomial.support_sum hm
  obtain ⟨i,hi,hm'⟩ := Finset.mem_biUnion.mp hmem
  have hmi : m = pairABExponent i := by
    exact Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm')
  rw [hmi]
  have he := hcoord i hi
  rw [pairBasisWeight_eq] at he
  change A * (∑ j, (pairIndexToTuple i j).1) + B * (∑ j, (pairIndexToTuple i j).2) ≤ D
  have hsum : (∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2)) =
      A * (∑ j, (pairIndexToTuple i j).1) + B * (∑ j, (pairIndexToTuple i j).2) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum]
  rw [hsum] at he
  omega

open scoped BigOperators
open MvPolynomial

end

open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairBoundaries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open MvPolynomial
open scoped Classical

theorem pairBoundaryExponent_injective {n k : ℕ} {i : Fin n}
    {m m' : (Fin n ⊕ Fin n) →₀ ℕ}
    (hm : PairNormal k m) (hm' : PairNormal k m')
    (hmi : m (Sum.inl i) = 0) (hmi' : m' (Sum.inl i) = 0)
    (h : pairBoundaryExponent k i m = pairBoundaryExponent k i m') : m = m' := by
  apply pairExponent_injective_normal hm hm'
  have hb := congrArg Prod.snd h
  have ha := congrArg Prod.fst h
  funext j
  by_cases hj : j = i
  · subst j
    simp_all [pairExponent, pairBoundaryExponent]
  · simpa [pairBoundaryExponent, hj] using congrFun ha j

theorem pairBoundaryMap_monomial {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (k : ℕ) (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (m : (Fin n ⊕ Fin n) →₀ ℕ) (c : R) :
    pairBoundaryMap k q φ i (monomial m c) =
      AddMonoidAlgebra.single (pairBoundaryExponent k i m)
        (φ c * (0:S) ^ m (Sum.inl i) * ∏ j ∈ Finset.univ.erase i, φ (q j)^m (Sum.inr j)) := by
  classical
  have hs (g : Fin n → ℤ) (j : Fin n) :
      (∑ x, if x = i then 0 else if j = x then g x else 0) =
        if j = i then 0 else g j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [pairBoundaryMap, eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    AddMonoidAlgebra.single_pow, AddMonoidAlgebra.prod_single,
    AddMonoidAlgebra.single_mul_single]
  change AddMonoidAlgebra.single (0 : (Fin n → ℤ) × ℕ) (φ c) * _ = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]
  congr 1
  · ext j
    · by_cases hj : j = i
      · subst j
        simp [pairBoundaryExponent, Prod.fst_sum, Finset.sum_apply,
          ite_apply, Pi.single_apply, nsmul_eq_mul, hs]
      · simp [pairBoundaryExponent, pairExponent, Prod.fst_sum, Finset.sum_apply,
          ite_apply, Pi.single_apply, nsmul_eq_mul, mul_comm, sub_eq_add_neg, hj, hs]
    · simp [pairBoundaryExponent, Prod.snd_sum]
  · have ha : (∏ j : Fin n, (if j = i then (0 : S) else 1) ^ m (Sum.inl j)) =
        (0 : S) ^ m (Sum.inl i) := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    have hb : (∏ j : Fin n, (if j = i then 1 else φ (q j)) ^ m (Sum.inr j)) =
        ∏ j ∈ Finset.univ.erase i, φ (q j) ^ m (Sum.inr j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [ite_true, one_pow, one_mul]
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
      simp [hj]
    rw [ha, hb]
    ring

theorem pairBoundaryMap_relation {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    {k : ℕ} (hk : 0 < k) (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (hqi : φ (q i) = 0) (j : Fin n) :
    pairBoundaryMap k q φ i (pairRelation k q j) = 0 := by
  classical
  simp only [pairRelation, map_sub, map_mul, map_pow]
  simp only [pairBoundaryMap, eval₂Hom_X', eval₂Hom_C, Sum.elim_inl, Sum.elim_inr,
    RingHom.comp_apply, AddMonoidAlgebra.singleZeroRingHom_apply]
  by_cases hj : j = i
  · subst j
    simp [hqi, Nat.ne_of_gt hk]
  · simp only [hj, ite_false, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single, one_pow, one_mul]
    have he : k • (Pi.single j (1 : ℤ), (0 : ℕ)) +
        (Pi.single j (-(k : ℤ)), (0 : ℕ)) = (0 : (Fin n → ℤ) × ℕ) := by
      ext a
      · by_cases ha : a = j <;> simp [ha]
      · simp
    rw [he]
    exact sub_self _

theorem pairBoundaryMap_normal_coeff {n : ℕ} {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain S] (k : ℕ) (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (hq : ∀ j, j ≠ i → φ (q j) ≠ 0)
    (r : MvPolynomial (Fin n ⊕ Fin n) R)
    (hr : ∀ m ∈ r.support, PairNormal k m) (he : pairBoundaryMap k q φ i r = 0)
    (m : (Fin n ⊕ Fin n) →₀ ℕ) (hmi : m (Sum.inl i) = 0) : φ (r.coeff m) = 0 := by
  classical
  by_cases hm : m ∈ r.support
  · have hc : (pairBoundaryMap k q φ i r).coeff (pairBoundaryExponent k i m) =
        φ (r.coeff m) * ∏ j ∈ Finset.univ.erase i, φ (q j) ^ m (Sum.inr j) := by
      conv_lhs => rw [r.as_sum, map_sum]
      rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        Finset.sum_eq_single_of_mem m hm]
      · simp [pairBoundaryMap_monomial, hmi, AddMonoidAlgebra.coeff_single]
      · intro m' hm' hne
        by_cases hmi' : m' (Sum.inl i) = 0
        · have hE : pairBoundaryExponent k i m' ≠ pairBoundaryExponent k i m :=
            fun hh => hne (pairBoundaryExponent_injective (hr m' hm') (hr m hm) hmi' hmi hh)
          simp [pairBoundaryMap_monomial, AddMonoidAlgebra.coeff_single, hE]
        · simp [pairBoundaryMap_monomial, hmi']
    rw [he] at hc
    have hp : (∏ j ∈ Finset.univ.erase i, φ (q j) ^ m (Sum.inr j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j hj => pow_ne_zero _ (hq j (Finset.mem_erase.mp hj).1))
    exact (mul_eq_zero.mp hc.symm).resolve_right hp
  · simp [notMem_support_iff.mp hm]

theorem pair_boundary_ideal_eq_ker {n : ℕ} {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] {k : ℕ} (hk : 0 < k)
    (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (hker : RingHom.ker φ = Ideal.span {q i})
    (hq : ∀ j, j ≠ i → φ (q j) ≠ 0) :
    Ideal.span (Set.range (pairRelation k q)) ⊔ Ideal.span {X (Sum.inl i)} =
      RingHom.ker (pairBoundaryMap k q φ i) := by
  classical
  let I : Ideal (MvPolynomial (Fin n ⊕ Fin n) R) :=
    Ideal.span (Set.range (pairRelation k q)) ⊔ Ideal.span {X (Sum.inl i)}
  have hqi : φ (q i) = 0 := by
    change q i ∈ RingHom.ker φ
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hle : I ≤ RingHom.ker (pairBoundaryMap k q φ i) := by
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact pairBoundaryMap_relation hk q φ i hqi j
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      change pairBoundaryMap k q φ i (X (Sum.inl i)) = 0
      simp [pairBoundaryMap]
  have hX : X (Sum.inl i) ∈ I :=
    (show Ideal.span {X (Sum.inl i)} ≤ I from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _))
  have hC : C (q i) ∈ I := by
    have hp : X (Sum.inl i) ^ k * X (Sum.inr i) ∈ I :=
      I.mul_mem_right _ (I.pow_mem_of_mem hX k hk)
    have hr : pairRelation k q i ∈ I :=
      (show Ideal.span (Set.range (pairRelation k q)) ≤ I from le_sup_left)
        (Ideal.subset_span ⟨i, rfl⟩)
    have hh := I.sub_mem hp hr
    simpa [pairRelation] using hh
  apply le_antisymm hle
  intro p hp
  obtain ⟨g, r, hpr, hr⟩ := pair_normal_form k q p
  have hg : Finsupp.linearCombination _ (pairRelation k q) g ∈ I := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro j _
    exact I.mul_mem_left _ ((show Ideal.span (Set.range (pairRelation k q)) ≤ I from le_sup_left)
      (Ideal.subset_span ⟨j, rfl⟩))
  have her : pairBoundaryMap k q φ i r = 0 := by
    have he := congrArg (pairBoundaryMap k q φ i) hpr
    rw [map_add, show pairBoundaryMap k q φ i p = 0 from hp,
      show pairBoundaryMap k q φ i (Finsupp.linearCombination _ (pairRelation k q) g) = 0
        from hle hg, zero_add] at he
    exact he.symm
  have hri : r ∈ I := by
    rw [r.as_sum]
    apply Ideal.sum_mem
    intro m _
    by_cases hmi : m (Sum.inl i) = 0
    · have hc := pairBoundaryMap_normal_coeff k q φ i hq r hr her m hmi
      change r.coeff m ∈ RingHom.ker φ at hc
      rw [hker, Ideal.mem_span_singleton] at hc
      obtain ⟨c, hc⟩ := hc
      rw [hc, ← C_mul_monomial]
      exact I.mul_mem_right _ hC
    · exact I.mem_of_dvd (X_dvd_monomial.mpr (Or.inr hmi)) hX
  rw [hpr]
  exact I.add_mem hg hri

theorem pair_boundary_ideal_isPrime {n : ℕ} {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] {k : ℕ} (hk : 0 < k)
    (q : Fin n → R) (φ : R →+* S) (i : Fin n)
    (hker : RingHom.ker φ = Ideal.span {q i})
    (hq : ∀ j, j ≠ i → φ (q j) ≠ 0) :
    (Ideal.span (Set.range (pairRelation k q)) ⊔ Ideal.span {X (Sum.inl i)}).IsPrime := by
  rw [pair_boundary_ideal_eq_ker hk q φ i hker hq]
  exact RingHom.ker_isPrime _

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_LaurentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem pairToLaurent_injective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Function.Injective (pairToLaurent k q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [pair_ideal_eq_ker k q hq]
  exact hx

theorem pairToLaurent_prod_coordinate {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (m : Fin n → ℕ) :
    pairToLaurent k q (∏ i, pairCoordinate k q i ^ m i) =
      AddMonoidAlgebra.single (fun i => (m i : ℤ)) 1 := by
  classical
  simp only [map_prod,map_pow,pairToLaurent_coordinate,AddMonoidAlgebra.single_pow,
    one_pow,AddMonoidAlgebra.prod_single,Finset.prod_const_one]
  congr 1
  ext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem pairLaurent_fractions {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (z : AddMonoidAlgebra R (Fin n → ℤ)) :
    ∃ x y : PairRing k q, y ∈ Submonoid.closure (Set.range (pairCoordinate k q)) ∧
      z * pairToLaurent k q y = pairToLaurent k q x := by
  classical
  induction z using AddMonoidAlgebra.induction_on with
  | of e =>
    refine ⟨∏ i, pairCoordinate k q i ^ (e i).toNat,
      ∏ i, pairCoordinate k q i ^ (-e i).toNat,?_,?_⟩
    · exact Submonoid.prod_mem _ fun i _ => Submonoid.pow_mem _
        (Submonoid.subset_closure (show pairCoordinate k q i ∈
          Set.range (pairCoordinate k q) from ⟨i,rfl⟩)) _
    · change AddMonoidAlgebra.single e 1 * _ = _
      rw [pairToLaurent_prod_coordinate,pairToLaurent_prod_coordinate,
        AddMonoidAlgebra.single_mul_single,one_mul]
      congr 1
      ext i
      simp only [Pi.add_apply]
      omega
  | add z w hz hw =>
    obtain ⟨x,a,ha,hx⟩ := hz
    obtain ⟨y,b,hb,hy⟩ := hw
    refine ⟨x*b+y*a,a*b,Submonoid.mul_mem _ ha hb,?_⟩
    rw [map_add,map_mul,map_mul,map_mul,← hx,← hy]
    ring
  | smul r z hz =>
    obtain ⟨x,a,ha,hx⟩ := hz
    refine ⟨Ideal.Quotient.mk _ (C r)*x,a,ha,?_⟩
    rw [map_mul,pairToLaurent_C,← hx,← mul_assoc]
    congr 1
    ext e
    simp

theorem pairLaurent_isLocalization {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    let : Algebra (PairRing k q) (AddMonoidAlgebra R (Fin n → ℤ)) :=
      (pairToLaurent k q).toAlgebra
    IsLocalization (Submonoid.closure (Set.range (pairCoordinate k q)))
      (AddMonoidAlgebra R (Fin n → ℤ)) := by
  let : Algebra (PairRing k q) (AddMonoidAlgebra R (Fin n → ℤ)) :=
    (pairToLaurent k q).toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro y
    change IsUnit (pairToLaurent k q y.val)
    have hv : ∀ a ∈ Submonoid.closure (Set.range (pairCoordinate k q)),
        IsUnit (pairToLaurent k q a) := by
      intro a ha
      induction ha using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨i,rfl⟩ := ha
        rw [pairToLaurent_coordinate]
        exact ⟨⟨AddMonoidAlgebra.single (Pi.single i 1) 1,
          AddMonoidAlgebra.single (-(Pi.single i 1)) 1,
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def],
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def]⟩,rfl⟩
      | one => simp
      | mul a b ha hb iha ihb => simpa only [map_mul] using iha.mul ihb
    exact hv y.val y.property
  · intro z
    obtain ⟨x,y,hy,hxy⟩ := pairLaurent_fractions k q z
    exact ⟨(x,⟨y,hy⟩),hxy⟩
  · intro x y he
    exact ⟨1,by simpa only [OneMemClass.coe_one,one_mul] using pairToLaurent_injective k q hq he⟩

end
section
open MvPolynomial

theorem pair_coordinate_prime {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] {k : ℕ} (hk : 0 < k)
    (q : Fin n → R) (φ : R →+* S) (i : Fin n) (hq0 : ∀ j, q j ≠ 0)
    (hker : RingHom.ker φ = Ideal.span {q i})
    (hq : ∀ j, j ≠ i → φ (q j) ≠ 0) :
    Prime (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q))) (X (Sum.inl i))) := by
  let I := Ideal.span (Set.range (pairRelation k q))
  let : I.IsPrime := pair_ideal_isPrime k q hq0
  have hprime : (I ⊔ Ideal.span {X (Sum.inl i)}).IsPrime :=
    pair_boundary_ideal_isPrime hk q φ i hker hq
  have hx0 : Ideal.Quotient.mk I (X (Sum.inl i)) ≠ 0 := by
    intro hx
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hx
    change X (Sum.inl i) ∈ Ideal.span (Set.range (pairRelation k q)) at hm
    rw [pair_ideal_eq_ker k q hq0] at hm
    change pairLaurentMap k q (X (Sum.inl i)) = 0 at hm
    simp [pairLaurentMap,AddMonoidAlgebra.single_eq_zero] at hm
  apply (Ideal.span_singleton_prime hx0).mp
  have : (I ⊔ Ideal.span {X (Sum.inl i)}).IsPrime := hprime
  have hp := Ideal.isPrime_map_quotientMk_of_isPrime
    (I := I) (p := I ⊔ Ideal.span {X (Sum.inl i)}) le_sup_left
  simpa only [Ideal.map_sup,Ideal.map_quotient_self,bot_sup_eq,Ideal.map_span,
    Set.image_singleton] using hp

theorem pair_root_coordinate_prime {n : ℕ} {K : Type*} [Field K]
    {k : ℕ} (hk : 0 < k) (θ : Fin n → K) (hθ : Function.Injective θ) (i : Fin n) :
    Prime (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k
      (fun j => Polynomial.X-Polynomial.C (θ j)))) ) (X (Sum.inl i))) := by
  apply pair_coordinate_prime hk (fun j => Polynomial.X-Polynomial.C (θ j))
    (Polynomial.evalRingHom (θ i)) i
  · exact fun j => Polynomial.X_sub_C_ne_zero (θ j)
  · exact Polynomial.ker_evalRingHom _
  · intro j hj
    change Polynomial.eval (θ i) (Polynomial.X-Polynomial.C (θ j)) ≠ 0
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_ne_zero]
    exact fun h => hj (hθ h.symm)

end

theorem extract_finite_nonunit_factors {R : Type*} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] (s : Finset R) (hs : ∀ a ∈ s, ¬ IsUnit a)
    {c : R} (hc : c ≠ 0) :
    ∃ a ∈ Submonoid.closure (s : Set R), ∃ c' : R,
      c' ≠ 0 ∧ c = a*c' ∧ ∀ p ∈ s, ¬ p ∣ c' := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => exact ⟨1,Submonoid.one_mem _,c,hc,by simp,by simp⟩
  | @insert p s hp ih =>
    obtain ⟨a,ha,q,hq,he,hnd⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr)) hc
    obtain ⟨v,c',hn,he'⟩ := WfDvdMonoid.max_power_factor' hq (hs p (Finset.mem_insert_self ..))
    have hc' : c' ≠ 0 := by intro h; simp [he',h] at hq
    refine ⟨a*p^v,Submonoid.mul_mem _ ?_ ?_,c',hc',?_,?_⟩
    · exact Submonoid.closure_mono (by simp only [Finset.coe_insert]; exact Set.subset_insert p _) ha
    · exact Submonoid.pow_mem _ (Submonoid.subset_closure (Finset.mem_insert_self ..)) v
    · rw [he,he',mul_assoc]
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hn
      · intro hrc
        apply hnd r hr
        rw [he']
        exact dvd_mul_of_dvd_right hrc _

theorem extract_prime_equation_from_open {R S : Type*}
    [CommRing R] [IsDomain R] [WfDvdMonoid R] [CommRing S] [Algebra R S]
    (s : Finset R) [IsLocalization (Submonoid.closure (s : Set R)) S]
    (hs : ∀ a ∈ s, Prime a) {F : R} (hF : F ≠ 0)
    (hlocal : ((Ideal.span {F}).map (algebraMap R S)).IsPrime) :
    ∃ e ∈ Submonoid.closure (s : Set R), ∃ c : R,
      c ≠ 0 ∧ F = e*c ∧ (∀ a ∈ s, ¬ a ∣ c) ∧
      (Ideal.span {c}).IsPrime ∧
      ((Ideal.span {F}).map (algebraMap R S)) =
        ((Ideal.span {c}).map (algebraMap R S)) := by
  obtain ⟨e,he,c,hc,hFc,hdiv⟩ :=
    extract_finite_nonunit_factors s (fun a ha => (hs a ha).not_isUnit) hF
  have hu : IsUnit (algebraMap R S e) := IsLocalization.map_units S (⟨e,he⟩ : Submonoid.closure (s : Set R))
  have heq : ((Ideal.span {F}).map (algebraMap R S)) =
      ((Ideal.span {c}).map (algebraMap R S)) := by
    rw [hFc,Ideal.map_span,Ideal.map_span,Set.image_singleton,Set.image_singleton,map_mul]
    exact Ideal.span_singleton_mul_left_unit hu _
  refine ⟨e,he,c,hc,hFc,hdiv,?_,heq⟩
  apply principal_isPrime_of_localization_coordinates (S := S) (s : Set R) c hs hdiv
  rwa [← heq]

open MvPolynomial

theorem rootPair_extract_prime_cut {n : ℕ} {K : Type*} [Field K]
    {k : ℕ} (hk : 0 < k) (θ : Fin n → K) (hθ : Function.Injective θ) :
    let q : Fin n → Polynomial K := fun j => Polynomial.X-Polynomial.C (θ j)
    ∀ F : PairRing k q, F ≠ 0 →
      (Ideal.span {pairToLaurent k q F}).IsPrime →
      ∃ e ∈ Submonoid.closure (Set.range (pairCoordinate k q)), ∃ c : PairRing k q,
        c ≠ 0 ∧ F = e*c ∧ (∀ i, ¬ pairCoordinate k q i ∣ c) ∧
        (Ideal.span {c}).IsPrime ∧
        (Ideal.span {pairToLaurent k q F}) = (Ideal.span {pairToLaurent k q c}) := by
  classical
  dsimp only
  let q : Fin n → Polynomial K := fun j => Polynomial.X-Polynomial.C (θ j)
  change ∀ F : PairRing k q, _
  intro F hF hlocal
  let : (Ideal.span (Set.range (pairRelation k q))).IsPrime :=
    pair_ideal_isPrime k q (fun j => Polynomial.X_sub_C_ne_zero (θ j))
  let : Algebra (PairRing k q) (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)) :=
    (pairToLaurent k q).toAlgebra
  let s : Finset (PairRing k q) := Finset.univ.image (pairCoordinate k q)
  have hs : (s : Set (PairRing k q)) = Set.range (pairCoordinate k q) := by
    simp [s]
  let : IsLocalization (Submonoid.closure (s : Set (PairRing k q)))
      (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)) := by
    rw [hs]
    exact pairLaurent_isLocalization k q (fun j => Polynomial.X_sub_C_ne_zero (θ j))
  have hsp : ∀ a ∈ s, Prime a := by
    intro a ha
    have har : a ∈ Set.range (pairCoordinate k q) := by rw [← hs]; exact ha
    obtain ⟨i,rfl⟩ := har
    exact pair_root_coordinate_prime hk θ hθ i
  have hl : ((Ideal.span {F}).map
      (algebraMap (PairRing k q) (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)))).IsPrime := by
    simpa only [Ideal.map_span,Set.image_singleton,RingHom.algebraMap_toAlgebra] using hlocal
  obtain ⟨e,he,c,hc,hFc,hdiv,hprime,heq⟩ :=
    extract_prime_equation_from_open s hsp hF hl
  refine ⟨e,?_,c,hc,hFc,?_,hprime,?_⟩
  · rwa [← hs]
  · intro i
    apply hdiv
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · simpa only [Ideal.map_span,Set.image_singleton,RingHom.algebraMap_toAlgebra] using heq

open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PrincipalLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

theorem homogeneous_dehomogenization_zero {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {t x : R} {D : ℕ} (ht0 : t ≠ 0)
    (ht : L t = Polynomial.monomial 1 t)
    (hx : L x = Polynomial.monomial D x)
    (hzero : Ideal.Quotient.mk (Ideal.span {t-1}) x = 0) : x = 0 := by
  let S := Localization.Away t
  let a : R →+* S := algebraMap R S
  let z : S := IsLocalization.Away.invSelf t
  let ev : R →+* S := (Polynomial.eval₂RingHom a z).comp L.toRingHom
  have het : ev (t-1) = 0 := by
    rw [map_sub,map_one,sub_eq_zero]
    change Polynomial.eval₂ a z (L t) = 1
    rw [ht,Polynomial.eval₂_monomial,pow_one]
    exact IsLocalization.Away.mul_invSelf t
  have hker : Ideal.span {t-1} ≤ RingHom.ker ev :=
    Ideal.span_le.mpr (by rintro _ rfl; exact het)
  have he : a x * z^D = 0 := by
    have h := hker (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    change Polynomial.eval₂ a z (L x) = 0 at h
    rwa [hx,Polynomial.eval₂_monomial] at h
  have hz : z*a t = 1 := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf t
  have hax : a x = 0 := by
    have h := congrArg (fun y : S => y*(a t)^D) he
    simpa only [mul_assoc,←mul_pow,hz,one_pow,mul_one,zero_mul] using h
  apply IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
  simpa only [map_zero] using hax

theorem homogeneous_dehomogenization_eq {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {t x y : R} {D : ℕ} (ht0 : t ≠ 0)
    (ht : L t = Polynomial.monomial 1 t)
    (hx : L x = Polynomial.monomial D x)
    (hy : L y = Polynomial.monomial D y)
    (he : Ideal.Quotient.mk (Ideal.span {t-1}) x =
      Ideal.Quotient.mk (Ideal.span {t-1}) y) : x = y := by
  apply sub_eq_zero.mp
  apply homogeneous_dehomogenization_zero L (D := D) ht0 ht
  · simp only [map_sub,hx,hy]
  · simp only [map_sub,he,sub_self]

theorem saturated_homogeneous_minimal_degree {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R)
    {t x y : R} {D E : ℕ} (ht0 : t ≠ 0)
    (ht : L t = Polynomial.monomial 1 t)
    (hx : L x = Polynomial.monomial D x)
    (hy : L y = Polynomial.monomial E y) (hxt : ¬ t ∣ x)
    (he : Ideal.Quotient.mk (Ideal.span {t-1}) x =
      Ideal.Quotient.mk (Ideal.span {t-1}) y) : D ≤ E := by
  by_contra hn
  have hED : E < D := by omega
  have hEq : x = y*t^(D-E) := by
    apply homogeneous_dehomogenization_eq L ht0 ht hx
    · simp only [map_mul,map_pow,hy,ht,Polynomial.monomial_pow,one_mul,
        Polynomial.monomial_mul_monomial,Nat.add_sub_of_le (Nat.le_of_lt hED)]
    · have htone : Ideal.Quotient.mk (Ideal.span {t-1}) t = 1 := by
        have h : Ideal.Quotient.mk (Ideal.span {t-1}) (t-1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
        simpa only [map_sub,map_one,sub_eq_zero] using h
      simp only [map_mul,map_pow,htone,one_pow,mul_one,he]
  apply hxt
  rw [hEq]
  exact dvd_mul_of_dvd_right (dvd_pow_self t (by omega)) y

theorem pairAffine_divisor_bounded_lift {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (r : PairCone k A B θ) (M : ℕ)
    (hM : ∀ i ∈ ((pairConeBasis k A B hB θ).repr r).support, pairBasisWeight A B i ≤ M)
    (hr : pairAffineMk k A B θ r ≠ 0)
    (x : PairAffine k A B θ) (hdiv : x ∣ pairAffineMk k A B θ r) :
    ∃ u v : ℕ, ∃ c : PairCone k A B θ, A*u+B*v ≤ M ∧
      pairConeScale k A B θ c = Polynomial.monomial (A*u+B*v) c ∧
      pairAffineMk k A B θ c = x ∧ c ≠ 0 ∧
      ¬ pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2) ∣ c := by
  let : (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ)))).IsPrime :=
    pair_ideal_isPrime k _ (pairConeQ_ne_zero k A B hB θ)
  obtain ⟨y,hxy⟩ := hdiv
  have hx0 : x ≠ 0 := by intro h; exact hr (hxy.trans (by rw [h]; exact zero_mul y))
  have hy0 : y ≠ 0 := by intro h; exact hr (hxy.trans (by rw [h]; exact mul_zero x))
  obtain ⟨rx,hrx⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨ry,hry⟩ := Ideal.Quotient.mk_surjective y
  have hrx0 : Ideal.Quotient.mk _ rx ≠ 0 := hrx ▸ hx0
  have hry0 : Ideal.Quotient.mk _ ry ≠ 0 := hry ▸ hy0
  obtain ⟨u,v,cx,hcx,hcxe,hcx0,hcxt⟩ := pairCone_minimal_lift k A B hB θ rx hrx0
  obtain ⟨u',v',cy,hcy,hcye,hcy0,hcyt⟩ := pairCone_minimal_lift k A B hB θ ry hry0
  have hcxmap : pairAffineMk k A B θ cx = x := hcxe.trans hrx
  have hcymap : pairAffineMk k A B θ cy = y := hcye.trans hry
  let t := pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)
  have htp : Prime t := pairCone_t_prime k A B hB θ
  obtain ⟨cr,hcr,hcre⟩ := basis_homogeneous_lift_at_degree (S := PairAffine k A B θ)
    (pairConeScale k A B θ) (pairConeBasis k A B hB θ) (pairBasisWeight A B)
    (pairConeBasis_homogeneous k A B hB θ) t (pairCone_t_homogeneous k A B θ)
    (pairAffineMk k A B θ) (pairAffineMk_t k A B θ) r M hM
  have hhom : pairConeScale k A B θ (cx*cy) =
      Polynomial.monomial ((A*u+B*v)+(A*u'+B*v')) (cx*cy) := by
    simp only [map_mul,hcx,hcy,Polynomial.monomial_mul_monomial]
  have hnt : ¬ t ∣ cx*cy := fun h => (htp.dvd_or_dvd h).elim hcxt hcyt
  have he : Ideal.Quotient.mk (Ideal.span {t-1}) (cx*cy) =
      Ideal.Quotient.mk (Ideal.span {t-1}) cr := by
    change pairAffineMk k A B θ (cx*cy) = pairAffineMk k A B θ cr
    rw [map_mul,hcxmap,hcymap,hcre,←hxy]
  have hle := saturated_homogeneous_minimal_degree (pairConeScale k A B θ)
    htp.ne_zero (pairCone_t_homogeneous k A B θ) hhom hcr hnt he
  exact ⟨u,v,cx,(Nat.le_add_right _ _).trans hle,hcx,hcxmap,hcx0,hcxt⟩

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PositiveCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem positiveLaurentMap_injective {n : ℕ} {R : Type*} [CommRing R] :
    Function.Injective (positiveLaurentMap : MvPolynomial (Fin n) R →+* _) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro e f h
  ext i
  have hi : (e i : ℤ) = (f i : ℤ) := congrFun h i
  exact_mod_cast hi

theorem positiveLaurentMap_prod_X {n : ℕ} {R : Type*} [CommRing R] (m : Fin n → ℕ) :
    positiveLaurentMap (∏ i, (X i : MvPolynomial (Fin n) R)^m i) =
      AddMonoidAlgebra.single (fun i => (m i : ℤ)) 1 := by
  classical
  simp only [map_prod,map_pow,positiveLaurentMap_X,AddMonoidAlgebra.single_pow,
    one_pow,AddMonoidAlgebra.prod_single,Finset.prod_const_one]
  congr 1
  ext j
  simp [Finset.sum_apply,Pi.single_apply]

theorem positiveLaurent_fractions {n : ℕ} {R : Type*} [CommRing R]
    (z : AddMonoidAlgebra R (Fin n → ℤ)) :
    ∃ x y : MvPolynomial (Fin n) R, y ∈ Submonoid.closure (Set.range X) ∧
      z * positiveLaurentMap y = positiveLaurentMap x := by
  classical
  induction z using AddMonoidAlgebra.induction_on with
  | of e =>
    refine ⟨∏ i, X i ^ (e i).toNat, ∏ i, X i ^ (-e i).toNat,?_,?_⟩
    · exact Submonoid.prod_mem _ fun i _ => Submonoid.pow_mem _
        (Submonoid.subset_closure (show X i ∈ Set.range (X : Fin n → MvPolynomial (Fin n) R) from ⟨i,rfl⟩)) _
    · change AddMonoidAlgebra.single e 1 * _ = _
      rw [positiveLaurentMap_prod_X,positiveLaurentMap_prod_X,
        AddMonoidAlgebra.single_mul_single,one_mul]
      congr 1
      ext i
      simp only [Pi.add_apply]
      omega
  | add z w hz hw =>
    obtain ⟨x,a,ha,hx⟩ := hz
    obtain ⟨y,b,hb,hy⟩ := hw
    refine ⟨x*b+y*a,a*b,Submonoid.mul_mem _ ha hb,?_⟩
    rw [map_add,map_mul,map_mul,map_mul,←hx,←hy]
    ring
  | smul r z hz =>
    obtain ⟨x,a,ha,hx⟩ := hz
    refine ⟨C r*x,a,ha,?_⟩
    rw [map_mul,positiveLaurentMap_C,←hx,←mul_assoc]
    congr 1
    ext e
    simp

theorem positiveLaurent_isLocalization {n : ℕ} {R : Type*} [CommRing R] :
    let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
      positiveLaurentMap.toAlgebra
    IsLocalization (Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R)))
      (AddMonoidAlgebra R (Fin n → ℤ)) := by
  let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
    positiveLaurentMap.toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro y
    change IsUnit (positiveLaurentMap y.val)
    have hu : ∀ a ∈ Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R)),
        IsUnit (positiveLaurentMap a) := by
      intro a ha
      induction ha using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨i,rfl⟩ := ha
        rw [positiveLaurentMap_X]
        exact ⟨⟨AddMonoidAlgebra.single (Pi.single i 1) 1,
          AddMonoidAlgebra.single (-(Pi.single i 1)) 1,
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def],
          by simp [AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.one_def]⟩,rfl⟩
      | one => simp
      | mul a b ha hb iha ihb => simpa only [map_mul] using iha.mul ihb
    exact hu y.val y.property
  · intro z
    obtain ⟨x,y,hy,hxy⟩ := positiveLaurent_fractions z
    exact ⟨(x,⟨y,hy⟩),hxy⟩
  · intro x y he
    exact ⟨1,by simpa only [OneMemClass.coe_one,one_mul] using positiveLaurentMap_injective he⟩

end
open MvPolynomial

theorem positiveToPair_toLaurent {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (p : MvPolynomial (Fin n) R) :
    pairToLaurent k q (positiveToPair k q p) = positiveLaurentMap p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [pairCoeffMap]
  | add p r hp hr => simp only [map_add,hp,hr]
  | mul_X p i hp => simp only [map_mul,hp,positiveToPair_X,pairToLaurent_coordinate,positiveLaurentMap_X]

theorem pair_laurent_evaluation {n : ℕ} {R L : Type*} [CommRing R] [Field L]
    (k : ℕ) (q : Fin n → R) (ψ : PairRing k q →+* L)
    (ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L)
    (ha : ∀ i, ψ (pairCoordinate k q i) ≠ 0)
    (hcomp : ∀ p, ℓ (positiveLaurentMap p) = ψ (positiveToPair k q p)) :
    ℓ.comp (pairToLaurent k q) = ψ := by
  have hC (r : R) : ℓ (pairToLaurent k q (pairCoeffMap k q r)) = ψ (pairCoeffMap k q r) := by
    simpa only [←positiveToPair_toLaurent k q,positiveToPair_C] using hcomp (C r)
  have hA (i : Fin n) : ℓ (pairToLaurent k q (pairCoordinate k q i)) = ψ (pairCoordinate k q i) := by
    simpa only [←positiveToPair_toLaurent k q,positiveToPair_X] using hcomp (X i)
  have hB (i : Fin n) : ℓ (pairToLaurent k q (Ideal.Quotient.mk _ (X (Sum.inr i)))) =
      ψ (Ideal.Quotient.mk _ (X (Sum.inr i))) := by
    apply mul_left_cancel₀ (pow_ne_zero k (ha i))
    have he1 := congrArg (fun x => ℓ (pairToLaurent k q x)) (pairCoordinate_equation k q i)
    have he2 := congrArg ψ (pairCoordinate_equation k q i)
    simp only [map_mul,map_pow] at he1 he2
    change ℓ (pairToLaurent k q (pairCoordinate k q i)) ^ k * _ = _ at he1
    rw [hA,hC] at he1
    exact he1.trans he2.symm
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C r => exact hC r
  | add p r hp hr => simpa only [map_add] using congrArg₂ (·+·) hp hr
  | mul_X p i hp =>
    simp only [RingHom.comp_apply,map_mul,hp]
    cases i with
    | inl j => rw [show Ideal.Quotient.mk _ (X (Sum.inl j)) = pairCoordinate k q j from rfl,hA]
    | inr j => rw [hB]

theorem positiveLaurent_kernel {n : ℕ} {R L : Type*} [CommRing R] [Field L]
    (φ : MvPolynomial (Fin n) R →+* L) (ha : ∀ i, φ (X i) ≠ 0) :
    ∃ ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L,
      (∀ p, ℓ (positiveLaurentMap p) = φ p) ∧
      RingHom.ker ℓ = (RingHom.ker φ).map positiveLaurentMap := by
  let : Algebra (MvPolynomial (Fin n) R) (AddMonoidAlgebra R (Fin n → ℤ)) :=
    positiveLaurentMap.toAlgebra
  let M := Submonoid.closure (Set.range (X : Fin n → MvPolynomial (Fin n) R))
  let : IsLocalization M (AddMonoidAlgebra R (Fin n → ℤ)) := positiveLaurent_isLocalization
  have hu : ∀ y : M, IsUnit (φ y.val) := by
    intro y
    have hh : ∀ a ∈ M, IsUnit (φ a) := by
      intro a ha'
      induction ha' using Submonoid.closure_induction with
      | mem a ha' =>
        obtain ⟨i,rfl⟩ := ha'
        exact isUnit_iff_ne_zero.mpr (ha i)
      | one => simp
      | mul a b ha' hb' iha ihb => simpa only [map_mul] using iha.mul ihb
    exact hh y.val y.property
  let ℓ : AddMonoidAlgebra R (Fin n → ℤ) →+* L := IsLocalization.lift hu
  have hc : ∀ p, ℓ (positiveLaurentMap p) = φ p := IsLocalization.lift_eq hu
  refine ⟨ℓ,hc,?_⟩
  have hk : (RingHom.ker ℓ).under (MvPolynomial (Fin n) R) = RingHom.ker φ := by
    ext p
    change ℓ (positiveLaurentMap p) = 0 ↔ φ p = 0
    rw [hc]
  have hm := IsLocalization.map_under M (AddMonoidAlgebra R (Fin n → ℤ)) (RingHom.ker ℓ)
  rw [hk] at hm
  exact hm.symm

theorem rootPair_projection_kernel {n : ℕ} {K L : Type*} [Field K] [Field L]
    {k : ℕ} (hk : 0 < k) (θ : Fin n → K) (hθ : Function.Injective θ)
    (ψ : PairRing k (fun j => Polynomial.X-Polynomial.C (θ j)) →+* L)
    (ha : ∀ i, ψ (pairCoordinate k _ i) ≠ 0)
    (F : MvPolynomial (Fin n) (Polynomial K)) (hF : F ≠ 0)
    (hker : ∀ p, ψ (positiveToPair k _ p) = 0 ↔ F ∣ p) :
    ∃ c : PairRing k (fun j => Polynomial.X-Polynomial.C (θ j)),
      c ≠ 0 ∧ c ∣ positiveToPair k _ F ∧
      (∀ i, ¬ pairCoordinate k _ i ∣ c) ∧ RingHom.ker ψ = Ideal.span {c} := by
  let q : Fin n → Polynomial K := fun j => Polynomial.X-Polynomial.C (θ j)
  let : (Ideal.span (Set.range (pairRelation k q))).IsPrime :=
    pair_ideal_isPrime k q (fun j => Polynomial.X_sub_C_ne_zero (θ j))
  let φ := ψ.comp (positiveToPair k q)
  have haφ : ∀ i, φ (X i) ≠ 0 := by simpa only [φ,RingHom.comp_apply,positiveToPair_X] using ha
  obtain ⟨ℓ,hℓ,hkerℓ⟩ := positiveLaurent_kernel φ haφ
  have hℓpair : ℓ.comp (pairToLaurent k q) = ψ := pair_laurent_evaluation k q ψ ℓ ha hℓ
  have hkerφ : RingHom.ker φ = Ideal.span {F} := by
    ext p
    exact (hker p).trans Ideal.mem_span_singleton.symm
  rw [hkerφ,Ideal.map_span,Set.image_singleton] at hkerℓ
  have hpos : positiveToPair k q F ≠ 0 := by
    intro h
    have hh := congrArg (pairToLaurent k q) h
    rw [positiveToPair_toLaurent,map_zero] at hh
    exact hF (positiveLaurentMap_injective (hh.trans (map_zero positiveLaurentMap).symm))
  have hlocal : (Ideal.span {pairToLaurent k q (positiveToPair k q F)}).IsPrime := by
    rw [positiveToPair_toLaurent,←hkerℓ]
    exact RingHom.ker_isPrime ℓ
  obtain ⟨e,he,c,hc,hFc,hdiv,hprime,heq⟩ := rootPair_extract_prime_cut hk θ hθ
    (positiveToPair k q F) hpos hlocal
  refine ⟨c,hc,⟨e,by simpa [mul_comm] using hFc⟩,hdiv,?_⟩
  let : Algebra (PairRing k q) (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)) :=
    (pairToLaurent k q).toAlgebra
  let : IsLocalization (Submonoid.closure (Set.range (pairCoordinate k q)))
      (AddMonoidAlgebra (Polynomial K) (Fin n → ℤ)) :=
    pairLaurent_isLocalization k q (fun j => Polynomial.X_sub_C_ne_zero (θ j))
  have hp : ∀ a ∈ Set.range (pairCoordinate k q), Prime a := by
    rintro a ⟨i,rfl⟩
    exact pair_root_coordinate_prime hk θ hθ i
  have hd : ∀ a ∈ Set.range (pairCoordinate k q), ¬ a ∣ c := by
    rintro a ⟨i,rfl⟩
    exact hdiv i
  have hs := principal_under_map_coordinates (S := AddMonoidAlgebra (Polynomial K) (Fin n → ℤ))
    (Set.range (pairCoordinate k q)) c hp hd
  have hceq : RingHom.ker ℓ = Ideal.map (pairToLaurent k q) (Ideal.span {c}) := by
    rw [Ideal.map_span,Set.image_singleton,←heq,positiveToPair_toLaurent,←hkerℓ]
  rw [←hs]
  ext x
  change ψ x = 0 ↔ pairToLaurent k q x ∈ Ideal.map (pairToLaurent k q) (Ideal.span {c})
  rw [←hceq]
  change ψ x = 0 ↔ ℓ (pairToLaurent k q x) = 0
  rw [←RingHom.comp_apply,hℓpair]

open MvPolynomial
open scoped BigOperators

theorem homogeneous_aeval_monomial {σ K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (z : σ → R) (w : σ → ℕ)
    (hz : ∀ i, L (z i) = Polynomial.monomial (w i) (z i))
    (m : σ →₀ ℕ) (a : K) :
    L (MvPolynomial.aeval z (monomial m a)) =
      Polynomial.monomial (Finsupp.weight w m) (MvPolynomial.aeval z (monomial m a)) := by
  let f : K →ₐ[K] R := Algebra.ofId K R
  have hf : MvPolynomial.aevalTower f z = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have hL : L.comp (MvPolynomial.aeval z) =
      MvPolynomial.aevalTower (L.comp f) (fun i => Polynomial.monomial (w i) (z i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.coe_comp,Function.comp_apply,aeval_X,aevalTower_X] using hz i
  have ha : (L.comp f) a = Polynomial.monomial 0 (f a) := by
    simp only [AlgHom.coe_comp,Function.comp_apply,f,Algebra.ofId_apply,L.commutes]
    rfl
  have hh := aevalTower_monomial_homogeneous f (L.comp f) z w m a 0 ha
  rw [←hL,hf] at hh
  simpa only [Nat.zero_add,AlgHom.coe_comp,Function.comp_apply] using hh

theorem polynomial_homogeneous_lift {σ K R S : Type*} [Field K] [CommRing R]
    [CommRing S] [Algebra K R] [Algebra K S]
    (L : R →ₐ[K] Polynomial R) (t : R) (ht : L t = Polynomial.monomial 1 t)
    (φ : R →ₐ[K] S) (hφ : φ t = 1)
    (z : σ → R) (w : σ → ℕ) (W : ℕ) (hw : ∀ i, w i ≤ W)
    (hz : ∀ i, L (z i) = Polynomial.monomial (w i) (z i))
    (p : MvPolynomial σ K) :
    ∃ c : R, L c = Polynomial.monomial (W*p.totalDegree) c ∧
      φ c = MvPolynomial.aeval (φ ∘ z) p := by
  classical
  let D := W*p.totalDegree
  have hm (m) (hm : m ∈ p.support) : Finsupp.weight w m ≤ D := by
    calc Finsupp.weight w m = ∑ i ∈ m.support, w i*m i := by
          simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]
      _ ≤ ∑ i ∈ m.support, W*m i := Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (hw i))
      _ = W * ∑ i ∈ m.support, m i := by rw [Finset.mul_sum]
      _ ≤ D := Nat.mul_le_mul_left _ (le_totalDegree hm)
  let a (m : σ →₀ ℕ) := MvPolynomial.aeval z (monomial m (p.coeff m))
  let v (m : σ →₀ ℕ) := a m * t^(D-Finsupp.weight w m)
  have hv (m) (hm' : m ∈ p.support) : L (v m) = Polynomial.monomial D (v m) := by
    dsimp [v,a]
    rw [map_mul,homogeneous_aeval_monomial L z w hz,map_pow,ht,
      Polynomial.monomial_pow,one_mul,Polynomial.monomial_mul_monomial,Nat.add_sub_of_le (hm m hm')]
  refine ⟨∑ m ∈ p.support, v m,?_,?_⟩
  · simp only [map_sum]
    exact Finset.sum_congr rfl (fun m hm' => hv m hm')
  · have hvφ (m) : φ (v m) = MvPolynomial.aeval (φ ∘ z) (monomial m (p.coeff m)) := by
      simp only [v,map_mul,map_pow,hφ,one_pow,mul_one,a]
      have he : φ.comp (MvPolynomial.aeval z) = MvPolynomial.aeval (φ ∘ z) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp
      exact AlgHom.congr_fun he _
    rw [map_sum]
    simp only [hvφ]
    rw [←map_sum,←p.as_sum]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section

section
open MvPolynomial

theorem positiveToPairHom_apply {n : ℕ} {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] (k : ℕ) (q : Fin n → R) (p : MvPolynomial (Fin n) R) :
    positiveToPairHom (K := K) k q p = positiveToPair k q p := rfl

theorem positiveToPair_option {n : ℕ} {K : Type*} [Field K]
    (k : ℕ) (θ : Fin n → K) (p : MvPolynomial (Option (Fin n)) K) :
    positiveToPair k (rootPairQ θ) (optionEquivRight K (Fin n) p) =
      MvPolynomial.aeval (fun i => i.elim (pairCoeffMap k (rootPairQ θ) Polynomial.X)
        (pairLeft k (rootPairQ θ))) p := by
  have he : (positiveToPairHom (K := K) k (rootPairQ θ)).comp
      (optionEquivRight K (Fin n)).toAlgHom =
      MvPolynomial.aeval (fun i => i.elim (pairCoeffMap k (rootPairQ θ) Polynomial.X)
        (pairLeft k (rootPairQ θ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none => simp [positiveToPairHom_apply]
    | some i => simp [positiveToPairHom_apply,pairLeft,pairCoordinate]
  exact AlgHom.congr_fun he p

theorem pairConeA_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin (n+1)) :
    pairConeScale k A B θ (pairConeA k A B θ i) =
      Polynomial.monomial A (pairConeA k A B θ i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairConeA,pairConeScale,pairScale_coeff,weightedScale_X,triplePairWeights]
  · change pairScalePre k A B (pairConeQ k A B θ) (weightedScale (triplePairWeights A B))
      (X (Sum.inl j)) = _
    simp [pairScalePre,pairConeA]

theorem pairConeB_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin (n+1)) :
    pairConeScale k A B θ (pairConeB k A B θ i) =
      Polynomial.monomial B (pairConeB k A B θ i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairConeB,pairConeScale,pairScale_coeff,weightedScale_X,triplePairWeights]
  · change pairScalePre k A B (pairConeQ k A B θ) (weightedScale (triplePairWeights A B))
      (X (Sum.inr j)) = _
    simp [pairScalePre,pairConeB]

theorem pairConeN_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    pairConeScale k A B (coneDifference θ) (pairConeN k A B θ) =
      Polynomial.monomial (k*A+B) (pairConeN k A B θ) := by
  simp only [pairConeN,map_add,map_mul,map_pow,pairConeA_homogeneous,pairConeB_homogeneous,
    pairCone_t_homogeneous,Polynomial.monomial_pow,Polynomial.monomial_mul_monomial,one_mul]
  rw [AlgHom.commutes]
  change Polynomial.monomial (A*k+B) _ + Polynomial.C (algebraMap K _ (θ 0)) *
    Polynomial.monomial (k*A+B) _ = _
  rw [Polynomial.C_mul_monomial,mul_comm A k,←map_add]

theorem rootPair_projection_homogeneous_lift {n : ℕ} {K : Type*} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (θ : Fin (n+1) → K)
    (p : MvPolynomial (Option (Fin (n+1))) K) :
    ∃ c : PairCone k A B (coneDifference θ),
      pairConeScale k A B (coneDifference θ) c =
        Polynomial.monomial ((k*A+B)*p.totalDegree) c ∧
      pairConeToRoot k A B θ c = positiveToPair k (rootPairQ θ)
        (optionEquivRight K (Fin (n+1)) p) := by
  let z : Option (Fin (n+1)) → PairCone k A B (coneDifference θ) :=
    fun i => i.elim (pairConeN k A B θ) (pairConeA k A B (coneDifference θ))
  let w : Option (Fin (n+1)) → ℕ := fun i => i.elim (k*A+B) (fun _ => A)
  have hw : ∀ i, w i ≤ k*A+B := by
    rintro (_|i)
    · exact le_rfl
    · exact (show A ≤ k*A by simpa using Nat.mul_le_mul_right A hk).trans (Nat.le_add_right _ _)
  have hz : ∀ i, pairConeScale k A B (coneDifference θ) (z i) = Polynomial.monomial (w i) (z i) := by
    rintro (_|i)
    · exact pairConeN_homogeneous k A B θ
    · exact pairConeA_homogeneous k A B (coneDifference θ) i
  obtain ⟨c,hc,hφc⟩ := polynomial_homogeneous_lift (pairConeScale k A B (coneDifference θ))
    (pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2))
    (pairCone_t_homogeneous k A B (coneDifference θ)) (pairConeToRoot k A B θ)
    (pairConeToRoot_t k A B θ) z w (k*A+B) hw hz p
  refine ⟨c,hc,?_⟩
  rw [hφc,positiveToPair_option]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> simp [z,Function.comp_def]

theorem pairConeToRoot_surjective {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) : Function.Surjective (pairConeToRoot k A B θ) := by
  intro x
  obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective (rootPairAffineEquiv k A B θ x)
  refine ⟨p,?_⟩
  have he : pairAffineMk k A B (coneDifference θ) p = rootPairAffineEquiv k A B θ x := hp
  apply (rootPairAffineEquiv k A B θ).injective
  exact (AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) p).trans he

theorem pairConeToRoot_kernel {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    RingHom.ker (pairConeToRoot k A B θ).toRingHom =
      Ideal.span {pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)-1} := by
  ext x
  change pairConeToRoot k A B θ x = 0 ↔ _
  rw [←Ideal.Quotient.eq_zero_iff_mem]
  change pairConeToRoot k A B θ x = 0 ↔ pairAffineMk k A B (coneDifference θ) x = 0
  have h := AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) x
  rw [←h]
  exact ((rootPairAffineEquiv k A B θ).map_eq_zero_iff).symm

theorem rootPair_bounded_cone_kernel {n : ℕ} {K L : Type*} [Field K] [Field L] [Algebra K L]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hB : 0 < B)
    (θ : Fin (n+1) → K) (hθ : Function.Injective θ)
    (ψ : RootPair k θ →ₐ[K] L) (ha : ∀ i, ψ (pairLeft k (rootPairQ θ) i) ≠ 0)
    (p : MvPolynomial (Option (Fin (n+1))) K) (hp : p ≠ 0)
    (hker : ∀ q, ψ (positiveToPair k (rootPairQ θ) q) = 0 ↔
      optionEquivRight K (Fin (n+1)) p ∣ q) :
    ∃ u v : ℕ, ∃ c : PairCone k A B (coneDifference θ),
      A*u+B*v ≤ (k*A+B)*p.totalDegree ∧
      pairConeScale k A B (coneDifference θ) c = Polynomial.monomial (A*u+B*v) c ∧
      c ≠ 0 ∧ ¬ pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2) ∣ c ∧
      RingHom.ker (ψ.comp (pairConeToRoot k A B θ)).toRingHom =
        Ideal.span {c} ⊔ Ideal.span {pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)-1} := by
  obtain ⟨x,hx,hdiv,hcoord,hxker⟩ := rootPair_projection_kernel hk θ hθ ψ.toRingHom ha
    (optionEquivRight K (Fin (n+1)) p) ((optionEquivRight K (Fin (n+1))).map_eq_zero_iff.not.mpr hp) hker
  obtain ⟨r,hr,hre⟩ := rootPair_projection_homogeneous_lift hk A B θ p
  have hM : ∀ i ∈ ((pairConeBasis k A B hB (coneDifference θ)).repr r).support,
      pairBasisWeight A B i ≤ (k*A+B)*p.totalDegree := by
    intro i hi
    have hh := homogeneous_coord (pairConeScale k A B (coneDifference θ))
      (pairConeBasis k A B hB (coneDifference θ)) (pairBasisWeight A B)
      (pairConeBasis_homogeneous k A B hB (coneDifference θ)) r ((k*A+B)*p.totalDegree) i
    simp only [hr,Polynomial.coeff_monomial,ite_true] at hh
    have he : pairBasisWeight A B i = (k*A+B)*p.totalDegree := by
      by_contra hn
      rw [ite_eq_right hn] at hh
      exact (Finsupp.mem_support_iff.mp hi) hh
    exact he.le
  have hpos : positiveToPair k (rootPairQ θ) (optionEquivRight K (Fin (n+1)) p) ≠ 0 := by
    intro hh
    have he := congrArg (pairToLaurent k (rootPairQ θ)) hh
    rw [positiveToPair_toLaurent,map_zero] at he
    exact hp ((optionEquivRight K (Fin (n+1))).injective
      (positiveLaurentMap_injective (he.trans (map_zero positiveLaurentMap).symm)))
  have he (r) : rootPairAffineEquiv k A B θ (pairConeToRoot k A B θ r) =
      pairAffineMk k A B (coneDifference θ) r :=
    AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) r
  have hr0 : pairAffineMk k A B (coneDifference θ) r ≠ 0 := by
    rw [←he,hre]
    exact (rootPairAffineEquiv k A B θ).map_eq_zero_iff.not.mpr hpos
  have hd : rootPairAffineEquiv k A B θ x ∣ pairAffineMk k A B (coneDifference θ) r := by
    rw [←he,hre]
    exact map_dvd (rootPairAffineEquiv k A B θ) hdiv
  obtain ⟨u,v,c,hD,hc,hce,hc0,hct⟩ := pairAffine_divisor_bounded_lift k A B hB
    (coneDifference θ) r ((k*A+B)*p.totalDegree) hM hr0 (rootPairAffineEquiv k A B θ x) hd
  have hcx : pairConeToRoot k A B θ c = x := (rootPairAffineEquiv k A B θ).injective
    ((he c).trans hce)
  refine ⟨u,v,c,hD,hc,hc0,hct,?_⟩
  have hspan : Ideal.span {x} = Ideal.map (pairConeToRoot k A B θ).toRingHom
      (Ideal.span {c}) := by
    rw [Ideal.map_span,Set.image_singleton]
    exact congrArg (fun y : RootPair k θ => Ideal.span {y}) hcx.symm
  change (RingHom.ker ψ.toRingHom).comap (pairConeToRoot k A B θ).toRingHom = _
  have hxker' : (RingHom.ker ψ.toRingHom : Ideal (RootPair k θ)) = Ideal.span {x} := hxker
  rw [hxker',hspan,
    Ideal.comap_map_of_surjective (pairConeToRoot k A B θ).toRingHom (pairConeToRoot_surjective k A B θ)]
  congr 1
  exact pairConeToRoot_kernel k A B θ

end
open scoped BigOperators

theorem finrank_map_eq_of_kernel_eq {K R S T : Type*} [Field K]
    [AddCommGroup R] [AddCommGroup S] [AddCommGroup T]
    [Module K R] [Module K S] [Module K T]
    (f : R →ₗ[K] S) (g : R →ₗ[K] T) (hker : LinearMap.ker f = LinearMap.ker g)
    (V : Submodule K R) : Module.finrank K (V.map f) = Module.finrank K (V.map g) := by
  have he : LinearMap.ker (f.domRestrict V) = LinearMap.ker (g.domRestrict V) := by
    ext x
    change x.val ∈ LinearMap.ker f ↔ x.val ∈ LinearMap.ker g
    rw [hker]
  rw [←LinearMap.range_domRestrict,←LinearMap.range_domRestrict,
    ←(f.domRestrict V).quotKerEquivRange.finrank_eq,
    ←(g.domRestrict V).quotKerEquivRange.finrank_eq,he]

theorem finrank_map_quotient_kernel {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (φ : R →ₐ[K] S) (I : Ideal R) (hker : RingHom.ker φ.toRingHom = I)
    (V : Submodule K R) :
    Module.finrank K (V.map (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Module.finrank K (V.map φ.toLinearMap) := by
  apply finrank_map_eq_of_kernel_eq
  ext x
  change Ideal.Quotient.mk I x = 0 ↔ φ x = 0
  rw [Ideal.Quotient.eq_zero_iff_mem,←hker]
  rfl

end

open MvPolynomial
open scoped BigOperators

theorem weightedSpace_mul_mem {σ K : Type*} [Field K]
    (w : σ → ℕ) {p q : MvPolynomial σ K} {A B : ℕ}
    (hp : p ∈ weightedSpace w A) (hq : q ∈ weightedSpace w B) :
    p*q ∈ weightedSpace w (A+B) := by
  rw [mem_weightedSpace] at hp hq ⊢
  by_cases hp0 : p = 0
  · simp [hp0,weightedTotalDegree_zero]
  by_cases hq0 : q = 0
  · simp [hq0,weightedTotalDegree_zero]
  rw [weightedTotalDegree_mul_exact w p q hp0 hq0]
  exact Nat.add_le_add hp hq

theorem weightedSpace_one {σ K : Type*} [Field K] (w : σ → ℕ) :
    (1 : MvPolynomial σ K) ∈ weightedSpace w 0 := by
  intro m hm
  have hm0 : m = 0 := Finset.mem_singleton.mp (support_one.subset hm)
  simp [hm0]

theorem weightedSpace_pow_mem {σ K : Type*} [Field K]
    (w : σ → ℕ) {p : MvPolynomial σ K} {A : ℕ}
    (hp : p ∈ weightedSpace w A) (e : ℕ) : p^e ∈ weightedSpace w (A*e) := by
  induction e with
  | zero => simpa using weightedSpace_one w
  | succ e ih => simpa only [pow_succ,Nat.mul_succ] using weightedSpace_mul_mem w ih hp

theorem weightedSpace_prod_mem {σ ι K : Type*} [Field K]
    (w : σ → ℕ) (s : Finset ι) (p : ι → MvPolynomial σ K) (A : ι → ℕ)
    (hp : ∀ i ∈ s, p i ∈ weightedSpace w (A i)) :
    ∏ i ∈ s, p i ∈ weightedSpace w (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedSpace_one w
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    exact weightedSpace_mul_mem w (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem weightedSpace_mono {σ K : Type*} [CommSemiring K]
    (w : σ → ℕ) {A B : ℕ} (h : A ≤ B) :
    weightedSpace (K := K) w A ≤ weightedSpace w B := by
  intro p hp m hm
  exact (hp hm).trans h

theorem weightedSpace_aeval {σ τ K : Type*} [Fintype σ] [Field K]
    (w : σ → ℕ) (v : τ → ℕ) (z : σ → MvPolynomial τ K)
    (hz : ∀ i, z i ∈ weightedSpace v (w i))
    (p : MvPolynomial σ K) (T : ℕ) (hp : p ∈ weightedSpace w T) :
    MvPolynomial.aeval z p ∈ weightedSpace v T := by
  classical
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro m hm
  rw [aeval_monomial,Finsupp.prod_fintype _ _ (by simp)]
  rw [←Algebra.smul_def]
  apply Submodule.smul_mem
  apply weightedSpace_mono v (hp hm)
  have hh := weightedSpace_prod_mem v Finset.univ (fun i => z i ^ m i)
    (fun i => w i * m i) (fun i _ => weightedSpace_pow_mem v (hz i) (m i))
  have he : Finsupp.weight w m = ∑ i, w i * m i := by
    rw [Finsupp.weight_eq_sum]
    simp only [nsmul_eq_mul,Nat.cast_id,mul_comm]
  rwa [he]

theorem totalSpace_aeval {σ τ K : Type*} [Fintype σ] [Field K]
    (z : σ → MvPolynomial τ K) (D : ℕ) (hz : ∀ i, (z i).totalDegree ≤ D)
    (p : MvPolynomial σ K) (T : ℕ) (hp : p ∈ totalSpace T) :
    MvPolynomial.aeval z p ∈ totalSpace (D*T) := by
  have hz' (i) : z i ∈ weightedSpace (fun _ => 1) D := by
    rw [mem_weightedSpace]
    change weightedTotalDegree 1 (z i) ≤ D
    rw [weightedTotalDegree_one]
    exact hz i
  have hp' : p ∈ weightedSpace (fun _ => D) (D*T) := by
    intro m hm
    calc Finsupp.weight (fun _ => D) m = D * m.sum (fun _ e => e) := by
          rw [Finsupp.weight_eq_sum,Finsupp.sum_fintype _ _ (by simp),Finset.mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => by simp [mul_comm])
      _ ≤ D*T := Nat.mul_le_mul_left D ((le_totalDegree hm).trans (mem_totalSpace.mp hp))
  have hh := weightedSpace_aeval (fun _ => D) (fun _ => 1) z hz' p (D*T) hp'
  rw [mem_weightedSpace] at hh
  change weightedTotalDegree 1 (MvPolynomial.aeval z p) ≤ D*T at hh
  rwa [weightedTotalDegree_one,←mem_totalSpace] at hh

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ProjectionDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem polynomial_projection_hilbert_le {n m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (J : Ideal (MvPolynomial (Fin m) K)) (z : Fin m → MvPolynomial (Fin n) K)
    (D : ℕ) (hz : ∀ i, (z i).totalDegree ≤ D)
    (hker : ∀ p, Ideal.Quotient.mk I (MvPolynomial.aeval z p) = 0 ↔ p ∈ J) (T : ℕ) :
    Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap) ≤
      Module.finrank K ((totalSpace (D*T)).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let := totalSpace_finite (n := n) (K := K) (D*T)
  let f₀ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval z)
  let f := Ideal.Quotient.liftₐ J f₀ (fun p hp => (hker p).mpr hp)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro y hy
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker p).mp hy)
  let g := (f.toLinearMap.domRestrict
    ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap)).codRestrict
      ((totalSpace (D*T)).map (Ideal.Quotient.mkₐ K I).toLinearMap) (by
        rintro ⟨y,p,hp,rfl⟩
        exact ⟨MvPolynomial.aeval z p,totalSpace_aeval z D hz p T hp,rfl⟩)
  apply LinearMap.finrank_le_finrank_of_injective (f := g)
  intro y z he
  exact Subtype.ext (hf (congrArg Subtype.val he))

theorem polynomial_projection_equation_degree_bound {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (z : Fin (h+1) → MvPolynomial (Fin n) K)
    (D : ℕ) (hD : 0 < D) (hz : ∀ i, (z i).totalDegree ≤ D)
    (q : MvPolynomial (Fin (h+1)) K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (MvPolynomial.aeval z p) = 0 ↔ q ∣ p) :
    (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h * (D:ℚ)^h := by
  let Q := P.comp (Polynomial.C (D:ℚ)*Polynomial.X)
  have hQT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace (D*T)).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        Q.eval (T:ℚ) := by
    obtain ⟨T₀,hT₀⟩ := Filter.eventually_atTop.mp hT
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀,fun T hTT => ?_⟩
    have hT' : T₀ ≤ D*T := hTT.trans (by simpa using Nat.mul_le_mul_right T hD)
    simpa [Q,Polynomial.eval_comp] using hT₀ (D*T) hT'
  have hQ : Q.natDegree ≤ h := by
    have hh := Polynomial.natDegree_comp_le (p := P) (q := Polynomial.C (D:ℚ)*Polynomial.X)
    have hND : (Polynomial.C (D:ℚ)*Polynomial.X).natDegree ≤ 1 := by
      exact le_trans Polynomial.natDegree_mul_le (by simp)
    exact (hh.trans ((Nat.mul_le_mul_left _ hND).trans_eq (Nat.mul_one _))).trans hP
  have hh : ∀ᶠ T : ℕ in Filter.atTop,
      (hypersurfaceHilbertPolynomial h q.totalDegree).eval (T:ℚ) ≤ Q.eval (T:ℚ) := by
    filter_upwards [hQT,Filter.eventually_ge_atTop q.totalDegree] with T hT hqT
    rw [←hT,←hypersurface_hilbert_polynomial q hq T hqT]
    exact_mod_cast polynomial_projection_hilbert_le I (Ideal.span {q}) z D hz
      (fun p => (hker p).trans Ideal.mem_span_singleton.symm) T
  have hc := coeff_le_of_eventually_nat_eval_le
    (hypersurfaceHilbertPolynomial h q.totalDegree) Q h
    (hypersurfaceHilbertPolynomial_degree _ _) hQ hh
  rw [hypersurfaceHilbertPolynomial_coeff,Polynomial.comp_C_mul_X_coeff] at hc
  have hf : (0:ℚ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  exact (div_le_iff₀ hf).mp hc |>.trans_eq (by ring)

end
section
open MvPolynomial

theorem polynomial_projection_equation_degree_bound_equiv {n h : ℕ}
    {σ K : Type*} [Field K] (e : Fin (h+1) ≃ σ)
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (z : σ → MvPolynomial (Fin n) K)
    (D : ℕ) (hD : 0 < D) (hz : ∀ i, (z i).totalDegree ≤ D)
    (q : MvPolynomial σ K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (MvPolynomial.aeval z p) = 0 ↔ q ∣ p) :
    (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h * (D:ℚ)^h := by
  let E := MvPolynomial.renameEquiv K e
  let q₀ := E.symm q
  have hq₀ : q₀ ≠ 0 := by
    intro hz
    apply hq
    have hh := congrArg E hz
    simpa only [q₀,E.apply_symm_apply,map_zero] using hh
  have he (p : MvPolynomial (Fin (h+1)) K) :
      MvPolynomial.aeval (z ∘ e) p = MvPolynomial.aeval z (E p) := by
    simp only [E,MvPolynomial.renameEquiv_apply,MvPolynomial.aeval_rename,Function.comp_def]
  have hk₀ (p) : Ideal.Quotient.mk I (MvPolynomial.aeval (z ∘ e) p) = 0 ↔ q₀ ∣ p := by
    rw [he,hker]
    have hh := map_dvd_iff E (a := q₀) (b := p)
    rwa [show E q₀ = q from E.apply_symm_apply q] at hh
  have hh := polynomial_projection_equation_degree_bound I P hP hT (z ∘ e) D hD
    (fun i => hz (e i)) q₀ hq₀ hk₀
  have hdeg : q₀.totalDegree = q.totalDegree := MvPolynomial.totalDegree_renameEquiv e.symm q
  rwa [hdeg] at hh

theorem affine_polynomial_projection_degree_bound {n h : ℕ} {σ K : Type*}
    [Field K] (e : Fin (h+1) ≃ σ)
    (I : Ideal (MvPolynomial (Fin n) K)) (hdim : affineDimension I = h)
    (z : σ → MvPolynomial (Fin n) K) (D : ℕ) (hD : 0 < D)
    (hz : ∀ i, (z i).totalDegree ≤ D)
    (q : MvPolynomial σ K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (MvPolynomial.aeval z p) = 0 ↔ q ∣ p) :
    (q.totalDegree:ℚ) ≤ affineDegree I * (D:ℚ)^h := by
  have hh := polynomial_projection_equation_degree_bound_equiv e I (coordinateHilbert I)
    hdim.le (coordinateHilbert_eventually I) z D hD hz q hq hker
  simpa only [affineDegree,hdim] using hh

end

theorem left_coordinates_transcendence_selection {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (a : Fin d → A) (x : A) (hx : Transcendental K x)
    [Algebra.IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) A] :
    ∃ m : ℕ, ∃ j : Fin m → Fin d,
      AlgebraicIndependent K (Fin.cases x (a ∘ j)) ∧ Function.Injective j ∧
      Algebra.trdeg K A = (m+1 : ℕ) := by
  classical
  have hx' : AlgebraicIndepOn K id {x} := by
    change AlgebraicIndependent K (fun z : ({x} : Set A) => z.val)
    rw [algebraicIndependent_singleton_iff (⟨x,rfl⟩ : ({x} : Set A))]
    exact hx
  obtain ⟨t,hxt,htt,htb⟩ := exists_isTranscendenceBasis_between
    (R := K) (A := A) {x} (insert x (Set.range a)) (by simp) hx'
  have htfin : t.Finite := ((Set.finite_range a).insert x).subset htt
  let : Fintype t := htfin.fintype
  let xt : t := ⟨x,hxt (Set.mem_singleton x)⟩
  have hcard : 0 < Fintype.card t := Fintype.card_pos_iff.mpr ⟨xt⟩
  let m := Fintype.card t - 1
  have hm : m+1 = Fintype.card t := by omega
  let e₀ : Fin (m+1) ≃ t := (finCongr hm).trans (Fintype.equivFin t).symm
  let e : Fin (m+1) ≃ t := (Equiv.swap 0 (e₀.symm xt)).trans e₀
  have he0 : e 0 = xt := by simp [e]
  have heA (i : Fin m) : (e i.succ).val ∈ Set.range a := by
    have hh := htt (e i.succ).property
    rcases hh with hh | hh
    · have heq : e i.succ = xt := Subtype.ext hh
      have : i.succ = 0 := e.injective (heq.trans he0.symm)
      exact (Fin.succ_ne_zero i this).elim
    · exact hh
  choose j hj using heA
  have heval : (fun i : Fin (m+1) => (e i).val) = Fin.cases x (a ∘ j) := by
    funext i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact congrArg Subtype.val he0
    · exact (hj l).symm
  have hi : AlgebraicIndependent K (Fin.cases x (a ∘ j)) := by
    simpa only [Function.comp_def,heval] using htb.1.comp e e.injective
  refine ⟨m,j,hi,?_,?_⟩
  · intro i l hil
    apply Fin.succ_injective
    apply hi.injective
    simp only [Fin.cases_succ,Function.comp_def,hil]
  · rw [←htb.cardinalMk_eq_trdeg,Cardinal.mk_fintype,←hm]

theorem pair_right_isAlgebraic {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i ^ k * b i = x - algebraMap K A (θ i))
    (i : Fin d) : IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) (b i) := by
  let S := Algebra.adjoin K (insert x (Set.range a))
  let ai : S := ⟨a i,Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i,rfl⟩)⟩
  let xi : S := ⟨x,Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let p : Polynomial S := Polynomial.C (ai^k) * Polynomial.X -
    Polynomial.C (xi - algebraMap K S (θ i))
  refine ⟨p,?_,?_⟩
  · intro hp
    have hh := congrArg (fun q : Polynomial S => q.coeff 1) hp
    have hh' : ai^k = 0 := by
      simpa only [p,Polynomial.coeff_sub,Polynomial.coeff_C_mul_X,
        Polynomial.coeff_C,ite_eq_right (by decide : (1:ℕ) ≠ 0),
        ite_eq_left rfl,ite_true,sub_zero,Polynomial.coeff_zero] using hh
    have hai : ai ≠ 0 := fun h => ha i (congrArg Subtype.val h)
    exact pow_ne_zero k hai hh'
  · change Polynomial.aeval (b i) p = 0
    simp only [p,map_sub,map_mul,Polynomial.aeval_C,Polynomial.aeval_X]
    change a i ^ k * b i - (x - algebraMap K A (θ i)) = 0
    exact sub_eq_zero.mpr (hab i)

theorem pair_projection_isAlgebraic {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i ^ k * b i = x - algebraMap K A (θ i))
    (hgen : Algebra.adjoin K (Set.range a ∪ Set.range b) = ⊤) :
    Algebra.IsAlgebraic (Algebra.adjoin K (insert x (Set.range a))) A := by
  constructor
  intro z
  have hz : IsAlgebraic (Algebra.adjoin K (Set.range a ∪ Set.range b)) z := by
    rw [hgen]
    exact isAlgebraic_algebraMap (R := (⊤ : Subalgebra K A)) ⟨z,trivial⟩
  apply hz.adjoin_of_forall_isAlgebraic
  rintro y ⟨hy,hyn⟩
  rcases hy with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact (hyn (Set.mem_insert_of_mem _ ⟨i,rfl⟩)).elim
  · exact pair_right_isAlgebraic k a b x θ ha hab i

open MvPolynomial

theorem principal_evaluation_kernel_reindex {σ τ K A : Type*}
    [Field K] [CommRing A] [Algebra K A] (e : σ ≃ τ)
    (x : σ → A) (y : τ → A) (hxy : ∀ i, y (e i) = x i)
    (q : MvPolynomial σ K)
    (hq : ∀ p, MvPolynomial.aeval x p = 0 ↔ q ∣ p) :
    ∀ p, MvPolynomial.aeval y p = 0 ↔ MvPolynomial.renameEquiv K e q ∣ p := by
  intro p
  let p₀ := (MvPolynomial.renameEquiv K e).symm p
  have he : MvPolynomial.aeval x p₀ = MvPolynomial.aeval y p := by
    have hh : (MvPolynomial.aeval y).comp (MvPolynomial.renameEquiv K e).toAlgHom =
        MvPolynomial.aeval x := by
      apply MvPolynomial.algHom_ext
      intro i
      simpa using hxy i
    have hv := AlgHom.congr_fun hh p₀
    simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,
      p₀,AlgEquiv.apply_symm_apply] using hv.symm
  rw [←he,hq]
  exact (map_dvd_iff (MvPolynomial.renameEquiv K e)).symm.trans (by
    rw [show MvPolynomial.renameEquiv K e p₀ = p from AlgEquiv.apply_symm_apply _ _])

theorem finite_basis_extra_dependent {h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (x : A) (a : Fin (h+1) → A) (htr : Algebra.trdeg K A = (h+1 : ℕ)) :
    ¬ AlgebraicIndependent K (Fin.cases x a) := by
  intro hI
  have hh := hI.lift_cardinalMk_le_trdeg
  simp only [Cardinal.mk_fintype,Fintype.card_fin,Cardinal.lift_natCast,htr] at hh
  have : h+2 ≤ h+1 := by exact_mod_cast hh
  omega

theorem pairProjectionIndex_evaluation {d h : ℕ} {A : Type*}
    (a : Fin d → A) (x : A) (j : Fin h → Fin d) (i : Fin d) (r : Fin (h+2)) :
    (fun o => o.elim x (a ∘ Fin.cases i j)) (pairProjectionIndex h r) =
      Fin.cases (a i) (Fin.cases x (a ∘ j)) r := by
  refine Fin.cases ?_ (fun r' => ?_) r
  · simp only [pairProjectionIndex_zero,Option.elim_some,Function.comp_apply,Fin.cases_zero]
  · refine Fin.cases ?_ (fun r'' => ?_) r'
    · change (fun o => o.elim x (a ∘ Fin.cases i j)) (pairProjectionIndex h 1) = x
      simp only [pairProjectionIndex_one,Option.elim_none]
    · simp only [pairProjectionIndex_succ_succ,Option.elim_some,Function.comp_apply,Fin.cases_succ]

theorem pair_principal_projection_of_extra {d h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (a : Fin d → A) (x : A) (j : Fin h → Fin d) (i : Fin d)
    (hj : AlgebraicIndependent K (Fin.cases x (a ∘ j)))
    (htr : Algebra.trdeg K A = (h+1 : ℕ)) :
    ∃ p : MvPolynomial (Option (Fin (h+1))) K, Irreducible p ∧
      (∀ q, MvPolynomial.aeval (fun o => o.elim x (a ∘ Fin.cases i j)) q = 0 ↔ p ∣ q) := by
  have hdep := finite_basis_extra_dependent (K := K) (h := h) (a i) (Fin.cases x (a ∘ j)) htr
  generalize hy : (Fin.cases x (a ∘ j) : Fin (h+1) → A) = y at hj hdep
  obtain ⟨q,hq,_,hkq⟩ := exists_principal_relation_of_dependent (K := K) (h := h+1) (a i) y hj hdep
  refine ⟨MvPolynomial.renameEquiv K (pairProjectionIndex h) q, ?_, ?_⟩
  · exact (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv K (pairProjectionIndex h)).toMulEquiv).mpr hq
  · apply principal_evaluation_kernel_reindex (pairProjectionIndex h) _ _ _ q hkq
    intro r
    rw [←hy]
    exact pairProjectionIndex_evaluation a x j i r

theorem pair_principal_projection_of_basis {d h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (a : Fin d → A) (x : A) (j : Fin h → Fin d)
    (hj : AlgebraicIndependent K (Fin.cases x (a ∘ j)))
    (hjinj : Function.Injective j) (htr : Algebra.trdeg K A = (h+1 : ℕ))
    (hhd : h+1 ≤ d) :
    ∃ j : Fin (h+1) → Fin d, Function.Injective j ∧
      ∃ p : MvPolynomial (Option (Fin (h+1))) K, Irreducible p ∧
        (∀ q, MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q = 0 ↔ p ∣ q) := by
  classical
  have hex : ∃ i : Fin d, i ∉ Set.range j := by
    by_contra hh
    push Not at hh
    have hsur : Function.Surjective j := hh
    have hc := Fintype.card_le_of_surjective _ hsur
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨i,hi⟩ := hex
  let js : Fin (h+1) → Fin d := Fin.cases i j
  have hjs : Function.Injective js := by
    intro r s hrs
    induction r using Fin.cases with
    | zero =>
      induction s using Fin.cases with
      | zero => rfl
      | succ s => exact (hi ⟨s,hrs.symm⟩).elim
    | succ r =>
      induction s using Fin.cases with
      | zero => exact (hi ⟨r,hrs⟩).elim
      | succ s => exact congrArg Fin.succ (hjinj hrs)
  obtain ⟨p,hp,hkp⟩ := pair_principal_projection_of_extra a x j i hj htr
  exact ⟨js,hjs,p,hp,hkp⟩

theorem pair_principal_projection_selection {d : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (k : ℕ) (a b : Fin d → A) (x : A) (θ : Fin d → K)
    (ha : ∀ i, a i ≠ 0) (hab : ∀ i, a i ^ k * b i = x - algebraMap K A (θ i))
    (hgen : Algebra.adjoin K (Set.range a ∪ Set.range b) = ⊤)
    (hx : Transcendental K x) (hdim : Algebra.trdeg K A ≤ d) :
    ∃ h : ℕ, ∃ j : Fin (h+1) → Fin d, Function.Injective j ∧
      Algebra.trdeg K A = (h+1 : ℕ) ∧
      ∃ p : MvPolynomial (Option (Fin (h+1))) K, Irreducible p ∧
        (∀ q, MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q = 0 ↔ p ∣ q) := by
  classical
  let := pair_projection_isAlgebraic k a b x θ ha hab hgen
  obtain ⟨h,j,hj,hjinj,htr⟩ := left_coordinates_transcendence_selection a x hx
  have hhd : h+1 ≤ d := by exact_mod_cast (htr ▸ hdim)
  obtain ⟨js,hjs,p,hp,hkp⟩ := pair_principal_projection_of_basis a x j hj hjinj htr hhd
  exact ⟨h, js, hjs, htr, p, hp, hkp⟩

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_RootPairHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial

theorem norm_projection_bounded {n d h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (k : ℕ) (a b : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
    (θ : Fin d → K)
    (ha : ∀ i, Ideal.Quotient.mk I (a i) ≠ 0)
    (hab : ∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ i))
    (hgen : Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
      Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤)
    (hx : Transcendental K (Ideal.Quotient.mk I x))
    (hdim : affineDimension I = h+1) (hd : h+1 ≤ d)
    (E D : ℕ) (hD : 0 < D) (hdeg : affineDegree I ≤ E)
    (hadeg : ∀ i, (a i).totalDegree ≤ D) (hxdeg : x.totalDegree ≤ D) :
    ∃ j : Fin (h+1) → Fin d, Function.Injective j ∧
      ∃ p : MvPolynomial (Option (Fin (h+1))) K, Irreducible p ∧
        p.totalDegree ≤ E*D^(h+1) ∧
        (∀ q, Ideal.Quotient.mk I (MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q) = 0 ↔ p ∣ q) := by
  have htr : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = (h+1 : ℕ) := by
    rw [←hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)]
    change (affineDimension I : Cardinal) = _
    rw [hdim]
  have htd : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) ≤ d := by
    rw [htr]
    exact_mod_cast hd
  obtain ⟨m,j,hj,hm,p,hp,hkp⟩ := pair_principal_projection_selection k
    (fun i => Ideal.Quotient.mk I (a i)) (fun i => Ideal.Quotient.mk I (b i))
    (Ideal.Quotient.mk I x) θ ha hab hgen hx htd
  have hmh : m = h := by
    have hh : m+1 = h+1 := by exact_mod_cast (hm.symm.trans htr)
    omega
  subst m
  have hker (q) : Ideal.Quotient.mk I (MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q) = 0 ↔ p ∣ q := by
    rw [←hkp]
    have hv : (fun o : Option (Fin (h+1)) => Ideal.Quotient.mk I (o.elim x (a ∘ j))) =
        (fun o => o.elim (Ideal.Quotient.mk I x) ((fun i => Ideal.Quotient.mk I (a i)) ∘ j)) := by
      funext o
      cases o <;> rfl
    change (Ideal.Quotient.mkₐ K I) (MvPolynomial.aeval _ q) = 0 ↔ _
    rw [MvPolynomial.comp_aeval_apply]
    change MvPolynomial.aeval (fun o : Option (Fin (h+1)) => Ideal.Quotient.mk I (o.elim x (a ∘ j))) q = 0 ↔ _
    rw [hv]
  refine ⟨j,hj,p,hp,?_,hker⟩
  have hb := affine_polynomial_projection_degree_bound (finSuccEquiv (h+1)) I hdim
    (fun o => o.elim x (a ∘ j)) D hD (by intro o; cases o with
      | none => exact hxdeg
      | some i => exact hadeg (j i)) p hp.ne_zero hker
  have hb' : (p.totalDegree:ℚ) ≤ (E:ℚ)*(D:ℚ)^(h+1) :=
    hb.trans (mul_le_mul_of_nonneg_right hdeg (by positivity))
  exact_mod_cast hb'

theorem rootPairEvaluation_projection {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i))
    (p : MvPolynomial (Option (Fin d)) K) :
    rootPairEvaluation k θ a b x hab
      (positiveToPair k (rootPairQ θ) (optionEquivRight K (Fin d) p)) =
      MvPolynomial.aeval (fun o => o.elim x a) p := by
  rw [positiveToPair_option,MvPolynomial.comp_aeval_apply]
  congr 1
  congr 1
  funext o
  cases o with
  | none => exact rootPairEvaluation_number k θ a b x hab
  | some i => exact rootPairEvaluation_left k θ a b x hab i

theorem rootPairEvaluation_comp_kernel {d : ℕ} {K S L : Type*}
    [Field K] [CommRing S] [CommRing L] [Algebra K S] [Algebra K L]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i))
    (e : S →ₐ[K] L) (he : Function.Injective e)
    (p : MvPolynomial (Option (Fin d)) K)
    (hker : ∀ q, MvPolynomial.aeval (fun o => o.elim x a) q = 0 ↔ p ∣ q) :
    ∀ q, (e.comp (rootPairEvaluation k θ a b x hab))
      (positiveToPair k (rootPairQ θ) q) = 0 ↔
        MvPolynomial.optionEquivRight K (Fin d) p ∣ q := by
  intro q
  let E := MvPolynomial.optionEquivRight K (Fin d)
  let q₀ := E.symm q
  have heq : E q₀ = q := E.apply_symm_apply q
  rw [←heq,AlgHom.comp_apply,rootPairEvaluation_projection,map_eq_zero_iff e he,hker]
  exact (map_dvd_iff E).symm

end
section
universe u v
open scoped BigOperators
theorem rootPair_actual_hilbert_uniform_allFields {n : ℕ} {K : Type u} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (E : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Type v) [Field L] [Algebra K L], ∀ (θ : Fin (n+1) → K), Function.Injective θ →
      ∀ (ψ : RootPair k θ →ₐ[K] L), (∀ i, ψ (pairLeft k (rootPairQ θ) i) ≠ 0) →
      ∀ (p : MvPolynomial (Option (Fin (n+1))) K), p ≠ 0 → p.totalDegree ≤ E →
      (∀ q, ψ (positiveToPair k (rootPairQ θ) q) = 0 ↔
        MvPolynomial.optionEquivRight K (Fin (n+1)) p ∣ q) →
      ∃ u v : ℕ, min A B ≤ A*u+B*v ∧ A*u+B*v ≤ (k*A+B)*E ∧
        ∀ T : ℕ, (k*A+B)*E ≤ T →
        |(Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference θ)) T).map
          (ψ.comp (pairConeToRoot k A B θ)).toLinearMap) : ℝ) -
          ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
            (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
          C*((T:ℝ)+1)^n := by
  classical
  let M := (k*A+B)*E
  choose C hC0 hC using fun u v =>
    pairAffine_cut_hilbert_uniform (n := n) (K := K) k A B hA hB u v
  let Ctotal : ℝ := ∑ u ∈ Finset.range (M+1), ∑ v ∈ Finset.range (M+1), C u v
  have htotal : 0 ≤ Ctotal := Finset.sum_nonneg fun u _ =>
    Finset.sum_nonneg fun v _ => hC0 u v
  refine ⟨Ctotal,htotal,fun L _ _ θ hθ ψ ha p hp hpE hker => ?_⟩
  obtain ⟨u,v,c,hD,hc,hc0,hct,hkerφ⟩ := rootPair_bounded_cone_kernel hk A B hB θ hθ ψ ha p hp hker
  let φ := ψ.comp (pairConeToRoot k A B θ)
  have hφc : φ c = 0 := by
    apply (show c ∈ RingHom.ker φ.toRingHom ↔ φ c = 0 from Iff.rfl).mp
    rw [hkerφ]
    exact (show Ideal.span {c} ≤ _ from le_sup_left) (Ideal.subset_span (Set.mem_singleton _))
  have hDpos : A*u+B*v ≠ 0 := by
    intro hh
    have hu := (pairCone_degree_zero_isUnit k A B hA hB (coneDifference θ) c hc0 (hh ▸ hc)).map φ
    exact hu.ne_zero hφc
  have hDlower : min A B ≤ A*u+B*v := by
    by_cases hu : u = 0
    · have hv : 1 ≤ v := by
        by_contra hh
        have hv0 : v = 0 := by omega
        exact hDpos (by simp [hu,hv0])
      exact (min_le_right A B).trans ((show B ≤ B*v by simpa using Nat.mul_le_mul_left B hv).trans (Nat.le_add_left _ _))
    · exact (min_le_left A B).trans ((show A ≤ A*u by simpa using Nat.mul_le_mul_left A (Nat.one_le_iff_ne_zero.mpr hu)).trans (Nat.le_add_right _ _))
  have hbound : A*u+B*v ≤ M := hD.trans (Nat.mul_le_mul_left _ hpE)
  have hu : u ≤ M := le_trans (le_trans (by simpa using Nat.mul_le_mul_right u hA)
    (Nat.le_add_right (A*u) (B*v))) hbound
  have hv : v ≤ M := le_trans (le_trans (by simpa using Nat.mul_le_mul_right v hB)
    (Nat.le_add_left (B*v) (A*u))) hbound
  have hsum : C u v ≤ Ctotal := by
    calc C u v ≤ ∑ j ∈ Finset.range (M+1), C u j :=
          Finset.single_le_sum (fun j _ => hC0 u j) (Finset.mem_range.mpr (by omega))
      _ ≤ Ctotal := Finset.single_le_sum (fun i _ =>
          Finset.sum_nonneg (fun j _ => hC0 i j)) (Finset.mem_range.mpr (by omega))
  refine ⟨u,v,hDlower,hbound,fun T hT => ?_⟩
  have hh := hC u v (coneDifference θ) c hc0 hc hct T (hbound.trans hT)
  rw [finrank_map_quotient_kernel φ _ hkerφ] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hsum (by positivity))

end
section
open MvPolynomial
open scoped BigOperators

theorem pairCone_homogeneous_image_le {n : ℕ} {σ K S : Type*}
    [Fintype σ] [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S) (g : MvPolynomial σ K →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (X 2)) = 1)
    (a b : Fin (n+1) → MvPolynomial σ K) (w : σ → ℕ)
    (ha : ∀ i, a i ∈ weightedSpace w A) (hb : ∀ i, b i ∈ weightedSpace w B)
    (hφa : ∀ i, φ (pairConeA k A B θ i) = g (a i))
    (hφb : ∀ i, φ (pairConeB k A B θ i) = g (b i)) (T : ℕ) :
    (homogeneousSpace (pairConeScale k A B θ) T).map φ.toLinearMap ≤
      (weightedSpace w T).map g.toLinearMap := by
  classical
  rintro y ⟨c,hc,rfl⟩
  let p := pairConePolynomial k A B hB θ c
  let z := Sum.elim a b
  let v : Fin (n+1) ⊕ Fin (n+1) → ℕ := Sum.elim (fun _ => A) (fun _ => B)
  have hp : p ∈ weightedSpace v T := by
    intro m hm
    have hh := pairConePolynomial_weight k A B hB θ c T
      ((mem_homogeneousSpace _ _ _).mp hc) m hm
    have he : Finsupp.weight v m = A*(∑ i, m (Sum.inl i))+ B*(∑ i, m (Sum.inr i)) := by
      rw [Finsupp.weight_eq_sum,Fintype.sum_sum_type]
      simp only [v,Sum.elim_inl,Sum.elim_inr,nsmul_eq_mul,Nat.cast_id,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    change Finsupp.weight v m ≤ T
    rwa [he]
  have hz : ∀ i, z i ∈ weightedSpace w (v i) := by
    intro i
    cases i with
    | inl i => exact ha i
    | inr i => exact hb i
  refine ⟨MvPolynomial.aeval z p,weightedSpace_aeval v w z hz p T hp,?_⟩
  change g (MvPolynomial.aeval z p) = φ c
  rw [MvPolynomial.comp_aeval_apply]
  have hv : g ∘ z = Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ) := by
    funext i
    cases i with
    | inl i => exact (hφa i).symm
    | inr i => exact (hφb i).symm
  change MvPolynomial.aeval (g ∘ z) p = φ c
  rw [hv]
  exact pairConePolynomial_eval k A B hB θ φ ht c

theorem rootPair_actual_hilbert_le {n N : ℕ} {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial (Fin N) K))
    (e : (MvPolynomial (Fin N) K ⧸ I) →ₐ[K] L) (he : Function.Injective e)
    (k A B : ℕ) (hB : 0 < B) (θ : Fin (n+1) → K)
    (ψ : RootPair k θ →ₐ[K] L)
    (a b : Fin (n+1) → MvPolynomial (Fin N) K) (w : Fin N → ℕ)
    (hw : ∀ i, w i ≠ 0)
    (ha : ∀ i, a i ∈ weightedSpace w A) (hb : ∀ i, b i ∈ weightedSpace w B)
    (hψa : ∀ i, ψ (pairLeft k (rootPairQ θ) i) = e (Ideal.Quotient.mk I (a i)))
    (hψb : ∀ i, ψ (pairRight k (rootPairQ θ) i) = e (Ideal.Quotient.mk I (b i))) (T : ℕ) :
    Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference θ)) T).map
      (ψ.comp (pairConeToRoot k A B θ)).toLinearMap) ≤
    Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  let g := e.comp (Ideal.Quotient.mkₐ K I)
  have := weightedSpace_finite (K := K) w hw T
  have hh := pairCone_homogeneous_image_le k A B hB (coneDifference θ)
    (ψ.comp (pairConeToRoot k A B θ)) g (by simp) a b w ha hb
    (fun i => by simpa only [g,AlgHom.comp_apply,Ideal.Quotient.mkₐ_eq_mk,pairConeToRoot_left] using hψa i)
    (fun i => by simpa only [g,AlgHom.comp_apply,Ideal.Quotient.mkₐ_eq_mk,pairConeToRoot_right] using hψb i) T
  have hr : Module.finrank K ((weightedSpace w T).map g.toLinearMap) =
      Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
    apply finrank_map_eq_of_kernel_eq
    ext p
    change e (Ideal.Quotient.mk I p) = 0 ↔ Ideal.Quotient.mk I p = 0
    exact map_eq_zero_iff e he
  exact (Submodule.finrank_mono hh).trans_eq hr

end
open MvPolynomial

universe u

theorem norm_ambient_hilbert_uniform {n d h : ℕ} {K : Type u} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (E D : ℕ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
        (θ : Fin d → K), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ i)) →
      Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ →
      Transcendental K (Ideal.Quotient.mk I x) →
      affineDimension I = h+1 → h+1 ≤ d → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → x.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ T : ℕ, (k*A+B)*(E*D^(h+1)) ≤ T →
        ((min A B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
          (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+1) -
          C*((T:ℝ)+1)^h ≤
          (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℝ) := by
  obtain ⟨C,hC,hunif⟩ := rootPair_actual_hilbert_uniform_allFields.{u,u}
    (n := h) (K := K) hk A B hA hB (E*D^(h+1))
  refine ⟨C,hC,fun I _ a b x θ hθ ha hab hgen hx hdim hd hdeg hadeg hxdeg w hw haw hbw T hT => ?_⟩
  obtain ⟨j,hj,p,hp,hpD,hkp⟩ := norm_projection_bounded I k a b x θ ha hab hgen hx
    hdim hd E D hD hdeg hadeg hxdeg
  let S := MvPolynomial (Fin n) K ⧸ I
  let L := FractionRing S
  let e : S →ₐ[K] L := IsScalarTower.toAlgHom K S L
  have he : Function.Injective e := IsFractionRing.injective S L
  let aj : Fin (h+1) → S := fun i => Ideal.Quotient.mk I (a (j i))
  let bj : Fin (h+1) → S := fun i => Ideal.Quotient.mk I (b (j i))
  let xj : S := Ideal.Quotient.mk I x
  have habj : ∀ i, aj i ^ k * bj i = xj - algebraMap K S ((θ ∘ j) i) := fun i => hab (j i)
  let ψ : RootPair k (θ ∘ j) →ₐ[K] L := e.comp (rootPairEvaluation k (θ ∘ j) aj bj xj habj)
  have hψa (i) : ψ (pairLeft k (rootPairQ (θ ∘ j)) i) = e (Ideal.Quotient.mk I (a (j i))) := by
    simp only [ψ,AlgHom.comp_apply,rootPairEvaluation_left,aj]
  have hψb (i) : ψ (pairRight k (rootPairQ (θ ∘ j)) i) = e (Ideal.Quotient.mk I (b (j i))) := by
    simp only [ψ,AlgHom.comp_apply,rootPairEvaluation_right,bj]
  have hpa (i) : ψ (pairLeft k (rootPairQ (θ ∘ j)) i) ≠ 0 := by
    rw [hψa,map_ne_zero_iff e he]
    exact ha (j i)
  have hproj (q) : MvPolynomial.aeval (fun o => o.elim xj aj) q = 0 ↔ p ∣ q := by
    rw [←hkp]
    have hh := MvPolynomial.comp_aeval_apply
      (f := fun o : Option (Fin (h+1)) => o.elim x (a ∘ j)) (Ideal.Quotient.mkₐ K I) q
    have hv : (fun o : Option (Fin (h+1)) => (Ideal.Quotient.mkₐ K I) (o.elim x (a ∘ j))) =
        (fun o => o.elim xj aj) := by funext o; cases o <;> rfl
    rw [hv] at hh
    exact Iff.of_eq (congrArg (fun y => y = 0) hh.symm)
  have hker := rootPairEvaluation_comp_kernel k (θ ∘ j) aj bj xj habj e he p hproj
  obtain ⟨r,s,hmin,_,hH⟩ := hunif L (θ ∘ j) (hθ.comp hj) ψ hpa p hp.ne_zero hpD hker
  have hR := rootPair_actual_hilbert_le I e he k A B hB (θ ∘ j) ψ
    (a ∘ j) (b ∘ j) w hw (fun i => haw (j i)) (fun i => hbw (j i)) hψa hψb T
  have hH' := (abs_le.mp (hH T hT)).1
  have hcoef : ((min A B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
      (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+1) ≤
    ((A*r+B*s : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
      (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+1) := by
    gcongr
  have hR' : (Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference (θ ∘ j))) T).map
      (ψ.comp (pairConeToRoot k A B (θ ∘ j))).toLinearMap) : ℝ) ≤
      (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℝ) := by exact_mod_cast hR
  linarith

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace QuarticPowerFree

theorem uniform_real_hilbert_floor (h M : ℕ) (L α C : ℝ)
    (hL : 0 < L) (hα : 0 ≤ α) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (H : ℕ → ℝ) (G : ℝ → ℝ),
      (∀ T, 0 ≤ G T) →
      (∀ T, 1 ≤ T → H ⌊L*T⌋₊ ≤ G T) →
      (∀ N, M ≤ N → α*(N:ℝ)^(h+1)-C*((N:ℝ)+1)^h ≤ H N) →
      ∀ T, 1 ≤ T → α*L^(h+1)*T^(h+1)-c*T^h ≤ G T := by
  let c := α*(h+1)*L^h + C*(L+1)^h + α*(M:ℝ)^(h+1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c,hc,fun H G hG hi hl T hT => ?_⟩
  let N := ⌊L*T⌋₊
  have hT0 : 0 ≤ T := by linarith
  have hLT : 0 ≤ L*T := mul_nonneg hL.le hT0
  have hN : (N:ℝ) ≤ L*T := Nat.floor_le hLT
  have hN1 : L*T < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hTh : 1 ≤ T^h := one_le_pow₀ hT
  have hpowtarget : α*L^(h+1)*T^(h+1) = α*(L*T)^(h+1) := by rw [mul_pow]; ring
  rw [hpowtarget]
  by_cases hMN : M ≤ N
  · have hh := (hl N hMN).trans (hi T hT)
    have hab : |L*T-(N:ℝ)| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hN)]; linarith
    have hdiff := abs_pow_sub_pow_le (a := L*T) (b := (N:ℝ)) (n := h+1)
    rw [abs_of_nonneg hLT,abs_of_nonneg hN0,max_eq_left hN,Nat.add_sub_cancel] at hdiff
    have hdiff' : (L*T)^(h+1)-(N:ℝ)^(h+1) ≤ (h+1:ℕ)*(L*T)^h := by
      refine (le_abs_self _).trans (hdiff.trans ?_)
      calc |L*T-(N:ℝ)| * (h+1:ℕ)*(L*T)^h ≤ 1*(h+1:ℕ)*(L*T)^h := by gcongr
           _ = (h+1:ℕ)*(L*T)^h := by ring
    have hd := mul_le_mul_of_nonneg_left hdiff' hα
    have hNp : (N:ℝ)+1 ≤ (L+1)*T := by nlinarith
    have he : C*((N:ℝ)+1)^h ≤ C*(L+1)^h*T^h := by
      rw [mul_assoc,←mul_pow]
      gcongr
    have hsmall : 0 ≤ α*(M:ℝ)^(h+1)*T^h := by positivity
    simp only [mul_pow] at hd ⊢
    push_cast at hd
    dsimp only [c]
    nlinarith only [hh,hd,he,hsmall]
  · have hNM : N+1 ≤ M := by omega
    have hNM' : (N:ℝ)+1 ≤ M := by exact_mod_cast hNM
    have hM : L*T ≤ M := by linarith
    have hp : (L*T)^(h+1) ≤ (M:ℝ)^(h+1) := pow_le_pow_left₀ hLT hM _
    have hpα := mul_le_mul_of_nonneg_left hp hα
    have hscale : α*(M:ℝ)^(h+1) ≤ α*(M:ℝ)^(h+1)*T^h :=
      le_mul_of_one_le_right (by positivity) hTh
    have hother : 0 ≤ (α*(h+1)*L^h+C*(L+1)^h)*T^h := by positivity
    dsimp only [c]
    linarith [hG T]

open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_RationalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace QuarticPowerFree

section
open MvPolynomial

theorem norm_real_hilbert_uniform {n d h : ℕ} {K : Type u} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (E D : ℕ) (hD : 0 < D) (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
        (θ : Fin d → K), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ i)) →
      Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ →
      Transcendental K (Ideal.Quotient.mk I x) →
      affineDimension I = h+1 → h+1 ≤ d → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → x.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = L*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        ((min A B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h * L^(h+1) /
          (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*T^(h+1) -
          C*T^h ≤ weightedHilbert I ω T := by
  let α : ℝ := ((min A B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
    (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨C,hC,hh⟩ := norm_ambient_hilbert_uniform (n := n) (d := d) (h := h)
    (K := K) hk A B hA hB E D hD
  obtain ⟨c,hc,hr⟩ := uniform_real_hilbert_floor h ((k*A+B)*(E*D^(h+1))) L α C hL hα hC
  refine ⟨c,hc,fun I _ a b x θ hθ ha hab hgen hx hdim hd hdeg hadeg hxdeg w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hr (fun N => (Module.finrank K ((weightedSpace w N).map
        (Ideal.Quotient.mkₐ K I).toLinearMap):ℝ))
    (fun t => (weightedHilbert I ω t:ℝ))
    (fun t => Nat.cast_nonneg _)
    (fun t ht => by
      exact_mod_cast Submodule.finrank_mono
        (weightedSpace_map_le_weightedFunctions I w ω hω L hL hscale t (by linarith)))
    (hh I a b x θ hθ ha hab hgen hx hdim hd hdeg hadeg hxdeg w hw haw hbw) T hT
  dsimp only [α] at hb
  convert hb using 1; ring

end

open MvPolynomial
open scoped Classical BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical

theorem quotient_pair_generates {n d : ℕ} (a b : Fin d → MvPolynomial (Fin n) ℂ)
    (hg : Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    Algebra.adjoin ℂ (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
      Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ := by
  let e := Ideal.Quotient.mkₐ ℂ I
  have hr : Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪ Set.range (fun i => Ideal.Quotient.mk I (b i)) =
      e '' (Set.range a ∪ Set.range b) := by
    simp only [Set.image_union,← Set.range_comp]
    rfl
  rw [hr,Algebra.adjoin_image,hg]
  apply top_unique
  intro z _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I z
  exact ⟨p,by trivial,_root_.rfl⟩

end
section
open MvPolynomial

open MvPolynomial
open scoped BigOperators Classical

attribute [instance] NormBoxSystem.field NormBoxSystem.charZero

end
open MvPolynomial
open scoped BigOperators Classical

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_QuarticComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

lemma quarticA_pos (j : Fin 100) : 0 < quarticA j := by dsimp [quarticA]; omega
lemma quarticB_pos (j : Fin 100) : 0 < quarticB j := by have := j.isLt; dsimp [quarticB]; omega

lemma quartic_generic_rat : ∀ (j : Fin 100) (h : Fin 2),
    (1:ℚ)/((h.val+3).factorial*((quarticNumerator j (h.val+3):ℚ)/1000)^(h.val+3)) ≤
      min (quarticA j) (quarticB j)*(2*quarticA j+quarticB j:ℕ)^(h.val+2)*400^(h.val+3)/
        ((h.val+3).factorial*(quarticA j:ℚ)^(h.val+3)*(quarticB j:ℚ)^(h.val+3)) := by decide +kernel

lemma quartic_generic_threshold (j : Fin 100) (h : ℕ) (hh : 3 ≤ h) (hh' : h ≤ 4) :
    1/((h.factorial:ℝ)*(quarticEnvelope j h)^h) ≤
      ((min (quarticA j) (quarticB j):ℕ):ℝ)*(2*quarticA j+quarticB j:ℕ)^(h-1)*400^h/
        ((h.factorial:ℝ)*(quarticA j:ℝ)^h*(quarticB j:ℝ)^h) := by
  have hb := quartic_generic_rat j ⟨h-3,by omega⟩
  have he : h-3+3=h := by omega
  have he' : h-3+2=h-1 := by omega
  dsimp only at hb
  rw [he,he'] at hb
  dsimp only [quarticEnvelope]
  have hb' := (Rat.cast_le (K := ℝ)).mpr hb
  push_cast at hb'
  simpa only [Nat.cast_min, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hb'

end

open MvPolynomial

theorem quartic_generic_threshold_uniform_oai {n h : ℕ} (j : Fin 100)
    (hh : 3 ≤ h) (hh' : h ≤ 4) (E D : ℕ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
        (a b : Fin 4 → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
        (θ : Fin 4 → ℂ), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^2*Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I q-algebraMap ℂ _ (θ i)) →
      Algebra.adjoin ℂ (Set.range a ∪ Set.range b) = ⊤ →
      Transcendental ℂ (Ideal.Quotient.mk I q) → affineDimension I = h → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → q.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w (quarticA j)) → (∀ i, b i ∈ weightedSpace w (quarticB j)) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = 400*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        T^h/((h.factorial:ℝ)*(quarticEnvelope j h)^h)-C*T^(h-1) ≤ weightedHilbert I ω T := by
  have hsucc : h-1+1 = h := by omega
  obtain ⟨C,hC,hbound⟩ := norm_real_hilbert_uniform (n := n) (d := 4) (h := h-1) (K := ℂ)
    (k := 2) (by omega) (quarticA j) (quarticB j) (quarticA_pos j) (quarticB_pos j) E D hD 400 (by norm_num)
  refine ⟨C,hC,fun I _ a b q θ hθ ha heq hg hq hdim hdeg hadeg hqdeg w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hbound I a b q θ hθ ha heq (quotient_pair_generates a b hg I) hq
    (hsucc ▸ hdim) (hsucc ▸ hh') hdeg hadeg hqdeg w hw haw hbw ω hω hscale T hT
  rw [hsucc] at hb
  have hc := mul_le_mul_of_nonneg_right (quartic_generic_threshold j h hh hh')
    (pow_nonneg (by linarith : 0 ≤ T) h)
  have hc' : T^h/((h.factorial:ℝ)*(quarticEnvelope j h)^h) ≤
      ((min (quarticA j) (quarticB j):ℕ):ℝ)*(2*quarticA j+quarticB j:ℕ)^(h-1)*400^h/
        ((h.factorial:ℝ)*(quarticA j:ℝ)^h*(quarticB j:ℝ)^h)*T^h := by
    simpa only [one_div_mul_eq_div] using hc
  linarith only [hb,hc']

open MvPolynomial
open scoped Classical BigOperators

end QuarticPowerFree

end OAI
end

theorem solution : type_of% @OAI.QuarticPowerFree.quartic_generic_threshold_uniform_oai := @OAI.QuarticPowerFree.quartic_generic_threshold_uniform_oai
