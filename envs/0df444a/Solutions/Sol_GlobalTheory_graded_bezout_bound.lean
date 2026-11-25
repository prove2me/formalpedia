-- Prove2me | solution 1 for GlobalTheory.graded_bezout_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:22:35.155882+00:00
-- url     : https://prove2.me/submissions/515e7668-0a3d-4225-8134-71a52a9fac7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientLeOne
import Theorems.Thm_GlobalTheory_GradedBezout_exists_ringKrullDim_quotient_eq_succ
import Theorems.Thm_GlobalTheory_GradedBezout_gradedQuotDeg_bot_le
import Theorems.Thm_GlobalTheory_GradedBezout_one_le_gradedQuotDeg
import Theorems.Thm_GlobalTheory_GradedBezout_ringKrullDim_quotient_of_mem_minimalPrimes_sup
import Theorems.Thm_GlobalTheory_GradedBezout_sum_gradedQuotDeg_le
import Theorems.Thm_GlobalTheory_exists_homogeneous_notMem_of_not_le
import Theorems.Thm_GlobalTheory_isHomogeneous_of_mem_minimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Polynomial
open scoped BigOperators
namespace GlobalTheory
namespace GradedBezoutCount
open GradedBezout
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] {𝒜 : ℕ → Submodule K T}
  [GradedAlgebra 𝒜]
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
end GradedBezoutCount
open Matrix Polynomial in
open scoped BigOperators in
private theorem exists_scale_of_homogeneousCore_ker_eq {K T : Type} [Field K] [CommRing T]
    [Algebra K T] {𝒜 : ℕ → Submodule K T} [GradedAlgebra 𝒜] {φ φ' : T →ₐ[K] K} {z : T}
    (hz : z ∈ 𝒜 1) (hφz : φ z ≠ 0)
    (hcore : (Ideal.homogeneousCore 𝒜 (RingHom.ker φ)).toIdeal =
      (Ideal.homogeneousCore 𝒜 (RingHom.ker φ')).toIdeal) :
    ∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ' y = c ^ e * φ y := by
  refine ⟨φ' z / φ z, fun e y hy => ?_⟩
  have hmem : φ z ^ e • y - φ y • z ^ e ∈ 𝒜 e := by
    have hze : z ^ e ∈ 𝒜 e := by simpa using SetLike.pow_mem_graded e hz
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hze)
  have hker : φ z ^ e • y - φ y • z ^ e ∈ (Ideal.homogeneousCore 𝒜 (RingHom.ker φ)).toIdeal := by
    refine Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨e, hmem⟩ ?_
    rw [RingHom.mem_ker]
    simp only [map_sub, map_smul, map_pow, smul_eq_mul]
    ring
  rw [hcore] at hker
  have h2 := Ideal.toIdeal_homogeneousCore_le 𝒜 _ hker
  rw [RingHom.mem_ker] at h2
  simp only [map_sub, map_smul, map_pow, smul_eq_mul] at h2
  rw [div_pow]
  field_simp
  linear_combination h2
open Matrix Polynomial in
open scoped BigOperators in
private theorem sup_span_ne_top_of_homogeneous_pos_degree {K T : Type} [Field K] [CommRing T] [Algebra K T]
    {𝒜 : ℕ → Submodule K T} [GradedAlgebra 𝒜] {Q : Ideal T} (hQ : Q.IsHomogeneous 𝒜)
    (hQt : Q ≠ ⊤) {h : T} {n : ℕ} (hh : h ∈ 𝒜 n) (hn : 0 < n) : Q ⊔ Ideal.span {h} ≠ ⊤ := by
  intro htop
  have h1 : (1 : T) ∈ Q ⊔ Ideal.span {h} := htop ▸ Submodule.mem_top
  obtain ⟨q, hq, y, hy, hqy⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hy
  apply hQt
  rw [Ideal.eq_top_iff_one]
  have h0 : ((DirectSum.decompose 𝒜 (q + h * t) 0 : T)) = 1 := by
    rw [hqy]; exact DirectSum.decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
    DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hh (by omega), add_zero] at h0
  exact h0 ▸ hQ 0 hq
open Matrix Polynomial in
open scoped BigOperators in
private theorem exists_algHom_vanishing_prime_ne_zero_of_notMem {K T : Type} [Field K] [IsAlgClosed K] [CommRing T]
    [Algebra K T] [Algebra.FiniteType K T] {P : Ideal T} [hP : P.IsPrime] {y : T} (hy : y ∉ P) :
    ∃ φ : T →ₐ[K] K, (∀ z ∈ P, φ z = 0) ∧ φ y ≠ 0 := by
  haveI := isJacobsonRing_of_finiteType (A := K) (B := T)
  have hJ : P.jacobson = P := IsJacobsonRing.out' P hP.isRadical
  rw [← hJ] at hy
  simp only [Ideal.jacobson, Ideal.mem_sInf, Set.mem_setOf_eq, not_forall] at hy
  obtain ⟨m, ⟨hPm, hm⟩, hym⟩ := hy
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (T ⧸ m)
  have hsurj : Function.Surjective (algebraMap K (T ⧸ m)) :=
    IsSepClosed.algebraMap_surjective K (T ⧸ m)
  let e : K ≃ₐ[K] T ⧸ m := AlgEquiv.ofBijective (Algebra.ofId K (T ⧸ m))
    ⟨(algebraMap K (T ⧸ m)).injective, hsurj⟩
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m), fun z hz => ?_, ?_⟩
  · simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hPm hz)]
  · intro h0
    apply hym
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using h0
open Matrix Polynomial in
open scoped BigOperators in
private theorem exists_mem_notMem_homogeneous_prime_of_finite_points {K T : Type} [Field K] [IsAlgClosed K] [CommRing T]
    [IsDomain T] [Algebra K T] {𝒜 : ℕ → Submodule K T} [GradedAlgebra 𝒜] {m : ℕ} {x : Fin m → T}
    (hx : ∀ i, x i ∈ 𝒜 1) (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
    {F : Set T} (hΦ : ∃ Φ : Set (T →ₐ[K] K), Φ.Finite ∧ ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) →
      (∀ f ∈ F, φ f = 0) → ∃ ψ ∈ Φ, (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y))
    {Q : Ideal T} [hQp : Q.IsPrime] (hQ : Q.IsHomogeneous 𝒜) {k : ℕ}
    (hdim : ringKrullDim (T ⧸ Q) = (k + 1 + 1 : ℕ)) : ∃ f ∈ F, f ∉ Q := by
  classical
  haveI : Algebra.FiniteType K T := _root_.GlobalTheory.GradedBezout.finiteType hfin
  by_contra! hFQ
  obtain ⟨Φ, hΦfin, hΦ⟩ := hΦ
  let G : Finset (T →ₐ[K] K) := hΦfin.toFinset.filter (fun ψ => ∃ i, ψ (x i) ≠ 0)
  let pol : (T →ₐ[K] K) → K[X] := fun ψ =>
    ∑ i : Fin m, Polynomial.C (ψ (x i)) * Polynomial.X ^ (i : ℕ)
  have hpol : ∀ ψ ∈ G, pol ψ ≠ 0 := by
    intro ψ hψ h0
    obtain ⟨-, i, hi⟩ := Finset.mem_filter.mp hψ
    have hc := congrArg (fun p : K[X] => p.coeff (i : ℕ)) h0
    simp [pol, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Fin.val_inj] at hc
    exact hi hc
  have hp : (∏ ψ ∈ G, pol ψ) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpol
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (∏ ψ ∈ G, pol ψ).roots.toFinset
  have heval : ∀ ψ ∈ G, (pol ψ).eval t ≠ 0 := by
    intro ψ hψ h0
    apply ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero hψ h0
  let h : T := ∑ i : Fin m, t ^ (i : ℕ) • x i
  have hh1 : h ∈ 𝒜 1 := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hx i)
  have hψh : ∀ ψ : T →ₐ[K] K, ψ h = (pol ψ).eval t := by
    intro ψ
    simp only [h, pol, map_sum, map_smul, smul_eq_mul, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hne : Q ⊔ Ideal.span {h} ≠ ⊤ :=
    sup_span_ne_top_of_homogeneous_pos_degree hQ hQp.ne_top hh1 one_pos
  obtain ⟨Q', hQ'⟩ := Ideal.nonempty_minimalPrimes hne
  haveI : Q'.IsPrime := hQ'.1.1
  have hQQ' : Q ⊔ Ideal.span {h} ≤ Q' := hQ'.1.2
  have hj : ∃ j, x j ∉ Q' := by
    by_contra! hall
    have hle := _root_.GlobalTheory.GradedBezout.ringKrullDim_quotient_le_zero hfin hall
    by_cases hhQ : h ∈ Q
    · have hsup : Q ⊔ Ideal.span {h} = Q :=
        sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hhQ)
      have hQ'Q : Q' = Q := by
        have hmem : Q' ∈ (Q ⊔ Ideal.span {h}).minimalPrimes := hQ'
        rw [hsup, Ideal.minimalPrimes_eq_subsingleton_self] at hmem
        exact hmem
      rw [hQ'Q, hdim] at hle
      have : k + 1 + 1 ≤ 0 := by exact_mod_cast hle
      omega
    · rw [_root_.GlobalTheory.GradedBezout.ringKrullDim_quotient_of_mem_minimalPrimes_sup hfin hdim hhQ hQ'] at hle
      have : k + 1 ≤ 0 := by exact_mod_cast hle
      omega
  obtain ⟨j, hj⟩ := hj
  obtain ⟨φ, hφQ', hφj⟩ := exists_algHom_vanishing_prime_ne_zero_of_notMem (K := K) hj
  have hφF : ∀ f ∈ F, φ f = 0 := fun f hf => hφQ' f (hQQ' (Ideal.mem_sup_left (hFQ f hf)))
  obtain ⟨ψ, hψΦ, c, hc⟩ := hΦ φ ⟨j, hφj⟩ hφF
  have h1 := hc 1 (x j) (hx j)
  rw [pow_one] at h1
  have hψj : ψ (x j) ≠ 0 := fun h0 => hφj (by rw [h1, h0, mul_zero])
  have hc0 : c ≠ 0 := fun h0 => hφj (by rw [h1, h0, zero_mul])
  have hψG : ψ ∈ G := Finset.mem_filter.mpr ⟨hΦfin.mem_toFinset.mpr hψΦ, j, hψj⟩
  have hφh : φ h = 0 :=
    hφQ' h (hQQ' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h)))
  have h2 := hc 1 h hh1
  rw [hφh, pow_one, hψh] at h2
  exact mul_ne_zero hc0 (heval ψ hψG) h2.symm
open Matrix Polynomial in
open scoped BigOperators in
private theorem card_le_of_points_lemma_2 {K T : Type} [Field K] [IsAlgClosed K] [CommRing T]
    [IsDomain T] [Algebra K T] {𝒜 : ℕ → Submodule K T} [GradedAlgebra 𝒜] {m : ℕ} {x : Fin m → T}
    (hx : ∀ i, x i ∈ 𝒜 1) (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
    {F : Set T} {a : ℕ} (hF : ∀ f ∈ F, f ∈ 𝒜 a)
    (hΦ : ∃ Φ : Set (T →ₐ[K] K), Φ.Finite ∧ ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) →
      (∀ f ∈ F, φ f = 0) → ∃ ψ ∈ Φ, (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y))
    (k : ℕ) : ∀ (Q : Ideal T) [Q.IsPrime], Q.IsHomogeneous 𝒜 →
      ringKrullDim (T ⧸ Q) = (k + 1 : ℕ) → ∀ J : Finset (Ideal T),
      (∀ P ∈ J, P.IsPrime ∧ P.IsHomogeneous 𝒜 ∧ Q ≤ P ∧ (∀ f ∈ F, f ∈ P) ∧ ∃ i, x i ∉ P) →
      (J.card : ℚ) ≤ (a : ℚ) ^ k * _root_.GlobalTheory.gradedQuotDeg 𝒜 k Q := by
  classical
  haveI : IsNoetherianRing T := _root_.GlobalTheory.GradedBezout.isNoetherianRing hfin
  induction k with
  | zero =>
    intro Q _ hQ hdim J hJ
    have heq : ∀ P ∈ J, P = Q := by
      intro P hP
      obtain ⟨hPp, hPh, hQP, -, i, hi⟩ := hJ P hP
      by_contra hne
      have hPQ : ¬ P ≤ Q := fun h => hne (le_antisymm h hQP)
      obtain ⟨n, y, hy, hyP, hyQ⟩ := _root_.GlobalTheory.exists_homogeneous_notMem_of_not_le 𝒜 hPh hPQ
      obtain ⟨Q'', hQ'', hQ''P⟩ := Ideal.exists_minimalPrimes_le (J := P)
        (sup_le hQP ((Ideal.span_singleton_le_iff_mem _).mpr hyP))
      haveI : Q''.IsPrime := hQ''.1.1
      have hd0 := _root_.GlobalTheory.GradedBezout.ringKrullDim_quotient_of_mem_minimalPrimes_sup hfin (r := 0) hdim hyQ hQ''
      have hQ''h : Q''.IsHomogeneous 𝒜 := _root_.GlobalTheory.isHomogeneous_of_mem_minimalPrimes 𝒜
        (_root_.GlobalTheory.GradedBezout.isHomogeneous_sup_span hQ hy) hQ''
      obtain ⟨e, he⟩ := _root_.GlobalTheory.GradedBezout.exists_ringKrullDim_quotient_eq_succ hx hfin hQ''h (i := i)
        (fun h => hi (hQ''P h))
      rw [hd0] at he
      have : (0 : ℕ) = e + 1 := by exact_mod_cast he
      omega
    have hcard : J.card ≤ 1 :=
      Finset.card_le_one.mpr fun P hP P' hP' => (heq P hP).trans (heq P' hP').symm
    have h1 := _root_.GlobalTheory.GradedBezout.one_le_gradedQuotDeg hx hfin hQ (r := 0) hdim
    simp only [pow_zero, one_mul]
    calc (J.card : ℚ) ≤ 1 := by exact_mod_cast hcard
      _ ≤ _ := h1
  | succ k ih =>
    intro Q _ hQ hdim J hJ
    obtain ⟨f, hfF, hfQ⟩ := exists_mem_notMem_homogeneous_prime_of_finite_points hx hfin hΦ hQ hdim
    have hfa := hF f hfF
    have hMfin := Ideal.finite_minimalPrimes_of_isNoetherianRing T (Q ⊔ Ideal.span {f})
    have hsub : J ⊆ hMfin.toFinset.biUnion (fun Q' => J.filter (fun P => Q' ≤ P)) := by
      intro P hP
      obtain ⟨hPp, -, hQP, hFP, -⟩ := hJ P hP
      obtain ⟨Q', hQ', hQ'P⟩ := Ideal.exists_minimalPrimes_le (J := P)
        (sup_le hQP ((Ideal.span_singleton_le_iff_mem _).mpr (hFP f hfF)))
      exact Finset.mem_biUnion.mpr
        ⟨Q', hMfin.mem_toFinset.mpr hQ', Finset.mem_filter.mpr ⟨hP, hQ'P⟩⟩
    have hterm : ∀ Q' ∈ hMfin.toFinset, ((J.filter (fun P => Q' ≤ P)).card : ℚ) ≤
        (a : ℚ) ^ k * _root_.GlobalTheory.gradedQuotDeg 𝒜 k Q' := by
      intro Q' hQ'
      rw [Set.Finite.mem_toFinset] at hQ'
      haveI : Q'.IsPrime := hQ'.1.1
      refine ih Q' (_root_.GlobalTheory.isHomogeneous_of_mem_minimalPrimes 𝒜
        (_root_.GlobalTheory.GradedBezout.isHomogeneous_sup_span hQ hfa) hQ')
        (_root_.GlobalTheory.GradedBezout.ringKrullDim_quotient_of_mem_minimalPrimes_sup hfin hdim hfQ hQ') _ ?_
      intro P hP
      obtain ⟨hPJ, hQ'P⟩ := Finset.mem_filter.mp hP
      obtain ⟨h1, h2, -, h4, h5⟩ := hJ P hPJ
      exact ⟨h1, h2, hQ'P, h4, h5⟩
    have hsum := _root_.GlobalTheory.GradedBezout.sum_gradedQuotDeg_le hx hfin hQ (e := k) hdim hfa hfQ
      hMfin.toFinset (fun Q' hQ' => hMfin.mem_toFinset.mp hQ')
    calc (J.card : ℚ)
        ≤ ((hMfin.toFinset.biUnion (fun Q' => J.filter (fun P => Q' ≤ P))).card : ℚ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ Q' ∈ hMfin.toFinset, ((J.filter (fun P => Q' ≤ P)).card : ℚ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ Q' ∈ hMfin.toFinset, (a : ℚ) ^ k * _root_.GlobalTheory.gradedQuotDeg 𝒜 k Q' := Finset.sum_le_sum hterm
      _ = (a : ℚ) ^ k * ∑ Q' ∈ hMfin.toFinset, _root_.GlobalTheory.gradedQuotDeg 𝒜 k Q' := by rw [Finset.mul_sum]
      _ ≤ (a : ℚ) ^ k * ((a : ℚ) * _root_.GlobalTheory.gradedQuotDeg 𝒜 (k + 1) Q) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (a : ℚ) ^ (k + 1) * _root_.GlobalTheory.gradedQuotDeg 𝒜 (k + 1) Q := by ring
end GlobalTheory
end

set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
open Matrix Polynomial
open scoped BigOperators
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (K T : Type) [Field K] [IsAlgClosed K] [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m g N d a : ℕ) (x : Fin m → T) (s : T) (F : Set T), 1 ≤ g → (∀ i, x i ∈ 𝒜 1) → Module.Finite (Algebra.adjoin K (Set.range x)) T → ringKrullDim T = (g + 1 : ℕ) → (∀ e, 1 ≤ e → Module.finrank K (𝒜 e) ≤ (N * e) ^ g) → s ∈ 𝒜 d → s ≠ 0 → (∀ f ∈ F, f ∈ 𝒜 a) → (∃ Φ : Set (T →ₐ[K] K), Φ.Finite ∧ ∀ φ : T →ₐ[K] K, (∃ i, φ (x i) ≠ 0) → (∀ f ∈ F, φ f = 0) → ∃ ψ ∈ Φ, (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ y = c ^ e * ψ y)) → ∀ (n : ℕ) (φ : Fin n → (T →ₐ[K] K)), (∀ j, ∃ i, φ j (x i) ≠ 0) → (∀ j, φ j s = 0 ∧ ∀ f ∈ F, φ j f = 0) → (∀ j j', (∃ c : K, ∀ (e : ℕ), ∀ y ∈ 𝒜 e, φ j' y = c ^ e * φ j y) → j = j') → n ≤ N ^ g * g.factorial * d * a ^ (g - 1)) := by
  intro K T _ _ _ _ _ 𝒜 _ m g N d a x s F hg hx hfin hdim hN hs hs0 hF hΦ n φ hφx hφ hinj
  classical
  haveI : IsNoetherianRing T := _root_.GlobalTheory.GradedBezout.isNoetherianRing hfin
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  let core : Fin n → Ideal T := fun j => (Ideal.homogeneousCore 𝒜 (RingHom.ker (φ j))).toIdeal
  have hcore_prime : ∀ j, (core j).IsPrime := fun j =>
    Ideal.IsPrime.homogeneousCore (RingHom.ker_isPrime _)
  have hcore_hom : ∀ j, (core j).IsHomogeneous 𝒜 := fun j =>
    (Ideal.homogeneousCore 𝒜 _).isHomogeneous
  have hcore_mem : ∀ j e y, y ∈ 𝒜 e → φ j y = 0 → y ∈ core j := fun j e y hy h0 =>
    Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨e, hy⟩ (RingHom.mem_ker.mpr h0)
  have hcore_x : ∀ j, ∃ i, x i ∉ core j := by
    intro j
    obtain ⟨i, hi⟩ := hφx j
    exact ⟨i, fun h => hi (RingHom.mem_ker.mp (Ideal.toIdeal_homogeneousCore_le 𝒜 _ h))⟩
  have hinjc : Function.Injective core := by
    intro j j' hjj
    obtain ⟨i, hi⟩ := hφx j
    exact hinj j j' (exists_scale_of_homogeneousCore_ker_eq (hx i) hi hjj)
  let J := Finset.univ.image core
  have hJcard : J.card = n := by
    rw [Finset.card_image_of_injective _ hinjc, Finset.card_univ, Fintype.card_fin]
  haveI : (⊥ : Ideal T).IsPrime := Ideal.bot_prime
  have hbot_h : (⊥ : Ideal T).IsHomogeneous 𝒜 := by
    intro i r hr
    rw [Ideal.mem_bot] at hr ⊢
    simp [hr]
  have hdim0 : ringKrullDim (T ⧸ (⊥ : Ideal T)) = (g + 1 + 1 : ℕ) := by
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot T), hdim]
  have hs0' : s ∉ (⊥ : Ideal T) := by simpa using hs0
  have hMfin := Ideal.finite_minimalPrimes_of_isNoetherianRing T ((⊥ : Ideal T) ⊔ Ideal.span {s})
  have hsub : J ⊆ hMfin.toFinset.biUnion (fun Q' => J.filter (fun P => Q' ≤ P)) := by
    intro P hP
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hP
    haveI := hcore_prime j
    obtain ⟨Q', hQ', hQ'P⟩ := Ideal.exists_minimalPrimes_le (J := core j)
      (sup_le bot_le ((Ideal.span_singleton_le_iff_mem _).mpr (hcore_mem j d s hs (hφ j).1)))
    exact Finset.mem_biUnion.mpr
      ⟨Q', hMfin.mem_toFinset.mpr hQ', Finset.mem_filter.mpr ⟨hP, hQ'P⟩⟩
  have hterm : ∀ Q' ∈ hMfin.toFinset, ((J.filter (fun P => Q' ≤ P)).card : ℚ) ≤
      (a : ℚ) ^ g * _root_.GlobalTheory.gradedQuotDeg 𝒜 g Q' := by
    intro Q' hQ'
    rw [Set.Finite.mem_toFinset] at hQ'
    haveI : Q'.IsPrime := hQ'.1.1
    refine card_le_of_points_lemma_2 hx hfin hF hΦ g Q' (_root_.GlobalTheory.isHomogeneous_of_mem_minimalPrimes
      𝒜 (_root_.GlobalTheory.GradedBezout.isHomogeneous_sup_span hbot_h hs) hQ')
      (_root_.GlobalTheory.GradedBezout.ringKrullDim_quotient_of_mem_minimalPrimes_sup hfin hdim0 hs0' hQ') _ ?_
    intro P hP
    obtain ⟨hPJ, hQ'P⟩ := Finset.mem_filter.mp hP
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hPJ
    exact ⟨hcore_prime j, hcore_hom j, hQ'P,
      fun f hf => hcore_mem j a f (hF f hf) ((hφ j).2 f hf), hcore_x j⟩
  have hsum := _root_.GlobalTheory.GradedBezout.sum_gradedQuotDeg_le hx hfin hbot_h (e := g) hdim0 hs hs0'
    hMfin.toFinset (fun Q' hQ' => hMfin.mem_toFinset.mp hQ')
  have hbound := _root_.GlobalTheory.GradedBezout.gradedQuotDeg_bot_le hx hfin (r := g + 1) (c := (N : ℚ))
    (Filter.eventually_atTop.mpr ⟨1, fun e he => by exact_mod_cast hN e he⟩)
  have key : (n : ℚ) ≤ (a : ℚ) ^ g * ((d : ℚ) * (((g + 1).factorial : ℚ) * (N : ℚ) ^ (g + 1))) := by
    rw [← hJcard]
    calc (J.card : ℚ)
        ≤ ((hMfin.toFinset.biUnion (fun Q' => J.filter (fun P => Q' ≤ P))).card : ℚ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ Q' ∈ hMfin.toFinset, ((J.filter (fun P => Q' ≤ P)).card : ℚ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ Q' ∈ hMfin.toFinset, (a : ℚ) ^ g * _root_.GlobalTheory.gradedQuotDeg 𝒜 g Q' := Finset.sum_le_sum hterm
      _ = (a : ℚ) ^ g * ∑ Q' ∈ hMfin.toFinset, _root_.GlobalTheory.gradedQuotDeg 𝒜 g Q' := by rw [Finset.mul_sum]
      _ ≤ (a : ℚ) ^ g * ((d : ℚ) * _root_.GlobalTheory.gradedQuotDeg 𝒜 (g + 1) ⊥) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := by gcongr
  have hfinal : (n : ℚ) ≤ ((N ^ (g + 1) * (g + 1).factorial * d * a ^ (g + 1 - 1) : ℕ) : ℚ) := by
    rw [Nat.add_sub_cancel]
    push_cast
    linarith [key]
  exact_mod_cast hfinal
end _root_.GlobalTheory
end GlobalTheory
