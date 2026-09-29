-- Prove2me | solution 1 for Localization.AtPrime.mem_range_of_forall_branch_of_forall_comap_eq_bot_and_valuation_dichotomy_of_map_eq_iInf_tensorProduct_valuationSubring_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e44bc098-fd9c-5ed0-9ada-d69895e4ae88

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Localization_AtPrime_mem_range_of_forall_branch_of_forall_comap_eq_bot_and_valuation_dichotomy_of_map_eq_iInf_tensorProduct_valuationSubring_of_liesOverPrime

set_option autoImplicit false

open IsLocalRing
open scoped TensorProduct

namespace LocalPlAlgebra

theorem exists_pow_mul_eq_algebraMap {S K : Type*} [CommRing S] [CommRing K] [Algebra S K]
    (p : S) (f : K)
    (h2 : ∀ 𝔮 : Ideal S, 𝔮.IsPrime → p ∉ 𝔮 → ∃ a s : S, s ∉ 𝔮 ∧ f * algebraMap S K s = algebraMap S K a) :
    ∃ (N : ℕ) (a : S), f * algebraMap S K (p ^ N) = algebraMap S K a := by
  classical
  let D : Ideal S :=
    { carrier := {s | ∃ a : S, f * algebraMap S K s = algebraMap S K a}
      add_mem' := by
        rintro s t ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', by rw [map_add, mul_add, ha, ha', map_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c s ⟨a, ha⟩
        exact ⟨c * a, by rw [smul_eq_mul, map_mul, mul_left_comm, ha, map_mul]⟩ }
  have hD : ∀ s : S, s ∈ D ↔ ∃ a : S, f * algebraMap S K s = algebraMap S K a := fun s => Iff.rfl
  have hrad : p ∈ D.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hDJ, hJ⟩
    by_contra hpJ
    obtain ⟨a, s, hs, hsa⟩ := h2 J hJ hpJ
    exact hs (hDJ ((hD s).mpr ⟨a, hsa⟩))
  obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff).mp hrad
  exact ⟨n, (hD _).mp hn⟩

theorem exists_eq_pow_mul_of_mul_eq_pow_mul {T : Type*} [CommRing T] (ϖ : T)
    (hϖ : (Ideal.span {ϖ} : Ideal T).IsPrime) (hreg : ϖ ∈ nonZeroDivisors T)
    (k : ℕ) (X Y Z : T) (hY : Y ∉ Ideal.span {ϖ}) (h : X * Y = ϖ ^ k * Z) :
    ∃ W : T, X = ϖ ^ k * W := by
  induction k generalizing X Z with
  | zero => exact ⟨X, by simp⟩
  | succ k ih =>
    have h1 : X * Y ∈ (Ideal.span {ϖ} : Ideal T) := by
      rw [h, pow_succ']
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ))
    have h2 : X ∈ (Ideal.span {ϖ} : Ideal T) := (hϖ.mem_or_mem h1).resolve_right hY
    obtain ⟨X', rfl⟩ := Ideal.mem_span_singleton'.mp h2
    have h3 : (X' * Y) * ϖ = (ϖ ^ k * Z) * ϖ := by
      have e1 : X' * ϖ * Y = (X' * Y) * ϖ := by ring
      have e2 : ϖ ^ (k + 1) * Z = (ϖ ^ k * Z) * ϖ := by ring
      rw [← e1, ← e2]; exact h
    have h4 : X' * Y = ϖ ^ k * Z := (mul_cancel_right_mem_nonZeroDivisors hreg).mp h3
    obtain ⟨W, hW⟩ := ih X' Z h4
    exact ⟨W, by rw [hW]; ring⟩

theorem tmul_one_mem_nonZeroDivisors {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R B] (a : A) (ha : a ∈ nonZeroDivisors A) :
    (a ⊗ₜ[R] (1 : B)) ∈ nonZeroDivisors (A ⊗[R] B) := by
  have hinj : Function.Injective (LinearMap.mulLeft R a) := by
    intro x y hxy
    have : a * x = a * y := hxy
    exact (mul_cancel_left_mem_nonZeroDivisors ha).mp this
  have hinj2 := Module.Flat.rTensor_preserves_injective_linearMap (M := B) (LinearMap.mulLeft R a) hinj
  have hmul : ∀ z : A ⊗[R] B, (a ⊗ₜ[R] (1 : B)) * z = (LinearMap.mulLeft R a).rTensor B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp [mul_add, hx, hy]
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [hmul] at hz
    exact hinj2 (by rw [hz, map_zero])
  · rw [mul_comm, hmul] at hz
    exact hinj2 (by rw [hz, map_zero])

theorem algebraMap_mem_nonZeroDivisors_of_isLocalization {T : Type*} [CommRing T] (M : Submonoid T)
    (S : Type*) [CommRing S] [Algebra T S] [IsLocalization M S] (x : T) (hx : x ∈ nonZeroDivisors T) :
    algebraMap T S x ∈ nonZeroDivisors S := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  have h1 : IsLocalization.mk' S (x * r) m = 0 := by
    rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm]; exact hy
  rw [IsLocalization.mk'_eq_zero_iff] at h1 ⊢
  obtain ⟨c, hc⟩ := h1
  refine ⟨c, ?_⟩
  have : (↑c * r) * x = 0 := by rw [mul_assoc, mul_comm r x]; exact hc
  exact (mem_nonZeroDivisors_iff_right.mp hx) _ this

theorem exists_finset_forall_mem_range_map {R P B : Type*} [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] (x : P ⊗[R] B) :
    ∃ Λ : Finset P, ∀ (A : Type*) [CommRing A] [Algebra R A] [Algebra A P] [IsScalarTower R A P],
      (↑Λ : Set P) ⊆ Set.range (algebraMap A P) →
      x ∈ Set.range (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun A _ _ _ _ _ => ⟨0, map_zero _⟩⟩
  | tmul l b =>
    refine ⟨{l}, fun A _ _ _ _ hA => ?_⟩
    obtain ⟨a, ha⟩ := hA (show l ∈ (({l} : Finset P) : Set P) by simp)
    exact ⟨a ⊗ₜ b, by rw [Algebra.TensorProduct.map_tmul]; simp [ha]⟩
  | add x y hx hy =>
    obtain ⟨Λx, hΛx⟩ := hx
    obtain ⟨Λy, hΛy⟩ := hy
    refine ⟨Λx ∪ Λy, fun A _ _ _ _ hA => ?_⟩
    obtain ⟨x', hx'⟩ := hΛx A (subset_trans (by simp) hA)
    obtain ⟨y', hy'⟩ := hΛy A (subset_trans (by simp) hA)
    exact ⟨x' + y', by rw [map_add, hx', hy']⟩

theorem exists_finset_forall_subset_range_map {R P B : Type*} [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] (F : Finset (P ⊗[R] B)) :
    ∃ Λ : Finset P, ∀ (A : Type*) [CommRing A] [Algebra R A] [Algebra A P] [IsScalarTower R A P],
      (↑Λ : Set P) ⊆ Set.range (algebraMap A P) →
      (↑F : Set (P ⊗[R] B)) ⊆ Set.range (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, fun A _ _ _ _ _ => by simp⟩
  | insert x F hxF ih =>
    obtain ⟨Λ, hΛ⟩ := ih
    obtain ⟨Λx, hΛx⟩ := exists_finset_forall_mem_range_map (R := R) x
    refine ⟨Λ ∪ Λx, fun A _ _ _ _ hA => ?_⟩
    rw [Finset.coe_insert, Set.insert_subset_iff]
    exact ⟨hΛx A (subset_trans (by simp) hA), hΛ A (subset_trans (by simp) hA)⟩

theorem map_toAlgHom_injective {R A P B : Type*} [CommRing R] [CommRing A] [CommRing P] [CommRing B]
    [Algebra R A] [Algebra R P] [Algebra R B] [Algebra A P] [IsScalarTower R A P] [Module.Flat R B]
    (hinj : Function.Injective (algebraMap A P)) :
    Function.Injective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)) := by
  have h1 : ∀ z, Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B) z =
      ((IsScalarTower.toAlgHom R A P).toLinearMap.rTensor B) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x y => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro z w hzw
  rw [h1, h1] at hzw
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := B) _ hinj hzw

section Coord

variable {R k κ B : Type*} [CommRing R] [Field k] [CommRing κ] [CommRing B]
  [Algebra R k] [Algebra R κ] [Algebra k κ] [IsScalarTower R k κ] [Algebra R B]

noncomputable def prime_coordMap (c : κ →ₗ[k] k) : κ ⊗[R] B →ₗ[R] k ⊗[R] B :=
  TensorProduct.map (c.restrictScalars R) LinearMap.id

theorem prime_coordMap_tmul (c : κ →ₗ[k] k) (x : κ) (b : B) :
    prime_coordMap (R := R) c (x ⊗ₜ[R] b) = c x ⊗ₜ[R] b := rfl

theorem prime_coordMap_mul (c : κ →ₗ[k] k) (y : k ⊗[R] B) (z : κ ⊗[R] B) :
    prime_coordMap (R := R) c (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R k κ) (AlgHom.id R B) y * z) =
      y * prime_coordMap (R := R) c z := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => rw [map_add, add_mul, map_add, h₁, h₂, add_mul]
  | tmul a b =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
    | tmul x d =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply,
        Algebra.TensorProduct.tmul_mul_tmul, prime_coordMap_tmul, prime_coordMap_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem prime_exists_eq_sum_coord {ι₀ : Type*} (e : Module.Basis ι₀ k κ) (z : κ ⊗[R] B) :
    ∃ I : Finset ι₀, ∀ J : Finset ι₀, I ⊆ J →
      z = ∑ i ∈ J, Algebra.TensorProduct.map (IsScalarTower.toAlgHom R k κ) (AlgHom.id R B)
        (prime_coordMap (R := R) (e.coord i) z) * (e i ⊗ₜ[R] (1 : B)) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun J _ => by simp⟩
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨I₁, h₁⟩ := h₁
    obtain ⟨I₂, h₂⟩ := h₂
    refine ⟨I₁ ∪ I₂, fun J hJ => ?_⟩
    conv_lhs => rw [h₁ J (Finset.union_subset_left hJ), h₂ J (Finset.union_subset_right hJ)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, map_add, add_mul]
  | tmul x b =>
    refine ⟨(e.repr x).support, fun J hJ => ?_⟩
    have hterm : ∀ i, Algebra.TensorProduct.map (IsScalarTower.toAlgHom R k κ) (AlgHom.id R B)
        (prime_coordMap (R := R) (e.coord i) (x ⊗ₜ[R] b)) * (e i ⊗ₜ[R] (1 : B)) = ((e.repr x i) • e i) ⊗ₜ[R] b := by
      intro i
      rw [prime_coordMap_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, Module.Basis.coord_apply, Algebra.smul_def]
    simp only [hterm, ← TensorProduct.sum_tmul]
    congr 1
    conv_lhs => rw [← e.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset (e.repr x) hJ (fun i a => a • e i) (fun i _ => zero_smul k (e i))]

end Coord

theorem comap_localRingHom_map_maximalIdeal_eq_span
    {R A P B : Type*} [CommRing R] [CommRing A] [CommRing P] [CommRing B]
    [Algebra R A] [Algebra R P] [Algebra R B] [Algebra A P] [IsScalarTower R A P]
    [IsLocalRing A] [IsLocalRing P] [IsLocalHom (algebraMap A P)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal (P ⊗[R] B)) [𝔔.IsPrime]
    (h𝔔 : (maximalIdeal P).map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)) ≤ 𝔔)
    (h𝔭 : ((maximalIdeal P).map ((algebraMap (P ⊗[R] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)).toRingHom)).IsPrime) :
    letI ι : A ⊗[R] B →+* P ⊗[R] B :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom
    Ideal.comap (Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl)
        ((maximalIdeal P).map ((algebraMap (P ⊗[R] B) (Localization.AtPrime 𝔔)).comp
          (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)).toRingHom))
      = Ideal.span {algebraMap (A ⊗[R] B) (Localization.AtPrime (𝔔.comap ι)) (ϖ ⊗ₜ[R] (1 : B))} := by
  classical
  set ι : A ⊗[R] B →+* P ⊗[R] B := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom with hιdef
  haveI hQA : (𝔔.comap ι).IsPrime := Ideal.comap_isPrime ι 𝔔
  let S := Localization.AtPrime 𝔔
  let SA := Localization.AtPrime (𝔔.comap ι)
  let incl : P →ₐ[R] P ⊗[R] B := Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)
  let 𝔪T : Ideal (P ⊗[R] B) := (maximalIdeal P).map incl
  have h𝔭eq : (maximalIdeal P).map ((algebraMap (P ⊗[R] B) S).comp incl.toRingHom) = 𝔪T.map (algebraMap (P ⊗[R] B) S) := by
    rw [← Ideal.map_map]
    rfl

  let k := ResidueField A
  let κ := ResidueField P
  let resA : A →ₐ[R] k := IsScalarTower.toAlgHom R A k
  let resP : P →ₐ[R] κ := IsScalarTower.toAlgHom R P κ
  let πA : A ⊗[R] B →ₐ[R] k ⊗[R] B := Algebra.TensorProduct.map resA (AlgHom.id R B)
  let πP : P ⊗[R] B →ₐ[R] κ ⊗[R] B := Algebra.TensorProduct.map resP (AlgHom.id R B)
  let jm : k ⊗[R] B →ₐ[R] κ ⊗[R] B := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R k κ) (AlgHom.id R B)
  have hresA : Function.Surjective resA := Ideal.Quotient.mk_surjective
  have hresP : Function.Surjective resP := Ideal.Quotient.mk_surjective
  have hkerresA : RingHom.ker resA = maximalIdeal A := Ideal.mk_ker
  have hkerresP : RingHom.ker resP = maximalIdeal P := Ideal.mk_ker
  have hkerP : RingHom.ker πP = 𝔪T := by
    show RingHom.ker (Algebra.TensorProduct.map resP (AlgHom.id R B)) = _
    rw [Algebra.TensorProduct.rTensor_ker _ hresP, hkerresP]
  have hkerA : RingHom.ker πA = Ideal.span {ϖ ⊗ₜ[R] (1 : B)} := by
    show RingHom.ker (Algebra.TensorProduct.map resA (AlgHom.id R B)) = _
    rw [Algebra.TensorProduct.rTensor_ker _ hresA, hkerresA, hϖ, Ideal.map_span, Set.image_singleton]
    rfl
  have hnat : ∀ w, jm (πA w) = πP (ι w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
    | tmul a b =>
      show jm (πA (a ⊗ₜ b)) = πP ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)) (a ⊗ₜ b))
      simp only [πA, πP, jm, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
      congr 1
  have hπP : Function.Surjective πP := Algebra.TensorProduct.map_surjective resP (AlgHom.id R B) hresP Function.surjective_id
  have hπA : Function.Surjective πA := Algebra.TensorProduct.map_surjective resA (AlgHom.id R B) hresA Function.surjective_id
  let Qb : Ideal (κ ⊗[R] B) := 𝔔.map πP
  have hQb : Qb.comap πP = 𝔔 := by
    show (𝔔.map πP).comap πP = 𝔔
    rw [Ideal.comap_map_of_surjective _ hπP, sup_eq_left]
    intro w hw
    apply h𝔔
    have : w ∈ RingHom.ker πP := hw
    rwa [hkerP] at this
  apply le_antisymm
  ·
    intro z hz
    rw [Ideal.mem_comap, h𝔭eq] at hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (𝔔.comap ι).primeCompl z
    rw [Localization.localRingHom_mk'] at hz
    obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hym⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔔.primeCompl S).mp hz
    simp only at hym
    have h1 : algebraMap (P ⊗[R] B) S (ι x * m) = algebraMap (P ⊗[R] B) S (y * ι s) := by
      rw [map_mul, map_mul, ← hym, mul_right_comm, IsLocalization.mk'_spec]
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists 𝔔.primeCompl S).mp h1
    simp only at hc'
    have ht𝔔 : c * m ∉ 𝔔 := fun h => (‹𝔔.IsPrime›.mem_or_mem h).elim hc hm
    have htx : (c * m) * ι x ∈ 𝔪T := by
      have e1 : (c * m) * ι x = c * (y * ι s) := by rw [← hc']; ring
      rw [e1]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hy)

    have htb : πP (c * m) ∉ Qb := fun h => ht𝔔 (by rw [← hQb]; exact h)
    have hzero : jm (πA x) * πP (c * m) = 0 := by
      rw [hnat, ← map_mul, mul_comm]
      have : (c * m) * ι x ∈ RingHom.ker πP := hkerP ▸ htx
      exact this

    let e := Module.Basis.ofVectorSpace k κ
    obtain ⟨I, hI⟩ := prime_exists_eq_sum_coord (R := R) (B := B) e (πP (c * m))
    have hex : ∃ i, jm (prime_coordMap (R := R) (e.coord i) (πP (c * m))) ∉ Qb := by
      by_contra hall
      push Not at hall
      apply htb
      rw [hI I (Finset.Subset.refl _)]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hall i)
    obtain ⟨i, hi⟩ := hex
    have ht₀x : πA x * prime_coordMap (R := R) (e.coord i) (πP (c * m)) = 0 := by
      have e2 := congrArg (prime_coordMap (R := R) (B := B) (e.coord i)) hzero
      rwa [prime_coordMap_mul, map_zero] at e2

    obtain ⟨t₁, ht₁⟩ := hπA (prime_coordMap (R := R) (e.coord i) (πP (c * m)))
    have ht₁𝔔 : t₁ ∉ 𝔔.comap ι := by
      intro h
      apply hi
      rw [← ht₁, hnat]
      exact Ideal.mem_map_of_mem _ h
    have hmem : t₁ * x ∈ RingHom.ker πA := by
      rw [RingHom.mem_ker, map_mul, ht₁, mul_comm]
      exact ht₀x
    rw [hkerA, Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    rw [Ideal.mem_span_singleton]
    refine ⟨IsLocalization.mk' SA w ⟨t₁ * s, Submonoid.mul_mem _ ht₁𝔔 s.2⟩, ?_⟩
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
    congr 1
    show (t₁ * ↑s) * x = ↑s * (ϖ ⊗ₜ[R] (1 : B) * w)
    rw [← hw]
    ring
  ·
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, Localization.localRingHom_to_map, h𝔭eq]
    apply Ideal.mem_map_of_mem
    have hϖm : algebraMap A P ϖ ∈ maximalIdeal P := by
      have hmem : ϖ ∈ maximalIdeal A := hϖ ▸ Ideal.mem_span_singleton_self ϖ
      exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
        (IsLocalRing.mem_maximalIdeal _).mp hmem ((isUnit_map_iff (algebraMap A P) ϖ).mp hu)
    have e3 : ι (ϖ ⊗ₜ[R] (1 : B)) = incl (algebraMap A P ϖ) := by
      show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)) (ϖ ⊗ₜ[R] (1 : B)) = _
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    rw [e3]
    exact Ideal.mem_map_of_mem _ hϖm

theorem exists_eq_pow_mul_and_localRingHom_not_mem
    {R A P B : Type*} [CommRing R] [CommRing A] [CommRing P] [CommRing B]
    [Algebra R A] [Algebra R P] [Algebra R B] [Algebra A P] [IsScalarTower R A P]
    [IsLocalRing A] [IsLocalRing P] [IsLocalHom (algebraMap A P)] [IsNoetherianRing (A ⊗[R] B)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal (P ⊗[R] B)) [𝔔.IsPrime]
    (h𝔔 : (maximalIdeal P).map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)) ≤ 𝔔)
    (h𝔭 : ((maximalIdeal P).map ((algebraMap (P ⊗[R] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)).toRingHom)).IsPrime) :
    letI ι : A ⊗[R] B →+* P ⊗[R] B :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom
    ∀ X : Localization.AtPrime (𝔔.comap ι), X ≠ 0 →
      ∃ (m : ℕ) (X₀ : Localization.AtPrime (𝔔.comap ι)),
        X = algebraMap (A ⊗[R] B) (Localization.AtPrime (𝔔.comap ι)) (ϖ ⊗ₜ[R] (1 : B)) ^ m * X₀ ∧
        Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl X₀ ∉
          ((maximalIdeal P).map ((algebraMap (P ⊗[R] B) (Localization.AtPrime 𝔔)).comp
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)).toRingHom)) := by
  classical
  set ι : A ⊗[R] B →+* P ⊗[R] B := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom with hιdef
  intro X hX
  haveI hQA : (𝔔.comap ι).IsPrime := Ideal.comap_isPrime ι 𝔔
  let SA := Localization.AtPrime (𝔔.comap ι)
  haveI : IsNoetherianRing SA := inferInstance
  let φ := Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl
  let ϖ' : SA := algebraMap (A ⊗[R] B) SA (ϖ ⊗ₜ[R] (1 : B))
  let I : Ideal SA := Ideal.span {ϖ'}
  have hI : Ideal.comap φ ((maximalIdeal P).map ((algebraMap (P ⊗[R] B) (Localization.AtPrime 𝔔)).comp
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)).toRingHom)) = I :=
    comap_localRingHom_map_maximalIdeal_eq_span ϖ hϖ 𝔔 h𝔔 h𝔭
  haveI hIp : I.IsPrime := hI ▸ Ideal.comap_isPrime φ _
  have hItop : I ≠ ⊤ := hIp.ne_top
  have hkrull : ⨅ i : ℕ, I ^ i = ⊥ := @Ideal.iInf_pow_eq_bot_of_isLocalRing SA _ I inferInstance inferInstance hItop
  have hnot : ¬ ∀ n : ℕ, X ∈ I ^ n := by
    intro hall
    apply hX
    have : X ∈ ⨅ i : ℕ, I ^ i := Ideal.mem_iInf.mpr hall
    rwa [hkrull, Ideal.mem_bot] at this
  push Not at hnot
  let n := Nat.find hnot
  have hn : X ∉ I ^ n := Nat.find_spec hnot
  have hn0 : n ≠ 0 := by
    intro h0
    apply hn
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
  have hXm : X ∈ I ^ m := by
    by_contra h
    have := Nat.find_min hnot (show m < n by omega)
    exact this h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hXm
  obtain ⟨X₀, hX₀⟩ := hXm
  refine ⟨m, X₀, by rw [← hX₀, mul_comm], ?_⟩
  intro hmem
  have hX₀I : X₀ ∈ I := by
    rw [← hI]
    exact hmem
  apply hn
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hX₀I
  exact ⟨u, by rw [← hX₀, ← hu, pow_succ]; ring⟩

theorem comap_localRingHom_map_maximalIdeal_eq_span_noprime
    {R A P B : Type*} [CommRing R] [CommRing A] [CommRing P] [CommRing B]
    [Algebra R A] [Algebra R P] [Algebra R B] [Algebra A P] [IsScalarTower R A P]
    [IsLocalRing A] [IsLocalRing P] [IsLocalHom (algebraMap A P)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal (P ⊗[R] B)) [𝔔.IsPrime]
    (h𝔔 : (maximalIdeal P).map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)) ≤ 𝔔) :
    letI ι : A ⊗[R] B →+* P ⊗[R] B :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom
    Ideal.comap (Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl)
        ((maximalIdeal P).map ((algebraMap (P ⊗[R] B) (Localization.AtPrime 𝔔)).comp
          (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)).toRingHom))
      = Ideal.span {algebraMap (A ⊗[R] B) (Localization.AtPrime (𝔔.comap ι)) (ϖ ⊗ₜ[R] (1 : B))} := by
  classical
  set ι : A ⊗[R] B →+* P ⊗[R] B := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom with hιdef
  haveI hQA : (𝔔.comap ι).IsPrime := Ideal.comap_isPrime ι 𝔔
  let S := Localization.AtPrime 𝔔
  let SA := Localization.AtPrime (𝔔.comap ι)
  let incl : P →ₐ[R] P ⊗[R] B := Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)
  let 𝔪T : Ideal (P ⊗[R] B) := (maximalIdeal P).map incl
  have h𝔭eq : (maximalIdeal P).map ((algebraMap (P ⊗[R] B) S).comp incl.toRingHom) = 𝔪T.map (algebraMap (P ⊗[R] B) S) := by
    rw [← Ideal.map_map]
    rfl

  let k := ResidueField A
  let κ := ResidueField P
  let resA : A →ₐ[R] k := IsScalarTower.toAlgHom R A k
  let resP : P →ₐ[R] κ := IsScalarTower.toAlgHom R P κ
  let πA : A ⊗[R] B →ₐ[R] k ⊗[R] B := Algebra.TensorProduct.map resA (AlgHom.id R B)
  let πP : P ⊗[R] B →ₐ[R] κ ⊗[R] B := Algebra.TensorProduct.map resP (AlgHom.id R B)
  let jm : k ⊗[R] B →ₐ[R] κ ⊗[R] B := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R k κ) (AlgHom.id R B)
  have hresA : Function.Surjective resA := Ideal.Quotient.mk_surjective
  have hresP : Function.Surjective resP := Ideal.Quotient.mk_surjective
  have hkerresA : RingHom.ker resA = maximalIdeal A := Ideal.mk_ker
  have hkerresP : RingHom.ker resP = maximalIdeal P := Ideal.mk_ker
  have hkerP : RingHom.ker πP = 𝔪T := by
    show RingHom.ker (Algebra.TensorProduct.map resP (AlgHom.id R B)) = _
    rw [Algebra.TensorProduct.rTensor_ker _ hresP, hkerresP]
  have hkerA : RingHom.ker πA = Ideal.span {ϖ ⊗ₜ[R] (1 : B)} := by
    show RingHom.ker (Algebra.TensorProduct.map resA (AlgHom.id R B)) = _
    rw [Algebra.TensorProduct.rTensor_ker _ hresA, hkerresA, hϖ, Ideal.map_span, Set.image_singleton]
    rfl
  have hnat : ∀ w, jm (πA w) = πP (ι w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
    | tmul a b =>
      show jm (πA (a ⊗ₜ b)) = πP ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)) (a ⊗ₜ b))
      simp only [πA, πP, jm, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
      congr 1
  have hπP : Function.Surjective πP := Algebra.TensorProduct.map_surjective resP (AlgHom.id R B) hresP Function.surjective_id
  have hπA : Function.Surjective πA := Algebra.TensorProduct.map_surjective resA (AlgHom.id R B) hresA Function.surjective_id
  let Qb : Ideal (κ ⊗[R] B) := 𝔔.map πP
  have hQb : Qb.comap πP = 𝔔 := by
    show (𝔔.map πP).comap πP = 𝔔
    rw [Ideal.comap_map_of_surjective _ hπP, sup_eq_left]
    intro w hw
    apply h𝔔
    have : w ∈ RingHom.ker πP := hw
    rwa [hkerP] at this
  apply le_antisymm
  ·
    intro z hz
    rw [Ideal.mem_comap, h𝔭eq] at hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (𝔔.comap ι).primeCompl z
    rw [Localization.localRingHom_mk'] at hz
    obtain ⟨⟨⟨y, hy⟩, ⟨m, hm⟩⟩, hym⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔔.primeCompl S).mp hz
    simp only at hym
    have h1 : algebraMap (P ⊗[R] B) S (ι x * m) = algebraMap (P ⊗[R] B) S (y * ι s) := by
      rw [map_mul, map_mul, ← hym, mul_right_comm, IsLocalization.mk'_spec]
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists 𝔔.primeCompl S).mp h1
    simp only at hc'
    have ht𝔔 : c * m ∉ 𝔔 := fun h => (‹𝔔.IsPrime›.mem_or_mem h).elim hc hm
    have htx : (c * m) * ι x ∈ 𝔪T := by
      have e1 : (c * m) * ι x = c * (y * ι s) := by rw [← hc']; ring
      rw [e1]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hy)

    have htb : πP (c * m) ∉ Qb := fun h => ht𝔔 (by rw [← hQb]; exact h)
    have hzero : jm (πA x) * πP (c * m) = 0 := by
      rw [hnat, ← map_mul, mul_comm]
      have : (c * m) * ι x ∈ RingHom.ker πP := hkerP ▸ htx
      exact this

    let e := Module.Basis.ofVectorSpace k κ
    obtain ⟨I, hI⟩ := prime_exists_eq_sum_coord (R := R) (B := B) e (πP (c * m))
    have hex : ∃ i, jm (prime_coordMap (R := R) (e.coord i) (πP (c * m))) ∉ Qb := by
      by_contra hall
      push Not at hall
      apply htb
      rw [hI I (Finset.Subset.refl _)]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hall i)
    obtain ⟨i, hi⟩ := hex
    have ht₀x : πA x * prime_coordMap (R := R) (e.coord i) (πP (c * m)) = 0 := by
      have e2 := congrArg (prime_coordMap (R := R) (B := B) (e.coord i)) hzero
      rwa [prime_coordMap_mul, map_zero] at e2

    obtain ⟨t₁, ht₁⟩ := hπA (prime_coordMap (R := R) (e.coord i) (πP (c * m)))
    have ht₁𝔔 : t₁ ∉ 𝔔.comap ι := by
      intro h
      apply hi
      rw [← ht₁, hnat]
      exact Ideal.mem_map_of_mem _ h
    have hmem : t₁ * x ∈ RingHom.ker πA := by
      rw [RingHom.mem_ker, map_mul, ht₁, mul_comm]
      exact ht₀x
    rw [hkerA, Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    rw [Ideal.mem_span_singleton]
    refine ⟨IsLocalization.mk' SA w ⟨t₁ * s, Submonoid.mul_mem _ ht₁𝔔 s.2⟩, ?_⟩
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
    congr 1
    show (t₁ * ↑s) * x = ↑s * (ϖ ⊗ₜ[R] (1 : B) * w)
    rw [← hw]
    ring
  ·
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, Localization.localRingHom_to_map, h𝔭eq]
    apply Ideal.mem_map_of_mem
    have hϖm : algebraMap A P ϖ ∈ maximalIdeal P := by
      have hmem : ϖ ∈ maximalIdeal A := hϖ ▸ Ideal.mem_span_singleton_self ϖ
      exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
        (IsLocalRing.mem_maximalIdeal _).mp hmem ((isUnit_map_iff (algebraMap A P) ϖ).mp hu)
    have e3 : ι (ϖ ⊗ₜ[R] (1 : B)) = incl (algebraMap A P ϖ) := by
      show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)) (ϖ ⊗ₜ[R] (1 : B)) = _
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    rw [e3]
    exact Ideal.mem_map_of_mem _ hϖm

theorem exists_eq_pow_mul_of_forall_mul_eq_pow_mul {T : Type*} [CommRing T] (ϖ : T)
    {ιx : Type*} (P : ιx → Ideal T) (hP : ∀ i, (P i).IsPrime) (hspan : Ideal.span {ϖ} = ⨅ i, P i)
    (hreg : ϖ ∈ nonZeroDivisors T)
    (k : ℕ) (X : T) (Y Z : ιx → T) (hY : ∀ i, Y i ∉ P i) (h : ∀ i, X * Y i = ϖ ^ k * Z i) :
    ∃ W : T, X = ϖ ^ k * W := by
  induction k generalizing X Z with
  | zero => exact ⟨X, by simp⟩
  | succ k ih =>
    have h2 : X ∈ (Ideal.span {ϖ} : Ideal T) := by
      rw [hspan, Ideal.mem_iInf]
      intro i
      have h1 : X * Y i ∈ P i := by
        have : X * Y i ∈ Ideal.span {ϖ} := by
          rw [h i, pow_succ']
          exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ))
        rw [hspan, Ideal.mem_iInf] at this
        exact this i
      exact ((hP i).mem_or_mem h1).resolve_right (hY i)
    obtain ⟨X', rfl⟩ := Ideal.mem_span_singleton'.mp h2
    have h4 : ∀ i, X' * Y i = ϖ ^ k * Z i := by
      intro i
      have h3 : (X' * Y i) * ϖ = (ϖ ^ k * Z i) * ϖ := by
        have e1 : X' * ϖ * Y i = (X' * Y i) * ϖ := by ring
        have e2 : ϖ ^ (k + 1) * Z i = (ϖ ^ k * Z i) * ϖ := by ring
        rw [← e1, ← e2]; exact h i
      exact (mul_cancel_right_mem_nonZeroDivisors hreg).mp h3
    obtain ⟨W, hW⟩ := ih X' Z h4
    exact ⟨W, by rw [hW]; ring⟩

theorem exists_eq_pow_mul_of_forall_localRingHom_not_mem
    {R A P B : Type*} [CommRing R] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing P] [CommRing B]
    [Algebra R A] [Algebra R P] [Algebra R B] [Algebra A P] [IsScalarTower R A P] [Module.Flat R B]
    [IsLocalRing P] [IsLocalHom (algebraMap A P)]
    (q : A) (hq : q ≠ 0)
    (𝔔 : Ideal (P ⊗[R] B)) [𝔔.IsPrime]
    (h𝔔 : (maximalIdeal P).map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)) ≤ 𝔔)
    {ιx : Type*} (𝔯 : ιx → Ideal (Localization.AtPrime 𝔔)) (h𝔯 : ∀ i, (𝔯 i).IsPrime)
    (h𝔭 : ((maximalIdeal P).map ((algebraMap (P ⊗[R] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)).toRingHom)) = ⨅ i, 𝔯 i) :
    letI ι := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom
    ∀ (N : ℕ) (X : Localization.AtPrime (𝔔.comap ι)) (Y Z : ιx → Localization.AtPrime (𝔔.comap ι)),
      (∀ i, X * Y i = algebraMap A (Localization.AtPrime (𝔔.comap ι)) q ^ N * Z i) →
      (∀ i, Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl (Y i) ∉ 𝔯 i) →
      ∃ W : Localization.AtPrime (𝔔.comap ι), X = algebraMap A (Localization.AtPrime (𝔔.comap ι)) q ^ N * W := by
  intro N X Y Z hXYZ hY
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖmax : maximalIdeal A = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq

  have hprime := comap_localRingHom_map_maximalIdeal_eq_span_noprime (R := R) (B := B) ϖ hϖmax 𝔔 h𝔔
  set ϖ' := algebraMap (A ⊗[R] B) (Localization.AtPrime (𝔔.comap
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom)) (ϖ ⊗ₜ[R] (1 : B)) with hϖ'
  have hspan : Ideal.span {ϖ'} = ⨅ i, (𝔯 i).comap (Localization.localRingHom _ 𝔔
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom rfl) := by
    rw [← hprime, h𝔭, Ideal.comap_iInf]
  have hYspan : ∀ i, Y i ∉ (𝔯 i).comap (Localization.localRingHom _ 𝔔
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom rfl) := by
    intro i; rw [Ideal.mem_comap]; exact hY i
  have hϖ'reg : ϖ' ∈ nonZeroDivisors _ :=
    algebraMap_mem_nonZeroDivisors_of_isLocalization
      (𝔔.comap (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom).primeCompl _ _
      (tmul_one_mem_nonZeroDivisors ϖ (mem_nonZeroDivisors_of_ne_zero hϖirr.ne_zero))
  obtain ⟨e, u, hqu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq hϖirr
  have halgϖ : algebraMap A (Localization.AtPrime (𝔔.comap
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom)) ϖ = ϖ' := by
    rw [hϖ', IsScalarTower.algebraMap_apply A (A ⊗[R] B), Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
  rw [hqu, map_mul, map_pow, halgϖ, mul_pow, ← pow_mul] at hXYZ ⊢
  set v := algebraMap A (Localization.AtPrime (𝔔.comap
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom)) ↑u with hv
  have h2 : ∀ i, X * Y i = ϖ' ^ (e * N) * (v ^ N * Z i) := by
    intro i; rw [hXYZ i]; ring
  obtain ⟨W, hW⟩ := exists_eq_pow_mul_of_forall_mul_eq_pow_mul ϖ' _ (fun i => Ideal.comap_isPrime _ _) hspan hϖ'reg
    (e * N) X Y _ hYspan h2
  have hu1 : v * algebraMap A _ ↑u⁻¹ = 1 := by
    rw [hv, ← map_mul, Units.mul_inv, map_one]
  refine ⟨(algebraMap A _ ↑u⁻¹) ^ N * W, ?_⟩
  rw [hW]
  symm
  calc v ^ N * ϖ' ^ (e * N) * (algebraMap A _ ↑u⁻¹ ^ N * W)
      = (v * algebraMap A _ ↑u⁻¹) ^ N * (ϖ' ^ (e * N) * W) := by ring
    _ = ϖ' ^ (e * N) * W := by rw [hu1, one_pow, one_mul]

theorem exists_mul_eq_pow_mul_of_separated_branch
    {R A P B : Type*} [CommRing R] [CommRing A] [CommRing P] [CommRing B]
    [Algebra R A] [Algebra R P] [Algebra R B] [Algebra A P] [IsScalarTower R A P]
    [IsLocalRing A] [IsLocalRing P] [IsLocalHom (algebraMap A P)] [IsNoetherianRing (A ⊗[R] B)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal (P ⊗[R] B)) [𝔔.IsPrime] [IsDomain (Localization.AtPrime 𝔔)]
    (h𝔔 : (maximalIdeal P).map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)) ≤ 𝔔)
    {ιx : Type*} [Fintype ιx] (𝔯 : ιx → Ideal (Localization.AtPrime 𝔔)) (h𝔯 : ∀ i, (𝔯 i).IsPrime)
    (h𝔭 : ((maximalIdeal P).map ((algebraMap (P ⊗[R] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := P) (B := B)).toRingHom)) = ⨅ i, 𝔯 i)
    (i₀ : ιx) :
    letI ι := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom
    letI φ := Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl
    (∀ j, (𝔯 j).comap φ = (𝔯 i₀).comap φ ∨ ∃ d, d ∈ (𝔯 j).comap φ ∧ d ∉ (𝔯 i₀).comap φ) →
    ∀ X : Localization.AtPrime (𝔔.comap ι), φ X ≠ 0 →
      ∃ (m : ℕ) (x₀ s₀ : Localization.AtPrime (𝔔.comap ι)),
        φ X * φ s₀ = φ (algebraMap (A ⊗[R] B) (Localization.AtPrime (𝔔.comap ι)) (ϖ ⊗ₜ[R] (1 : B))) ^ m * φ x₀ ∧
        φ s₀ ∉ 𝔯 i₀ ∧ φ x₀ ∉ 𝔯 i₀ := by
  intro hsep X hX
  classical
  let ι := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A P) (AlgHom.id R B)).toRingHom
  let SA := Localization.AtPrime (𝔔.comap ι)
  let φ : SA →+* Localization.AtPrime 𝔔 := Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl
  let ϖ' : SA := algebraMap (A ⊗[R] B) SA (ϖ ⊗ₜ[R] (1 : B))
  let 𝔯' : ιx → Ideal SA := fun j => (𝔯 j).comap φ
  haveI h𝔯'p : ∀ j, (𝔯' j).IsPrime := fun j => Ideal.comap_isPrime φ (𝔯 j)
  haveI : (𝔯' i₀).IsPrime := h𝔯'p i₀
  have hspan : Ideal.span {ϖ'} = ⨅ j, 𝔯' j := by
    have := comap_localRingHom_map_maximalIdeal_eq_span_noprime (R := R) (B := B) ϖ hϖ 𝔔 h𝔔
    rw [← this, h𝔭, Ideal.comap_iInf]
  have hϖ'mem : ∀ j, ϖ' ∈ 𝔯' j := by
    have h1 : ϖ' ∈ ⨅ j, 𝔯' j := by rw [← hspan]; exact Ideal.mem_span_singleton_self _
    exact fun j => (Ideal.mem_iInf.mp h1) j

  have hsep' : ∀ j, ∃ d : SA, d ∈ 𝔯' j ∧ (d ∈ 𝔯' i₀ → 𝔯' j = 𝔯' i₀) := by
    intro j
    rcases hsep j with h | ⟨d, hd1, hd2⟩
    · exact ⟨ϖ', hϖ'mem j, fun _ => h⟩
    · exact ⟨d, hd1, fun h => absurd h hd2⟩
  choose d hd hdimp using hsep'
  let D : SA := ∏ j ∈ (Finset.univ.filter fun j => 𝔯' j ≠ 𝔯' i₀), d j
  have hD : D ∉ 𝔯' i₀ := by
    intro hmem
    obtain ⟨j, hj, hj2⟩ := (Ideal.IsPrime.prod_mem_iff (p := 𝔯' i₀)).mp hmem
    exact (Finset.mem_filter.mp hj).2 (hdimp j hj2)
  have hrD : ∀ r ∈ 𝔯' i₀, r * D ∈ Ideal.span {ϖ'} := by
    intro r hr
    rw [hspan, Ideal.mem_iInf]
    intro j
    by_cases hj : 𝔯' j = 𝔯' i₀
    · rw [hj]; exact Ideal.mul_mem_right _ _ hr
    · apply Ideal.mul_mem_left
      exact Ideal.prod_mem (𝔯' j) (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) (hd j)

  let L := Localization.AtPrime (𝔯' i₀)
  haveI : IsNoetherianRing SA := IsLocalization.isNoetherianRing (𝔔.comap ι).primeCompl SA inferInstance
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing (𝔯' i₀).primeCompl L inferInstance
  let π : L := algebraMap SA L ϖ'
  have hmaxL : maximalIdeal L = Ideal.span {π} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝔯' i₀).primeCompl z
      have hr : r ∈ 𝔯' i₀ := (IsLocalization.AtPrime.mk'_mem_maximal_iff L (𝔯' i₀) r s).mp hz
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (hrD r hr)

      refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' (M := (𝔯' i₀).primeCompl) L w ⟨(s : SA) * D, ?_⟩, ?_⟩
      · intro hmem
        rcases (h𝔯'p i₀).mem_or_mem hmem with h1 | h2
        · exact s.2 h1
        · exact hD h2
      · show IsLocalization.mk' (M := (𝔯' i₀).primeCompl) L w _ * algebraMap SA L ϖ' = IsLocalization.mk' L r s
        rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
        apply IsLocalization.mk'_eq_of_eq
        show ((s : SA) * D) * r = (s : SA) * (ϖ' * w)
        rw [mul_comm ϖ' w, hw]; ring
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L (𝔯' i₀) ϖ').mpr (hϖ'mem i₀)

  have hπtop : (Ideal.span {π} : Ideal L) ≠ ⊤ := by
    rw [← hmaxL]; exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top
  have hKrull : ⨅ n : ℕ, (Ideal.span {π} : Ideal L) ^ n = ⊥ :=
    @Ideal.iInf_pow_eq_bot_of_isLocalRing L _ (Ideal.span {π}) inferInstance inferInstance hπtop
  have hφc : ∀ c : (𝔯' i₀).primeCompl, φ c ≠ 0 := by
    intro c h0
    apply c.2
    show (c : SA) ∈ (𝔯 i₀).comap φ
    rw [Ideal.mem_comap, h0]; exact (𝔯 i₀).zero_mem
  have hXL : algebraMap SA L X ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (𝔯' i₀).primeCompl L X).mp h0
    apply hX
    have h1 := congrArg φ hc
    rw [map_mul, map_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (hφc c)
    · exact h2
  have hnot : ¬ ∀ n : ℕ, algebraMap SA L X ∈ (Ideal.span {π} : Ideal L) ^ n := by
    intro hall
    apply hXL
    have h1 : algebraMap SA L X ∈ ⨅ n : ℕ, (Ideal.span {π} : Ideal L) ^ n := Ideal.mem_iInf.mpr hall
    rwa [hKrull, Ideal.mem_bot] at h1
  push Not at hnot
  let n₀ := Nat.find hnot
  have hn₀ : algebraMap SA L X ∉ (Ideal.span {π} : Ideal L) ^ n₀ := Nat.find_spec hnot
  have hn₀pos : n₀ ≠ 0 := by
    intro h0
    apply hn₀
    rw [h0, pow_zero, Ideal.one_eq_top]; trivial
  obtain ⟨m, hm⟩ : ∃ m, n₀ = m + 1 := Nat.exists_eq_succ_of_ne_zero hn₀pos
  have hXm : algebraMap SA L X ∈ (Ideal.span {π} : Ideal L) ^ m := by
    by_contra hc
    have := Nat.find_min hnot (show m < n₀ by omega)
    exact this hc
  rw [Ideal.span_singleton_pow] at hXm
  obtain ⟨X₁, hX₁⟩ := Ideal.mem_span_singleton'.mp hXm
  have hX₁unit : IsUnit X₁ := by
    by_contra hnu
    have hmem : X₁ ∈ maximalIdeal L := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [hmaxL] at hmem
    obtain ⟨X₂, hX₂⟩ := Ideal.mem_span_singleton'.mp hmem
    apply hn₀
    rw [hm, Ideal.span_singleton_pow, ← hX₁, ← hX₂]
    exact Ideal.mem_span_singleton'.mpr ⟨X₂, by ring⟩
  obtain ⟨⟨x₀, s₀⟩, hx₀s₀⟩ := IsLocalization.mk'_surjective (𝔯' i₀).primeCompl X₁
  dsimp only at hx₀s₀
  have hx₀ : x₀ ∉ 𝔯' i₀ := by
    have := (IsLocalization.AtPrime.isUnit_mk'_iff L (𝔯' i₀) x₀ s₀).mp (hx₀s₀ ▸ hX₁unit)
    exact this

  have hL : algebraMap SA L (X * s₀) = algebraMap SA L (ϖ' ^ m * x₀) := by
    rw [map_mul, ← hX₁, ← hx₀s₀, map_mul, map_pow]
    calc IsLocalization.mk' L x₀ s₀ * algebraMap SA L ϖ' ^ m * algebraMap SA L ↑s₀
        = algebraMap SA L ϖ' ^ m * (IsLocalization.mk' L x₀ s₀ * algebraMap SA L ↑s₀) := by ring
      _ = algebraMap SA L ϖ' ^ m * algebraMap SA L x₀ := by rw [IsLocalization.mk'_spec]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (𝔯' i₀).primeCompl L).mp hL
  refine ⟨m, x₀, s₀, ?_, fun h => s₀.2 (Ideal.mem_comap.mpr h), fun h => hx₀ (Ideal.mem_comap.mpr h)⟩
  have h1 := congrArg φ hc
  rw [map_mul, map_mul, map_mul, map_mul, map_pow] at h1
  exact mul_left_cancel₀ (hφc c) h1

theorem exists_dvr_layer (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    [Algebra ↥(GaloisRep.ratLocalizedAt p) ↥Pl] (halg : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥Pl = ρ)
    (Λ : Finset ↥Pl) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : Algebra ↥(GaloisRep.ratLocalizedAt p) A) (_ : Algebra A ↥Pl)
      (_ : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A ↥Pl),
      IsLocalHom (algebraMap A ↥Pl) ∧ Function.Injective (algebraMap A ↥Pl) ∧
      (↑Λ : Set ↥Pl) ⊆ Set.range (algebraMap A ↥Pl) := by
  classical
  let SΛ : Set (AlgebraicClosure ℚ) := (fun l : ↥Pl => (l : AlgebraicClosure ℚ)) '' (Λ : Set ↥Pl)
  haveI : Finite SΛ := ((Λ.finite_toSet).image _).to_subtype
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ SΛ
  haveI : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral)
  let A : Type := ↥(Pl.comap (algebraMap L (AlgebraicClosure ℚ)))
  haveI hdvr : IsDiscreteValuationRing A :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime L Pl (Fact.out) hPl
  have hmemA : ∀ a : A, ((algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap A L)) a ∈ Pl := fun a => a.2
  let f : A →+* ↥Pl := ((algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap A L)).codRestrict Pl hmemA
  have hf : ∀ a : A, (f a : AlgebraicClosure ℚ) = algebraMap L (AlgebraicClosure ℚ) (a : L) := fun a => rfl

  have hRQ : ∀ r : ↥(GaloisRep.ratLocalizedAt p),
      algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) = ((ρ r : ↥Pl) : AlgebraicClosure ℚ) := by
    intro r
    have : algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) = (Pl.subtype.comp ρ) r := by
      rw [hρ]; rfl
    rw [this]; rfl
  have hRmem : ∀ r : ↥(GaloisRep.ratLocalizedAt p),
      ((algebraMap ℚ L).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) r ∈
        Pl.comap (algebraMap L (AlgebraicClosure ℚ)) := by
    intro r
    rw [ValuationSubring.mem_comap, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    change algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) ∈ Pl
    rw [hRQ]
    exact (ρ r).2
  let g : ↥(GaloisRep.ratLocalizedAt p) →+* A :=
    ((algebraMap ℚ L).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)).codRestrict _ hRmem
  have hg : ∀ r, ((g r : A) : L) = algebraMap ℚ L (r : ℚ) := fun r => rfl
  letI : Algebra A ↥Pl := f.toAlgebra
  letI : Algebra ↥(GaloisRep.ratLocalizedAt p) A := g.toAlgebra
  have htower : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A ↥Pl := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    rw [halg]
    apply Subtype.ext
    change ((ρ r : ↥Pl) : AlgebraicClosure ℚ) = (f (g r) : AlgebraicClosure ℚ)
    rw [hf, hg, ← IsScalarTower.algebraMap_apply, hRQ]
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : (f a : AlgebraicClosure ℚ) = f b := by rw [hab]
    rw [hf, hf] at h1
    exact Subtype.ext ((algebraMap L (AlgebraicClosure ℚ)).injective h1)
  have hloc : IsLocalHom f := by
    refine ⟨fun a ha => ?_⟩
    have hfa0 : (f a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have : f a = 0 := Subtype.ext h0
      exact not_isUnit_zero (this ▸ ha)
    have ha0 : (a : L) ≠ 0 := by
      intro h0; apply hfa0; rw [hf, h0, map_zero]
    obtain ⟨u, hu⟩ := ha
    have hinv : ((f a : AlgebraicClosure ℚ))⁻¹ ∈ Pl := by
      have hmul : (f a : AlgebraicClosure ℚ) * ((u⁻¹ : (↥Pl)ˣ) : ↥Pl) = 1 := by
        rw [← hu]
        have h2 : ((u : ↥Pl) * ((u⁻¹ : (↥Pl)ˣ) : ↥Pl) : ↥Pl) = 1 := u.mul_inv
        have h3 := congrArg Subtype.val h2
        simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using h3
      rw [inv_eq_of_mul_eq_one_right hmul]
      exact ((u⁻¹ : (↥Pl)ˣ) : ↥Pl).2
    have hinv' : algebraMap L (AlgebraicClosure ℚ) (a : L)⁻¹ ∈ Pl := by
      rw [map_inv₀, ← hf]; exact hinv
    let b : A := ⟨(a : L)⁻¹, hinv'⟩
    exact IsUnit.of_mul_eq_one (b := b) (Subtype.ext (mul_inv_cancel₀ ha0))
  refine ⟨A, inferInstance, inferInstance, hdvr, g.toAlgebra, f.toAlgebra, htower, hloc, hfinj, ?_⟩
  intro l hl
  have hlL : (l : AlgebraicClosure ℚ) ∈ L :=
    IntermediateField.subset_adjoin ℚ SΛ ⟨l, hl, rfl⟩
  refine ⟨⟨⟨(l : AlgebraicClosure ℚ), hlL⟩, ?_⟩, ?_⟩
  · show algebraMap L (AlgebraicClosure ℚ) ⟨(l : AlgebraicClosure ℚ), hlL⟩ ∈ Pl
    exact l.2
  · exact Subtype.ext rfl

end LocalPlAlgebra

set_option maxHeartbeats 1600000 in

theorem node_mem_range_of_forall_comap_eq_bot
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    [Algebra ↥(GaloisRep.ratLocalizedAt p) ↥Pl] (halg : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra ↥(GaloisRep.ratLocalizedAt p) B]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt p) B] [Module.Flat ↥(GaloisRep.ratLocalizedAt p) B]
    (𝔔 : Ideal (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B)) [𝔔.IsPrime]
    (h𝔔 : 𝔔.comap (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom =
      maximalIdeal ↥Pl)
    [IsDomain (Localization.AtPrime 𝔔)]
    {ιx : Type} [Fintype ιx] (𝔯 : ιx → Ideal (Localization.AtPrime 𝔔)) (h𝔯 : ∀ i, (𝔯 i).IsPrime)
    (h𝔭 : ((maximalIdeal ↥Pl).map ((algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft
          (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom)) =
      ⨅ i, 𝔯 i)
    (K : Type) [Field K] [Algebra (Localization.AtPrime 𝔔) K] [IsFractionRing (Localization.AtPrime 𝔔) K] :
    letI S := Localization.AtPrime 𝔔
    letI toS : ↥Pl →+* S := (algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) S).comp
      (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom
    ∀ h : K,
      (∀ i, ∃ a c : S, c ∉ 𝔯 i ∧ h * algebraMap S K c = algebraMap S K a) →
      (∀ 𝔮 : Ideal S, 𝔮.IsPrime → 𝔮.comap toS = ⊥ →
        ∃ a s : S, s ∉ 𝔮 ∧ h * algebraMap S K s = algebraMap S K a) →
      h ∈ Set.range (algebraMap S K) := by
  classical
  set toS : ↥Pl →+* Localization.AtPrime 𝔔 :=
    (algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime 𝔔)).comp
      (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom
    with htoSdef

  have hpmax : (p : ↥Pl) ∈ maximalIdeal ↥Pl := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    have : ((p : ↥Pl) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) := by norm_cast
    rw [this]; exact hPl
  have hp0Pl : (p : ↥Pl) ≠ 0 := by
    intro h0
    have h1 : ((p : ↥Pl) : AlgebraicClosure ℚ) = 0 := by rw [h0]; rfl
    have h2 : ((p : ↥Pl) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) := by norm_cast
    rw [h2] at h1
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
  have h𝔔ge : (maximalIdeal ↥Pl).map (Algebra.TensorProduct.includeLeft
      (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)) ≤ 𝔔 :=
    Ideal.map_le_iff_le_comap.mpr h𝔔.ge
  have htoS : ∀ a : ↥Pl, toS a = algebraMap _ (Localization.AtPrime 𝔔) (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B)) :=
    fun a => rfl
  have hnzdS : ∀ a : ↥Pl, a ≠ 0 → toS a ∈ nonZeroDivisors (Localization.AtPrime 𝔔) := fun a ha =>
    LocalPlAlgebra.algebraMap_mem_nonZeroDivisors_of_isLocalization 𝔔.primeCompl (Localization.AtPrime 𝔔) _
      (LocalPlAlgebra.tmul_one_mem_nonZeroDivisors a (mem_nonZeroDivisors_of_ne_zero ha))
  have hpS0 : toS (p : ↥Pl) ≠ 0 := nonZeroDivisors.ne_zero (hnzdS _ hp0Pl)
  have hKinj : Function.Injective (algebraMap (Localization.AtPrime 𝔔) K) :=
    IsFractionRing.injective (Localization.AtPrime 𝔔) K
  intro h h1 h2

  have h2' : ∀ 𝔮 : Ideal (Localization.AtPrime 𝔔), 𝔮.IsPrime → toS (p : ↥Pl) ∉ 𝔮 →
      ∃ a s : (Localization.AtPrime 𝔔), s ∉ 𝔮 ∧ h * algebraMap (Localization.AtPrime 𝔔) K s =
        algebraMap (Localization.AtPrime 𝔔) K a := by
    intro 𝔮 h𝔮 hp𝔮
    refine h2 𝔮 h𝔮 ?_
    haveI : (𝔮.comap toS).IsPrime := Ideal.comap_isPrime toS 𝔮
    refine ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime (Fact.out) Pl hPl _ ?_
    intro heq
    apply hp𝔮
    have : (p : ↥Pl) ∈ 𝔮.comap toS := heq ▸ hpmax
    rwa [Ideal.mem_comap] at this
  obtain ⟨N, a', ha'⟩ := LocalPlAlgebra.exists_pow_mul_eq_algebraMap (toS (p : ↥Pl)) h h2'

  choose a c hc hac using h1
  have heqS : ∀ i, a' * c i = (toS (p : ↥Pl)) ^ N * a i := by
    intro i
    apply hKinj
    rw [map_mul, map_mul, ← ha', ← hac i]
    ring

  obtain ⟨⟨α', sa'⟩, hα'⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl a'
  dsimp only at hα'
  have hfrac : ∀ i, ∃ (α γ : ↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (sa sc t : 𝔔.primeCompl),
      IsLocalization.mk' (Localization.AtPrime 𝔔) α sa = a i ∧
      IsLocalization.mk' (Localization.AtPrime 𝔔) γ sc = c i ∧
      (t : ↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) * (↑sa * (α' * γ)) =
        ↑t * ((↑sa' * ↑sc) * (((p : ↥Pl) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B)) ^ N * α)) := by
    intro i
    obtain ⟨⟨α, sa⟩, hα⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl (a i)
    obtain ⟨⟨γ, sc⟩, hγ⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl (c i)
    dsimp only at hα hγ
    have hpT : (toS (p : ↥Pl)) ^ N = algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime 𝔔)
        (((p : ↥Pl) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B)) ^ N) := by
      rw [htoS, map_pow]
    have heq := heqS i
    rw [← hα, ← hγ, ← hα', ← IsLocalization.mk'_mul, hpT, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists 𝔔.primeCompl] at heq
    obtain ⟨t, ht⟩ := heq
    exact ⟨α, γ, sa, sc, t, hα, hγ, by simpa only [Submonoid.coe_mul] using ht⟩
  choose α γ sa sc t hα hγ ht using hfrac

  obtain ⟨Λ, hΛ⟩ := LocalPlAlgebra.exists_finset_forall_subset_range_map (R := ↥(GaloisRep.ratLocalizedAt p))
    ({α', ↑sa'} ∪ Finset.univ.biUnion (fun i => ({α i, γ i, ↑(sa i), ↑(sc i), ↑(t i)} :
      Finset (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B))))
  obtain ⟨A, _i1, _i2, _i3, _i4, _i5, _i6, hloc, hAinj, hΛA⟩ :=
    LocalPlAlgebra.exists_dvr_layer p Pl hPl ρ hρ halg Λ
  haveI := hloc
  have hF := hΛ A hΛA
  let ιA := Algebra.TensorProduct.map (IsScalarTower.toAlgHom (↥(GaloisRep.ratLocalizedAt p)) A ↥Pl)
    (AlgHom.id (↥(GaloisRep.ratLocalizedAt p)) B)
  let ι : A ⊗[↥(GaloisRep.ratLocalizedAt p)] B →+* ↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B := ιA.toRingHom
  have hιapp : ∀ z, ι z = ιA z := fun z => rfl
  have hιtmul : ∀ (x : A) (y : B), ιA (x ⊗ₜ y) = algebraMap A ↥Pl x ⊗ₜ y := fun x y =>
    Algebra.TensorProduct.map_tmul _ _ x y
  have hF' : ∀ z, z ∈ ({α', ↑sa'} ∪ Finset.univ.biUnion (fun i => ({α i, γ i, ↑(sa i), ↑(sc i), ↑(t i)} :
      Finset (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B)))) → ∃ z₀, ιA z₀ = z := fun z hz => hF hz
  have memi : ∀ i (z : ↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B),
      z ∈ ({α i, γ i, ↑(sa i), ↑(sc i), ↑(t i)} : Finset _) →
      z ∈ ({α', ↑sa'} ∪ Finset.univ.biUnion (fun i => ({α i, γ i, ↑(sa i), ↑(sc i), ↑(t i)} :
        Finset (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B)))) := by
    intro i z hz
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hz⟩
  obtain ⟨α₀', hα₀'⟩ := hF' α' (by simp)
  obtain ⟨sa₀', hsa₀'⟩ := hF' ↑sa' (by simp)
  have eα : ∀ i, ∃ z₀, ιA z₀ = α i := fun i => hF' _ (memi i _ (by simp))
  have eγ : ∀ i, ∃ z₀, ιA z₀ = γ i := fun i => hF' _ (memi i _ (by simp))
  have esa : ∀ i, ∃ z₀, ιA z₀ = ↑(sa i) := fun i => hF' _ (memi i _ (by simp))
  have esc : ∀ i, ∃ z₀, ιA z₀ = ↑(sc i) := fun i => hF' _ (memi i _ (by simp))
  have et : ∀ i, ∃ z₀, ιA z₀ = ↑(t i) := fun i => hF' _ (memi i _ (by simp))
  choose α₀ hα₀ using eα
  choose γ₀ hγ₀ using eγ
  choose sa₀ hsa₀ using esa
  choose sc₀ hsc₀ using esc
  choose t₀ ht₀ using et
  have hιinj : Function.Injective ιA :=
    LocalPlAlgebra.map_toAlgHom_injective (R := ↥(GaloisRep.ratLocalizedAt p)) (B := B) hAinj
  have hιp : ιA ((p : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B)) =
      (p : ↥Pl) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B) := by
    rw [hιtmul, map_natCast]
  have heqA : ∀ i, t₀ i * (sa₀ i * (α₀' * γ₀ i)) =
      t₀ i * ((sa₀' * sc₀ i) * (((p : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B)) ^ N * α₀ i)) := by
    intro i
    apply hιinj
    rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_pow,
      hα₀, hsa₀, hγ₀, hsc₀, hα₀', hsa₀', ht₀, hιp]
    exact ht i
  have hmemc : ∀ {s : A ⊗[↥(GaloisRep.ratLocalizedAt p)] B} {s' : 𝔔.primeCompl}, ιA s = ↑s' →
      s ∈ (𝔔.comap ι).primeCompl := by
    intro s s' hs hs2
    apply s'.2
    have h3 : ι s ∈ 𝔔 := hs2
    rwa [hιapp, hs] at h3
  obtain ⟨φ, hφ⟩ : ∃ φ : Localization.AtPrime (𝔔.comap ι) →+* Localization.AtPrime 𝔔,
      φ = Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl := ⟨_, rfl⟩
  have hφmk : ∀ (x : A ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (s : (𝔔.comap ι).primeCompl) (s' : 𝔔.primeCompl),
      ιA s = ↑s' → φ (IsLocalization.mk' (Localization.AtPrime (𝔔.comap ι)) x s) =
        IsLocalization.mk' (Localization.AtPrime 𝔔) (ιA x) s' := by
    intro x s s' hs
    rw [hφ, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs
  obtain ⟨X, hXdef⟩ : ∃ X : Localization.AtPrime (𝔔.comap ι),
      X = IsLocalization.mk' (Localization.AtPrime (𝔔.comap ι)) α₀' ⟨sa₀', hmemc hsa₀'⟩ := ⟨_, rfl⟩
  let Y : ιx → Localization.AtPrime (𝔔.comap ι) := fun i =>
    IsLocalization.mk' (Localization.AtPrime (𝔔.comap ι)) (γ₀ i) ⟨sc₀ i, hmemc (hsc₀ i)⟩
  let Z : ιx → Localization.AtPrime (𝔔.comap ι) := fun i =>
    IsLocalization.mk' (Localization.AtPrime (𝔔.comap ι)) (α₀ i) ⟨sa₀ i, hmemc (hsa₀ i)⟩
  have hpA0 : (p : A) ≠ 0 := by
    intro h0
    apply hp0Pl
    rw [← map_natCast (algebraMap A ↥Pl) p, h0, map_zero]
  have halgp : algebraMap A (Localization.AtPrime (𝔔.comap ι)) (p : A) =
      algebraMap (A ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime (𝔔.comap ι))
        ((p : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B)) := by
    rw [IsScalarTower.algebraMap_apply A (A ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime (𝔔.comap ι)),
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hpSA : (algebraMap A (Localization.AtPrime (𝔔.comap ι)) (p : A)) ^ N =
      algebraMap (A ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime (𝔔.comap ι))
        (((p : A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B)) ^ N) := by
    rw [halgp, map_pow]
  have hφp : φ (algebraMap A (Localization.AtPrime (𝔔.comap ι)) (p : A)) = toS (p : ↥Pl) := by
    rw [halgp, hφ, Localization.localRingHom_to_map, htoS, hιapp, hιp]
  have hXYZ : ∀ i, X * Y i = algebraMap A (Localization.AtPrime (𝔔.comap ι)) (p : A) ^ N * Z i := by
    intro i
    simp only [Y, Z]
    rw [hXdef, ← IsLocalization.mk'_mul, hpSA, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists (𝔔.comap ι).primeCompl]
    refine ⟨⟨t₀ i, hmemc (ht₀ i)⟩, ?_⟩
    rw [Submonoid.coe_mul]
    exact heqA i
  have hφY : ∀ i, Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl (Y i) ∉ 𝔯 i := by
    intro i
    have e1 : φ (Y i) = c i :=
      (hφmk (γ₀ i) ⟨sc₀ i, hmemc (hsc₀ i)⟩ (sc i) (hsc₀ i)).trans
        ((congrArg (fun z => IsLocalization.mk' (Localization.AtPrime 𝔔) z (sc i)) (hγ₀ i)).trans (hγ i))
    rw [← hφ, e1]
    exact hc i
  obtain ⟨W, hW⟩ := LocalPlAlgebra.exists_eq_pow_mul_of_forall_localRingHom_not_mem
    (R := ↥(GaloisRep.ratLocalizedAt p)) (B := B) (p : A) hpA0 𝔔 h𝔔ge 𝔯 h𝔯 h𝔭 N X Y Z hXYZ hφY
  have hφX : φ X = a' :=
    (congrArg φ hXdef).trans ((hφmk α₀' ⟨sa₀', hmemc hsa₀'⟩ sa' hsa₀').trans
      ((congrArg (fun z => IsLocalization.mk' (Localization.AtPrime 𝔔) z sa') hα₀').trans hα'))
  have ha'W : a' = (toS (p : ↥Pl)) ^ N * φ W := by
    have h1 := congrArg φ hW
    rw [map_mul, map_pow, hφp, hφX] at h1
    exact h1
  refine ⟨φ W, ?_⟩
  have h4 : algebraMap (Localization.AtPrime 𝔔) K ((toS (p : ↥Pl)) ^ N) ≠ 0 := by
    rw [map_ne_zero_iff _ hKinj]; exact pow_ne_zero N hpS0
  symm
  apply mul_right_cancel₀ h4
  rw [ha', ha'W, map_mul, mul_comm]

set_option maxHeartbeats 1600000 in

theorem node_valuation_dichotomy
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    [Algebra ↥(GaloisRep.ratLocalizedAt p) ↥Pl] (halg : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra ↥(GaloisRep.ratLocalizedAt p) B]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt p) B] [Module.Flat ↥(GaloisRep.ratLocalizedAt p) B]
    (𝔔 : Ideal (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B)) [𝔔.IsPrime]
    (h𝔔 : 𝔔.comap (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom =
      maximalIdeal ↥Pl)
    [IsDomain (Localization.AtPrime 𝔔)]
    {ιx : Type} [Fintype ιx] (𝔯 : ιx → Ideal (Localization.AtPrime 𝔔)) (h𝔯 : ∀ i, (𝔯 i).IsPrime)
    (h𝔯min : ∀ i j, 𝔯 i ≤ 𝔯 j → 𝔯 i = 𝔯 j)
    (h𝔭 : ((maximalIdeal ↥Pl).map ((algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft
          (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom)) =
      ⨅ i, 𝔯 i)
    (K : Type) [Field K] [Algebra (Localization.AtPrime 𝔔) K] [IsFractionRing (Localization.AtPrime 𝔔) K] :
    letI S := Localization.AtPrime 𝔔
    ∀ i, ∀ h : K,
      (∃ a c : S, c ∉ 𝔯 i ∧ h * algebraMap S K c = algebraMap S K a) ∨
      (∃ a c : S, c ∉ 𝔯 i ∧ h⁻¹ * algebraMap S K c = algebraMap S K a) := by
  classical
  set toS : ↥Pl →+* Localization.AtPrime 𝔔 :=
    (algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime 𝔔)).comp
      (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom
    with htoSdef
  have h𝔔ge : (maximalIdeal ↥Pl).map (Algebra.TensorProduct.includeLeft
      (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)) ≤ 𝔔 :=
    Ideal.map_le_iff_le_comap.mpr h𝔔.ge
  have htoS : ∀ a : ↥Pl, toS a = algebraMap _ (Localization.AtPrime 𝔔) (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B)) :=
    fun a => rfl
  have hnzdS : ∀ a : ↥Pl, a ≠ 0 → toS a ∈ nonZeroDivisors (Localization.AtPrime 𝔔) := fun a ha =>
    LocalPlAlgebra.algebraMap_mem_nonZeroDivisors_of_isLocalization 𝔔.primeCompl (Localization.AtPrime 𝔔) _
      (LocalPlAlgebra.tmul_one_mem_nonZeroDivisors a (mem_nonZeroDivisors_of_ne_zero ha))
  have hKinj : Function.Injective (algebraMap (Localization.AtPrime 𝔔) K) :=
    IsFractionRing.injective (Localization.AtPrime 𝔔) K
  intro i₀ h
  haveI : (𝔯 i₀).IsPrime := h𝔯 i₀
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := Localization.AtPrime 𝔔) h
  have h1𝔯 : (1 : Localization.AtPrime 𝔔) ∉ 𝔯 i₀ := fun h1 => (h𝔯 i₀).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  by_cases hx : x = 0
  · left
    exact ⟨0, 1, h1𝔯, by simp [hx]⟩
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  obtain ⟨⟨ξ, sx⟩, hξ⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl x
  obtain ⟨⟨η, sy⟩, hη⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl y
  dsimp only at hξ hη

  have hsepT : ∀ j, ∃ δ : ↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B, 𝔯 j ≠ 𝔯 i₀ →
      algebraMap _ (Localization.AtPrime 𝔔) δ ∈ 𝔯 j ∧ algebraMap _ (Localization.AtPrime 𝔔) δ ∉ 𝔯 i₀ := by
    intro j
    by_cases hj : 𝔯 j = 𝔯 i₀
    · exact ⟨0, fun h => absurd hj h⟩
    have hnle : ¬ 𝔯 j ≤ 𝔯 i₀ := fun hle => hj (h𝔯min j i₀ hle)
    obtain ⟨dS, hdS1, hdS2⟩ := SetLike.not_le_iff_exists.mp hnle
    obtain ⟨⟨δ, u⟩, hδu⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl dS
    dsimp only at hδu
    refine ⟨δ, fun _ => ⟨?_, ?_⟩⟩
    · have : algebraMap _ (Localization.AtPrime 𝔔) δ = dS * algebraMap _ _ (u : ↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) := by
        rw [← hδu, IsLocalization.mk'_spec]
      rw [this]; exact (𝔯 j).mul_mem_right _ hdS1
    · intro hmem
      apply hdS2
      rw [← hδu, IsLocalization.mk'_eq_mul_mk'_one]
      exact (𝔯 i₀).mul_mem_right _ hmem
  choose δ hδ using hsepT

  obtain ⟨Λ, hΛ⟩ := LocalPlAlgebra.exists_finset_forall_subset_range_map (R := ↥(GaloisRep.ratLocalizedAt p))
    ({ξ, ↑sx, η, ↑sy} ∪ Finset.univ.image δ : Finset (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B))
  obtain ⟨A, _i1, _i2, _i3, _i4, _i5, _i6, hloc, hAinj, hΛA⟩ :=
    LocalPlAlgebra.exists_dvr_layer p Pl hPl ρ hρ halg Λ
  haveI := hloc
  haveI : IsNoetherianRing (A ⊗[↥(GaloisRep.ratLocalizedAt p)] B) :=
    Algebra.FiniteType.isNoetherianRing A (A ⊗[↥(GaloisRep.ratLocalizedAt p)] B)
  have hF := hΛ A hΛA
  let ιA := Algebra.TensorProduct.map (IsScalarTower.toAlgHom (↥(GaloisRep.ratLocalizedAt p)) A ↥Pl)
    (AlgHom.id (↥(GaloisRep.ratLocalizedAt p)) B)
  let ι : A ⊗[↥(GaloisRep.ratLocalizedAt p)] B →+* ↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B := ιA.toRingHom
  have hιapp : ∀ z, ι z = ιA z := fun z => rfl
  have hιtmul : ∀ (x : A) (y : B), ιA (x ⊗ₜ y) = algebraMap A ↥Pl x ⊗ₜ y := fun x y =>
    Algebra.TensorProduct.map_tmul _ _ x y
  have hF' : ∀ z, z ∈ ({ξ, ↑sx, η, ↑sy} ∪ Finset.univ.image δ : Finset (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B)) →
      ∃ z₀, ιA z₀ = z := fun z hz => hF hz
  obtain ⟨ξ₀, hξ₀⟩ := hF' ξ (by simp)
  obtain ⟨sx₀, hsx₀⟩ := hF' ↑sx (by simp)
  obtain ⟨η₀, hη₀⟩ := hF' η (by simp)
  obtain ⟨sy₀, hsy₀⟩ := hF' ↑sy (by simp)
  have eδ : ∀ j, ∃ z₀, ιA z₀ = δ j := fun j =>
    hF' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem δ (Finset.mem_univ j)))
  choose δ₀ hδ₀ using eδ
  have hmemc : ∀ {s : A ⊗[↥(GaloisRep.ratLocalizedAt p)] B} {s' : 𝔔.primeCompl}, ιA s = ↑s' →
      s ∈ (𝔔.comap ι).primeCompl := by
    intro s s' hs hs2
    apply s'.2
    have h3 : ι s ∈ 𝔔 := hs2
    rwa [hιapp, hs] at h3

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hval := LocalPlAlgebra.exists_mul_eq_pow_mul_of_separated_branch
    (R := ↥(GaloisRep.ratLocalizedAt p)) (A := A) (P := ↥Pl) (B := B) ϖ hϖirr.maximalIdeal_eq 𝔔 h𝔔ge 𝔯 h𝔯 h𝔭 i₀
  obtain ⟨φ, hφ⟩ : ∃ φ : Localization.AtPrime (𝔔.comap ι) →+* Localization.AtPrime 𝔔,
      φ = Localization.localRingHom (𝔔.comap ι) 𝔔 ι rfl := ⟨_, rfl⟩
  rw [← hφ] at hval
  have hφmk : ∀ (x : A ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (s : (𝔔.comap ι).primeCompl) (s' : 𝔔.primeCompl),
      ιA s = ↑s' → φ (IsLocalization.mk' (Localization.AtPrime (𝔔.comap ι)) x s) =
        IsLocalization.mk' (Localization.AtPrime 𝔔) (ιA x) s' := by
    intro x s s' hs
    rw [hφ, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs
  have hφalg : ∀ z : A ⊗[↥(GaloisRep.ratLocalizedAt p)] B,
      φ (algebraMap _ (Localization.AtPrime (𝔔.comap ι)) z) = algebraMap _ (Localization.AtPrime 𝔔) (ιA z) := by
    intro z; rw [hφ, Localization.localRingHom_to_map]; rfl

  have hsep : ∀ j, (𝔯 j).comap φ = (𝔯 i₀).comap φ ∨ ∃ d, d ∈ (𝔯 j).comap φ ∧ d ∉ (𝔯 i₀).comap φ := by
    intro j
    by_cases hj : 𝔯 j = 𝔯 i₀
    · left; rw [hj]
    · right
      refine ⟨algebraMap _ (Localization.AtPrime (𝔔.comap ι)) (δ₀ j), ?_, ?_⟩
      · rw [Ideal.mem_comap, hφalg, hδ₀]; exact (hδ j hj).1
      · rw [Ideal.mem_comap, hφalg, hδ₀]; exact (hδ j hj).2
  specialize hval hsep

  obtain ⟨X, hXdef⟩ : ∃ X : Localization.AtPrime (𝔔.comap ι),
      X = IsLocalization.mk' (Localization.AtPrime (𝔔.comap ι)) ξ₀ ⟨sx₀, hmemc hsx₀⟩ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Localization.AtPrime (𝔔.comap ι),
      Y = IsLocalization.mk' (Localization.AtPrime (𝔔.comap ι)) η₀ ⟨sy₀, hmemc hsy₀⟩ := ⟨_, rfl⟩
  have hφX : φ X = x :=
    (congrArg φ hXdef).trans ((hφmk ξ₀ ⟨sx₀, hmemc hsx₀⟩ sx hsx₀).trans
      ((congrArg (fun z => IsLocalization.mk' (Localization.AtPrime 𝔔) z sx) hξ₀).trans hξ))
  have hφY : φ Y = y :=
    (congrArg φ hYdef).trans ((hφmk η₀ ⟨sy₀, hmemc hsy₀⟩ sy hsy₀).trans
      ((congrArg (fun z => IsLocalization.mk' (Localization.AtPrime 𝔔) z sy) hη₀).trans hη))
  have hX0 : φ X ≠ 0 := by rw [hφX]; exact hx
  have hY0 : φ Y ≠ 0 := by rw [hφY]; exact hy0
  obtain ⟨m, x₀, s₀, hXm, hs₀, hx₀⟩ := hval X hX0
  obtain ⟨n, y₀, s₁, hYn, hs₁, hy₀⟩ := hval Y hY0
  rw [hφX] at hXm
  rw [hφY] at hYn
  obtain ⟨w, hw⟩ : ∃ w : Localization.AtPrime 𝔔, w = φ (algebraMap (A ⊗[↥(GaloisRep.ratLocalizedAt p)] B)
      (Localization.AtPrime (𝔔.comap ι)) (ϖ ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] (1 : B))) := ⟨_, rfl⟩
  rw [← hw] at hXm hYn
  have hw' : w = toS (algebraMap A ↥Pl ϖ) := by rw [hw, hφalg, htoS, hιtmul]
  have hϖPl0 : algebraMap A ↥Pl ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ hAinj]; exact hϖirr.ne_zero
  have hw0 : w ≠ 0 := by rw [hw']; exact nonZeroDivisors.ne_zero (hnzdS _ hϖPl0)
  have hKx : algebraMap (Localization.AtPrime 𝔔) K x ≠ 0 := by rw [map_ne_zero_iff _ hKinj]; exact hx
  have hKy : algebraMap (Localization.AtPrime 𝔔) K y ≠ 0 := by rw [map_ne_zero_iff _ hKinj]; exact hy0
  rcases Nat.lt_or_ge m n with hmn | hnm
  swap
  · left
    refine ⟨w ^ (m - n) * φ x₀ * φ s₁, φ s₀ * φ y₀, fun hmem => ?_, ?_⟩
    · rcases (h𝔯 i₀).mem_or_mem hmem with h1 | h2
      · exact hs₀ h1
      · exact hy₀ h2
    · have hS : x * (φ s₀ * φ y₀) = (w ^ (m - n) * φ x₀ * φ s₁) * y := by
        calc x * (φ s₀ * φ y₀) = (x * φ s₀) * φ y₀ := by ring
          _ = w ^ m * φ x₀ * φ y₀ := by rw [hXm]
          _ = w ^ (m - n) * w ^ n * φ x₀ * φ y₀ := by rw [pow_sub_mul_pow w hnm]
          _ = w ^ (m - n) * φ x₀ * (y * φ s₁) := by rw [hYn]; ring
          _ = (w ^ (m - n) * φ x₀ * φ s₁) * y := by ring
      rw [div_mul_eq_mul_div, div_eq_iff hKy]
      calc algebraMap _ K x * algebraMap _ K (φ s₀ * φ y₀)
          = algebraMap _ K (x * (φ s₀ * φ y₀)) := (map_mul _ _ _).symm
        _ = algebraMap _ K ((w ^ (m - n) * φ x₀ * φ s₁) * y) := by rw [hS]
        _ = _ := map_mul _ _ _
  · right
    refine ⟨w ^ (n - m) * φ y₀ * φ s₀, φ s₁ * φ x₀, fun hmem => ?_, ?_⟩
    · rcases (h𝔯 i₀).mem_or_mem hmem with h1 | h2
      · exact hs₁ h1
      · exact hx₀ h2
    · have hS : y * (φ s₁ * φ x₀) = (w ^ (n - m) * φ y₀ * φ s₀) * x := by
        calc y * (φ s₁ * φ x₀) = (y * φ s₁) * φ x₀ := by ring
          _ = w ^ n * φ y₀ * φ x₀ := by rw [hYn]
          _ = w ^ (n - m) * w ^ m * φ y₀ * φ x₀ := by rw [pow_sub_mul_pow w hmn.le]
          _ = w ^ (n - m) * φ y₀ * (x * φ s₀) := by rw [hXm]; ring
          _ = (w ^ (n - m) * φ y₀ * φ s₀) * x := by ring
      rw [inv_div, div_mul_eq_mul_div, div_eq_iff hKx]
      calc algebraMap _ K y * algebraMap _ K (φ s₁ * φ x₀)
          = algebraMap _ K (y * (φ s₁ * φ x₀)) := (map_mul _ _ _).symm
        _ = algebraMap _ K ((w ^ (n - m) * φ y₀ * φ s₀) * x) := by rw [hS]
        _ = _ := map_mul _ _ _

theorem solution
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))

    [Algebra ↥(GaloisRep.ratLocalizedAt p) ↥Pl] (halg : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra ↥(GaloisRep.ratLocalizedAt p) B]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt p) B] [Module.Flat ↥(GaloisRep.ratLocalizedAt p) B]
    (𝔔 : Ideal (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B)) [𝔔.IsPrime]
    (h𝔔 : 𝔔.comap (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom =
      maximalIdeal ↥Pl)
    [IsDomain (Localization.AtPrime 𝔔)]

    {m : ℕ} (𝔯 : Fin m → Ideal (Localization.AtPrime 𝔔)) (h𝔯 : ∀ i, (𝔯 i).IsPrime)

    (h𝔯min : ∀ i j, 𝔯 i ≤ 𝔯 j → 𝔯 i = 𝔯 j)
    (h𝔭 : (maximalIdeal ↥Pl).map ((algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft
          (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom) = ⨅ i, 𝔯 i)
    (K : Type) [Field K] [Algebra (Localization.AtPrime 𝔔) K] [IsFractionRing (Localization.AtPrime 𝔔) K] :
    letI S := Localization.AtPrime 𝔔
    letI toS : ↥Pl →+* S := (algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) S).comp
      (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom
    letI 𝔭 : Ideal S := (maximalIdeal ↥Pl).map toS

    (∀ h : K,
      (∀ i, ∃ a c : S, c ∉ 𝔯 i ∧ h * algebraMap S K c = algebraMap S K a) →
      (∀ 𝔮 : Ideal S, 𝔮.IsPrime → 𝔮.comap toS = ⊥ →
        ∃ a s : S, s ∉ 𝔮 ∧ h * algebraMap S K s = algebraMap S K a) →
      h ∈ Set.range (algebraMap S K)) ∧

    (∀ i, ∀ h : K,
      (∃ a c : S, c ∉ 𝔯 i ∧ h * algebraMap S K c = algebraMap S K a) ∨
      (∃ a c : S, c ∉ 𝔯 i ∧ h⁻¹ * algebraMap S K c = algebraMap S K a)) :=
  ⟨node_mem_range_of_forall_comap_eq_bot p Pl hPl ρ hρ halg B 𝔔 h𝔔 𝔯 h𝔯 h𝔭 K,
   node_valuation_dichotomy p Pl hPl ρ hρ halg B 𝔔 h𝔔 𝔯 h𝔯 h𝔯min h𝔭 K⟩

end S_Localization_AtPrime_mem_range_of_forall_branch_of_forall_comap_eq_bot_and_valuation_dichotomy_of_map_eq_iInf_tensorProduct_valuationSubring_of_liesOverPrime
end P2MW
export P2MW.S_Localization_AtPrime_mem_range_of_forall_branch_of_forall_comap_eq_bot_and_valuation_dichotomy_of_map_eq_iInf_tensorProduct_valuationSubring_of_liesOverPrime (solution)
