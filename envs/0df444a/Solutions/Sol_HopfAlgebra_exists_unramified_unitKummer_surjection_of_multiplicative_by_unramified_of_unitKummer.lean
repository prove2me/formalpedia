-- Prove2me | solution 1 for HopfAlgebra.exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3a853f6a-1924-53cf-8bef-f05590317538

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one
import Theorems.Thm_padicPlace_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace UnitKummerSurjection

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => AlgebraicClosure ℚ_[p]
local notation "Γ" => (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
local notation "I" => ValuationSubring.inertiaSubgroupIn ℚ_[p] (padicIntegers p)

theorem exists_mem_inertia_apply_eq_pow (k : ℕ) (a : (ZMod (p ^ k))ˣ) :
    ∃ σ ∈ I, ∀ μ : Ω, μ ^ p ^ k = 1 → σ μ = μ ^ (a : ZMod (p ^ k)).val := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨σ, hσI, hσ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one (padicPlace p) hp
      (padicPlace_liesOverPrime p) k a
  obtain ⟨τ, hτI, hτσ⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq p σ hσI
  refine ⟨τ, hτI, ?_⟩

  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ₀ (p ^ k) := by
    have hdeg : (Polynomial.cyclotomic (p ^ k) (AlgebraicClosure ℚ)).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos _)).ne'
    obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨ζ₀, (Polynomial.isRoot_cyclotomic_iff_charZero (NeZero.pos _)).mp hζ₀⟩
  have hζ : IsPrimitiveRoot (padicEmbedding p ζ₀) (p ^ k) :=
    hζ₀.map_of_injective (padicEmbedding p).toRingHom.injective
  intro μ hμ
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  have hj : (ζ₀ ^ j) ^ p ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow]
  have h2 : σ (ζ₀ ^ j) = (ζ₀ ^ j) ^ (a : ZMod (p ^ k)).val := hσ _ hj
  rw [← map_pow, ← padicEmbedding_localGaloisToGlobal, hτσ]
  erw [h2]
  rw [map_pow]

section Bookkeeping

variable {p}
variable (N : ℕ) {M : Type} [AddCommGroup M] (hpM : ∀ x : M, (p ^ N) • x = 0)

omit [Fact p.Prime] in
include hpM in

lemma nsmul_eq_nsmul_of_modEq_pow {c d : ℕ} (h : c ≡ d [MOD p ^ N]) (x : M) : c • x = d • x := by
  have key : ∀ e : ℕ, e • x = (e % p ^ N) • x := fun e => by
    conv_lhs => rw [← Nat.div_add_mod e (p ^ N), add_nsmul, mul_comm, mul_nsmul', hpM, smul_zero, zero_add]
  rw [key c, key d, h]

variable (ζ : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ (p ^ N))

include hζ in
lemma modEq_of_pow_eq_pow {c d : ℕ} (h : ζ ^ c = ζ ^ d) : c ≡ d [MOD p ^ N] := by
  have hk : 0 < p ^ N := pow_pos (Nat.Prime.pos Fact.out) N
  have key : ∀ e : ℕ, ζ ^ e = ζ ^ (e % p ^ N) := fun e => by
    conv_lhs => rw [← Nat.div_add_mod e (p ^ N), pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  exact hζ.pow_inj (Nat.mod_lt _ hk) (Nat.mod_lt _ hk) (by rw [← key, ← key, h])

variable (n : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → ℕ)
  (hn : ∀ (τ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (ξ : AlgebraicClosure ℚ_[p]), ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ)

include hζ hn in

lemma n_mul_modEq (σ τ : Γ) : n (σ * τ) ≡ n σ * n τ [MOD p ^ N] := by
  apply modEq_of_pow_eq_pow N ζ hζ
  have h1 := hn (σ * τ) ζ hζ.pow_eq_one
  rw [AlgEquiv.mul_apply, hn τ ζ hζ.pow_eq_one, map_pow, hn σ ζ hζ.pow_eq_one, ← pow_mul] at h1
  exact h1.symm

include hζ hn in
lemma n_one_modEq : n 1 ≡ 1 [MOD p ^ N] := by
  apply modEq_of_pow_eq_pow N ζ hζ
  rw [pow_one, ← hn 1 ζ hζ.pow_eq_one, AlgEquiv.one_apply]

include hζ hn in

lemma n_modEq_one_of_apply_eq (σ : Γ) (hσ : σ ζ = ζ) : n σ ≡ 1 [MOD p ^ N] := by
  apply modEq_of_pow_eq_pow N ζ hζ
  rw [pow_one, ← hn σ ζ hζ.pow_eq_one, hσ]

include hζ hn in

lemma n_modEq_of_forall_apply_eq_pow (σ : Γ) (a : ℕ) (hσ : ∀ ξ : Ω, ξ ^ p ^ N = 1 → σ ξ = ξ ^ a) :
    n σ ≡ a [MOD p ^ N] := by
  apply modEq_of_pow_eq_pow N ζ hζ
  rw [← hn σ ζ hζ.pow_eq_one, hσ ζ hζ.pow_eq_one]

include hn in

lemma comm_apply_eq_self (σ τ : Γ) (ξ : Ω) (hξ : ξ ^ p ^ N = 1) : (σ * τ * σ⁻¹ * τ⁻¹) ξ = ξ := by
  have hpow : ∀ (γ : Γ) (e : ℕ), (ξ ^ e) ^ p ^ N = 1 := fun γ e => by
    rw [← pow_mul, mul_comm, pow_mul, hξ, one_pow]

  have hσ : ξ ^ (n σ⁻¹ * n σ) = ξ := by
    conv_rhs => rw [← σ.apply_symm_apply ξ]
    rw [pow_mul, ← hn σ⁻¹ ξ hξ, ← hn σ _ (by rw [← map_pow, hξ, map_one])]
    rfl
  have hτ : ξ ^ (n τ⁻¹ * n τ) = ξ := by
    conv_rhs => rw [← τ.apply_symm_apply ξ]
    rw [pow_mul, ← hn τ⁻¹ ξ hξ, ← hn τ _ (by rw [← map_pow, hξ, map_one])]
    rfl
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn τ⁻¹ ξ hξ, map_pow, hn σ⁻¹ ξ hξ,
    ← pow_mul, map_pow, hn τ ξ hξ, ← pow_mul, map_pow, hn σ ξ hξ, ← pow_mul,
    show n σ * (n τ * (n σ⁻¹ * n τ⁻¹)) = (n τ⁻¹ * n τ) * (n σ⁻¹ * n σ) by ring, pow_mul, hτ, hσ]

end Bookkeeping

lemma mem_decompositionSubgroup (σ : Γ) : σ ∈ (padicIntegers p).decompositionSubgroup ℚ_[p] := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, mem_padicIntegers_iff,
    mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]

lemma conj_mem_inertia (σ τ : Γ) (hτ : τ ∈ I) : σ * τ * σ⁻¹ ∈ I := by
  obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ
  refine Subgroup.mem_map.mpr ⟨⟨σ, mem_decompositionSubgroup p σ⟩ * τ₀ * ⟨σ, mem_decompositionSubgroup p σ⟩⁻¹,
    ?_, rfl⟩
  have hN : ((padicIntegers p).inertiaSubgroup ℚ_[p]).Normal := by
    unfold ValuationSubring.inertiaSubgroup; infer_instance
  exact hN.conj_mem τ₀ hτ₀ _

lemma comm_mem_inertia (g σ : Γ) (hg : g ∈ I) : g * σ * g⁻¹ * σ⁻¹ ∈ I := by
  have h := conj_mem_inertia p σ g⁻¹ ((I).inv_mem hg)
  simpa [mul_assoc] using (I).mul_mem hg (by simpa [mul_assoc] using h)

section Level

variable {p}
variable (N : ℕ) (M : Type) [AddCommGroup M]
  [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
  (M₁ : AddSubgroup M) (n : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → ℕ) {t : ℕ}
  (u : Fin t → AlgebraicClosure ℚ_[p])
  (hpM : ∀ x : M, (p ^ N) • x = 0)
  (hM₁ : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])), ∀ y ∈ M₁, σ • y ∈ M₁)
  (ζ : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ (p ^ N))
  (hn : ∀ (τ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (ξ : AlgebraicClosure ℚ_[p]),
    ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ)

def levelSubgroup : Subgroup Γ where
  carrier := {σ | (∀ y ∈ M₁, σ • y = n σ • y) ∧ (∀ x : M, σ • x - x ∈ M₁) ∧ ∀ i, σ (u i) = u i}
  mul_mem' := by
    rintro σ τ ⟨hσ1, hσ2, hσ3⟩ ⟨hτ1, hτ2, hτ3⟩
    refine ⟨fun y hy => ?_, fun x => ?_, fun i => by rw [AlgEquiv.mul_apply, hτ3, hσ3]⟩
    · rw [mul_smul, hτ1 y hy, smul_comm, hσ1 y hy, smul_smul, mul_comm (n τ) (n σ),
        nsmul_eq_nsmul_of_modEq_pow N hpM (n_mul_modEq N ζ hζ n hn σ τ).symm]
    · have : (σ * τ) • x - x = σ • (τ • x - x) + (σ • x - x) := by rw [mul_smul, smul_sub]; abel
      rw [this]
      exact M₁.add_mem (hM₁ σ _ (hτ2 x)) (hσ2 x)
  one_mem' := by
    refine ⟨fun y _ => ?_, fun x => by rw [one_smul, sub_self]; exact M₁.zero_mem, fun i => rfl⟩
    rw [one_smul, nsmul_eq_nsmul_of_modEq_pow N hpM (n_one_modEq N ζ hζ n hn), one_nsmul]
  inv_mem' := by
    rintro σ ⟨hσ1, hσ2, hσ3⟩
    refine ⟨fun y hy => ?_, fun x => ?_, fun i => ?_⟩
    · have hw : σ⁻¹ • y ∈ M₁ := hM₁ σ⁻¹ y hy
      have h1 : y = n σ • σ⁻¹ • y := by rw [← hσ1 _ hw, smul_inv_smul]
      have hmod : n σ⁻¹ * n σ ≡ 1 [MOD p ^ N] :=
        ((n_mul_modEq N ζ hζ n hn σ⁻¹ σ).symm.trans (by rw [inv_mul_cancel]; exact n_one_modEq N ζ hζ n hn))
      conv_rhs => rw [h1, smul_smul, nsmul_eq_nsmul_of_modEq_pow N hpM hmod, one_nsmul]
    · have : σ⁻¹ • x - x = σ⁻¹ • (-(σ • x - x)) := by rw [neg_sub, smul_sub, inv_smul_smul]
      rw [this]
      exact hM₁ σ⁻¹ _ (M₁.neg_mem (hσ2 x))
    · rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, hσ3]

variable {N M M₁ n u hpM hM₁ ζ hζ hn}

lemma mem_levelSubgroup_iff (σ : Γ) : σ ∈ levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn ↔
    (∀ y ∈ M₁, σ • y = n σ • y) ∧ (∀ x : M, σ • x - x ∈ M₁) ∧ ∀ i, σ (u i) = u i := Iff.rfl

lemma inertia_le_levelSubgroup
    (hmult : ∀ τ ∈ I, ∀ y ∈ M₁, τ • y = n τ • y) (hquot : ∀ τ ∈ I, ∀ x : M, τ • x - x ∈ M₁)
    (huI : ∀ i, ∀ τ ∈ I, τ (u i) = u i) :
    (I) ≤ levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn :=
  fun τ hτ => ⟨hmult τ hτ, hquot τ hτ, fun i => huI i τ hτ⟩

variable [Finite M]

lemma isOpen_levelSubgroup
    (hM : ∀ x : M, IsOpen (MulAction.stabilizer Γ x : Set Γ)) :
    IsOpen (levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn : Set Γ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have h1 : (⋂ x : M, (MulAction.stabilizer Γ x : Set Γ)) ∈ nhds (1 : Γ) :=
    (Filter.iInter_mem).2 fun x => (hM x).mem_nhds (by simp)
  have h2 : (⋂ i : Fin t, (MulAction.stabilizer Γ (u i) : Set Γ)) ∈ nhds (1 : Γ) :=
    (Filter.iInter_mem).2 fun i => (stabilizer_isOpen_of_isIntegral (K := ℚ_[p]) (u i)).mem_nhds (by simp)
  have h3 : (MulAction.stabilizer Γ ζ : Set Γ) ∈ nhds (1 : Γ) :=
    (stabilizer_isOpen_of_isIntegral (K := ℚ_[p]) ζ).mem_nhds (by simp)
  apply Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem h1 h2) h3)
  rintro σ ⟨⟨hσM, hσu⟩, hσζ⟩
  simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hσM hσu hσζ
  refine ⟨fun y _ => ?_, fun x => by rw [hσM, sub_self]; exact M₁.zero_mem, hσu⟩
  rw [hσM, nsmul_eq_nsmul_of_modEq_pow N hpM (n_modEq_one_of_apply_eq N ζ hζ n hn σ hσζ), one_nsmul]

noncomputable def levelField : IntermediateField ℚ_[p] Ω :=
  IntermediateField.fixedField (levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn)

scoped instance isAlgClosure_padicAlgCl : IsAlgClosure ℚ_[p] Ω := ⟨inferInstance, inferInstance⟩
scoped instance isGalois_padicAlgCl : IsGalois ℚ_[p] Ω := IsAlgClosure.isGalois ℚ_[p] _

lemma fixingSubgroup_levelField (hM : ∀ x : M, IsOpen (MulAction.stabilizer Γ x : Set Γ)) :
    (levelField (N := N) (M := M) (M₁ := M₁) (n := n) (u := u) (hpM := hpM) (hM₁ := hM₁) (ζ := ζ)
      (hζ := hζ) (hn := hn)).fixingSubgroup = levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn, Subgroup.isClosed_of_isOpen _ (isOpen_levelSubgroup hM)⟩

lemma finiteDimensional_levelField (hM : ∀ x : M, IsOpen (MulAction.stabilizer Γ x : Set Γ)) :
    FiniteDimensional ℚ_[p] (levelField (N := N) (M := M) (M₁ := M₁) (n := n) (u := u) (hpM := hpM)
      (hM₁ := hM₁) (ζ := ζ) (hζ := hζ) (hn := hn)) := by
  rw [← InfiniteGalois.isOpen_iff_finite]
  change IsOpen ((levelField (hpM := hpM) (hM₁ := hM₁) (hζ := hζ) (hn := hn)).fixingSubgroup : Set Γ)
  rw [fixingSubgroup_levelField hM]
  exact isOpen_levelSubgroup hM

omit [Finite M] in
lemma mem_levelField_of_forall (x : Ω) (hx : ∀ σ ∈ levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn, σ x = x) :
    x ∈ levelField (N := N) (M := M) (M₁ := M₁) (n := n) (u := u) (hpM := hpM) (hM₁ := hM₁) (ζ := ζ)
      (hζ := hζ) (hn := hn) :=
  (IntermediateField.mem_fixedField_iff _ _).2 hx

end Level

section Cocycle

variable {p}
variable (N : ℕ) {M : Type} [AddCommGroup M] (hpM : ∀ x : M, (p ^ N) • x = 0)
  (ζ : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ (p ^ N))
  (n : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → ℕ)
  (hn : ∀ (τ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (ξ : AlgebraicClosure ℚ_[p]),
    ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ)
  (S : Subgroup (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]))
  (hIS : ValuationSubring.inertiaSubgroupIn ℚ_[p] (padicIntegers p) ≤ S)
  (g₀ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]))
  (hg₀ : g₀ ∈ ValuationSubring.inertiaSubgroupIn ℚ_[p] (padicIntegers p))
  (hg₀2 : ∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → g₀ ξ = ξ ^ 2)

include hpM hζ hn hIS hg₀ hg₀2 in

lemma eq_zero_of_forall_mem_inertia (E : Γ → M)
    (hE : ∀ σ ∈ S, ∀ τ ∈ S, E (σ * τ) = E σ + n σ • E τ)
    (hE0 : ∀ τ ∈ I, E τ = 0) : ∀ σ ∈ S, E σ = 0 := by
  intro σ hσ
  have hg₀S : g₀ ∈ S := hIS hg₀
  set c := g₀ * σ * g₀⁻¹ * σ⁻¹ with hc
  have hcI : c ∈ I := comm_mem_inertia p g₀ σ hg₀
  have hcζ : c ζ = ζ := comm_apply_eq_self N n hn g₀ σ ζ hζ.pow_eq_one
  have hL : E (g₀ * σ) = 2 • E σ := by
    rw [hE g₀ hg₀S σ hσ, hE0 g₀ hg₀, zero_add,
      nsmul_eq_nsmul_of_modEq_pow N hpM (n_modEq_of_forall_apply_eq_pow N ζ hζ n hn g₀ 2 hg₀2)]
  have hR : E (c * (σ * g₀)) = E σ := by
    rw [hE c (hIS hcI) (σ * g₀) (S.mul_mem hσ hg₀S), hE0 c hcI, zero_add,
      nsmul_eq_nsmul_of_modEq_pow N hpM (n_modEq_one_of_apply_eq N ζ hζ n hn c hcζ), one_nsmul,
      hE σ hσ g₀ hg₀S, hE0 g₀ hg₀, smul_zero, add_zero]
  have hgrp : g₀ * σ = c * (σ * g₀) := by rw [hc]; group
  rw [hgrp, hR, two_nsmul] at hL
  simpa using hL

include hpM hζ hn hIS hg₀ hg₀2 in

lemma eq_coboundary_of_forall_mem_inertia_fixing (D : Γ → M)
    (hD : ∀ σ ∈ S, ∀ τ ∈ S, D (σ * τ) = D σ + n σ • D τ)
    (hD0 : ∀ τ ∈ I, (∀ ξ : Ω, ξ ^ p ^ N = 1 → τ ξ = ξ) → D τ = 0) :
    ∀ σ ∈ S, D σ = n σ • D g₀ - D g₀ := by
  have hg₀S : g₀ ∈ S := hIS hg₀

  have step1 : ∀ τ ∈ I, D τ = n τ • D g₀ - D g₀ := by
    intro τ hτ
    set c := g₀ * τ * g₀⁻¹ * τ⁻¹ with hc
    have hcI : c ∈ I := comm_mem_inertia p g₀ τ hg₀
    have hcfix : ∀ ξ : Ω, ξ ^ p ^ N = 1 → c ξ = ξ := fun ξ hξ => comm_apply_eq_self N n hn g₀ τ ξ hξ
    have hL : D (g₀ * τ) = D g₀ + 2 • D τ := by
      rw [hD g₀ hg₀S τ (hIS hτ),
        nsmul_eq_nsmul_of_modEq_pow N hpM (n_modEq_of_forall_apply_eq_pow N ζ hζ n hn g₀ 2 hg₀2)]
    have hR : D (c * (τ * g₀)) = D τ + n τ • D g₀ := by
      rw [hD c (hIS hcI) (τ * g₀) (S.mul_mem (hIS hτ) hg₀S), hD0 c hcI hcfix, zero_add,
        nsmul_eq_nsmul_of_modEq_pow N hpM (n_modEq_one_of_apply_eq N ζ hζ n hn c (hcfix ζ hζ.pow_eq_one)),
        one_nsmul, hD τ (hIS hτ) g₀ hg₀S]
    have hgrp : g₀ * τ = c * (τ * g₀) := by rw [hc]; group
    rw [hgrp, hR, two_nsmul, ← add_assoc, add_comm (D τ) (n τ • D g₀)] at hL
    rw [eq_sub_iff_add_eq, add_comm]
    exact (add_right_cancel hL).symm

  set z := D g₀ with hz
  have hE := eq_zero_of_forall_mem_inertia N hpM ζ hζ n hn S hIS g₀ hg₀ hg₀2
    (fun σ => D σ - (n σ • z - z)) (fun σ hσ τ hτ => by
      have hmod : n (σ * τ) • z = n σ • n τ • z := by
        rw [smul_smul, nsmul_eq_nsmul_of_modEq_pow N hpM (n_mul_modEq N ζ hζ n hn σ τ)]
      rw [hD σ hσ τ hτ, hmod, nsmul_sub, nsmul_sub]
      abel) (fun τ hτ => by rw [step1 τ hτ, sub_self])
  intro σ hσ
  exact sub_eq_zero.mp (hE σ hσ)

end Cocycle

end UnitKummerSurjection
p2m_reactivate "P2MW.S_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer.UnitKummerSurjection"

open UnitKummerSurjection in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ)
    (M : Type) [AddCommGroup M] [Finite M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (hM : ∀ x : M, IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x : Set (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])))
    (hpM : ∀ x : M, (p ^ N) • x = 0)
    (M₁ : AddSubgroup M) (hM₁ : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])), ∀ y ∈ M₁, σ • y ∈ M₁)
    (n : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → ℕ)
    (hn : ∀ (τ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (ξ : AlgebraicClosure ℚ_[p]), ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ)
    (hmult : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ y ∈ M₁, τ • y = n τ • y)
    (hquot : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ x : M, τ • x - x ∈ M₁)
    (ζ : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ_[p])
    (hu : ∀ i, (padicIntegers p).valuation (u i) = 1)
    (huI : ∀ i, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], τ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (φ : Fin t → (M →+ M)) (hφ₁ : ∀ i x, φ i x ∈ M₁) (hφ₀ : ∀ i, ∀ y ∈ M₁, φ i y = 0)
    (hdec : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], (∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → ∀ x : M, τ • x - x = ∑ i, (k i) • φ i x) :
    ∃ (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])), FiniteDimensional ℚ_[p] ↥K ∧
      (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ K.fixingSubgroup ∧
      (∀ σ ∈ K.fixingSubgroup, ∀ y ∈ M₁, σ • y = n σ • y) ∧
      (∀ σ ∈ K.fixingSubgroup, ∀ x : M, σ • x - x ∈ M₁) ∧
      ∃ (b a : ℕ) (r ρ : Fin b → Fin a → AlgebraicClosure ℚ_[p]) (κ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → Fin b → Fin a → ℕ),
        (∀ m k, r m k ∈ K) ∧ (∀ m k, (padicIntegers p).valuation (r m k) = 1) ∧ (∀ m k, ρ m k ^ p ^ N = r m k) ∧
        (∀ σ ∈ K.fixingSubgroup, ∀ m k, σ (ρ m k) = ζ ^ κ σ m k * ρ m k) ∧
        ∃ π : (Fin b → ZMod (p ^ N)) × (Fin a → ZMod (p ^ N)) →+ M, Function.Surjective π ∧
          ∀ σ ∈ K.fixingSubgroup, ∀ (i : Fin b → ZMod (p ^ N)) (l : Fin a → ZMod (p ^ N)),
            π (fun m => n σ • i m + ∑ k, κ σ m k • l k, l) = σ • π (i, l) := by
  classical
  have hp : p.Prime := Fact.out
  have hn0 : 0 < p ^ N := pow_pos hp.pos N
  haveI : NeZero (p ^ N) := ⟨hn0.ne'⟩

  have hIS : (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn :=
    inertia_le_levelSubgroup hmult hquot huI
  set S := levelSubgroup N M M₁ n u hpM hM₁ ζ hζ hn with hSdef
  set K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
    levelField (N := N) (M := M) (M₁ := M₁) (n := n) (u := u) (hpM := hpM) (hM₁ := hM₁) (ζ := ζ) (hζ := hζ)
      (hn := hn) with hKdef
  have hKfix : K.fixingSubgroup = S := fixingSubgroup_levelField hM
  have hKfd : FiniteDimensional ℚ_[p] K := finiteDimensional_levelField hM
  have hmemS : ∀ σ ∈ S, (∀ y ∈ M₁, σ • y = n σ • y) ∧ (∀ x : M, σ • x - x ∈ M₁) ∧ ∀ i, σ (u i) = u i :=
    fun σ hσ => (mem_levelSubgroup_iff σ).1 hσ

  obtain ⟨b, ⟨eM₁⟩⟩ := Finite.exists_equiv_fin (↥M₁)
  obtain ⟨a, ⟨eM⟩⟩ := Finite.exists_equiv_fin M
  let y : Fin b → M := fun m => ((eM₁.symm m : ↥M₁) : M)
  let x : Fin a → M := fun k => eM.symm k
  have hy : ∀ m, y m ∈ M₁ := fun m => (eM₁.symm m).2
  let A : Fin t → Fin b → Fin a → ℕ := fun i m k => if eM₁ ⟨φ i (x k), hφ₁ i (x k)⟩ = m then 1 else 0
  have hA : ∀ i k, φ i (x k) = ∑ m, A i m k • y m := by
    intro i k
    simp only [A, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, y,
      Equiv.symm_apply_apply]
  let r : Fin b → Fin a → AlgebraicClosure ℚ_[p] := fun m k => ∏ i, u i ^ A i m k
  let ρ : Fin b → Fin a → AlgebraicClosure ℚ_[p] := fun m k => ∏ i, β i ^ A i m k
  have hρr : ∀ m k, ρ m k ^ p ^ N = r m k := by
    intro m k
    simp only [ρ, r, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hβ]
  have hu0 : ∀ i, u i ≠ 0 := by
    intro i h0
    have h1 := hu i
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hβ0 : ∀ i, β i ≠ 0 := by
    intro i h0
    apply hu0 i
    rw [← hβ i, h0, zero_pow hn0.ne']
  have hρ0 : ∀ m k, ρ m k ≠ 0 := fun m k => Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hβ0 i)
  have hrval : ∀ m k, (padicIntegers p).valuation (r m k) = 1 := by
    intro m k
    simp only [r, map_prod, map_pow, hu, one_pow, Finset.prod_const_one]
  have hrS : ∀ σ ∈ S, ∀ m k, σ (r m k) = r m k := by
    intro σ hσ m k
    simp only [r, map_prod, map_pow, (hmemS σ hσ).2.2]
  have hrK : ∀ m k, r m k ∈ K := fun m k => mem_levelField_of_forall _ (fun σ hσ => hrS σ hσ m k)

  have hκex : ∀ σ ∈ S, ∀ m k, ∃ j : ℕ, σ (ρ m k) = ζ ^ j * ρ m k := by
    intro σ hσ m k
    have h1 : (σ (ρ m k) / ρ m k) ^ p ^ N = 1 := by
      rw [div_pow, ← map_pow, hρr, hrS σ hσ, ← hρr, div_self (pow_ne_zero _ (hρ0 m k))]
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
    exact ⟨j, by rw [hj, div_mul_cancel₀ _ (hρ0 m k)]⟩
  let κ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → Fin b → Fin a → ℕ := fun σ m k =>
    if h : ∃ j : ℕ, σ (ρ m k) = ζ ^ j * ρ m k then h.choose else 0
  have hκ : ∀ σ ∈ S, ∀ m k, σ (ρ m k) = ζ ^ κ σ m k * ρ m k := by
    intro σ hσ m k
    simp only [κ, dif_pos (hκex σ hσ m k)]
    exact (hκex σ hσ m k).choose_spec
  have hκmul : ∀ σ ∈ S, ∀ τ ∈ S, ∀ m k, κ (σ * τ) m k ≡ κ σ m k + n σ * κ τ m k [MOD p ^ N] := by
    intro σ hσ τ hτ m k
    apply modEq_of_pow_eq_pow N ζ hζ
    apply mul_right_cancel₀ (hρ0 m k)
    rw [← hκ (σ * τ) (S.mul_mem hσ hτ), AlgEquiv.mul_apply, hκ τ hτ, map_mul, map_pow, hn σ ζ hζ.pow_eq_one,
      hκ σ hσ, ← pow_mul, ← mul_assoc, ← pow_add, add_comm]
  have hκI : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ kk : Fin t → ℕ,
      (∀ i, τ (β i) = ζ ^ kk i * β i) → ∀ m k, κ τ m k ≡ ∑ i, kk i * A i m k [MOD p ^ N] := by
    intro τ hτ kk hkk m k
    apply modEq_of_pow_eq_pow N ζ hζ
    apply mul_right_cancel₀ (hρ0 m k)
    rw [← hκ τ (hIS hτ)]
    simp only [ρ, map_prod, map_pow, hkk, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
      Finset.prod_pow_eq_pow_sum]

  let D : Fin a → (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → M := fun k σ =>
    (σ • x k - x k) - ∑ m, κ σ m k • y m
  have hDS : ∀ k, ∀ σ ∈ S, ∀ τ ∈ S, D k (σ * τ) = D k σ + n σ • D k τ := by
    intro k σ hσ τ hτ
    obtain ⟨hσ1, -, -⟩ := hmemS σ hσ
    obtain ⟨-, hτ2, -⟩ := hmemS τ hτ
    have e1 : (σ * τ) • x k - x k = σ • (τ • x k - x k) + (σ • x k - x k) := by rw [mul_smul, smul_sub]; abel
    have e2 : σ • (τ • x k - x k) = n σ • (τ • x k - x k) := hσ1 _ (hτ2 (x k))
    have e3 : ∑ m, κ (σ * τ) m k • y m = ∑ m, κ σ m k • y m + n σ • ∑ m, κ τ m k • y m := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [nsmul_eq_nsmul_of_modEq_pow N hpM (hκmul σ hσ τ hτ m k), add_nsmul, ← smul_smul]
    simp only [D]
    rw [e1, e2, e3]
    simp only [smul_sub]
    abel
  have hD0 : ∀ k, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p],
      (∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → τ ξ = ξ) → D k τ = 0 := by
    intro k τ hτ hτfix
    have hkex : ∀ i, ∃ j : ℕ, τ (β i) = ζ ^ j * β i := by
      intro i
      have h1 : (τ (β i) / β i) ^ p ^ N = 1 := by
        rw [div_pow, ← map_pow, hβ, huI i τ hτ, ← hβ, div_self (pow_ne_zero _ (hβ0 i))]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
      exact ⟨j, by rw [hj, div_mul_cancel₀ _ (hβ0 i)]⟩
    choose kk hkk using hkex
    have h1 := hdec τ hτ hτfix kk hkk (x k)
    simp only [D]
    rw [h1, sub_eq_zero]
    simp_rw [hA, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul]
    exact nsmul_eq_nsmul_of_modEq_pow N hpM (hκI τ hτ kk hkk m k).symm (y m)

  obtain ⟨g₀, hg₀I, hg₀2⟩ : ∃ g₀ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p],
      ∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → g₀ ξ = ξ ^ 2 := by
    have h2 : Nat.Coprime 2 (p ^ N) :=
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_right N
    obtain ⟨g₀, hg₀, hg₀act⟩ := exists_mem_inertia_apply_eq_pow p N (ZMod.unitOfCoprime 2 h2)
    refine ⟨g₀, hg₀, fun η hη => ?_⟩
    have hmod : η ^ (2 % p ^ N) = η ^ 2 := by
      conv_rhs => rw [← Nat.div_add_mod 2 (p ^ N), pow_add, pow_mul, hη, one_pow, one_mul]
    have hthis := hg₀act η hη
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, hmod] at hthis
    exact hthis
  let z : Fin a → M := fun k => D k g₀
  have hDz : ∀ k, ∀ σ ∈ S, D k σ = n σ • z k - z k := fun k =>
    eq_coboundary_of_forall_mem_inertia_fixing N hpM ζ hζ n hn S hIS g₀ hg₀I hg₀2 (D k) (hDS k) (hD0 k)
  have hzM₁ : ∀ k, z k ∈ M₁ := by
    intro k
    exact M₁.sub_mem (hquot g₀ hg₀I (x k)) (M₁.sum_mem fun m _ => M₁.nsmul_mem (hy m) _)

  let x' : Fin a → M := fun k => x k - z k
  have hx' : ∀ σ ∈ S, ∀ k, σ • x' k = x' k + ∑ m, κ σ m k • y m := by
    intro σ hσ k
    obtain ⟨hσ1, -, -⟩ := hmemS σ hσ
    have h := hDz k σ hσ
    simp only [D] at h
    simp only [x', smul_sub]
    rw [hσ1 _ (hzM₁ k)]
    have h' : σ • x k - x k - (n σ • z k - z k) = ∑ m, κ σ m k • y m := by
      rw [← sub_eq_zero] at h ⊢
      rw [← h]
      abel
    rw [← h']
    abel

  letI : Module (ZMod (p ^ N)) M := AddCommGroup.zmodModule hpM
  have hzsmul : ∀ (c : ZMod (p ^ N)) (w : M), c • w = c.val • w := fun c w => by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul]
  have hσc : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (c : ZMod (p ^ N)) (w : M),
      σ • c • w = c • σ • w := fun σ c w => by rw [hzsmul, smul_comm, ← hzsmul]
  let π : (Fin b → ZMod (p ^ N)) × (Fin a → ZMod (p ^ N)) →+ M :=
    { toFun := fun v => ∑ m, v.1 m • y m + ∑ k, v.2 k • x' k
      map_zero' := by simp
      map_add' := fun v w => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        abel }
  have hπ : ∀ v, π v = ∑ m, v.1 m • y m + ∑ k, v.2 k • x' k := fun v => rfl
  refine ⟨K, hKfd, hKfix ▸ hIS, ?_, ?_, b, a, r, ρ, κ, hrK, hrval, hρr, ?_, π, ?_, ?_⟩
  · intro σ hσ; rw [hKfix] at hσ; exact (hmemS σ hσ).1
  · intro σ hσ; rw [hKfix] at hσ; exact (hmemS σ hσ).2.1
  · intro σ hσ m k; rw [hKfix] at hσ; exact hκ σ hσ m k
  ·
    intro w
    set k₀ := eM w with hk₀
    set m₀ := eM₁ ⟨z k₀, hzM₁ k₀⟩ with hm₀
    refine ⟨(Pi.single m₀ 1, Pi.single k₀ 1), ?_⟩
    rw [hπ]
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [y, x', hm₀, hk₀, Equiv.symm_apply_apply, x]
    abel
  ·
    intro σ hσ i l
    rw [hKfix] at hσ
    obtain ⟨hσ1, -, -⟩ := hmemS σ hσ
    rw [hπ, hπ]
    simp only
    rw [smul_add, Finset.smul_sum, Finset.smul_sum]
    have e1 : ∀ m, σ • i m • y m = n σ • i m • y m := fun m => by rw [hσc, hσ1 _ (hy m), smul_comm]
    have e2 : ∀ k, σ • l k • x' k = l k • x' k + ∑ m, κ σ m k • l k • y m := fun k => by
      rw [hσc, hx' σ hσ k, smul_add, Finset.smul_sum]
      refine congrArg _ (Finset.sum_congr rfl fun m _ => ?_)
      rw [smul_comm]
    simp_rw [e1, e2, add_smul, Finset.sum_add_distrib, Finset.sum_smul, smul_assoc]
    rw [Finset.sum_comm]
    abel

end S_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer
end P2MW
export P2MW.S_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer (solution)
