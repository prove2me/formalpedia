-- Prove2me | solution 1 for MarkovEntanglement.agentwise_value_locality_implies_separable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-09T16:06:25.974826+00:00
-- url     : https://prove2.me/submissions/238bc1bc-62ff-4571-b3e4-87be2ea336ca

import Definitions.Def_markov_entanglement_multi
import Theorems.Thm_MarkovEntanglement_agentwise_marginal_independence_implies_separable

open scoped BigOperators

namespace MarkovEntanglement

variable {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-! ### Part 1. The Bellman operator as a linear map -/

/-- `Q ↦ Q - γ • (P Q)`, whose fibre over `r` is the set of Bellman solutions. -/
noncomputable def bellmanMap (P : Matrix (Joint S) (Joint S) ℝ) (γ : ℝ) :
    (Joint S → ℝ) →ₗ[ℝ] (Joint S → ℝ) where
  toFun Q := fun p => Q p - γ * ∑ q, P p q * Q q
  map_add' Q₁ Q₂ := by
    funext p
    have h : ∑ q, P p q * (Q₁ q + Q₂ q) = (∑ q, P p q * Q₁ q) + ∑ q, P p q * Q₂ q := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    simp only [Pi.add_apply, h]
    ring
  map_smul' c Q := by
    funext p
    have h : ∑ q, P p q * (c * Q q) = c * ∑ q, P p q * Q q := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    simp only [Pi.smul_apply, smul_eq_mul, h, RingHom.id_apply]
    ring

lemma bellmanMap_apply (P : Matrix (Joint S) (Joint S) ℝ) (γ : ℝ) (Q : Joint S → ℝ)
    (p : Joint S) : bellmanMap P γ Q p = Q p - γ * ∑ q, P p q * Q q := rfl

lemma isBellmanQ_iff (P : Matrix (Joint S) (Joint S) ℝ) (γ : ℝ) (r Q : Joint S → ℝ) :
    IsBellmanQ P r γ Q ↔ bellmanMap P γ Q = r := by
  constructor
  · intro h
    funext p
    rw [bellmanMap_apply]
    linarith [h p]
  · intro h p
    have := congrFun h p
    rw [bellmanMap_apply] at this
    linarith

lemma bellmanMap_injective (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) : Function.Injective (bellmanMap P γ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Q hQ
  rcases isEmpty_or_nonempty (Joint S) with hE | hNE
  · funext p; exact (IsEmpty.false p).elim
  obtain ⟨p₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Joint S)) (fun p => |Q p|) Finset.univ_nonempty
  have key : ∀ p, Q p = γ * ∑ q, P p q * Q q := by
    intro p
    have := congrFun hQ p
    rw [bellmanMap_apply] at this
    simp only [Pi.zero_apply] at this
    linarith
  have hbnd : |Q p₀| ≤ γ * |Q p₀| := by
    calc |Q p₀| = |γ * ∑ q, P p₀ q * Q q| := by rw [← key p₀]
      _ = γ * |∑ q, P p₀ q * Q q| := by rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ γ * ∑ q, |P p₀ q * Q q| := by
          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hγ0
      _ = γ * ∑ q, P p₀ q * |Q q| := by
          congr 1
          exact Finset.sum_congr rfl fun q _ => by
            rw [abs_mul, abs_of_nonneg (hP.1 p₀ q)]
      _ ≤ γ * ∑ q, P p₀ q * |Q p₀| := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) hγ0
          exact mul_le_mul_of_nonneg_left (hmax q (Finset.mem_univ q)) (hP.1 p₀ q)
      _ = γ * |Q p₀| := by rw [← Finset.sum_mul, hP.2 p₀, one_mul]
  have hz : |Q p₀| = 0 := le_antisymm (by nlinarith [abs_nonneg (Q p₀)]) (abs_nonneg _)
  funext p
  have : |Q p| ≤ 0 := by
    have := hmax p (Finset.mem_univ p)
    linarith [hz]
  simpa using abs_nonpos_iff.mp this

lemma bellmanMap_bijective (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) : Function.Bijective (bellmanMap P γ) :=
  ⟨bellmanMap_injective P hP γ hγ0 hγ1,
    (LinearMap.injective_iff_surjective).mp (bellmanMap_injective P hP γ hγ0 hγ1)⟩

/-! ### Part 2. Functions that do not depend on agent `i` -/

/-- The subspace of functions on the joint space that ignore agent `i`'s coordinate. -/
def agentIndep (i : Fin N) : Submodule ℝ (Joint S → ℝ) where
  carrier := {Q | ∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → Q p = Q q}
  add_mem' := by
    intro a b ha hb p q h
    simp only [Pi.add_apply, ha p q h, hb p q h]
  zero_mem' := by intro p q _; rfl
  smul_mem' := by
    intro c a ha p q h
    simp only [Pi.smul_apply, ha p q h]

lemma mem_agentIndep {i : Fin N} {Q : Joint S → ℝ} :
    Q ∈ agentIndep i ↔ ∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → Q p = Q q := Iff.rfl

/-! ### Part 3. Value locality forces the Bellman operator to preserve `agentIndep i`

The hypothesis says the *preimage* of `agentIndep i` under the Bellman operator is contained
in `agentIndep i`.  Since the operator is bijective, that preimage has the same dimension as
`agentIndep i`, so the inclusion is an equality — which is the *forward* invariance we want. -/

lemma bellmanMap_maps_agentIndep
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hloc : ∀ (i : Fin N) (r Q : Joint S → ℝ),
      (∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → r p = r q) →
      IsBellmanQ P r γ Q →
      ∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → Q p = Q q)
    (i : Fin N) {Q : Joint S → ℝ} (hQ : Q ∈ agentIndep (S := S) i) :
    bellmanMap P γ Q ∈ agentIndep (S := S) i := by
  classical
  have hbij := bellmanMap_bijective P hP γ hγ0 hγ1
  set e : (Joint S → ℝ) ≃ₗ[ℝ] (Joint S → ℝ) := LinearEquiv.ofBijective (bellmanMap P γ) hbij
    with he
  have hle : (agentIndep (S := S) i).comap (bellmanMap P γ) ≤ agentIndep (S := S) i := by
    intro R hR
    have hRmem : bellmanMap P γ R ∈ agentIndep (S := S) i := Submodule.mem_comap.mp hR
    exact hloc i (bellmanMap P γ R) R hRmem ((isBellmanQ_iff P γ _ R).mpr rfl)
  have hcoe : (agentIndep (S := S) i).comap (bellmanMap P γ)
      = (agentIndep (S := S) i).comap (e : (Joint S → ℝ) →ₗ[ℝ] (Joint S → ℝ)) := rfl
  have hrank : Module.finrank ℝ ((agentIndep (S := S) i).comap (bellmanMap P γ))
      = Module.finrank ℝ (agentIndep (S := S) i) := by
    rw [hcoe, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have heq : (agentIndep (S := S) i).comap (bellmanMap P γ) = agentIndep (S := S) i :=
    Submodule.eq_of_le_of_finrank_eq hle hrank
  exact Submodule.mem_comap.mp (heq.ge hQ)

/-- Consequently the transition matrix itself preserves functions that ignore agent `i`. -/
lemma mulVec_mem_agentIndep
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hloc : ∀ (i : Fin N) (r Q : Joint S → ℝ),
      (∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → r p = r q) →
      IsBellmanQ P r γ Q →
      ∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → Q p = Q q)
    (i : Fin N) {Q : Joint S → ℝ} (hQ : Q ∈ agentIndep (S := S) i) :
    (fun p => ∑ q, P p q * Q q) ∈ agentIndep (S := S) i := by
  have hT := bellmanMap_maps_agentIndep P hP γ hγ.le hγ1 hloc i hQ
  intro p q hpq
  have h1 : Q p = Q q := hQ p q hpq
  have h2 : bellmanMap P γ Q p = bellmanMap P γ Q q := hT p q hpq
  rw [bellmanMap_apply, bellmanMap_apply] at h2
  have : γ * ∑ x, P p x * Q x = γ * ∑ x, P q x * Q x := by linarith
  exact mul_left_cancel₀ (ne_of_gt hγ) this

/-! ### Part 4. The entrywise consequence: the `i`-marginal ignores agent `i`'s state -/

lemma sum_update_eq (P : Matrix (Joint S) (Joint S) ℝ) (i : Fin N) (p q₀ : Joint S) :
    ∑ q : Joint S,
        P p q * (if (∀ j, j ≠ i → q j = q₀ j) then (1 : ℝ) else 0)
      = ∑ t : S i, P p (Function.update q₀ i t) := by
  classical
  have hstep : ∀ q : Joint S,
      P p q * (if (∀ j, j ≠ i → q j = q₀ j) then (1 : ℝ) else 0)
        = if (∀ j, j ≠ i → q j = q₀ j) then P p q else 0 := by
    intro q; split <;> ring
  rw [Finset.sum_congr rfl fun q _ => hstep q, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine (Finset.sum_nbij' (fun t : S i => Function.update q₀ i t) (fun q : Joint S => q i)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    exact Function.update_of_ne hj t q₀
  · intro q _; exact Finset.mem_univ _
  · intro t _; exact Function.update_self i t q₀
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    show Function.update q₀ i (q i) = q
    funext j
    by_cases hj : j = i
    · subst hj; exact Function.update_self j (q j) q₀
    · rw [Function.update_of_ne hj, hq j hj]
  · intro t _; rfl

/-- **The key entrywise condition.**  Summing the joint transition over agent `i`'s next
state gives a quantity that does not see agent `i`'s current state. -/
lemma marginal_indep_of_valueLocality
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hloc : ∀ (i : Fin N) (r Q : Joint S → ℝ),
      (∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → r p = r q) →
      IsBellmanQ P r γ Q →
      ∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → Q p = Q q)
    (i : Fin N) (p p' q₀ : Joint S) (hpp' : ∀ j, j ≠ i → p j = p' j) :
    ∑ t : S i, P p (Function.update q₀ i t) = ∑ t : S i, P p' (Function.update q₀ i t) := by
  classical
  have hQmem : (fun q : Joint S => if (∀ j, j ≠ i → q j = q₀ j) then (1 : ℝ) else 0)
      ∈ agentIndep (S := S) i := by
    intro a b hab
    simp only
    congr 1
    apply propext
    constructor
    · intro h j hj; rw [← hab j hj]; exact h j hj
    · intro h j hj; rw [hab j hj]; exact h j hj
  have hthis := mulVec_mem_agentIndep P hP γ hγ hγ1 hloc i hQmem p p' hpp'
  rw [← sum_update_eq P i p q₀, ← sum_update_eq P i p' q₀]
  exact hthis

end MarkovEntanglement

open MarkovEntanglement in
theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hloc : ∀ (i : Fin N) (r Q : Joint S → ℝ),
      (∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → r p = r q) →
      IsBellmanQ P r γ Q →
      ∀ p q : Joint S, (∀ j, j ≠ i → p j = q j) → Q p = Q q) :
    IsSeparableN P :=
  MarkovEntanglement.agentwise_marginal_independence_implies_separable P hP
    (fun i p p' q hpp' =>
      MarkovEntanglement.marginal_indep_of_valueLocality P hP γ hγ hγ1 hloc i p p' q hpp')
