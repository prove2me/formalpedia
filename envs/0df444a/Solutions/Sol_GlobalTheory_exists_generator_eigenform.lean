-- Prove2me | solution 1 for GlobalTheory.exists_generator_eigenform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:53.096009+00:00
-- url     : https://prove2.me/submissions/d6113edf-5834-4525-a127-708d63992087

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SimultaneousEigenbasisIntegral
import Theorems.Thm_GlobalTheory_exists_diagonal_operator_killing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type}
    [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ))
    (hli : LinearIndependent ℂ fun k ↦ ψ (b k))
    {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ)
    (hT : ∀ a v j, ψ (T a v) j = lam a j * ψ v j)
    (hsep : ∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k)
    (hK : ∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) (i : Fin g) :
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e := by
  classical
  obtain ⟨P, C, hC, hCs, hP⟩ :=
    exists_diagonal_operator_killing R ψ T lam hT hsep hK i (Finset.univ.erase i) (by simp)

  obtain ⟨w, hw⟩ : ∃ w, ψ w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hspan : Submodule.span ℂ (Set.range fun k ↦ ψ (b k)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by simp)
    have hle : Submodule.span ℂ (Set.range fun k ↦ ψ (b k)) ≤
        LinearMap.ker (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simpa using hcon (b k)
    rw [hspan] at hle
    have := hle (Submodule.mem_top (x := fun _ => (1 : ℂ)))
    simp at this
  have hexp : ∀ v, ψ v = ∑ k, ((b.repr v k : R) : ℂ) • ψ (b k) := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, Subring.smul_def]
  have hprop : ∀ v, ψ (P v) = (ψ v i / ψ w i) • ψ (P w) := by
    intro v
    funext k
    simp only [Pi.smul_apply, hP, smul_eq_mul]
    by_cases hk : k = i
    · subst hk; field_simp
    · rw [hCs k (by simp [hk])]; simp
  have hcoord : ∀ v k, ((b.repr (P v) k : R) : ℂ) = (ψ v i / ψ w i) * ((b.repr (P w) k : R) : ℂ) := by
    intro v k
    have h := hprop v
    rw [hexp (P v), hexp (P w), Finset.smul_sum] at h
    simp only [smul_smul] at h
    exact (Fintype.linearIndependent_iffₛ.mp hli _ _ h) k
  obtain ⟨k₀, hk₀⟩ : ∃ k, ((b.repr (P w) k : R) : ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := congrFun (hexp (P w)) i
    simp only [hcon, zero_smul, Finset.sum_const_zero, hP, Pi.zero_apply] at h
    exact mul_ne_zero hC hw h
  set e₀ : V →ₗ[R] R := b.coord k₀ ∘ₗ P with he₀
  set c₀ : ℂ := ((b.repr (P w) k₀ : R) : ℂ) / ψ w i with hc₀
  have hc₀0 : c₀ ≠ 0 := div_ne_zero hk₀ hw
  have he₀v : ∀ v, ((e₀ v : R) : ℂ) = c₀ * ψ v i := by
    intro v
    have := hcoord v k₀
    simp only [he₀, LinearMap.comp_apply, Module.Basis.coord_apply]
    rw [this, hc₀]; ring
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (LinearMap.range e₀ : Ideal R)).principal
  have hdmem : d ∈ LinearMap.range e₀ := by
    rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨v₁, hv₁⟩ := hdmem
  have hq : ∀ v, ∃ q : R, q • d = e₀ v := by
    intro v
    have : e₀ v ∈ LinearMap.range e₀ := ⟨v, rfl⟩
    rw [hd] at this
    exact Submodule.mem_span_singleton.mp this
  choose q hq using hq
  have hd0 : (d : ℂ) ≠ 0 := by
    intro h0
    have h1 := he₀v w
    rw [← hq w, smul_eq_mul, Subring.coe_mul, h0, mul_zero] at h1
    exact mul_ne_zero hc₀0 hw h1.symm
  set e : V →ₗ[R] R := b.constr R fun k => q (b k) with he
  have hde : d • e = e₀ := by
    refine b.ext fun k => ?_
    rw [LinearMap.smul_apply, he, Module.Basis.constr_basis, ← hq (b k), smul_eq_mul, smul_eq_mul,
      mul_comm]
  have hev : ∀ v, ((e v : R) : ℂ) = c₀ / d * ψ v i := by
    intro v
    have h1 := he₀v v
    rw [← hde, LinearMap.smul_apply, smul_eq_mul, Subring.coe_mul] at h1
    field_simp
    linear_combination h1
  have hv₁' : c₀ * ψ v₁ i = d := by rw [← he₀v, hv₁]
  refine ⟨e, c₀ / d, div_ne_zero hc₀0 hd0, hev, fun e' c' he' => ⟨e' v₁, ?_⟩⟩
  ext v
  rw [LinearMap.smul_apply, smul_eq_mul, Subring.coe_mul, he', he', hev]
  field_simp
  linear_combination (-(c' * ψ v i)) * hv₁'
end GlobalTheory
