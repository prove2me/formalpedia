-- Prove2me | solution 1 for GlobalTheory.CardQuotientPow.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:44.690796+00:00
-- url     : https://prove2.me/submissions/a98be6c0-77bc-4931-a007-7d9e30fe1669

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow
import Theorems.Thm_GlobalTheory_CardQuotientPow_card_quot_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardQuotientPow
open Module Submodule
namespace GlobalTheory.CardQuotientPow
theorem _root_.solution {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Module.Basis ι R M) {p : R}
    (hp : Irreducible p) (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m := by
  classical
  set N := LinearMap.range φ with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hφ
  have h : finrank R N = finrank R M := e.finrank_eq.symm
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let f : M →ₗ[R] M := N.subtype ∘ₗ (b'.equiv ab (Equiv.refl _) : M →ₗ[R] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, b'.equiv_apply, Equiv.refl_apply,
      Submodule.subtype_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hφf : Associated (LinearMap.det φ) (LinearMap.det f) := by
    have : φ = N.subtype ∘ₗ (e : M →ₗ[R] N) := by ext x; rfl
    rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  choose k hk using fun i =>
    IsDiscreteValuationRing.associated_pow_irreducible (smithNormalFormCoeffs_ne_zero b h i) hp
  refine ⟨∑ i, k i, ?_, ?_⟩
  · rw [← Finset.prod_pow_eq_pow_sum]
    refine hφf.trans ?_
    rw [hdetf]
    exact Associated.prod _ _ _ fun i _ => hk i
  · rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← card_quot_pow hp, Ideal.span_singleton_eq_span_singleton.mpr (hk i)]
end GlobalTheory.CardQuotientPow
