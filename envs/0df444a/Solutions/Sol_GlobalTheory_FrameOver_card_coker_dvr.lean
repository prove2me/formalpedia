-- Prove2me | solution 1 for GlobalTheory.FrameOver.card_coker_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:52.420677+00:00
-- url     : https://prove2.me/submissions/348ed5ec-1565-4950-8999-54af30ea910e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameOver
namespace GlobalTheory.FrameOver
theorem _root_.solution {R M : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] {ϖ : R}
    (hϖ : Irreducible ϖ) (φ : M →ₗ[R] M) (n : ℕ) (hd : Associated (LinearMap.det φ) (ϖ ^ n)) :
    Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n := by
  have hd0 : LinearMap.det φ ≠ 0 := hd.ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hd0 (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)
  let N := LinearMap.range φ
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hinj
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype.comp (e' : M →ₗ[R] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    have : f (b' i) = b'.equiv ab (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have h1 : Associated (LinearMap.det φ) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv N.subtype e e'
  have h2 : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  have h3 : Associated (∏ i, a i) (ϖ ^ n) := h2 ▸ h1.symm.trans hd
  have ha0 : ∀ i, a i ≠ 0 := fun i => Submodule.smithNormalFormCoeffs_ne_zero b h i
  choose k hk using fun i => IsDiscreteValuationRing.associated_pow_irreducible (ha0 i) hϖ
  have h4 : Associated (∏ i, a i) (ϖ ^ ∑ i, k i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ fun i _ => hk i
  have h5 : ∑ i, k i = n := by
    have h6 := h4.symm.trans h3
    exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h6.dvd)
      ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h6.symm.dvd)
  have hp : (Ideal.span {ϖ}).IsPrime := hϖ.maximalIdeal_eq ▸ inferInstance
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi, ← h5,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hq := cardQuot_pow_of_prime (P := Ideal.span {ϖ})
    (fun h => hϖ.ne_zero (Ideal.span_singleton_eq_bot.1 h)) (i := k i)
  rw [Ideal.span_singleton_pow, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  rw [← hq, ← Ideal.span_singleton_eq_span_singleton.2 (hk i)]
end GlobalTheory.FrameOver
