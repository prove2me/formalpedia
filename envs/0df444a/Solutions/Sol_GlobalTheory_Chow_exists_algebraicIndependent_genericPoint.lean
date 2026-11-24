-- Prove2me | solution 1 for GlobalTheory.Chow.exists_algebraicIndependent_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:46.939742+00:00
-- url     : https://prove2.me/submissions/3a087b45-5861-4212-bd9e-8e4a610596fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_Chow_exists_ringKrullDim_eq_and_trdeg_eq
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {σ β : Type} [Fintype σ] [Fintype β]
omit [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution [Finite σ] {p : Ideal (MvPolynomial σ K)}
    [p.IsPrime] (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) = (Fintype.card β : ℕ)) :
    ∃ κ : β → σ, AlgebraicIndependent K fun i => genericPoint p (κ i) := by
  let A := MvPolynomial σ K ⧸ p
  obtain ⟨s, hs, hs'⟩ := exists_ringKrullDim_eq_and_trdeg_eq K A
  have hsβ : s = Fintype.card β := by
    rw [hs] at hdim
    exact_mod_cast hdim
  let x : σ → A := fun j => Ideal.Quotient.mk p (X j)
  have htop : Algebra.adjoin K (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    have : aeval x = Ideal.Quotient.mkₐ K p := algHom_ext fun j => aeval_X _ _
    rw [this]
    exact Ideal.Quotient.mk_surjective
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A :=
    ⟨fun a => isAlgebraic_algebraMap (⟨a, htop ▸ trivial⟩ : Algebra.adjoin K (Set.range x))⟩
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range x)
  have hc := hb.cardinalMk_eq_trdeg
  rw [hs', hsβ] at hc
  obtain ⟨e⟩ : Nonempty (β ≃ t) := by
    rw [← Cardinal.lift_mk_eq', hc]
    simp
  choose κ hκ using fun i => ht (e i).2
  refine ⟨κ, ?_⟩
  have h1 := (hb.1.comp e e.injective).map'
    (f := IsScalarTower.toAlgHom K A (FractionRing A)) (IsFractionRing.injective A _)
  convert h1 using 2 with i
  simp [genericPoint, ← hκ, x, A]
end GlobalTheory.Chow
