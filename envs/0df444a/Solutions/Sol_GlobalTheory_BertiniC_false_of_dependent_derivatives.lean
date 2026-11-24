-- Prove2me | solution 1 for GlobalTheory.BertiniC.false_of_dependent_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:42:23.886447+00:00
-- url     : https://prove2.me/submissions/fd212952-93aa-4b06-a347-4fe28f702421

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentKaehlerDOfAlgebraicIndependentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelation
import Theorems.Thm_GlobalTheory_T_linearIndependent_kaehlerD_of_algebraicIndependent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BertiniC
open KaehlerDifferential
namespace GlobalTheory.BertiniC
theorem _root_.solution {k A κ : Type} [Field k] [CharZero k] [CommRing A] [Algebra k A]
    [Field κ] [Algebra k κ] [Algebra A κ] [IsScalarTower k A κ] [Algebra.EssFiniteType k κ]
    (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A)
    (hω : ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l)
    {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι)
    (hi₀ : i₀ ∈ J) (t : Fin M × ι → κ) (ht : AlgebraicIndependent k t) (c : Fin M → κ)
    (r1 : ∀ i ∈ J, ∑ p, t (i, p) * algebraMap A κ (f p) = 0)
    (r2 : ∀ l, ∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p)) = 0)
    (r3 : c i₀ - 1 = 0) (s : κ) (r4s : s * algebraMap A κ (f p₀) - 1 = 0) : False := by
  have r4 : algebraMap A κ (f p₀) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_sub, neg_eq_zero] at r4s
    exact one_ne_zero r4s
  have hlin := GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent k κ t ht
  set m : Fin n → KaehlerDifferential k κ := fun l => KaehlerDifferential.map k k A κ (ω l) with hm
  have hdψ : ∀ a : A, D k κ (algebraMap A κ a) = ∑ l, algebraMap A κ (δ l a) • m l := by
    intro a
    rw [← KaehlerDifferential.map_D k k A κ, hω a, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.map_smul, algebraMap_smul]
  have e1 : ∀ i ∈ J, ∑ p, algebraMap A κ (f p) • D k κ (t (i, p)) =
      - ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) := by
    intro i hi
    have h := congrArg (D k κ) (r1 i hi)
    rw [map_sum, map_zero] at h
    simp only [Derivation.leibniz, Finset.sum_add_distrib] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have e2 : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) = 0 := by
    have : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) =
        ∑ l, (∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p))) • m l := by
      simp only [hdψ, Finset.smul_sum, Finset.sum_smul, Finset.mul_sum, smul_smul, mul_assoc]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [this]
    simp [r2]
  have key : ∑ x ∈ J ×ˢ (Finset.univ : Finset ι), (c x.1 * algebraMap A κ (f x.2)) • D k κ (t x) = 0 := by
    rw [Finset.sum_product]
    simp only [mul_smul, ← Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun i hi => by rw [e1 i hi]), ]
    simp only [smul_neg, Finset.sum_neg_distrib, e2, neg_zero]
  have := linearIndependent_iff'.1 hlin _ _ key (i₀, p₀) (by simp [hi₀])
  rw [sub_eq_zero.1 r3, one_mul] at this
  exact r4 this
end GlobalTheory.BertiniC
