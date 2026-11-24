-- Prove2me | solution 1 for GlobalTheory.residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:26.718099+00:00
-- url     : https://prove2.me/submissions/71cf643f-37d1-495a-811b-0bdad0db6790

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsOpenImmersionIsStandardSmoothOfRelativeD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K B : Type} [Field K]
    [CommRing B] [Algebra K B] (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K B]
    (p : Ideal B) [p.IsPrime] (hp : ∀ q : Ideal B, q.IsPrime → q ≤ p → q = p) :
    Algebra.EssFiniteType K p.ResidueField ∧ Algebra.trdeg K p.ResidueField = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K B
  letI : Algebra (MvPolynomial (Fin d) K) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) B := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Algebra.FiniteType K B := .trans (S := MvPolynomial (Fin d) K) inferInstance inferInstance
  refine ⟨.comp K B _, ?_⟩
  obtain ⟨q, hqp, hq, hqo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal (MvPolynomial (Fin d) K))) (q := p.under (MvPolynomial (Fin d) K)) p bot_le
  obtain rfl := hp q hq hqp
  haveI : FaithfulSMul (MvPolynomial (Fin d) K) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    rw [IsScalarTower.algebraMap_apply _ B, Ideal.algebraMap_residueField_eq_zero] at ha
    have : a ∈ q.under (MvPolynomial (Fin d) K) := ha
    rwa [← hqo.over] at this
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin d) K) q.ResidueField := by
    let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal (MvPolynomial (Fin d) K)) q
    have : Module.Finite (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField q.ResidueField :=
      inferInstance
    have : Algebra.IsAlgebraic (MvPolynomial (Fin d) K)
        (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (Fin d) K))
    exact Algebra.IsAlgebraic.trans _ (⊥ : Ideal (MvPolynomial (Fin d) K)).ResidueField _
  rw [← trdeg_add_eq K (MvPolynomial (Fin d) K), MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero]
  simp
end GlobalTheory
