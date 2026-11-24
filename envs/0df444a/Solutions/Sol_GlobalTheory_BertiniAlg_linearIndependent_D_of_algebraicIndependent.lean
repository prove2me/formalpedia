-- Prove2me | solution 1 for GlobalTheory.BertiniAlg.linearIndependent_D_of_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:24.951607+00:00
-- url     : https://prove2.me/submissions/94f3f20b-50a2-42c9-9ca8-f193e0dfed1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentKaehlerDOfAlgebraicIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped TensorProduct
open KaehlerDifferential
open GlobalTheory GlobalTheory.BertiniAlg
namespace GlobalTheory.BertiniAlg
theorem _root_.solution (k κ : Type) [Field k] [CharZero k] [Field κ]
    [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ)
    (ht : AlgebraicIndependent k t) :
    LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  let P := MvPolynomial σ k
  let φ : P →ₐ[k] κ := MvPolynomial.aeval t
  have hφ : Function.Injective φ := ht
  algebraize [φ.toRingHom]
  have : IsScalarTower k P κ := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let K := FractionRing P
  have hinj : Function.Injective (algebraMap P κ) := hφ
  let : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower P K κ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : IsScalarTower k K κ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k P K, ← IsScalarTower.algebraMap_apply P K κ,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.EssFiniteType K κ := .of_comp k K κ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.FormallySmooth K κ := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale P K := .of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallySmooth P κ := .comp P K κ
  have hH : Subsingleton (Algebra.H1Cotangent P κ) := Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinjm : Function.Injective (mapBaseChange k P κ) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k P κ x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  let b := (mvPolynomialBasis k σ).baseChange κ
  have h := b.linearIndependent.map' (mapBaseChange k P κ) (LinearMap.ker_eq_bot.2 hinjm)
  have hX (s : σ) : algebraMap P κ (MvPolynomial.X s) = t s := MvPolynomial.aeval_X t s
  have e : (fun s => KaehlerDifferential.D k κ (t s)) = mapBaseChange k P κ ∘ b := by
    funext s
    simp only [Function.comp_apply, b, Module.Basis.baseChange_apply, mvPolynomialBasis_apply]
    erw [mapBaseChange_tmul, one_smul, map_D, hX]
  rw [e]
  exact h
end GlobalTheory.BertiniAlg
