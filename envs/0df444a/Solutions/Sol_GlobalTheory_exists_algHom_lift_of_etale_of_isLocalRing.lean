-- Prove2me | solution 1 for GlobalTheory.exists_algHom_lift_of_etale_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:32:27.887956+00:00
-- url     : https://prove2.me/submissions/9d3df307-f2e0-4db3-a501-32239c7b233b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_isUnit_of_isUnit_mk_of_le_jacobson

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution {R A S : Type*} [CommRing R] [CommRing A]
    [CommRing S] [Algebra R A] [Algebra R S] [Algebra.Etale R A] [IsLocalRing S] (J : Ideal S)
    [HenselianRing S J] (φ : A →ₐ[R] S ⧸ J) :
    ∃ ψ : A →ₐ[R] S, ∀ a, Ideal.Quotient.mk J (ψ a) = φ a := by
  have hJ : J ≤ (⊥ : Ideal S).jacobson := HenselianRing.jac
  have hJtop : J ≠ ⊤ := by
    rintro rfl
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hJ
    exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 hJ)
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let Q : Ideal A := (maximalIdeal (S ⧸ J)).comap φ
  obtain ⟨f, hfQ, ⟨⟨P⟩⟩⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have hf : IsUnit (φ f) := by
    simpa [Q] using hfQ
  let φ' : Localization.Away f →ₐ[R] S ⧸ J := IsLocalization.Away.liftAlgHom f hf
  have hφ' : ∀ a, φ' (algebraMap _ _ a) = φ a := fun a ↦ by simp [φ']
  obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (φ' P.x)
  have hm : P.HasMap (Ideal.Quotient.mkₐ R J x₀) := by
    have := P.hasMap.map φ'
    rwa [← hx₀] at this
  obtain ⟨x, hx, hxx⟩ := HenselianRing.is_henselian (I := J) (P.f.map (algebraMap R S))
    (P.monic_f.map _) x₀ (by
      rw [eval_map_algebraMap, ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R,
        ← aeval_algHom_apply]
      exact hm.1) (by
      rw [derivative_map, eval_map_algebraMap, ← Ideal.Quotient.mkₐ_eq_mk R,
        ← aeval_algHom_apply]
      exact hm.isUnit_derivative_f)
  have hxx' : Ideal.Quotient.mkₐ R J x = Ideal.Quotient.mkₐ R J x₀ := Ideal.Quotient.eq.2 hxx
  have hmx : P.HasMap x := by
    refine ⟨by simpa [eval_map_algebraMap] using hx.eq_zero, ?_⟩
    apply isUnit_of_isUnit_mk_of_le_jacobson hJ
    rw [← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply, hxx']
    exact hm.2
  let ψ' : Localization.Away f →ₐ[R] S := (P.lift x hmx).comp P.equivRing.toAlgHom
  have hψ' : (Ideal.Quotient.mkₐ R J).comp ψ' = φ' := by
    apply P.hom_ext
    change Ideal.Quotient.mkₐ R J (P.lift x hmx (P.equivRing P.x)) = _
    rw [StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X, hxx']
    exact hx₀
  refine ⟨ψ'.comp (IsScalarTower.toAlgHom R A _), fun a ↦ ?_⟩
  rw [← hφ', ← hψ']
  rfl
end GlobalTheory
