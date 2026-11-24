-- Prove2me | solution 1 for GlobalTheory.exists_lift_to_complete_dvr_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:46.982096+00:00
-- url     : https://prove2.me/submissions/0ae205fa-1ccf-46db-9556-458ae49b0e8d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftToCompleteDvrOfFinite
import Theorems.Thm_Formalism_L2_G_IntCl_complete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  intro A R _ _ _ hinj hfin V _ _ _ _ hC h
  classical
  let p : Ideal A := RingHom.ker h
  haveI : p.IsPrime := RingHom.ker_isPrime h
  haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal R) (by
    rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  let K := FractionRing V
  let Ω := AlgebraicClosure K
  letI : Algebra (A ⧸ p) (R ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hQp.symm)
  have hcomp : (algebraMap (A ⧸ p) (R ⧸ Q)).comp (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk Q).comp (algebraMap A R) := rfl
  haveI : Algebra.IsIntegral (A ⧸ p) (R ⧸ Q) := by
    constructor
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact IsIntegral.map_of_comp_eq (Ideal.Quotient.mk p) (Ideal.Quotient.mk Q) hcomp
      (Algebra.IsIntegral.isIntegral r)
  have hinj0 : Function.Injective (algebraMap (A ⧸ p) (R ⧸ Q)) :=
    Ideal.quotientMap_injective' (le_of_eq hQp)
  let g0 : (A ⧸ p) →+* Ω := (algebraMap K Ω).comp ((algebraMap V K).comp (RingHom.kerLift h))
  have hg0 : Function.Injective g0 :=
    (algebraMap K Ω).injective.comp ((IsFractionRing.injective V K).comp (RingHom.kerLift_injective h))
  letI : Algebra (A ⧸ p) Ω := g0.toAlgebra
  haveI : Module.IsTorsionFree (A ⧸ p) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinj0
  haveI : Module.IsTorsionFree (A ⧸ p) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hg0
  haveI : Algebra.IsAlgebraic (A ⧸ p) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (R ⧸ Q) →ₐ[A ⧸ p] Ω := IsAlgClosed.lift
  let ρ1 : R →+* Ω := σ.toRingHom.comp (Ideal.Quotient.mk Q)
  have hρ1 : ∀ a : A, ρ1 (algebraMap A R a) = algebraMap K Ω (algebraMap V K (h a)) := by
    intro a
    show σ (Ideal.Quotient.mk Q (algebraMap A R a)) = _
    rw [← RingHom.comp_apply, ← hcomp, RingHom.comp_apply, σ.commutes]
    rfl
  obtain ⟨s, hs⟩ := hfin.fg_top
  let M : IntermediateField K Ω := IntermediateField.adjoin K (ρ1 '' (s : Set R))
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ r : R, ρ1 r ∈ M := by
    intro r
    have hr : r ∈ Submodule.span A (s : Set R) := hs ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact M.add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def, map_mul, hρ1]; exact M.mul_mem (M.algebraMap_mem _) hx
  let ψ : R →+* M := ρ1.codRestrict M hmem
  have hψ : (algebraMap V M).comp h = ψ.comp (algebraMap A R) := by
    ext a
    simp only [RingHom.comp_apply]
    show (algebraMap V M (h a) : Ω) = ρ1 (algebraMap A R a)
    rw [hρ1]
    rfl
  have hint : ∀ r : R, ψ r ∈ integralClosure V M := fun r =>
    IsIntegral.map_of_comp_eq h ψ hψ (Algebra.IsIntegral.isIntegral r)
  let ρ : R →+* integralClosure V M := ψ.codRestrict (integralClosure V M) hint
  haveI hdvr := Formalism.L2.G.IntCl.isDVR V K M hC
  have hfinj := Formalism.L2.G.IntCl.alg_injective V K M
  haveI : FaithfulSMul V (integralClosure V M) := (faithfulSMul_iff_algebraMap_injective _ _).2 hfinj
  refine ⟨integralClosure V M, inferInstance, inferInstance, hdvr,
    (RingHom.charZero_iff hfinj).1 inferInstance, algebraMap V (integralClosure V M), ρ,
    Formalism.L2.G.IntCl.complete V K M hC, hfinj, Algebra.IsIntegral.isLocalHom _ _, ?_⟩
  ext a
  show ρ1 (algebraMap A R a) = (algebraMap V M (h a) : Ω)
  rw [hρ1]
  rfl
end GlobalTheory
