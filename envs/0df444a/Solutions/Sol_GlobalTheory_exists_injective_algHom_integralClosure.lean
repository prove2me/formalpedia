-- Prove2me | solution 1 for GlobalTheory.exists_injective_algHom_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:20.290879+00:00
-- url     : https://prove2.me/submissions/631d11fe-bd4a-464c-928e-ba9cce3ce03f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {p K}
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
namespace GlobalTheory
theorem _root_.solution (B : Type*) [CommRing B] [IsDomain B]
    [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] (hp : (p : B) ≠ 0) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (g : B →ₐ[ℤ_[p]] integralClosure ℤ_[p] K), Function.Injective g := by
  classical
  have hinj : Function.Injective (algebraMap ℤ_[p] B) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0
      (PadicInt.irreducible_p (p := p))
    rw [map_mul, map_pow, map_natCast] at ha
    exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero n hp) ha
  haveI : FaithfulSMul ℤ_[p] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : FaithfulSMul ℤ_[p] (PadicAlgCl p) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective _ _))
  let φ : B →ₐ[ℤ_[p]] PadicAlgCl p := IsAlgClosed.lift
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have : (RingHom.ker φ).comap (algebraMap ℤ_[p] B) = ⊥ := by
      refine eq_bot_iff.mpr fun a ha => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, φ.commutes] at ha
      exact (FaithfulSMul.algebraMap_injective ℤ_[p] (PadicAlgCl p)) (by simpa using ha)
    have h := Ideal.eq_bot_of_comap_eq_bot this
    exact (Ideal.mem_bot.mp (h ▸ (RingHom.mem_ker.mpr hb : b ∈ RingHom.ker φ)))
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := B)
  let K := IntermediateField.adjoin ℚ_[p] ((s.image φ : Finset _) : Set (PadicAlgCl p))
  haveI : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ b, φ b ∈ K := by
    intro b
    have hb : b ∈ Submodule.span ℤ_[p] (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact K.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact K.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, ← algebraMap_smul ℚ_[p]]
      exact K.smul_mem hx
  let ψ : B →ₐ[ℤ_[p]] K :=
    { toFun := fun b => ⟨φ b, hmem b⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun a b => Subtype.ext (map_add φ a b)
      commutes' := fun a => Subtype.ext (φ.commutes a) }
  refine ⟨K, inferInstance, ψ.codRestrict (integralClosure ℤ_[p] K) fun b =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) b).map ψ, fun a b h => hφ ?_⟩
  exact congrArg (fun z : integralClosure ℤ_[p] K => ((z : K) : PadicAlgCl p)) h
end GlobalTheory
