-- Prove2me | solution 1 for GlobalTheory.CuspGL.TeichEmb.exists_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:14.592243+00:00
-- url     : https://prove2.me/submissions/4c583ebe-deb4-414d-8263-06443804fb2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL.TeichEmb
open Polynomial IntermediateField in
private theorem exists_pow_eq_one_algebraicClosure_of_finite (F : Type) [Field F] [Finite F]
    (x : AlgebraicClosure F) (hx : x ≠ 0) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  have hfin : FiniteDimensional F F⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Finite F⟮x⟯ := Module.finite_of_finite F
  have hne : (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : F⟮x⟯) ≠ 0 := by
    intro h; exact hx (congrArg Subtype.val h)
  obtain ⟨n, hn, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (Units.mk0 _ hne))
  refine ⟨n, hn, ?_⟩
  have := congrArg (fun u : (F⟮x⟯)ˣ => ((u : F⟮x⟯) : AlgebraicClosure F)) hpow
  simpa using this
end GlobalTheory.CuspGL.TeichEmb
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.TeichEmb
open Polynomial IntermediateField
namespace GlobalTheory.CuspGL.TeichEmb
namespace _root_.GlobalTheory.CuspGL.TeichEmb
theorem _root_.solution :
    ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ,
      ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  intro F _ _
  set p := ringChar F
  have : Fact p.Prime :=
    ⟨(CharP.char_is_prime_or_zero F p).resolve_right (CharP.char_ne_zero_of_finite F p)⟩
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have : PerfectRing (AlgebraicClosure F) p := inferInstance
  let W := WittVector p (AlgebraicClosure F)
  have : IsDomain W := inferInstance
  letI : Algebra (ZMod p) (AlgebraicClosure F) := ZMod.algebra _ p
  have hW : CharZero W := by
    let f : ℤ_[p] →+* W := (WittVector.map (algebraMap (ZMod p) (AlgebraicClosure F))).comp
      (WittVector.equiv p).symm.toRingHom
    have hf : Function.Injective f :=
      (WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure F)).injective).comp
        (WittVector.equiv p).symm.injective
    exact (RingHom.charZero_iff hf).mp inferInstance
  let Ω := AlgebraicClosure (FractionRing W)
  have : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  have : CharZero Ω := inferInstance
  let g : W →+* Ω := (algebraMap (FractionRing W) Ω).comp (algebraMap W (FractionRing W))
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  let ι : AlgebraicClosure F →* Ω := (g : W →* Ω).comp (WittVector.teichmuller p)
  have hι : Function.Injective ι := by
    intro x y h
    have h1 : WittVector.teichmuller p x = WittVector.teichmuller p y := hg h
    simpa using congrArg (fun w : W => w.coeff 0) h1
  have hmem : ∀ x, ι x ∈ algebraicClosure ℚ Ω := by
    intro x
    rw [mem_algebraicClosure_iff]
    by_cases hx : x = 0
    · subst hx
      have : ι 0 = 0 := by
        show g (WittVector.teichmuller p 0) = 0
        rw [WittVector.teichmuller_zero, map_zero]
      rw [this]; exact isAlgebraic_zero
    · obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_algebraicClosure_of_finite F x hx
      refine (IsIntegral.of_pow hn ?_).isAlgebraic
      rw [← map_pow, hpow, map_one]; exact isIntegral_one
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ Ω) := algebraicClosure.isAlgebraic ℚ Ω
  let φ : algebraicClosure ℚ Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨{ toFun := fun x => φ ⟨ι x, hmem x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact (congrArg φ (Subtype.ext (map_one ι) : (⟨ι 1, hmem 1⟩ : algebraicClosure ℚ Ω) = 1)).trans
      (map_one φ)
  · intro x y
    rw [← map_mul]; exact congrArg φ (Subtype.ext (map_mul ι x y))
  · intro x y _ _ h
    exact hι (congrArg Subtype.val (φ.injective h))
end _root_.GlobalTheory.CuspGL.TeichEmb
end GlobalTheory.CuspGL.TeichEmb
