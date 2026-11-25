-- Prove2me | solution 1 for GlobalTheory.TorusRoot.exists_root_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:11.759258+00:00
-- url     : https://prove2.me/submissions/caaefd01-d863-47ac-8aae-2a3bc42902b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPthRootTorusPointNilpotentAugmentedExt
import Theorems.Thm_GlobalTheory_TorusRoot_exists_root_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TorusRoot
namespace GlobalTheory.TorusRoot
theorem _root_.solution :
    ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ χ : Multiplicative X →* Aˣ,
    (∀ x, π (χ x).val = 1) →
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (χ' : Multiplicative X →* A'ˣ), Function.Injective f ∧ π'.comp f = π ∧
      IsNilpotent (RingHom.ker π') ∧ (∀ x, π' (χ' x).val = 1) ∧
      χ' ^ p = (Units.map (f : A →* A')).comp χ := by
  intro Ω _ p _ _ X _ _ _ A _ _ π hπ χ hχ
  let b := Module.finBasis ℤ X
  obtain ⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩ :=
    exists_root_fin Ω p _ A π hπ (fun i => χ (Multiplicative.ofAdd (b i))) (fun i => hχ _)
  let l : X →ₗ[ℤ] Additive Bˣ := b.constr ℤ (fun i => Additive.ofMul (s i))
  have hl : ∀ i, l (b i) = Additive.ofMul (s i) := fun i => b.constr_basis ℤ _ i
  let χ' : Multiplicative X →* Bˣ := AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom
  have hχ' : ∀ i, χ' (Multiplicative.ofAdd (b i)) = s i := fun i => by
    change Additive.toMul (l (b i)) = _
    rw [hl]; rfl
  have key : ∀ {G : Type} [CommGroup G] (φ ψ : Multiplicative X →* G),
      (∀ i, φ (Multiplicative.ofAdd (b i)) = ψ (Multiplicative.ofAdd (b i))) → φ = ψ := by
    intro G _ φ ψ h
    have : (MonoidHom.toAdditiveRight φ).toIntLinearMap =
        (MonoidHom.toAdditiveRight ψ).toIntLinearMap :=
      b.ext fun i => congrArg Additive.ofMul (h i)
    refine MonoidHom.ext fun x => ?_
    exact congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)
  refine ⟨B, inferInstance, inferInstance, f, ρ, χ', hf, hρ, hρn, ?_, ?_⟩
  · have : (Units.map (ρ : B →* Ω)).comp χ' = 1 := key _ _ fun i => by
      ext
      simpa [hχ'] using hs1 i
    intro x
    exact congrArg Units.val (DFunLike.congr_fun this x)
  · exact key _ _ fun i => by
      rw [MonoidHom.pow_apply, hχ', hs]; rfl
end GlobalTheory.TorusRoot
