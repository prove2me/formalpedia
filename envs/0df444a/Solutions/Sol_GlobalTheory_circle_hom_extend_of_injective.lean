-- Prove2me | solution 1 for GlobalTheory.circle_hom_extend_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:51.821978+00:00
-- url     : https://prove2.me/submissions/0b298bab-476f-428b-b06b-9a7bc9060d3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsContinuousCircleCharExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A B : Type} [CommGroup A] [CommGroup B] (i : A →* B)
    (hi : Function.Injective i) (ψ : A →* Circle) : ∃ χ : B →* Circle, ∀ a, χ (i a) = ψ a := by
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective (Additive.toMul u)
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    apply Additive.toMul.injective
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [toMul_nsmul, toMul_ofMul]
    rw [← ht, ← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive i) hi (MonoidHom.toAdditive ψ)
  refine ⟨MonoidHom.toAdditive.symm ρ, fun a => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hρ (Additive.ofMul a))
end GlobalTheory
