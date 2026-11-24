-- Prove2me | solution 1 for GlobalTheory.ThetaSplit.exists_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:32:58.46504+00:00
-- url     : https://prove2.me/submissions/f49e9bcf-973e-4526-accd-ddf36dd61647

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit
namespace GlobalTheory.ThetaSplit
theorem _root_.solution {C U : Type} [CommGroup C] [CommGroup U]
    (hU : ∀ n : ℕ, 0 < n → ∀ y : U, ∃ x : U, x ^ n = y) (a : C → C → U) (hs : ∀ x y, a x y = a y x)
    (hc : ∀ x y z, a x y * a (x * y) z = a y z * a x (y * z)) :
    ∃ b : C → U, ∀ x y, b (x * y) * a x y = b x * b y := by
  have h1 : ∀ x, a 1 x = a 1 1 := fun x => by
    have := hc 1 1 x
    simp only [_root_.one_mul] at this
    exact (mul_right_cancel this).symm
  letI : CommGroup (CocycleExt a) :=
    { mul := fun p q => ⟨p.u * q.u * a p.c q.c, p.c * q.c⟩
      one := ⟨(a 1 1)⁻¹, 1⟩
      inv := fun p => ⟨p.u⁻¹ * (a p.c⁻¹ p.c)⁻¹ * (a 1 1)⁻¹, p.c⁻¹⟩
      mul_assoc := fun p q r => CocycleExt.ext (by
        show p.u * q.u * a p.c q.c * r.u * a (p.c * q.c) r.c = p.u * (q.u * r.u * a q.c r.c) * a p.c (q.c * r.c)
        have e := congrArg Additive.ofMul (hc p.c q.c r.c)
        apply Additive.ofMul.injective
        simp only [ofMul_mul] at e ⊢
        linear_combination (norm := abel) e) (_root_.mul_assoc _ _ _)
      one_mul := fun p => CocycleExt.ext (by
        show (a 1 1)⁻¹ * p.u * a 1 p.c = p.u
        rw [h1 p.c, mul_comm (a 1 1)⁻¹, inv_mul_cancel_right]) (_root_.one_mul _)
      mul_one := fun p => CocycleExt.ext (by
        show p.u * (a 1 1)⁻¹ * a p.c 1 = p.u
        rw [hs p.c, h1 p.c, inv_mul_cancel_right]) (_root_.mul_one _)
      inv_mul_cancel := fun p => CocycleExt.ext (by
        show p.u⁻¹ * (a p.c⁻¹ p.c)⁻¹ * (a 1 1)⁻¹ * p.u * a p.c⁻¹ p.c = (a 1 1)⁻¹
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (inv_mul_cancel _)
      mul_comm := fun p q => CocycleExt.ext (by
        show p.u * q.u * a p.c q.c = q.u * p.u * a q.c p.c
        rw [hs, mul_comm p.u]) (mul_comm _ _) }
  let j : U →* CocycleExt a := MonoidHom.mk' (fun u => ⟨u * (a 1 1)⁻¹, 1⟩) fun u v => CocycleExt.ext (by
    show u * v * (a 1 1)⁻¹ = u * (a 1 1)⁻¹ * (v * (a 1 1)⁻¹) * a 1 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel) (_root_.mul_one _).symm
  have hj : Function.Injective j := fun u v h => mul_right_cancel (congrArg CocycleExt.u h)
  letI : DivisibleBy (Additive U) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn y => by
    obtain ⟨x, hx⟩ := hU n (Nat.pos_of_ne_zero hn) y.toMul
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  letI : DivisibleBy (Additive U) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive U)).extension_property_addMonoidHom
    (MonoidHom.toAdditive j) hj (AddMonoidHom.id _)
  let σ : CocycleExt a →* U := AddMonoidHom.toMultiplicative ρ
  have hσ : ∀ u, σ (j u) = u := fun u => DFunLike.congr_fun hρ (Additive.ofMul u)
  refine ⟨fun x => σ ⟨1, x⟩, fun x y => ?_⟩
  rw [← map_mul σ, ← hσ (a x y), ← map_mul σ]
  refine congrArg σ (CocycleExt.ext ?_ (_root_.mul_one _))
  show 1 * (a x y * (a 1 1)⁻¹) * a (x * y) 1 = 1 * 1 * a x y
  rw [hs (x * y), h1 (x * y)]
  simp
end GlobalTheory.ThetaSplit
