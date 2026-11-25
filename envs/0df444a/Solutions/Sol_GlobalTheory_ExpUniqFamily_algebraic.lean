-- Prove2me | solution 1 for GlobalTheory.ExpUniqFamily.algebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:38:20.265417+00:00
-- url     : https://prove2.me/submissions/a1e565bc-a6d2-479b-8210-4368acc1d188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Theorems.Thm_GlobalTheory_ExpUniqFamily_linear_eq_zero_of_discrete
import Theorems.Thm_GlobalTheory_ExpUniqFamily_eq_iff_sub
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.ExpUniqFamily
namespace GlobalTheory.ExpUniqFamily
theorem _root_.solution {O Q L L' : Type} [CommRing O] [Group Q] [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {g : ℕ} (χ : Fin g → O → ℂ) (P : L →+ (Fin g → ℂ)) (P' : L' →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x i, P (a • x) i = χ i a * P x i) (hP' : ∀ (a : O) x i, P' (a • x) i = χ i a * P' x i)
    (iP : Function.Injective P) (iP' : Function.Injective P')
    (dP : DiscreteTopology P.range) (dP' : DiscreteTopology P'.range)
    (e e' : (Fin g → ℂ) → Q) (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (act : O → Q → Q) (hl : ∀ a z, e (fun k => χ k a * z k) = act a (e z))
    (hl' : ∀ a z, e' (fun k => χ k a * z k) = act a (e' z))
    (f f' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, e' (f z) = e z) (hf' : ∀ z, e (f' z) = e' z) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : L ≃ₗ[O] L'), (∀ z, e' (h z) = e z) ∧
      (∀ a, P' (gam a) = h (P a)) ∧
      ∀ (k : ℕ) a b, 0 < k → e ((k : ℂ)⁻¹ • P a) = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  have h1 : ∀ z, f' (f z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P.range (f' ∘ₗ f - LinearMap.id) (fun z => (hk _).1 <|
      (eq_iff_sub e ha _ _).1 (by simp [hf, hf'])) z
  have h2 : ∀ z, f (f' z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ f' - LinearMap.id) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp [hf, hf'])) z
  let d : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => LinearMap.pi fun k => χ k a • LinearMap.proj k
  have hd : ∀ a z, d a z = fun k => χ k a * z k := fun a z => rfl
  have h3 : ∀ a z, f (d a z) = d a (f z) := fun a z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ d a - d a ∘ₗ f) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp only [LinearMap.comp_apply, hf, hd, hl, hl'])) z
  have m1 : ∀ a, ∃ b, P' b = f (P a) := fun a => (hk' _).1 (by rw [hf]; exact (hk _).2 ⟨a, rfl⟩)
  have m2 : ∀ b, ∃ a, P a = f' (P' b) := fun b => (hk _).1 (by rw [hf']; exact (hk' _).2 ⟨b, rfl⟩)
  choose ga hga using m1
  choose de hde using m2
  let gam : L ≃ₗ[O] L' :=
    { toFun := ga
      invFun := de
      map_add' := fun a b => iP' (by simp [hga])
      map_smul' := fun c a => iP' (by
        have e1 : P (c • a) = d c (P a) := funext fun i => hP c a i
        have e2 : P' (c • ga a) = d c (P' (ga a)) := funext fun i => hP' c _ i
        rw [RingHom.id_apply, hga, e1, e2, hga, h3])
      left_inv := fun a => iP (by rw [hde, hga, h1])
      right_inv := fun b => iP' (by rw [hga, hde, h2]) }
  refine ⟨LinearEquiv.ofLinear f f' (LinearMap.ext h2) (LinearMap.ext h1), gam, hf, hga, ?_⟩
  intro k a b hk0 hab
  have hk1 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  rw [← hf, map_smul, ← hga, eq_iff_sub e' ha', hk'] at hab
  obtain ⟨c, hc⟩ := hab
  refine ⟨c, iP' ?_⟩
  show P' (ga a) = _
  rw [map_add, map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hk1, one_smul]
  abel
end GlobalTheory.ExpUniqFamily
