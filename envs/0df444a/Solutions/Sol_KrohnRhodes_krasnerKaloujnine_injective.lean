-- Prove2me | solution 1 for KrohnRhodes.krasnerKaloujnine_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:56:10.311619+00:00
-- url     : https://prove2.me/submissions/92ae716e-6097-46cb-9c18-b9dd991a7e5d

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Mathlib
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.RegularWreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
attribute [local simp] KrohnRhodes.krasnerKaloujnine_hom_left

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
open KrohnRhodes
universe u
variable {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]
namespace KrohnRhodes
theorem _root_.solution :
    Function.Injective (krasnerKaloujnine_hom N) := by
  intro g₁ g₂ h
  -- From φ(g₁) = φ(g₂), read off π(g₁) = π(g₂) and the left components agree.
  have hright : QuotientGroup.mk' N g₁ = QuotientGroup.mk' N g₂ := by
    have := congrArg RegularWreathProduct.right h
    simpa [krasnerKaloujnine_hom, krasnerKaloujnineFun] using this
  have hleft : ∀ q : G ⧸ N,
      (krasnerKaloujnine_hom N g₁).left q = (krasnerKaloujnine_hom N g₂).left q := by
    intro q
    have := congrArg RegularWreathProduct.left h
    exact congrFun this q
  -- Take q = 1.
  have h1 : (krasnerKaloujnine_hom N g₁).left 1 = (krasnerKaloujnine_hom N g₂).left 1 := hleft 1
  have hval : ((krasnerKaloujnine_hom N g₁).left 1 : G) =
      ((krasnerKaloujnine_hom N g₂).left 1 : G) := congrArg Subtype.val h1
  rw [krasnerKaloujnine_hom_left, krasnerKaloujnine_hom_left] at hval
  -- The (s(1))⁻¹ on the left and section_ N (mk'⁻¹ * 1) on the right cancel since π(g₁) = π(g₂).
  rw [hright] at hval
  -- s(1)⁻¹ * g₁ * s((mk' g₂)⁻¹) = s(1)⁻¹ * g₂ * s((mk' g₂)⁻¹)
  have hcancel : g₁ = g₂ := by
    have : (section_ N 1)⁻¹ * g₁ * section_ N ((QuotientGroup.mk' N g₂)⁻¹ * 1) =
        (section_ N 1)⁻¹ * g₂ * section_ N ((QuotientGroup.mk' N g₂)⁻¹ * 1) := hval
    -- Cancel: multiply both sides by section_ N 1 on the left and
    -- section_ N (...)⁻¹ on the right.
    set a : G := section_ N 1
    set b : G := section_ N ((QuotientGroup.mk' N g₂)⁻¹ * 1)
    have : a⁻¹ * g₁ * b = a⁻¹ * g₂ * b := this
    have : g₁ = g₂ := by
      have h1 : a * (a⁻¹ * g₁ * b) * b⁻¹ = g₁ := by group
      have h2 : a * (a⁻¹ * g₂ * b) * b⁻¹ = g₂ := by group
      calc g₁ = a * (a⁻¹ * g₁ * b) * b⁻¹ := h1.symm
        _ = a * (a⁻¹ * g₂ * b) * b⁻¹ := by rw [this]
        _ = g₂ := h2
    exact this
  exact hcancel
end KrohnRhodes
