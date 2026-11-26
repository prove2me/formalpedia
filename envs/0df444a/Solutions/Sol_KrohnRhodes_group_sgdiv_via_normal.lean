-- Prove2me | solution 1 for KrohnRhodes.group_sgdiv_via_normal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:56:56.591544+00:00
-- url     : https://prove2.me/submissions/73f37e39-451c-4c9d-8d7b-de36c61a8355

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Mathlib
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.RegularWreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_injective
public import Theorems.Thm_KrohnRhodes_regularWreath_to_monoidWreath_injective


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
open KrohnRhodes
universe u
variable {G : Type u} [Group G]
namespace KrohnRhodes
theorem _root_.solution {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] :
    SgDiv G (WreathProduct N (G ⧸ N) (G ⧸ N)) := by
  classical
  -- Composition of Krasner embedding and the bridge to monoid wreath.
  set ψ : G →* WreathProduct N (G ⧸ N) (G ⧸ N) :=
    (regularWreath_to_monoidWreath N (G ⧸ N)).comp (krasnerKaloujnine_hom N) with hψdef
  have hbridge_inj : Function.Injective (regularWreath_to_monoidWreath N (G ⧸ N)) :=
    regularWreath_to_monoidWreath_injective N (G ⧸ N)
  have hkras_inj : Function.Injective (krasnerKaloujnine_hom N) :=
    krasnerKaloujnine_injective N
  have hψinj : Function.Injective ψ := fun a b hab => hkras_inj (hbridge_inj hab)
  -- The image of G in WreathProduct as a Subsemigroup.
  refine ⟨{
    carrier := Set.range ψ
    mul_mem' := by
      rintro a b ⟨ga, rfl⟩ ⟨gb, rfl⟩
      exact ⟨ga * gb, ψ.map_mul ga gb⟩ }, ?_, ?_⟩
  · -- Inverse map: range → G via choice (well-defined by injectivity).
    refine
    { toFun := fun u => Function.invFun ψ (u : WreathProduct N (G ⧸ N) (G ⧸ N))
      map_mul' := ?_ }
    intro a b
    obtain ⟨ga, ha⟩ := a.2
    obtain ⟨gb, hb⟩ := b.2
    change Function.invFun ψ ((a * b : { x // x ∈ Set.range ψ }) : WreathProduct N (G ⧸ N) (G ⧸ N))
        = Function.invFun ψ (a : WreathProduct N (G ⧸ N) (G ⧸ N))
          * Function.invFun ψ (b : WreathProduct N (G ⧸ N) (G ⧸ N))
    have hcoe : ((a * b : { x // x ∈ Set.range ψ }) : WreathProduct N (G ⧸ N) (G ⧸ N))
        = ψ (ga * gb) := by
      change (a : WreathProduct N (G ⧸ N) (G ⧸ N)) * (b : WreathProduct N (G ⧸ N) (G ⧸ N))
        = ψ (ga * gb)
      rw [ψ.map_mul, ha, hb]
    rw [hcoe]
    rw [Function.leftInverse_invFun hψinj (ga * gb)]
    rw [← ha, Function.leftInverse_invFun hψinj ga]
    rw [← hb, Function.leftInverse_invFun hψinj gb]
  · -- Surjectivity.
    intro g
    refine ⟨⟨ψ g, g, rfl⟩, ?_⟩
    change Function.invFun ψ (ψ g) = g
    exact Function.leftInverse_invFun hψinj g
end KrohnRhodes
