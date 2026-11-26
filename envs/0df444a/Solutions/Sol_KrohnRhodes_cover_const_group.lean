-- Prove2me | solution 1 for KrohnRhodes.cover_const_group
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:59.974209+00:00
-- url     : https://prove2.me/submissions/6a12cfaa-e9e6-4cc2-b0c5-85469ea2edf6

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {G Q : Type} [Group G] (act : G →* Function.End Q) (x : Q) :
    ∃ w : WreathProduct ↥(resetSubmonoid Q) G G,
      Covers (groupProj act) w (constEnd x) := by
  -- The DKS family-2 witness: decoration `f_x(m) := constEnd (act m⁻¹ x)` — a constant of
  -- `End Q`, hence a generator of the reset submonoid — and trivial base.
  refine ⟨⟨fun m => ⟨constEnd (act m⁻¹ x), Submonoid.subset_closure ⟨act m⁻¹ x, rfl⟩⟩, 1⟩, ?_⟩
  intro p y
  -- Up to definitional unfolding the cover equation reads `act (1 * y) (act y⁻¹ x) = x`;
  -- the group inverse cancels through multiplicativity:
  have key : act ((1 : G) * y) (act y⁻¹ x) = x := by
    calc act ((1 : G) * y) (act y⁻¹ x)
        = act (y * y⁻¹) x := by rw [one_mul, map_mul]; rfl
      _ = x := by rw [mul_inv_cancel, map_one]; rfl
  exact key
end KrohnRhodes
