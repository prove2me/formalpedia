-- Prove2me | solution 1 for KrohnRhodes.cover_act_group
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:46.156364+00:00
-- url     : https://prove2.me/submissions/557f2eb1-c667-4689-981b-f8568a8ac53b

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
public import Theorems.Thm_KrohnRhodes_constEnd_mul
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
attribute [local simp] KrohnRhodes.constEnd_mul
attribute [local simp] KrohnRhodes.krasnerKaloujnine_hom_left



set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {G Q : Type} [Group G] (act : G →* Function.End Q) (g : G) :
    ∃ w : WreathProduct ↥(resetSubmonoid Q) G G,
      Covers (groupProj act) w (act g) := by
  -- The DKS family-1 witness: trivial decoration, base `g`. Then
  -- `ŵ • (p, y) = (p, g·y)` decodes to `act (g·y) p = act g (act y p)` by
  -- multiplicativity of `act` (composition in `Function.End` is definitional).
  refine ⟨⟨fun _ => 1, g⟩, fun p y => ?_⟩
  simp only [groupProj, one_smul, smul_eq_mul, map_mul]
  rfl
end KrohnRhodes
