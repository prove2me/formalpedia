-- Prove2me | solution 1 for KrohnRhodes.group_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:04.090686+00:00
-- url     : https://prove2.me/submissions/317be14b-6cf9-41c6-99da-6406a1bcf297

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
public import Theorems.Thm_KrohnRhodes_sgdiv_of_covering
public import Theorems.Thm_KrohnRhodes_cover_act_group
public import Theorems.Thm_KrohnRhodes_cover_const_group
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
theorem _root_.solution {G Q : Type} [Group G] (act : G →* Function.End Q) :
    SgDiv ↥(closureMonoid act) (WreathProduct ↥(resetSubmonoid Q) G G) := by
  -- The decoding `groupProj` is surjective: `φ (q, 1) = act 1 q = q`.
  have hφ : Function.Surjective (groupProj act) := fun q =>
    ⟨(q, 1), by simp only [groupProj, map_one]; rfl⟩
  -- Division from covering at the DEFINING generating set of the closure
  -- (`closureMonoid act` is literally the closure of `range act ∪ range constEnd`,
  -- so the generation hypothesis is `rfl`):
  refine sgdiv_of_covering hφ
    (Set.range (⇑act) ∪ Set.range (constEnd : Q → Function.End Q))
    (closureMonoid act) rfl ?_
  rintro t (⟨g, rfl⟩ | ⟨x, rfl⟩)
  · -- Group translations: family 1.
    exact cover_act_group act g
  · -- Constants: family 2.
    exact cover_const_group act x
end KrohnRhodes
