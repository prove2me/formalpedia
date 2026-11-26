-- Prove2me | solution 1 for KrohnRhodes.cover_act_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:28.849169+00:00
-- url     : https://prove2.me/submissions/c839afd5-e368-4fd7-98fc-a0fc9df39575

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
theorem _root_.solution {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M)
    (N : Submonoid M) (n : ↥N) :
    ∃ w : WreathProduct ↥(closureMonoid (localActHom act c))
      ↥(closureMonoid (extAct act N)) (Q ⊕ ↥N),
      Covers (dksProj act c N) w (act n.1) := by
  refine ⟨⟨fun _ => 1, ⟨extAct act N n,
    Submonoid.subset_closure (Set.mem_union_left _ ⟨n, rfl⟩)⟩⟩, ?_⟩
  intro p y
  cases y with
  | inl q => rfl
  | inr m =>
      change act ((n * m : ↥N) : M) p.1 = act (n : M) (act (m : M) p.1)
      rw [MulMemClass.coe_mul, map_mul]
      rfl
end KrohnRhodes
