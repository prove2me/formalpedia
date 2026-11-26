-- Prove2me | solution 1 for KrohnRhodes.cover_act_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:39.862436+00:00
-- url     : https://prove2.me/submissions/3c92ccbf-c735-48b3-9703-c8bdb7977616

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
public import Theorems.Thm_KrohnRhodes_MonoidDivides_trans


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M)
    (N : Submonoid M) :
    ∃ w : WreathProduct ↥(closureMonoid (localActHom act c))
      ↥(closureMonoid (extAct act N)) (Q ⊕ ↥N),
      Covers (dksProj act c N) w (act c) := by
  -- The DKS family-3 witness: the decoration `f_c` sends a state `inl q` to the constant
  -- transformation of `cQ` onto `⟨act c q⟩`, and `inr n` to the local action of
  -- `c·n·c ∈ cM ∩ Mc`; the base is the constant onto `inr 1`.
  refine ⟨⟨Sum.elim
      (fun q => ⟨constEnd ⟨act c q, q, rfl⟩,
        Submonoid.subset_closure (Set.mem_union_right _ ⟨_, rfl⟩)⟩)
      (fun n => ⟨localActHom act c ⟨c * n.1 * c, ⟨n.1 * c, mul_assoc c n.1 c⟩, ⟨c * n.1, rfl⟩⟩,
        Submonoid.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)⟩),
      ⟨constEnd (Sum.inr 1),
        Submonoid.subset_closure (Set.mem_union_right _ ⟨_, rfl⟩)⟩⟩, ?_⟩
  -- After the constant base, the second coordinate is `inr 1`, so the decoded value is
  -- `act 1` of the new local state's value — i.e. that value itself:
  have hone : ∀ z : Q, act ((1 : ↥N) : M) z = z := by
    intro z
    rw [OneMemClass.coe_one, map_one]
    rfl
  -- The local-divisor computation: for `u ∈ cM ∩ Mc` with `u = c·m·c` and a local state
  -- `p = act c x`, the chosen-factorization action value is `act c (act m p)` — the
  -- choice drops out because the value equals `act (c·m·c) x`:
  have key : ∀ (u : LocalDivisor M c) (m : M), u.val = c * m * c →
      ∀ p : cQSet act c, act (Classical.choose u.mem_right) p.1 = act c (act m p.1) := by
    intro u m hu p
    obtain ⟨x, hx⟩ := p.2
    have hb := Classical.choose_spec u.mem_right
    rw [hx]
    calc act (Classical.choose u.mem_right) (act c x)
        = act (Classical.choose u.mem_right * c) x := by rw [map_mul]; rfl
      _ = act u.val x := by rw [← hb]
      _ = act (c * m * c) x := by rw [hu]
      _ = act c (act m (act c x)) := by rw [map_mul, map_mul]; rfl
  intro p y
  cases y with
  | inl q => exact hone (act c q)
  | inr n =>
      exact (hone _).trans
        (key ⟨c * n.1 * c, ⟨n.1 * c, mul_assoc c n.1 c⟩, ⟨c * n.1, rfl⟩⟩ n.1 rfl p)
end KrohnRhodes
