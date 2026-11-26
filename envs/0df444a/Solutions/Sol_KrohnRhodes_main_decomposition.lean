-- Prove2me | solution 1 for KrohnRhodes.main_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:02.613452+00:00
-- url     : https://prove2.me/submissions/fdfb9a92-6ed7-4b43-bd7c-679253cddf47

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
public import Theorems.Thm_KrohnRhodes_closure_monoid_gen
public import Theorems.Thm_KrohnRhodes_sgdiv_of_covering
public import Theorems.Thm_KrohnRhodes_dks_proj_surjective
public import Theorems.Thm_KrohnRhodes_cover_const_end
public import Theorems.Thm_KrohnRhodes_cover_act_of_mem
public import Theorems.Thm_KrohnRhodes_cover_act_c

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {M Q : Type} [Monoid M] [DecidableEq M] [Nonempty Q]
    (act : M →* Function.End Q) (A : Finset M)
    (_hA : Submonoid.closure (A : Set M) = ⊤) (c : M) (N : Submonoid M)
    (_hN : ((A.erase c : Finset M) : Set M) ⊆ (N : Set M)) :
    SgDiv ↥(closureMonoid act)
      (WreathProduct ↥(closureMonoid (localActHom act c))
        ↥(closureMonoid (extAct act N)) (Q ⊕ ↥N)) := by
  -- Division from covering, at the decoding `dksProj` (surjective since `Q` is nonempty)
  -- and the generating set `act '' A ∪ {constants}` of the closure (`closure_monoid_gen`
  -- at the generation hypothesis `_hA`):
  refine sgdiv_of_covering (dks_proj_surjective act c N)
    ((⇑act) '' (A : Set M) ∪ Set.range (constEnd : Q → Function.End Q))
    (closureMonoid act) (closure_monoid_gen act (A : Set M) _hA) ?_
  rintro t (⟨a, ha, rfl⟩ | ⟨x, rfl⟩)
  · -- Generators `act a`, `a ∈ A`: family 3 covers the chosen `c`, family 2 covers the
    -- members of `N` — and `a ≠ c` lands in `N` through the containment `_hN`.
    by_cases hac : a = c
    · rw [hac]
      exact cover_act_c act c N
    · exact cover_act_of_mem act c N
        ⟨a, _hN (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hac, Finset.mem_coe.mp ha⟩))⟩
  · -- Constant generators: family 1.
    exact cover_const_end act c N x
end KrohnRhodes
