-- Prove2me | solution 1 for GlobalTheory.HL.encard_orbit_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:15:45.325002+00:00
-- url     : https://prove2.me/submissions/820767fe-5a52-4f61-af88-0e93680e5c07

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (H : Subgroup G) (P : X → Prop) (π : X → Y)
    (hP : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x) (x : X) (hx : P x)
    (hfin : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0) :
    ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X).encard
      = (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) := by
  have h1 : ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X)
      = MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x := by
    ext z
    simp only [Set.mem_setOf_eq, Quotient.eq'', MulAction.orbitRel_apply]
    constructor
    · rintro ⟨⟨h, rfl⟩, -, hz⟩
      have h2 := (hP h h.2 x hx).2
      exact ⟨⟨h, h.2, h2.symm.trans hz⟩, rfl⟩
    · rintro ⟨⟨h, hh, hs⟩, rfl⟩
      have h2 := hP h hh x hx
      exact ⟨⟨⟨h, hh⟩, rfl⟩, h2.1, h2.2.trans hs⟩
  have h2 : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x))
      = (MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext ⟨h, hh, hs⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun a => a.2, fun a => ⟨hh, a⟩⟩
  rw [h1, h2]
  rw [h2] at hfin
  exact (Set.finite_of_ncard_ne_zero hfin).cast_ncard_eq.symm
end GlobalTheory.HL
