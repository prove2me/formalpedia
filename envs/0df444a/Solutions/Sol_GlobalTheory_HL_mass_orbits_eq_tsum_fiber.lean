-- Prove2me | solution 1 for GlobalTheory.HL.mass_orbits_eq_tsum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:27.113073+00:00
-- url     : https://prove2.me/submissions/529a3934-01bf-4070-8461-7b56dd1ec8e1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
import Theorems.Thm_GlobalTheory_HL_encard_eq_tsum_fiber
import Theorems.Thm_GlobalTheory_HL_encard_orbit_fiber
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
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
theorem _root_.solution : ∀ {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y] (H K0 : Subgroup G) (P : X → Prop) (π : X → Y), K0 ≤ H → (∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x ∧ invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (H ⊓ MulAction.stabilizer G x)) → (∀ x, P x → K0.relIndex (H ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ K0.relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G (π x)).relIndex K0 ≠ 0) → (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G o.out)) else 0) = ∑' c : MulAction.orbitRel.Quotient H Y, ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G c.out)) * (({x | P x ∧ π x = c.out} : Set X).encard : ℝ≥0∞) := by
  intro G X Y _ _ _ H K0 P π _ hP hc
  have hP' : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x :=
    fun h hh x hx => ⟨(hP h hh x hx).1, (hP h hh x hx).2.1⟩
  simp only [fun c : MulAction.orbitRel.Quotient H Y =>
    encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X))
      (fun x => P x ∧ π x = c.out), ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  have hmem : ∀ z : X, (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = o →
      ∃ h ∈ H, h • z = o.out := by
    intro z hz
    have : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient H X) = Quotient.mk'' z := by
      rw [hz]; exact Quotient.out_eq' o
    rw [Quotient.eq'', MulAction.orbitRel_apply] at this
    obtain ⟨h, hh⟩ := this
    exact ⟨h, h.2, hh⟩
  split_ifs with ho
  · set c0 : MulAction.orbitRel.Quotient H Y := Quotient.mk'' (π o.out) with hc0
    rw [tsum_eq_single c0]
    · have : (Quotient.mk'' c0.out : MulAction.orbitRel.Quotient H Y) = Quotient.mk'' (π o.out) :=
        Quotient.out_eq' c0
      rw [Quotient.eq'', MulAction.orbitRel_apply] at this
      obtain ⟨⟨h, hh⟩, hy⟩ := this
      have hy' : h • π o.out = c0.out := hy
      obtain ⟨p1, p2, p3⟩ := hP h hh _ ho
      have ho' : o = Quotient.mk'' (h • o.out) := by
        conv_lhs => rw [← Quotient.out_eq' o]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [← p3, ← hy', ← p2]
      generalize h • o.out = x at p1 ho'
      obtain ⟨a1, a2, a3, a4⟩ := hc x p1
      have hle : H ⊓ MulAction.stabilizer G x ≤ H ⊓ MulAction.stabilizer G (π x) := by
        rintro g ⟨g1, g2⟩
        refine ⟨g1, ?_⟩
        have g3 : g • x = x := g2
        have := (hP' g g1 x p1).2
        rw [g3] at this
        exact this.symm
      obtain ⟨-, -, b, -⟩ := invVol_mul_pos_le_conj K0 _ _ a3 a4 a1 a2
      rw [ho', encard_orbit_fiber H P π hP' x p1 (Subgroup.relIndex_ne_zero_trans a2 a3), b hle,
        ENNReal.ofReal_mul' (Nat.cast_nonneg _)]
      simp
    · intro c hne
      have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
          Set X) = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, h3⟩
        obtain ⟨h, hh, e⟩ := hmem z h1
        apply hne
        rw [hc0, ← e, (hP' h hh z h2).2, h3]
        conv_lhs => rw [← Quotient.out_eq' c]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [this]; simp
  · symm
    refine ENNReal.tsum_eq_zero.2 fun c => ?_
    have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
        Set X) = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      obtain ⟨h, hh, e⟩ := hmem z h1
      exact ho (e ▸ (hP' h hh z h2).1)
    rw [this]; simp
end GlobalTheory.HL
