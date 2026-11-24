-- Prove2me | solution 1 for GlobalTheory.RowFubini.haar_trace_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:53:35.066098+00:00
-- url     : https://prove2.me/submissions/cd8b1459-c82b-46a3-8b47-ff48e8b9575c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
import Theorems.Thm_GlobalTheory_RowFubini_measure_pos_lt_top
import Theorems.Thm_GlobalTheory_RowFubini_comap_open_compact
import Theorems.Thm_GlobalTheory_RowFubini_map_open_compact
import Theorems.Thm_GlobalTheory_RowFubini_mem_conjSub
import Theorems.Thm_GlobalTheory_RowFubini_conjSub_open_compact
import Theorems.Thm_GlobalTheory_RowFubini_cross_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
namespace GlobalTheory.RowFubini
theorem _root_.solution : ∀ {X Y : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N K : Subgroup X) (π : R →* Y) (σ : Y →* R),
    IsClosed (R : Set X) → IsClosed (N : Set X) → N ≤ R → IsOpen (K : Set X) → IsCompact (K : Set X) →
    Continuous π → Continuous σ → (∀ y, π (σ y) = y) → (∀ r : R, π r = 1 ↔ r.1 ∈ N) →
    ∀ ρ : Measure R, ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure N) (ν : Measure Y), 0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : X,
      ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} = κ * la.real {n : N | b⁻¹ * n.1 * b ∈ K} * ν.real (π '' {r : R | b⁻¹ * r.1 * b ∈ K}) := by
  intro X Y _ _ _ _ _ _ _ _ _ _ R N K π σ hR hN hNR hKo hKc hπ hσ hsec hker ρ hρ
  obtain ⟨aKo, aKc⟩ := comap_open_compact R K hR hKo hKc
  obtain ⟨nKo, nKc⟩ := comap_open_compact N K hN hKo hKc
  obtain ⟨pKo, pKc⟩ := map_open_compact _ π σ hπ hσ hsec aKo aKc
  let la : Measure N := Measure.haarMeasure ⟨⟨_, nKc⟩, by
    show (interior ((K.comap N.subtype : Subgroup N) : Set N)).Nonempty
    rw [nKo.interior_eq]; exact ⟨1, Subgroup.one_mem _⟩⟩
  let ν : Measure Y := Measure.haarMeasure ⟨⟨_, pKc⟩, by
    show (interior (((K.comap R.subtype).map π : Subgroup Y) : Set Y)).Nonempty
    rw [pKo.interior_eq]; exact ⟨1, Subgroup.one_mem _⟩⟩
  have hla : la.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hν : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have pos : ∀ Q : Subgroup X, IsOpen (Q : Set X) → IsCompact (Q : Set X) →
      0 < ρ.real (Q.comap R.subtype) ∧ 0 < la.real (Q.comap N.subtype) ∧
        0 < ν.real ((Q.comap R.subtype).map π) := by
    intro Q ho hc
    obtain ⟨ao, ac⟩ := comap_open_compact R Q hR ho hc
    obtain ⟨no, nc⟩ := comap_open_compact N Q hN ho hc
    obtain ⟨po, pc⟩ := map_open_compact _ π σ hπ hσ hsec ao ac
    obtain ⟨a1, a2⟩ := measure_pos_lt_top ρ _ ao ac
    obtain ⟨n1, n2⟩ := measure_pos_lt_top la _ no nc
    obtain ⟨p1, p2⟩ := measure_pos_lt_top ν _ po pc
    exact ⟨ENNReal.toReal_pos a1.ne' a2.ne, ENNReal.toReal_pos n1.ne' n2.ne,
      ENNReal.toReal_pos p1.ne' p2.ne⟩
  obtain ⟨aK, nK, pK⟩ := pos K hKo hKc
  refine ⟨ρ.real (K.comap R.subtype) /
    (la.real (K.comap N.subtype) * ν.real ((K.comap R.subtype).map π)), la, ν,
    div_pos aK (mul_pos nK pK), hla, hν, fun b => ?_⟩
  obtain ⟨hCo, hCc⟩ := conjSub_open_compact K b hKo hKc
  have hDo : IsOpen ((conjSub K b ⊓ K : Subgroup X) : Set X) := hCo.inter hKo
  have hDc : IsCompact ((conjSub K b ⊓ K : Subgroup X) : Set X) :=
    hCc.inter_right (K.isClosed_of_isOpen hKo)
  obtain ⟨-, nD, pD⟩ := pos _ hDo hDc
  have e1 := cross_identity R N π σ hR hN hNR hπ hσ hsec hker ρ la ν _ _ inf_le_left hDo hDc
    hCo hCc
  have e2 := cross_identity R N π σ hR hN hNR hπ hσ hsec hker ρ la ν _ _ inf_le_right hDo hDc
    hKo hKc
  have sR : {r : R | b⁻¹ * r.1 * b ∈ K} = ((conjSub K b).comap R.subtype : Subgroup R) := by
    ext r; exact (mem_conjSub K b r.1).symm
  have sN : {n : N | b⁻¹ * n.1 * b ∈ K} = ((conjSub K b).comap N.subtype : Subgroup N) := by
    ext n; exact (mem_conjSub K b n.1).symm
  rw [sR, sN, ← Subgroup.coe_map, div_mul_eq_mul_div, div_mul_eq_mul_div,
    eq_div_iff (mul_pos nK pK).ne']
  apply mul_right_cancel₀ (mul_pos nD pD).ne'
  linear_combination (la.real (K.comap N.subtype) * ν.real ((K.comap R.subtype).map π)) * e1 -
    (la.real ((conjSub K b).comap N.subtype) *
      ν.real (((conjSub K b).comap R.subtype).map π)) * e2
end GlobalTheory.RowFubini
