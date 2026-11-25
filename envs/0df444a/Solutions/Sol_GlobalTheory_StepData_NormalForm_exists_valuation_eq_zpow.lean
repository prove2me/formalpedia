-- Prove2me | solution 1 for GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:27.890444+00:00
-- url     : https://prove2.me/submissions/acb5b7d4-2286-409c-a355-f11743ea4e7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsValuationEqZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.NormalForm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open MeasureTheory ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData.NormalForm
namespace _root_.GlobalTheory.StepData.NormalForm
theorem _root_.solution {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    (d : kˣ) : ∃ e : ℤ, valuation k (d : k) = valuation k (ϖ : k) ^ e := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hu0 : φ (uniformizer k) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact (uniformizer_pos).ne'
  have hu1 : φ (uniformizer k) < 1 := by
    rw [← map_one φ]; exact φ.strictMono uniformizer_lt_one
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hu0
  have ha1 : a.toAdd < 0 := by
    rw [← ha] at hu1
    exact_mod_cast hu1
  have ha2 : -1 ≤ a.toAdd := by
    have h1 : φ.symm ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) < 1 := by
      rw [← map_one φ.symm]
      exact φ.symm.strictMono
        (by exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) < 1 by decide))
    have h2 := le_uniformizer_iff.mpr h1
    have h3 := φ.strictMono.monotone h2
    simp only [OrderMonoidIso.apply_symm_apply, ← ha] at h3
    exact_mod_cast h3
  have ha3 : a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective; simp; omega
  have hd0 : φ (valuation k (d : k)) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]; exact d.ne_zero
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.mp hd0
  have hz : φ (uniformizer k ^ (-b.toAdd)) = φ (uniformizer k) ^ (-b.toAdd) := map_zpow₀ φ _ _
  have key : φ (valuation k (d : k)) = φ (valuation k (ϖ : k) ^ (-b.toAdd)) := by
    rw [hϖ, hz, ← ha, ← hb, ha3, ← WithZero.coe_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp
  exact ⟨-b.toAdd, φ.injective key⟩
end _root_.GlobalTheory.StepData.NormalForm
end GlobalTheory.StepData.NormalForm
