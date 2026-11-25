-- Prove2me | solution 1 for HcInf.cayleyLoc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:43.975004+00:00
-- url     : https://prove2.me/submissions/ed003c7e-bd72-4e47-8611-933b8584daf5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
import Theorems.Thm_HcInf_cayS_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HcInf
theorem _root_.solution (hM : CayInvMeas) (hI : CayInvIff) (hU : CaySUnivMeas) (hD : CayleyDens) :
    CayleyLoc := by
  intro P Q m hm c hc0 hcT lam hlam hlim ε hε
  obtain ⟨D, hD0, hDm, f, hf, hft, hmap⟩ := hD P Q m hm c hc0 hcT lam hlam hlim
  have hε0 : ((ε : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hε.ne'
  have h1ε : (1 + (ε : ℝ≥0∞)) ≠ ⊤ := by simp
  set N : Set ℝ≥0∞ := {y | y < (1 + (ε : ℝ≥0∞)) * c} ∩ {y | c < (1 + (ε : ℝ≥0∞)) * y} with hN
  have hNo : IsOpen N := by
    refine isOpen_lt continuous_id continuous_const |>.inter ?_
    exact isOpen_lt continuous_const (ENNReal.continuous_const_mul h1ε)
  have hlt : c < (1 + (ε : ℝ≥0∞)) * c := by
    rw [add_mul, one_mul]
    exact ENNReal.lt_add_right hcT (mul_ne_zero hε0 hc0)
  have hcN : c ∈ N := ⟨hlt, hlt⟩
  set V : Set (lieU P Q) := D ∩ f ⁻¹' N with hV
  have hVm : MeasurableSet V := hDm.inter (hf hNo.measurableSet)
  have hV0 : V ∈ 𝓝 (0 : lieU P Q) := Filter.inter_mem hD0 (hft (hNo.mem_nhds hcN))
  have hVD : V ⊆ D := Set.inter_subset_left
  refine ⟨V, hV0, hVm, ?_, cayInv P Q, hM P Q, ?_, f, hf, ?_, ?_⟩
  · rw [cayS_eq hI]
    exact (hU P Q).inter (hM P Q hVm)
  · intro g X hX
    constructor
    · intro h
      exact ⟨⟨X, hX, h⟩, hI P Q g X h⟩
    · rintro ⟨⟨X', hX', h'⟩, hg⟩
      rw [hI P Q g X' h'] at hg
      rw [← hg]
      exact h'
  · intro X hX
    exact ⟨hX.2.1.le, hX.2.2.le⟩
  · have e1 : cayS V = cayInv P Q ⁻¹' V ∩ cayS D := by
      rw [cayS_eq hI, cayS_eq hI P Q D, Set.inter_comm]
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2, hVD h1⟩
      · rintro ⟨h1, h2, -⟩
        exact ⟨h1, h2⟩
    rw [e1, ← Measure.restrict_restrict (hM P Q hVm), ← Measure.restrict_map (hM P Q) hVm, hmap,
      restrict_withDensity hVm, Measure.restrict_restrict hVm, Set.inter_eq_left.2 hVD]
end HcInf
