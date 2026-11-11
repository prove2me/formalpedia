-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.normalizedClusterVolume_eq_at_peak
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:55.602671+00:00
-- url     : https://prove2.me/submissions/6740af2c-9d0c-4df2-a20a-879eb55fe657

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_clusterPeaks_finite_of_mass_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_finite_clusterUpperSet_has_peak
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_finite_clusterUpperSet_of_mass_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_le_one_iff

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularClusterMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S =
      G.stabilizerWeight o a * G.modularMass a S := by
  unfold modularMass
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  split_ifs with hx
  · exact G.stabilizerWeight_change_base hc hl o a x
  · exact (mul_zero _).symm

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularSuperlevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma clusterPeaks_nonempty_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hm : G.modularMass v (G.cluster ω v) ≠ ∞) :
    (G.clusterPeaks ω v).Nonempty := by
  obtain ⟨y,hy,hp,_⟩ := G.finite_clusterUpperSet_has_peak hc hl ω v
    (G.finite_clusterUpperSet_of_mass_ne_top hm)
  exact ⟨y,hy,hp⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PeakRatioTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_eq_one_of_peaks (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (hr : (G.openGraph ω).Reachable x y)
    (hx : G.clusterPeak ω x) (hy : G.clusterPeak ω y) :
    G.stabilizerWeight x y = 1 := by
  apply le_antisymm (hx y hr)
  have h := (G.stabilizerWeight_le_one_iff hc hl x y x).mp (hy x hr.symm)
  simpa only [G.stabilizerWeight_self] using h

lemma clusterPeakRatio_eq_inv_mass (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x y : V) (hh : G.modularMass x (G.cluster ω x) ≠ ∞)
    (hy : y∈G.clusterPeaks ω x) :
    G.clusterPeakRatio ω x = (G.modularMass y (G.cluster ω x))⁻¹ := by
  have hf := G.clusterPeaks_finite_of_mass_ne_top hc hl ω x hh
  have hnon := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω x hh
  have hpos : (G.clusterPeaks ω x).ncard ≠ 0 := (Set.ncard_pos hf).mpr hnon |>.ne'
  unfold clusterPeakRatio
  rw [tsum_eq_sum (s := hf.toFinset) (fun z hz => by
    simp only [hf.mem_toFinset] at hz
    simp only [peakRatioTransport,ite_eq_right hz])]
  have heq (z : V) (hz : z ∈ hf.toFinset) : G.peakRatioTransport ω x z =
      (G.modularMass y (G.cluster ω x))⁻¹ * ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹ := by
    have hz' := hf.mem_toFinset.mp hz
    rw [peakRatioTransport,ite_eq_left hz',G.modularMass_change_base hc hl z y,
      G.stabilizerWeight_eq_one_of_peaks hc hl ω (hz'.1.symm.trans hy.1) hz'.2 hy.2,one_mul]
  rw [Finset.sum_congr rfl heq]
  simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
  rw [←mul_assoc,mul_comm ((G.clusterPeaks ω x).ncard : ℝ≥0∞),mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast hpos) (ENNReal.natCast_ne_top _),mul_one]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedPeakTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma normalizedClusterVolume_eq_at_peak_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x) (hf : G.modularMass x (G.cluster ω x)≠∞) :
    G.normalizedClusterVolume ω x=G.modularMass x (G.cluster ω x) := by
  rw [normalizedClusterVolume,G.clusterPeakRatio_eq_inv_mass hc hl ω x x hf
    ⟨SimpleGraph.Reachable.refl x,hp⟩,ite_eq_right (ENNReal.inv_ne_zero.mpr hf),inv_inv]

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.normalizedClusterVolume_eq_at_peak_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.normalizedClusterVolume_eq_at_peak_oai.{u_1, u_2}
