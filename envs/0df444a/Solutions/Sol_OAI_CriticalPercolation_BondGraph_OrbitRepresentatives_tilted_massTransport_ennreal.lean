-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:17:17.205413+00:00
-- url     : https://prove2.me/submissions/481b89db-6e84-4d62-9bda-48bf00458f6a

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_OrbitRepresentatives_enn_fiber_sum

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

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_TiltedMassTransport
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma suborbitCard_mul_modularRatio (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (x y : V) :
    (G.suborbitCard y x : ℝ) * G.modularRatio x y = G.suborbitCard x y := by
  unfold modularRatio
  have hn : (G.suborbitCard y x : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x))
  field_simp

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_TiltedTransportENNReal
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
namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma tsum_ennRow (F : V → V → ℝ≥0∞) :
    (∑' p, ennRow G R F p) = ∑ x ∈ R.roots, ∑' y, F x y := by
  change (∑' p : {x // x∈R.roots} × V, F p.1 p.2) = _
  rw [ENNReal.tsum_prod (f := fun (x : {x // x∈R.roots}) y => F x y)]
  simp only [tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => ∑' y, F x y)

lemma tilted_massTransport_ennreal_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) :
    (∑ x ∈ R.roots, ∑' y, F x y) =
      ∑ y ∈ R.roots, ∑' x, F x y * G.stabilizerWeight y x := by
  let F' := fun x y => F y x * G.stabilizerWeight x y
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := by
    simp only [F',hF,Aut.stabilizerWeight]
  have heq : (∑' p, ennRow G R F p) = (∑' p, ennRow G R F' p) := by
    calc
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q}, ennRow G R F p :=
        (ENNReal.tsum_fiberwise _ _).symm
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          ennRow G R F' p := by
        apply tsum_congr
        intro q
        induction q using Quotient.inductionOn' with
        | h p =>
          change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2}, ennRow G R F z) =
            ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1}, ennRow G R F' z
          rw [enn_fiber_sum G R hc hl F hF,enn_fiber_sum G R hc hl F' hF']
          have hbal : (G.suborbitCard p.2 p.1 : ℝ≥0∞) * G.stabilizerWeight p.2 p.1 =
              (G.suborbitCard p.1 p.2 : ℝ≥0∞) := by
            unfold stabilizerWeight
            rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _),
              G.suborbitCard_mul_modularRatio hc hl,ENNReal.ofReal_natCast]
          simp only [F']
          rw [mul_left_comm, hbal, mul_comm]
      _ = ∑' p, ennRow G R F' p :=
        (G.swapPairOrbit.tsum_eq _).trans (ENNReal.tsum_fiberwise _ _)
  rw [tsum_ennRow G R F,tsum_ennRow G R F'] at heq
  exact heq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.OrbitRepresentatives.tilted_massTransport_ennreal_oai.{u_1, u_2}
