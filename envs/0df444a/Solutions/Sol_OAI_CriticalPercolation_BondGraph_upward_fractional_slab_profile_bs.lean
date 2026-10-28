-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.upward_fractional_slab_profile_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:00:06.538841+00:00
-- url     : https://prove2.me/submissions/5f122aeb-ec6b-4c96-82b9-75c8589c3d78

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BernoulliProduct

variable {E : Type*}

lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_TailProduct
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_eq_infinitePi (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id

lemma independent_coordinates (q : E → unitInterval) :
    iIndep coordinateSigma (law q) := by
  rw [law_eq_infinitePi]
  exact iIndepFun_infinitePi (X := fun _ (b : Prop) => b) (fun _ => measurable_id)

lemma independent_blocks (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl coordinateSigma_le (independent_coordinates q) S

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BlockExposure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E B : Type*}

lemma measurable_block_of_dependsOn {A : Type*} [MeasurableSpace A]
    {f : Set E → A} (hf : Measurable f) (S : Set E) (hdep : DependsOn f S) :
    @Measurable (Set E) A (blockSigma S) inferInstance f := by
  have hm := hf.comp (measurable_forceOn_block Sᶜ (∅ : Set E))
  rw [compl_compl] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  apply hdep
  intro e he
  simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he),
    Set.mem_empty_iff_false]
  rfl

lemma lintegral_indicator_fresh (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hdep : DependsOn (fun ω => ω ∈ A) S)
    (g : Set E → ℝ≥0∞) (hg : Measurable g) (hgdep : DependsOn g Sᶜ) :
    (∫⁻ ω, A.indicator g ω ∂law q) = law q A * ∫⁻ ω, g ω ∂law q := by
  have hAb : MeasurableSet[blockSigma S] A := by
    have hm := hA.preimage (measurable_forceOn_block Sᶜ (∅ : Set E))
    rw [compl_compl] at hm
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    apply Iff.of_eq
    apply hdep
    intro e he
    simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he)]
    rfl
  have hgb := measurable_block_of_dependsOn hg Sᶜ hgdep
  have hi := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (blockSigma_le S) (blockSigma_le Sᶜ)
    (independent_blocks q S)
    ((measurable_const : @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance
      (fun _ => 1)).indicator hAb) hgb
  have heq : (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω * g ω) = A.indicator g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  have hone := lintegral_indicator_const (μ := law q) hA (1 : ℝ≥0∞)
  simp only [one_mul] at hone
  rw [heq, hone] at hi
  exact hi

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Restriction

theorem measurable_set_restrict (s : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply e.val).comp MeasurableEquiv.setOfPred.symm.measurable))

 
theorem law_map_restrict (p : unitInterval) (s : Set E) :
    (law p : Measure (Set E)).map (fun ω => (Subtype.val ⁻¹' ω : Set s)) = law p := by
  have hm := measurable_set_restrict s
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ∘
      (fun f : E → Prop => {e | f e}) =
      (fun f : s → Prop => {e | f e}) ∘ s.domRestrict := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop),
    Measure.infinitePi_map_restrict', setBernoulli_eq_map]
  simp only [Set.mem_univ]

end Restriction

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Criticality_Sharpness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Russo formulae, exterior exposure and subcritical sharpness. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SharpnessSusceptibility
open Filter Topology
attribute [local instance] Classical.propDecidable Classical.decEq


theorem internalEdges_mono (G : BondGraph V E) {S T : Set V} (h : S ⊆ T) :
    internalEdges G S ⊆ internalEdges G T := fun _ he x hx => h (he x hx)

end SharpnessSusceptibility

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_image_equiv (e : E ≃ E) :
    Measurable (fun ω : Set E => e '' ω) := by
  have he : (fun ω : Set E => e '' ω) = (fun ω => e.symm ⁻¹' ω) := by
    funext ω
    ext i
    simp
  rw [he]
  exact Measurable.of_eval (fun index => measurable_set_mem (e.symm index))

lemma law_map_equiv (p : unitInterval) (e : E ≃ E) :
    (law (fun _ : E => p)).map (fun ω : Set E => e '' ω) = law (fun _ : E => p) := by
  unfold law
  rw [Measure.map_map (measurable_image_equiv e) MeasurableEquiv.setOfPred.measurable]
  have he : (fun ω : Set E => e '' ω) ∘ MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ MeasurableEquiv.piCongrLeft (fun _ : E => Prop) e := by
    funext ω
    ext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_piCongrLeft (fun _ : E => bitMeasure p) e]

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma law_map_aut (p : unitInterval) (φ : G.Aut) :
    (G.law p).map (fun ω : Set E => φ.edge '' ω) = G.law p := by
  simpa only [BernoulliProduct.law_const, law] using
    BernoulliProduct.law_map_equiv p φ.edge

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PhaseInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_openGraph (G : BondGraph V E) (ω : Set E) :
    (criticalModel G).openGraph ω = openSimpleGraph G ω := by
  ext x y
  simp only [CriticalPercolation.BondGraph.openGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_image, openSimpleGraph, criticalModel]
  tauto

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RelativeModular
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace Subgroup
open scoped _root_.Subgroup
variable {Γ : Type*} [Group Γ]

lemma relativeMass_self (A : Subgroup Γ) : relativeMass A A = 1 := by
  simp [relativeMass]

end Subgroup
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_GraphModular
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularRatio_self (x : V) : G.modularRatio x x = 1 := by
  rw [modularRatio_eq_relativeMass,Subgroup.relativeMass_self]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularClusterMass
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

@[simp] lemma stabilizerWeight_self (o : V) : G.stabilizerWeight o o = 1 := by
  simp [stabilizerWeight,modularRatio_self]

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedMassTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma tilted_massTransport (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (hrow : ∀ x, (Function.support (F x)).Finite)
    (hcol : ∀ y, (Function.support (fun x => F x y)).Finite) :
    (∑ x ∈ R.roots, ∑' y, F x y) =
      ∑ y ∈ R.roots, ∑' x, F x y * G.modularRatio x y := by
  let F' := fun x y => F y x * G.modularRatio y x
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := by
    simp only [F',hF,Aut.modularRatio]
  have hc' (x : V) : (Function.support (F' x)).Finite := by
    apply (hcol x).subset
    intro y hy
    exact fun hz => hy (by simp only [F',hz,zero_mul])
  have hs : Summable (weightedRow G R (fun _ => 1) F) :=
    summable_of_hasFiniteSupport (weightedRow_finite G R _ F hrow)
  have ht : Summable (weightedRow G R (fun _ => 1) F') :=
    summable_of_hasFiniteSupport (weightedRow_finite G R _ F' hc')
  have heq : (∑' p, weightedRow G R (fun _ => 1) F p) =
      ∑' p, weightedRow G R (fun _ => 1) F' p := by
    calc
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q},
          weightedRow G R (fun _ => 1) F p :=
        (hs.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq.symm
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          weightedRow G R (fun _ => 1) F' p := by
        apply tsum_congr
        intro q
        induction q using Quotient.inductionOn' with
        | h p =>
          change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2},
            weightedRow G R (fun _ => 1) F z) =
              ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1},
                weightedRow G R (fun _ => 1) F' z
          rw [fiber_sum G R hc hl _ (fun _ _ => rfl) F hF,
            fiber_sum G R hc hl _ (fun _ _ => rfl) F' hF']
          simp only [one_mul,F']
          rw [mul_left_comm,suborbitCard_mul_modularRatio G hc hl,mul_comm]
      _ = ∑' p, weightedRow G R (fun _ => 1) F' p := by
        exact (G.swapPairOrbit.tsum_eq (fun q =>
          ∑' p : (pairMap G R) ⁻¹' {q}, weightedRow G R (fun _ => 1) F' p)).trans
            (ht.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq
  rw [tsum_weightedRow G R _ F hrow,tsum_weightedRow G R _ F' hc'] at heq
  simpa only [one_mul,F'] using heq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedTransportENNReal
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma enn_fiber_sum_root (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x : {x // x∈R.roots}) (y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  let := (G.stabilizerOrbit_finite hc hl x y).fintype
  rw [← (fiberEquiv G R x y).symm.tsum_eq]
  have hv (z : G.stabilizerOrbit x y) :
      ennRow G R F ((fiberEquiv G R x y).symm z) = F x y := by
    change F x z = F x y
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp z.property
    have hh := hF φ x y
    rwa [hx,hy] at hh
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (G.stabilizerOrbit x y) = G.suborbitCard x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]

lemma enn_fiber_sum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) (x y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ.vertex.symm y
  have hy : φ.vertex v = y := φ.vertex.apply_symm_apply y
  have hq : G.pairOrbit (φ.vertex u) y = G.pairOrbit u v := by
    rw [←hy,Aut.pairOrbit]
  rw [hq,enn_fiber_sum_root G R hc hl F hF ⟨u,hu⟩ v]
  change (G.suborbitCard u v : ℝ≥0∞) * F u v = _
  rw [←hy,Aut.suborbitCard,hF]

lemma tsum_ennRow (F : V → V → ℝ≥0∞) :
    (∑' p, ennRow G R F p) = ∑ x ∈ R.roots, ∑' y, F x y := by
  change (∑' p : {x // x∈R.roots} × V, F p.1 p.2) = _
  rw [ENNReal.tsum_prod (f := fun (x : {x // x∈R.roots}) y => F x y)]
  simp only [tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => ∑' y, F x y)

lemma tilted_massTransport_ennreal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
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

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RandomTiltedTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
variable {V E : Type*} [Countable V] (G : BondGraph V E)

omit [Countable V] in
lemma expected_enn_transport_aut (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (φ : G.Aut) (x y : V) :
    (∫⁻ ω, F ω (φ.vertex x) (φ.vertex y) ∂G.law p) = ∫⁻ ω, F ω x y ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [lintegral_map (hm _ _) (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [ha]

lemma OrbitRepresentatives.random_tilted_transport (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y) :
    (∑ x ∈ R.roots, ∫⁻ ω, ∑' y, F ω x y ∂G.law p) =
      ∑ y ∈ R.roots, ∫⁻ ω, ∑' x, F ω x y * G.stabilizerWeight y x ∂G.law p := by
  simp_rw [lintegral_tsum (fun y => (hm _ y).aemeasurable),
    lintegral_tsum (fun x => ((hm x _).mul_const _).aemeasurable),
    lintegral_mul_const _ (hm _ _)]
  exact OrbitRepresentatives.tilted_massTransport_ennreal G R hc hl _ (G.expected_enn_transport_aut p F hm ha)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularCharacter
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularRatio_aut_translate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio o (φ.vertex x) =
      G.modularRatio o (φ.vertex o) * G.modularRatio o x := by
  rw [←G.modularRatio_cocycle hc hl o (φ.vertex o) (φ.vertex x),Aut.modularRatio]

lemma modularRatio_aut_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio x (φ.vertex x) = G.modularRatio o (φ.vertex o) := by
  have h1 := G.modularRatio_cocycle hc hl o x (φ.vertex x)
  rw [G.modularRatio_aut_translate hc hl o x φ] at h1
  exact (mul_left_cancel₀ (ne_of_gt (G.modularRatio_pos hc hl o x)))
    (h1.trans (mul_comm _ _))

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ModularSlabs
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma modularLogHeight_self (x : V) : G.modularLogHeight x x = 0 := by
  simp only [modularLogHeight,G.modularRatio_self,Real.log_one]

lemma modularLogHeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x v y : V) : G.modularLogHeight x y = G.modularLogHeight x v + G.modularLogHeight v y := by
  unfold modularLogHeight
  rw [← Real.log_mul (G.modularRatio_pos hc hl v x).ne' (G.modularRatio_pos hc hl y v).ne']
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

lemma Aut.modularLogHeight (φ : G.Aut) (x y : V) :
    G.modularLogHeight (φ.vertex x) (φ.vertex y) = G.modularLogHeight x y := by
  simp only [CriticalPercolation.BondGraph.modularLogHeight,Aut.modularRatio]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitHeightComparison
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma orbitAdjustedHeight_self (a : V → ℝ) (x : V) :
    G.orbitAdjustedHeight a x x = 0 := by simp [orbitAdjustedHeight]

lemma orbitAdjustedHeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (x v y : V) :
    G.orbitAdjustedHeight a x y = G.orbitAdjustedHeight a x v + G.orbitAdjustedHeight a v y := by
  simp only [orbitAdjustedHeight,G.modularLogHeight_change_base hc hl x v y]
  ring

lemma orbitAdjustedHeight_aut (a : V → ℝ) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x)
    (φ : G.Aut) (x y : V) :
    G.orbitAdjustedHeight a (φ.vertex x) (φ.vertex y) = G.orbitAdjustedHeight a x y := by
  simp only [orbitAdjustedHeight,Aut.modularLogHeight,ha]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NormalizedLayerTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitAdjustedHeight_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (x y : V) :
    G.orbitAdjustedHeight a y x = -G.orbitAdjustedHeight a x y := by
  have hh := G.orbitAdjustedHeight_change_base hc hl a x y x
  rw [G.orbitAdjustedHeight_self] at hh
  linarith

lemma orbitAdjustedHeight_exp_balance (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ha : ∀ x, 0 < a x) (x y : V) :
    ENNReal.ofReal (a x)*G.stabilizerWeight y x =
      ENNReal.ofReal (a y)*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) := by
  rw [stabilizerWeight,←ENNReal.ofReal_mul (ha x).le,
    ←ENNReal.ofReal_mul (ha y).le]
  congr 1
  rw [orbitAdjustedHeight,modularLogHeight,Real.exp_sub,Real.exp_add,
    Real.exp_log (G.modularRatio_pos hc hl x y),Real.exp_log (ha x),Real.exp_log (ha y)]
  field_simp [(ha y).ne']

theorem OrbitRepresentatives.random_normalized_tilted_transport [Countable V]
    (R : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (hF : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y)=F ω x y) :
    (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, ∑' y, F ω x y ∂G.law p)) =
      ∑ y ∈ R.roots, ENNReal.ofReal (a y)*
        (∫⁻ ω, ∑' x, F ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ∂G.law p) := by
  have hh := OrbitRepresentatives.random_tilted_transport G R hc hl p
    (fun ω x y => ENNReal.ofReal (a x)*F ω x y)
    (fun x y => measurable_const.mul (hm x y))
    (fun φ ω x y => by rw [ha φ x,hF φ ω x y])
  have hin (ω : Set E) (y : V) :
      (∑' x, (ENNReal.ofReal (a x)*F ω x y)*G.stabilizerWeight y x) =
        ENNReal.ofReal (a y)*(∑' x, F ω x y*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) := by
    rw [←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro x
    calc
      _ = F ω x y*(ENNReal.ofReal (a x)*G.stabilizerWeight y x) := by ring
      _ = F ω x y*(ENNReal.ofReal (a y)*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) := by
        rw [G.orbitAdjustedHeight_exp_balance hc hl a hapos x y]
      _ = _ := by ring
  simp_rw [ENNReal.tsum_mul_left,hin,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hh
  exact hh

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ConsistentLayers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma adjustedLayerIndex_self (a : V → ℝ) (R u : ℝ) (x : V) :
    G.adjustedLayerIndex a R u x x=0 := by simp [adjustedLayerIndex]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitNeighborChain
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma orbit_out_aut (x : V) : ∃ φ : G.Aut, φ.vertex (G.vertexOrbit x).out = x := by
  have he : (Quotient.mk'' (G.vertexOrbit x).out : G.VertexOrbit) = Quotient.mk'' x :=
    (G.vertexOrbit x).out_eq'
  exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp (Quotient.exact he))

lemma modularWalkDegree_pos [Nontrivial V] (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x : V) : 0 < G.modularWalkDegree x := by
  apply (Set.ncard_pos (G.finite_neighbors hl x)).mpr
  have h := hc.preconnected.not_isIsolated x
  unfold SimpleGraph.IsIsolated at h
  push Not at h
  exact h

lemma modularWalkDegree_aut (φ : G.Aut) (x : V) :
    G.modularWalkDegree (φ.vertex x) = G.modularWalkDegree x := by
  have he : φ.vertex '' G.fullGraph.neighborSet x = G.fullGraph.neighborSet (φ.vertex x) := by
    ext y
    obtain ⟨z,rfl⟩ := φ.vertex.surjective y
    simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,SimpleGraph.mem_neighborSet,
      Aut.fullGraph_adj]
  unfold modularWalkDegree
  rw [← he,Set.ncard_image_of_injective _ φ.vertex.injective]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitNormalization
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stationaryOrbitWeight_pos [Nontrivial V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) (x : V) :
    0 < G.stationaryOrbitWeight μ x :=
  div_pos (hμ _) (Nat.cast_pos.mpr (G.modularWalkDegree_pos hc hl x))

lemma stationaryOrbitWeight_aut (μ : G.VertexOrbit → ℝ) (φ : G.Aut) (x : V) :
    G.stationaryOrbitWeight μ (φ.vertex x) = G.stationaryOrbitWeight μ x := by
  simp only [stationaryOrbitWeight,G.vertexOrbit_aut,G.modularWalkDegree_aut]

lemma stationaryOrbitWeight_out (μ : G.VertexOrbit → ℝ) (x : V) :
    G.stationaryOrbitWeight μ x = G.stationaryOrbitWeight μ (G.vertexOrbit x).out := by
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  simpa only [hφ] using G.stationaryOrbitWeight_aut μ φ (G.vertexOrbit x).out

theorem stationaryOrbitWeight_uniform_bounds [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ G.stationaryOrbitWeight μ x ∧
      G.stationaryOrbitWeight μ x ≤ M := by
  let : Nonempty G.VertexOrbit := ⟨G.vertexOrbit (Classical.arbitrary V)⟩
  let w : G.VertexOrbit → ℝ := fun i => G.stationaryOrbitWeight μ i.out
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ
    (show G.VertexOrbit → OrderDual ℝ from w) Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  refine ⟨w i,w j,G.stationaryOrbitWeight_pos hc hl μ hμ i.out,fun x => ?_⟩
  rw [G.stationaryOrbitWeight_out μ x]
  exact ⟨hi (G.vertexOrbit x) (Finset.mem_univ _),hj (G.vertexOrbit x) (Finset.mem_univ _)⟩

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma sum_roots_eq_orbitSum [Fintype G.VertexOrbit] (f : G.VertexOrbit → ℝ) :
    ∑ x ∈ R.roots, f (G.vertexOrbit x) = ∑ i, f i := by
  rw [← Finset.sum_coe_sort R.roots (fun x => f (G.vertexOrbit x))]
  exact (R.orbitEquiv G).sum_comp f

end OrbitRepresentatives

lemma orbitNeighborCount_eq_at_vertex (hl : G.LocallyFinite) (x : V) (i : G.VertexOrbit) :
    G.orbitNeighborCount hl (G.vertexOrbit x) i =
      (((G.finite_neighbors hl x).toFinset).filter fun y => G.vertexOrbit y = i).card := by
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  have himage :
      ((((G.finite_neighbors hl (G.vertexOrbit x).out).toFinset).filter
        fun y => G.vertexOrbit y = i).image φ.vertex) =
      (((G.finite_neighbors hl x).toFinset).filter fun y => G.vertexOrbit y = i) := by
    ext y
    constructor
    · rintro h
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hz,ho⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_filter.mpr ⟨(G.finite_neighbors hl x).mem_toFinset.mpr ?_,?_⟩
      · rw [← hφ]
        exact (Aut.fullGraph_adj G φ _ _).mpr ((G.finite_neighbors hl _).mem_toFinset.mp hz)
      · simpa only [G.vertexOrbit_aut] using ho
    · intro hy
      obtain ⟨hy,ho⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_image.mpr ⟨φ.vertex.symm y,Finset.mem_filter.mpr ⟨?_,?_⟩,
        Equiv.apply_symm_apply _ _⟩
      · apply (G.finite_neighbors hl _).mem_toFinset.mpr
        apply (Aut.fullGraph_adj G φ _ _).mp
        have hy' : G.fullGraph.Adj x y := (G.finite_neighbors hl x).mem_toFinset.mp hy
        simpa only [hφ,Equiv.apply_symm_apply] using hy'
      · have he : G.vertexOrbit (φ.vertex.symm y) = G.vertexOrbit y := by
          simpa only [Equiv.apply_symm_apply] using (G.vertexOrbit_aut φ (φ.vertex.symm y)).symm
        exact he.trans ho
  rw [← himage,Finset.card_image_of_injective _ φ.vertex.injective]
  rfl

lemma orbitNeighborTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) (i : G.VertexOrbit) (φ : G.Aut) (x y : V) :
    G.orbitNeighborTransport a i (φ.vertex x) (φ.vertex y) =
      G.orbitNeighborTransport a i x y := by
  simp only [orbitNeighborTransport,G.vertexOrbit_aut,Aut.fullGraph_adj,ha]

lemma orbitNeighborTransport_row_finite (hl : G.LocallyFinite) (a : V → ℝ)
    (i : G.VertexOrbit) (x : V) : (Function.support (G.orbitNeighborTransport a i x)).Finite := by
  apply (G.finite_neighbors hl x).subset
  intro y hy
  by_contra h
  exact hy (ite_eq_right (by simpa only [SimpleGraph.mem_neighborSet] using not_and_of_not_right _ h))

lemma orbitNeighborTransport_col_finite (hl : G.LocallyFinite) (a : V → ℝ)
    (i : G.VertexOrbit) (y : V) : (Function.support (fun x => G.orbitNeighborTransport a i x y)).Finite := by
  apply (G.finite_neighbors hl y).subset
  intro x hx
  by_contra h
  apply hx
  apply ite_eq_right
  exact not_and_of_not_right _ (fun hxy => h hxy.symm)

lemma orbitNeighborTransport_row (hl : G.LocallyFinite) (a : V → ℝ)
    (i : G.VertexOrbit) (x : V) :
    ∑' y, G.orbitNeighborTransport a i x y =
      a x * G.orbitNeighborCount hl (G.vertexOrbit x) i := by
  unfold orbitNeighborTransport
  rw [tsum_eq_sum (f := fun y => if G.vertexOrbit y = i ∧ G.fullGraph.Adj x y then a x else 0)
    (s := (G.finite_neighbors hl x).toFinset) (fun y hy => ite_eq_right (by
      intro h
      exact hy ((G.finite_neighbors hl x).mem_toFinset.mpr h.2)))]
  rw [G.orbitNeighborCount_eq_at_vertex hl x i]
  have he : (∑ y ∈ (G.finite_neighbors hl x).toFinset,
      if G.vertexOrbit y = i ∧ G.fullGraph.Adj x y then a x else 0) =
    ∑ y ∈ ((G.finite_neighbors hl x).toFinset).filter (fun y => G.vertexOrbit y = i), a x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    have hxy : G.fullGraph.Adj x y := (G.finite_neighbors hl x).mem_toFinset.mp hy
    simp only [hxy,and_true]
  rw [he,Finset.sum_const,nsmul_eq_mul,mul_comm]

lemma weightedNeighborIncoming_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x) (φ : G.Aut) (y : V) :
    G.weightedNeighborIncoming a (φ.vertex y) = G.weightedNeighborIncoming a y := by
  unfold weightedNeighborIncoming
  rw [← φ.vertex.tsum_eq (fun x =>
    if G.fullGraph.Adj x (φ.vertex y) then a x * G.modularRatio x (φ.vertex y) else 0)]
  apply tsum_congr
  intro x
  simp only [Aut.fullGraph_adj,ha,Aut.modularRatio]

lemma orbitNeighborTransport_incoming (a : V → ℝ) (i : G.VertexOrbit) (y : V) :
    (∑' x, G.orbitNeighborTransport a i x y * G.modularRatio x y) =
      if G.vertexOrbit y = i then G.weightedNeighborIncoming a y else 0 := by
  by_cases hy : G.vertexOrbit y = i
  · simp only [orbitNeighborTransport,hy,true_and,if_true,weightedNeighborIncoming]
    apply tsum_congr
    intro x
    split_ifs <;> simp only [zero_mul]
  · simp only [orbitNeighborTransport,hy,false_and,if_false,zero_mul,tsum_zero]

theorem weightedNeighborIncoming_stationary [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ) (y : V) :
    G.weightedNeighborIncoming (G.stationaryOrbitWeight μ) y = μ (G.vertexOrbit y) := by
  let R := G.orbitRepresentatives hq
  let a := G.stationaryOrbitWeight μ
  have ha := G.stationaryOrbitWeight_aut μ
  have hout (i : G.VertexOrbit) :
      (∑ x ∈ R.roots, ∑' z, G.orbitNeighborTransport a i x z) = μ i := by
    calc
      _ = ∑ x ∈ R.roots, a x * G.orbitNeighborCount hl (G.vertexOrbit x) i := by
        apply Finset.sum_congr rfl
        intro x _
        exact G.orbitNeighborTransport_row hl a i x
      _ = ∑ j, (μ j / G.modularWalkDegree j.out) * G.orbitNeighborCount hl j i := by
        rw [← R.sum_roots_eq_orbitSum G]
        apply Finset.sum_congr rfl
        intro x _
        rw [show a x = a (G.vertexOrbit x).out from G.stationaryOrbitWeight_out μ x]
        simp only [a,stationaryOrbitWeight,vertexOrbit,Quotient.out_eq']
      _ = Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ i := by
        unfold Percolation.BenjaminiSchramm.orbitChainStep orbitWalkKernel
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = μ i := congrFun hstat i
  have hin (i : G.VertexOrbit) :
      (∑ z ∈ R.roots, ∑' x, G.orbitNeighborTransport a i x z * G.modularRatio x z) =
        G.weightedNeighborIncoming a i.out := by
    calc
      _ = ∑ z ∈ R.roots, if G.vertexOrbit z = i then
          G.weightedNeighborIncoming a (G.vertexOrbit z).out else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        rw [G.orbitNeighborTransport_incoming]
        obtain ⟨φ,hφ⟩ := G.orbit_out_aut z
        by_cases hz : G.vertexOrbit z = i
        · simp only [hz,if_true]
          have he := G.weightedNeighborIncoming_aut a ha φ (G.vertexOrbit z).out
          rw [hφ] at he
          simpa only [hz] using he
        · simp only [hz,if_false]
      _ = ∑ j : G.VertexOrbit, if j = i then G.weightedNeighborIncoming a j.out else 0 :=
        R.sum_roots_eq_orbitSum G (fun j => if j = i then G.weightedNeighborIncoming a j.out else 0)
      _ = _ := by simp
  have hi (i : G.VertexOrbit) : G.weightedNeighborIncoming a i.out = μ i := by
    rw [← hin i,← R.tilted_massTransport G hc hl _
      (G.orbitNeighborTransport_aut a ha i) (G.orbitNeighborTransport_row_finite hl a i)
      (G.orbitNeighborTransport_col_finite hl a i)]
    exact hout i
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut y
  calc
    _ = G.weightedNeighborIncoming a (G.vertexOrbit y).out := by
      simpa only [hφ] using G.weightedNeighborIncoming_aut a ha φ (G.vertexOrbit y).out
    _ = _ := hi (G.vertexOrbit y)

theorem stationaryOrbitWeight_neighbor_sum [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ) (x : V) :
    (∑ y ∈ (G.finite_neighbors hl x).toFinset,
      G.stationaryOrbitWeight μ y * G.modularRatio y x) =
        G.stationaryOrbitWeight μ x * G.modularWalkDegree x := by
  have he : G.weightedNeighborIncoming (G.stationaryOrbitWeight μ) x =
      ∑ y ∈ (G.finite_neighbors hl x).toFinset,
        G.stationaryOrbitWeight μ y * G.modularRatio y x := by
    unfold weightedNeighborIncoming
    rw [tsum_eq_sum (s := (G.finite_neighbors hl x).toFinset)
      (fun y hy => ite_eq_right (fun hxy => hy ((G.finite_neighbors hl x).mem_toFinset.mpr hxy.symm)))]
    apply Finset.sum_congr rfl
    intro y hy
    exact ite_eq_left ((G.finite_neighbors hl x).mem_toFinset.mp hy).symm
  rw [← he,G.weightedNeighborIncoming_stationary hc hl hq μ hstat]
  unfold stationaryOrbitWeight
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (G.modularWalkDegree_pos hc hl x).ne')]

theorem stationaryOrbitHeight_harmonic [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ) (x : V) :
    (∑ y ∈ (G.finite_neighbors hl x).toFinset,
      Real.exp (G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y)) =
        G.modularWalkDegree x := by
  have he (y : V) :
      Real.exp (G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y) =
        (G.stationaryOrbitWeight μ y * G.modularRatio y x) / G.stationaryOrbitWeight μ x := by
    rw [orbitAdjustedHeight,modularLogHeight,Real.exp_sub,Real.exp_add,
      Real.exp_log (G.modularRatio_pos hc hl y x),
      Real.exp_log (G.stationaryOrbitWeight_pos hc hl μ hμ y),
      Real.exp_log (G.stationaryOrbitWeight_pos hc hl μ hμ x)]
    ring
  simp_rw [he]
  rw [← Finset.sum_div,G.stationaryOrbitWeight_neighbor_sum hc hl hq μ hstat]
  exact mul_div_cancel_left₀ _ (G.stationaryOrbitWeight_pos hc hl μ hμ x).ne'

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HarmonicHeightAscent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma height_harmonic_flat_or_rise (hl : G.LocallyFinite) (f : V → ℝ)
    (hf : ∀ x, (∑ y ∈ (G.finite_neighbors hl x).toFinset, Real.exp (f y-f x)) =
      G.modularWalkDegree x) (x : V) :
    (∃ y, G.fullGraph.Adj x y ∧ f x < f y) ∨
      (∀ y, G.fullGraph.Adj x y → f y = f x) := by
  by_cases hu : ∃ y, G.fullGraph.Adj x y ∧ f x < f y
  · exact Or.inl hu
  right
  have hle (y : V) (hy : y ∈ (G.finite_neighbors hl x).toFinset) :
      Real.exp (f y-f x) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact sub_nonpos.mpr (le_of_not_gt (fun h => hu ⟨y,(G.finite_neighbors hl x).mem_toFinset.mp hy,h⟩))
  have hs : (∑ y ∈ (G.finite_neighbors hl x).toFinset, Real.exp (f y-f x)) =
      ∑ _y ∈ (G.finite_neighbors hl x).toFinset, (1 : ℝ) := by
    rw [hf,Finset.sum_const,nsmul_eq_mul,mul_one]
    simp only [modularWalkDegree,Set.ncard_eq_toFinset_card _ (G.finite_neighbors hl x)]
  intro y hxy
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp hs y ((G.finite_neighbors hl x).mem_toFinset.mpr hxy)
  exact sub_eq_zero.mp (Real.exp_injective (by simpa only [Real.exp_zero] using he))

lemma harmonic_ascent_walk (f : V → ℝ)
    (hf : ∀ x, (∃ y, G.fullGraph.Adj x y ∧ f x < f y) ∨
      (∀ y, G.fullGraph.Adj x y → f y = f x)) {x y : V}
    (w : G.fullGraph.Walk x y) (hxy : f y ≠ f x) :
    ∃ z, ∃ q : G.fullGraph.Walk x z, (∀ v ∈ q.support, f x ≤ f v) ∧ f x < f z := by
  induction w with
  | nil => exact False.elim (hxy rfl)
  | @cons x u y hxu w ih =>
    rcases hf x with ⟨z,hxz,hz⟩ | hflat
    · refine ⟨z,.cons hxz .nil,?_,hz⟩
      intro v hv
      simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,List.mem_cons,
        List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl
      · exact le_rfl
      · exact hz.le
    · have hux := hflat u hxu
      obtain ⟨z,q,hq,hz⟩ := ih (by simpa only [hux] using hxy)
      refine ⟨z,.cons hxu q,?_,by simpa only [hux] using hz⟩
      intro v hv
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact le_rfl
      · simpa only [hux] using hq v hv

lemma orbitAdjustedHeight_nonconstant (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x)
    (hu : ¬ G.CombinatoriallyUnimodular) (x : V) :
    ∃ y, G.orbitAdjustedHeight a x y ≠ 0 := by
  by_contra h
  push Not at h
  apply hu
  intro φ y
  have hx := h (φ.vertex x)
  simp only [orbitAdjustedHeight,ha,add_sub_cancel_right] at hx
  have he : G.modularRatio (φ.vertex x) x = 1 := by
    rw [← Real.exp_log (G.modularRatio_pos hc hl (φ.vertex x) x)]
    rw [show Real.log (G.modularRatio (φ.vertex x) x) = 0 from hx,Real.exp_zero]
  have he' : G.modularRatio x (φ.vertex x) = 1 := by
    have hcoc := G.modularRatio_cocycle hc hl x (φ.vertex x) x
    rw [he,mul_one,G.modularRatio_self] at hcoc
    exact hcoc
  rw [← G.modularRatio_aut_base hc hl x y φ] at he'
  unfold modularRatio at he'
  have hcard := (div_eq_one_iff_eq
    (Nat.cast_ne_zero.mpr (G.suborbitCard_pos hc hl (φ.vertex y) y).ne')).mp he'
  exact_mod_cast hcard

theorem stationaryOrbitHeight_ascent [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) (x : V) :
    ∃ y, ∃ w : G.fullGraph.Walk x y,
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
        0 < G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  let f := G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x
  have hself : f x = 0 := G.orbitAdjustedHeight_self _ x
  obtain ⟨y,hy⟩ := G.orbitAdjustedHeight_nonconstant hc hl _
    (G.stationaryOrbitWeight_aut μ) hu x
  have hhar (v : V) : (∑ y ∈ (G.finite_neighbors hl v).toFinset, Real.exp (f y-f v)) =
      G.modularWalkDegree v := by
    have he (y : V) : f y-f v = G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v y := by
      dsimp [f]
      rw [G.orbitAdjustedHeight_change_base hc hl _ x v y,add_sub_cancel_left]
    simp_rw [he]
    exact G.stationaryOrbitHeight_harmonic hc hl hq μ hμ hstat v
  obtain ⟨z,w,hw,hz⟩ := G.harmonic_ascent_walk f (G.height_harmonic_flat_or_rise hl f hhar)
    (hc x y).some (by simpa only [hself] using hy)
  refine ⟨z,w,?_,?_⟩
  · intro v hv
    simpa only [hself] using hw v hv
  · simpa only [hself] using hz

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_UniformHeightAscent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_uniform_ascent [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : Percolation.BenjaminiSchramm.orbitChainStep (G.orbitWalkKernel hl) μ = μ)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L : ℕ, ∀ x, ∃ y, ∃ w : G.fullGraph.Walk x y,
      w.length ≤ L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v) ∧
      ε ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  let : Nonempty G.VertexOrbit := ⟨G.vertexOrbit (Classical.arbitrary V)⟩
  choose y w hw hr using fun i : G.VertexOrbit =>
    G.stationaryOrbitHeight_ascent hc hl hq μ hμ hstat hu i.out
  let a := G.stationaryOrbitWeight μ
  let rise : G.VertexOrbit → ℝ := fun i => G.orbitAdjustedHeight a i.out (y i)
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ rise Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ
    (fun k : G.VertexOrbit => (w k).length) Finset.univ_nonempty
  refine ⟨rise i,hr i,(w j).length,fun x => ?_⟩
  let k := G.vertexOrbit x
  obtain ⟨φ,hφ⟩ := G.orbit_out_aut x
  let f : G.fullGraph →g G.fullGraph :=
    ⟨φ.vertex,fun {_ _} h => (Aut.fullGraph_adj G φ _ _).mpr h⟩
  refine ⟨φ.vertex (y k),((w k).map f).copy hφ rfl,?_,?_,?_⟩
  · simpa only [SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map] using
      hj k (Finset.mem_univ _)
  · intro v hv
    simp only [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨z,hz,rfl⟩ := hv
    change 0 ≤ G.orbitAdjustedHeight a x (φ.vertex z)
    rw [← hφ,G.orbitAdjustedHeight_aut a (G.stationaryOrbitWeight_aut μ)]
    exact hw k z hz
  · change rise i ≤ G.orbitAdjustedHeight a x (φ.vertex (y k))
    rw [← hφ,G.orbitAdjustedHeight_aut a (G.stationaryOrbitWeight_aut μ)]
    exact hi k (Finset.mem_univ _)

lemma height_ascent_iterate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (L : ℕ)
    (hstep : ∀ x, ∃ y, ∃ w : G.fullGraph.Walk x y, w.length ≤ L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v) ∧ ε ≤ G.orbitAdjustedHeight a x y)
    (n : ℕ) (x : V) :
    ∃ y, ∃ w : G.fullGraph.Walk x y, w.length ≤ n*L ∧
      (∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v) ∧
      n*ε ≤ G.orbitAdjustedHeight a x y := by
  induction n with
  | zero =>
    refine ⟨x,.nil,by simp,?_,by simp⟩
    intro v hv
    have he : v = x := List.mem_singleton.mp hv
    rw [he,G.orbitAdjustedHeight_self]
  | succ n ih =>
    obtain ⟨y,w,hlen,hw,hr⟩ := ih
    obtain ⟨z,q,hqlen,hq,hqr⟩ := hstep y
    refine ⟨z,w.append q,?_,?_,?_⟩
    · rw [SimpleGraph.Walk.length_append]
      exact (Nat.add_le_add hlen hqlen).trans_eq (Nat.succ_mul n L).symm
    · intro v hv
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
      · exact hw v hv
      · rw [G.orbitAdjustedHeight_change_base hc hl a x y v]
        exact add_nonneg ((mul_nonneg (Nat.cast_nonneg n) hε).trans hr) (hq v hv)
    · rw [G.orbitAdjustedHeight_change_base hc hl a x y z]
      push_cast
      nlinarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerMomentDecomposition
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_lintegral_rpow_le_rpow_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    (∫⁻ ω, f ω ^ b ∂μ) ≤ (∫⁻ ω, f ω ∂μ)^b := by
  by_cases he : b = 1
  · simp only [he,ENNReal.rpow_one,le_refl]
  have hblt : b < 1 := lt_of_le_of_ne hb1 he
  have hc := Real.holderConjugate_one_div hb (sub_pos.mpr hblt) (by ring : b+(1-b)=1)
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
    ((hf.pow_const b).aemeasurable) (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) μ)
  have hcancel : b*(1/b)=1 := by field_simp
  have hinv : 1/(1/b)=b := by field_simp
  simpa only [Pi.mul_apply,mul_one,ENNReal.one_rpow,←ENNReal.rpow_mul,hcancel,ENNReal.rpow_one,
    lintegral_const,measure_univ,one_mul,hinv] using hh

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma measurable_restrictedLayerCount [Countable V] [Countable E]
    (I : Set E) (A : Set V) (x : V) : Measurable (fun ω => restrictedLayerCount G I A ω x) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.tsum fun y => Measurable.ite
    (measurable_const.and ((measurableSet_conn G x y).mem.comp hm)).setOf
    measurable_const measurable_const

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakFiniteEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {E : Type*}

lemma finiteBondPattern_dependsOn (F : Finset E) (σ : Set E) :
    DependsOn (fun ω => ω ∈ finiteBondPattern F σ) (F : Set E) := by
  intro ω η h
  apply propext
  constructor
  · intro hω e he
    exact (h e he).symm.trans (hω e he)
  · intro hη e he
    exact (h e he).trans (hη e he)

lemma measurableSet_finiteBondPattern [Countable E] (F : Finset E) (σ : Set E) :
    MeasurableSet (finiteBondPattern F σ) :=
  (Measurable.forall fun e => measurable_const.imp
    ((measurable_set_mem e).eq_const (e ∈ σ))).setOf

lemma finiteBondPattern_probability_lower (p : unitInterval) (F : Finset E) (σ : Set E) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) ≤ law p (finiteBondPattern F σ) := by
  let T : Set (F : Set E) := Subtype.val ⁻¹' σ
  have he : finiteBondPattern F σ =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (F : Set E))) ⁻¹' {T} := by
    ext ω
    change (∀ e ∈ F, (e ∈ ω)=(e ∈ σ)) ↔ Subtype.val ⁻¹' ω=T
    constructor
    · intro h
      ext e
      exact Iff.of_eq (h e e.property)
    · intro h e he
      exact propext (show (⟨e,he⟩ : (F : Set E)) ∈ Subtype.val ⁻¹' ω ↔
        (⟨e,he⟩ : (F : Set E)) ∈ T from by rw [h])
  have hprob : (law p).real (finiteBondPattern F σ) =
      (p : ℝ)^T.ncard*(1-p : ℝ)^Tᶜ.ncard := by
    unfold Measure.real
    rw [he,←Measure.map_apply (measurable_set_restrict _) (MeasurableSet.singleton T),law_map_restrict]
    change (ProbabilityTheory.setBernoulli Set.univ p).real {T}=_
    simpa only [←Set.compl_eq_univ_sdiff] using ProbabilityTheory.setBernoulli_real_singleton p
      (Set.subset_univ T) (Set.toFinite Set.univ)
  have hcard : T.ncard+Tᶜ.ncard=F.card := by
    calc
      _ = Nat.card (F : Set E) := Set.ncard_add_ncard_compl T
      _ = F.card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe F
  have hmin : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hb : (min (p : ℝ) (1-p))^F.card ≤ (p : ℝ)^T.ncard*(1-p : ℝ)^Tᶜ.ncard := by
    rw [←hcard,pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hmin (min_le_left _ _) _)
      (pow_le_pow_left₀ hmin (min_le_right _ _) _) (pow_nonneg hmin _) (pow_nonneg p.2.1 _)
  exact ENNReal.ofReal_le_of_le_toReal (hb.trans_eq hprob.symm)

lemma fresh_finiteBondPattern_cell_lower [Countable E]
    (p : unitInterval) (Q : Set E) (A : Set (Set E)) (hA : MeasurableSet A)
    (hdep : DependsOn (fun ω => ω ∈ A) Q)
    (F : Finset E) (hF : (F : Set E) ⊆ Qᶜ) (σ : Set E) :
    law p A*ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) ≤
      law p (A ∩ finiteBondPattern F σ) := by
  let B := finiteBondPattern F σ
  have hB : MeasurableSet B := measurableSet_finiteBondPattern F σ
  have hg : Measurable (B.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hB
  have hd : DependsOn (B.indicator (fun _ => (1 : ℝ≥0∞))) Qᶜ := by
    change ∀ (ω η : Set E), (∀ e ∈ Qᶜ, (e ∈ ω)=(e ∈ η)) →
      B.indicator (fun _ => (1 : ℝ≥0∞)) ω = B.indicator (fun _ => (1 : ℝ≥0∞)) η
    intro ω η h
    have he := finiteBondPattern_dependsOn F σ (fun e he => h e (hF he))
    change (ω ∈ B)=(η ∈ B) at he
    by_cases hω : ω ∈ B
    · have hη : η ∈ B := (Iff.of_eq he).mp hω
      simp only [Set.indicator_of_mem hω,Set.indicator_of_mem hη]
    · have hη : η ∉ B := fun hη => hω ((Iff.of_eq he).mpr hη)
      simp only [Set.indicator_of_notMem hω,Set.indicator_of_notMem hη]
  have hi := CriticalPercolation.BernoulliProduct.lintegral_indicator_fresh
    (fun _ : E => p) Q A hA hdep _ hg hd
  rw [CriticalPercolation.BernoulliProduct.law_const] at hi
  have he : A.indicator (B.indicator (fun _ => (1 : ℝ≥0∞))) =
      (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [Set.indicator,ha,hb]
  rw [he,lintegral_indicator_fun_one (hA.inter hB),lintegral_indicator_fun_one hB] at hi
  exact (mul_le_mul' le_rfl (finiteBondPattern_probability_lower p F σ)).trans_eq hi.symm

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FiniteEnergyModification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma forceOn_finitePattern_eq (F : Finset E) (σ : Set (F : Set E)) (ω : Set E)
    (hω : ω ∈ finiteBondPattern F (Subtype.val '' σ)) :
    forceOn (F : Set E) (Subtype.val '' σ) ω=ω := by
  ext e
  rw [mem_forceOn]
  by_cases he : e ∈ (F : Set E)
  · simpa only [he,if_true] using (Iff.of_eq (hω e he)).symm
  · simp only [he,if_false]

lemma finiteBondPattern_pairwise (F : Finset E) :
    Pairwise (fun σ τ : Set (F : Set E) => Disjoint
      (finiteBondPattern F (Subtype.val '' σ)) (finiteBondPattern F (Subtype.val '' τ))) := by
  intro σ τ hστ
  apply Set.disjoint_left.mpr
  intro ω hσ hτ
  apply hστ
  ext e
  have hh := (hσ e e.property).symm.trans (hτ e e.property)
  simpa only [Set.mem_image,Subtype.val_injective.eq_iff,exists_eq_right] using Iff.of_eq hh

lemma iUnion_finiteBondPattern (F : Finset E) :
    (⋃ σ : Set (F : Set E), finiteBondPattern F (Subtype.val '' σ))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  refine Set.mem_iUnion.mpr ⟨Subtype.val ⁻¹' ω,?_⟩
  intro e he
  apply propext
  simp only [Set.mem_image,Set.mem_preimage]
  constructor
  · intro heω
    exact ⟨⟨e,he⟩,heω,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact hz

lemma forced_event_dependsOn_compl (F : Finset E) (σ : Set E) (B : Set (Set E)) :
    DependsOn (fun ω => forceOn (F : Set E) σ ω ∈ B) (F : Set E)ᶜ := by
  intro ω η hωη
  let ξ : Set E := {e | ω e}
  let ζ : Set E := {e | η e}
  have hh : forceOn (F : Set E) σ ξ=forceOn (F : Set E) σ ζ := by
    ext e
    rw [mem_forceOn,mem_forceOn]
    by_cases he : e ∈ (F : Set E)
    · simp only [he,if_true]
    · simp only [he,if_false]
      exact Iff.of_eq (hωη e he)
  exact congrArg (fun ξ : Set E => ξ ∈ B) hh

variable [Countable E]

lemma finiteModification_probability (p : unitInterval) (F : Finset E)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*law p (finiteModification F B) ≤ law p B := by
  let A (σ : Set (F : Set E)) := (forceOn (F : Set E) (Subtype.val '' σ)) ⁻¹' B
  let P (σ : Set (F : Set E)) := finiteBondPattern F (Subtype.val '' σ)
  have hmA (σ : Set (F : Set E)) : MeasurableSet (A σ) :=
    hB.preimage (measurable_forceOn _ _)
  have hcell (σ : Set (F : Set E)) :
      law p (A σ)*ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) ≤ law p (B ∩ P σ) := by
    have he : A σ ∩ P σ=B ∩ P σ := by
      ext ω
      constructor
      · rintro ⟨ha,hp⟩
        exact ⟨forceOn_finitePattern_eq F σ ω hp ▸ ha,hp⟩
      · rintro ⟨hb,hp⟩
        refine ⟨?_,hp⟩
        change forceOn (F : Set E) (Subtype.val '' σ) ω ∈ B
        rw [forceOn_finitePattern_eq F σ ω hp]
        exact hb
    have hh := fresh_finiteBondPattern_cell_lower p (F : Set E)ᶜ (A σ) (hmA σ)
      (forced_event_dependsOn_compl F _ B) F (by simp only [compl_compl]; exact Set.Subset.rfl)
        (Subtype.val '' σ)
    rwa [he] at hh
  have hd : Pairwise (fun σ τ : Set (F : Set E) => Disjoint (B ∩ P σ) (B ∩ P τ)) :=
    fun σ τ hστ => (finiteBondPattern_pairwise F hστ).mono Set.inter_subset_right Set.inter_subset_right
  have hp : (⋃ σ : Set (F : Set E), B ∩ P σ)=B := by
    rw [←Set.inter_iUnion,iUnion_finiteBondPattern,Set.inter_univ]
  calc
    _ ≤ ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*∑' σ : Set (F : Set E), law p (A σ) :=
      mul_le_mul' le_rfl (measure_iUnion_le A)
    _ = ∑' σ : Set (F : Set E), law p (A σ)*ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) := by
      rw [ENNReal.tsum_mul_right,mul_comm]
    _ ≤ ∑' σ : Set (F : Set E), law p (B ∩ P σ) := ENNReal.tsum_le_tsum hcell
    _ = _ := by rw [←measure_iUnion hd (fun σ => hB.inter (measurableSet_finiteBondPattern F _)),hp]

theorem finite_energy_modification_bound (p : unitInterval) (F : Finset E)
    (A B : Set (Set E)) (hB : MeasurableSet B)
    (hmod : ∀ ω ∈ A, ∃ η ∈ B, ∀ e ∉ F, (e ∈ ω)=(e ∈ η)) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*law p A ≤ law p B := by
  apply (mul_le_mul' le_rfl (measure_mono ?_)).trans (finiteModification_probability p F B hB)
  intro ω hω
  obtain ⟨η,hη,hagree⟩ := hmod ω hω
  let σ : Set (F : Set E) := Subtype.val ⁻¹' η
  refine Set.mem_iUnion.mpr ⟨σ,?_⟩
  have hh : forceOn (F : Set E) (Subtype.val '' σ) ω=η := by
    ext e
    rw [mem_forceOn]
    by_cases he : e ∈ (F : Set E)
    · simp only [he,if_true,Set.mem_image]
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact hz
      · intro heη
        exact ⟨⟨e,he⟩,heη,rfl⟩
    · simpa only [he,if_false] using Iff.of_eq (hagree e he)
  change forceOn (F : Set E) (Subtype.val '' σ) ω ∈ B
  rw [hh]
  exact hη

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_HalfspaceRootComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma walk_finite_open_restriction {x y : V} (w : (openSimpleGraph G Set.univ).Walk x y)
    (D : Set V) (hD : ∀ v ∈ w.support, v ∈ D) :
    ∃ s : Finset E, s.card ≤ w.length ∧ ∀ ω : Set E, (s : Set E) ⊆ ω →
      Conn G (ω ∩ internalEdges G D) x y := by
  obtain ⟨l,hl,he,_ho⟩ := walk_lift_bonds G Set.univ w
  have hlen : l.length = w.length := by
    simpa only [List.length_map,SimpleGraph.Walk.length_edges] using congrArg List.length he
  refine ⟨l.toFinset,(List.toFinset_card_le l).trans_eq hlen,fun ω hω => ?_⟩
  apply hl.conn
  intro e he'
  refine ⟨hω (List.mem_toFinset.mpr he'),?_⟩
  intro v hv
  exact hD v (SimpleGraph.Walk.mem_support_of_mem_edges (he ▸ List.mem_map_of_mem he') hv)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FiniteEnergyObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct

variable {E : Type*} [Countable E]

lemma finite_forcing_measure_bound (p : unitInterval) (F : Finset E) (σ : Set E) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) •
      (law p).map (forceOn (F : Set E) σ) ≤ law p := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.smul_apply,Measure.map_apply (measurable_forceOn _ _) hB,smul_eq_mul]
  apply finite_energy_modification_bound p F _ B hB
  intro ω hω
  refine ⟨forceOn (F : Set E) σ ω,hω,?_⟩
  intro e he
  rw [mem_forceOn]
  simp only [Finset.mem_coe,he,if_false]

lemma lintegral_finite_forcing_bound (p : unitInterval) (F : Finset E) (σ : Set E)
    (X : Set E → ℝ≥0∞) (hX : Measurable X) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*
      (∫⁻ ω, X (forceOn (F : Set E) σ ω) ∂law p) ≤ ∫⁻ ω, X ω ∂law p := by
  have hh := lintegral_mono' (finite_forcing_measure_bound p F σ) (le_refl X)
  rwa [lintegral_smul_measure,lintegral_map hX (measurable_forceOn _ _),smul_eq_mul] at hh

variable {V : Type*} [Countable V] (G : BondGraph V E)

omit [Countable E] [Countable V] in
lemma rooted_forced_layer_count_le (F : Finset E) (I J : Set E) (W Z : Set V)
    (hIJ : I ⊆ J) (hWZ : W ⊆ Z) (x y : V)
    (hpath : ∀ η : Set E, (F : Set E) ⊆ η → Conn G (η ∩ J) x y)
    (ω : Set E) :
    restrictedLayerCount G I W ω y ≤
      restrictedLayerCount G J Z (forceOn (F : Set E) Set.univ ω) x := by
  let η := forceOn (F : Set E) Set.univ ω
  have hωη : ω ⊆ η := by
    intro e he
    rw [mem_forceOn]
    by_cases heF : e ∈ (F : Set E)
    · simp only [heF,if_true,Set.mem_univ]
    · simpa only [heF,if_false] using he
  have hFη : (F : Set E) ⊆ η := by
    intro e he
    rw [mem_forceOn,ite_eq_left he]
    exact Set.mem_univ e
  have hxy := hpath η hFη
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ W ∧ Conn G (ω ∩ I) y z
  · have hconn := hxy.trans (conn_mono G (Set.inter_subset_inter hωη hIJ) hz.2)
    have ht : z ∈ Z ∧ Conn G (η ∩ J) x z := ⟨hWZ hz.1,hconn⟩
    rw [ite_eq_left hz,ite_eq_left ht]
  · rw [ite_eq_right hz]
    exact bot_le

theorem forced_path_fractional_layer_comparison
    (p : unitInterval) (F : Finset E) (I J : Set E) (W Z : Set V)
    (hIJ : I ⊆ J) (hWZ : W ⊆ Z) (x y : V)
    (hpath : ∀ η : Set E, (F : Set E) ⊆ η → Conn G (η ∩ J) x y)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*
      (∫⁻ ω, (restrictedLayerCount G I W ω y)^q ∂law p) ≤
        ∫⁻ ω, (restrictedLayerCount G J Z ω x)^q ∂law p := by
  apply (mul_le_mul' le_rfl (lintegral_mono (fun ω =>
    ENNReal.rpow_le_rpow (rooted_forced_layer_count_le G F I J W Z hIJ hWZ x y hpath ω) hq))).trans
  exact lintegral_finite_forcing_bound p F Set.univ _
    ((measurable_restrictedLayerCount G J Z x).pow_const q)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FirstHeightPeakWalk
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V : Type*} {H : SimpleGraph V}

lemma first_height_peak_walk (f : V → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ {u v}, H.Adj u v → |f v-f u| ≤ R)
    {x y : V} (p : H.Walk x y) (a b : ℝ)
    (ha : a ≤ f x) (hb : f x ≤ b) (hend : b ≤ f y)
    (hlow : ∀ z ∈ p.support, a ≤ f z) :
    ∃ z, ∃ q : H.Walk x z, q.length ≤ p.length ∧
      b ≤ f z ∧ f z ≤ b+R ∧ ∀ v ∈ q.support, a ≤ f v ∧ f v ≤ f z := by
  induction p with
  | @nil u =>
    refine ⟨u,.nil,le_rfl,hend,by linarith,?_⟩
    intro v hv
    have hv' : v=u := List.mem_singleton.mp hv
    subst v
    exact ⟨ha,le_rfl⟩
  | @cons x v y huv p ih =>
    by_cases hx : b ≤ f x
    · refine ⟨x,.nil,Nat.zero_le _,hx,by linarith,?_⟩
      intro z hz
      have hz' : z=x := List.mem_singleton.mp hz
      subst z
      exact ⟨ha,le_rfl⟩
    have hav : a ≤ f v := hlow v (by simp)
    by_cases hv : b ≤ f v
    · have hvu := (abs_le.mp (hjump huv)).2
      refine ⟨v,.cons huv .nil,by simp,hv,by linarith,?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
        List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨ha,by linarith⟩
      · exact ⟨hav,le_rfl⟩
    · obtain ⟨z,q,hq,hz,hzR,hbound⟩ := ih hav (le_of_not_ge hv) hend
        (fun z hz => hlow z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz))
      refine ⟨z,.cons huv q,Nat.succ_le_succ hq,hz,hzR,?_⟩
      intro w hw
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨ha,by linarith⟩
      · exact hbound w hw

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_bounded_ascent_to_level
    [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ c : ℝ, 0 ≤ c → ∀ x,
      ∃ y, ∃ w : G.fullGraph.Walk x y, (w.length : ℝ) ≤ A*c+B ∧
        c ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ c+R ∧
        ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤
            G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_ascent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  refine ⟨(L : ℝ)/ε+1,L,by positivity,Nat.cast_nonneg _,fun c hc0 x => ?_⟩
  let n := ⌈c/ε⌉₊
  have hn : c ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil (c/ε))
  have hn' : (n : ℝ) ≤ c/ε+1 := (Nat.ceil_lt_add_one (div_nonneg hc0 hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_ascent_iterate hc hl a ε hε.le L hstep n x
  have hj : ∀ {u v}, G.fullGraph.Adj u v →
      |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
    intro u v huv
    have huv' : (Percolation.openSimpleGraph G.ends Set.univ).Adj u v := by
      rw [←criticalModel_openGraph G.ends Set.univ]
      exact huv
    obtain ⟨e,_he,he⟩ := huv'.2
    have hv := hjump e u v (by rw [he]; simp) (by rw [he]; simp)
    rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
    simpa only [add_sub_cancel_left] using hv
  obtain ⟨z,q,hq,hz,hzR,hbound⟩ := first_height_peak_walk
    (G.orbitAdjustedHeight a x) R hR hj w 0 c (by simp) (by simpa using hc0) (hn.trans hwy) hw
  refine ⟨z,q,?_,hz,hzR,hbound⟩
  have hqn : q.length ≤ n*L := hq.trans hwlen
  have hqn' : (q.length : ℝ) ≤ (n : ℝ)*L := by exact_mod_cast hqn
  have hm := mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  calc
    _ ≤ (n : ℝ)*L := hqn'
    _ ≤ (c/ε+1)*L := hm
    _ = ((L : ℝ)/ε+1)*c+L-c := by ring
    _ ≤ ((L : ℝ)/ε+1)*c+L := by linarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FractionalHolder
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

lemma fractional_holder_with_count
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Ω → ℝ≥0∞) (hA : Measurable A) (hB : Measurable B)
    (hBfin : ∀ᵐ ω ∂μ, 1 ≤ B ω ∧ B ω ≠ ⊤)
    {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hδ : 0 ≤ δ) (hδa : δ ≤ 1-a) :
    (∫⁻ ω, A ω^a ∂μ) ≤
      (∫⁻ ω, A ω*B ω^(-δ) ∂μ)^a * (∫⁻ ω, B ω^a ∂μ)^δ := by
  by_cases hδ0 : δ=0
  · simpa only [hδ0,neg_zero,ENNReal.rpow_zero,mul_one] using
      ennreal_lintegral_rpow_le_rpow_lintegral μ A hA ha ha1.le
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  have hc : (1/a).HolderConjugate (1/(1-a)) :=
    Real.holderConjugate_one_div ha (sub_pos.mpr ha1) (by ring)
  have hcancel : a*(1/a)=1 := by field_simp
  have hinva : 1/(1/a)=a := by field_simp
  have hinvb : 1/(1/(1-a))=1-a := by field_simp
  have hfactor : (fun ω => A ω^a) =ᵐ[μ]
      (fun ω => (A ω*B ω^(-δ))^a * B ω^(a*δ)) := by
    filter_upwards [hBfin] with ω hω
    have hne : B ω ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hω.1)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le,←ENNReal.rpow_mul,mul_assoc,
      ←ENNReal.rpow_add _ _ hne hω.2,
      show -δ*a+a*δ=0 by ring,ENNReal.rpow_zero,mul_one]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
    (((hA.mul (hB.pow_const (-δ))).pow_const a).aemeasurable)
      ((hB.pow_const (a*δ)).aemeasurable)
  simp only [Pi.mul_apply,←ENNReal.rpow_mul,hcancel,ENNReal.rpow_one,hinva,hinvb] at hh
  have hb : 0 < δ/(1-a) := div_pos hδpos (sub_pos.mpr ha1)
  have hb1 : δ/(1-a) ≤ 1 := (div_le_one (sub_pos.mpr ha1)).mpr hδa
  have hj := ennreal_lintegral_rpow_le_rpow_lintegral μ (fun ω => B ω^a)
    (hB.pow_const a) hb hb1
  have he : a*δ*(1/(1-a))=a*(δ/(1-a)) := by ring
  have he' : δ/(1-a)*(1-a)=δ := by field_simp [ne_of_gt (sub_pos.mpr ha1)]
  calc
    _ = ∫⁻ ω, (A ω*B ω^(-δ))^a*B ω^(a*δ) ∂μ := lintegral_congr_ae hfactor
    _ ≤ (∫⁻ ω, A ω*B ω^(-δ) ∂μ)^a *
        (∫⁻ ω, B ω^(a*δ*(1/(1-a))) ∂μ)^(1-a) := hh
    _ ≤ (∫⁻ ω, A ω*B ω^(-δ) ∂μ)^a *
        ((∫⁻ ω, B ω^a ∂μ)^(δ/(1-a)))^(1-a) := by
      apply mul_le_mul' le_rfl
      apply ENNReal.rpow_le_rpow _ (sub_nonneg.mpr ha1.le)
      simpa only [←ENNReal.rpow_mul,he] using hj
    _ = _ := by rw [←ENNReal.rpow_mul,he']

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FractionalBandTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_mul_negative_rpow_le (X : ℝ≥0∞) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) : X*X^(-δ) ≤ X^(1-δ) := by
  by_cases hzero : X=0
  · simp only [hzero,zero_mul,ENNReal.zero_rpow_of_pos (sub_pos.mpr hδ1),le_refl]
  by_cases htop : X=⊤
  · subst X
    by_cases hδ0 : δ=0
    · simp [hδ0]
    · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
      rw [ENNReal.top_rpow_of_neg (neg_neg_of_pos hδpos),mul_zero]
      exact bot_le
  apply le_of_eq
  calc
    _ = X^(1 : ℝ)*X^(-δ) := congrArg (fun Y => Y*X^(-δ)) (ENNReal.rpow_one X).symm
    _ = _ := (ENNReal.rpow_add 1 (-δ) hzero htop).symm

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FractionalSlabGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedSlabBandCount_eq_restricted (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) :
    G.adjustedSlabBandCount a d c l u ω x = restrictedLayerCount G.ends
      (Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
      {z | l ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u} ω x := by
  apply tsum_congr
  intro y
  unfold adjustedSlabBandTransport
  by_cases hc : Percolation.Conn G.ends
      (ω ∩ Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) x y
  <;> by_cases hl : l ≤ G.orbitAdjustedHeight a x y
  <;> by_cases hu : G.orbitAdjustedHeight a x y ≤ u
  <;> simp [hc,hl,hu]

lemma adjusted_slab_connection_change_root
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (ω : Set E) (x y v w : V) (d c d' c' : ℝ)
    (hlo : d'+G.orbitAdjustedHeight a x y ≤ d)
    (hhi : c ≤ c'+G.orbitAdjustedHeight a x y)
    (hconn : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) v w) :
    Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d' ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ c'}) v w := by
  apply Percolation.conn_mono G.ends (Set.inter_subset_inter_right _
    (Percolation.internalEdges_mono G.ends ?_)) hconn
  intro z hz
  have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
  exact ⟨by linarith [hz.1],by linarith [hz.2]⟩

lemma reverse_slab_band_count_le_zero_band
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (d c l u : ℝ) (ω : Set E) (x y : V)
    (hxy : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d+(u-l) ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c-(u-l)}) x y)
    (hylo : l ≤ G.orbitAdjustedHeight a x y) (hyhi : G.orbitAdjustedHeight a x y ≤ u) :
    G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω y ≤
      G.adjustedSlabBandCount a d c (l-u) (u-l) ω x := by
  have hxy' := G.adjusted_slab_connection_change_root hc hl a ω x y x y
    (d+(u-l)) (c-(u-l)) (d-l) (c-u) (by linarith) (by linarith) hxy
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {v | d-l ≤ G.orbitAdjustedHeight a y v ∧ G.orbitAdjustedHeight a y v ≤ c-u}) y z ∧
      -u ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ -l
  · have hconn := G.adjusted_slab_connection_change_root hc hl a ω y x x z
      (d-l) (c-u) d c (by rw [G.orbitAdjustedHeight_reverse hc hl a x y]; linarith)
        (by rw [G.orbitAdjustedHeight_reverse hc hl a x y]; linarith) (hxy'.trans hz.1)
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
    have ht : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | d ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ c}) x z ∧
        l-u ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ u-l :=
      ⟨hconn,by linarith [hz.2.1],by linarith [hz.2.2]⟩
    simp only [adjustedSlabBandTransport,ite_eq_left hz,ite_eq_left ht,le_refl]
  · simp only [adjustedSlabBandTransport,ite_eq_right hz]
    exact bot_le

lemma fractionalReverseSlabTransport_incoming_lower
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (d c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ω : Set E) (x y : V) :
    ENNReal.ofReal (Real.exp l)*
      (G.adjustedSlabBandTransport a (d+(u-l)) (c-(u-l)) l u ω x y *
        (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ)) ≤
      G.fractionalReverseSlabTransport a d c l u δ ω y x *
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
  by_cases hxy : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
      {z | d+(u-l) ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c-(u-l)}) x y ∧
      l ≤ G.orbitAdjustedHeight a x y ∧ G.orbitAdjustedHeight a x y ≤ u
  · have hrev : Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {z | d-l ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ c-u}) y x ∧
        -u ≤ G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ -l := by
      rw [G.orbitAdjustedHeight_reverse hc hl a x y]
      exact ⟨Percolation.conn_symm G.ends _ (G.adjusted_slab_connection_change_root hc hl a ω x y x y
        (d+(u-l)) (c-(u-l)) (d-l) (c-u) (by linarith [hxy.2.2])
          (by linarith [hxy.2.1]) hxy.1),by linarith [hxy.2.2],by linarith [hxy.2.1]⟩
    simp only [fractionalReverseSlabTransport,adjustedSlabBandTransport,
      ite_eq_left hxy,ite_eq_left hrev,one_mul]
    have hpow : (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ) ≤
        (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω y)^(-δ) := by
      simp only [ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
        (G.reverse_slab_band_count_le_zero_band hc hl a d c l u ω x y hxy.1 hxy.2.1 hxy.2.2) hδ)
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hxy.2.1)) hpow).trans_eq
      (mul_comm _ _)
  · simp only [adjustedSlabBandTransport,ite_eq_right hxy,zero_mul,mul_zero]
    exact bot_le

lemma adjustedSlabBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (d c l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.adjustedSlabBandTransport a d c l u (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.adjustedSlabBandTransport a d c l u ω x y := by
  have hD : φ.vertex ⁻¹' {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧
      G.orbitAdjustedHeight a (φ.vertex x) z ≤ c} =
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.orbitAdjustedHeight_aut a ha]
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a (φ.vertex x) z ∧ G.orbitAdjustedHeight a (φ.vertex x) z ≤ c}) =
      ω ∩ Percolation.internalEdges G.ends {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c} := by
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ←Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  unfold adjustedSlabBandTransport
  rw [←Percolation.conn_aut_iff G.ends φ.preserves,hmask,G.orbitAdjustedHeight_aut a ha]

lemma adjustedSlabBandCount_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (d c l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x : V) :
    G.adjustedSlabBandCount a d c l u (φ.edge '' ω) (φ.vertex x) =
      G.adjustedSlabBandCount a d c l u ω x := by
  unfold adjustedSlabBandCount
  rw [←φ.vertex.tsum_eq]
  simp only [G.adjustedSlabBandTransport_aut a ha]

variable [Countable V] [Countable E]

lemma measurable_adjustedSlabBandTransport (a : V → ℝ) (d c l u : ℝ) (x y : V) :
    Measurable (fun ω => G.adjustedSlabBandTransport a d c l u ω x y) := by
  have hm : Measurable (fun ω : Set E => ω ∩ Percolation.internalEdges G.ends
      {z | d ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.ite (((Percolation.measurableSet_conn G.ends x y).mem.comp hm).and
    measurable_const).setOf measurable_const measurable_const

lemma measurable_adjustedSlabBandCount (a : V → ℝ) (d c l u : ℝ) (x : V) :
    Measurable (fun ω => G.adjustedSlabBandCount a d c l u ω x) :=
  Measurable.tsum fun y => G.measurable_adjustedSlabBandTransport a d c l u x y

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FractionalSlabTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma fractionalReverseSlabTransport_outgoing (a : V → ℝ) (d c l u : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (ω : Set E) (x : V) :
    (∑' y, G.fractionalReverseSlabTransport a d c l u δ ω x y) ≤
      (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω x)^(1-δ) := by
  unfold fractionalReverseSlabTransport
  rw [ENNReal.tsum_mul_right]
  exact ennreal_mul_negative_rpow_le _ hδ hδ1

lemma fractionalReverseSlabTransport_incoming_sum
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (d c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ω : Set E) (x : V) :
    ENNReal.ofReal (Real.exp l)*
      (G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x *
        (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ)) ≤
      ∑' y, G.fractionalReverseSlabTransport a d c l u δ ω y x *
        ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) := by
  rw [adjustedSlabBandCount,←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun y =>
    G.fractionalReverseSlabTransport_incoming_lower hc hl a d c l u hδ ω x y

variable [Countable V] [Countable E]

lemma measurable_fractionalReverseSlabTransport (a : V → ℝ) (d c l u δ : ℝ) (x y : V) :
    Measurable (fun ω => G.fractionalReverseSlabTransport a d c l u δ ω x y) :=
  (G.measurable_adjustedSlabBandTransport a _ _ _ _ x y).mul
    ((G.measurable_adjustedSlabBandCount a _ _ _ _ x).pow_const (-δ))

omit [Countable V] [Countable E] in
lemma fractionalReverseSlabTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (d c l u δ : ℝ)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.fractionalReverseSlabTransport a d c l u δ (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.fractionalReverseSlabTransport a d c l u δ ω x y := by
  simp only [fractionalReverseSlabTransport,G.adjustedSlabBandTransport_aut a ha,
    G.adjustedSlabBandCount_aut a ha]

theorem expected_fractional_slab_transport
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (p : unitInterval) (d c l u : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
      G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x *
        (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ) ∂G.law p)) ≤
      ENNReal.ofReal (Real.exp (-l)) *
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω x)^(1-δ) ∂G.law p)) := by
  let B (ω : Set E) (x : V) := G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x *
    (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ)
  have he := OrbitRepresentatives.random_normalized_tilted_transport G O hc hl a hapos ha p
    (G.fractionalReverseSlabTransport a d c l u δ)
    (G.measurable_fractionalReverseSlabTransport a d c l u δ)
    (G.fractionalReverseSlabTransport_aut a ha d c l u δ)
  have hw : ENNReal.ofReal (Real.exp l)*
      (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, B ω x ∂G.law p)) ≤
      ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
        (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω x)^(1-δ) ∂G.law p) := by
    calc
      _ ≤ ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          ∑' y, G.fractionalReverseSlabTransport a d c l u δ ω y x *
            ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a x y)) ∂G.law p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        calc
          _ = ENNReal.ofReal (a x)*(∫⁻ ω, ENNReal.ofReal (Real.exp l)*B ω x ∂G.law p) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            ring
          _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono
            (G.fractionalReverseSlabTransport_incoming_sum hc hl a d c l u hδ · x))
      _ = ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
          ∑' y, G.fractionalReverseSlabTransport a d c l u δ ω x y ∂G.law p) := he.symm
      _ ≤ _ := Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl
        (lintegral_mono (G.fractionalReverseSlabTransport_outgoing a d c l u hδ hδ1 · x))
  calc
    _ = ENNReal.ofReal (Real.exp (-l))*(ENNReal.ofReal (Real.exp l)*
        (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, B ω x ∂G.law p))) := by
      rw [←mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add,
        neg_add_cancel,Real.exp_zero,ENNReal.ofReal_one,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hw

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FractionalSlabEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma expected_slab_band_product_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (d c l u δ : ℝ)
    (φ : G.Aut) (p : unitInterval) (x : V) :
    (∫⁻ ω, G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω (φ.vertex x) *
      (G.adjustedSlabBandCount a d c (l-u) (u-l) ω (φ.vertex x))^(-δ) ∂G.law p) =
    ∫⁻ ω, G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x *
      (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^(-δ) ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  have hm : Measurable (fun ω : Set E =>
      G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω (φ.vertex x) *
        (G.adjustedSlabBandCount a d c (l-u) (u-l) ω (φ.vertex x))^(-δ)) :=
    (G.measurable_adjustedSlabBandCount a _ _ _ _ _).mul
      ((G.measurable_adjustedSlabBandCount a _ _ _ _ _).pow_const (-δ))
  rw [lintegral_map hm
      (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [G.adjustedSlabBandCount_aut a ha]

theorem fractional_slab_band_estimate
    (O : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (m : ℝ) (hm : 0 < m) (ham : ∀ x, m ≤ a x)
    (p : unitInterval) (d c l u : ℝ) (x : V)
    {α δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hδ : 0 ≤ δ) (hδα : δ ≤ 1-α)
    (hZfin : ∀ᵐ ω ∂G.law p,
      1 ≤ G.adjustedSlabBandCount a d c (l-u) (u-l) ω x ∧
        G.adjustedSlabBandCount a d c (l-u) (u-l) ω x ≠ ⊤)
    (L Q : ℝ≥0∞)
    (hL : (∫⁻ ω, (G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)^α ∂G.law p) ≤ L)
    (hQ : ∀ r ∈ O.roots, (∫⁻ ω,
      (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω r)^(1-δ) ∂G.law p) ≤ Q) :
    (∫⁻ ω, (G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x)^α ∂G.law p) ≤
      (((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-l))*
        (∑ r ∈ O.roots, ENNReal.ofReal (a r)))*Q)^α * L^δ := by
  let B (ω : Set E) (z : V) := G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω z *
    (G.adjustedSlabBandCount a d c (l-u) (u-l) ω z)^(-δ)
  have hroot : ENNReal.ofReal m*(∫⁻ ω, B ω x ∂G.law p) ≤
      ∑ r ∈ O.roots, ENNReal.ofReal (a r)*(∫⁻ ω, B ω r ∂G.law p) := by
    obtain ⟨r,hr,φ,rfl⟩ := O.cover x
    change ENNReal.ofReal m*(∫⁻ ω,
      G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω (φ.vertex r) *
        (G.adjustedSlabBandCount a d c (l-u) (u-l) ω (φ.vertex r))^(-δ) ∂G.law p) ≤ _
    rw [G.expected_slab_band_product_aut a ha d c l u δ φ p r]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (ham r)) le_rfl).trans
      (Finset.single_le_sum (f := fun r => ENNReal.ofReal (a r)*(∫⁻ ω, B ω r ∂G.law p))
        (fun _ _ => bot_le) hr)
  have hδ1 : δ < 1 := by linarith
  have hprod : (∫⁻ ω, B ω x ∂G.law p) ≤
      ((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-l))*
        (∑ r ∈ O.roots, ENNReal.ofReal (a r)))*Q := by
    have hqsum : (∑ r ∈ O.roots, ENNReal.ofReal (a r)*(∫⁻ ω,
        (G.adjustedSlabBandCount a (d-l) (c-u) (-u) (-l) ω r)^(1-δ) ∂G.law p)) ≤
        (∑ r ∈ O.roots, ENNReal.ofReal (a r))*Q := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun r hr => mul_le_mul' le_rfl (hQ r hr)
    have hh := hroot.trans ((G.expected_fractional_slab_transport O hc hl a hapos ha p d c l u hδ hδ1).trans
      (mul_le_mul' le_rfl hqsum))
    calc
      _ = (ENNReal.ofReal m)⁻¹*(ENNReal.ofReal m*(∫⁻ ω, B ω x ∂G.law p)) := by
        rw [←mul_assoc,ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hm))
          ENNReal.ofReal_ne_top,one_mul]
      _ ≤ _ := (mul_le_mul' le_rfl hh).trans_eq (by ring)
  exact (fractional_holder_with_count (G.law p)
    (fun ω => G.adjustedSlabBandCount a (d+(u-l)) (c-(u-l)) l u ω x)
    (fun ω => G.adjustedSlabBandCount a d c (l-u) (u-l) ω x)
    (G.measurable_adjustedSlabBandCount a _ _ _ _ x)
    (G.measurable_adjustedSlabBandCount a _ _ _ _ x) hZfin hα hα1 hδ hδα).trans
      (mul_le_mul' (ENNReal.rpow_le_rpow hprod hα.le) (ENNReal.rpow_le_rpow hL hδ))

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedLayerCount_eq_card (I : Set E) (A : Set V) (ω : Set E) (x : V)
    (F : Finset V) (hF : ∀ y, y ∈ F ↔ y ∈ A ∧ Conn G (ω ∩ I) x y) :
    restrictedLayerCount G I A ω x = F.card := by
  unfold restrictedLayerCount
  rw [tsum_eq_sum (s := F) (fun y hy => ite_eq_right (fun hh => hy ((hF y).mpr hh)))]
  calc
    _ = ∑ _y ∈ F, (1 : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun y hy => ite_eq_left ((hF y).mp hy))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabCountBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedLayerCount_zero_or_one_le (I : Set E) (W : Set V) (ω : Set E) (x : V) :
    restrictedLayerCount G I W ω x=0 ∨ 1 ≤ restrictedLayerCount G I W ω x := by
  by_cases hex : ∃ y, y ∈ W ∧ Conn G (ω ∩ I) x y
  · obtain ⟨y,hy⟩ := hex
    apply Or.inr
    unfold restrictedLayerCount
    exact ((show (1 : ℝ≥0∞)=(if y ∈ W ∧ Conn G (ω ∩ I) x y then 1 else 0) from
      (ite_eq_left hy).symm).le.trans (ENNReal.le_tsum
        (f := fun z => if z ∈ W ∧ Conn G (ω ∩ I) x z then 1 else 0) y))
  · exact Or.inl (ENNReal.tsum_eq_zero.mpr fun y => ite_eq_right (fun h => hex ⟨y,h⟩))

lemma restrictedLayerCount_lt_top_of_finite (I : Set E) (W : Set V) (ω : Set E) (x : V)
    (hfin : (cluster G ω x).Finite) : restrictedLayerCount G I W ω x < ⊤ := by
  have hIF : (cluster G (ω ∩ I) x ∩ W).Finite :=
    (hfin.subset fun z hz => conn_mono G Set.inter_subset_left hz.1)
  let S := hIF.toFinset
  have he : restrictedLayerCount G I W ω x=S.card :=
    restrictedLayerCount_eq_card G I W ω x S (fun y => by
      simp only [S,hIF.mem_toFinset,Set.mem_inter_iff]
      exact and_comm)
  rw [he]
  exact ENNReal.natCast_lt_top _

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma adjustedSlabBandCount_rpow_mono_exponent (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) {q q' : ℝ} (hq : 0 < q) (hqq' : q ≤ q') :
    (G.adjustedSlabBandCount a d c l u ω x)^q ≤
      (G.adjustedSlabBandCount a d c l u ω x)^q' := by
  simp only [G.adjustedSlabBandCount_eq_restricted]
  rcases restrictedLayerCount_zero_or_one_le G.ends _ _ ω x with hz | ho
  · rw [hz,ENNReal.zero_rpow_of_pos hq,ENNReal.zero_rpow_of_pos (hq.trans_le hqq')]
  · exact ENNReal.rpow_le_rpow_of_exponent_le ho hqq'

lemma one_le_adjustedSlabZeroBandCount (a : V → ℝ) (d c B : ℝ)
    (hB : 0 ≤ B) (ω : Set E) (x : V) :
    1 ≤ G.adjustedSlabBandCount a d c (-B) B ω x := by
  apply le_trans _ (ENNReal.le_tsum x)
  unfold adjustedSlabBandTransport
  rw [ite_eq_left]
  exact ⟨Percolation.conn_refl G.ends _ x,by simpa using neg_nonpos.mpr hB,by simpa using hB⟩

lemma adjustedSlabBandCount_lt_top_of_finite (a : V → ℝ) (d c l u : ℝ)
    (ω : Set E) (x : V) (hfin : (Percolation.cluster G.ends ω x).Finite) :
    G.adjustedSlabBandCount a d c l u ω x < ⊤ := by
  rw [G.adjustedSlabBandCount_eq_restricted]
  exact restrictedLayerCount_lt_top_of_finite G.ends _ _ ω x hfin

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabRootShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem fractional_slab_root_ascent
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (p : unitInterval) (k r c B : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r)
    {x y : V} (w : G.fullGraph.Walk x y)
    (hcy : c ≤ G.orbitAdjustedHeight a x y)
    (hw : ∀ v ∈ w.support, 0 ≤ G.orbitAdjustedHeight a x v ∧
      G.orbitAdjustedHeight a x v ≤ G.orbitAdjustedHeight a x y)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length)*
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {z | -k-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c})
        {z | -k-B ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -k+B} ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {z | -(k+G.orbitAdjustedHeight a x y)-r ≤ G.orbitAdjustedHeight a y z ∧
          G.orbitAdjustedHeight a y z ≤ 0})
        {z | -(k+G.orbitAdjustedHeight a x y)-B ≤ G.orbitAdjustedHeight a y z ∧
          G.orbitAdjustedHeight a y z ≤ -(k+G.orbitAdjustedHeight a x y)+B} ω y)^q ∂G.law p := by
  let h := G.orbitAdjustedHeight a x y
  let I := Percolation.internalEdges G.ends {z | -k-r ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ c}
  let J := Percolation.internalEdges G.ends {z | -(k+h)-r ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ 0}
  let W : Set V := {z | -k-B ≤ G.orbitAdjustedHeight a x z ∧ G.orbitAdjustedHeight a x z ≤ -k+B}
  let Z : Set V := {z | -(k+h)-B ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ -(k+h)+B}
  have hIJ : I ⊆ J := Percolation.internalEdges_mono G.ends (by
    intro z hz
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
    exact ⟨by dsimp [h]; linarith [hz.1],by linarith [hz.2]⟩)
  have hWZ : W ⊆ Z := by
    intro z hz
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
    exact ⟨by dsimp [h]; linarith [hz.1],by dsimp [h]; linarith [hz.2]⟩
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by
      rw [←criticalModel_openGraph G.ends Set.univ]
      exact h⟩
  obtain ⟨F,hF,hconn⟩ := walk_finite_open_restriction G.ends (w.reverse.map f)
    {z | -(k+h)-r ≤ G.orbitAdjustedHeight a y z ∧ G.orbitAdjustedHeight a y z ≤ 0} (by
      intro z hz
      have hz' : z ∈ w.support := by
        rw [SimpleGraph.Walk.support_map] at hz
        change z ∈ w.reverse.support.map id at hz
        simpa only [List.map_id_fun,id_eq,SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
      have hh := G.orbitAdjustedHeight_change_base hc hl a x y z
      exact ⟨by dsimp [h]; linarith [(hw z hz').1],by linarith [(hw z hz').2]⟩)
  have hlen : F.card ≤ w.length := by
    simpa only [SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_reverse] using hF
  have hcost : ENNReal.ofReal ((min (p : ℝ) (1-p))^w.length) ≤
      ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) := by
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_of_le_one (le_min p.2.1 (sub_nonneg.mpr p.2.2))
      ((min_le_left _ _).trans p.2.2) hlen
  exact (mul_le_mul' hcost le_rfl).trans
    (forced_path_fractional_layer_comparison G.ends p F I J W Z hIJ hWZ y x hconn hq)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SlabFractionalProfileShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma finite_energy_cancel_length (X Y : ℝ≥0∞) (δ A B c : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlen : (N : ℝ) ≤ A*c+B)
    (hXY : ENNReal.ofReal (δ^N)*X ≤ Y) :
    X ≤ ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)))*Y := by
  have he : Real.exp (-Real.log δ*(N : ℝ))*δ^N=1 := by
    rw [←Real.exp_log hδ,←Real.exp_nat_mul,←Real.exp_add,Real.log_exp]
    rw [show -Real.log δ*(N : ℝ)+(N : ℝ)*Real.log δ=0 by ring,Real.exp_zero]
  have hc : ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*ENNReal.ofReal (δ^N)=1 := by
    rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),he,ENNReal.ofReal_one]
  have hs : 0 ≤ -Real.log δ := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  calc
    _ = ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*(ENNReal.ofReal (δ^N)*X) := by
      rw [←mul_assoc,hc,one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-Real.log δ*(N : ℝ)))*Y := mul_le_mul' le_rfl hXY
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hlen hs))) le_rfl

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem finite_ceiling_fractional_profile [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (L : ℝ) (hprofile : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p R L) :
    ∃ T : ℝ, 0 < T ∧ ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ c : ℝ, 0 ≤ c → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount (G.stationaryOrbitWeight μ) (-k-r) c (-k-R) (-k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp (ζ*k+L*r+T*c)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpaths⟩ := G.stationaryOrbitHeight_bounded_ascent_to_level
    hc hl hq μ hμ hstat hu R hR.le hjump
  let δ := min (p : ℝ) (1-p)
  have hδ : 0 < δ := lt_min hp0 (sub_pos.mpr hp1)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans p.2.2
  let s := -Real.log δ
  have hs : 0 ≤ s := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  let T := s*A+1
  refine ⟨T,by dsimp [T]; positivity,fun q hq0 hq1 ζ hζ hζ1 => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hprofile q hq0 hq1 ζ hζ
  refine ⟨C*ENNReal.ofReal (Real.exp (s*B+R)),ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top,
    fun k hk r hr c hc0 x => ?_⟩
  obtain ⟨y,w,hlen,hcy,hyc,hw⟩ := hpaths c hc0 x
  have hXY := G.fractional_slab_root_ascent hc hl a p k r c R hk hr w hcy hw hq0.le
  simp_rw [←G.adjustedSlabBandCount_eq_restricted] at hXY
  have hh := finite_energy_cancel_length _ _ δ A B c w.length hδ hδ1 hlen hXY
  have hlevel : 0 ≤ k+G.orbitAdjustedHeight a x y := add_nonneg hk (hc0.trans hcy)
  have hb := hbound (k+G.orbitAdjustedHeight a x y) hlevel r hr y
  apply hh.trans ((mul_le_mul' le_rfl hb).trans ?_)
  have he : -Real.log δ*(A*c+B)+(ζ*(k+G.orbitAdjustedHeight a x y)+L*r) ≤
      (s*B+R)+(ζ*k+L*r+T*c) := by
    have hζh : ζ*G.orbitAdjustedHeight a x y ≤ G.orbitAdjustedHeight a x y :=
      mul_le_of_le_one_left (hc0.trans hcy) hζ1
    dsimp [s,T]
    nlinarith
  calc
    _ = C*ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)+(ζ*(k+G.orbitAdjustedHeight a x y)+L*r))) := by
      simp only [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ ≤ C*ENNReal.ofReal (Real.exp ((s*B+R)+(ζ*k+L*r+T*c))) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
    _ = _ := by
      rw [Real.exp_add (s*B+R) (ζ*k+L*r+T*c),
        ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TruncatedFractionalSummation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_exp_rpow (t a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (Real.exp t)^a=ENNReal.ofReal (Real.exp (t*a)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) ha,←Real.exp_mul]

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_UpwardFractionalSlabProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
lemma fractional_two_profile_product (A B : ℝ≥0∞) (t u v w k r a δ : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    (A*ENNReal.ofReal (Real.exp (t*k+u*r)))^a*
      (B*ENNReal.ofReal (Real.exp (v*k+w*r)))^δ =
      (A^a*B^δ)*ENNReal.ofReal (Real.exp ((a*t+δ*v)*k+(a*u+δ*w)*r)) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha,ENNReal.mul_rpow_of_nonneg _ _ hδ,
    ennreal_exp_rpow _ _ ha,ennreal_exp_rpow _ _ hδ]
  calc
    _ = (A^a*B^δ)*(ENNReal.ofReal (Real.exp ((t*k+u*r)*a))*
        ENNReal.ofReal (Real.exp ((v*k+w*r)*δ))) := by ac_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
      rw [show (t*k+u*r)*a+(v*k+w*r)*δ=(a*t+δ*v)*k+(a*u+δ*w)*r by ring]

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem upward_fractional_slab_profile_bs_oai [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (Percolation.cluster G.ends ω x).Finite)
    (L₁ L₂ : ℝ)
    (hprofile₁ : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p R L₁)
    (hprofile₂ : G.lowerSlabFractionalProfile (G.stationaryOrbitWeight μ) p (2*R) L₂) :
    ∃ U : ℝ, 0 < U ∧ ∀ q : ℝ, 0 < q → q < 1 → ∀ ζ : ℝ, 0 < ζ →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ r : ℝ, 0 ≤ r → ∀ x : V,
        (∫⁻ ω, (G.adjustedSlabBandCount (G.stationaryOrbitWeight μ) (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp ((-1+ζ)*k+U*r)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨T₁,hT₁,hshift₁⟩ := G.finite_ceiling_fractional_profile hc hl hq μ hμ hstat hu R hR hjump
    p hp0 hp1 L₁ hprofile₁
  have hjump₂ : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ 2*R := by
    intro e v w hv hw
    exact (hjump e v w hv hw).trans (by linarith)
  obtain ⟨T₂,hT₂,hshift₂⟩ := G.finite_ceiling_fractional_profile hc hl hq μ hμ hstat hu
    (2*R) (by positivity) hjump₂ p hp0 hp1 L₂ hprofile₂
  obtain ⟨m,M,hm,hbounds⟩ := G.stationaryOrbitWeight_uniform_bounds hc hl μ hμ
  let O := G.orbitRepresentatives hq
  let D := (ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))*ENNReal.ofReal (Real.exp R)
  have hD : D < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hm))
      (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top)) ENNReal.ofReal_lt_top
  let U := |L₁|+T₁+|L₂|+T₂+1
  refine ⟨U,by dsimp [U]; positivity,?_⟩
  intro q hq0 hq1 ζ hζ
  let η := min ((1-q)/2) (min (ζ/4) (1/4))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hηq : η ≤ (1-q)/2 := min_le_left _ _
  have hηζ : η ≤ ζ/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
  let q' := 1-η
  have hq'0 : 0 < q' := by dsimp [q']; linarith
  have hq'1 : q' < 1 := by dsimp [q']; linarith
  have hqq' : q ≤ q' := by dsimp [q']; linarith
  let δ := min ((1-q')/2) (ζ/(4*(T₂+1)))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hζ (by positivity))
  have hδq' : δ ≤ 1-q' := (min_le_left _ _).trans (by linarith)
  have hδ1 : δ < 1 := by linarith
  have hδT : δ*T₂ ≤ ζ/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*(T₂+1) by positivity)).mp (min_le_right ((1-q')/2) (ζ/(4*(T₂+1))))
    change δ*(4*(T₂+1)) ≤ ζ at hh
    nlinarith
  let ε := min (ζ/4) (1/2)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hεζ : ε ≤ ζ/4 := min_le_left _ _
  obtain ⟨C₁,hC₁,hbound₁⟩ := hshift₁ (1-δ) (by linarith) (by linarith) ε hε hε1
  obtain ⟨C₂,hC₂,hbound₂⟩ := hshift₂ q' hq'0 hq'1 ε hε hε1
  let Q := C₁*ENNReal.ofReal (Real.exp (L₁*R+T₁*R))
  let Z := C₂*ENNReal.ofReal (Real.exp (L₂*(2*R)+T₂*(2*R)))
  have hQ : Q < ⊤ := ENNReal.mul_lt_top hC₁ ENNReal.ofReal_lt_top
  have hZ : Z < ⊤ := ENNReal.mul_lt_top hC₂ ENNReal.ofReal_lt_top
  let A := D*Q
  have hA : A < ⊤ := ENNReal.mul_lt_top hD hQ
  let C := A^q'*Z^δ
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hq'0.le hA.ne) (ENNReal.rpow_lt_top_of_nonneg hδ.le hZ.ne)
  refine ⟨C,hC,fun k hk r hr x => ?_⟩
  have hzero : (∫⁻ ω, (G.adjustedSlabBandCount a (-r-2*R) (k+r+2*R) (-2*R) (2*R) ω x)^q' ∂G.law p) ≤
      Z*ENNReal.ofReal (Real.exp (T₂*k+(L₂+T₂)*r)) := by
    have hh := hbound₂ 0 (by norm_num) (r+2*R) (by positivity) (k+r+2*R) (by positivity) x
    simp only [neg_zero,zero_sub,zero_add,mul_zero] at hh
    rw [←neg_mul] at hh
    rw [show -(r+2*R)= -r-2*R by ring] at hh
    apply hh.trans_eq
    dsimp [Z]
    rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
    rw [show L₂*(r+2*R)+T₂*(k+r+2*R)=(L₂*(2*R)+T₂*(2*R))+(T₂*k+(L₂+T₂)*r) by ring]
  have hdown (y : V) : (∫⁻ ω, (G.adjustedSlabBandCount a (-k-r-R) (r+R) (-k-R) (-k+R) ω y)^(1-δ) ∂G.law p) ≤
      Q*ENNReal.ofReal (Real.exp (ε*k+(L₁+T₁)*r)) := by
    have hh := hbound₁ k hk (r+R) (by positivity) (r+R) (by positivity) y
    rw [show -k-(r+R)= -k-r-R by ring] at hh
    apply hh.trans_eq
    dsimp [Q]
    rw [mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
    rw [show ε*k+L₁*(r+R)+T₁*(r+R)=(L₁*R+T₁*R)+(ε*k+(L₁+T₁)*r) by ring]
  have hZfin : ∀ᵐ ω ∂G.law p,
      1 ≤ G.adjustedSlabBandCount a (-r-2*R) (k+r+2*R) (-2*R) (2*R) ω x ∧
      G.adjustedSlabBandCount a (-r-2*R) (k+r+2*R) (-2*R) (2*R) ω x ≠ ⊤ := by
    filter_upwards [hfin x] with ω hω
    exact ⟨by simpa only [neg_mul] using
      G.one_le_adjustedSlabZeroBandCount a (-r-2*R) (k+r+2*R) (2*R) (by positivity) ω x,
      (G.adjustedSlabBandCount_lt_top_of_finite a _ _ _ _ ω x hω).ne⟩
  have hwidth : (k+R)-(k-R)=2*R := by ring
  have hnegl : -(k-R)= -k+R := by ring
  have hnegu : -(k+R)= -k-R := by ring
  have hlow : -r-2*R- (k-R)= -k-r-R := by ring
  have hhigh : k+r+2*R-(k+R)=r+R := by ring
  have hfwlo : -r-2*R+2*R= -r := by ring
  have hfwup : k+r+2*R-2*R=k+r := by ring
  have hminus : (k-R)-(k+R)= -2*R := by ring
  have hh := G.fractional_slab_band_estimate O hc hl a (G.stationaryOrbitWeight_pos hc hl μ hμ)
    (G.stationaryOrbitWeight_aut μ) m hm (fun z => (hbounds z).1) p (-r-2*R) (k+r+2*R) (k-R) (k+R) x
    hq'0 hq'1 hδ.le hδq'
    (by simpa only [hminus,hwidth] using hZfin)
    (Z*ENNReal.ofReal (Real.exp (T₂*k+(L₂+T₂)*r))) (Q*ENNReal.ofReal (Real.exp (ε*k+(L₁+T₁)*r)))
    (by simpa only [hminus,hwidth] using hzero)
    (fun y _ => by simpa only [hlow,hhigh,hnegu,hnegl] using hdown y)
  simp only [hwidth,hfwlo,hfwup] at hh
  have hfactor : (((ENNReal.ofReal m)⁻¹*ENNReal.ofReal (Real.exp (-(k-R)))*
      (∑ r ∈ O.roots, ENNReal.ofReal (a r)))*(Q*ENNReal.ofReal (Real.exp (ε*k+(L₁+T₁)*r)))) =
        A*ENNReal.ofReal (Real.exp ((ε-1)*k+(L₁+T₁)*r)) := by
    dsimp [A,D]
    have he : Real.exp (-(k-R))*Real.exp (ε*k+(L₁+T₁)*r)=Real.exp R*Real.exp ((ε-1)*k+(L₁+T₁)*r) := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    calc
      _ = ((ENNReal.ofReal m)⁻¹*(∑ r ∈ O.roots, ENNReal.ofReal (a r))*Q)*
          (ENNReal.ofReal (Real.exp (-(k-R)))*ENNReal.ofReal (Real.exp (ε*k+(L₁+T₁)*r))) := by ac_rfl
      _ = _ := by
        rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),he,ENNReal.ofReal_mul (Real.exp_nonneg _)]
        ac_rfl
  rw [hfactor] at hh
  have heq : (A*ENNReal.ofReal (Real.exp ((ε-1)*k+(L₁+T₁)*r)))^q'*
      (Z*ENNReal.ofReal (Real.exp (T₂*k+(L₂+T₂)*r)))^δ =
      C*ENNReal.ofReal (Real.exp ((q'*(ε-1)+δ*T₂)*k+(q'*(L₁+T₁)+δ*(L₂+T₂))*r)) :=
    fractional_two_profile_product A Z (ε-1) (L₁+T₁) T₂ (L₂+T₂) k r q' δ hq'0.le hδ.le
  have hmono : (∫⁻ ω, (G.adjustedSlabBandCount a (-r) (k+r) (k-R) (k+R) ω x)^q ∂G.law p) ≤
      ∫⁻ ω, (G.adjustedSlabBandCount a (-r) (k+r) (k-R) (k+R) ω x)^q' ∂G.law p :=
    lintegral_mono (fun ω => G.adjustedSlabBandCount_rpow_mono_exponent a _ _ _ _ ω x hq0 hqq')
  apply (hmono.trans hh).trans
  rw [heq]
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hqε : q'*ε ≤ ε := mul_le_of_le_one_left hε.le hq'1.le
  have hrate : q'*(ε-1)+δ*T₂ ≤ -1+ζ := by dsimp [q'] at hqε ⊢; nlinarith
  have hcoef₁ : q'*(L₁+T₁) ≤ |L₁|+T₁ :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) le_rfl) hq'0.le).trans
      (mul_le_of_le_one_left (by positivity) hq'1.le)
  have hcoef₂ : δ*(L₂+T₂) ≤ |L₂|+T₂ :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) le_rfl) hδ.le).trans
      (mul_le_of_le_one_left (by positivity) hδ1.le)
  have hcoeff : q'*(L₁+T₁)+δ*(L₂+T₂) ≤ U := by dsimp [U]; linarith
  exact add_le_add (mul_le_mul_of_nonneg_right hrate hk) (mul_le_mul_of_nonneg_right hcoeff hr)

end CriticalPercolation.BondGraph

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.upward_fractional_slab_profile_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.upward_fractional_slab_profile_bs_oai.{u_1, u_2}
