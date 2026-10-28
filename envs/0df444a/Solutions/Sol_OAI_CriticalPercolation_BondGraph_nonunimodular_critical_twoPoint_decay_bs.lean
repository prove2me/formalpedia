-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.nonunimodular_critical_twoPoint_decay_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:11:17.836503+00:00
-- url     : https://prove2.me/submissions/b8a04479-de59-4191-a9d1-5f7f6a40e540

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_nonunimodular_critical_mass_finite_ae_bs

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem countable_vertices (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable V := by
  obtain ⟨o⟩ := hconnected.nonempty
  have hc : (⋃ n : ℕ, G.vertexBall o n).Countable :=
    Set.countable_iUnion fun n => (G.vertexBall_finite hlocal o n).countable
  have heq : (⋃ n : ℕ, G.vertexBall o n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n, hn⟩ := G.reachable_mem_vertexBall (hconnected o v)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

theorem countable_bonds (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable E := by
  let := G.countable_vertices hconnected hlocal
  have hc : (⋃ v : V, {e : E | v ∈ G.ends e}).Countable :=
    Set.countable_iUnion fun v => (hlocal v).countable
  have heq : (⋃ v : V, {e : E | v ∈ G.ends e}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    exact Set.mem_iUnion.mpr ⟨(G.ends e).out.1, Sym2.out_fst_mem _⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_TwoPoint
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule10
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

lemma hit_singleton_eq (o v : V) :
    G.hitEvent o {v} = {ω | (G.openGraph ω).Reachable o v} := by
  ext ω
  simp only [BondGraph.hitEvent,Set.mem_ofPred_eq,Set.inter_singleton_nonempty,BondGraph.cluster]

end CriticalPercolation.Sharpness
end
end CurrentModule10

end

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

lemma stabilizerWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight o x =
      G.stabilizerWeight o a * G.stabilizerWeight a x := by
  unfold stabilizerWeight
  rw [←ENNReal.ofReal_mul (G.modularRatio_pos hc hl a o).le]
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularSuperlevels
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma finite_clusterUpperSet_of_mass_ne_top {ω : Set E} {v : V}
    (hm : G.modularMass v (G.cluster ω v) ≠ ∞) : (G.clusterUpperSet ω v).Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm (ε := 1) one_ne_zero).subset
  intro x hx
  change 1 ≤ if x∈G.cluster ω v then G.stabilizerWeight v x else 0
  rw [ite_eq_left hx.1]
  exact hx.2

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_LightTwoPointDecay
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_upperEscapeEvent [Countable V] [Countable E] (v : V) (R : ℕ) :
    MeasurableSet (G.upperEscapeEvent v R) := by
  exact (Measurable.exists fun x =>
    ((G.measurable_reachable v x).and measurable_const).and measurable_const).setOf

lemma upperEscapeEvent_antitone (v : V) : Antitone (G.upperEscapeEvent v) := by
  rintro n m h ω ⟨x,hx,hh⟩
  exact ⟨x,hx,fun hn => hh (G.vertexBall_mono v h hn)⟩

lemma not_iInter_upperEscape_of_mass_finite (hc : G.fullGraph.Connected)
    {ω : Set E} {v : V} (hm : G.modularMass v (G.cluster ω v)≠∞) :
    ω∉⋂ R : ℕ, G.upperEscapeEvent v R := by
  obtain ⟨R,hR⟩ := G.finite_subset_vertexBall hc v (G.finite_clusterUpperSet_of_mass_ne_top hm)
  intro h
  obtain ⟨x,hx,hout⟩ := Set.mem_iInter.mp h R
  exact hout (hR hx)

lemma tendsto_upperEscape_zero [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (v : V)
    (hm : ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    Tendsto (fun R => (G.law p).real (G.upperEscapeEvent v R)) atTop (𝓝 0) := by
  have hz : G.law p (⋂ R : ℕ, G.upperEscapeEvent v R)=0 := by
    simpa only [not_not,Set.ofPred_mem_eq] using
      (ae_iff.mp (hm.mono (fun _ h => G.not_iInter_upperEscape_of_mass_finite hc h)))
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun R => (G.measurableSet_upperEscapeEvent v R).nullMeasurableSet)
    (G.upperEscapeEvent_antitone v) ⟨0,measure_ne_top _ _⟩
  rw [hz] at h
  have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  change Tendsto (fun R => (G.law p).real (G.upperEscapeEvent v R)) atTop
    (𝓝 ((0 : ℝ≥0∞).toReal)) at hh
  simpa only [ENNReal.toReal_zero] using hh

lemma Aut.upperEscapeEvent_preimage (φ : G.Aut) (v : V) (R : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.upperEscapeEvent (φ.vertex v) R =
      G.upperEscapeEvent v R := by
  ext ω
  change (∃ x, (_ ∧ _) ∧ _) ↔ (∃ x, (_ ∧ _) ∧ _)
  constructor
  · rintro ⟨x,hx,hout⟩
    obtain ⟨y,rfl⟩ := φ.vertex.surjective x
    refine ⟨y,⟨?_,?_⟩,?_⟩
    · exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mp hx.1
    · simpa only [φ.stabilizerWeight] using hx.2
    · exact fun hy => hout ((φ.vertexBall_mem G v y R).mpr hy)
  · rintro ⟨x,hx,hout⟩
    refine ⟨φ.vertex x,⟨?_,?_⟩,?_⟩
    · exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mpr hx.1
    · simpa only [φ.stabilizerWeight] using hx.2
    · exact fun hy => hout ((φ.vertexBall_mem G v x R).mp hy)

lemma Aut.upperEscapeEvent_real [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (v : V) (R : ℕ) :
    (G.law p).real (G.upperEscapeEvent (φ.vertex v) R) =
      (G.law p).real (G.upperEscapeEvent v R) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_upperEscapeEvent _ _),φ.upperEscapeEvent_preimage]

lemma uniform_upperEscape_small [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hq : G.QuasiTransitive) (p : unitInterval)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞)
    (ε : ℝ) (hε : 0<ε) :
    ∃ R : ℕ, ∀ v, (G.law p).real (G.upperEscapeEvent v R)<ε := by
  obtain ⟨S,hS,hcover⟩ := hq
  have he (s : V) : ∀ᶠ R in atTop, (G.law p).real (G.upperEscapeEvent s R)<ε :=
    (G.tendsto_upperEscape_zero hc p s (hm s)).eventually (gt_mem_nhds hε)
  have hh := hS.toFinset.eventually_all.mpr (fun s _ => he s)
  obtain ⟨R,hR⟩ := hh.exists
  refine ⟨R,fun v => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover v
  rw [φ.upperEscapeEvent_real]
  exact hR s (hS.mem_toFinset.mpr hs)

lemma stabilizerWeight_ge_one_either (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : 1≤G.stabilizerWeight x y ∨ 1≤G.stabilizerWeight y x := by
  by_cases hxy : 1≤G.stabilizerWeight x y
  · exact Or.inl hxy
  · apply Or.inr
    by_contra hyx
    have hprod := G.stabilizerWeight_change_base hc hl x y x
    rw [G.stabilizerWeight_self] at hprod
    have hh : (1 : ℝ≥0∞)<1 := calc
      1 = G.stabilizerWeight x y * G.stabilizerWeight y x := hprod
      _ ≤ G.stabilizerWeight x y * 1 := by
        gcongr
        exact le_of_not_ge hyx
      _ = G.stabilizerWeight x y := mul_one _
      _ < 1 := lt_of_not_ge hxy
    exact (lt_irrefl _) hh

lemma twoPoint_symm (p : unitInterval) (x y : V) :
    CriticalPercolation.Sharpness.twoPoint G p x y=
      CriticalPercolation.Sharpness.twoPoint G p y x := by
  unfold CriticalPercolation.Sharpness.twoPoint
  rw [CriticalPercolation.Sharpness.hit_singleton_eq,
    CriticalPercolation.Sharpness.hit_singleton_eq]
  congr 1
  ext ω
  exact SimpleGraph.reachable_comm

theorem uniform_twoPoint_decay_of_finite_mass
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∀ ε : ℝ, 0<ε → ∃ R : ℕ, ∀ x y, y∉G.vertexBall x R →
      CriticalPercolation.Sharpness.twoPoint G p x y<ε := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  intro ε hε
  obtain ⟨R,hR⟩ := G.uniform_upperEscape_small hc hq p hm ε hε
  refine ⟨R,fun x y hxy => ?_⟩
  have h (x y : V) (hxy : y∉G.vertexBall x R) (hw : 1≤G.stabilizerWeight x y) :
      CriticalPercolation.Sharpness.twoPoint G p x y<ε := by
    apply lt_of_le_of_lt ?_ (hR x)
    unfold CriticalPercolation.Sharpness.twoPoint
    apply measureReal_mono (μ := G.law p) ?_ (measure_ne_top _ _)
    rw [CriticalPercolation.Sharpness.hit_singleton_eq]
    exact fun ω hω => ⟨y,⟨hω,hw⟩,hxy⟩
  rcases G.stabilizerWeight_ge_one_either hc hl x y with hw|hw
  · exact h x y hxy hw
  · rw [G.twoPoint_symm p x y]
    exact h y x (fun hx => hxy (G.vertexBall_comm.mpr hx)) hw

theorem nonunimodular_critical_twoPoint_decay_bs_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular) :
    ∀ ε : ℝ, 0<ε → ∃ R : ℕ, ∀ x y, y∉G.vertexBall x R →
      CriticalPercolation.Sharpness.twoPoint G G.criticalProbability x y<ε := by
  apply G.uniform_twoPoint_decay_of_finite_mass hc hl hq G.criticalProbability
  intro v
  exact (G.nonunimodular_critical_mass_finite_ae_bs hc hl hq hpc hu v).mono (fun ω h => (h v).ne)

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.nonunimodular_critical_twoPoint_decay_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.nonunimodular_critical_twoPoint_decay_bs_oai.{u_1, u_2}
