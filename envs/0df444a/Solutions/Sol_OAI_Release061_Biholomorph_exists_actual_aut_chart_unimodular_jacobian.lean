-- Prove2me | solution 1 for OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:53:40.629564+00:00
-- url     : https://prove2.me/submissions/e96be9c9-7abd-4cb1-b926-46d2d91f19af

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003

section
-- module Solutions.OAIQ025_SD.Compat
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ActionAutomorphismHomRange
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology TopologicalSpace
open scoped Classical

theorem bounded_divisible_automorphism_compact_cover {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    ∃ K : Set (Biholomorph U U), IsCompact K ∧
      ∀ a : Biholomorph U U, ∃ γ : Γ, ∃ b ∈ K, a=actionAutomorphismHom U Γ hhol γ*b := by
  obtain ⟨K,hK,hcover⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  let H := actionAutomorphismHom U Γ hhol
  refine ⟨(fun a : Biholomorph U U => a.toHomeomorph p) ⁻¹' K,
    (bounded_divisible_automorphism_evaluation_proper hU hc hb Γ hhol p).isCompact_preimage hK,?_⟩
  intro a
  obtain ⟨y,hy,γ,hγ⟩ := hcover (a.toHomeomorph p)
  refine ⟨γ,(H γ)⁻¹*a,?_,?_⟩
  · change γ⁻¹ • (a.toHomeomorph p) ∈ K
    rw [← hγ,inv_smul_smul]
    exact hy
  · change a=H γ*((H γ)⁻¹*a)
    group

theorem proper_discrete_orbit_map {X Γ : Type*} [TopologicalSpace X] [T2Space X]
    [CompactlyCoherentSpace X] [Group Γ] [TopologicalSpace Γ] [MulAction Γ X]
    [ProperSMul Γ X] (p : X) : IsProperMap (fun γ : Γ => γ • p) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_id.smul continuous_const,?_⟩
  intro K hK
  have h := (ProperSMul.isProperMap_smul_pair (G := Γ) (X := X)).isCompact_preimage
    (hK.prod (isCompact_singleton (x := p)))
  have he : Prod.fst '' ((fun gx : Γ × X => (gx.1 • gx.2,gx.2)) ⁻¹' (K ×ˢ {p})) =
      (fun γ : Γ => γ • p) ⁻¹' K := by
    ext γ
    constructor
    · rintro ⟨⟨δ,x⟩,⟨hx,hxp⟩,rfl⟩
      change δ • x ∈ K at hx
      change δ • p ∈ K
      rw [← mem_singleton_iff.mp hxp]
      exact hx
    · intro hγ
      exact ⟨(γ,p),⟨hγ,rfl⟩,rfl⟩
  rw [← he]
  exact h.image continuous_fst

theorem actionAutomorphismHom_proper {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsProperMap (actionAutomorphismHom U Γ hhol) := by
  exact isProperMap_of_comp_of_t2 continuous_of_discreteTopology
    (Biholomorph.continuous_evaluation p) (proper_discrete_orbit_map p)

theorem discrete_range_of_isClosedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology X] {f : X → Y} (hf : IsClosedMap f) : DiscreteTopology (Set.range f) := by
  apply discreteTopology_iff_forall_isClosed.mpr
  intro S
  have he : f '' (f ⁻¹' (Subtype.val '' S))=Subtype.val '' S := by
    apply image_preimage_eq_of_subset
    rintro x ⟨y,hy,rfl⟩
    exact y.property
  have h := (hf _ (isClosed_discrete (f ⁻¹' (Subtype.val '' S)))).preimage
    (continuous_subtype_val (p := fun x => x ∈ Set.range f))
  rw [he,preimage_image_eq _ Subtype.val_injective] at h
  exact h

theorem actionAutomorphismHom_range_discrete {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsClosed ((actionAutomorphismHom U Γ hhol).range : Set (Biholomorph U U)) ∧
      DiscreteTopology (actionAutomorphismHom U Γ hhol).range := by
  have hp := actionAutomorphismHom_proper Γ hhol p
  exact ⟨hp.isClosedMap.isClosed_range,discrete_range_of_isClosedMap hp.isClosedMap⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_UniformLatticeHaarRight
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped Classical

theorem exists_measurable_injective_real (X : Type*) [TopologicalSpace X]
    [MetrizableSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] :
    ∃ f : X → ℝ, Measurable f ∧ Function.Injective f := by
  let : MetricSpace X := metrizableSpaceMetric X
  let Y := UniformSpace.Completion X
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  obtain ⟨e,he⟩ := exists_measurableEmbedding_real Y
  exact ⟨fun x => e (x : Y),he.measurable.comp (UniformSpace.Completion.continuous_coe (α := X)).measurable,
    he.injective.comp (UniformSpace.Completion.coe_injective X)⟩

theorem uniform_lattice_measurable_transversal {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]
    (K : Set G) (hK : IsCompact K)
    (hcover : ∀ g : G, ∃ h : H, ∃ k ∈ K, g=(h:G)*k) :
    ∃ S : Set G, S ⊆ K ∧ MeasurableSet S ∧ ∀ x : G, ∃! h : H, (h:G)*x ∈ S := by
  let : Countable H := countable_of_Lindelof_of_discrete
  obtain ⟨e,hem,hei⟩ := exists_measurable_injective_real G
  let S : Set G := {x | x ∈ K ∧ ∀ h : H, (h:G)*x ∈ K → e x ≤ e ((h:G)*x)}
  refine ⟨S,fun _ hx => hx.1,?_,?_⟩
  · have heq : S=K ∩ ⋂ h : H, {x : G | (h:G)*x ∈ K → e x ≤ e ((h:G)*x)} := by
      ext x; simp only [S,mem_ofPred_eq,mem_inter_iff,mem_iInter]
    rw [heq]
    apply hK.isClosed.measurableSet.inter
    apply MeasurableSet.iInter
    intro h
    exact (hK.isClosed.measurableSet.preimage (continuous_const.mul continuous_id).measurable).imp
      (measurableSet_le hem (hem.comp (continuous_const.mul continuous_id).measurable))
  · intro x
    have hp : IsProperMap (fun h : H => (h:G)*x) :=
      (Homeomorph.mulRight x).isProperMap.comp hH.isProperMap_subtypeVal
    have hf := (hp.isCompact_preimage hK).finite_of_discrete
    have hn : ((fun h : H => (h:G)*x) ⁻¹' K).Nonempty := by
      obtain ⟨h,k,hk,rfl⟩ := hcover x
      exact ⟨h⁻¹,by simpa using hk⟩
    obtain ⟨a,ha,hmin⟩ := Set.exists_min_image _ (fun h : H => e ((h:G)*x)) hf hn
    change (a:G)*x ∈ K at ha
    have has : (a:G)*x ∈ S := by
      refine ⟨ha,?_⟩
      intro h hh
      simpa only [Subgroup.coe_mul,mul_assoc] using hmin (h*a) (by simpa [mul_assoc] using hh)
    refine ⟨a,has,?_⟩
    intro b hb
    apply Subtype.ext
    apply mul_right_cancel (b := x)
    apply hei
    apply le_antisymm
    · have ht := hb.2 (a*b⁻¹) (by simpa only [Subgroup.coe_mul,Subgroup.coe_inv,
        mul_assoc,inv_mul_cancel_left] using ha)
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,inv_mul_cancel_left] using ht
    · exact hmin b hb.1

theorem uniform_lattice_haar_right_invariant {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]
    (K : Set G) (hK : IsCompact K)
    (hcover : ∀ g : G, ∃ h : H, ∃ k ∈ K, g=(h:G)*k)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  let : Countable H := countable_of_Lindelof_of_discrete
  obtain ⟨S,hSK,hS,hu⟩ := uniform_lattice_measurable_transversal H hH K hK hcover
  have hs : IsFundamentalDomain H S μ := IsFundamentalDomain.mk' hS.nullMeasurableSet hu
  have h0 : μ S ≠ 0 := hs.measure_ne_zero (NeZero.ne μ)
  have htop : μ S ≠ ⊤ := ne_top_of_le_ne_top hK.measure_ne_top (measure_mono hSK)
  constructor
  intro g
  have ht : IsFundamentalDomain H ((fun x : G => x*g) ⁻¹' S) μ := by
    apply IsFundamentalDomain.mk' ((hS.preimage (continuous_mul_const g).measurable).nullMeasurableSet)
    intro x
    change ∃! h : H, (h:G)*x*g ∈ S
    simpa only [mul_assoc] using hu (x*g)
  have heq : (Measure.map (fun x : G => x*g) μ) S=μ S := by
    rw [Measure.map_apply (continuous_mul_const g).measurable hS]
    exact (hs.measure_eq ht).symm
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,Measure.smul_apply] at heq
  have hc : (Measure.modularCharacterFun g : ENNReal)=1 :=
    (ENNReal.mul_eq_right h0 htop).mp heq
  have hc' : Measure.modularCharacterFun g=1 := by exact_mod_cast hc
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,hc',one_smul]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompactFaithfulIsotropy
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped Classical

theorem bounded_divisible_automorphism_unimodular {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    let _ : LocallyCompactSpace (Biholomorph U U) :=
      bounded_divisible_automorphism_locallyCompact hU hc hb Γ hhol p
    let _ : MeasurableSpace (Biholomorph U U) := borel (Biholomorph U U)
    let _ : BorelSpace (Biholomorph U U) := ⟨rfl⟩
    (Measure.haar : Measure (Biholomorph U U)).IsMulRightInvariant := by
  let : LocallyCompactSpace (Biholomorph U U) :=
    bounded_divisible_automorphism_locallyCompact hU hc hb Γ hhol p
  let : MeasurableSpace (Biholomorph U U) := borel (Biholomorph U U)
  let : BorelSpace (Biholomorph U U) := ⟨rfl⟩
  let H := (actionAutomorphismHom U Γ hhol).range
  obtain ⟨hclosed,hdiscrete⟩ := actionAutomorphismHom_range_discrete Γ hhol p
  let : DiscreteTopology H := hdiscrete
  obtain ⟨K,hK,hcover⟩ := bounded_divisible_automorphism_compact_cover hU hc hb Γ hhol p
  apply uniform_lattice_haar_right_invariant H hclosed K hK
  intro a
  obtain ⟨γ,b,hb,h⟩ := hcover a
  exact ⟨⟨actionAutomorphismHom U Γ hhol γ,⟨γ,rfl⟩⟩,b,hb,h⟩

end

open Set Filter Topology TopologicalSpace
open scoped Classical
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem firstJet_injective (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) (p : U) : Function.Injective (firstJet p) := by
  intro a b hab
  have hp : a.toHomeomorph p=b.toHomeomorph p := congrArg Prod.fst hab
  have hd : a.derivativeAt p=b.derivativeAt p := congrArg Prod.snd hab
  have he : b⁻¹*a=1 := by
    apply eq_one_of_firstJet hU hc hb (b⁻¹*a) p
    · simp only [mul_apply,inv_apply,hp,Homeomorph.symm_apply_apply]
    · rw [derivativeAt_mul hU,hp,hd]
      rw [← derivativeAt_mul hU,inv_mul_cancel,derivativeAt_one hU]
  exact (inv_mul_eq_one.mp he).symm

theorem firstJet_continuous (hU : IsOpen U) [LocallyCompactSpace U] (p : U) :
    Continuous (firstJet p) :=
  (continuous_evaluation p).prodMk (derivativeAt_continuous hU p)

theorem firstJet_isClosedEmbedding (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsClosedEmbedding (firstJet p) := by
  have hp : IsProperMap (firstJet p) :=
    isProperMap_of_comp_of_t2 (firstJet_continuous hU p) continuous_fst
      (bounded_divisible_automorphism_evaluation_proper hU hc hb Γ hhol p)
  exact .of_continuous_injective_isClosedMap (firstJet_continuous hU p)
    (firstJet_injective hU hc hb p) hp.isClosedMap

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocalAutomorphismODEGroup2
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem local_automorphism_ODE_group_law_of_contDiffAt (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (p : U) (X : Affine n → Affine n)
    (hX : ContDiffAt ℝ 1 X p.val)
    (g : ℝ → Biholomorph U U) (hg0 : g 0=1)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0<δ) (hball : closedBall p.val r⊆U)
    (hgc : ContinuousOn g (Icc (-δ) δ))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ ε > (0:ℝ), ε<δ ∧ ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t := by
  have hgc0 : ContinuousAt g 0 := (hgc 0 ⟨by linarith,hδ.le⟩).continuousAt
    (Icc_mem_nhds (by linarith) hδ)
  obtain ⟨L,K,hK,hL⟩ := hX.exists_lipschitzOnWith
  obtain ⟨ρ,hρ,hρK⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (inter_mem hK (ball_mem_nhds p.val hr))
  obtain ⟨ε₀,hε₀,hstep₀⟩ := ambientAut_uniform_at_zero hU g hgc0 hg0 p
    (ball_mem_nhds p.val hρ)
  obtain ⟨ε₁,hε₁,hstep₁⟩ := ambientAut_uniform_at_zero hU g hgc0 hg0 p
    (ball_mem_nhds p.val hε₀)
  let ε : ℝ := min (δ/3) (min (ε₀/3) ε₁)
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) hε₁)
  have hεδ : ε≤δ/3 := min_le_left _ _
  have hεε₀ : ε≤ε₀/3 := (min_le_right _ _).trans (min_le_left _ _)
  have hεε₁ : ε≤ε₁ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,hε,by linarith,?_⟩
  intro s t hs ht
  apply eq_of_ambientAut_eventuallyEq hU hc p
  filter_upwards [ball_mem_nhds p.val (lt_min hε₀ (lt_min hε₁ hr))] with x hx
  have hx₀ : x∈ball p.val ε₀ := ball_subset_ball (min_le_left _ _) hx
  have hx₁ : x∈ball p.val ε₁ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx
  have hxr : x∈closedBall p.val r := ball_subset_closedBall
    (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hx)
  have hxu : x∈U := hball hxr
  have htx : (g t).ambientAut x∈ball p.val ε₀ := hstep₁ t (ht.trans_le hεε₁) x hx₁
  have htxr : (g t).ambientAut x∈closedBall p.val r := ball_subset_closedBall
    (hρK (hstep₀ t (by linarith) x hx₀)).2
  have hs' : s∈Ioo (-ε) ε := abs_lt.mp hs
  have ht' : t∈Ioo (-ε) ε := abs_lt.mp ht
  have hsum {u : ℝ} (hu : u∈Ioo (-ε) ε) : u+t∈Ioo (-δ) δ ∧ |u+t|<ε₀ := by
    have ha := abs_add_le u t
    have hu' : |u|<ε := abs_lt.mpr hu
    constructor
    · constructor <;> linarith [ht'.1,ht'.2,hu.1,hu.2]
    · linarith
  have heq := ODE_solution_unique_of_mem_Ioo
    (v := fun (_ : ℝ) y => X y) (s := fun _ => K) (a := -ε) (b := ε) (t₀ := 0)
    (fun _ _ => hL) (show (0:ℝ)∈Ioo (-ε) ε from ⟨by linarith,hε⟩)
    (f := fun u => (g (u+t)).ambientAut x)
    (g := fun u => (g u).ambientAut ((g t).ambientAut x))
    (fun u hu => ⟨by
      have hshift : HasDerivAt (fun v : ℝ => v+t) 1 u := by simpa only [id_eq] using (hasDerivAt_id u).add_const t
      have hh := (hd x hxr (u+t) (hsum hu).1).hasDerivAt.scomp u hshift
      simpa only [Function.comp_def,one_smul] using hh,
      (hρK (hstep₀ (u+t) (hsum hu).2 x hx₀)).1⟩)
    (fun u hu => ⟨(hd _ htxr u (by constructor <;> linarith [hu.1,hu.2])).hasDerivAt,
      (hρK (hstep₀ u (by have hh := abs_lt.mpr hu; linarith) _ htx)).1⟩)
    (by
      rw [zero_add,hg0]
      rw [ambientAut_apply (g t) ⟨x,hxu⟩,ambientAut_apply,one_apply])
  have hh := heq hs'
  dsimp only at hh
  rw [ambientAut_apply (g t) ⟨x,hxu⟩,ambientAut_apply,
    ← mul_apply,← ambientAut_apply] at hh
  exact hh

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ConsistentVariableStepsTendsto
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric

open Set Filter Topology Metric
open scoped NNReal

theorem consistent_variable_steps_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (l : Filter ι) [NeBot l]
    (q : ι → E → E) (h : ι → ℝ) (N : ι → ℕ) (X : E → E) (K : Set E)
    {L : ℝ≥0} (hL : LipschitzOnWith L X K)
    (hpos : ∀ i, 0≤h i) (hsmall : Tendsto h l (𝓝 0))
    (hcons : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ x∈K,
      ‖q i x-x-h i • X x‖≤ε*h i)
    (p : E) (α : ℝ → E) {T t : ℝ} (hT : 0≤T) (hα0 : α 0=p)
    (hduration : ∀ i, (N i:ℝ)*h i≤T)
    (ht : Tendsto (fun i => (N i:ℝ)*h i) l (𝓝 t))
    (hαK : ∀ s∈Icc 0 T, α s∈K)
    (hαd : ∀ s∈Icc 0 T, HasStrictDerivAt α (X (α s)) s)
    (hαv : ∀ s∈Icc 0 T, ContinuousAt (fun s => X (α s)) s)
    (hit : ∀ᶠ i in l, ∀ j≤N i, ((q i)^[j]) p∈K) :
    Tendsto (fun i => ((q i)^[N i]) p) l (𝓝 (α t)) := by
  have hs (i : ι) {j : ℕ} (hj : j≤N i) : (j:ℝ)*h i∈Icc 0 T :=
    ⟨mul_nonneg (Nat.cast_nonneg _) (hpos i),
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (hpos i)).trans (hduration i)⟩
  have htmem : t∈Icc 0 T := isClosed_Icc.mem_of_tendsto ht
    (Eventually.of_forall fun i => hs i le_rfl)
  have hαt : Tendsto (fun i => α ((N i:ℝ)*h i)) l (𝓝 (α t)) :=
    (hαd t htmem).hasDerivAt.continuousAt.tendsto.comp ht
  have hdist : Tendsto (fun i => dist (((q i)^[N i]) p) (α ((N i:ℝ)*h i))) l (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun i => ha.trans_le (dist_nonneg)
    · intro η hη
      let C : ℝ := 2*T*Real.exp (L*T)
      have hC : 0≤C := by dsimp [C]; positivity
      let ε : ℝ := η/(C+1)
      have hε : 0<ε := div_pos hη (by linarith)
      have hεC : ε*C<η := by
        have he : ε*(C+1)=η := div_mul_cancel₀ η (by linarith)
        nlinarith
      have hy := hsmall.eventually (uniform_curve_taylor α (fun s => X (α s))
        (Icc 0 T) isCompact_Icc hαv hαd hε)
      filter_upwards [hcons ε hε,hy,hit] with i hqi hai hiti
      let x : ℕ → E := fun j => ((q i)^[j]) p
      let y : ℕ → E := fun j => α ((j:ℝ)*h i)
      have hxj (j : ℕ) (hj : j<N i) : x j∈K := hiti j hj.le
      have hyj (j : ℕ) (hj : j<N i) : y j∈K := hαK _ (hs i hj.le)
      have hxe (j : ℕ) (hj : j<N i) : ‖x (j+1)-x j-h i • X (x j)‖≤ε*|h i| := by
        simpa only [x,Function.iterate_succ_apply',abs_of_nonneg (hpos i)] using hqi (x j) (hxj j hj)
      have hye (j : ℕ) (hj : j<N i) : ‖y (j+1)-y j-h i • X (y j)‖≤ε*|h i| := by
        have he := hai ((j:ℝ)*h i) (hs i hj.le)
        have hj' : ((j+1:ℕ):ℝ)*h i=(j:ℝ)*h i+h i := by rw [Nat.cast_add,Nat.cast_one]; ring
        simpa only [y,hj'] using he
      have hv := finite_euler_comparison X K hL x y hε.le (by simp [x,y,hα0]) hxj hyj hxe hye
      have hb : (N i:ℝ)*(2*ε*|h i|)*Real.exp ((N i:ℝ)*L*|h i|)≤ε*C := by
        rw [abs_of_nonneg (hpos i)]
        have hE : (N i:ℝ)*L*h i≤L*T := by
          calc
            (N i:ℝ)*L*h i = L*((N i:ℝ)*h i) := by ring
            _ ≤ L*T := mul_le_mul_of_nonneg_left (hduration i) L.coe_nonneg
        have he : (N i:ℝ)*(2*ε*h i)≤2*ε*T := by
          nlinarith [mul_le_mul_of_nonneg_left (hduration i) (by positivity : 0≤2*ε)]
        calc
          _ ≤ (2*ε*T)*Real.exp (L*T) := mul_le_mul he (Real.exp_le_exp.mpr hE)
            (Real.exp_nonneg _) (by positivity)
          _ = ε*C := by dsimp [C]; ring
      simpa only [dist_eq_norm,x,y] using (hv.trans hb).trans_lt hεC
  exact hαt.congr_dist (by simpa only [dist_comm] using hdist)
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_VariableEulerAutomorphismFamily
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric

theorem floor_steps_tendsto {ι : Type*} (l : Filter ι) (h : ι → ℝ)
    (hp : ∀ i, 0<h i) (hh : Tendsto h l (𝓝 0)) {t : ℝ} (ht : 0≤t) :
    Tendsto (fun i => (⌊t/h i⌋₊ : ℝ)*h i) l (𝓝 t) := by
  have hle (i : ι) : (⌊t/h i⌋₊ : ℝ)*h i≤t := by
    exact (le_div_iff₀ (hp i)).mp (Nat.floor_le (div_nonneg ht (hp i).le))
  have hlt (i : ι) : t-(⌊t/h i⌋₊ : ℝ)*h i≤h i := by
    have hh' := (div_lt_iff₀ (hp i)).mp (Nat.lt_floor_add_one (t/h i))
    nlinarith
  have hzero : Tendsto (fun i => t-(⌊t/h i⌋₊ : ℝ)*h i) l (𝓝 0) :=
    squeeze_zero (fun i => sub_nonneg.mpr (hle i)) hlt hh
  have hconst : Tendsto (fun _ : ι => t) l (𝓝 t) := tendsto_const_nhds
  have hfinal := hconst.sub hzero
  simpa only [sub_sub_cancel,sub_zero] using hfinal

theorem iterate_displacement_of_bound {E : Type*} [NormedAddCommGroup E]
    (q : E → E) (p x : E) {R B : ℝ} {N : ℕ} (hB : 0≤B)
    (hsize : dist x p+(N:ℝ)*B≤R)
    (hstep : ∀ y∈closedBall p R, ‖q y-y‖≤B) :
    ∀ j≤N, dist ((q^[j]) x) p≤dist x p+(j:ℝ)*B := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hjN : j≤N := (Nat.le_succ j).trans hj
    have hi := ih hjN
    have hmem : (q^[j]) x∈closedBall p R := hi.trans
      ((add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjN) hB)).trans hsize)
    rw [Function.iterate_succ_apply']
    calc
      dist (q ((q^[j]) x)) p ≤ dist (q ((q^[j]) x)) ((q^[j]) x)+dist ((q^[j]) x) p := dist_triangle _ _ _
      _ ≤ B+(dist x p+(j:ℝ)*B) := add_le_add (by simpa only [dist_eq_norm] using hstep _ hmem) hi
      _ = dist x p+((j+1:ℕ):ℝ)*B := by rw [Nat.cast_add,Nat.cast_one]; ring

open Set Filter Topology Metric
open scoped NNReal
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem variable_Euler_automorphism_family (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0<h i) (hh : Tendsto h l (𝓝 0))
    (p : U) (X : Affine n → Affine n) {R r M T : ℝ}
    (hr : 0 < r) (hM : 0≤M) (hT : 0<T) (hsize : r+M*T≤R)
    (hRU : closedBall p.val R⊆U) {L : ℝ≥0}
    (hL : LipschitzOnWith L X (closedBall p.val R))
    (hstep : ∀ᶠ i in l, ∀ y∈closedBall p.val R, ‖(q i).ambientAut y-y‖≤M*h i)
    (hcons : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ y∈closedBall p.val R,
      ‖(q i).ambientAut y-y-h i • X y‖≤ε*h i)
    (α : Affine n → ℝ → Affine n)
    (hα0 : ∀ x∈closedBall p.val r, α x 0=x)
    (hα : ∀ x∈closedBall p.val r, ∀ t∈Icc 0 T,
      α x t∈closedBall p.val R ∧ HasStrictDerivAt (α x) (X (α x t)) t ∧
        ContinuousAt (fun s => X (α x s)) t)
    (hαc : ContinuousOn (fun z : Affine n × ℝ => α z.1 z.2) (closedBall p.val r ×ˢ Icc 0 T)) :
    ∃ g : ℝ → Biholomorph U U, g 0=1 ∧ ContinuousOn g (Icc 0 T) ∧
      (∀ t∈Icc 0 T, Tendsto (fun i => (q i)^⌊t/h i⌋₊) l (𝓝 (g t))) ∧
      ∀ x∈closedBall p.val r, ∀ t∈Icc 0 T, (g t).ambientAut x=α x t := by
  let N : ℝ → ι → ℕ := fun t i => ⌊t/h i⌋₊
  have hNt (t : ℝ) (ht : 0≤t) (i : ι) : (N t i:ℝ)*h i≤t :=
    (le_div_iff₀ (hp i)).mp (Nat.floor_le (div_nonneg ht (hp i).le))
  have hNr {t : ℝ} (ht : t∈Icc 0 T) {i : ι} {j : ℕ} (hj : j≤N t i) : (j:ℝ)*(M*h i)≤M*T := by
    calc
      (j:ℝ)*(M*h i) = M*((j:ℝ)*h i) := by ring
      _ ≤ M*T := mul_le_mul_of_nonneg_left
        (((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) (hp i).le).trans (hNt t ht.1 i)).trans ht.2) hM
  have hrR : r≤R := (le_add_of_nonneg_right (mul_nonneg hM hT.le)).trans hsize
  have hball : closedBall p.val r⊆U := (closedBall_subset_closedBall hrR).trans hRU
  have hit (x : Affine n) (hx : x∈closedBall p.val r) (t : ℝ) (ht : t∈Icc 0 T) :
      ∀ᶠ i in l, ∀ j≤N t i, (((q i).ambientAut)^[j]) x∈closedBall p.val R := by
    filter_upwards [hstep] with i hi
    intro j hj
    have hb : 0≤M*h i := mul_nonneg hM (hp i).le
    have hn : dist x p.val+(N t i:ℝ)*(M*h i)≤R :=
      (add_le_add (mem_closedBall.mp hx) (hNr ht le_rfl)).trans hsize
    exact (iterate_displacement_of_bound (q i).ambientAut p.val x hb hn hi j hj).trans
      ((add_le_add (mem_closedBall.mp hx) (hNr ht hj)).trans hsize)
  have htend (x : Affine n) (hx : x∈closedBall p.val r) (t : ℝ) (ht : t∈Icc 0 T) :
      Tendsto (fun i => ((q i).ambientAut^[N t i]) x) l (𝓝 (α x t)) := by
    exact consistent_variable_steps_tendsto l (fun i => (q i).ambientAut) h (N t) X _ hL
      (fun i => (hp i).le) hh hcons x (α x) hT.le (hα0 x hx)
      (fun i => (hNt t ht.1 i).trans ht.2) (floor_steps_tendsto l h hp hh ht.1)
      (fun s hs => (hα x hx s hs).1) (fun s hs => (hα x hx s hs).2.1)
      (fun s hs => (hα x hx s hs).2.2) (hit x hx t ht)
  let V : Set U := Subtype.val ⁻¹' closedBall p.val R
  have hV : IsCompact V := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa only [V,image_preimage_eq_inter_range,Subtype.range_coe_subtype,ofPred_mem_eq,
      inter_eq_left.mpr hRU] using isCompact_closedBall p.val R
  let K : Set (Biholomorph U U) := (fun e : Biholomorph U U => e.toHomeomorph p) ⁻¹' V
  have hK : IsCompact K :=
    (bounded_divisible_automorphism_evaluation_proper hU hc hbd Γ hhol p).isCompact_preimage hV
  have hpow (t : ℝ) (ht : t∈Icc 0 T) : ∀ᶠ i in l, (q i)^(N t i)∈K := by
    filter_upwards [hit p.val (mem_closedBall_self hr.le) t ht] with i hi
    have he := hi (N t i) le_rfl
    change ((q i)^(N t i)).toHomeomorph p∈V
    change (((q i)^(N t i)).toHomeomorph p).val∈closedBall p.val R
    simpa only [ambientAut_iterate] using he
  have hex (t : ℝ) : ∃ e : Biholomorph U U, t∈Icc 0 T →
      Tendsto (fun i => (q i)^(N t i)) l (𝓝 e) ∧
      EqOn e.ambientAut (fun x => α x t) (closedBall p.val r) := by
    by_cases ht : t∈Icc 0 T
    · obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc l
        (fun i => (q i)^(N t i)) K hK (hpow t ht) p hr hball (fun x => α x t) (by
          intro x hx
          simpa only [ambientAut_iterate (p := ⟨x,hball hx⟩),ambientAut_apply (p := ⟨x,hball hx⟩)] using htend x hx t ht)
      exact ⟨e,fun _ => ⟨he,heq⟩⟩
    · exact ⟨1,fun h => (ht h).elim⟩
  choose g hg using hex
  have hgK (t : ℝ) (ht : t∈Icc 0 T) : g t∈K := hK.isClosed.mem_of_tendsto (hg t ht).1 (hpow t ht)
  have hg0 : g 0=1 := by
    have he := (hg 0 ⟨le_rfl,hT.le⟩).1
    have he' : Tendsto (fun _ : ι => (1 : Biholomorph U U)) l (𝓝 (g 0)) := by simpa only [N,zero_div,Nat.floor_zero,pow_zero] using he
    exact tendsto_nhds_unique he' tendsto_const_nhds
  have hgc : ContinuousOn g (Icc 0 T) := by
    intro t ht
    have : NeBot (𝓝[Icc 0 T] t) := nhdsWithin_neBot_of_mem ht
    have hv (x : Affine n) (hx : x∈closedBall p.val r) :
        Tendsto (fun s => (g s).ambientAut x) (𝓝[Icc 0 T] t) (𝓝 (α x t)) := by
      have hpath : ContinuousOn (fun s => α x s) (Icc 0 T) := hαc.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hx,hs⟩)
      apply (hpath t ht).tendsto.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ((hg s hs).2 hx).symm
    obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc
      (𝓝[Icc 0 T] t) g K hK (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact hgK s hs) p hr hball (fun x => α x t) hv
    have hegt : e=g t := eq_of_ambientAut_eventuallyEq hU hc p (by
      filter_upwards [closedBall_mem_nhds p.val hr] with x hx
      exact (heq hx).trans ((hg t ht).2 hx).symm)
    change Tendsto g (𝓝[Icc 0 T] t) (𝓝 (g t))
    rwa [hegt] at he
  exact ⟨g,hg0,hgc,(fun t ht => (hg t ht).1),(fun x hx t ht => (hg t ht).2 hx)⟩
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterLocalODE
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem exists_oneParameter_of_local_ODE_germ (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (p : U) (X : Affine n → Affine n)
    (hX : ContDiffAt ℝ 1 X p.val)
    (g : ℝ → Biholomorph U U) (hg0 : g 0=1)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0<δ) (hball : closedBall p.val r⊆U)
    (hgc : ContinuousOn g (Icc (-δ) δ))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ infinitesimalGenerator H=ᶠ[𝓝 p.val] X := by
  obtain ⟨ε,hε,_,hm⟩ := local_automorphism_ODE_group_law_of_contDiffAt hU hc p X hX g hg0 hr hδ hball hgc hd
  have hgc0 : ContinuousAt g 0 := (hgc 0 ⟨by linarith,hδ.le⟩).continuousAt
    (Icc_mem_nhds (by linarith) hδ)
  obtain ⟨H,hH0,hHc,hHm,hHloc⟩ := local_real_hom_extension g hg0 hgc0 hε hm
  refine ⟨H,hH0,hHc,hHm,?_⟩
  filter_upwards [closedBall_mem_nhds p.val hr] with x hx
  have hdx := hd x hx 0 ⟨by linarith,hδ⟩
  have heq : (fun t => (g t).ambientAut x)=ᶠ[𝓝 (0:ℝ)] (fun t => (H t).ambientAut x) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hε] with t ht
    rw [hHloc t (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)]
  have hdH := hdx.congr_of_eventuallyEq heq
  have heq0 : (g 0).ambientAut x=x := by rw [hg0,ambientAut_apply 1 ⟨x,hball hx⟩,one_apply]
  change deriv (fun t => (H t).ambientAut x) 0=X x
  simpa only [heq0] using hdH.hasDerivAt.deriv
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterPositiveLocal2
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem exists_oneParameter_of_positive_local_ODE_germ (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (p : U)
    (X : Affine n → Affine n)
    (g : ℝ → Biholomorph U U) {r T : ℝ} (hr : 0 < r) (hT : 0<T)
    (hX : ContDiffAt ℝ 1 X ((g (T/2)).toHomeomorph p).val)
    (_hball : closedBall p.val r⊆U) (hgc : ContinuousOn g (Icc 0 T))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo 0 T,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧
      infinitesimalGenerator H=ᶠ[𝓝 ((g (T/2)).toHomeomorph p).val] X := by
  let C : ℝ := T/2
  let δ : ℝ := T/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  let p' : U := (g C).toHomeomorph p
  have hi : ((g C)⁻¹).ambientAut p'.val=p.val := by
    rw [ambientAut_apply]
    change (((g C)⁻¹).toHomeomorph ((g C).toHomeomorph p)).val=p.val
    rw [← mul_apply,inv_mul_cancel,one_apply]
  have hpre : ((g C)⁻¹).ambientAut ⁻¹' ball p.val r ∈ 𝓝 p'.val := by
    apply (ambientAut_analytic hU ((g C)⁻¹) p'.val p'.property).continuousAt
    simpa only [hi] using ball_mem_nhds p.val hr
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hpre (hU.mem_nhds p'.property))
  let f : ℝ → Biholomorph U U := fun t => g (C+t)*(g C)⁻¹
  have hf0 : f 0=1 := by simp only [f,add_zero,mul_inv_cancel]
  have hfc : ContinuousOn f (Icc (-δ) δ) := by
    apply (hgc.comp (continuous_const.add continuous_id).continuousOn ?_).mul continuous_const.continuousOn
    intro t ht
    dsimp [C,δ] at *
    constructor <;> linarith [ht.1,ht.2]
  have hfd : ∀ x∈closedBall p'.val ρ, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (f s).ambientAut x) (X ((f t).ambientAut x)) t := by
    intro x hx t ht
    have hxu : x∈U := (hρsub hx).2
    let y : U := ((g C)⁻¹).toHomeomorph ⟨x,hxu⟩
    have hy : y.val∈closedBall p.val r := by
      have hv := ball_subset_closedBall (hρsub hx).1
      change ((g C)⁻¹).ambientAut x∈closedBall p.val r at hv
      simpa only [ambientAut_apply (p := ⟨x,hxu⟩)] using hv
    have htt : C+t∈Ioo 0 T := by
      dsimp [C,δ] at *
      constructor <;> linarith [ht.1,ht.2]
    have hs : HasStrictDerivAt (fun s : ℝ => C+s) 1 t := by
      simpa only [id_eq] using (hasStrictDerivAt_id t).const_add C
    have hh := (hd y.val hy (C+t) htt).scomp t hs
    have he (s : ℝ) : (f s).ambientAut x=(g (C+s)).ambientAut y.val := by
      rw [ambientAut_apply (f s) ⟨x,hxu⟩,ambientAut_apply]
      exact congrArg Subtype.val (mul_apply _ _ _)
    simpa only [Function.comp_def,one_smul,← he] using hh
  exact exists_oneParameter_of_local_ODE_germ hU hc p' X hX f hf0 hρ hδ
    (fun x hx => (hρsub hx).2) hfc hfd

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalizedAutomorphismLocalLimit
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
open scoped NNReal
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem normalized_automorphism_local_limit_complete (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0<h i) (hh : Tendsto h l (𝓝 0))
    (S : Set (Affine n)) (hS : IsOpen S) (hSc : IsPreconnected S) (hSU : S⊆U)
    (p : U) (hpS : p.val∈S) (X : Affine n → Affine n) (hX : AnalyticOnNhd ℂ X S)
    (hq : TendstoLocallyUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x)) X l S) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ EqOn (infinitesimalGenerator H) X S := by
  have hf : ContDiffAt ℝ 1 X p.val := (hX p.val hpS).contDiffAt.restrict_scalars ℝ
  obtain ⟨L,W,hW,hL⟩ := hf.exists_lipschitzOnWith
  obtain ⟨R,hR,hRsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem hW (hS.mem_nhds hpS))
  let K : Set (Affine n) := closedBall p.val R
  have hKS : K⊆S := fun x hx => (hRsub hx).2
  have hKU : K⊆U := hKS.trans hSU
  have hLK : LipschitzOnWith L X K := hL.mono (fun x hx => (hRsub hx).1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hconv : TendstoUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x)) X l K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hq.mono hKS)
  have hcons (ε : ℝ) (hε : 0<ε) : ∀ᶠ i in l, ∀ y∈K,
      ‖(q i).ambientAut y-y-h i • X y‖≤ε*h i := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with i hi
    intro y hy
    have he : (q i).ambientAut y-y-h i • X y=
        h i • ((h i)⁻¹ • ((q i).ambientAut y-y)-X y) := by
      rw [smul_sub,smul_smul,mul_inv_cancel₀ (ne_of_gt (hp i)),one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (hp i)]
    have hb : ‖(h i)⁻¹ • ((q i).ambientAut y-y)-X y‖≤ε := by
      exact le_of_lt (by simpa only [dist_eq_norm,norm_sub_rev] using hi y hy)
    calc
      _ ≤ h i*ε := mul_le_mul_of_nonneg_left hb (hp i).le
      _ = ε*h i := mul_comm _ _
  obtain ⟨C,hC,hCb⟩ := (hK.image_of_continuousOn (hX.continuousOn.mono hKS)).isBounded.exists_pos_norm_le
  let M : ℝ := C+1
  have hM : 0<M := by dsimp [M]; linarith
  have hstep : ∀ᶠ i in l, ∀ y∈K, ‖(q i).ambientAut y-y‖≤M*h i := by
    filter_upwards [hcons 1 zero_lt_one] with i hi
    intro y hy
    have hb := hCb (X y) (mem_image_of_mem X hy)
    have he : (q i).ambientAut y-y=((q i).ambientAut y-y-h i • X y)+h i • X y := by abel
    rw [he]
    calc
      _ ≤ ‖(q i).ambientAut y-y-h i • X y‖+‖h i • X y‖ := norm_add_le _ _
      _ ≤ 1*h i+h i*C := add_le_add (hi y hy) (by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hp i)]
        exact mul_le_mul_of_nonneg_left hb (hp i).le)
      _ = M*h i := by dsimp [M]; ring
  obtain ⟨r₀,hr₀,δ₀,hδ₀,α,hα0,hα,hαc⟩ := exists_local_integralCurves_in_nhds X p.val K
    (closedBall_mem_nhds p.val hR) (fun y hy => (hX y (hKS hy)).continuousAt) hf
  let r : ℝ := min r₀ (R/2)
  let T : ℝ := min δ₀ (R/(2*M))
  have hr : 0 < r := lt_min hr₀ (half_pos hR)
  have hT : 0<T := lt_min hδ₀ (div_pos hR (by positivity))
  have hrr : r ≤ r₀ := min_le_left _ _
  have hrR : r≤R/2 := min_le_right _ _
  have hTδ : T≤δ₀ := min_le_left _ _
  have hTM : T≤R/(2*M) := min_le_right _ _
  have hsize : r+M*T≤R := by
    have hv := (le_div_iff₀ (show 0<2*M by positivity)).mp hTM
    nlinarith
  have hbU : closedBall p.val r⊆U :=
    (closedBall_subset_closedBall (hrR.trans (half_le_self hR.le))).trans hKU
  have htδ {t : ℝ} (ht : t∈Icc 0 T) : t∈Icc (-δ₀) δ₀ := by
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨g,_,hgc,_,hgeq⟩ := variable_Euler_automorphism_family hU hc hbd Γ hhol l q h hp hh p X
    hr hM.le hT hsize hKU hLK hstep hcons α
    (fun x hx => hα0 x (closedBall_subset_closedBall hrr hx))
    (fun x hx t ht => hα x (closedBall_subset_closedBall hrr hx) t (htδ ht))
    (hαc.mono (fun z hz => ⟨closedBall_subset_closedBall hrr hz.1,htδ hz.2⟩))
  have htc : T/2∈Icc 0 T := ⟨by positivity,half_le_self hT.le⟩
  have hp' : ((g (T/2)).toHomeomorph p).val∈S := by
    have he := hgeq p.val (mem_closedBall_self hr.le) (T/2) htc
    rw [ambientAut_apply] at he
    rw [he]
    exact hKS (hα p.val (mem_closedBall_self hr₀.le) (T/2) (htδ htc)).1
  have hxd : ContDiffAt ℝ 1 X ((g (T/2)).toHomeomorph p).val :=
    (hX _ hp').contDiffAt.restrict_scalars ℝ
  obtain ⟨H,hH0,hHc,hHm,hHg⟩ := exists_oneParameter_of_positive_local_ODE_germ hU hc p X g hr hT hxd hbU hgc (by
    intro x hx t ht
    have heq : α x=ᶠ[𝓝 t] (fun s => (g s).ambientAut x) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hgeq x hx s ⟨hs.1.le,hs.2.le⟩).symm
    have hd := (hα x (closedBall_subset_closedBall hrr hx) t (htδ ⟨ht.1.le,ht.2.le⟩)).2.1
    have hder := hd.congr_of_eventuallyEq heq
    simpa only [hgeq x hx t ⟨ht.1.le,ht.2.le⟩] using hder)
  refine ⟨H,hH0,hHc,hHm,?_⟩
  exact ((infinitesimalGenerator_analytic hU H hHc hbd hH0 hHm).mono hSU).eqOn_of_preconnected_of_eventuallyEq hX hSc hp' hHg

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PowersTendstoOneVanishing
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem powers_tendsto_one_of_vanishing_normalized_displacement
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0≤h i) (N : ι → ℕ) {T : ℝ} (hT : 0<T)
    (hNT : ∀ i, (N i:ℝ)*h i≤T) (p : U) {R : ℝ} (hR : 0<R)
    (hRU : closedBall p.val R⊆U)
    (hstep : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ y∈closedBall p.val R,
      ‖(q i).ambientAut y-y‖≤ε*h i) :
    Tendsto (fun i => (q i)^(N i)) l (𝓝 1) := by
  have hbound (ε : ℝ) (hε : 0<ε) : ∀ᶠ i in l, ∀ x∈closedBall p.val (R/2),
      dist (((q i).ambientAut^[N i]) x) x≤ε := by
    let d : ℝ := min (R/(4*T)) (ε/(2*T))
    have hd : 0<d := lt_min (div_pos hR (by positivity)) (div_pos hε (by positivity))
    have hdR : d*T≤R/4 := by
      have hv := (le_div_iff₀ (show 0<4*T by positivity)).mp (min_le_left (R/(4*T)) (ε/(2*T)))
      dsimp [d]
      nlinarith
    have hdε : d*T≤ε/2 := by
      have hv := (le_div_iff₀ (show 0<2*T by positivity)).mp (min_le_right (R/(4*T)) (ε/(2*T)))
      dsimp [d]
      nlinarith
    filter_upwards [hstep d hd] with i hi
    intro x hx
    have hsub : closedBall x (R/2)⊆closedBall p.val R := by
      intro y hy
      exact (dist_triangle y x p.val).trans (by linarith [mem_closedBall.mp hy,mem_closedBall.mp hx])
    have hn : (N i:ℝ)*(d*h i)≤d*T := by
      calc
        _ = d*((N i:ℝ)*h i) := by ring
        _ ≤ d*T := mul_le_mul_of_nonneg_left (hNT i) hd.le
    have hh := iterate_displacement_of_bound (q i).ambientAut x x (mul_nonneg hd.le (hp i))
      (R := R/2) (N := N i) (by simpa only [dist_self,zero_add] using hn.trans (hdR.trans (by linarith)))
      (fun y hy => hi y (hsub hy)) (N i) le_rfl
    simp only [dist_self,zero_add] at hh
    exact hh.trans (hn.trans (hdε.trans (half_le_self hε.le)))
  have hball : closedBall p.val (R/2)⊆U := (closedBall_subset_closedBall (half_le_self hR.le)).trans hRU
  have htend (x : Affine n) (hx : x∈closedBall p.val (R/2)) :
      Tendsto (fun i => ((q i)^(N i)).ambientAut x) l (𝓝 x) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hbound (ε/2) (half_pos hε)] with i hi
    have hv := hi x hx
    simpa only [ambientAut_iterate (p := ⟨x,hball hx⟩),ambientAut_apply (p := ⟨x,hball hx⟩)] using
      hv.trans_lt (half_lt_self hε)
  let V : Set U := Subtype.val ⁻¹' closedBall p.val R
  have hV : IsCompact V := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa only [V,image_preimage_eq_inter_range,Subtype.range_coe_subtype,ofPred_mem_eq,
      inter_eq_left.mpr hRU] using isCompact_closedBall p.val R
  let K : Set (Biholomorph U U) := (fun e : Biholomorph U U => e.toHomeomorph p) ⁻¹' V
  have hK : IsCompact K :=
    (bounded_divisible_automorphism_evaluation_proper hU hc hbd Γ hhol p).isCompact_preimage hV
  have hpow : ∀ᶠ i in l, (q i)^(N i)∈K := by
    filter_upwards [hbound R hR] with i hi
    have hv := hi p.val (mem_closedBall_self (by linarith))
    change (((q i)^(N i)).toHomeomorph p).val∈closedBall p.val R
    simpa only [mem_closedBall,ambientAut_iterate] using hv
  obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc l
    (fun i => (q i)^(N i)) K hK hpow p (half_pos hR) hball id htend
  have he1 : e=1 := eq_of_ambientAut_eventuallyEq hU hc p (by
    filter_upwards [closedBall_mem_nhds p.val (half_pos hR)] with x hx
    rw [heq hx,ambientAut_apply 1 ⟨x,hball hx⟩,one_apply]
    rfl)
  rwa [he1] at he
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolomorphicNearIdLower
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

namespace Biholomorph
open Set Filter Topology Metric
variable {n : ℕ} {U : Set (Affine n)}

theorem powers_eventually_mem_nhds_of_vanishing_normalized_displacement
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0≤h i) (N : ι → ℕ) {T : ℝ} (hT : 0<T)
    (hNT : ∀ i, (N i:ℝ)*h i≤T) (p : U) {R : ℝ} (hR : 0<R)
    (hRU : closedBall p.val R⊆U)
    (hstep : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ y∈closedBall p.val R,
      ‖(q i).ambientAut y-y‖≤ε*h i)
    (W : Set (Biholomorph U U)) (hW : W∈𝓝 1) :
    ∀ᶠ i in l, ∀ j≤N i, (q i)^j∈W := by
  let J := {z : ι × ℕ // z.2≤N z.1}
  let π : J → ι := fun z => z.val.1
  let k : Filter J := comap π l
  have hπ : Function.Surjective π := fun i => ⟨⟨(i,0),Nat.zero_le _⟩,rfl⟩
  have : NeBot k := (inferInstance : NeBot l).comap_of_surj hπ
  have hcπ : Tendsto π k l := tendsto_comap
  have hN' (z : J) : (z.val.2:ℝ)*h (π z)≤T :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr z.property) (hp (π z))).trans (hNT (π z))
  have ht := powers_tendsto_one_of_vanishing_normalized_displacement hU hc hbd Γ hhol k
    (fun z => q (π z)) (fun z => h (π z)) (fun z => hp (π z)) (fun z => z.val.2) hT hN' p hR hRU (by
      intro ε hε
      exact hcπ.eventually (hstep ε hε))
  have he := ht.eventually hW
  obtain ⟨S,hS,hsub⟩ := mem_comap.mp he
  filter_upwards [hS] with i hi
  intro j hj
  exact hsub (show π ⟨(i,j),hj⟩∈S from hi)
end Biholomorph

open Set Filter Metric Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem holomorphic_near_id_lower_dist {g : E → E} {p : E} {R : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball p R))
    (hb : ∀ x ∈ ball p R, ‖g x-x‖ ≤ R/16) : ∀ x∈ball p (R/4), ∀ y∈ball p (R/4), dist x y≤2*dist (g x) (g y) := by
  intro x hx y hy
  let h : E → E := fun z => g z-z
  have hsub : ball x (R/2) ⊆ ball p R := by
    intro z hz
    rw [mem_ball] at *
    exact (dist_triangle z x p).trans_lt (by linarith)
  have hdiff : DifferentiableOn ℂ h (ball x (R/2)) :=
    (hg.sub differentiableOn_id).mono hsub
  have hm : MapsTo h (ball x (R/2)) (closedBall (h x) (R/8)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      have hz' := hb z (hsub hz)
      have hx' := hb x (ball_subset_ball (by linarith) hx)
      dsimp [h]
      linarith)
  have hyx : y ∈ ball x (R/2) := by
    rw [mem_ball] at *
    exact (dist_triangle y p x).trans_lt (by rw [dist_comm p x]; linarith)
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hm hyx
  have hc : (R/8)/(R/2)=(1/4 : ℝ) := by field_simp [ne_of_gt hR]; ring
  rw [hc] at hs
  have he : y-x=(g y-g x)-(h y-h x) := by dsimp [h]; abel
  have hdist : dist y x≤dist (g y) (g x)+dist (h y) (h x) := by
    rw [dist_eq_norm y x,he]
    simpa only [dist_eq_norm] using norm_sub_le (g y-g x) (h y-h x)
  rw [dist_comm y x] at hs
  rw [dist_comm y x,dist_comm (g y) (g x)] at hdist
  linarith [dist_nonneg (x := g x) (y := g y)]
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalizedDisplacementZeroUniform
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma iterateAverage_sub_id_bound_finite {f : E → E} {T : Set E} {ε : ℝ}
    (N : ℕ) (he : ∀ j≤N, ∀ x ∈ T, ‖f^[j] x-x‖ ≤ ε) {x : E} (hx : x ∈ T) :
    ‖iterateAverage f N x-x‖ ≤ ε := by
  have hn : (N+1 : ℝ) ≠ 0 := by positivity
  have hnC : (N+1 : ℂ) ≠ 0 := by exact_mod_cast hn
  have heq : iterateAverage f N x-x =
      (N+1 : ℂ)⁻¹ • ∑ j ∈ Finset.range (N+1), (f^[j] x-x) := by
    rw [Finset.sum_sub_distrib,smul_sub]
    simp only [Finset.sum_const,Finset.card_range,← Nat.cast_smul_eq_nsmul ℂ,
      Nat.cast_add,Nat.cast_one,smul_smul,inv_mul_cancel₀ hnC,one_smul,iterateAverage]
  rw [heq,norm_smul,norm_inv]
  rw [show (N : ℂ)+1 = ((N+1 : ℕ) : ℂ) by push_cast; rfl,Complex.norm_natCast]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    ((N : ℝ)+1)⁻¹ * ‖∑ j ∈ Finset.range (N+1), (f^[j] x-x)‖ ≤
        ((N : ℝ)+1)⁻¹ * ∑ j ∈ Finset.range (N+1), ‖f^[j] x-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((N : ℝ)+1)⁻¹ * ∑ _j ∈ Finset.range (N+1), ε := by
      gcongr with j hj
      exact he j (by have := Finset.mem_range.mp hj; omega) x hx
    _ = ε := by simp [hn]

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem displacement_set_mem_nhds_one [LocallyCompactSpace U]
    (K : Set (Affine n)) (hK : IsCompact K) (hKU : K⊆U) {ε : ℝ} (hε : 0<ε) :
    {a : Biholomorph U U | ∀ x∈K, ‖a.ambientAut x-x‖<ε}∈𝓝 1 := by
  have hconv := ambientAut_tendstoLocallyUniformly
    (show Tendsto (id : Biholomorph U U → Biholomorph U U) (𝓝 1) (𝓝 1) from tendsto_id)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hconv.mono hKU)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with a ha
  intro x hx
  simpa only [id_eq,ambientAut_apply 1 ⟨x,hKU hx⟩,one_apply,dist_eq_norm,norm_sub_rev] using ha x hx

theorem normalized_displacement_zero_of_uniform_small_powers
    (hU : IsOpen U) [LocallyCompactSpace U]
    {ι : Type*} (l : Filter ι) (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0<h i) (N : ι → ℕ)
    (hNH : ∀ᶠ i in l, 1≤((N i+1:ℕ):ℝ)*h i)
    (hpow : ∀ W : Set (Biholomorph U U), W∈𝓝 1 →
      ∀ᶠ i in l, ∀ j≤N i+1, (q i)^j∈W) :
    TendstoLocallyUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x))
      (fun _ => 0) l U := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro p hpU
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hpU)
  refine ⟨ball p (r/8),mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p (by positivity)),?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let d : ℝ := min (r/16) (ε/4)
  have hd : 0<d := lt_min (by positivity) (by positivity)
  let W : Set (Biholomorph U U) := {a | ∀ x∈closedBall p r, ‖a.ambientAut x-x‖<d}
  have hW : W∈𝓝 1 := displacement_set_mem_nhds_one _ (isCompact_closedBall _ _) hrU hd
  filter_upwards [hNH,hpow W hW] with i hi hpi
  intro x hx
  have hxR : x∈closedBall p r := ball_subset_closedBall (ball_subset_ball (by linarith) hx)
  have hclose (j : ℕ) (hj : j≤N i+1) (z : Affine n) (hz : z∈closedBall p r) :
      ‖((q i).ambientAut^[j]) z-z‖<d := by
    have hv := hpi j hj z hz
    simpa only [ambientAut_iterate (p := ⟨z,hrU hz⟩),ambientAut_apply (p := ⟨z,hrU hz⟩)] using hv
  let F : Affine n → Affine n := iterateAverage (q i).ambientAut (N i)
  have hm : MapsTo (q i).ambientAut U U := fun z hz => by
    rw [ambientAut_apply (q i) ⟨z,hz⟩]
    exact ((q i).toHomeomorph ⟨z,hz⟩).property
  have hFd : DifferentiableOn ℂ F (ball p r) :=
    (iterateAverage_analytic ((q i).ambientAut_analytic hU) hm (N i)).differentiableOn.mono (ball_subset_closedBall.trans hrU)
  have hFb (z : Affine n) (hz : z∈ball p r) : ‖F z-z‖ ≤ r/16 := by
    have he : ∀ j≤N i, ∀ y∈ball p r, ‖((q i).ambientAut^[j]) y-y‖≤d := by
      intro j hj y hy
      exact (hclose j (by omega) y (ball_subset_closedBall hy)).le
    exact (iterateAverage_sub_id_bound_finite (N i) he hz).trans (min_le_left _ _)
  have hqx : (q i).ambientAut x∈ball p (r/4) := by
    have hh := hclose 1 (by omega) x hxR
    simp only [Function.iterate_one] at hh
    have hb : d ≤ r/16 := min_le_left _ _
    exact (dist_triangle ((q i).ambientAut x) x p).trans_lt (by rw [dist_eq_norm]; linarith [mem_ball.mp hx])
  have hl := holomorphic_near_id_lower_dist hr hFd hFb x
    (ball_subset_ball (by linarith) hx) ((q i).ambientAut x) hqx
  have hmean : dist (F x) (F ((q i).ambientAut x)) =
      (((N i+1:ℕ):ℝ))⁻¹ * ‖((q i).ambientAut^[N i+1]) x-x‖ := by
    rw [dist_eq_norm,norm_sub_rev,iterateAverage_coboundary]
    rw [norm_smul,norm_inv]
    congr 1
    rw [show (N i:ℂ)+1=((N i+1:ℕ):ℂ) by push_cast; rfl,Complex.norm_natCast]
  rw [hmean,dist_eq_norm,norm_sub_rev] at hl
  have hhclose : ‖((q i).ambientAut^[N i+1]) x-x‖<ε/4 := (hclose _ le_rfl x hxR).trans_le (min_le_right _ _)
  have he : ((h i)⁻¹ * (((N i+1:ℕ):ℝ))⁻¹)≤1 := by
    rw [← mul_inv_rev]
    exact inv_le_one_of_one_le₀ hi
  rw [dist_eq_norm,zero_sub,norm_neg,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hp i)]
  calc
    _ ≤ (h i)⁻¹*(2*((((N i+1:ℕ):ℝ))⁻¹*‖((q i).ambientAut^[N i+1]) x-x‖)) :=
      mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr (hp i).le)
    _ = 2*((h i)⁻¹*(((N i+1:ℕ):ℝ))⁻¹)*‖((q i).ambientAut^[N i+1]) x-x‖ := by ring
    _ ≤ 2*‖((q i).ambientAut^[N i+1]) x-x‖ := by
      nlinarith [norm_nonneg (((q i).ambientAut^[N i+1]) x-x)]
    _ < ε := by linarith
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalizedAutomorphismsHaveNonzero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem normalized_displacement_zero_of_local_zero
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0<h i) (hh : Tendsto h l (𝓝 0))
    (p : U) {R : ℝ} (hR : 0<R) (hRU : closedBall p.val R⊆U)
    (hstep : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ y∈closedBall p.val R,
      ‖(q i).ambientAut y-y‖≤ε*h i) :
    TendstoLocallyUniformlyOn (fun i x => (h i)⁻¹ • ((q i).ambientAut x-x))
      (fun _ => 0) l U := by
  let N : ι → ℕ := fun i => ⌊1/h i⌋₊
  let M : ι → ℕ := fun i => if h i≤1 then N i+1 else 0
  have hM (i : ι) : (M i:ℝ)*h i≤2 := by
    dsimp [M]
    split_ifs with hi
    · have hn : (N i:ℝ)*h i≤1 :=
        (le_div_iff₀ (hp i)).mp (Nat.floor_le (div_nonneg zero_le_one (hp i).le))
      push_cast
      nlinarith
    · simp
  have hhi : ∀ᶠ i in l, h i≤1 := (hh.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ hi => hi.le)
  apply normalized_displacement_zero_of_uniform_small_powers hU l q h hp N
  · exact Eventually.of_forall (fun i => by
      have hn := (div_lt_iff₀ (hp i)).mp (Nat.lt_floor_add_one (1/h i))
      dsimp [N]
      push_cast
      exact hn.le)
  · intro W hW
    have he := powers_eventually_mem_nhds_of_vanishing_normalized_displacement hU hc hbd Γ hhol l q h
      (fun i => (hp i).le) M (by norm_num : (0:ℝ)<2) hM p hR hRU hstep W hW
    filter_upwards [he,hhi] with i hi hhi
    simpa only [M,ite_eq_left hhi] using hi

theorem normalized_automorphisms_have_nonzero_complete_limit
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (q : ℕ → Biholomorph U U) (h : ℕ → ℝ) (hp : ∀ i, 0<h i)
    (hh : Tendsto h atTop (𝓝 0)) (p : U) {R : ℝ} (hR : 0<R)
    (hRU : closedBall p.val R⊆U)
    (hbound : ∀ i, ∀ x∈closedBall p.val R, ‖(q i).ambientAut x-x‖≤h i)
    (hmax : ∀ i, ∃ x∈closedBall p.val R, h i≤‖(q i).ambientAut x-x‖) :
    ∃ X : Affine n → Affine n, IsCompleteGenerator U X ∧ X≠0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun i x => (h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)) X atTop (ball p.val R) := by
  let f : ℕ → Affine n → Affine n := fun i x => (h i)⁻¹ • ((q i).ambientAut x-x)
  have hfd (i : ℕ) : DifferentiableOn ℂ (f i) U := by
    intro x hx
    exact ((((q i).ambientAut_analytic hU x hx).differentiableAt.sub
      differentiableAt_id).const_smul (h i)⁻¹).differentiableWithinAt
  have hfb (i : ℕ) (x : Affine n) (hx : x∈closedBall p.val R) : ‖f i x‖≤1 := by
    dsimp [f]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hp i)]
    calc
      _ ≤ (h i)⁻¹*h i := mul_le_mul_of_nonneg_left (hbound i x hx) (inv_nonneg.mpr (hp i).le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (hp i))
  obtain ⟨F,hFd,φ,hφ,hconv⟩ := montel_expanding_domains isOpen_ball f (by
    intro x hx
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
    exact ⟨r,hr,1,zero_lt_one,hrsub,Eventually.of_forall (fun i =>
      ⟨(hfd i).mono (hrsub.trans (ball_subset_closedBall.trans hRU)),
       fun y hy => hfb i y (ball_subset_closedBall (hrsub hy))⟩)⟩)
  have hFa : AnalyticOnNhd ℂ F (ball p.val R) := analyticOnNhd_of_differentiableOn_affine isOpen_ball hFd
  obtain ⟨H,hH0,hHc,hHm,hHF⟩ := normalized_automorphism_local_limit_complete hU hc hbd Γ hhol atTop
    (q ∘ φ) (h ∘ φ) (fun i => hp (φ i)) (hh.comp hφ.tendsto_atTop)
    (ball p.val R) isOpen_ball (convex_ball p.val R).isPreconnected (ball_subset_closedBall.trans hRU)
    p (mem_ball_self hR) F hFa hconv
  let X := infinitesimalGenerator H
  have hX : IsCompleteGenerator U X := ⟨H,hHc,hH0,hHm,rfl⟩
  refine ⟨X,hX,?_,φ,hφ,hconv.congr_right (fun x hx => (hHF hx).symm)⟩
  intro hzero
  have hFzero : EqOn F (fun _ => 0) (ball p.val R) := by
    intro x hx
    rw [← hHF hx]
    change X x=0
    rw [hzero]
    rfl
  have hz := hconv.congr_right hFzero
  have hsmall : closedBall p.val (R/2)⊆ball p.val R := closedBall_subset_ball (half_lt_self hR)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall p.val (R/2))).mp (hz.mono hsmall)
  have hstep : ∀ ε : ℝ, 0<ε → ∀ᶠ i in atTop, ∀ y∈closedBall p.val (R/2),
      ‖(q (φ i)).ambientAut y-y‖≤ε*h (φ i) := by
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with i hi
    intro y hy
    have he : (q (φ i)).ambientAut y-y=h (φ i) • f (φ i) y := by
      dsimp [f]
      rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (hp (φ i))),one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (hp (φ i))]
    have hv : ‖f (φ i) y‖≤ε := le_of_lt (by simpa only [dist_eq_norm,zero_sub,norm_neg] using hi y hy)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hv (hp (φ i)).le
  have hg := normalized_displacement_zero_of_local_zero hU hc hbd Γ hhol atTop (q ∘ φ) (h ∘ φ)
    (fun i => hp (φ i)) (hh.comp hφ.tendsto_atTop) p (half_pos hR)
    (hsmall.trans (ball_subset_closedBall.trans hRU)) hstep
  have hgu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall p.val R)).mp (hg.mono hRU)
  obtain ⟨i,hi⟩ := (Metric.tendstoUniformlyOn_iff.mp hgu 1 zero_lt_one).exists
  obtain ⟨x,hx,hmaxx⟩ := hmax (φ i)
  have hi' : ‖(h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)‖<1 := by
    simpa only [Function.comp_apply,dist_eq_norm,zero_sub,norm_neg] using hi x hx
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hp (φ i))] at hi'
  have hl : 1≤(h (φ i))⁻¹*‖(q (φ i)).ambientAut x-x‖ := by
    calc
      1 = (h (φ i))⁻¹*h (φ i) := (inv_mul_cancel₀ (ne_of_gt (hp (φ i)))).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmaxx (inv_nonneg.mpr (hp (φ i)).le)
  exact (not_lt_of_ge hl) hi'
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SmallAutomorphismsHaveNonzero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem exists_displacement_maximum_normalization
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (q : ℕ → Biholomorph U U) (hq : Tendsto q atTop (𝓝 1)) (hne : ∀ i, q i≠1)
    (p : U) {R : ℝ} (hR : 0<R) (hRU : closedBall p.val R⊆U) :
    ∃ h : ℕ → ℝ, (∀ i, 0<h i) ∧ Tendsto h atTop (𝓝 0) ∧
      (∀ i, ∀ x∈closedBall p.val R, ‖(q i).ambientAut x-x‖≤h i) ∧
      (∀ i, ∃ x∈closedBall p.val R, h i≤‖(q i).ambientAut x-x‖) := by
  have hm (i : ℕ) : ∃ x∈closedBall p.val R,
      ∀ y∈closedBall p.val R, ‖(q i).ambientAut y-y‖≤‖(q i).ambientAut x-x‖ :=
    (isCompact_closedBall p.val R).exists_isMaxOn ⟨p.val,mem_closedBall_self hR.le⟩
      ((((q i).ambientAut_analytic hU).continuousOn.sub continuousOn_id).norm.mono hRU)
  choose x hxb hxm using hm
  let h : ℕ → ℝ := fun i => ‖(q i).ambientAut (x i)-x i‖
  have hp (i : ℕ) : 0<h i := by
    by_contra hn
    have hz : h i=0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    apply hne i
    apply eq_of_ambientAut_eventuallyEq hU hc p
    filter_upwards [closedBall_mem_nhds p.val hR] with y hy
    have hz' : ‖(q i).ambientAut (x i)-x i‖=0 := hz
    have hy0 : (q i).ambientAut y=y := sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [hz'] using hxm i y hy) (norm_nonneg _)))
    rw [hy0,ambientAut_apply 1 ⟨y,hRU hy⟩,one_apply]
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall p.val R)).mp
    ((ambientAut_tendstoLocallyUniformly hq).mono hRU)
  have ht : Tendsto h atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with i hi
    have hb := hi (x i) (hxb i)
    rw [dist_eq_norm,sub_zero,Real.norm_eq_abs,abs_of_pos (hp i)]
    rw [ambientAut_apply 1 ⟨x i,hRU (hxb i)⟩,one_apply,dist_eq_norm,norm_sub_rev] at hb
    exact hb
  exact ⟨h,hp,ht,hxm,fun i => ⟨x i,hxb i,le_rfl⟩⟩

theorem small_automorphisms_have_nonzero_complete_tangent
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (q : ℕ → Biholomorph U U) (hq : Tendsto q atTop (𝓝 1)) (hne : ∀ i, q i≠1)
    (p : U) {R : ℝ} (hR : 0<R) (hRU : closedBall p.val R⊆U) :
    ∃ h : ℕ → ℝ, (∀ i, 0<h i) ∧ Tendsto h atTop (𝓝 0) ∧
      ∃ X : Affine n → Affine n, IsCompleteGenerator U X ∧ X≠0 ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun i x => (h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)) X atTop (ball p.val R) := by
  obtain ⟨h,hp,hh,hbound,hmax⟩ := exists_displacement_maximum_normalization hU hc q hq hne p hR hRU
  exact ⟨h,hp,hh,normalized_automorphisms_have_nonzero_complete_limit hU hc hbd Γ hhol q h hp hh p hR hRU hbound hmax⟩
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectedJetSequencesNot
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem ambientFirstJet_continuous (hU : IsOpen U) [LocallyCompactSpace U] (p : U) :
    Continuous (ambientFirstJet p) := by
  have hv : Continuous (fun a : Biholomorph U U => a.ambientAut p.val) := by
    simpa only [Function.comp_def,ambientAut_apply] using continuous_subtype_val.comp (continuous_evaluation p)
  exact hv.prodMk (derivativeAt_continuous hU p)

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (p : U)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU hc hbd Γ hhol

theorem projected_jet_sequences_not_coincident
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] E)
    (hP : ∀ X : Affine n → Affine n, IsCompleteGenerator U X →
      P (X p.val,fderiv ℂ X p.val)=0 → X=0)
    (a b : ℕ → Biholomorph U U) (ha : Tendsto a atTop (𝓝 1))
    (hb : Tendsto b atTop (𝓝 1)) (hne : ∀ i, a i≠b i)
    (heq : ∀ i, P (ambientFirstJet p (a i))=P (ambientFirstJet p (b i))) : False := by
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds p.property)
  let q : ℕ → Biholomorph U U := fun i => a i*(b i)⁻¹
  have hq : Tendsto q atTop (𝓝 1) := by simpa only [mul_one,inv_one] using ha.mul hb.inv
  have hqne (i : ℕ) : q i≠1 := by
    intro he
    apply hne i
    calc
      a i = q i*b i := by simp [q]
      _ = b i := by rw [he,one_mul]
  obtain ⟨h,hp,hh,X,hX,hXne,φ,hφ,hconv⟩ := small_automorphisms_have_nonzero_complete_tangent
    hU hc hbd Γ hhol q hq hqne p hR hRU
  let y : ℕ → U := fun i => (b (φ i)).toHomeomorph p
  have hy : Tendsto (fun i => (y i).val) atTop (𝓝 p.val) := by
    simpa only [Function.comp_def,one_apply,y] using
      (continuous_subtype_val.comp (continuous_evaluation p)).continuousAt.tendsto.comp (hb.comp hφ.tendsto_atTop)
  have hyb : Tendsto (fun i => (y i).val) atTop (𝓝[ball p.val R] p.val) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy,hy (ball_mem_nhds _ hR)⟩
  let f : ℕ → Affine n → Affine n := fun i x => (h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)
  have hfd (i : ℕ) : DifferentiableOn ℂ (f i) U := by
    intro x hx
    exact ((((q (φ i)).ambientAut_analytic hU x hx).differentiableAt.sub differentiableAt_id).const_smul (h (φ i))⁻¹).differentiableWithinAt
  have hder := tendstoLocallyUniformlyOn_fderiv isOpen_ball hconv
    (fun x hx => ⟨ball p.val R,isOpen_ball.mem_nhds hx,Eventually.of_forall
      (fun i => (hfd i).mono (ball_subset_closedBall.trans hRU))⟩)
  have hXa := hX.analyticOnNhd hU hbd
  have hval := hconv.tendsto_comp (hXa p.val p.property).continuousAt.continuousWithinAt (mem_ball_self hR) hyb
  have hd := hder.tendsto_comp (hXa p.val p.property).fderiv.continuousAt.continuousWithinAt (mem_ball_self hR) hyb
  have hDb : Tendsto (fun i => (b (φ i)).derivativeAt p) atTop (𝓝 1) := by
    simpa only [Function.comp_def,derivativeAt_one hU] using
      (derivativeAt_continuous hU p).continuousAt.tendsto.comp (hb.comp hφ.tendsto_atTop)
  have hcomp : Continuous (fun z : (Affine n →L[ℂ] Affine n) × (Affine n →L[ℂ] Affine n) => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  have hj := hval.prodMk_nhds (hcomp.continuousAt.tendsto.comp (hd.prodMk_nhds hDb))
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id] at hj
  have hv (i : ℕ) : f i (y i).val=(h (φ i))⁻¹ • ((a (φ i)).ambientAut p.val-(b (φ i)).ambientAut p.val) := by
    have hab : q (φ i)*b (φ i)=a (φ i) := by simp [q]
    dsimp only [f]
    rw [ambientAut_apply (q (φ i)) (y i),ambientAut_apply (b (φ i)) p]
    congr 2
    change ((q (φ i)*b (φ i)).toHomeomorph p).val=(a (φ i)).ambientAut p.val
    rw [hab,ambientAut_apply]
  have hD (i : ℕ) : (fderiv ℂ (f i) (y i).val).comp ((b (φ i)).derivativeAt p)=
      (h (φ i))⁻¹ • ((a (φ i)).derivativeAt p-(b (φ i)).derivativeAt p) := by
    have hab : q (φ i)*b (φ i)=a (φ i) := by simp [q]
    have hmul := derivativeAt_mul hU (q (φ i)) (b (φ i)) p
    rw [hab] at hmul
    change (fderiv ℂ ((h (φ i))⁻¹ • ((q (φ i)).ambientAut-id)) (y i).val).comp ((b (φ i)).derivativeAt p) = _
    rw [fderiv_const_smul (((q (φ i)).ambientAut_analytic hU (y i).val (y i).property).differentiableAt.sub differentiableAt_id),
      fderiv_sub ((q (φ i)).ambientAut_analytic hU (y i).val (y i).property).differentiableAt differentiableAt_id,fderiv_id]
    simp only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.sub_comp,ContinuousLinearMap.id_comp]
    change (a (φ i)).derivativeAt p=(fderiv ℂ (q (φ i)).ambientAut (y i).val).comp ((b (φ i)).derivativeAt p) at hmul
    rw [←hmul]
  have hj' : Tendsto (fun i => (h (φ i))⁻¹ • (ambientFirstJet p (a (φ i))-ambientFirstJet p (b (φ i))))
      atTop (𝓝 (X p.val,fderiv ℂ X p.val)) := by
    convert hj using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    exact Prod.ext (hv i).symm (hD i).symm
  have ht := P.continuous.continuousAt.tendsto.comp hj'
  have hz (i : ℕ) : P ((h (φ i))⁻¹ • (ambientFirstJet p (a (φ i))-ambientFirstJet p (b (φ i))))=0 := by
    rw [map_smul,map_sub,heq,sub_self,smul_zero]
  simp only [Function.comp_def,hz] at ht
  exact hXne (hP X hX (tendsto_nhds_unique ht tendsto_const_nhds))
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompleteGeneratorJetProjection
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (p : U)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU hc hbd Γ hhol

theorem projected_firstJet_locally_injective
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] E)
    (hP : ∀ X : Affine n → Affine n, IsCompleteGenerator U X →
      P (X p.val,fderiv ℂ X p.val)=0 → X=0) :
    ∃ W : Set (Biholomorph U U), W∈𝓝 1 ∧ Set.InjOn (fun a => P (ambientFirstJet p a)) W := by
  classical
  by_contra hn
  let W : ℕ → Set (Biholomorph U U) := fun i =>
    firstJet p ⁻¹' ball (firstJet p 1) (1/((i:ℝ)+1))
  have hW (i : ℕ) : W i∈𝓝 1 := (firstJet_continuous hU p).continuousAt.preimage_mem_nhds
    (ball_mem_nhds _ (by positivity))
  have hex (i : ℕ) : ∃ a∈W i, ∃ b∈W i,
      P (ambientFirstJet p a)=P (ambientFirstJet p b) ∧ a≠b := by
    have hi : ¬Set.InjOn (fun a => P (ambientFirstJet p a)) (W i) := fun hi => hn ⟨W i,hW i,hi⟩
    unfold Set.InjOn at hi
    push Not at hi
    exact hi
  choose a ha b hb he hne using hex
  have hv (q : ℕ → Biholomorph U U) (hq : ∀ i, q i∈W i) : Tendsto q atTop (𝓝 1) := by
    apply (firstJet_isClosedEmbedding hU hc hbd Γ hhol p).isEmbedding.isInducing.tendsto_nhds_iff.mpr
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun i => (hq i).le) tendsto_one_div_add_atTop_nhds_zero_nat
  exact projected_jet_sequences_not_coincident hU hc hbd Γ hhol p P hP a b (hv a ha) (hv b hb) hne he

omit hc in

theorem exists_complete_generator_jet_projection (hc' : IsConnected U) :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc' hbd Γ hhol p),
      (∀ X : completeGeneratorSpace hU hc' hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc' hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc' hbd Γ hhol p X) ∧
      (∀ X : Affine n → Affine n, IsCompleteGenerator U X →
        P (X p.val,fderiv ℂ X p.val)=0 → X=0) := by
  classical
  let J := completeGeneratorFirstJet hU hc' hbd Γ hhol p
  obtain ⟨K,hK⟩ := (LinearMap.range J).exists_isCompl
  let P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] LinearMap.range J :=
    ⟨(LinearMap.range J).projectionOnto K hK,
      LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) (E := Affine n × (Affine n →L[ℂ] Affine n))
        (F' := LinearMap.range J) ((LinearMap.range J).projectionOnto K hK)⟩
  refine ⟨P,?_,?_⟩
  · intro X
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_of_mem_left hK ⟨X,rfl⟩)
  · intro X hX hz
    have hJ : J ⟨X,hX⟩=0 := by
      have he := Submodule.projectionOnto_apply_of_mem_left hK (show J ⟨X,hX⟩∈LinearMap.range J from ⟨⟨X,hX⟩,rfl⟩)
      have hp : P (J ⟨X,hX⟩)=0 := hz
      have hpv := congrArg Subtype.val hp
      change ((J.range.projectionOnto K hK) (J ⟨X,hX⟩)).val=0 at hpv
      rw [he] at hpv
      exact hpv
    have hx0 : (⟨X,hX⟩ : completeGeneratorSpace hU hc' hbd Γ hhol)=0 :=
      (completeGeneratorFirstJet_injective hU hc' hbd Γ hhol p) (by simpa only [map_zero] using hJ)
    exact congrArg Subtype.val hx0
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterDerivativeJoint
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem ambientAut_second_derivative_joint_continuousAt {q : Biholomorph U U × Affine n} (hq : q.2∈U) :
    ContinuousAt (fun z : Biholomorph U U × Affine n => fderiv ℂ (fderiv ℂ z.1.ambientAut) z.2) q := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro z hz
  have ha := continuous_fst.tendsto q |>.comp hz
  have hx := continuous_snd.tendsto q |>.comp hz
  have hxu : Tendsto (fun j => (z j).2) atTop (𝓝[U] q.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx,hx (hU.mem_nhds hq)⟩
  have hf := tendstoLocallyUniformlyOn_fderiv hU (ambientAut_tendstoLocallyUniformly ha)
    (fun x hx => ⟨U,hU.mem_nhds hx,Eventually.of_forall
      (fun j => ((z j).1.ambientAut_analytic hU).differentiableOn)⟩)
  have hf2 := tendstoLocallyUniformlyOn_fderiv hU hf
    (fun x hx => ⟨U,hU.mem_nhds hx,Eventually.of_forall
      (fun j y hy => ((z j).1.ambientAut_analytic hU y hy).fderiv.differentiableAt.differentiableWithinAt)⟩)
  exact hf2.tendsto_comp (q.1.ambientAut_analytic hU q.2 hq).fderiv.fderiv.continuousAt.continuousWithinAt hq hxu

variable (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
include hbd ha ha0 ham

theorem oneParameter_derivativeAt_hasDerivAt (s : ℝ) (p : U) :
    HasDerivAt (fun t => (a t).derivativeAt p)
      ((fderiv ℂ (infinitesimalGenerator a) ((a s).toHomeomorph p).val).comp ((a s).derivativeAt p)) s := by
  let y : U := (a s).toHomeomorph p
  have hd0 := oneParameter_fderiv_hasDerivAt_zero hU hbd a ha ha0 ham y.val y.property
  have hd0' : HasDerivAt (fun t => (a t).derivativeAt y)
      (fderiv ℂ (infinitesimalGenerator a) y.val) (s-s) := by simpa only [sub_self,derivativeAt] using hd0
  have his : HasDerivAt (fun t : ℝ => t-s) 1 s := by simpa only [id_eq] using (hasDerivAt_id s).sub_const s
  have hdt := hd0'.scomp s (h := fun t : ℝ => t-s) his
  simp only [one_smul] at hdt
  let L := ((ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).flip
    ((a s).derivativeAt p)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt s hdt
  have he (t : ℝ) : (a t).derivativeAt p=((a (t-s)).derivativeAt y).comp ((a s).derivativeAt p) := by
    have hat : a t=a (t-s)*a s := by rw [← ham,sub_add_cancel]
    rw [hat,derivativeAt_mul hU]
  have heq : (fun t => (a t).derivativeAt p)=(fun t => ((a (t-s)).derivativeAt y).comp ((a s).derivativeAt p)) := funext he
  rw [heq]
  exact hd

theorem oneParameter_derivative_joint_hasStrictFDerivAt (s : ℝ) (p : U) :
    HasStrictFDerivAt (fun z : ℝ × Affine n => fderiv ℂ (a z.1).ambientAut z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        ((fderiv ℂ (infinitesimalGenerator a) ((a s).toHomeomorph p).val).comp ((a s).derivativeAt p))).coprod
        ((fderiv ℂ (fderiv ℂ (a s).ambientAut) p.val).restrictScalars ℝ)) (s,p.val) := by
  have hn : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,p.val), z.2∈U :=
    continuous_snd.continuousAt (hU.mem_nhds p.property)
  have hj : ContinuousAt (fun z : ℝ × Affine n => (a z.1).ambientAut z.2) (s,p.val) :=
    (ambientAut_joint_continuousAt hU p.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hdj : ContinuousAt (fun z : ℝ × Affine n => fderiv ℂ (a z.1).ambientAut z.2) (s,p.val) :=
    (ambientAut_derivative_joint_continuousAt hU p.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hddj : ContinuousAt (fun z : ℝ × Affine n => fderiv ℂ (fderiv ℂ (a z.1).ambientAut) z.2) (s,p.val) :=
    (ambientAut_second_derivative_joint_continuousAt hU p.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hXj : ContinuousAt (fun z : ℝ × Affine n => fderiv ℂ (infinitesimalGenerator a) ((a z.1).ambientAut z.2)) (s,p.val) := by
    have hX := (infinitesimalGenerator_analytic hU a ha hbd ha0 ham
      ((a s).toHomeomorph p).val ((a s).toHomeomorph p).property).fderiv.continuousAt
    have hX' : ContinuousAt (fderiv ℂ (infinitesimalGenerator a)) ((a s).ambientAut p.val) := by simpa only [ambientAut_apply] using hX
    exact hX'.comp (x := (s,p.val)) hj
  have ht := hXj.clm_comp hdj
  have h1 : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,p.val), HasFDerivAt
      (fun t => fderiv ℂ (a t).ambientAut z.2)
      (ContinuousLinearMap.toSpanSingleton ℝ ((fderiv ℂ (infinitesimalGenerator a) ((a z.1).ambientAut z.2)).comp (fderiv ℂ (a z.1).ambientAut z.2))) z.1 := by
    filter_upwards [hn] with z hz
    simpa only [ambientAut_apply (a _) ⟨z.2,hz⟩,derivativeAt] using
      (oneParameter_derivativeAt_hasDerivAt hU hbd a ha ha0 ham z.1 ⟨z.2,hz⟩).hasFDerivAt
  have h2 : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,p.val), HasFDerivAt
      (fun y => fderiv ℂ (a z.1).ambientAut y)
      ((fderiv ℂ (fderiv ℂ (a z.1).ambientAut) z.2).restrictScalars ℝ) z.2 := by
    filter_upwards [hn] with z hz
    exact ((a z.1).ambientAut_analytic hU z.2 hz).fderiv.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℝ) (u := (s,p.val)) (f := fun t y => fderiv ℂ (a t).ambientAut y)
    (f₁ := fun t y => ContinuousLinearMap.toSpanSingleton ℝ
      ((fderiv ℂ (infinitesimalGenerator a) ((a t).ambientAut y)).comp (fderiv ℂ (a t).ambientAut y)))
    (f₂ := fun t y => (fderiv ℂ (fderiv ℂ (a t).ambientAut) y).restrictScalars ℝ) h1 h2
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Affine n →L[ℂ] Affine n)).continuous.continuousAt.comp ht)
    ((ContinuousLinearMap.continuous_restrictScalars ℝ).continuousAt.comp hddj)
  dsimp only [Function.HasUncurry.uncurry,Function.hasUncurryInduction,Function.hasUncurryBase,id_eq] at hd
  simpa only [ambientAut_apply,derivativeAt] using hd
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FirstJetFlowMul
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU
omit [LocallyCompactSpace U] in
lemma ambientAut_one_second_fderiv (p : U) :
    fderiv ℂ (fderiv ℂ (1 : Biholomorph U U).ambientAut) p.val=0 := by
  have he : fderiv ℂ (1 : Biholomorph U U).ambientAut =ᶠ[𝓝 p.val]
      (fun _ => (1 : Affine n →L[ℂ] Affine n)) := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    exact derivativeAt_one hU ⟨x,hx⟩
  rw [he.fderiv_eq]
  simp only [fderiv_const_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem firstJet_flow_mul_hasStrictFDerivAt_zero
    (hbd : Bornology.IsBounded U) (p : U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (c : E → Biholomorph U U) (hc0 : c 0=1)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hc : HasStrictFDerivAt (fun t => ambientFirstJet p (c t)) L 0)
    (l : E →L[ℝ] ℝ) :
    HasStrictFDerivAt (fun t => ambientFirstJet p (a (l t)*c t))
      (((ContinuousLinearMap.toSpanSingleton ℝ
        (infinitesimalGenerator a p.val,fderiv ℂ (infinitesimalGenerator a) p.val)).comp l)+L) 0 := by
  have hA := oneParameter_joint_hasStrictFDerivAt hU a ha hbd ha0 ham 0 p
  rw [ha0,one_apply,derivativeAt_one hU] at hA
  have hD := oneParameter_derivative_joint_hasStrictFDerivAt hU hbd a ha ha0 ham 0 p
  rw [ha0,one_apply,derivativeAt_one hU,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id,ambientAut_one_second_fderiv hU] at hD
  have hcval : (c 0).ambientAut p.val=p.val := by rw [hc0,ambientAut_apply,one_apply]
  have hcd : (c 0).derivativeAt p=1 := by rw [hc0,derivativeAt_one hU]
  have hu := l.hasStrictFDerivAt.prodMk hc.fst
  change HasStrictFDerivAt (fun t => (l t,(c t).ambientAut p.val))
    (l.prod ((ContinuousLinearMap.fst ℝ _ _).comp L)) 0 at hu
  have hu0 : (l 0,(c 0).ambientAut p.val)=(0,p.val) := by rw [map_zero,hcval]
  rw [←hu0] at hA hD
  have hAv := hA.comp 0 hu
  have hDv := hD.comp 0 hu
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    (fderiv ℂ (a (l 0)).ambientAut ((c 0).ambientAut p.val),(c 0).derivativeAt p)).comp 0 (hDv.prodMk hc.snd)
  have hpair := hAv.prodMk hB
  have hfun : (fun t => ambientFirstJet p (a (l t)*c t)) =
      (fun t => ((a (l t)).ambientAut ((c t).ambientAut p.val),
        (fderiv ℂ (a (l t)).ambientAut ((c t).ambientAut p.val)).comp ((c t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU (a (l t)) (c t) p
  rw [hfun]
  convert hpair using 1
  · rfl
  apply DFunLike.ext
  intro v
  apply Prod.ext
  · change l v • infinitesimalGenerator a p.val+(L v).1 =
      l v • infinitesimalGenerator a p.val+(L v).1
    rfl
  · change l v • fderiv ℂ (infinitesimalGenerator a) p.val+(L v).2 =
      (fderiv ℂ (a (l 0)).ambientAut ((c 0).ambientAut p.val)).comp ((L v).2) +
      (l v • fderiv ℂ (infinitesimalGenerator a) p.val + (0 : Affine n →L[ℂ] (Affine n →L[ℂ] Affine n)) ((L v).1)).comp ((c 0).derivativeAt p)
    rw [map_zero,ha0,hcval,show fderiv ℂ (1 : Biholomorph U U).ambientAut p.val=1 from derivativeAt_one hU p,hcd]
    simp only [zero_apply,add_zero,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp]
    exact add_comm _ _
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FlowWordFirstJet
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*}

theorem flowWord_zero (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ)
    (ha0 : ∀ i, a i 0=1) (is : List ι) : flowWord a l is 0=1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [flowWord,map_zero,ha0,ih,mul_one]

theorem flowWord_continuous [LocallyCompactSpace U]
    (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ)
    (ha : ∀ i, Continuous (a i)) (is : List ι) : Continuous (flowWord a l is) := by
  induction is with
  | nil => exact continuous_const
  | cons i is ih => exact ((ha i).comp (l i).continuous).mul ih

theorem flowWord_firstJet_hasStrictFDerivAt_zero
    (hU : IsOpen U) [LocallyCompactSpace U] (hbd : Bornology.IsBounded U) (p : U)
    (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ)
    (ha : ∀ i, Continuous (a i)) (ha0 : ∀ i, a i 0=1)
    (ham : ∀ i s t, a i (s+t)=a i s*a i t) (is : List ι) :
    HasStrictFDerivAt (fun t => ambientFirstJet p (flowWord a l is t))
      ((is.map (fun i => (ContinuousLinearMap.toSpanSingleton ℝ
        (infinitesimalGenerator (a i) p.val,fderiv ℂ (infinitesimalGenerator (a i)) p.val)).comp (l i))).sum) 0 := by
  induction is with
  | nil =>
    change HasStrictFDerivAt (fun _ : E => ambientFirstJet p (1 : Biholomorph U U)) 0 0
    exact hasStrictFDerivAt_const _ _
  | cons i is ih =>
    exact firstJet_flow_mul_hasStrictFDerivAt_zero hU hbd p (a i) (ha i) (ha0 i) (ham i)
      (flowWord a l is) (flowWord_zero a l ha0 is) _ ih (l i)
end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_firstJet_flow_mul_strictFDeriv
    (hbd : Bornology.IsBounded U) (p : U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (c : E → Biholomorph U U) (t₀ : E)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hc : HasStrictFDerivAt (fun t => ambientFirstJet p (c t)) L t₀)
    (l : E →L[ℝ] ℝ) :
    ∃ L' : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p (a (l t)*c t)) L' t₀ := by
  have hA := oneParameter_joint_hasStrictFDerivAt hU a ha hbd ha0 ham (l t₀) ((c t₀).toHomeomorph p)
  have hD := oneParameter_derivative_joint_hasStrictFDerivAt hU hbd a ha ha0 ham (l t₀) ((c t₀).toHomeomorph p)
  have hu := l.hasStrictFDerivAt.prodMk hc.fst
  change HasStrictFDerivAt (fun t => (l t,(c t).ambientAut p.val))
    (l.prod ((ContinuousLinearMap.fst ℝ _ _).comp L)) t₀ at hu
  have hu0 : (l t₀,(c t₀).ambientAut p.val)=(l t₀,((c t₀).toHomeomorph p).val) := by rw [ambientAut_apply]
  rw [←hu0] at hA hD
  have hAv := hA.comp t₀ hu
  have hDv := hD.comp t₀ hu
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    (fderiv ℂ (a (l t₀)).ambientAut ((c t₀).ambientAut p.val),(c t₀).derivativeAt p)).comp t₀ (hDv.prodMk hc.snd)
  have hpair := hAv.prodMk hB
  have hfun : (fun t => ambientFirstJet p (a (l t)*c t)) =
      (fun t => ((a (l t)).ambientAut ((c t).ambientAut p.val),
        (fderiv ℂ (a (l t)).ambientAut ((c t).ambientAut p.val)).comp ((c t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU (a (l t)) (c t) p
  rw [hfun]
  exact ⟨_,hpair⟩

theorem flowWord_exists_firstJet_strictFDeriv {ι : Type*}
    (hbd : Bornology.IsBounded U) (p : U)
    (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ)
    (ha : ∀ i, Continuous (a i)) (ha0 : ∀ i, a i 0=1)
    (ham : ∀ i s t, a i (s+t)=a i s*a i t) (is : List ι) (t₀ : E) :
    ∃ L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p (flowWord a l is t)) L t₀ := by
  induction is with
  | nil =>
    refine ⟨0,?_⟩
    change HasStrictFDerivAt (fun _ : E => ambientFirstJet p (1 : Biholomorph U U)) 0 t₀
    exact hasStrictFDerivAt_const _ _
  | cons i is ih =>
    obtain ⟨L,hL⟩ := ih
    exact exists_firstJet_flow_mul_strictFDeriv hU hbd p (a i) (ha i) (ha0 i) (ham i)
      (flowWord a l is) t₀ L hL (l i)
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteFlowParametrization
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (p : U)
include hU hc hbd Γ hhol

theorem exists_finite_flow_parametrization_with_regular_jets
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
    (hP : ∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) :
    ∃ F : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) → Biholomorph U U,
      Continuous F ∧ F 0=1 ∧
      HasStrictFDerivAt (fun t => P (ambientFirstJet p (F t)))
        (ContinuousLinearMap.id ℝ _) 0 ∧
      HasStrictFDerivAt (𝕜 := ℝ) (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
        (F := Affine n × (Affine n →L[ℂ] Affine n)) (fun t => ambientFirstJet p (F t))
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)).subtypeL 0 ∧
      ∀ (p' : U) (t₀ : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
        ∃ L : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) →L[ℝ]
          (Affine n × (Affine n →L[ℂ] Affine n)),
          HasStrictFDerivAt (𝕜 := ℝ) (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
            (F := Affine n × (Affine n →L[ℂ] Affine n)) (fun t => ambientFirstJet p' (F t)) L t₀ := by
  classical
  let J := completeGeneratorFirstJet hU hc hbd Γ hhol p
  let R : Type := ↥(LinearMap.range J)
  let _ : Module.Free ℝ R := Module.Free.of_divisionRing ℝ R
  let _ : AddCommMonoid (R →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n))) := ContinuousLinearMap.addCommMonoid
  let d := Module.finrank ℝ R
  let b : Module.Basis (Fin d) ℝ R := Module.finBasis ℝ R
  have hex (i : Fin d) : ∃ X : completeGeneratorSpace hU hc hbd Γ hhol,
      J X=(b i).val := (b i).property
  choose X hX using hex
  have hflow (i : Fin d) := (X i).property
  choose a ha ha0 ham hgen using hflow
  let l : Fin d → R →L[ℝ] ℝ := fun i =>
    ⟨b.coord i, LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) (E := R) (F' := ℝ) (b.coord i)⟩
  let is : List (Fin d) := List.ofFn id
  let F : R → Biholomorph U U := flowWord (E := R) a l is
  let L : R →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)) :=
    (is.map (fun i => (ContinuousLinearMap.toSpanSingleton ℝ
      (infinitesimalGenerator (a i) p.val,fderiv ℂ (infinitesimalGenerator (a i)) p.val)).comp (l i))).sum
  have hf : HasStrictFDerivAt (fun t => ambientFirstJet p (F t)) L 0 :=
    flowWord_firstJet_hasStrictFDerivAt_zero (E := R) hU hbd p a l ha ha0 ham is
  have hL : L=J.range.subtypeL := by
    apply DFunLike.ext
    intro v
    change L v=v.val
    dsimp only [L,is]
    rw [List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply,id_eq,sum_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply]
    have he (i : Fin d) : (infinitesimalGenerator (a i) p.val,
        fderiv ℂ (infinitesimalGenerator (a i)) p.val)=(b i).val := by
      rw [hgen i]
      exact hX i
    simp_rw [he]
    have hv := congrArg J.range.subtype (b.sum_repr v)
    rw [map_sum] at hv
    simp only [map_smul] at hv
    exact hv
  rw [hL] at hf
  have hPc := ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R) (x := ambientFirstJet p (F 0)) P
  have hp := HasStrictFDerivAt.comp (𝕜 := ℝ) (E := R) (F := Affine n × (Affine n →L[ℂ] Affine n)) (G := R) 0 hPc hf
  have hPL : P.comp J.range.subtypeL=ContinuousLinearMap.id ℝ R := by
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    change (P v.val).val=v.val
    obtain ⟨X,hXv⟩ := v.property
    rw [←hXv]
    exact hP X
  rw [hPL] at hp
  refine ⟨F,flowWord_continuous (E := R) a l ha is,flowWord_zero (E := R) a l ha0 is,hp,hf,?_⟩
  intro p' t₀
  exact flowWord_exists_firstJet_strictFDeriv (E := R) hU hbd p' a l ha ha0 ham is t₀

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectedChartObservableCont
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

section
open Set Filter Topology Metric
open scoped NNReal

theorem continuous_differential_of_everywhere_strict
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E → E →L[ℝ] F)
    (hD : ∀ x, HasStrictFDerivAt f (D x) x) : Continuous D := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let c : ℝ≥0 := ⟨ε/2, (half_pos hε).le⟩
  obtain ⟨S,hS,happrox⟩ := (hD x).approximates_deriv_on_nhds (c := c) (Or.inr (half_pos hε))
  obtain ⟨W,hWS,hWo,hxW⟩ := _root_.mem_nhds_iff.mp hS
  filter_upwards [hWo.mem_nhds hxW] with y hy
  have hyD : HasFDerivAt (fun z => f z-D x z) (D y-D x) y :=
    (hD y).hasFDerivAt.sub (D x).hasFDerivAt
  have hb := hyD.le_of_lipschitzOn (hWo.mem_nhds hy) (happrox.lipschitzOnWith.mono hWS)
  rw [dist_eq_norm]
  exact hb.trans_lt (half_lt_self hε)

theorem contDiff_one_of_everywhere_strict
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (h : ∀ x, ∃ D : E →L[ℝ] F, HasStrictFDerivAt f D x) :
    ContDiff ℝ 1 f := by
  choose D hD using h
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨D,continuous_differential_of_everywhere_strict f D hD,fun x => (hD x).hasFDerivAt⟩
end

open Set Filter Topology

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectedChartObservableStrict
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

section
open Set Filter Topology Metric

theorem openChart_of_projected_parametrization
    {A : Type*} [TopologicalSpace A] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (q : A → E) (hq : Continuous q) (a : A)
    (W : Set A) (hW : W∈𝓝 a) (hinj : Set.InjOn q W)
    (F : E → A) (hF : Continuous F) (hF0 : F 0=a)
    (hd : HasStrictFDerivAt (fun x => q (F x)) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ e : OpenPartialHomeomorph A E, (e : A → E)=q ∧ a∈e.source := by
  obtain ⟨V,hVW,hVo,haV⟩ := mem_nhds_iff.mp hW
  have hi : Set.InjOn q V := hinj.mono hVW
  have hd' : HasStrictFDerivAt (fun x => q (F x))
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) 0 := hd
  let e0 := hd'.toOpenPartialHomeomorph (fun x => q (F x))
  let e := e0.restrOpen (F ⁻¹' V) (hVo.preimage hF)
  have he0 : 0∈e.source := ⟨hd'.mem_toOpenPartialHomeomorph_source,by simpa only [mem_preimage,hF0] using haV⟩
  have hev (x : E) : e x=q (F x) := rfl
  have hFe {x : E} (hx : x∈e.target) : F (e.symm x)∈V := (e.map_target hx).2
  have hqFe {x : E} (hx : x∈e.target) : q (F (e.symm x))=x := e.right_inv hx
  let c : OpenPartialHomeomorph A E :=
    { toFun := q
      invFun := fun x => F (e.symm x)
      source := V∩q ⁻¹' e.target
      target := e.target
      map_source' := fun _ hx => hx.2
      map_target' := fun _ hx => ⟨hFe hx,by simpa only [mem_preimage,hqFe hx] using hx⟩
      left_inv' := fun _ hx => hi (hFe hx.2) hx.1 (hqFe hx.2)
      right_inv' := fun _ hx => hqFe hx
      open_source := hVo.inter (e.open_target.preimage hq)
      open_target := e.open_target
      continuousOn_toFun := hq.continuousOn
      continuousOn_invFun := hF.comp_continuousOn e.continuousOn_symm }
  refine ⟨c,rfl,haV,?_⟩
  have hem := e.map_source he0
  simpa only [mem_preimage,hev,hF0] using hem
end

open Set Filter Topology

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectedChartCommonCOne
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

open Set Filter Topology

theorem projected_chart_common_COne_restriction
    {A : Type*} [TopologicalSpace A] {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : OpenPartialHomeomorph A E) (a : A) (ha : a∈e.source)
    (F : E → A) (hF : Continuous F) (hF0 : F 0=a)
    (hd : HasStrictFDerivAt (fun x => e (F x)) (ContinuousLinearMap.id ℝ E) 0)
    (hD : ContDiffAt ℝ 1 (fun x => e (F x)) 0)
    {Q : Type*} (G : Q → A → H) (hG : ∀ q, ContDiff ℝ 1 (fun x => G q (F x))) :
    ∃ c : OpenPartialHomeomorph A E, (c : A → E)=e ∧ a∈c.source ∧
      ∀ q y, y∈c.target → ContDiffAt ℝ 1 (fun t => G q (c.symm t)) y := by
  have hd' : HasStrictFDerivAt (fun x => e (F x))
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) 0 := hd
  let I := hd'.localInverse (fun x => e (F x)) (ContinuousLinearEquiv.refl ℝ E) 0
  have hI : HasStrictFDerivAt I (ContinuousLinearMap.id ℝ E) (e a) := by
    simpa [I,hF0] using hd'.to_localInverse
  have hIC1 : ContDiffAt ℝ 1 I (e a) := by
    simpa only [ContDiffAt.localInverse,hF0] using hD.to_localInverse hd'.hasFDerivAt (by decide : (1 : WithTop ℕ∞)≠0)
  have hI0 : I (e a)=0 := by
    simpa only [hF0] using hd'.localInverse_apply_image
  have hFI : Tendsto (fun y => F (I y)) (𝓝 (e a)) (𝓝 a) := by
    have ht := hF.continuousAt.tendsto.comp hI.continuousAt.tendsto
    simpa only [Function.comp_def,hI0,hF0] using ht
  have hmem : ∀ᶠ y in 𝓝 (e a), F (I y)∈e.source :=
    hFI (e.open_source.mem_nhds ha)
  have hright : ∀ᶠ y in 𝓝 (e a), e (F (I y))=y := by
    simpa only [hF0] using hd'.eventually_right_inverse
  have hgood : ∀ᶠ y in 𝓝 (e a), ContDiffAt ℝ 1 I y ∧ F (I y)∈e.source ∧ e (F (I y))=y := by
    filter_upwards [hIC1.eventually (by simp),hmem,hright] with y hy hm hr using ⟨hy,hm,hr⟩
  obtain ⟨W,hW,hWo,haW⟩ := _root_.mem_nhds_iff.mp hgood
  let c : OpenPartialHomeomorph A E := (e.symm.restrOpen W hWo).symm
  have hac : a∈c.source := by
    have hh := (e.symm.restrOpen W hWo).map_source (show e a∈e.target∩W from ⟨e.map_source ha,haW⟩)
    change a∈(e.symm.restrOpen W hWo).target
    simpa only [OpenPartialHomeomorph.coe_restrOpen,e.left_inv ha] using hh
  refine ⟨c,rfl,hac,?_⟩
  intro q y hy
  have hyW : y∈W := hy.2
  have hcomp : ContDiffAt ℝ 1 (fun t => G q (F (I t))) y :=
    (hG q).contDiffAt.comp y (hW hyW).1
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hWo.mem_nhds hyW] with t ht
  have hs := (hW ht).2
  have he : e.symm t=F (I t) := by
    calc
      e.symm t=e.symm (e (F (I t))) := congrArg e.symm hs.2.symm
      _=F (I t) := e.left_inv hs.1
  change G q (e.symm t)=G q (F (I t))
  rw [he]
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FirstJetConstMul2
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_firstJet_COne_neighborhood :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
      ∀ (p' : U) y, y∈e.target → ContDiffAt ℝ 1 (fun t => ambientFirstJet p' (e.symm t)) y := by
  let R : Type := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  let _ : CompleteSpace R := FiniteDimensional.complete ℝ R
  obtain ⟨P,hP,hPinj⟩ := exists_complete_generator_jet_projection hU hbd Γ hhol p hc
  obtain ⟨W,hW,hinj⟩ := projected_firstJet_locally_injective (E := R)
    hU hc.isPreconnected hbd Γ hhol p P hPinj
  obtain ⟨F,hF,hF0,hd,_,hreg⟩ := exists_finite_flow_parametrization_with_regular_jets hU hc hbd Γ hhol p P hP
  obtain ⟨e,he,he1⟩ := openChart_of_projected_parametrization (A := Biholomorph U U) (E := R)
    (fun a => P (ambientFirstJet p a)) (P.continuous.comp (ambientFirstJet_continuous hU p))
    1 W hW hinj F hF hF0 hd
  have hjet (p' : U) : ContDiff ℝ 1 (fun t : R => ambientFirstJet p' (F t)) :=
    contDiff_one_of_everywhere_strict _ (hreg p')
  have hproj : ContDiffAt ℝ 1 (fun t : R => e (F t)) 0 := by
    have hPdiff := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
      (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R) P
    simpa only [Function.comp_def,he] using (hPdiff.comp (hjet p)).contDiffAt (x := (0:R))
  obtain ⟨c,hce,hc1,hcC1⟩ := projected_chart_common_COne_restriction (E := R) e 1 he1
    F hF hF0 (by simpa only [he] using hd) hproj ambientFirstJet hjet
  exact ⟨P,c,hce.trans he,hc1,hP,hcC1⟩
end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU

theorem firstJet_mul_const_contDiffAt
    (p : U) (g : Biholomorph U U) (c : E → Biholomorph U U) (t₀ : E)
    (hc : ContDiffAt ℝ 1 (fun t => ambientFirstJet (g.toHomeomorph p) (c t)) t₀) :
    ContDiffAt ℝ 1 (fun t => ambientFirstJet p (c t*g)) t₀ := by
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.contDiff (n := 1)).contDiffAt.comp t₀
    (hc.snd.prodMk (show ContDiffAt ℝ 1 (fun _ : E => g.derivativeAt p) t₀ from contDiffAt_const))
  have hpair := hc.fst.prodMk hB
  have he : (fun t => ambientFirstJet p (c t*g)) =
      (fun t => ((c t).ambientAut (g.toHomeomorph p).val,
        ((c t).derivativeAt (g.toHomeomorph p)).comp (g.derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · exact derivativeAt_mul hU (c t) g p
  rw [he]
  exact hpair

theorem firstJet_const_mul_contDiffAt
    (p : U) (g : Biholomorph U U) (c : E → Biholomorph U U) (t₀ : E)
    (hc : ContDiffAt ℝ 1 (fun t => ambientFirstJet p (c t)) t₀) :
    ContDiffAt ℝ 1 (fun t => ambientFirstJet p (g*c t)) t₀ := by
  have hy : (c t₀).ambientAut p.val∈U := by
    rw [ambientAut_apply]
    exact ((c t₀).toHomeomorph p).property
  have hA := ((g.ambientAut_analytic hU _ hy).contDiffAt (n := 1)).restrict_scalars ℝ
  have hD := ((g.ambientAut_analytic hU _ hy).fderiv.contDiffAt (n := 1)).restrict_scalars ℝ
  have hAv := hA.comp t₀ hc.fst
  have hDv := hD.comp t₀ hc.fst
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.contDiff (n := 1)).contDiffAt.comp t₀ (hDv.prodMk hc.snd)
  have hpair := hAv.prodMk hB
  have he : (fun t => ambientFirstJet p (g*c t)) =
      (fun t => (g.ambientAut ((c t).ambientAut p.val),
        (fderiv ℂ g.ambientAut ((c t).ambientAut p.val)).comp ((c t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU g (c t) p
  rw [he]
  exact hpair
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OpenChartLeftTranslate
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem openChart_leftTranslate_det_ne_zero
    (e : OpenPartialHomeomorph G E)
    (hC : ∀ (g : G) y, y∈e.target →
      ContDiffAt ℝ 1 (fun t => e (g*e.symm t)) y)
    (g : G) (y : E) (hy : y∈e.target) (hg : g*e.symm y∈e.source) :
    LinearMap.det (M := E) (fderiv ℝ (fun t => e (g*e.symm t)) y).toLinearMap ≠ 0 := by
  let f : E → E := fun t => e (g*e.symm t)
  let q : E → E := fun t => e (g⁻¹*e.symm t)
  have hf : DifferentiableAt ℝ f y := (hC g y hy).differentiableAt (by simp)
  have hfy : f y∈e.target := e.map_source hg
  have hq : DifferentiableAt ℝ q (f y) := (hC g⁻¹ (f y) hfy).differentiableAt (by simp)
  have hc : ContinuousAt (fun t => g*e.symm t) y :=
    continuousAt_const.mul (e.symm.continuousAt hy)
  have hs : ∀ᶠ t in 𝓝 y, g*e.symm t∈e.source :=
    hc.preimage_mem_nhds (e.open_source.mem_nhds hg)
  have ht : ∀ᶠ t in 𝓝 y, t∈e.target := e.open_target.mem_nhds hy
  have heq : (q ∘ f) =ᶠ[𝓝 y] id := by
    filter_upwards [hs,ht] with t hgt ht
    dsimp only [q,f,Function.comp_apply,id_eq]
    rw [e.left_inv hgt,inv_mul_cancel_left,e.right_inv ht]
  have hd := (hq.hasFDerivAt.comp y hf.hasFDerivAt).congr_of_eventuallyEq heq.symm
  have hcomp : (fderiv ℝ q (f y)).comp (fderiv ℝ f y)=ContinuousLinearMap.id ℝ E :=
    hd.unique (hasFDerivAt_id y)
  have hinj : Function.Injective (fderiv ℝ f y) := by
    intro u v huv
    have h := congrArg (fderiv ℝ q (f y)) huv
    simpa only [←ContinuousLinearMap.comp_apply,hcomp,ContinuousLinearMap.id_apply] using h
  intro hz
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hinj)
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartLeftDensityJacobian
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chartLeftMap_fderiv_cocycle
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (hC : ∀ (g : G) y, y∈e.target →
      ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (g : G) (x : E) (hx : x∈e.target) (_hg : g*e.symm x∈e.source) :
    fderiv ℝ (chartLeftMap e (g*e.symm x)) (e 1) =
      (fderiv ℝ (chartLeftMap e g) x).comp
        (fderiv ℝ (chartLeftMap e (e.symm x)) (e 1)) := by
  have hbase := e.map_source he1
  have hax : chartLeftMap e (e.symm x) (e 1)=x := by
    simp only [chartLeftMap,e.left_inv he1,mul_one,e.right_inv hx]
  have hdx := (hC (e.symm x) (e 1) hbase).differentiableAt (by simp)
  have hdg := (hC g x hx).differentiableAt (by simp)
  have ht : ∀ᶠ t in 𝓝 (e 1), e.symm x*e.symm t∈e.source := by
    have hc : ContinuousAt (fun t => e.symm x*e.symm t) (e 1) :=
      continuousAt_const.mul (e.symm.continuousAt hbase)
    have hv : e.symm x*e.symm (e 1)∈e.source := by
      simpa only [e.left_inv he1,mul_one] using e.map_target hx
    exact hc.preimage_mem_nhds (e.open_source.mem_nhds hv)
  have heq : (chartLeftMap e g ∘ chartLeftMap e (e.symm x)) =ᶠ[𝓝 (e 1)]
      chartLeftMap e (g*e.symm x) := by
    filter_upwards [ht] with t ht
    simp only [chartLeftMap,Function.comp_apply,e.left_inv ht,mul_assoc]
  have hdg' : HasFDerivAt (chartLeftMap e g) (fderiv ℝ (chartLeftMap e g) x)
      (chartLeftMap e (e.symm x) (e 1)) := by rw [hax]; exact hdg.hasFDerivAt
  have hc := (hdg'.comp (e 1) hdx.hasFDerivAt).congr_of_eventuallyEq heq.symm
  exact hc.fderiv

theorem chartLeftDensity_jacobian
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (hC : ∀ (g : G) y, y∈e.target →
      ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (hD : ∀ (g : G) y, y∈e.target → g*e.symm y∈e.source →
      (fderiv ℝ (chartLeftMap e g) y).det ≠ 0)
    (g : G) (x : E) (hx : x∈e.target) (hg : g*e.symm x∈e.source) :
    chartLeftDensity e (chartLeftMap e g x) *
      |(fderiv ℝ (chartLeftMap e g) x).det| = chartLeftDensity e x := by
  have hcomp := chartLeftMap_fderiv_cocycle e he1 hC g x hx hg
  have heq : e.symm (chartLeftMap e g x)=g*e.symm x := e.left_inv hg
  have hd := hD g x hx hg
  unfold chartLeftDensity
  rw [heq,hcomp]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,abs_mul]
  rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hd),mul_one]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectedChartLeftDifferential
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU
omit [LocallyCompactSpace U] in

theorem projected_chart_left_differential_apply
    (p : U) (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] E)
    (e : OpenPartialHomeomorph (Biholomorph U U) E)
    (he : (e : Biholomorph U U → E)=(fun a => P (ambientFirstJet p a)))
    (he1 : 1∈e.source)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hL : HasStrictFDerivAt (fun t => ambientFirstJet p (e.symm t)) L (e 1))
    (g : Biholomorph U U) (v : E) :
    (fderiv ℝ (chartLeftMap e g) (e 1)) v =
      P (g.derivativeAt p (L v).1,
        (fderiv ℂ (fderiv ℂ g.ambientAut) p.val) (L v).1 +
          (g.derivativeAt p).comp (L v).2) := by
  have hy : (e.symm (e 1)).ambientAut p.val=p.val := by
    rw [e.left_inv he1]
    simp only [ambientAut_apply,one_apply]
  have hid : fderiv ℂ (e.symm (e 1)).ambientAut p.val=1 := by
    change (e.symm (e 1)).derivativeAt p=1
    rw [e.left_inv he1,derivativeAt_one hU]
  have hA := ((g.ambientAut_analytic hU p.val p.property).hasStrictFDerivAt).restrictScalars ℝ
  have hD := ((g.ambientAut_analytic hU p.val p.property).fderiv.hasStrictFDerivAt).restrictScalars ℝ
  have hA' : HasStrictFDerivAt g.ambientAut ((g.derivativeAt p).restrictScalars ℝ)
      ((e.symm (e 1)).ambientAut p.val) := by rw [hy]; exact hA
  have hD' : HasStrictFDerivAt (fderiv ℂ g.ambientAut)
      ((fderiv ℂ (fderiv ℂ g.ambientAut) p.val).restrictScalars ℝ)
      ((e.symm (e 1)).ambientAut p.val) := by rw [hy]; exact hD
  have hAv := hA'.comp (e 1) hL.fst
  have hDv := hD'.comp (e 1) hL.fst
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    (fderiv ℂ g.ambientAut ((e.symm (e 1)).ambientAut p.val),
      (e.symm (e 1)).derivativeAt p)).comp (e 1) (hDv.prodMk hL.snd)
  have hpair := hAv.prodMk hB
  have hj : (fun t => ambientFirstJet p (g*e.symm t)) =
      (fun t => (g.ambientAut ((e.symm t).ambientAut p.val),
        (fderiv ℂ g.ambientAut ((e.symm t).ambientAut p.val)).comp ((e.symm t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU g (e.symm t) p
  have hPc := ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ)
    (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := E)
    (x := (g.ambientAut ((e.symm (e 1)).ambientAut p.val),
      (fderiv ℂ g.ambientAut ((e.symm (e 1)).ambientAut p.val)).comp
        ((e.symm (e 1)).derivativeAt p))) P
  have hp := HasStrictFDerivAt.comp (𝕜 := ℝ) (E := E)
    (F := Affine n × (Affine n →L[ℂ] Affine n)) (G := E) (e 1) hPc hpair
  have hf := hp.hasFDerivAt.congr_of_eventuallyEq (f₁ := chartLeftMap e g) (by
    filter_upwards [] with t
    rw [chartLeftMap,he]
    dsimp only
    rw [congrFun hj t]
    rfl)
  rw [hf.fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.one_def,
    IsBoundedBilinearMap.deriv, B,hy,hid,derivativeAt,add_comm]
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BiHaarInvInvariant
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph
open Set Filter Topology
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
include hU

theorem projected_chart_left_determinant_continuous
    (p : U) (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] E)
    (e : OpenPartialHomeomorph (Biholomorph U U) E)
    (he : (e : Biholomorph U U → E)=(fun a => P (ambientFirstJet p a)))
    (he1 : 1∈e.source)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hL : HasStrictFDerivAt (fun t => ambientFirstJet p (e.symm t)) L (e 1)) :
    Continuous (fun g : Biholomorph U U => (fderiv ℝ (chartLeftMap e g) (e 1)).det) := by
  classical
  have hd : Continuous (fun g : Biholomorph U U => g.derivativeAt p) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    exact (ambientAut_derivative_joint_continuousAt hU (q := (g,p.val)) p.property).comp (x := g)
      (show ContinuousAt (fun a : Biholomorph U U => (a,p.val)) g from
        continuousAt_id.prodMk continuousAt_const)
  have hdd : Continuous (fun g : Biholomorph U U => fderiv ℂ (fderiv ℂ g.ambientAut) p.val) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    exact (ambientAut_second_derivative_joint_continuousAt hU (q := (g,p.val)) p.property).comp (x := g)
      (show ContinuousAt (fun a : Biholomorph U U => (a,p.val)) g from
        continuousAt_id.prodMk continuousAt_const)
  have heval (v : E) : Continuous (fun g : Biholomorph U U =>
      (fderiv ℝ (chartLeftMap e g) (e 1)) v) := by
    simp_rw [projected_chart_left_differential_apply hU p P e he he1 L hL]
    exact P.continuous.comp ((hd.clm_apply continuous_const).prodMk
      ((hdd.clm_apply continuous_const).add (hd.clm_comp continuous_const)))
  let b := Module.finBasis ℝ E
  have hm : Continuous (fun g : Biholomorph U U =>
      LinearMap.toMatrix b b (fderiv ℝ (chartLeftMap e g) (e 1)).toLinearMap) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [LinearMap.toMatrix_apply,ContinuousLinearMap.coe_coe]
    exact (continuous_apply i).comp ((continuous_equivFun_basis b).comp (heval (b j)))
  have hh := hm.matrix_det
  simpa only [LinearMap.det_toMatrix,ContinuousLinearMap.det] using hh
end Release061.Biholomorph

namespace Release061
open TopologicalSpace Set MeasureTheory MeasureTheory.Measure Function
open scoped ENNReal NNReal

theorem biHaar_isInvInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [μ.Regular] :
    μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have hh : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ,hc,Measure.map_smul c,
      ← inv_def μ,hc,smul_smul,pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at hh
    simpa only [inv_involutive,Involutive.comp_self,Measure.map_id] using hh
  have K : PositiveCompacts G := Classical.arbitrary _
  have hh : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have hcp : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 hh
  have hc1 : c=1 := (ENNReal.pow_right_strictMono two_ne_zero).injective hcp
  rw [hc,hc1,one_smul]
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartDensityMeasureLeft
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

omit [IsTopologicalGroup G] [NormedSpace ℝ E] in
theorem chartInverseExtension_measurable (e : OpenPartialHomeomorph G E) :
    Measurable (chartInverseExtension e) := by
  classical
  exact e.continuousOn_invFun.measurable_piecewise continuous_const.continuousOn
    e.open_target.measurableSet

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chartInverseExtension_eq (e : OpenPartialHomeomorph G E) {x : E}
    (hx : x∈e.target) : chartInverseExtension e x=e.symm x := by
  classical
  simp only [chartInverseExtension,piecewise_eq_of_mem _ _ _ hx]

omit [IsTopologicalGroup G] [NormedSpace ℝ E] in
theorem chartPart_measurable (e : OpenPartialHomeomorph G E) {A : Set G}
    (hA : MeasurableSet A) : MeasurableSet (chartPart e A) :=
  e.open_target.measurableSet.inter (hA.preimage (chartInverseExtension_measurable e))

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mem_chartPart_iff (e : OpenPartialHomeomorph G E) (A : Set G) (x : E) :
    x∈chartPart e A ↔ x∈e.target ∧ e.symm x∈A := by
  constructor
  · rintro ⟨hx,ha⟩
    exact ⟨hx,by simpa only [mem_preimage,chartInverseExtension_eq e hx] using ha⟩
  · rintro ⟨hx,ha⟩
    exact ⟨hx,by simpa only [mem_preimage,chartInverseExtension_eq e hx] using ha⟩

omit [IsTopologicalGroup G] [NormedSpace ℝ E] in
theorem chartDensityMeasure_apply (e : OpenPartialHomeomorph G E) (μE : Measure E)
    (ρ : E → ℝ) {A : Set G} (hA : MeasurableSet A) :
    chartDensityMeasure e μE ρ A = ∫⁻ x in chartPart e A, ENNReal.ofReal (ρ x) ∂μE := by
  rw [chartDensityMeasure,Measure.map_apply (chartInverseExtension_measurable e) hA,
    Measure.restrict_apply (hA.preimage (chartInverseExtension_measurable e))]
  rw [withDensity_apply _ ((hA.preimage (chartInverseExtension_measurable e)).inter
    e.open_target.measurableSet)]
  apply congrArg (fun S => ∫⁻ x in S, ENNReal.ofReal (ρ x) ∂μE)
  exact Set.inter_comm _ _

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in

theorem chartLeftMap_image_overlap (e : OpenPartialHomeomorph G E)
    (g : G) {A B : Set G} (hAS : A⊆e.source) (hBS : B⊆e.source) :
    chartLeftMap e g '' chartPart e (A ∩ (fun x => g*x) ⁻¹' B) =
      chartPart e (B ∩ (fun y => g⁻¹*y) ⁻¹' A) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [mem_chartPart_iff] at hx ⊢
    have hg : g*e.symm x∈e.source := hBS hx.2.2
    refine ⟨e.map_source hg,?_⟩
    simp only [chartLeftMap,e.left_inv hg,mem_inter_iff,mem_preimage,inv_mul_cancel_left]
    exact ⟨hx.2.2,hx.2.1⟩
  · intro hy
    rw [mem_chartPart_iff] at hy
    have ha : g⁻¹*e.symm y∈e.source := hAS hy.2.2
    refine ⟨e (g⁻¹*e.symm y),?_,?_⟩
    · rw [mem_chartPart_iff]
      refine ⟨e.map_source ha,?_⟩
      simp only [e.left_inv ha,mem_inter_iff,mem_preimage,mul_inv_cancel_left]
      exact ⟨hy.2.2,hy.2.1⟩
    · simp only [chartLeftMap,e.left_inv ha,mul_inv_cancel_left,e.right_inv hy.1]

theorem chartDensityMeasure_left_overlap [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph G E) (μE : Measure E) [μE.IsAddHaarMeasure]
    (ρ : E → ℝ)
    (hC : ∀ (g : G) y, y∈e.target → ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (hρ : ∀ (g : G) x, x∈e.target → g*e.symm x∈e.source →
      ρ (chartLeftMap e g x) * |(fderiv ℝ (chartLeftMap e g) x).det| = ρ x)
    (g : G) (A B : Set G) (hA : MeasurableSet A) (hAS : A⊆e.source)
    (hB : MeasurableSet B) (hBS : B⊆e.source) :
    chartDensityMeasure e μE ρ (B ∩ (fun y => g⁻¹*y) ⁻¹' A) =
      chartDensityMeasure e μE ρ (A ∩ (fun x => g*x) ⁻¹' B) := by
  let S := chartPart e (A ∩ (fun x => g*x) ⁻¹' B)
  have hS : MeasurableSet S := chartPart_measurable e
    (hA.inter (hB.preimage (continuous_const.mul continuous_id).measurable))
  have hder : ∀ x∈S, HasFDerivWithinAt (chartLeftMap e g)
      (fderiv ℝ (chartLeftMap e g) x) S x := by
    intro x hx
    exact ((hC g x ((mem_chartPart_iff e _ x).mp hx).1).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn (chartLeftMap e g) S := by
    intro x hx y hy hxy
    have hx := (mem_chartPart_iff e _ x).mp hx
    have hy := (mem_chartPart_iff e _ y).mp hy
    have heq : g*e.symm x=g*e.symm y := e.injOn (hBS hx.2.2) (hBS hy.2.2) hxy
    exact e.symm.injOn hx.1 hy.1 (mul_left_cancel heq)
  have hmA : MeasurableSet (A ∩ (fun x => g*x) ⁻¹' B) :=
    hA.inter (hB.preimage (continuous_const.mul continuous_id).measurable)
  have hmB : MeasurableSet (B ∩ (fun y => g⁻¹*y) ⁻¹' A) :=
    hB.inter (hA.preimage (continuous_const.mul continuous_id).measurable)
  rw [chartDensityMeasure_apply e μE ρ hmB, chartDensityMeasure_apply e μE ρ hmA,
    ← chartLeftMap_image_overlap e g hAS hBS]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μE hS hder hinj]
  apply setLIntegral_congr_fun hS
  intro x hx
  have hx := (mem_chartPart_iff e _ x).mp hx
  dsimp only
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [mul_comm,hρ g x hx.1 (hBS hx.2.2)]
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocalHaarEqualMass
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set MeasureTheory
open scoped ENNReal NNReal

theorem local_haar_cross_multiply
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (S : Set G)
    (hν : ∀ (g : G) (A B : Set G), MeasurableSet A → A ⊆ S →
      MeasurableSet B → B ⊆ S →
      ν (B ∩ (fun y => g⁻¹*y) ⁻¹' A) = ν (A ∩ (fun x => g*x) ⁻¹' B))
    {A B : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hB : MeasurableSet B) (hBS : B ⊆ S) :
    μ A * ν B = μ B * ν A := by
  classical
  let a : G → ℝ≥0∞ := A.indicator 1
  let b : G → ℝ≥0∞ := B.indicator 1
  have ha : Measurable a := measurable_const.indicator hA
  have hb : Measurable b := measurable_const.indicator hB
  have hleft (y : G) : (∫⁻ g, a (g⁻¹*y) ∂μ) = μ A := by
    rw [lintegral_inv_eq_self (fun g => a (g*y)),lintegral_mul_right_eq_self]
    exact lintegral_indicator_one hA
  have hright (x : G) : (∫⁻ g, b (g*x) ∂μ) = μ B := by
    rw [lintegral_mul_right_eq_self]
    exact lintegral_indicator_one hB
  have hsetL (g : G) : (∫⁻ y, b y*a (g⁻¹*y) ∂ν) =
      ν (B ∩ (fun y => g⁻¹*y) ⁻¹' A) := by
    have he : (fun y => b y*a (g⁻¹*y)) =
        (B ∩ (fun y => g⁻¹*y) ⁻¹' A).indicator 1 := by
      funext y
      by_cases hy : y∈B <;> by_cases hg : g⁻¹*y∈A <;> simp [a,b,hy,hg]
    rw [he]
    exact lintegral_indicator_one (hB.inter (hA.preimage (measurable_const.mul measurable_id)))
  have hsetR (g : G) : (∫⁻ x, a x*b (g*x) ∂ν) =
      ν (A ∩ (fun x => g*x) ⁻¹' B) := by
    have he : (fun x => a x*b (g*x)) =
        (A ∩ (fun x => g*x) ⁻¹' B).indicator 1 := by
      funext x
      by_cases hx : x∈A <;> by_cases hg : g*x∈B <;> simp [a,b,hx,hg]
    rw [he]
    exact lintegral_indicator_one (hA.inter (hB.preimage (measurable_const.mul measurable_id)))
  calc
    μ A * ν B = ∫⁻ y, b y * (∫⁻ g, a (g⁻¹*y) ∂μ) ∂ν := by
      simp_rw [hleft]
      rw [lintegral_mul_const _ hb,show (∫⁻ y, b y ∂ν)=ν B from lintegral_indicator_one hB,mul_comm]
    _ = ∫⁻ y, ∫⁻ g, b y*a (g⁻¹*y) ∂μ ∂ν := by
      congr with y
      exact (lintegral_const_mul _ ((ha.comp (measurable_inv.mul_const y)))).symm
    _ = ∫⁻ g, ∫⁻ y, b y*a (g⁻¹*y) ∂ν ∂μ := by
      apply lintegral_lintegral_swap
      exact ((hb.comp measurable_fst).mul
        (ha.comp (measurable_snd.inv.mul measurable_fst))).aemeasurable
    _ = ∫⁻ g, ∫⁻ x, a x*b (g*x) ∂ν ∂μ := by
      apply lintegral_congr
      intro g
      rw [hsetL,hsetR]
      exact hν g A B hA hAS hB hBS
    _ = ∫⁻ x, ∫⁻ g, a x*b (g*x) ∂μ ∂ν := by
      apply lintegral_lintegral_swap
      exact ((ha.comp measurable_snd).mul
        (hb.comp (measurable_fst.mul measurable_snd))).aemeasurable
    _ = ∫⁻ x, a x * (∫⁻ g, b (g*x) ∂μ) ∂ν := by
      congr with x
      exact lintegral_const_mul _ (hb.comp (measurable_id.mul_const x))
    _ = μ B * ν A := by
      simp_rw [hright]
      rw [lintegral_mul_const _ ha,show (∫⁻ x, a x ∂ν)=ν A from lintegral_indicator_one hA,mul_comm]

theorem local_haar_equal_mass
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (S : Set G)
    (hν : ∀ (g : G) (A B : Set G), MeasurableSet A → A ⊆ S →
      MeasurableSet B → B ⊆ S →
      ν (B ∩ (fun y => g⁻¹*y) ⁻¹' A) = ν (A ∩ (fun x => g*x) ⁻¹' B))
    {B : Set G} (hB : MeasurableSet B) (hBS : B ⊆ S)
    (hB0 : μ B ≠ 0) (hBtop : μ B ≠ (∞ : ℝ≥0∞))
    {A A' : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hA' : MeasurableSet A') (hA'S : A' ⊆ S) (h : μ A=μ A') :
    ν A=ν A' := by
  apply (ENNReal.mul_right_inj hB0 hBtop).mp
  rw [← local_haar_cross_multiply μ ν S hν hA hAS hB hBS,
    ← local_haar_cross_multiply μ ν S hν hA' hA'S hB hBS,h]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartDensityPreservedBy
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

omit [Group G] [IsTopologicalGroup G] [NormedSpace ℝ E] in

theorem chart_inverse_image_measurable (e : OpenPartialHomeomorph G E)
    {A : Set E} (hA : MeasurableSet A) (hAt : A⊆e.target) :
    MeasurableSet (e.symm '' A) := by
  classical
  let F : G → E := e.source.piecewise e (fun _ => 0)
  have hF : Measurable F := e.continuousOn_toFun.measurable_piecewise
    continuous_const.continuousOn e.open_source.measurableSet
  have heq : e.symm '' A = e.source ∩ F ⁻¹' A := by
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩
      have ht := hAt hx
      refine ⟨e.map_target ht,?_⟩
      simpa only [mem_preimage,F,piecewise_eq_of_mem _ _ _ (e.map_target ht),e.right_inv ht]
        using hx
    · rintro ⟨hg,ha⟩
      refine ⟨e g,?_,e.left_inv hg⟩
      simpa only [mem_preimage,F,piecewise_eq_of_mem _ _ _ hg] using ha
  rw [heq]
  exact e.open_source.measurableSet.inter (hA.preimage hF)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chartPart_inverse_image (e : OpenPartialHomeomorph G E)
    {A : Set E} (hAt : A⊆e.target) : chartPart e (e.symm '' A)=A := by
  ext x
  rw [mem_chartPart_iff]
  constructor
  · rintro ⟨hx,y,hy,heq⟩
    have : y=x := e.symm.injOn (hAt hy) hx heq
    simpa only [this] using hy
  · intro hx
    exact ⟨hAt hx,x,hx,rfl⟩

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chartPart_map_inverse_image (e : OpenPartialHomeomorph G E)
    (F : G → G) {A : Set E} (_hAt : A⊆e.target)
    (hFs : ∀ x∈A, F (e.symm x)∈e.source) :
    chartPart e (F '' (e.symm '' A)) = (fun x => e (F (e.symm x))) '' A := by
  ext y
  rw [mem_chartPart_iff]
  constructor
  · rintro ⟨hy,g,⟨x,hx,rfl⟩,hxy⟩
    exact ⟨x,hx,by dsimp only; rw [hxy,e.right_inv hy]⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨e.map_source (hFs x hx),e.symm x,⟨x,hx,rfl⟩,?_⟩
    exact (e.left_inv (hFs x hx)).symm

theorem chart_density_preserved_by_haar_homeomorph [FiniteDimensional ℝ E]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (μE : Measure E) [μE.IsAddHaarMeasure]
    (ρ : E → ℝ)
    (hC : ∀ (g : G) y, y∈e.target → ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (hρ : ∀ (g : G) x, x∈e.target → g*e.symm x∈e.source →
      ρ (chartLeftMap e g x) * |(fderiv ℝ (chartLeftMap e g) x).det| = ρ x)
    (F : G ≃ₜ G) (hF : MeasurePreserving F μ μ)
    {A : Set E} (hA : MeasurableSet A) (hAt : A⊆e.target)
    (hFs : ∀ x∈A, F (e.symm x)∈e.source) :
    (∫⁻ x in (fun y => e (F (e.symm y))) '' A, ENNReal.ofReal (ρ x) ∂μE) =
      ∫⁻ x in A, ENNReal.ofReal (ρ x) ∂μE := by
  let ν := chartDensityMeasure e μE ρ
  let : SFinite ν := by dsimp only [ν,chartDensityMeasure]; infer_instance
  obtain ⟨B,hBnh,hBs,hBk⟩ := local_compact_nhds (e.open_source.mem_nhds he1)
  have hB : MeasurableSet B := hBk.isClosed.measurableSet
  have hB0 : μ B ≠ 0 := (μ.measure_pos_of_mem_nhds hBnh).ne'
  have hBtop : μ B ≠ (∞ : ℝ≥0∞) := hBk.measure_lt_top.ne
  have hIA := chart_inverse_image_measurable e hA hAt
  have hFA : MeasurableSet (F '' (e.symm '' A)) := F.measurableEmbedding.measurableSet_image.mpr hIA
  have hIs : e.symm '' A⊆e.source := by rintro _ ⟨x,hx,rfl⟩; exact e.map_target (hAt hx)
  have hFAs : F '' (e.symm '' A)⊆e.source := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact hFs x hx
  have hmass : μ (F '' (e.symm '' A))=μ (e.symm '' A) :=
    by
      have hh := hF.measure_preimage hFA.nullMeasurableSet
      rw [F.injective.preimage_image] at hh
      exact hh.symm
  have hn := local_haar_equal_mass μ ν e.source
    (chartDensityMeasure_left_overlap e μE ρ hC hρ) hB hBs hB0 hBtop
    hFA hFAs hIA hIs hmass
  dsimp only [ν] at hn
  rw [chartDensityMeasure_apply e μE ρ hFA,chartDensityMeasure_apply e μE ρ hIA,
    chartPart_inverse_image e hAt,chartPart_map_inverse_image e F hAt hFs] at hn
  exact hn
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartAbsDetOne
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem abs_det_eq_one_of_local_density_preserving
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Set E) (hS : IsOpen S) (f : E → E) (f' : E → E →L[ℝ] E)
    (ρ : E → ℝ)
    (hf : ∀ x∈S, HasFDerivAt f (f' x) x)
    (hinj : InjOn f S)
    (hρ : ContinuousOn ρ S)
    (hρf : ContinuousOn (ρ ∘ f) S)
    (hD : ContinuousOn (fun x => (f' x).det) S)
    (hm : ∀ A : Set E, MeasurableSet A → A⊆S →
      (∫⁻ x in f '' A, ENNReal.ofReal (ρ x) ∂μ) =
        ∫⁻ x in A, ENNReal.ofReal (ρ x) ∂μ)
    {x : E} (hx : x∈S) (hfx : f x=x) (hρx : 0<ρ x) :
    |(f' x).det|=1 := by
  let j : E → ℝ≥0∞ := fun y => ENNReal.ofReal |(f' y).det| * ENNReal.ofReal (ρ (f y))
  let r : E → ℝ≥0∞ := fun y => ENNReal.ofReal (ρ y)
  have hjc : ContinuousOn j S := by
    have hc := ENNReal.continuous_ofReal.comp_continuousOn (hD.abs.mul hρf)
    simpa only [j,Function.comp_def,Pi.mul_apply,ENNReal.ofReal_mul (abs_nonneg _)] using hc
  have hrc : ContinuousOn r S := ENNReal.continuous_ofReal.comp_continuousOn hρ
  have heq : j =ᵐ[μ.restrict S] r := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀
      (hjc.aemeasurable hS.measurableSet) (hrc.aemeasurable hS.measurableSet)
    intro A hA _
    rw [Measure.restrict_restrict hA]
    have hAS : MeasurableSet (A∩S) := hA.inter hS.measurableSet
    have hd : ∀ y∈A∩S, HasFDerivWithinAt f (f' y) (A∩S) y :=
      fun y hy => (hf y hy.2).hasFDerivWithinAt
    have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hAS hd
      (hinj.mono inter_subset_right) (fun y => ENNReal.ofReal (ρ y))
    exact hh.symm.trans (hm (A∩S) hAS inter_subset_right)
  have hxj := Measure.eqOn_open_of_ae_eq heq hS hjc hrc hx
  dsimp only [j,r] at hxj
  rw [hfx,← ENNReal.ofReal_mul (abs_nonneg _)] at hxj
  have heqreal : |(f' x).det| * ρ x=ρ x :=
    by
      have ht := congrArg ENNReal.toReal hxj
      simpa only [ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg _) hρx.le),
        ENNReal.toReal_ofReal hρx.le] using ht
  exact (mul_right_cancel₀ hρx.ne' (heqreal.trans (one_mul _).symm))

theorem chart_abs_det_one_of_haar_preserving
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (μE : Measure E) [μE.IsAddHaarMeasure]
    (hC : ∀ (g : G) y, y∈e.target → ContDiffAt ℝ 1 (chartLeftMap e g) y)
    (hD : ∀ (g : G) y, y∈e.target → g*e.symm y∈e.source →
      (fderiv ℝ (chartLeftMap e g) y).det≠0)
    (hρ : ContinuousOn (chartLeftDensity e) e.target)
    (F : G ≃ₜ G) (hF : MeasurePreserving F μ μ) (hF1 : F 1=1)
    (hFC : ∀ y, y∈e.target → ContDiffAt ℝ 1 (fun x => e (F (e.symm x))) y) :
    |(fderiv ℝ (fun x => e (F (e.symm x))) (e 1)).det|=1 := by
  let f : E → E := fun x => e (F (e.symm x))
  let S : Set E := e.target ∩ (fun x => F (e.symm x)) ⁻¹' e.source
  have hSt : S⊆e.target := inter_subset_left
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hc : ContinuousAt (fun y => F (e.symm y)) x :=
      F.continuous.continuousAt.comp (e.symm.continuousAt hx.1)
    exact inter_mem (e.open_target.mem_nhds hx.1) (hc (e.open_source.mem_nhds hx.2))
  have hfS : MapsTo f S e.target := fun x hx => e.map_source hx.2
  have hf : ContinuousOn f S := fun x hx => (hFC x hx.1).continuousAt.continuousWithinAt
  have hdet : ContinuousOn (fun x => (fderiv ℝ f x).det) S := by
    intro x hx
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hFC x hx.1).continuousAt_fderiv one_ne_zero)).continuousWithinAt
  have hinj : InjOn f S := by
    intro x hx y hy hxy
    exact e.symm.injOn hx.1 hy.1 (F.injective (e.injOn hx.2 hy.2 hxy))
  have hmass (A : Set E) (hA : MeasurableSet A) (hAS : A⊆S) :
      (∫⁻ x in f '' A, ENNReal.ofReal (chartLeftDensity e x) ∂μE) =
        ∫⁻ x in A, ENNReal.ofReal (chartLeftDensity e x) ∂μE :=
    chart_density_preserved_by_haar_homeomorph e he1 μ μE (chartLeftDensity e) hC
      (chartLeftDensity_jacobian e he1 hC hD) F hF hA (hAS.trans hSt)
      (fun x hx => (hAS hx).2)
  have hone : e 1∈S := by
    refine ⟨e.map_source he1,?_⟩
    simpa only [mem_preimage,e.left_inv he1,hF1] using he1
  have hfix : f (e 1)=e 1 := by simp only [f,e.left_inv he1,hF1]
  have hpos : 0 < chartLeftDensity e (e 1) := by
    apply inv_pos.mpr
    apply abs_pos.mpr
    apply hD _ _ (e.map_source he1)
    simpa only [e.left_inv he1,one_mul] using he1
  exact abs_det_eq_one_of_local_density_preserving μE S hS f (fderiv ℝ f)
    (chartLeftDensity e) (fun x hx => ((hFC x hx.1).differentiableAt (by simp)).hasFDerivAt)
    hinj (hρ.mono hSt) (hρ.comp hf hfS) hdet hmass hone hfix hpos
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AutChartUnimodularJacobian
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology MeasureTheory

theorem chartLeftDensity_continuousOn
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (hdet : Continuous (fun g : G => (fderiv ℝ (chartLeftMap e g) (e 1)).det))
    (hD : ∀ (g : G) y, y∈e.target → g*e.symm y∈e.source →
      (fderiv ℝ (chartLeftMap e g) y).det≠0) :
    ContinuousOn (chartLeftDensity e) e.target := by
  change ContinuousOn (fun x => |(fderiv ℝ (chartLeftMap e (e.symm x)) (e 1)).det|⁻¹) e.target
  apply ((hdet.comp_continuousOn e.symm.continuousOn).abs).inv₀
  intro x hx
  apply abs_ne_zero.mpr
  apply hD _ _ (e.map_source he1)
  simpa only [e.left_inv he1,mul_one] using e.map_target hx

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_chart_unimodular_jacobian_oai :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
      (∀ (p' : U) y, y∈e.target →
        ContDiffAt ℝ 1 (fun t => ambientFirstJet p' (e.symm t)) y) ∧
      ∀ g : Biholomorph U U,
        |(fderiv ℝ (fun x => e (g*e.symm x*g⁻¹)) (e 1)).det|=1 := by
  let R : Type := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  let _ : FiniteDimensional ℝ R := inferInstance
  let _ : ProperSpace R := FiniteDimensional.proper ℝ R
  let _ : LocallyCompactSpace R := inferInstance
  let _ : MeasurableSpace R := borel R
  let _ : BorelSpace R := ⟨rfl⟩
  let _ : LocallyCompactSpace (Biholomorph U U) :=
    bounded_divisible_automorphism_locallyCompact hU hc.isPreconnected hbd Γ hhol p
  let _ : MeasurableSpace (Biholomorph U U) := borel (Biholomorph U U)
  let _ : BorelSpace (Biholomorph U U) := ⟨rfl⟩
  let μ : Measure (Biholomorph U U) := Measure.haar
  let _ : μ.IsMulRightInvariant :=
    bounded_divisible_automorphism_unimodular hU hc.isPreconnected hbd Γ hhol p
  let _ : μ.IsInvInvariant := biHaar_isInvInvariant μ
  obtain ⟨P,e,he,he1,hP,hreg⟩ := exists_actual_aut_firstJet_COne_neighborhood hU hc hbd Γ hhol p
  have hC (g h : Biholomorph U U) (y : R) (hy : y∈e.target) :
      ContDiffAt ℝ 1 (fun t => e (g*e.symm t*h)) y := by
    have hr := firstJet_mul_const_contDiffAt hU p h e.symm y (hreg (h.toHomeomorph p) y hy)
    have hl := firstJet_const_mul_contDiffAt hU p g (fun t => e.symm t*h) y hr
    have hPdiff := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
        (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R) P).contDiffAt.comp y hl
    simpa only [Function.comp_def,he,mul_assoc] using hPdiff
  have hCL (g : Biholomorph U U) (y : R) (hy : y∈e.target) :
      ContDiffAt ℝ 1 (chartLeftMap e g) y := by
    change ContDiffAt ℝ 1 (fun t => e (g*e.symm t)) y
    simpa only [mul_one] using hC g 1 y hy
  have hD (g : Biholomorph U U) (y : R) (hy : y∈e.target) (hg : g*e.symm y∈e.source) :
      (fderiv ℝ (chartLeftMap e g) y).det≠0 :=
    openChart_leftTranslate_det_ne_zero e hCL g y hy hg
  have hL := (hreg p (e 1) (e.map_source he1)).hasStrictFDerivAt (by simp)
  have hdet := projected_chart_left_determinant_continuous hU p P e he he1 _ hL
  have hρ := chartLeftDensity_continuousOn e he1 hdet hD
  refine ⟨P,e,he,he1,hP,hreg,?_⟩
  intro g
  let F : (Biholomorph U U) ≃ₜ (Biholomorph U U) :=
    (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  have hF : MeasurePreserving F μ μ :=
    (measurePreserving_mul_right μ g⁻¹).comp (measurePreserving_mul_left μ g)
  have hF1 : F 1=1 := by simp [F]
  exact chart_abs_det_one_of_haar_preserving e he1 μ (Measure.addHaar : Measure R)
    hCL hD hρ F hF hF1 (hC g g⁻¹)
end Biholomorph
end Release061

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian_oai.{u_1} := @OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian_oai.{u_1}
