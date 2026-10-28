-- Prove2me | solution 1 for OAI.ElasticityPlanar.local_supported_of_dense_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:23:07.880874+00:00
-- url     : https://prove2.me/submissions/2a773323-b6c9-4a27-9205-1e62ce656e23

import Mathlib
import Definitions.Def_OAIQ6El005
import Theorems.Thm_OAI_ElasticityPlanar_local_graph_solution

section
-- module Solutions.OAIQ6_Elast.Elasticity_Compact
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Topology
namespace ElasticityCompact
variable {A P F : Type*} [TopologicalSpace A] [CompactSpace A]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivAt_compact (f : P → C(A,F)) (q : P → C(A,P →L[ℝ] F))
    (hq : Continuous q)
    (hd : ∀ p a, HasFDerivAt (fun p => f p a) (q p a) p) (p : P) :
    HasFDerivAt f (flipLinear (q p)) p := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r,hr,he⟩ := (Metric.continuousAt_iff (f := q) (a := p)).mp hq.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds p hr] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro a
  have hb (z : P) (hz : z∈Metric.ball p r) : ‖q z a-q p a‖ ≤ ε := by
    have hh := le_of_lt (he hz)
    simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := q z) (g := q p) a).trans hh
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hd z a).hasFDerivWithinAt) hb (convex_ball p r)
    (Metric.mem_ball_self hr) hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [CompactSpace A] [NormedSpace ℝ P] [NormedSpace ℝ F] [NormedSpace ℝ E] in
lemma curryCompact_continuous (f : P × E → F) (hf : Continuous f) (j : A → E) (hj : Continuous j) :
    Continuous (curryCompact f hf j hj) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hf.comp (continuous_fst.prodMk (hj.comp continuous_snd))

lemma curryCompact_hasFDerivAt (f : P × E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : A → E) (hj : Continuous j) (p : P) :
    HasFDerivAt (curryCompact f hf.continuous j hj)
      (flipLinear ⟨fun a => (fderiv ℝ f (p,j a)).comp (ContinuousLinearMap.inl ℝ P E),
        ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp (continuous_const.prodMk hj)).clm_comp continuous_const⟩) p := by
  let q : P → C(A,P →L[ℝ] F) := fun p =>
    ⟨fun a => (fderiv ℝ f (p,j a)).comp (ContinuousLinearMap.inl ℝ P E),
      ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp (continuous_const.prodMk hj)).clm_comp continuous_const⟩
  apply hasFDerivAt_compact _ q ?_ ?_ p
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp
      (continuous_fst.prodMk (hj.comp continuous_snd))).clm_comp continuous_const
  · intro p a
    exact (hf.differentiable (by simp) (p,j a)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).prodMk (hasFDerivAt_const (j a) p))

/-- Smooth currying over a compact set. This supplies the Banach-space parameter
regularity needed for the actual coefficient multipliers and linear ODE. -/
theorem curryCompact_contDiff [FiniteDimensional ℝ P]
    (f : P × E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : A → E) (hj : Continuous j) :
    ContDiff ℝ (⊤ : ℕ∞) (curryCompact f hf.continuous j hj) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing f with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact curryCompact_continuous f hf.continuous j hj
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv_apply]
    refine ⟨fun p => (curryCompact_hasFDerivAt f hf j hj p).differentiableAt,by simp,fun v => ?_⟩
    let f' : P × E → F := fun q => fderiv ℝ f q (v,0)
    have hf' : ContDiff ℝ (⊤ : ℕ∞) f' := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    have he : (fun p => fderiv ℝ (curryCompact f hf.continuous j hj) p v)=
        curryCompact f' hf'.continuous j hj := by
      funext p
      ext a
      rw [(curryCompact_hasFDerivAt f hf j hj p).fderiv]
      rfl
    rw [he]
    exact ih f' hf'
end ElasticityCompact

end
end
section
noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal
namespace ElasticityCompact
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {S : Set E} [CompactSpace S]
omit [NormedSpace ℝ E] in
lemma toLinfCompact_ae (hS : MeasurableSet S) (μ : Measure E) (f : C(S,ℂ)) :
    toLinfCompact hS μ f =ᵐ[μ] zeroExtend f := MemLp.coeFn_toLp (zeroExtend_memLp hS μ f)
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A joint smooth family with a fixed compact spatial support is genuinely
smooth with values in L-infinity, not merely pointwise smooth. -/
theorem exists_smooth_linf_family (hS : MeasurableSet S) (μ : Measure E)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) :
    ∃ b : P → Lp ℂ ∞ μ, ContDiff ℝ (⊤ : ℕ∞) b ∧ ∀ p, b p =ᵐ[μ] fun x => a (p,x) := by
  let f := curryCompact a ha.continuous (fun x : S => (x:E)) continuous_subtype_val
  have hf := curryCompact_contDiff a ha (fun x : S => (x:E)) continuous_subtype_val
  refine ⟨fun p => toLinfCompact hS μ (f p),?_,fun p => ?_⟩
  · have hL : ContDiff ℝ (⊤ : ℕ∞) (toLinfCompact hS μ) :=
      (toLinfCompact hS μ).restrictScalars ℝ |>.contDiff
    exact hL.comp hf
  · apply (toLinfCompact_ae hS μ (f p)).trans
    apply Eventually.of_forall
    intro x
    by_cases hx : x∈S
    · exact zeroExtend_mem (f p) ⟨x,hx⟩
    · rw [zeroExtend_notMem _ hx]
      change 0=a (p,x)
      exact (hs p x hx).symm
end ElasticityCompact

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityRegularity
open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A joint smooth compactly spatially supported coefficient yields a genuinely
operator-norm-smooth family of actual L2 multipliers. -/
theorem exists_smooth_lp_multiplier {S : Set E} (hS : IsCompact S)
    (a : P × E → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hs : ∀ p x, x∉S → a (p,x)=0) :
    ∃ M : P → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ContDiff ℝ (⊤ : ℕ∞) M ∧ ∀ p f,
        (M p f : 𝓢'(E,ℂ))=smulLeftCLM ℂ (fun x => a (p,x)) (f : 𝓢'(E,ℂ)) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨b,hb,hbe⟩ := ElasticityCompact.exists_smooth_linf_family hS.measurableSet
    (volume : Measure E) a ha hs
  let B := (ContinuousLinearMap.mul ℂ ℂ).holderL (volume : Measure E) ∞ 2 2
  refine ⟨fun p => B (b p),(B.restrictScalars ℝ).contDiff.comp hb,fun p f => ?_⟩
  have ha' : ContDiff ℝ (⊤ : ℕ∞) (fun x => a (p,x)) :=
    ha.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (fun x => a (p,x)) := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hS.isClosed
    intro x hx
    contrapose! hx
    simpa only [Function.mem_support,not_not] using hs p x hx
  have hm := compact_bounded_multiplier ha' hc
  have hprod : B (b p) f=(hm.toLp (fun x => a (p,x))) • f := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (b p) f,
      Lp.coeFn_lpSMul (r := 2) (hm.toLp _) f,hm.coeFn_toLp,hbe p] with x h₁ h₂ h₃ h₄
    change ((ContinuousLinearMap.mul ℂ ℂ).holder 2 (b p) f) x=_
    rw [h₁,h₂]
    simp only [Pi.smul_apply',h₃,h₄]
    rfl
  rw [hprod,Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth ha') hm]
end ElasticityRegularity
namespace ElasticityPlanar
open MeasureTheory Complex TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators LineDeriv
variable {n : Type*} [Fintype n]

lemma toSchwartz_d (v : ℂ) (φ : Test) : toSchwartz (d v φ)=∂_{v} (toSchwartz φ) := by
  ext z
  rfl
lemma toSchwartz_mul (a : ℂ → ℂ) (ha : a.HasTemperateGrowth) (φ : Test) :
    toSchwartz (mulSmooth a ha.1 φ)=SchwartzMap.smulLeftCLM ℂ a (toSchwartz φ) := by
  ext z
  simp only [toSchwartz_apply,SchwartzMap.smulLeftCLM_apply_apply ha,smul_eq_mul]
  rfl
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions _root_.OAI.ElasticityPlanar.graphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
lemma lp_dist_sum (f : n → PL2) : ((∑ j, f j : PL2) : 𝓢'(ℂ,ℂ))=∑ j, (f j : 𝓢'(ℂ,ℂ)) :=
  map_sum (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2) f _

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators LineDeriv Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]

omit [Fintype n] in
lemma entryInjection_apply (i : n) (f : Hilbert n) : entryInjection i f=(f i : 𝓢'(ℂ,ℂ)) := rfl

lemma planarOperator_apply (a : n → n → ℂ → ℂ) (i : n) (f : Hilbert n) :
    planarOperator a i f=ElasticityPlanarDistribution.dbar (f i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (f j : 𝓢'(ℂ,ℂ)) := by
  simp only [planarOperator,ContinuousLinearMap.comp_apply,add_apply,smul_apply,sum_apply,
    entryInjection_apply,LineDeriv.lineDerivOpCLM_apply,ElasticityPlanarDistribution.dbar]

end ElasticityPlanar
section
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators Manifold
namespace ElasticityRegularity
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
lemma complex_clm_apply_smooth {f : P → E →L[ℂ] F} {g : P → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => f p (g p)) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp hf).clm_apply hg
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
lemma complex_clm_comp_smooth {f : P → F →L[ℂ] G} {g : P → E →L[ℂ] F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (f p).comp (g p)) := by
  let C := ContinuousLinearMap.compL ℂ E F G
  exact complex_clm_apply_smooth ((C.restrictScalars ℝ).contDiff.comp hf) hg
end ElasticityRegularity
namespace ElasticityPlanar
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
theorem exists_smooth_matrix_multiplier {K : Set ℂ} (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0) :
    ∃ M : P → Hilbert n →L[ℂ] Hilbert n,
      ContDiff ℝ (⊤ : ℕ∞) M ∧ ∀ p (f : Hilbert n) i,
        (M p f i : 𝓢'(ℂ,ℂ))=∑ j, smulLeftCLM ℂ (fun z => a i j (p,z)) (f j : 𝓢'(ℂ,ℂ)) := by
  choose L hL hLe using fun i j => exists_smooth_lp_multiplier hK (a i j) (ha i j) (hs i j)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => PL2)
  let M' : P → (n → PL2) →L[ℂ] (n → PL2) := fun p =>
    ContinuousLinearMap.pi (fun i => ∑ j, (L i j p).comp (ContinuousLinearMap.proj j))
  have hM' : ContDiff ℝ (⊤ : ℕ∞) M' := by
    apply (ContinuousLinearMap.piEquivL ℂ (n → PL2) (fun _ : n => PL2)).toContinuousLinearMap.restrictScalars ℝ |>.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    exact ContDiff.sum (fun j _ => complex_clm_comp_smooth (hL i j) contDiff_const)
  refine ⟨fun p => e.symm.toContinuousLinearMap.comp ((M' p).comp e.toContinuousLinearMap),
    complex_clm_comp_smooth contDiff_const (complex_clm_comp_smooth hM' contDiff_const),fun p f i => ?_⟩
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,e,
    PiLp.continuousLinearEquiv_apply,PiLp.continuousLinearEquiv_symm_apply,WithLp.ofLp_toLp,
    M',ContinuousLinearMap.pi_apply,sum_apply,ContinuousLinearMap.proj_apply]
  rw [lp_dist_sum]
  exact Finset.sum_congr rfl (fun j _ => hLe i j p (f j))

end ElasticityPlanar

end
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap ENNReal LineDeriv BigOperators
variable {n : Type*} [Fintype n]
open ElasticityRegularity

lemma dbar_schwartz (v : 𝓢(ℂ,ℂ)) :
    ElasticityPlanarDistribution.dbar (v : 𝓢'(ℂ,ℂ))=(schwartzDbar v : 𝓢'(ℂ,ℂ)) := by
  simp only [ElasticityPlanarDistribution.dbar,schwartzDbar,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]
  rw [map_add,map_smul]
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

open ElasticityRegularity
variable {n : Type*} [Fintype n]
lemma L2_distribution (u : Test) : (L2 u : 𝓢'(ℂ,ℂ))=(toSchwartz u : 𝓢'(ℂ,ℂ)) :=
  Lp.toTemperedDistribution_toLp_eq (toSchwartz u)
lemma planarOperator_test (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u : n → Test) (i : n) :
    planarOperator a i (embed u)=entryInjection i (embed (transport a (fun i j => (ha i j).1) u)) := by
  simp only [planarOperator_apply,entryInjection_apply,embed_apply,L2_distribution,dbar_schwartz]
  have ht : toSchwartz (transport a (fun i j => (ha i j).1) u i)=
      schwartzDbar (toSchwartz (u i))+∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (toSchwartz (u j)) := by
    simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,map_sum,
      toSchwartz_d,schwartzDbar]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => toSchwartz_mul (a i j) (ha i j) (u j))
  rw [ht,map_add,map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => distribution_schwartz_product (ha i j) (toSchwartz (u j)))

/-- Closing compact test graphs preserves the actual distributional operator. -/
theorem graph_equation (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u : closedGraph S a (fun i j => (ha i j).1)) (i : n) :
    planarOperator a i (graphFirst S a (fun i j => (ha i j).1) u)=
      entryInjection i (graphSecond S a (fun i j => (ha i j).1) u) := by
  let F := (planarOperator a i).comp (WithLp.fstL 2 ℂ (Hilbert n) (Hilbert n))
  let G := (entryInjection i).comp (WithLp.sndL 2 ℂ (Hilbert n) (Hilbert n))
  have hc : IsClosed {v : GraphSpace n | F v=G v} := isClosed_eq F.continuous G.continuous
  have hsub : ((testGraph S a (fun i j => (ha i j).1)).range : Set (GraphSpace n)) ⊆ {v | F v=G v} := by
    rintro v ⟨w,rfl⟩
    exact planarOperator_test a ha w i
  exact closure_minimal hsub hc u.property

lemma test_support_distribution {S : Set ℂ} (u : Test) (hu : tsupport (u : ℂ → ℂ)⊆S) :
    LocalEqual Sᶜ (L2 u : 𝓢'(ℂ,ℂ)) 0 := by
  intro φ _ hs
  rw [L2_distribution]
  change (∫ z : ℂ, φ z • toSchwartz u z)=0
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  by_cases hz : z∈S
  · have hz' : z∉tsupport (φ : ℂ → ℂ) := fun h => hs h hz
    rw [image_eq_zero_of_notMem_tsupport hz',zero_smul]
    rfl
  · have hz' : z∉tsupport (u : ℂ → ℂ) := fun h => hz (hu h)
    rw [toSchwartz_apply,image_eq_zero_of_notMem_tsupport hz',smul_zero]
    rfl

/-- Graph closure retains support, in the literal distributional sense. -/
theorem graph_support (S : Set ℂ) (a : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (u : closedGraph S a ha) (i : n) :
    LocalEqual Sᶜ (entryInjection i (graphFirst S a ha u)) 0 := by
  intro φ hc hs
  let F : GraphSpace n →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp ((entryInjection i).comp (WithLp.fstL 2 ℂ (Hilbert n) (Hilbert n)))
  have hclosed : IsClosed {v : GraphSpace n | F v=0} := isClosed_eq F.continuous continuous_const
  have hsub : ((testGraph S a ha).range : Set (GraphSpace n)) ⊆ {v | F v=0} := by
    rintro v ⟨w,rfl⟩
    exact test_support_distribution (w.val i) (w.property i) φ hc hs
  exact closure_minimal hsub hclosed u.property
end ElasticityPlanar
namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma shifted_graph_equation {S : Set ℂ} (a b : n → n → ℂ → ℂ)
    (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (M : Hilbert n →L[ℂ] Hilbert n)
    (hM : ∀ w i, entryInjection i (M w)=
      ∑ j, smulLeftCLM ℂ (b i j) (entryInjection j w)-
        ∑ j, smulLeftCLM ℂ (a i j) (entryInjection j w))
    (u : closedGraph S a (fun i j => (ha i j).1)) (i : n) :
    planarOperator b i (graphFirst S a (fun i j => (ha i j).1) u)=
      entryInjection i ((graphSecond S a (fun i j => (ha i j).1)+
        M.comp (graphFirst S a (fun i j => (ha i j).1))) u) := by
  have h₀ := graph_equation S a ha u i
  simp only [add_apply,ContinuousLinearMap.comp_apply,map_add,hM]
  rw [← h₀,planarOperator_apply,planarOperator_apply]
  simp only [entryInjection_apply]
  abel

lemma graph_test_solution {S : Set ℂ} (a b : n → n → ℂ → ℂ)
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (A : closedGraph S a ha →L[ℂ] Hilbert n)
    (hA : ∀ u i, planarOperator b i (graphFirst S a ha u)=entryInjection i (A u))
    (f : Hilbert n) (v : n → Test) (hv : ∀ i, tsupport (v i : ℂ → ℂ)⊆S)
    (heq : ∀ i, planarOperator b i (embed v)=entryInjection i f) :
    ∃ u : closedGraph S a ha, A u=f := by
  let w : closedGraph S a ha := ⟨testGraph S a ha ⟨v,hv⟩,
    (testGraph S a ha).range.le_topologicalClosure ⟨⟨v,hv⟩,rfl⟩⟩
  refine ⟨w,?_⟩
  apply PiLp.ext
  intro i
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  change entryInjection i (A w)=entryInjection i f
  rw [← hA w i]
  exact heq i

/-- A local smooth supported solution family, derived from compact-test graph
solvability on a dense set. No range-surjectivity assumption is required. -/
theorem local_supported_of_dense_tests_oai {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (f : P → Hilbert n) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {D : Set P} (hD : Dense D)
    (hex : ∀ p∈D, ∃ v : n → Test, (∀ i, tsupport (v i : ℂ → ℂ)⊆S) ∧
      ∀ i, planarOperator (fun i j z => a i j (p,z)) i (embed v)=entryInjection i (f p))
    (p₀ : P) :
    ∃ (U : Set P) (u : P → Hilbert n), IsOpen U ∧ p₀∈U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u U ∧ ∀ p∈U, ∀ i,
        planarOperator (fun i j z => a i j (p,z)) i (u p)=entryInjection i (f p) ∧
        LocalEqual Sᶜ (entryInjection i (u p)) 0 := by
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  let a₀ : n → n → ℂ → ℂ := fun i j z => a i j (p₀,z)
  let ha₀ := fun i j => (hat p₀ i j).1
  obtain ⟨M,hM,hMe⟩ := exists_smooth_matrix_multiplier hK a ha hs
  let I : closedGraph S a₀ ha₀ →L[ℂ] Hilbert n := graphFirst S a₀ ha₀
  let J : closedGraph S a₀ ha₀ →L[ℂ] Hilbert n := graphSecond S a₀ ha₀
  let A : P → closedGraph S a₀ ha₀ →L[ℂ] Hilbert n := fun p => J+(M p-M p₀).comp I
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := contDiff_const.add
    (complex_clm_comp_smooth (hM.sub contDiff_const) contDiff_const)
  have he (p : P) (u : closedGraph S a₀ ha₀) (i : n) :
      planarOperator (fun i j z => a i j (p,z)) i (I u)=entryInjection i (A p u) := by
    apply shifted_graph_equation a₀ (fun i j z => a i j (p,z)) (hat p₀)
      (M p-M p₀) (fun w k => ?_) u i
    simp only [sub_apply,map_sub,entryInjection_apply,hMe p,hMe p₀]
    rfl
  have hex' : ∀ p∈D, ∃ u : closedGraph S a₀ ha₀, A p u=f p := by
    intro p hp
    obtain ⟨v,hv,heq⟩ := hex p hp
    exact graph_test_solution a₀ (fun i j z => a i j (p,z)) ha₀ (A p) (he p) (f p) v hv heq
  have hA₀ : A p₀=graphSecond S a₀ ha₀ := by
    simp only [A,sub_self,ContinuousLinearMap.zero_comp,add_zero,J]
  obtain ⟨U,u,hU,hp₀,hu,huEq⟩ := local_graph_solution hS a₀ ha₀ A hA p₀ hA₀ f hf hD hex'
  refine ⟨U,fun p => I (u p),hU,hp₀,(I.restrictScalars ℝ).contDiff.comp_contDiffOn hu,fun p hp i => ?_⟩
  exact ⟨(he p (u p) i).trans (congrArg (entryInjection i) (huEq p hp)),graph_support S a₀ ha₀ (u p) i⟩
end ElasticityPlanar

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElasticityPlanar.local_supported_of_dense_tests_oai.{u_1, u_2} := @OAI.ElasticityPlanar.local_supported_of_dense_tests_oai.{u_1, u_2}
