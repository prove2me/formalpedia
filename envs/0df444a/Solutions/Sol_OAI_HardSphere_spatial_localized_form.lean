-- Prove2me | solution 1 for OAI.HardSphere.spatial_localized_form
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:34:57.253839+00:00
-- url     : https://prove2.me/submissions/24acd091-933d-494e-9dcc-a21bc4eddc33

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_spatial_spectral_average

section
-- module Solutions.OAIQ054_HS.HardSphere_Capacity_IntegralMulSq
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HardSphere.RayCapacity

lemma integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hi : inner ℝ F G=∫ x, f x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp [F,G,hx,hy,mul_comm]
  have hnF : ‖F‖^2=∫ x, (f x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp [F,hx,pow_two]
  have hnG : ‖G‖^2=∫ x, (g x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp [G,hx,pow_two]
  rw [← hi,← hnF,← hnG,← mul_pow,← sq_abs (inner ℝ F G)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm F G)

lemma interval_memLp_two {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) : MemLp f 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq (hf.mono Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc)).mpr
  exact hf.pow 2 |>.integrableOn_Icc |>.mono_set Ioc_subset_Icc_self

lemma inv_sq_integral {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    (∫ t : ℝ in r..s, (t⁻¹)^2)=r⁻¹-s⁻¹ := by
  have hc : ContinuousOn (fun t : ℝ ↦ (t⁻¹)^2) (uIcc r s) := by
    rw [uIcc_of_le hrs]
    exact (continuousOn_id.inv₀ (fun t ht ↦ (hr.trans_le ht.1).ne')).pow 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ ↦ -(t⁻¹)) (f' := fun t ↦ (t⁻¹)^2) (a := r) (b := s) ?_
    hc.intervalIntegrable
  · simpa only [neg_sub_neg] using h
  · intro t ht
    rw [uIcc_of_le hrs] at ht
    convert (hasDerivAt_inv (hr.trans_le ht.1).ne').neg using 1
    all_goals try with_reducible_and_instances rfl
    simp

lemma ray_pointwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    ‖f s-f r‖^2 ≤ (r⁻¹-s⁻¹)*(∫ t in r..s, ‖deriv f t‖^2*t^2) := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hfg : ContinuousOn (fun t : ℝ ↦ ‖deriv f t‖*t) (Icc r s) :=
    (hdc.norm.mul continuous_id).continuousOn
  have hig : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Icc r s) :=
    continuousOn_id.inv₀ (fun t ht ↦ (hr.trans_le ht.1).ne')
  have hcauchy := integral_mul_sq_le (interval_memLp_two hig) (interval_memLp_two hfg)
  have hprod : (∫ t in Ioc r s, t⁻¹*(‖deriv f t‖*t))=∫ t in r..s, ‖deriv f t‖ := by
    rw [intervalIntegral.integral_of_le hrs]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    field_simp [(hr.trans ht.1).ne']
  have hgrad : (∫ t in Ioc r s, (‖deriv f t‖*t)^2)=∫ t in r..s, ‖deriv f t‖^2*t^2 := by
    rw [intervalIntegral.integral_of_le hrs]
    simp only [mul_pow]
  have hinv : (∫ t in Ioc r s, (t⁻¹)^2)=r⁻¹-s⁻¹ := by
    rw [← intervalIntegral.integral_of_le hrs,inv_sq_integral hr hrs]
  rw [hprod,hgrad,hinv] at hcauchy
  have hdis := norm_sub_le_integral_of_norm_deriv_le_of_le hrs
    hf.continuous.continuousOn (hf.differentiable (by norm_num)).differentiableOn
    (ae_of_all _ (fun _ _ ↦ le_rfl)) (hdc.norm.intervalIntegrable r s)
  exact (pow_le_pow_left₀ (norm_nonneg _) hdis 2).trans hcauchy

lemma ray_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r R : ℝ} (hr : 0 < r) (hR : 0≤R)
    (hz : ∀ t ∈ Icc (0:ℝ) r, f t=0) :
    (∫ t in (0:ℝ)..R, ‖f t‖^2*t^2) ≤
      R^3/(3*r)*(∫ t in (0:ℝ)..R, ‖deriv f t‖^2*t^2) := by
  have hdc := hf.continuous_deriv (by norm_num)
  have hgrad : Continuous (fun t : ℝ ↦ ‖deriv f t‖^2*t^2) :=
    (hdc.norm.pow 2).mul (continuous_id.pow 2)
  let A := ∫ t in (0:ℝ)..R, ‖deriv f t‖^2*t^2
  have hA : 0≤A := intervalIntegral.integral_nonneg_of_forall hR
    (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb (s : ℝ) (hs : s∈Icc (0:ℝ) R) : ‖f s‖^2 ≤ r⁻¹*A := by
    by_cases hsr : s ≤ r
    · rw [hz s ⟨hs.1,hsr⟩,norm_zero,zero_pow (by decide)]
      exact mul_nonneg (inv_nonneg.mpr hr.le) hA
    · have hrs : r ≤ s := le_of_lt (lt_of_not_ge hsr)
      have hp := ray_pointwise hf hr hrs
      rw [hz r ⟨hr.le,le_rfl⟩,sub_zero] at hp
      have hI : 0≤∫ t in r..s, ‖deriv f t‖^2*t^2 :=
        intervalIntegral.integral_nonneg_of_forall hrs (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hIA : (∫ t in r..s, ‖deriv f t‖^2*t^2)≤A :=
        intervalIntegral.integral_mono_interval hr.le hrs hs.2
          (ae_of_all _ (fun _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))) (hgrad.intervalIntegrable 0 R)
      apply hp.trans
      exact (mul_le_mul_of_nonneg_right (sub_le_self _ (inv_nonneg.mpr (hr.le.trans hrs))) hI).trans
        (mul_le_mul_of_nonneg_left hIA (inv_nonneg.mpr hr.le))
  have h := intervalIntegral.integral_mono_on (μ := volume) hR
    (((hf.continuous.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R)
    ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 R)
    (fun t ht ↦ mul_le_mul_of_nonneg_right (hb t ht) (sq_nonneg t))
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq] at h
  rw [intervalIntegral.integral_const_mul,integral_pow] at h
  norm_num at h
  convert h using 1; dsimp [A]; ring

lemma ray_lintegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) {r R B : ℝ} (hr : 0 < r) (hR : 0≤R)
    (hRB : R≤B) (hz : ∀ t ∈ Icc (0:ℝ) r, f t=0)
    {g : ℝ → ℝ} (hg : Continuous g) (hgn : ∀t, 0≤g t)
    (hgrad : ∀t∈Icc (0:ℝ) R, ‖deriv f t‖^2 ≤ g t) :
    (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (‖f t‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (g t)) := by
  have hB := hR.trans hRB
  have hdc := hf.continuous_deriv (by norm_num)
  have hgi : IntervalIntegrable (fun t ↦ g t*t^2) volume 0 R := (hg.mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hfi : IntervalIntegrable (fun t ↦ ‖f t‖^2*t^2) volume 0 R :=
    ((hf.continuous.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hdi : IntervalIntegrable (fun t ↦ ‖deriv f t‖^2*t^2) volume 0 R := ((hdc.norm.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 R
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hR hdi hgi
    (fun t ht ↦ mul_le_mul_of_nonneg_right (hgrad t ht) (sq_nonneg t))
  have hbound := (ray_integral hf hr hR hz).trans
    (mul_le_mul_of_nonneg_left hmono (by positivity : 0≤R^3/(3*r)))
  have hcoef : R^3/(3*r) ≤ B^3/(3*r) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hR hRB 3) (by positivity)
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_right hcoef
    (intervalIntegral.integral_nonneg_of_forall hR (fun t ↦ mul_nonneg (hgn t) (sq_nonneg t))))
  rw [intervalIntegral.integral_of_le hR,intervalIntegral.integral_of_le hR] at hfinal
  have hfI : (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (‖f t‖^2))=
      ENNReal.ofReal (∫ t in Ioc (0:ℝ) R, ‖f t‖^2*t^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Ioc 0 R)) (f := fun t ↦ ‖f t‖^2*t^2)
      hfi.1
      (ae_of_all _ (fun t ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_comm]
  have hgI : (∫⁻ t in Ioc (0:ℝ) R, ENNReal.ofReal (t^2)*ENNReal.ofReal (g t))=
      ENNReal.ofReal (∫ t in Ioc (0:ℝ) R, g t*t^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Ioc 0 R)) (f := fun t ↦ g t*t^2)
      hgi.1
      (ae_of_all _ (fun t ↦ mul_nonneg (hgn t) (sq_nonneg _)))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul (hgn t),mul_comm]
  rw [hfI,hgI,← ENNReal.ofReal_mul (by positivity : 0≤B^3/(3*r))]
  exact ENNReal.ofReal_le_ofReal hfinal

end HardSphere.RayCapacity

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Energy
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

omit [InnerProductSpace ℂ H] in
lemma energy_nonneg (u : H × (J → H)) : 0 ≤ energy u :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma energy_smul (c : ℂ) (u : H × (J → H)) :
    energy (c • u) = ‖c‖ ^ 2 * energy u := by
  simp [energy, norm_smul, mul_pow, Finset.mul_sum]

theorem rayleigh (M : Submodule ℂ (H × (J → H))) (u : H × (J → H))
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  by_cases hz : ‖v.1‖ = 0
  · simpa [hz] using energy_nonneg v
  · let c : ℂ := ((‖v.1‖ : ℂ))⁻¹
    have hc : ‖c‖ = ‖v.1‖⁻¹ := by simp [c, Complex.norm_real]
    have hv' : ‖(c • v).1‖ = 1 := by
      simp only [Prod.smul_fst, norm_smul, hc]
      exact inv_mul_cancel₀ hz
    have h := hmin (c • v) (M.smul_mem c hv) hv'
    rw [energy_smul, hc] at h
    calc
      energy u * ‖v.1‖ ^ 2 ≤ (‖v.1‖⁻¹ ^ 2 * energy v) * ‖v.1‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = energy v := by field_simp

end HardSphere.Variational

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Basic
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere

lemma bosonic_iff_pullback {N : ℕ} {L : Length} (ψ : ScalarL2 N L) :
    bosonic ψ ↔ ∀ σ, permutationPullback σ ψ = ψ := by
  have hae (σ : Equiv.Perm (Fin N)) :
      (permutationPullback σ ψ : Configuration N L → ℂ) =ᵐ[volume]
        fun X ↦ ψ (permuteConfiguration σ X) :=
    Lp.coeFn_compMeasurePreserving ψ (measurePreserving_permute σ)
  constructor
  · intro h σ
    exact Lp.ext ((hae σ).trans (h σ))
  · intro h σ
    have hh := hae σ
    rw [h σ] at hh
    exact hh.symm

section

attribute [local instance] scalarL2_normedAddCommGroup scalarL2_module

@[simp] lemma mem_bosonicSubmodule {N : ℕ} {L : Length} {ψ : ScalarL2 N L} :
    ψ ∈ bosonicSubmodule N L ↔ bosonic ψ := by
  simp only [bosonicSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact (bosonic_iff_pullback ψ).symm

end

@[simp] lemma mem_groundFormSubmodule {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L} :
    u ∈ groundFormSubmodule N L a ↔ u ∈ dirichletDomain N L a ∧ bosonic u.1 := by
  simp [groundFormSubmodule]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FirstVariation
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
namespace HardSphere

theorem IsGroundVector.rayleigh {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (v : Jet N L)
    (hv : v ∈ dirichletDomain N L a) (hb : bosonic v.1) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  exact Variational.rayleigh (groundFormSubmodule N L a) u
    (fun w hw hn ↦ hu.2.2.2 w (mem_groundFormSubmodule.mp hw).1
      (mem_groundFormSubmodule.mp hw).2 hn) v
    (mem_groundFormSubmodule.mpr ⟨hv, hb⟩)

lemma SmoothTest.jet_permute {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (σ : Equiv.Perm (Fin N)) :
    (f.permute σ).jet = permutationJet σ f.jet := by
  apply Prod.ext
  · apply Lp.ext
    exact (MemLp.coeFn_toLp (f.permute σ).memLp).trans
      ((Lp.coeFn_compMeasurePreserving f.jet.1 (measurePreserving_permute σ)).trans
        ((measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
          (MemLp.coeFn_toLp f.memLp))).symm
  · funext p
    apply Lp.ext
    have h := (measurePreserving_permute (L := L) σ).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (f.partial_memLp (σ.symm p.1, p.2)))
    refine (MemLp.coeFn_toLp ((f.permute σ).partial_memLp p)).trans ?_
    change coordDerivative N L (f.toFun ∘ permuteConfiguration σ) p =ᵐ[volume] _
    rw [coordDerivative_permute]
    exact ((Lp.coeFn_compMeasurePreserving _ (measurePreserving_permute σ)).trans h).symm

lemma energy_permutationJet {N : ℕ} {L : Length} (σ : Equiv.Perm (Fin N))
    (u : Jet N L) : energy (permutationJet σ u) = energy u := by
  change (∑ p : Direction N, ‖Lp.compMeasurePreserving _ (measurePreserving_permute σ)
    (u.2 (σ.symm p.1, p.2))‖ ^ 2) = _
  simp only [Lp.norm_compMeasurePreserving]
  exact Equiv.sum_comp (Equiv.prodCongr σ.symm (Equiv.refl (Fin 3)))
    (fun p ↦ ‖u.2 p‖ ^ 2)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ConfigurationPath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace L2Multiplier
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma coe_clm (f : α → ℂ) (hf : MemLp f ∞ μ) (u : Lp ℂ 2 μ) :
    clm f hf u =ᵐ[μ] fun x ↦ f x * u x := coe_apply f hf u

end L2Multiplier

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqIntegral
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace IndicatorStrong
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re]
  · congr 1
    ext x
    simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  · exact L2.integrable_inner f f

end IndicatorStrong

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothMultiplier
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma SmoothTest.jet_multiply {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) (g : SmoothTest N L a) :
    (g.multiply f).jet = f.onJet g.jet := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (g.multiply f).memLp, MemLp.coeFn_toLp g.memLp,
      L2Multiplier.coe_clm f.toFun f.memLp_top g.jet.1] with X h1 h2 h3
    change _ = (f.onScalar g.jet.1) X
    exact h1.trans (by simpa only [SmoothTest.multiply, Pi.mul_apply, SmoothTest.jet,
      SmoothMultiplier.onScalar, h2] using h3.symm)
  · funext p
    apply Lp.ext
    have hder := coordDerivative_mul (f.smooth.differentiable (by simp))
      (g.smooth.differentiable (by simp)) p
    filter_upwards [MemLp.coeFn_toLp ((g.multiply f).partial_memLp p),
      MemLp.coeFn_toLp g.memLp, MemLp.coeFn_toLp (g.partial_memLp p),
      L2Multiplier.coe_clm f.toFun f.memLp_top (g.jet.2 p),
      L2Multiplier.coe_clm _ (f.partial_memLp_top p) g.jet.1,
      Lp.coeFn_add (f.onScalar (g.jet.2 p))
        (L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1)] with X h1 h2 h3 h4 h5 h6
    change _ = (f.onScalar (g.jet.2 p) + L2Multiplier.clm _ (f.partial_memLp_top p) g.jet.1) X
    rw [h6, Pi.add_apply, SmoothMultiplier.onScalar, h4, h5]
    simp only [SmoothTest.jet]
    rw [h1]
    change coordDerivative N L (f.toFun * g.toFun) p X = _
    rw [hder]
    simp only [Pi.add_apply, Pi.mul_apply, h2, h3]
    ring

lemma SmoothMultiplier.onJet_mem_domain {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothMultiplier N L) {u : Jet N L} (hu : u ∈ dirichletDomain N L a) :
    f.onJet u ∈ dirichletDomain N L a := by
  apply map_mem_closure f.onJet.continuous hu
  rintro _ ⟨g, rfl⟩
  exact ⟨g.multiply f, g.jet_multiply f⟩

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqLpIntegral
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

lemma norm_sq_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2=∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,← integral_re]
  · apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,inner_self_eq_norm_sq]
  · exact L2.integrable_inner _ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_Regularize
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HilbertRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt {ε : ℝ} (hε : 0<ε) (z : E) :
    HasFDerivAt (regularize ε) (differential ε z) z := by
  have hn : ‖z‖^2+ε^2≠0 := by positivity
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε^2)).sqrt hn).sub_const ε)
  have hd : differential ε z = Complex.ofRealCLM.comp
      ((1/(2*Real.sqrt (‖z‖^2+ε^2))) • (2 • innerSL ℝ z)) := by
    ext w
    simp [differential,two_smul,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hd]
  exact h

omit [InnerProductSpace ℝ E] in
lemma sqroot_ge_norm (ε : ℝ) (z : E) : ‖z‖≤Real.sqrt (‖z‖^2+ε^2) :=
  (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith [sq_nonneg ε])

lemma differential_apply_le (ε : ℝ) (z w : E) : ‖differential ε z w‖≤‖w‖ := by
  by_cases hz : z=0
  · simp [hz,differential]
  have hp : 0<Real.sqrt (‖z‖^2+ε^2) :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz) (sqroot_ge_norm ε z)
  simp only [differential,smul_apply,ContinuousLinearMap.comp_apply,norm_smul,
    Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos hp,innerSL_apply_apply]
  change _*‖inner ℝ z w‖≤_
  apply le_trans (mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) z w) (by positivity :
    0≤(Real.sqrt (‖z‖^2+ε^2))⁻¹))
  rw [← div_eq_inv_mul,div_le_iff₀ hp]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (sqroot_ge_norm ε z) (norm_nonneg w)

lemma differential_le (ε : ℝ) (z : E) : ‖differential ε z‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simpa only [one_mul] using differential_apply_le ε z w

lemma fderiv_eq {ε : ℝ} (hε : 0<ε) (z : E) :
    fderiv ℝ (regularize ε) z=differential ε z := (hasFDerivAt hε z).fderiv

lemma lipschitz {ε : ℝ} (hε : 0<ε) : LipschitzWith 1 (regularize (E := E) ε) :=
  lipschitzWith_of_nnnorm_fderiv_le ((smooth hε).differentiable (by simp))
    (fun z ↦ by rw [fderiv_eq hε]; exact NNReal.coe_le_coe.mp (differential_le ε z))

lemma norm_le {ε : ℝ} (hε : 0<ε) (z : E) : ‖regularize ε z‖≤‖z‖ := by
  simpa only [zero hε.le,sub_zero,NNReal.coe_one,one_mul] using
    (lipschitz hε).norm_sub_le z 0

omit [InnerProductSpace ℝ E] in
lemma tendsto_regularize (z : E) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n ↦ regularize (e n) z) atTop (𝓝 (‖z‖ : ℂ)) := by
  have h : Tendsto (fun n ↦ Real.sqrt (‖z‖^2+e n^2)-e n) atTop (𝓝 ‖z‖) := by
    have h := (((tendsto_const_nhds (x := ‖z‖^2)).add (he.pow 2)).sqrt.sub he)
    simpa only [zero_pow (by norm_num : 2≠0),add_zero,sub_zero,Real.sqrt_sq (norm_nonneg _)] using h
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp h

end HilbertRegularization

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TestVector
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
section

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

lemma testVector_continuous (F : I → SmoothTest N L a) : Continuous (testVector F) :=
  continuous_of_continuous_lift (testVector_smooth F).continuous

lemma testVector_derivative (F : I → SmoothTest N L a) (X : Configuration N L) (p : Direction N) (i : I) :
    (fderiv ℝ (fun R : LiftedConfiguration N ↦ testVector F (project N L R)) (representative N L X)
      (Pi.single p.1 (Pi.single p.2 1))) i = coordDerivative N L (F i).toFun p X := by
  have hF := (testVector_smooth F).differentiable (by simp) (representative N L X)
  have hi := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2
    (testVector F (project N L (representative N L X))) i).comp (representative N L X) hF.hasFDerivAt).fderiv
  exact (congrArg (fun d ↦ d (Pi.single p.1 (Pi.single p.2 1))) hi).symm

lemma rmsTest_derivative_le (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε)
    (X : Configuration N L) (p : Direction N) :
    ‖coordDerivative N L (SmoothTest.rms F hε).toFun p X‖^2≤
      ∑ i : I, ‖coordDerivative N L (F i).toFun p X‖^2 := by
  have he : (fun R : LiftedConfiguration N ↦ (SmoothTest.rms F hε).toFun (project N L R))=
      HilbertRegularization.regularize ε ∘ (fun R ↦ testVector F (project N L R)) := rfl
  change ‖fderiv ℝ (fun R ↦ (SmoothTest.rms F hε).toFun (project N L R)) (representative N L X)
    (Pi.single p.1 (Pi.single p.2 1))‖^2≤_
  rw [he,fderiv_comp _ ((HilbertRegularization.smooth hε).differentiable (by simp)).differentiableAt
    ((testVector_smooth F).differentiable (by simp)).differentiableAt,
    HilbertRegularization.fderiv_eq hε,ContinuousLinearMap.comp_apply,project_representative]
  calc
    _ ≤ ‖fderiv ℝ (fun R ↦ testVector F (project N L R)) (representative N L X)
        (Pi.single p.1 (Pi.single p.2 1))‖^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (HilbertRegularization.differential_apply_le ε _ _) 2
    _ = _ := by rw [EuclideanSpace.norm_sq_eq]; simp only [testVector_derivative]

end

variable {N : ℕ} {L : Length} {a : ℝ} {I : Type*} [Fintype I]

lemma rmsTest_energy_le (F : I → SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    energy (SmoothTest.rms F hε).jet ≤ ∑ i,energy (F i).jet := by
  classical
  change (∑ p, ‖(SmoothTest.rms F hε).jet.2 p‖^2)≤∑ i,∑ p,‖(F i).jet.2 p‖^2
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  simp only [SmoothTest.jet,norm_sq_toLp_eq_integral]
  rw [← integral_finsetSum (f := fun i X ↦ ‖coordDerivative N L (F i).toFun p X‖^2) Finset.univ (fun i _ ↦ ((F i).continuous_partial p).norm.pow 2 |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  apply integral_mono
  · exact ((SmoothTest.rms F hε).continuous_partial p).norm.pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_finsetSum _ (fun i _ ↦ ((F i).continuous_partial p).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro X
    exact rmsTest_derivative_le F hε X p

lemma rmsTest_norm_limit (F : I → SmoothTest N L a) {e : ℕ → ℝ}
    (he : ∀ k,0<e k) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖(SmoothTest.rms F (he k)).jet.1‖^2) atTop
      (𝓝 (∑ i,‖(F i).jet.1‖^2)) := by
  classical
  have hint : Integrable (fun X ↦ ‖testVector F X‖^2) (volume : Measure (Configuration N L)) :=
    ((testVector_continuous F).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlim := tendsto_integral_of_dominated_convergence (fun X ↦ ‖testVector F X‖^2)
    (fun k ↦ ((SmoothTest.rms F (he k)).continuous.norm.pow 2).aestronglyMeasurable)
    hint (fun k ↦ ae_of_all _ (fun X ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (HilbertRegularization.norm_le (he k) (testVector F X)) 2))
    (ae_of_all _ (fun X ↦ (HilbertRegularization.tendsto_regularize (testVector F X) he0).norm.pow 2))
  have hI : (∫ X : Configuration N L, ‖(‖testVector F X‖ : ℂ)‖^2) =
      ∑ i,‖(F i).jet.1‖^2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    simp only [EuclideanSpace.norm_sq_eq,testVector]
    rw [integral_finsetSum (f := fun i X ↦ ‖(F i).toFun X‖^2) Finset.univ (fun i _ ↦ ((F i).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    simp only [SmoothTest.jet,norm_sq_toLp_eq_integral]
  rw [hI] at hlim
  simp only [SmoothTest.jet,norm_sq_toLp_eq_integral,SmoothTest.rms,rmsTestFun] at hlim ⊢
  exact hlim
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_RmsPermuteFunBosonic
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
variable {N : ℕ} {L : Length} {a : ℝ}

lemma rmsPermute_fun_bosonic (f : SmoothTest N L a) (ε : ℝ) (τ : Equiv.Perm (Fin N))
    (X : Configuration N L) :
    rmsTestFun (fun σ ↦ f.permute σ) ε (permuteConfiguration τ X)=
      rmsTestFun (fun σ ↦ f.permute σ) ε X := by
  unfold rmsTestFun HilbertRegularization.regularize
  have hsum : ‖testVector (fun σ ↦ f.permute σ) (permuteConfiguration τ X)‖^2=
      ‖testVector (fun σ ↦ f.permute σ) X‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,testVector,SmoothTest.permute,Function.comp_apply]
    exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ ↦ ‖f.toFun (permuteConfiguration σ X)‖^2)
  rw [hsum]

lemma rmsPermute_bosonic (f : SmoothTest N L a) {ε : ℝ} (hε : 0<ε) :
    bosonic (SmoothTest.rms (fun σ ↦ f.permute σ) hε).jet.1 := by
  intro τ
  let g := SmoothTest.rms (fun σ ↦ f.permute σ) hε
  have hg : (g.jet.1 : Configuration N L → ℂ)=ᵐ[volume] g.toFun := g.memLp.coeFn_toLp
  have hgt := (measurePreserving_permute τ).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hgt,hg] with X hX hY
  exact hX.trans ((rmsPermute_fun_bosonic f ε τ X).trans hY.symm)

lemma IsGroundVector.rayleigh_smooth_all {u : Jet N L} (hu : IsGroundVector N L a u)
    (f : SmoothTest N L a) : energy u*‖f.jet.1‖^2≤energy f.jet := by
  classical
  let e : ℕ → ℝ := fun k ↦ 1/((k:ℝ)+1)
  have he (k) : 0<e k := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hle (k : ℕ) : energy u*‖(SmoothTest.rms (fun σ ↦ f.permute σ) (he k)).jet.1‖^2≤
      ∑ σ : Equiv.Perm (Fin N), energy (f.permute σ).jet :=
    (hu.rayleigh _ (subset_closure (Set.mem_range_self _)) (rmsPermute_bosonic f (he k))).trans
      (rmsTest_energy_le _ (he k))
  have hl := le_of_tendsto ((rmsTest_norm_limit (fun σ ↦ f.permute σ) he he0).const_mul (energy u))
    (Eventually.of_forall hle)
  have hn (σ : Equiv.Perm (Fin N)) : ‖(f.permute σ).jet.1‖=‖f.jet.1‖ := by
    rw [f.jet_permute]
    exact Lp.norm_compMeasurePreserving _ _
  simp only [hn] at hl
  simp only [SmoothTest.jet_permute,energy_permutationJet,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hl
  have hc : 0<(Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith

lemma IsGroundVector.rayleigh_all {u : Jet N L} (hu : IsGroundVector N L a u)
    (v : Jet N L) (hv : v∈dirichletDomain N L a) : energy u*‖v.1‖^2≤energy v := by
  have hc : IsClosed {w : Jet N L | energy u*‖w.1‖^2≤energy w} := by
    apply isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2))
    exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  apply closure_minimal ?_ hc hv
  rintro _ ⟨f,rfl⟩
  exact hu.rayleigh_smooth_all f
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoeScalar
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma SmoothMultiplier.coe_onScalar {n : ℕ} {L : Length} (f : SmoothMultiplier n L) (u : ScalarL2 n L) :
    f.onScalar u =ᵐ[volume] fun X ↦ f.toFun X*u X := L2Multiplier.coe_clm _ _ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ScalarPartitionIms
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma real_norm_sq (z : ℂ) (hz : conj z=z) : ‖z‖^2=(z*z).re := by
  have he := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z:=z))
  simpa only [hz,Complex.ofReal_re,Complex.normSq_eq_norm_sq] using he

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
noncomputable section

lemma productPartition_apply (n : ℕ) (L : Length) (a c : SmoothMultiplier 1 L)
    (σ : Fin n → Bool) (X : Configuration n L) :
    (productPartition n L a c σ).toFun X=∏ i, (cond (σ i) a c).orbital (X i) := rfl

lemma productPartition_real {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (σ : Fin n → Bool) (X : Configuration n L) :
    conj ((productPartition n L a c σ).toFun X)=(productPartition n L a c σ).toFun X := by
  simp only [productPartition_apply,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp only [Bool.cond_false,Bool.cond_true,SmoothMultiplier.orbital,ha,hc]

lemma productPartition_unity {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (X : Configuration n L) :
    (∑ σ : Fin n → Bool, (productPartition n L a c σ).toFun X*(productPartition n L a c σ).toFun X)=1 := by
  simp_rw [productPartition_apply,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) ↦
    (cond b a c).orbital (X i)*(cond b a c).orbital (X i))]
  simp only [Fintype.sum_bool,Bool.cond_true,Bool.cond_false,hp,Finset.prod_const_one]

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SelectedEnergyAddCompl
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

lemma lipschitz_spatialProject (L : Length) : LipschitzWith 1 (spatialProject L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0≤dist x y)).mpr
  intro j
  calc
    dist ((x j : ℝ) : AddCircle L.val) ((y j : ℝ) : AddCircle L.val)
      = ‖((x j-y j : ℝ) : AddCircle L.val)‖ := by rw [dist_eq_norm,QuotientAddGroup.mk_sub]
    _ ≤ ‖x j-y j‖ := QuotientAddGroup.norm_mk_le_norm
    _ ≤ dist x y := by rw [←dist_eq_norm]; exact dist_le_pi_dist x y j

lemma torusMollify_approximation (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    {f : Torus L → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (x : Torus L) :
    dist (torusMollify L φ f x) (f x) ≤ (C:ℝ)*φ.rOut := by
  obtain ⟨z,hz⟩ : ∃ z : SpatialLift, spatialProject L z=x := by
    refine ⟨fun j ↦ ((AddCircle.equivIco L.val 0) (x j)).val,?_⟩
    ext j
    exact AddCircle.coe_equivIco
  rw [← hz,show torusMollify L φ f (spatialProject L z)=
    (φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun y ↦ f (spatialProject L y))) z from congrFun (torusMollify_lift L φ f) z]
  apply φ.dist_normed_convolution_le (hf.continuous.comp (continuous_spatialProject L)).aestronglyMeasurable
  intro y hy
  have hh : dist (f (spatialProject L y)) (f (spatialProject L z)) ≤ (C:ℝ)*dist y z := by
    simpa only [mul_one,Function.comp_apply] using (hf.comp (lipschitz_spatialProject L)).dist_le_mul y z
  exact hh.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le C.coe_nonneg)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Profile
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma profile_one {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t ≤ h) : profile h t=1 := by
  rw [profile,Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos]; exact (div_le_one hh).mpr ht)]
  ring

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EuclideanTorus
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

lemma euclideanTorusPoint_dist (L : Length) (x y : Torus L) :
    dist (euclideanTorusPoint L x) (euclideanTorusPoint L y)=torusDistance L x y :=
  PiLp.dist_eq_of_L2 _ _

lemma spatialSiteDistance_nonneg (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    0≤ spatialSiteDistance L A x := Metric.infDist_nonneg

lemma spatialSiteDistance_attained (L : Length) (A : Finset (Torus L)) (hA : A.Nonempty) (x : Torus L) :
    ∃ y∈A, spatialSiteDistance L A x=torusDistance L x y := by
  have hc : IsCompact (euclideanTorusPoint L '' (A:Set (Torus L))) :=
    (A.finite_toSet.image _).isCompact
  obtain ⟨y,⟨z,hz,rfl⟩,he⟩ := hc.exists_infDist_eq_dist (by exact Set.Nonempty.image _ hA.to_set) (euclideanTorusPoint L x)
  exact ⟨z,hz,he.trans (euclideanTorusPoint_dist L x z)⟩

lemma smoothSpatialDistance_approximation (L : Length) (A : Finset (Torus L)) (x : Torus L) :
    |smoothSpatialDistance L A x-spatialSiteDistance L A x|≤1 := by
  apply (torusMollify_approximation L spatialDistanceBump (spatialSiteDistance_lipschitz L A) x).trans
  change (spatialMetricConstant:ℝ)*(1/((spatialMetricConstant:ℝ)+1))≤1
  rw [mul_one_div,(div_le_one (by positivity : 0<(spatialMetricConstant:ℝ)+1))]
  linarith

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma spatialInside_apply (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    (spatialInside L A H).toFun X=(spatialSine H (smoothSpatialDistance L A (X 0)):ℂ) := rfl
lemma spatialOutside_apply (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    (spatialOutside L A H).toFun X=(spatialCosine H (smoothSpatialDistance L A (X 0)):ℂ) := rfl
lemma spatialInside_real (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    conj ((spatialInside L A H).toFun X)=(spatialInside L A H).toFun X := by
  rw [spatialInside_apply,Complex.conj_ofReal]
lemma spatialOutside_real (L : Length) (A : Finset (Torus L)) (H : ℝ) (X : Configuration 1 L) :
    conj ((spatialOutside L A H).toFun X)=(spatialOutside L A H).toFun X := by
  rw [spatialOutside_apply,Complex.conj_ofReal]

lemma spatialPartition_unity (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L) :
    (spatialInside L A H).orbital x*(spatialInside L A H).orbital x+
      (spatialOutside L A H).orbital x*(spatialOutside L A H).orbital x=1 := by
  change (Real.sin (spatialAngle H (smoothSpatialDistance L A x)):ℂ)*
    (Real.sin (spatialAngle H (smoothSpatialDistance L A x)):ℂ)+
    (Real.cos (spatialAngle H (smoothSpatialDistance L A x)):ℂ)*
    (Real.cos (spatialAngle H (smoothSpatialDistance L A x)):ℂ)=1
  have h := Real.sin_sq_add_cos_sq (spatialAngle H (smoothSpatialDistance L A x))
  exact_mod_cast (show Real.sin (spatialAngle H (smoothSpatialDistance L A x))*
    Real.sin (spatialAngle H (smoothSpatialDistance L A x))+
    Real.cos (spatialAngle H (smoothSpatialDistance L A x))*Real.cos (spatialAngle H (smoothSpatialDistance L A x))=1 by nlinarith only [h])

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadiusLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory

lemma radiusLaw_tail_eq {t : ℝ} (ht : 0≤t) : radiusLaw.real (Ici t)=Real.exp (-t) := by
  have h := measureReal_compl (μ:=radiusLaw) (s:=Iic t) measurableSet_Iic
  rw [compl_Iic,probReal_univ,←cdf_eq_real,radiusLaw,cdf_expMeasure_eq (by norm_num),ite_eq_left ht,one_mul] at h
  have he : radiusLaw.real (Ici t)=radiusLaw.real (Ioi t) := by
    unfold Measure.real
    rw [measure_congr (Ioi_ae_eq_Ici (μ:=radiusLaw) (a:=t))]
  rw [he]
  change (expMeasure 1).real (Ioi t)=_
  rw [h]
  ring

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter

lemma L2_bounded_weight_integrable {n : ℕ} {L : Length} (u : ScalarL2 n L)
    {v : Configuration n L → ℝ} {B : ℝ} (hv : Measurable v) (hb : ∀ X, |v X|≤B) :
    Integrable (fun X ↦ v X*‖u X‖^2) volume := by
  have hi := ((Lp.memLp u).integrable_norm_pow (by norm_num)).const_mul B
  apply hi.mono' (hv.mul ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2)).aestronglyMeasurable
  exact Eventually.of_forall fun X ↦ by
    change ‖v X*‖u X‖^2‖≤B*‖u X‖^2
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u X‖)]
    exact mul_le_mul_of_nonneg_right (hb X) (sq_nonneg _)

lemma weightedSiteCount_nonneg {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    0≤ weightedSiteCount L A X := by
  unfold weightedSiteCount
  split_ifs <;> positivity

lemma weightedSiteCount_le {n : ℕ} (L : Length) (A : Finset (Torus L)) (X : Configuration n L) :
    weightedSiteCount L A X≤(n:ℝ) := by
  unfold weightedSiteCount
  split_ifs
  · calc
      _ ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum (fun i _ ↦ Real.exp_le_one_iff.mpr (neg_nonpos.mpr (spatialSiteDistance_nonneg L A _)))
      _ = _ := by simp
  · positivity

lemma weightedSiteCount_continuous {n : ℕ} (L : Length) (A : Finset (Torus L)) :
    Continuous (weightedSiteCount (n:=n) L A) := by
  unfold weightedSiteCount
  split_ifs
  · exact continuous_finsetSum _ (fun i _ ↦ Real.continuous_exp.comp
      (((spatialSiteDistance_lipschitz L A).continuous.comp (continuous_apply i)).neg))
  · exact continuous_const

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_Point
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates

lemma polar_integral (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p) = ∫⁻ θ in angle, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r*F (r*Real.cos θ,r*Real.sin θ) := by
  rw [← lintegral_comp_polarCoord_symm F]
  exact setLIntegral_prod_symm _ (by fun_prop)

lemma cylindrical_integral (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p)=∫⁻ θ in angle, ∫⁻ z : ℝ, ∫⁻ r : ℝ,
      ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)) := by
  rw [Measure.volume_eq_prod,lintegral_prod _ hF.aemeasurable]
  have hp (z : ℝ) := polar_integral (fun p ↦ F (z,p)) (hF.comp (measurable_const.prodMk measurable_id))
  conv_lhs => arg 2; ext z; rw [hp z]
  have he (z θ : ℝ) : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)))=
      ∫⁻ r : ℝ, ENNReal.ofReal r*F (z,(r*Real.cos θ,r*Real.sin θ)) := by
    apply setLIntegral_eq_of_support_subset
    intro r hr
    by_contra h
    have hr0 : r≤0 := not_lt.mp h
    simp only [ENNReal.ofReal_of_nonpos hr0,zero_mul,Function.mem_support,ne_eq,not_true_eq_false] at hr
  simp_rw [he]
  apply lintegral_lintegral_swap
  exact (by fun_prop : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
    ENNReal.ofReal p.2*F (p.1.1,(p.2*Real.cos p.1.2,p.2*Real.sin p.1.2)))).lintegral_prod_right.aemeasurable

lemma spherical_integral (F : Point → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p)=∫⁻ θ in angle, ∫⁻ φ in angle, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal (r^2*Real.cos φ)*F (spherePoint r φ θ) := by
  rw [cylindrical_integral F hF]
  apply lintegral_congr
  intro θ
  let G : ℝ × ℝ → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal p.1*F (p.2,(p.1*Real.cos θ,p.1*Real.sin θ))
  have hG : Measurable G := by unfold G; fun_prop
  rw [← lintegral_prod_symm G hG.aemeasurable,← Measure.volume_eq_prod,polar_integral G hG]
  apply lintegral_congr
  intro φ
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp [G,spherePoint]
  rw [← mul_assoc,← ENNReal.ofReal_mul (le_of_lt hr)]
  congr 2
  ring

open Filter
open scoped Topology BigOperators

lemma spherePoint_eq (r φ θ : ℝ) : spherePoint r φ θ=r • direction φ θ := by
  ext <;> simp [spherePoint,direction,mul_assoc]

lemma sqRadius_smul (t : ℝ) (x : Point) : sqRadius (t • x)=t^2*sqRadius x := by
  simp only [sqRadius,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma direction_unit (φ θ : ℝ) : sqRadius (direction φ θ)=1 := by
  have hp := Real.sin_sq_add_cos_sq φ
  have ht := Real.cos_sq_add_sin_sq θ
  dsimp [sqRadius,direction]
  nlinarith [sq_nonneg (Real.cos φ)]

lemma ray_terminal {K : Set Point} (hk : IsClosed K) (hc : Convex ℝ K) (h0 : (0:Point)∈K)
    {B : ℝ} (hB : 0≤B) (hb : ∀ x∈K, sqRadius x≤B^2) {ω : Point} (hu : sqRadius ω=1) :
    ∃ R : ℝ, 0≤R ∧ R≤B ∧ {t : ℝ | 0≤t ∧ t • ω∈K}=Icc 0 R := by
  let S : Set ℝ := {t : ℝ | 0≤t ∧ t • ω∈K}
  have hs0 : (0:ℝ)∈S := by simpa [S] using h0
  have hsclosed : IsClosed S := isClosed_Ici.inter (hk.preimage (continuous_id.smul continuous_const))
  have hsub : S⊆Icc 0 B := by
    intro t ht
    have hn := hb (t • ω) ht.2
    rw [sqRadius_smul,hu,mul_one] at hn
    exact ⟨ht.1,(sq_le_sq₀ ht.1 hB).mp hn⟩
  have hscompact : IsCompact S := isCompact_Icc.of_isClosed_subset hsclosed hsub
  have hsconvex : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),?_⟩
    simpa only [smul_eq_mul,add_smul,mul_smul] using hc hx.2 hy.2 ha hb hab
  let R := sSup S
  have hR : R∈S := hscompact.sSup_mem ⟨0,hs0⟩
  refine ⟨R,(hsub hR).1,(hsub hR).2,?_⟩
  ext t
  constructor
  · intro ht
    exact ⟨ht.1,le_csSup hscompact.bddAbove ht⟩
  · intro ht
    exact hsconvex.ordConnected.out hs0 hR ht

end HardSphere.SphericalCoordinates

namespace HardSphere.SphericalCoordinates
open scoped Topology

lemma linear_unit_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Point →L[ℝ] E) {ω : Point} (hu : sqRadius ω=1) :
    ‖D ω‖^2 ≤ ‖D axis0‖^2+‖D axis1‖^2+‖D axis2‖^2 := by
  have he : ω=ω.1 • axis0+ω.2.1 • axis1+ω.2.2 • axis2 := by
    ext <;> simp [axis0,axis1,axis2]
  have hn : ‖D ω‖ ≤ |ω.1| * ‖D axis0‖+|ω.2.1| * ‖D axis1‖+|ω.2.2| * ‖D axis2‖ := by
    have hd := congrArg D he
    simp only [map_add,map_smul] at hd
    rw [hd]
    calc
      _ ≤ (‖ω.1 • D axis0‖+‖ω.2.1 • D axis1‖)+‖ω.2.2 • D axis2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [norm_smul,Real.norm_eq_abs]
  have hcs (a b c A B C : ℝ) : (a*A+b*B+c*C)^2≤(a^2+b^2+c^2)*(A^2+B^2+C^2) := by
    nlinarith [sq_nonneg (a*B-b*A),sq_nonneg (a*C-c*A),sq_nonneg (b*C-c*B)]
  have hs := hcs |ω.1| |ω.2.1| |ω.2.2| ‖D axis0‖ ‖D axis1‖ ‖D axis2‖
  simp only [sq_abs] at hs
  change ω.1^2+ω.2.1^2+ω.2.2^2=1 at hu
  rw [hu,one_mul] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

lemma gradSq_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Point → E) (x : Point) : 0≤gradSq f x := by unfold gradSq; positivity

lemma continuous_gradSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) : Continuous (gradSq f) := by
  have hd := hf.continuous_fderiv (by norm_num)
  unfold gradSq
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add
    ((hd.clm_apply continuous_const).norm.pow 2)

lemma ray_deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {ω : Point} (hu : sqRadius ω=1) (t : ℝ) :
    ‖deriv (fun s : ℝ ↦ f (s • ω)) t‖^2≤gradSq f (t • ω) := by
  have hd := ((hf.differentiable (by norm_num) (t • ω)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const ω)
  have he : deriv (fun s : ℝ ↦ f (s • ω)) t=fderiv ℝ f (t • ω) ω := by
    simpa only [Function.comp_def,id_eq,one_smul] using hd.deriv
  rw [he]
  simpa only [one_smul,gradSq] using linear_unit_bound (fderiv ℝ f (t • ω)) hu

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadialIndicator
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates

lemma radial_indicator {K : Set Point} {ω : Point} {R : ℝ}
    (hR : {t : ℝ | 0≤t ∧ t • ω∈K}=Icc 0 R) (a : ℝ → ℝ≥0∞) (H : Point → ℝ≥0∞) :
    (∫⁻ t in Ioi (0:ℝ), a t*(K.indicator H) (t • ω))=
      ∫⁻ t in Ioc (0:ℝ) R, a t*H (t • ω) := by
  classical
  rw [← lintegral_indicator measurableSet_Ioi,← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht0 : 0<t
  · have hk : t • ω∈K ↔ t≤R := by
      have he := Set.ext_iff.mp hR t
      simpa only [mem_ofPred_eq,mem_Icc,ht0.le,true_and] using he
    by_cases htR : t≤R
    · simp [ht0,htR,hk.mpr htR]
    · simp [ht0,htR,mt hk.mp htR]
  · simp [ht0]

lemma convex_capacity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {K : Set Point}
    (hk : IsClosed K) (hc : Convex ℝ K) (h0 : (0:Point)∈K)
    {r B : ℝ} (hr : 0 < r) (hB : 0≤B) (hb : ∀x∈K,sqRadius x≤B^2)
    (hz : ∀x, sqRadius x ≤ r^2 → f x=0) :
    (∫⁻ x in K, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ x in K, ENNReal.ofReal (gradSq f x)) := by
  classical
  rw [← lintegral_indicator hk.measurableSet,← lintegral_indicator hk.measurableSet]
  have hm : Measurable (fun x ↦ ENNReal.ofReal (‖f x‖^2)) := by
    simpa only [Pi.pow_apply] using (hf.continuous.norm.pow 2).measurable.ennreal_ofReal
  rw [spherical_integral (K.indicator (fun x ↦ ENNReal.ofReal (‖f x‖^2))) (hm.indicator hk.measurableSet),
    spherical_integral (K.indicator (fun x ↦ ENNReal.ofReal (gradSq f x)))
      (((continuous_gradSq hf).measurable.ennreal_ofReal).indicator hk.measurableSet)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro θ
  dsimp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro φ
  dsimp only
  obtain ⟨R,hR,hRB,he⟩ := ray_terminal hk hc h0 hB hb (direction_unit φ θ)
  simp only [spherePoint_eq]
  rw [radial_indicator he,radial_indicator he]
  have hweight (t : ℝ) : ENNReal.ofReal (t^2*Real.cos φ)=
      ENNReal.ofReal (Real.cos φ)*ENNReal.ofReal (t^2) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_comm]
  simp_rw [hweight,mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,
    mul_comm (ENNReal.ofReal (B^3/(3*r))),mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply RayCapacity.ray_lintegral (f := fun t ↦ f (t • direction φ θ))
    (hf.comp (contDiff_id.smul contDiff_const)) hr hR hRB
  · intro t ht
    apply hz
    rw [sqRadius_smul,direction_unit,mul_one]
    exact pow_le_pow_left₀ ht.1 ht.2 2
  · exact (continuous_gradSq hf).comp (continuous_id.smul continuous_const)
  · intro t
    exact gradSq_nonneg f _
  · intro t _
    exact ray_deriv_bound hf (direction_unit φ θ) t

open scoped Topology

lemma translate_set_lintegral {K : Set Point} (hk : MeasurableSet K) (y : Point)
    (H : Point → ℝ≥0∞) :
    (∫⁻ x in {x | y+x∈K}, H (y+x))=∫⁻x in K,H x := by
  classical
  have hK : MeasurableSet {x : Point | y+x∈K} :=
    hk.preimage (show Measurable (fun x : Point ↦ y+x) from measurable_const.add measurable_id)
  rw [← lintegral_indicator hK,
    ← lintegral_indicator hk]
  have he : ({x | y+x∈K}.indicator (fun x ↦ H (y+x)))=fun x ↦ K.indicator H (y+x) := by
    funext x
    by_cases hx : y+x∈K <;> simp [hx]
  have : (volume : Measure Point).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod,Measure.volume_eq_prod]
    apply Measure.prod.instIsAddLeftInvariant
  rw [he,lintegral_add_left_eq_self]

lemma convex_capacity_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {K : Set Point}
    (hk : IsClosed K) (hc : Convex ℝ K) {y : Point} (hy : y∈K)
    {r B : ℝ} (hr : 0 < r) (hB : 0≤B) (hb : ∀x∈K,sqRadius (x-y)≤B^2)
    (hz : ∀x, sqRadius (x-y) ≤ r^2 → f x=0) :
    (∫⁻ x in K, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (B^3/(3*r))*(∫⁻ x in K, ENNReal.ofReal (gradSq f x)) := by
  let K' : Set Point := {x | y+x∈K}
  have hkc : IsClosed K' := hk.preimage (continuous_const.add continuous_id)
  have hcv : Convex ℝ K' := by
    intro x hx z hz a b ha hb hab
    change y+(a • x+b • z)∈K
    have he : y+(a • x+b • z)=a • (y+x)+b • (y+z) := by
      rw [smul_add,smul_add]
      calc
        y+(a • x+b • z)=(a+b) • y+(a • x+b • z) := by rw [hab,one_smul]
        _ = _ := by rw [add_smul]; abel
    rw [he]
    exact hc hx hz ha hb hab
  have h := convex_capacity (f := fun x ↦ f (y+x)) (K := K') (hf.comp (contDiff_const.add contDiff_id)) hkc hcv
    (by simpa [K'] using hy) hr hB (by
      intro x hx
      simpa only [add_sub_cancel_left] using hb (y+x) hx) (by
      intro x hx
      apply hz (y+x)
      simpa only [add_sub_cancel_left] using hx)
  have hg (x : Point) : gradSq (fun z ↦ f (y+z)) x=gradSq f (y+x) := by
    simp only [gradSq,fderiv_comp_add_left]
  simp_rw [hg] at h
  dsimp only [K'] at h
  rw [translate_set_lintegral hk.measurableSet y (fun x ↦ ENNReal.ofReal (‖f x‖^2)),
    translate_set_lintegral hk.measurableSet y (fun x ↦ ENNReal.ofReal (gradSq f x))] at h
  exact h

lemma cube_radius {b y x : Point} {l : ℝ} (hl : 0≤l) (hy : y∈cube b l) (hx : x∈cube b l) :
    sqRadius (x-y)≤(Real.sqrt 3*l)^2 := by
  have hc (u v a : ℝ) (hu : a≤u ∧ u≤a+l) (hv : a≤v ∧ v≤a+l) : (u-v)^2≤l^2 := by
    have h := (sq_le_sq₀ (abs_nonneg (u-v)) hl).mpr (abs_le.mpr ⟨by linarith,by linarith⟩)
    simpa only [sq_abs] using h
  have h1 := hc x.1 y.1 b.1 ⟨hx.1.1,hx.2.1⟩ ⟨hy.1.1,hy.2.1⟩
  have h2 := hc x.2.1 y.2.1 b.2.1 ⟨hx.1.2.1,hx.2.2.1⟩ ⟨hy.1.2.1,hy.2.2.1⟩
  have h3 := hc x.2.2 y.2.2 b.2.2 ⟨hx.1.2.2,hx.2.2.2⟩ ⟨hy.1.2.2,hy.2.2.2⟩
  simp only [sqRadius,Prod.fst_sub,Prod.snd_sub,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  linarith

lemma cube_capacity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} (hf : ContDiff ℝ 1 f) {b y : Point} {r l : ℝ}
    (hr : 0 < r) (hl : 0≤l) (hy : y∈cube b l)
    (hz : ∀x, sqRadius (x-y) ≤ r^2 → f x=0) :
    (∫⁻ x in cube b l, ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*(∫⁻ x in cube b l, ENNReal.ofReal (gradSq f x)) := by
  have h := convex_capacity_center hf isClosed_Icc (convex_Icc _ _) hy hr
    (mul_nonneg (Real.sqrt_nonneg 3) hl) (fun _ hx ↦ cube_radius hl hy hx) hz
  have he : (Real.sqrt 3*l)^3/(3*r)=Real.sqrt 3*l^3/r := by
    rw [mul_pow,pow_succ (Real.sqrt 3) 2,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
    field_simp
  rw [he] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ParticleGradSq
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open Filter
open scoped Topology BigOperators

lemma insertNth_affine {n : ℕ} (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    i.insertNth x Y=(ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := by
  funext k
  induction k using i.succAboveCases with
  | x => simp
  | p k => simp [Fin.succAbove_ne]

lemma contDiff_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F) (i : Fin (n+1)) (Y : Fin n → Point) :
    ContDiff ℝ 1 (fun x ↦ F (i.insertNth x Y)) := by
  have he : (fun x : Point ↦ i.insertNth x Y)=fun x ↦
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := funext (insertNth_affine i Y)
  change ContDiff ℝ 1 (F ∘ fun x : Point ↦ i.insertNth x Y)
  rw [he]
  exact hF.comp ((ContinuousLinearMap.contDiff _).add contDiff_const)

lemma fderiv_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    fderiv ℝ (fun z ↦ F (i.insertNth z Y)) x=
      (fderiv ℝ F (i.insertNth x Y)).comp (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) := by
  have hi : HasFDerivAt (fun z : Point ↦ i.insertNth z Y)
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x := by
    have he : (fun x : Point ↦ i.insertNth x Y)=fun x ↦
        (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := funext (insertNth_affine i Y)
    rw [he]
    exact (ContinuousLinearMap.hasFDerivAt _).add_const _
  have hf := ((hF.differentiable (by norm_num) (i.insertNth x Y)).hasFDerivAt).comp x hi
  simpa only [Function.comp_def] using hf.fderiv

lemma gradSq_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    gradSq (fun z ↦ F (i.insertNth z Y)) x=particleGradSq F i (i.insertNth x Y) := by
  simp only [gradSq,fderiv_coordinate_slice hF,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply,particleGradSq]

lemma continuous_particleGradSq {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F) (i : Fin n) :
    Continuous (particleGradSq F i) := by
  have hd := hF.continuous_fderiv (by norm_num)
  unfold particleGradSq
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add
    ((hd.clm_apply continuous_const).norm.pow 2)

lemma lintegral_insertNth {n : ℕ} (μ : Fin (n+1) → Measure Point) [∀i,SigmaFinite (μ i)]
    (i : Fin (n+1)) (H : (Fin (n+1) → Point) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ X, H X ∂Measure.pi μ)=
      ∫⁻ Y, ∫⁻ x, H (i.insertNth x Y) ∂μ i ∂Measure.pi (fun j ↦ μ (i.succAbove j)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Point) i
  have he := (measurePreserving_piFinSuccAbove μ i).symm
  rw [← he.lintegral_comp_emb e.symm.measurableEmbedding H]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk]
  apply lintegral_prod_symm
  exact (hH.comp e.symm.measurable).aemeasurable

lemma sector_coordinate_capacity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0≤l) (b : Fin (n+1) → Point)
    (i : Fin (n+1)) (j : Fin n) (hb : b (i.succAbove j)=b i)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b a) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        (∫⁻ X, ENNReal.ofReal (particleGradSq F i X) ∂Measure.pi (fun a ↦ volume.restrict (cube (b a) l))) := by
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  rw [lintegral_insertNth _ i _ hm,lintegral_insertNth _ i _ (continuous_particleGradSq hF i).measurable.ennreal_ofReal,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  have hae : ∀ᵐ Y ∂Measure.pi (fun a : Fin n ↦ volume.restrict (cube (b (i.succAbove a)) l)),
      Y j∈cube (b (i.succAbove j)) l :=
    Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem isClosed_Icc.measurableSet)
  filter_upwards [hae] with Y hY
  rw [hb] at hY
  have h := cube_capacity (contDiff_coordinate_slice hF i Y) hr hl hY (by
    intro x hx
    apply hz (i.insertNth x Y) i (i.succAbove j) (Fin.ne_succAbove i j)
    simpa only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove] using hx)
  simp_rw [gradSq_coordinate_slice hF] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ActiveLabels
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma mem_activeLabels {α ι : Type*} [Fintype α] (σ : α → ι) (i : α) :
    i∈activeLabels σ ↔ ∃ j, j≠i ∧ σ j=σ i := by
  classical
  simp only [activeLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma inactive_card_le {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] (σ : α → ι) :
    (activeLabels σ)ᶜ.card≤Fintype.card ι := by
  classical
  apply Finset.card_le_card_of_injOn σ (by simp)
  intro a ha b _ hab
  by_contra hne
  have ha' : a∉activeLabels σ := Finset.mem_compl.mp ha
  apply ha'
  simp only [activeLabels,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨b,(fun h ↦ hne h.symm),hab.symm⟩

lemma active_card_lower {α ι : Type*} [Fintype α] [Fintype ι] (σ : α → ι) :
    Fintype.card α-Fintype.card ι≤(activeLabels σ).card := by
  classical
  have h := inactive_card_le σ
  rw [Finset.card_compl] at h
  have hc := (activeLabels σ).card_le_univ
  omega

lemma sector_capacity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0≤l) {ι : Type*} [Fintype ι]
    (b : ι → Point) (σ : Fin (n+1) → ι)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ((n+1-Fintype.card ι : ℕ) : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) := by
  classical
  let μ := Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))
  let M := ∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂μ
  let G := fun i ↦ ∫⁻ X, ENNReal.ofReal (particleGradSq F i X) ∂μ
  let C := ENNReal.ofReal (Real.sqrt 3*l^3/r)
  have hi (i : Fin (n+1)) (hi : i∈activeLabels σ) : M≤C*G i := by
    obtain ⟨j,hji,hs⟩ := (mem_activeLabels σ i).mp hi
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
    exact sector_coordinate_capacity hF hr hl (fun a ↦ b (σ a)) i k (congrArg b hs) hz
  have hs := Finset.sum_le_sum hi
  have hcard := active_card_lower σ
  rw [Fintype.card_fin] at hcard
  calc
    _ ≤ ((activeLabels σ).card : ℝ≥0∞)*M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = ∑ _ ∈ activeLabels σ, M := by simp
    _ ≤ ∑ i ∈ activeLabels σ, C*G i := hs
    _ = C*∑ i ∈ activeLabels σ, G i := (Finset.mul_sum _ _ _).symm
    _ ≤ C*∑ i, G i := by gcongr; exact Finset.subset_univ _
    _ = _ := rfl

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SubcubeBase
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma subdivision_index {n : ℕ} (hn : 2≤n) :
    ∃j : ℕ, 1≤j ∧ 2*j^3≤n ∧ n≤16*j^3 := by
  have hex : ∃k : ℕ, n<2*k^3 := by
    refine ⟨n+1,?_⟩
    nlinarith [sq_nonneg (n:ℤ)]
  let k := Nat.find hex
  have hk : n<2*k^3 := Nat.find_spec hex
  have hk0 : k≠0 := by intro he; simp [he] at hk
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : 2*j^3≤n := by
    have ht : j<Nat.find hex := by change j<k; omega
    exact Nat.le_of_not_gt (Nat.find_min hex ht)
  have hjpos : 1≤j := by
    by_contra h
    have : j=0 := by omega
    simp [hj,this] at hk
    omega
  refine ⟨j,hjpos,hmin,?_⟩
  have hp : (j+1)^3≤(2*j)^3 := Nat.pow_le_pow_left (by omega : j+1≤2*j) 3
  rw [hj] at hk
  nlinarith

lemma subdivided_cube_capacity {n j : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r h : ℝ} (hr : 0 < r) (hh : 0≤h) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ((n+1-j^3 : ℕ) : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b (j*h)))) ≤
      ENNReal.ofReal (Real.sqrt 3*h^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b (j*h)))) := by
  rw [cube_configuration_subdivision b hh]
  simp_rw [lintegral_sum_measure,tsum_fintype]
  rw [Finset.mul_sum,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hc : Fintype.card (Fin j × Fin j × Fin j)=j^3 := by simp only [Fintype.card_prod,Fintype.card_fin]; ring
  simpa only [hc] using sector_capacity hF hr hh (subcubeBase b h) σ hz

lemma cube_coefficient {n j : ℕ} (hn : 2≤n) (hj : 1≤j) (hup : 2*j^3≤n) (hlo : n≤16*j^3)
    {r l : ℝ} (hr : 0 < r) (hl : 0<l) :
    (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*(Real.sqrt 3*(l/(j:ℝ))^3/r) ≤
      ((n-j^3:ℕ):ℝ) := by
  have hjs : (0:ℝ)<j := by exact_mod_cast hj
  have hrr := hr.ne'
  have hlr := hl.ne'
  have hsr : Real.sqrt 3≠0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hjn : j^3≤n := by omega
  rw [Nat.cast_sub hjn,Nat.cast_pow]
  have he : (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*(Real.sqrt 3*(l/(j:ℝ))^3/r)=
      (n:ℝ)*((n:ℝ)-1)/(64*(j:ℝ)^3) := by field_simp
  rw [he]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<64*(j:ℝ)^3)).mpr
  have hup' : 2*(j:ℝ)^3≤(n:ℝ) := by exact_mod_cast hup
  have hlo' : (n:ℝ)≤16*(j:ℝ)^3 := by exact_mod_cast hlo
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have ht : (0:ℝ)≤(j:ℝ)^3 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hlo' (show (0:ℝ)≤n by positivity)
  have h2 := mul_le_mul_of_nonneg_left hup' ht
  nlinarith

lemma smooth_cube_energy {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0<l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) ≤
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := by
  by_cases hn : 2≤n
  · obtain ⟨j,hj,hu,hd⟩ := subdivision_index hn
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    have hjr : (0:ℝ)<j := by exact_mod_cast hj
    have hlj : (j:ℝ)*(l/(j:ℝ))=l := by field_simp
    have h := subdivided_cube_capacity (j := j) hF hr (le_of_lt (div_pos hl hjr)) b hz
    rw [hlj] at h
    let A := 1/(64*Real.sqrt 3)*r/l^3*((m+1:ℕ):ℝ)*(((m+1:ℕ):ℝ)-1)
    let C := Real.sqrt 3*(l/(j:ℝ))^3/r
    have hC : 0<C := by dsimp [C]; positivity
    have hA : 0≤A := by
      have hm : (1:ℝ)≤((m+1:ℕ):ℝ) := by norm_num
      have hm' : (0:ℝ)≤((m+1:ℕ):ℝ)-1 := by linarith
      dsimp [A]; positivity
    have hco : ENNReal.ofReal A*ENNReal.ofReal C≤((m+1-j^3:ℕ):ℝ≥0∞) := by
      rw [← ENNReal.ofReal_mul hA]
      have hc := ENNReal.ofReal_le_ofReal (cube_coefficient hn hj hu hd hr hl)
      simpa only [ENNReal.ofReal_natCast] using hc
    apply (ENNReal.mul_le_mul_iff_left (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top).mp
    calc
      _ = (ENNReal.ofReal A*ENNReal.ofReal C)*
          (∫⁻ X,ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := by
            dsimp only [A]; ac_rfl
      _ ≤ ((m+1-j^3:ℕ):ℝ≥0∞)*_ := mul_le_mul_of_nonneg_right hco (by positivity)
      _ ≤ ENNReal.ofReal C*∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := h
      _ = _ := mul_comm _ _
  · have hcases : n=0 ∨ n=1 := by omega
    rcases hcases with rfl | rfl <;> simp

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SpatialPartitionEnergy
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma reindexPoint_apply {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (X : J → Point) (i : I) : reindexPoint e X i=X (e i) := rfl

lemma reindexPoint_single {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (j : J) (v : Point) : reindexPoint e (Pi.single j v)=Pi.single (e.symm j) v := by
  funext i
  by_cases hi : i=e.symm j
  · subst i
    simp [reindexPoint_apply]
  · have hj : e i≠j := by
      intro h
      apply hi
      simpa only [Equiv.symm_apply_apply] using congrArg e.symm h
    simp [reindexPoint_apply,hi,hj]

lemma reindexPoint_preserving {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (μ : I → Measure Point) [∀i,SigmaFinite (μ i)] :
    MeasurePreserving (reindexPoint e) (Measure.pi (fun j ↦ μ (e.symm j))) (Measure.pi μ) := by
  convert measurePreserving_piCongrLeft μ e.symm using 1
  all_goals try with_reducible_and_instances rfl
  funext X i
  simp [reindexPoint_apply,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

lemma indexGradSq_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) (e : I ≃ J) (j : J) (X : J → Point) :
    indexGradSq (F ∘ reindexPoint e) j X=indexGradSq F (e.symm j) (reindexPoint e X) := by
  have hd := ((hF.differentiable (by norm_num) (reindexPoint e X)).hasFDerivAt).comp X
    (reindexPoint e).hasFDerivAt
  simp only [indexGradSq,hd.fderiv,ContinuousLinearMap.comp_apply,reindexPoint_single]

lemma continuous_indexGradSq {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) (i : I) : Continuous (indexGradSq F i) := by
  have hd := hF.continuous_fderiv (by norm_num)
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add
    ((hd.clm_apply continuous_const).norm.pow 2)

lemma finite_cube_energy {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0<l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(Fintype.card I:ℝ)*((Fintype.card I:ℝ)-1))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) ≤
        ∑ i, (∫⁻ X, ENNReal.ofReal (indexGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := by
  let e := Fintype.equivFin I
  let T := reindexPoint e
  have h := smooth_cube_energy (hF.comp T.contDiff) hr hl b (F := F ∘ T) ?_
  rotate_left
  · intro X a c hac hd
    apply hz (T X) (e.symm a) (e.symm c) (fun h ↦ hac (e.symm.injective h))
    simpa only [T,reindexPoint_apply,Equiv.apply_symm_apply] using hd
  have hp := reindexPoint_preserving e (fun _ ↦ volume.restrict (cube b l))
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn : (∫⁻ X,ENNReal.ofReal (‖(F ∘ T) X‖^2)
      ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)))=
      ∫⁻ X,ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)) :=
    hp.lintegral_comp hm
  rw [hn] at h
  have hd (j : Fin (Fintype.card I)) :
      particleGradSq (F ∘ T) j=indexGradSq F (e.symm j) ∘ T := by
    funext X
    exact indexGradSq_reindex hF e j X
  have hg (j : Fin (Fintype.card I)) :
      (∫⁻ X,ENNReal.ofReal (particleGradSq (F ∘ T) j X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)))=
      ∫⁻ X,ENNReal.ofReal (indexGradSq F (e.symm j) X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)) := by
    rw [hd]
    exact hp.lintegral_comp (continuous_indexGradSq hF _).measurable.ennreal_ofReal
  simp_rw [hg] at h
  rw [e.symm.sum_comp (fun i ↦ ∫⁻ X,ENNReal.ofReal (indexGradSq F i X)
    ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)))] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SubsetPointLinear
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma subsetPointFill_affine {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p]
    (Y : {i // ¬p i} → Point) (X : {i // p i} → Point) :
    subsetPointFill p Y X=subsetPointLinear p X+subsetPointFill p Y 0 := by
  funext i
  by_cases hi : p i <;> simp [subsetPointFill,subsetPointLinear,hi]

lemma subsetPointLinear_single {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → Prop) [DecidablePred p] (i : {i // p i}) (v : Point) :
    subsetPointLinear p (Pi.single i v)=Pi.single i.val v := by
  funext j
  by_cases hj : p j
  · by_cases he : j=i.val
    · subst j
      simp [subsetPointLinear,hj]
    · have hn : (⟨j,hj⟩ : Subtype p)≠i := fun h ↦ he (congrArg Subtype.val h)
      simp [subsetPointLinear,hj,he,hn]
  · have he : j≠i.val := by rintro rfl; exact hj i.property
    simp [subsetPointLinear,hj,he]

lemma contDiff_subsetPointFill {I : Type*} [Fintype I]
    (p : I → Prop) [DecidablePred p] (Y : {i // ¬p i} → Point) :
    ContDiff ℝ 1 (subsetPointFill p Y) := by
  have he : subsetPointFill p Y=fun X ↦ subsetPointLinear p X+subsetPointFill p Y 0 :=
    funext (subsetPointFill_affine p Y)
  rw [he]
  exact (subsetPointLinear p).contDiff.add contDiff_const

lemma indexGradSq_subset {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F)
    (p : I → Prop) [DecidablePred p] (Y : {i // ¬p i} → Point)
    (X : {i // p i} → Point) (i : {i // p i}) :
    indexGradSq (F ∘ subsetPointFill p Y) i X=indexGradSq F i.val (subsetPointFill p Y X) := by
  have hd : HasFDerivAt (subsetPointFill p Y) (subsetPointLinear p) X := by
    have he : subsetPointFill p Y=fun X ↦ subsetPointLinear p X+subsetPointFill p Y 0 :=
      funext (subsetPointFill_affine p Y)
    rw [he]
    exact (subsetPointLinear p).hasFDerivAt.add_const _
  have hf := ((hF.differentiable (by norm_num) (subsetPointFill p Y X)).hasFDerivAt).comp X hd
  simp only [indexGradSq,hf.fderiv,ContinuousLinearMap.comp_apply,subsetPointLinear_single]

lemma lintegral_subsetPointFill {I : Type*} [Fintype I]
    (μ : I → Measure Point) [∀i,SigmaFinite (μ i)]
    (p : I → Prop) [DecidablePred p] (H : (I → Point) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ X,H X ∂Measure.pi μ)=
      ∫⁻ Y, ∫⁻ X, H (subsetPointFill p Y X)
        ∂Measure.pi (fun i : {i // p i} ↦ μ i.val)
        ∂Measure.pi (fun i : {i // ¬p i} ↦ μ i.val) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I ↦ Point) p
  have he := (measurePreserving_piEquivPiSubtypeProd μ p).symm
  rw [← he.lintegral_comp_emb e.symm.measurableEmbedding H]
  apply lintegral_prod_symm
  exact (hH.comp e.symm.measurable).aemeasurable

lemma subset_cube_energy {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F)
    (p : I → Prop) [DecidablePred p] {r l : ℝ} (hr : 0 < r) (hl : 0<l)
    (b : I → Point) (b₀ : Point) (hb : ∀i : {i // p i}, b i.val=b₀)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(Fintype.card {i // p i}:ℝ)*
      ((Fintype.card {i // p i}:ℝ)-1))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun i ↦ volume.restrict (cube (b i) l))) ≤
        ∑ i : {i // p i}, (∫⁻ X, ENNReal.ofReal (indexGradSq F i.val X)
          ∂Measure.pi (fun i ↦ volume.restrict (cube (b i) l))) := by
  let μ := fun i ↦ (volume : Measure Point).restrict (cube (b i) l)
  have hslice (Y : {i // ¬p i} → Point) := finite_cube_energy
    (hF.comp (contDiff_subsetPointFill p Y)) hr hl b₀ (F := F ∘ subsetPointFill p Y) (by
      intro X a c hac hd
      apply hz (subsetPointFill p Y X) a.val c.val (fun h ↦ hac (Subtype.ext h))
      simpa only [subsetPointFill,dite_eq_left a.property,dite_eq_left c.property] using hd)
  have hμ : (fun i : {i // p i} ↦ μ i.val)=fun _ ↦ volume.restrict (cube b₀ l) := by
    funext i
    simp only [μ,hb]
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn := lintegral_subsetPointFill μ p (fun X ↦ ENNReal.ofReal (‖F X‖^2)) hm
  rw [hn,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hi := lintegral_mono hslice (μ := Measure.pi (fun i : {i // ¬p i} ↦ μ i.val))
  rw [←hμ] at hi
  simp only [Function.comp_apply,indexGradSq_subset hF] at hi
  apply hi.trans_eq
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (lintegral_subsetPointFill μ p _
      (continuous_indexGradSq hF i.val).measurable.ennreal_ofReal).symm
  · intro i _
    have he := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I ↦ Point) p).symm.measurable
    exact (((continuous_indexGradSq hF i.val).measurable.ennreal_ofReal.comp he).lintegral_prod_left')

lemma sector_cell_energy {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) {r l : ℝ} (hr : 0 < r) (hl : 0<l)
    (b : C → Point) (σ : I → C)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    (∑ v : C, ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(Fintype.card {i // σ i=v}:ℝ)*
      ((Fintype.card {i // σ i=v}:ℝ)-1)))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) ≤
        ∑ i : I, (∫⁻ X, ENNReal.ofReal (indexGradSq F i X)
          ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) := by
  rw [Finset.sum_mul]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun v _ ↦
    subset_cube_energy hF (fun i ↦ σ i=v) hr hl (b ∘ σ) (b v)
      (fun i ↦ congrArg b i.property) hz)
  dsimp only [Function.comp_apply] at h
  rw [Fintype.sum_fiberwise σ (fun i ↦ ∫⁻ X,ENNReal.ofReal (indexGradSq F i X)
    ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l)))] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Capacity_SectorActiveCapacity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma sector_active_capacity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0≤l) {ι : Type*} [Fintype ι]
    (b : ι → Point) (σ : Fin n → ι)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ((activeLabels σ).card : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) := by
  classical
  cases n with
  | zero => simp [activeLabels]
  | succ n =>
    let μ := Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))
    let M := ∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂μ
    let G := fun i ↦ ∫⁻ X, ENNReal.ofReal (particleGradSq F i X) ∂μ
    let C := ENNReal.ofReal (Real.sqrt 3*l^3/r)
    have hi (i : Fin (n+1)) (hi : i∈activeLabels σ) : M≤C*G i := by
      obtain ⟨j,hji,hs⟩ := (mem_activeLabels σ i).mp hi
      obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
      exact sector_coordinate_capacity hF hr hl (fun a ↦ b (σ a)) i k (congrArg b hs) hz
    calc
      _ = ∑ _ ∈ activeLabels σ, M := by simp only [Finset.sum_const,nsmul_eq_mul]; rfl
      _ ≤ ∑ i ∈ activeLabels σ, C*G i := Finset.sum_le_sum hi
      _ = C*∑ i ∈ activeLabels σ, G i := (Finset.mul_sum _ _ _).symm
      _ ≤ C*∑ i, G i := by gcongr; exact Finset.subset_univ _
      _ = _ := rfl

lemma activeLabels_reindex_card {I J C : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (σ : I → C) : (activeLabels (σ ∘ e.symm)).card=(activeLabels σ).card := by
  classical
  have he : (activeLabels (σ ∘ e.symm)).map e.symm.toEmbedding=activeLabels σ := by
    ext i
    simp only [Finset.mem_map,Equiv.toEmbedding_apply,mem_activeLabels,Function.comp_apply]
    constructor
    · rintro ⟨j,⟨k,hkj,hσ⟩,rfl⟩
      exact ⟨e.symm k,fun h ↦ hkj (e.symm.injective h),hσ⟩
    · rintro ⟨k,hki,hσ⟩
      refine ⟨e i,⟨e k,fun h ↦ hki (e.injective h),?_⟩,e.symm_apply_apply i⟩
      simpa only [Equiv.symm_apply_apply] using hσ
  rw [←he,Finset.card_map]

lemma finite_sector_active_capacity {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0 < r) (hl : 0≤l) (b : C → Point) (σ : I → C)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ((activeLabels σ).card : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (indexGradSq F i X)
          ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) := by
  let e := Fintype.equivFin I
  let T := reindexPoint e
  have h := sector_active_capacity (hF.comp T.contDiff) hr hl b (σ ∘ e.symm) (F := F ∘ T) (by
    intro X a c hac hd
    apply hz (T X) (e.symm a) (e.symm c) (fun h ↦ hac (e.symm.injective h))
    simpa only [T,reindexPoint_apply,Equiv.apply_symm_apply] using hd)
  rw [activeLabels_reindex_card] at h
  let μ := fun i ↦ volume.restrict (cube (b (σ i)) l)
  have hp := reindexPoint_preserving e μ
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn : (∫⁻ X,ENNReal.ofReal (‖(F ∘ T) X‖^2) ∂Measure.pi (fun j ↦ μ (e.symm j)))=
      ∫⁻ X,ENNReal.ofReal (‖F X‖^2) ∂Measure.pi μ := hp.lintegral_comp hm
  change _ * (∫⁻ X,ENNReal.ofReal (‖(F ∘ T) X‖^2) ∂Measure.pi (fun j ↦ μ (e.symm j))) ≤ _ at h
  rw [hn] at h
  apply h.trans_eq
  congr 1
  calc
    _ = ∑ j,∫⁻ X,ENNReal.ofReal (indexGradSq F (e.symm j) X) ∂Measure.pi μ := by
      apply Finset.sum_congr rfl
      intro j _
      change (∫⁻ X,ENNReal.ofReal (indexGradSq (F ∘ T) j X) ∂Measure.pi (fun j ↦ μ (e.symm j)))=_
      dsimp only [T]
      simp_rw [indexGradSq_reindex hF]
      exact hp.lintegral_comp (continuous_indexGradSq hF _).measurable.ennreal_ofReal
    _ = _ := Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)

lemma selected_sector_active_capacity {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) (p : I → Prop) [DecidablePred p]
    {r l : ℝ} (hr : 0 < r) (hl : 0≤l) (b : C → Point) (σ : I → C)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    ((activeLabels (fun i : {i // p i} ↦ σ i.val)).card : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i : {i // p i}, (∫⁻ X, ENNReal.ofReal (indexGradSq F i.val X)
          ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) := by
  let μ := fun i ↦ (volume : Measure Point).restrict (cube (b (σ i)) l)
  have hslice (Y : {i // ¬p i} → Point) := finite_sector_active_capacity
    (hF.comp (contDiff_subsetPointFill p Y)) hr hl b (fun i : {i // p i} ↦ σ i.val)
    (F := F ∘ subsetPointFill p Y) (by
      intro X a c hac hd
      apply hz (subsetPointFill p Y X) a.val c.val (fun h ↦ hac (Subtype.ext h))
      simpa only [subsetPointFill,dite_eq_left a.property,dite_eq_left c.property] using hd)
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn := lintegral_subsetPointFill μ p (fun X ↦ ENNReal.ofReal (‖F X‖^2)) hm
  rw [hn,← lintegral_const_mul' _ _ (by simp)]
  have hi := lintegral_mono hslice (μ := Measure.pi (fun i : {i // ¬p i} ↦ μ i.val))
  simp only [Function.comp_apply,indexGradSq_subset hF] at hi
  apply hi.trans_eq
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (lintegral_subsetPointFill μ p _
      (continuous_indexGradSq hF i.val).measurable.ennreal_ofReal).symm
  · intro i _
    have he := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I ↦ Point) p).symm.measurable
    exact (((continuous_indexGradSq hF i.val).measurable.ennreal_ofReal.comp he).lintegral_prod_left')

lemma selected_subdivided_active_capacity {n j : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F) (p : Fin n → Prop) [DecidablePred p]
    {r l : ℝ} (hr : 0 < r) (hl : 0≤l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    (∑ σ : Fin n → (Fin j × Fin j × Fin j),
      ((activeLabels (fun i : {i // p i} ↦ σ i.val)).card : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2)
        ∂Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b l (σ i)) l)))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
      ∑ i : {i // p i}, ∫⁻ X,ENNReal.ofReal (particleGradSq F i.val X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b ((j:ℝ)*l))) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → (Fin j × Fin j × Fin j))))
    (fun σ _ ↦ selected_sector_active_capacity hF p hr hl (subcubeBase b l) σ hz)
  apply h.trans_eq
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [cube_configuration_subdivision b hl,Measure.sum_fintype,MeasureTheory.lintegral_finsetSum_measure]
  rfl

end HardSphere.SphericalCoordinates

open Set Function MeasureTheory
open scoped ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PointFin
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma pointFin_apply (x : Point) : pointFin x=![x.1,x.2.1,x.2.2] := by
  ext i
  fin_cases i <;> rfl

lemma configurationFin_apply {n : ℕ} (X : Fin n → Point) (i : Fin n) :
    configurationFin n X i=pointFin (X i) := rfl

lemma configurationFin_single {n : ℕ} (i : Fin n) (q : Fin 3) :
    configurationFin n (Pi.single i (![axis0,axis1,axis2] q))=Pi.single i (Pi.single q 1) := by
  funext k t
  by_cases hk : k=i
  · subst k
    fin_cases q <;> fin_cases t <;> simp [configurationFin_apply,pointFin_apply,axis0,axis1,axis2]
  · simp [configurationFin_apply,hk]

lemma sqRadius_eq_sum (x : Point) : sqRadius x=∑ j : Fin 3,(pointFin x j)^2 := by
  simp [sqRadius,pointFin_apply,Fin.sum_univ_succ,add_assoc]

end HardSphere.SphericalCoordinates

namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma addCircle_dist_coe_sq_le (L : Length) (x y : ℝ) :
    dist (x : AddCircle L.val) (y : AddCircle L.val)^2≤(x-y)^2 := by
  have hn : dist (x : AddCircle L.val) (y : AddCircle L.val)≤|x-y| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have hh := (sq_le_sq₀ dist_nonneg (abs_nonneg (x-y))).mpr hn
  simpa only [sq_abs] using hh

lemma cubeParameter_distance {n : ℕ} (L : Length) (X : Fin n → Point) (i j : Fin n)
    {a : ℝ} (ha : 0≤a) (hd : sqRadius (X i-X j)≤a^2) :
    torusDistance L (cubeParameter n L X i) (cubeParameter n L X j)≤a := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨ha,le_trans ?_ hd⟩
  rw [sqRadius_eq_sum]
  apply Finset.sum_le_sum
  intro q _
  simpa only [cubeParameter,project,configurationFin_apply,map_sub,Pi.sub_apply] using
    addCircle_dist_coe_sq_le L (pointFin (X i) q) (pointFin (X j) q)

lemma SmoothTest.cube_zero {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) (ha : 0≤a)
    (X : Fin n → Point) (i j : Fin n) (hij : i≠j) (hd : sqRadius (X i-X j)≤a^2) :
    f.toFun (cubeParameter n L X)=0 := by
  by_contra hz
  have h := f.support_allowed (subset_tsupport _ hz)
  have hdist := cubeParameter_distance L X i j ha hd
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (not_lt_of_ge hdist) (h i j hlt)
  · have hs : torusDistance L (cubeParameter n L X j) (cubeParameter n L X i)=
        torusDistance L (cubeParameter n L X i) (cubeParameter n L X j) := by
      simp only [torusDistance,dist_comm]
    rw [← hs] at hdist
    exact (not_lt_of_ge hdist) (h j i hgt)

lemma SmoothTest.cube_smooth {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) :
    ContDiff ℝ 1 (fun X : Fin n → Point ↦ f.toFun (cubeParameter n L X)) :=
  (f.smooth.of_le (by simp)).comp (configurationFin n).contDiff

lemma SmoothTest.cube_derivative {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (X : Fin n → Point) (i : Fin n) (q : Fin 3) :
    fderiv ℝ (fun X : Fin n → Point ↦ f.toFun (cubeParameter n L X)) X
      (Pi.single i (![axis0,axis1,axis2] q))=
        coordDerivative n L f.toFun (i,q) (cubeParameter n L X) := by
  rw [cubeParameter,coordDerivative_project]
  have h := ((f.smooth.differentiable (by simp) (configurationFin n X)).hasFDerivAt).comp X
    (configurationFin n).hasFDerivAt
  rw [show (fun X ↦ f.toFun (cubeParameter n L X))=
    (fun Y ↦ f.toFun (project n L Y)) ∘ configurationFin n from rfl,h.fderiv]
  simp only [ContinuousLinearMap.comp_apply,configurationFin_single]

lemma SmoothTest.cube_gradient {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (X : Fin n → Point) (i : Fin n) :
    particleGradSq (fun X ↦ f.toFun (cubeParameter n L X)) i X=
      ∑ q : Fin 3, ‖coordDerivative n L f.toFun (i,q) (cubeParameter n L X)‖^2 := by
  have h0 := f.cube_derivative X i 0
  have h1 := f.cube_derivative X i 1
  have h2 := f.cube_derivative X i 2
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis0)=_ at h0
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis1)=_ at h1
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis2)=_ at h2
  simp only [particleGradSq,h0,h1,h2,Fin.sum_univ_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
    Fin.sum_univ_zero,add_zero]
  ring

lemma smooth_norm_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) :
    ENNReal.ofReal (‖hf.toLp f‖^2)=∫⁻ x,ENNReal.ofReal (‖f x‖^2) ∂μ := by
  have he : ‖hf.toLp f‖^2=∫ x,‖f x‖^2 ∂μ := by
    rw [@norm_sq_eq_re_inner ℂ,L2.inner_def,← integral_re (L2.integrable_inner (hf.toLp f) (hf.toLp f))]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [hx,inner_self_eq_norm_sq_to_K,RCLike.re_ofReal_pow]
  rw [he,ofReal_integral_eq_lintegral_ofReal (hf.integrable_norm_pow (by decide : (2:ℕ)≠0))
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg ‖f x‖))]

lemma cube_energy_coefficient_nonneg (n : ℕ) {a l : ℝ} (ha : 0≤a) (hl : 0≤l) :
    0≤1/(64*Real.sqrt 3)*a/l^3*(n:ℝ)*((n:ℝ)-1) := by
  cases n with
  | zero => simp
  | succ n =>
    have hn : (0:ℝ)≤((n+1:ℕ):ℝ)-1 := by norm_num
    positivity

lemma SmoothTest.cube_gradient_lintegral {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (i : Fin n) :
    (∫⁻ X, ENNReal.ofReal (particleGradSq (fun X ↦ f.toFun (cubeParameter n L X)) i X)
      ∂Measure.pi (fun _ ↦ volume.restrict (cube 0 L.val)))=
        ∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i,q)‖^2) := by
  simp_rw [f.cube_gradient,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun q _ ↦ by
    exact (((f.continuous_partial (i,q)).measurable.comp (cubeParameter_preserving n L).measurable).norm.pow_const 2).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro q _
  rw [(cubeParameter_preserving n L).lintegral_comp
    (f := fun x ↦ ENNReal.ofReal (‖coordDerivative n L f.toFun (i,q) x‖^2))
    (((f.continuous_partial (i,q)).measurable.norm.pow_const 2).ennreal_ofReal),← smooth_norm_lintegral (f.partial_memLp (i,q))]
  rfl

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CubeCell
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma unitSectorRestriction_ae {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (σ : Fin n → CubeCell K) (u : ScalarL2 n L) :
    unitSectorRestriction hL σ u=ᵐ[unitSectorMeasure n K σ] fun X ↦ u (cubeParameter n L X) := by
  have h₁ := Lp.coeFn_LpToLpOfMeasureLeSMul (c := (1:ℝ≥0∞)) (by norm_num)
    (show unitSectorMeasure n K σ≤1 • Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val)) by
      simpa only [one_smul] using unitSectorMeasure_le hL σ)
    ((Lp.compMeasurePreservingₗᵢ ℝ (cubeParameter n L) (cubeParameter_preserving n L)) u)
  apply h₁.trans
  apply (Measure.absolutelyContinuous_of_le (unitSectorMeasure_le hL σ)).ae_eq
  exact Lp.coeFn_compMeasurePreserving u (cubeParameter_preserving n L)

lemma SmoothTest.unitSector_norm {n K : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (hL : L.val=(K:ℝ)) (σ : Fin n → CubeCell K) :
    ENNReal.ofReal (‖unitSectorRestriction hL σ f.jet.1‖^2)=
      ∫⁻ X,ENNReal.ofReal (‖f.toFun (cubeParameter n L X)‖^2) ∂unitSectorMeasure n K σ := by
  have h₁ := unitSectorRestriction_ae hL σ f.jet.1
  have h₂ : (fun X ↦ f.jet.1 (cubeParameter n L X))=ᵐ[unitSectorMeasure n K σ]
      fun X ↦ f.toFun (cubeParameter n L X) := by
    apply (Measure.absolutelyContinuous_of_le (unitSectorMeasure_le hL σ)).ae_eq
    exact (cubeParameter_preserving n L).quasiMeasurePreserving.ae_eq_comp f.memLp.coeFn_toLp
  have hn := smooth_norm_lintegral (Lp.memLp (unitSectorRestriction hL σ f.jet.1))
  rw [Lp.toLp_coeFn] at hn
  rw [hn]
  apply lintegral_congr_ae
  filter_upwards [h₁.trans h₂] with X hX
  rw [hX]

end HardSphere

namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma selected_sector_cell_energy {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) (p : I → Prop) [DecidablePred p]
    {r l : ℝ} (hr : 0 < r) (hl : 0<l) (b : C → Point) (σ : I → C)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    (∑ v : C, ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*
      (Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
      ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) ≤
        ∑ i : {i // p i}, (∫⁻ X, ENNReal.ofReal (indexGradSq F i.val X)
          ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) := by
  let μ := fun i ↦ (volume : Measure Point).restrict (cube (b (σ i)) l)
  have hslice (Y : {i // ¬p i} → Point) := sector_cell_energy
    (hF.comp (contDiff_subsetPointFill p Y)) hr hl b (fun i : {i // p i} ↦ σ i.val)
    (F := F ∘ subsetPointFill p Y) (by
      intro X a c hac hd
      apply hz (subsetPointFill p Y X) a.val c.val (fun h ↦ hac (Subtype.ext h))
      simpa only [subsetPointFill,dite_eq_left a.property,dite_eq_left c.property] using hd)
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn := lintegral_subsetPointFill μ p (fun X ↦ ENNReal.ofReal (‖F X‖^2)) hm
  rw [hn,← lintegral_const_mul' _ _ (by simp)]
  have hi := lintegral_mono hslice (μ := Measure.pi (fun i : {i // ¬p i} ↦ μ i.val))
  simp only [Function.comp_apply,indexGradSq_subset hF] at hi
  apply hi.trans_eq
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (lintegral_subsetPointFill μ p _
      (continuous_indexGradSq hF i.val).measurable.ennreal_ofReal).symm
  · intro i _
    have he := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I ↦ Point) p).symm.measurable
    exact (((continuous_indexGradSq hF i.val).measurable.ennreal_ofReal.comp he).lintegral_prod_left')

lemma selected_subdivided_cell_energy {n j : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F) (p : Fin n → Prop) [DecidablePred p]
    {r l : ℝ} (hr : 0 < r) (hl : 0<l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c) ≤ r^2 → F X=0) :
    (∑ σ : Fin n → (Fin j × Fin j × Fin j),
      (∑ v : Fin j × Fin j × Fin j,
        ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*
          (Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
          ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2)
        ∂Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b l (σ i)) l)))) ≤
      ∑ i : {i // p i}, ∫⁻ X,ENNReal.ofReal (particleGradSq F i.val X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b ((j:ℝ)*l))) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → (Fin j × Fin j × Fin j))))
    (fun σ _ ↦ selected_sector_cell_energy hF p hr hl (subcubeBase b l) σ hz)
  apply h.trans_eq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [cube_configuration_subdivision b hl.le,Measure.sum_fintype,MeasureTheory.lintegral_finsetSum_measure]
  rfl

end HardSphere.SphericalCoordinates

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HalfShiftCover
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere.GridGeometry

lemma half_shift_cover {x y : ℝ} (h : |x-y|<1/2) :
    ⌊x⌋=⌊y⌋ ∨ ⌊x-1/2⌋=⌊y-1/2⌋ := by
  wlog hxy : x≤y
  · have he := this (x := y) (y := x) (by simpa only [abs_sub_comm] using h) (le_of_not_ge hxy)
    exact he.imp Eq.symm Eq.symm
  have hx := Int.floor_le x
  have hx' := Int.lt_floor_add_one x
  have hd := (abs_lt.mp h).1
  by_cases hy : y<(⌊x⌋:ℝ)+1
  · left
    exact (Int.floor_eq_iff.mpr ⟨hx.trans hxy,hy⟩).symm
  · right
    have hxf : ⌊x-1/2⌋=⌊x⌋ := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
    have hyf : ⌊y-1/2⌋=⌊x⌋ := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
    exact hxf.trans hyf.symm

lemma index_coe {j : ℕ} {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l) (b x : ℝ) :
    index hl hL b (x : AddCircle L)=(⌊(x-b)/l⌋ : ZMod j) := rfl

lemma index_pair_cover {j : ℕ} {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l)
    (x y : AddCircle L) (hd : dist x y<l/2) :
    index hl hL 0 x=index hl hL 0 y ∨
      index hl hL (l/2) x=index hl hL (l/2) y := by
  obtain ⟨d,hdq,hdr⟩ := QuotientAddGroup.exists_norm_mk_lt (x-y) (sub_pos.mpr hd)
  obtain ⟨v,rfl⟩ := QuotientAddGroup.mk_surjective y
  have he : ((d+v : ℝ) : AddCircle L)=x := by
    rw [QuotientAddGroup.mk_add,hdq]
    abel
  rw [←he]
  simp only [index_coe]
  have hb : |(d+v)/l-v/l|<1/2 := by
    rw [← sub_div,add_sub_cancel_right,abs_div,abs_of_pos hl,div_lt_iff₀ hl]
    have hn : |d|<l/2 := by
      rw [Real.norm_eq_abs,←dist_eq_norm] at hdr
      linarith
    linarith
  have hg := half_shift_cover hb
  rcases hg with hg | hg
  · left
    simpa only [sub_zero] using congrArg (fun z : ℤ ↦ (z : ZMod j)) hg
  · right
    have h₁ : (d+v-l/2)/l=(d+v)/l-1/2 := by field_simp
    have h₂ : (v-l/2)/l=v/l-1/2 := by field_simp
    rw [h₁,h₂]
    exact congrArg (fun z : ℤ ↦ (z : ZMod j)) hg

lemma measurable_index {j : ℕ} {L l : ℝ} [Fact (0<L)] (hl : 0<l) (hL : L=(j:ℝ)*l) (b : ℝ) :
    Measurable (index hl hL b) := by
  have he : index hl hL b=(fun x : AddCircle L ↦ (⌊(((AddCircle.equivIco L 0) x).val-b)/l⌋ : ZMod j)) := by
    funext x
    rw [← AddCircle.coe_equivIco (p := L) (a := 0) (y := x),index_coe]
    simp only [AddCircle.coe_equivIco]
  rw [he]
  have hm := ((measurable_subtype_coe.comp (AddCircle.measurableEquivIco L 0).measurable).sub_const b).div_const l
  exact (measurable_of_countable (fun z : ℤ ↦ (z : ZMod j))).comp hm.floor

lemma index_in_cell {j : ℕ} [NeZero j] {L l : ℝ} (hl : 0<l) (hL : L=(j:ℝ)*l)
    (b : ℝ) (v : Fin j) {x : ℝ} (hx : x∈Ico (b+(v:ℝ)*l) (b+(v:ℝ)*l+l)) :
    index hl hL b (x : AddCircle L)=ZMod.finEquiv j v := by
  rw [index_coe]
  have he : ⌊(x-b)/l⌋=(v.val:ℤ) := Int.floor_eq_iff.mpr ⟨by
    rw [Int.cast_natCast,le_div_iff₀ hl]; linarith [hx.1],by
    rw [Int.cast_natCast,div_lt_iff₀ hl]; nlinarith [hx.2]⟩
  rw [he,Int.cast_natCast]
  apply ZMod.val_injective j
  rw [ZMod.val_natCast_of_lt v.isLt]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne j)
  rfl
end HardSphere.GridGeometry

namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma gridSectorRestriction_ae {n j : ℕ} {L : Length} {l : ℝ} (hl : 0≤l) (hL : L.val=(j:ℝ)*l)
    (b : Point) (σ : Fin n → CubeCell j) (u : ScalarL2 n L) :
    gridSectorRestriction hl hL b σ u=ᵐ[gridSectorMeasure n j b l σ] fun X ↦ u (cubeParameter n L X) := by
  have h₁ := Lp.coeFn_LpToLpOfMeasureLeSMul (c := (1:ℝ≥0∞)) (by norm_num)
    (show gridSectorMeasure n j b l σ≤1 • Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val)) by
      simpa only [one_smul] using gridSectorMeasure_le hl hL b σ)
    ((Lp.compMeasurePreservingₗᵢ ℝ (cubeParameter n L) (cubeParameter_preserving_base n L b)) u)
  apply h₁.trans
  apply (Measure.absolutelyContinuous_of_le (gridSectorMeasure_le hl hL b σ)).ae_eq
  exact Lp.coeFn_compMeasurePreserving u (cubeParameter_preserving_base n L b)

lemma gridSector_norm {n j : ℕ} {L : Length} {l : ℝ} (hl : 0≤l) (hL : L.val=(j:ℝ)*l)
    (b : Point) (σ : Fin n → CubeCell j) (u : ScalarL2 n L) :
    ENNReal.ofReal (‖gridSectorRestriction hl hL b σ u‖^2)=
      ∫⁻ X,ENNReal.ofReal (‖u (cubeParameter n L X)‖^2) ∂gridSectorMeasure n j b l σ := by
  have hn := smooth_norm_lintegral (Lp.memLp (gridSectorRestriction hl hL b σ u))
  rw [Lp.toLp_coeFn] at hn
  rw [hn]
  apply lintegral_congr_ae
  filter_upwards [gridSectorRestriction_ae hl hL b σ u] with X hX
  rw [hX]

lemma SmoothTest.gridSector_norm {n j : ℕ} {L : Length} {a l : ℝ} (f : SmoothTest n L a)
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (σ : Fin n → CubeCell j) :
    ENNReal.ofReal (‖gridSectorRestriction hl hL b σ f.jet.1‖^2)=
      ∫⁻ X,ENNReal.ofReal (‖f.toFun (cubeParameter n L X)‖^2) ∂gridSectorMeasure n j b l σ := by
  rw [HardSphere.gridSector_norm]
  apply lintegral_congr_ae
  have h₂ : (fun X ↦ f.jet.1 (cubeParameter n L X))=ᵐ[gridSectorMeasure n j b l σ]
      fun X ↦ f.toFun (cubeParameter n L X) := by
    apply (Measure.absolutelyContinuous_of_le (gridSectorMeasure_le hl hL b σ)).ae_eq
    exact (cubeParameter_preserving_base n L b).quasiMeasurePreserving.ae_eq_comp f.memLp.coeFn_toLp
  filter_upwards [h₂] with X hX
  rw [hX]

lemma SmoothTest.cube_gradient_lintegral_base {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (b : Point) (i : Fin n) :
    (∫⁻ X, ENNReal.ofReal (particleGradSq (fun X ↦ f.toFun (cubeParameter n L X)) i X)
      ∂Measure.pi (fun _ ↦ volume.restrict (cube b L.val)))=
        ∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i,q)‖^2) := by
  simp_rw [f.cube_gradient,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun q _ ↦ by
    exact (((f.continuous_partial (i,q)).measurable.comp (cubeParameter_preserving_base n L b).measurable).norm.pow_const 2).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro q _
  rw [(cubeParameter_preserving_base n L b).lintegral_comp
    (f := fun x ↦ ENNReal.ofReal (‖coordDerivative n L f.toFun (i,q) x‖^2))
    (((f.continuous_partial (i,q)).measurable.norm.pow_const 2).ennreal_ofReal),← smooth_norm_lintegral (f.partial_memLp (i,q))]
  rfl
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SelectedUnitCellPenalty
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma continuous_selectedUnitCellPenalty {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (p : Fin n → Prop) [DecidablePred p] (a : ℝ) :
    Continuous (selectedUnitCellPenalty (n := n) hL p a) := by
  apply continuous_finsetSum
  intro σ _
  exact continuous_const.mul ((unitSectorRestriction hL σ).continuous.norm.pow 2)

lemma SmoothTest.selected_cell_energy {n K : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (hL : L.val=(K:ℝ)) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a) : selectedUnitCellPenalty hL p a f.jet.1≤ selectedEnergy p f.jet := by
  have h := selected_subdivided_cell_energy (j := K) f.cube_smooth p ha (by norm_num : (0:ℝ)<1) 0
    (f.cube_zero ha.le)
  simp only [one_pow,div_one,mul_one,←hL] at h
  have hn (σ : Fin n → CubeCell K) := f.unitSector_norm hL σ
  simp only [unitSectorMeasure] at hn
  simp_rw [←hn,f.cube_gradient_lintegral] at h
  have hco (σ : Fin n → CubeCell K) (v : CubeCell K) :
      0≤1/(64*Real.sqrt 3)*a*(Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
        ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1) := by
    simpa only [one_pow,div_one] using cube_energy_coefficient_nonneg
      (Fintype.card {i : {i // p i} // σ i.val=v}) ha.le (by norm_num : (0:ℝ)≤1)
  have hp : ENNReal.ofReal (selectedUnitCellPenalty hL p a f.jet.1)=
      ∑ σ : Fin n → CubeCell K,
        (∑ v : CubeCell K,ENNReal.ofReal (1/(64*Real.sqrt 3)*a*(Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*
          ((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)))*ENNReal.ofReal (‖unitSectorRestriction hL σ f.jet.1‖^2) := by
    rw [selectedUnitCellPenalty,ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ mul_nonneg (Finset.sum_nonneg (fun v _ ↦ hco σ v)) (sq_nonneg _))]
    apply Finset.sum_congr rfl
    intro σ _
    rw [ENNReal.ofReal_mul (Finset.sum_nonneg (fun v _ ↦ hco σ v)),ENNReal.ofReal_sum_of_nonneg (fun v _ ↦ hco σ v)]
  have he : ENNReal.ofReal (selectedEnergy p f.jet)=∑ i : {i // p i},∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i.val,q)‖^2) := by
    rw [selectedEnergy,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)
  apply (ENNReal.ofReal_le_ofReal_iff (by unfold selectedEnergy; positivity)).mp
  rw [hp,he]
  exact h

lemma dirichlet_selected_cell_energy {n K : ℕ} {L : Length} {a : ℝ}
    (hL : L.val=(K:ℝ)) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a) (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    selectedUnitCellPenalty hL p a u.1≤ selectedEnergy p u := by
  have hc : IsClosed {u : Jet n L | selectedUnitCellPenalty hL p a u.1≤ selectedEnergy p u} := by
    apply isClosed_le
    · exact (continuous_selectedUnitCellPenalty hL p a).comp continuous_fst
    · exact continuous_finsetSum _ (fun i _ ↦ continuous_finsetSum _
        (fun q _ ↦ ((continuous_apply (i.val,q)).comp continuous_snd).norm.pow 2))
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact f.selected_cell_energy hL p ha) hu

lemma measurable_unitSite {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) :
    Measurable (unitSite hL) :=
  ((measurable_unitIndex hL).comp (measurable_pi_apply 0)).prodMk
    (((measurable_unitIndex hL).comp (measurable_pi_apply 1)).prodMk
      ((measurable_unitIndex hL).comp (measurable_pi_apply 2)))

lemma unitIndex_coe {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (v : Fin K) {x : ℝ}
    (hx : x∈Ico (v:ℝ) ((v:ℝ)+1)) : unitIndex hL (x : AddCircle L.val)=v := by
  have hx0 : 0≤x := (Nat.cast_nonneg v.val).trans hx.1
  have hxL : x<L.val := by
    rw [hL]
    have hv : (v:ℝ)+1≤(K:ℝ) := by exact_mod_cast v.isLt
    exact hx.2.trans_le hv
  apply Fin.ext
  change ⌊((AddCircle.equivIco L.val 0) (x : AddCircle L.val)).val⌋₊=v.val
  rw [AddCircle.equivIco_coe_eq ⟨hx0,by simpa only [zero_add] using hxL⟩]
  exact (Nat.floor_eq_iff hx0).mpr hx

lemma cube_ae_halfOpen (b : Point) (l : ℝ) :
    ∀ᵐ x ∂volume.restrict (cube b l),
      x.1∈Ico b.1 (b.1+l) ∧ x.2.1∈Ico b.2.1 (b.2.1+l) ∧ x.2.2∈Ico b.2.2 (b.2.2+l) := by
  rw [cube_volume,← restrict_Ico_eq_restrict_Icc,← restrict_Ico_eq_restrict_Icc,
    ← restrict_Ico_eq_restrict_Icc]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Ico] with z hz
  exact ⟨hx,hy,hz⟩

lemma unitSector_site_ae {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (σ : Fin n → CubeCell K) :
    ∀ᵐ X ∂unitSectorMeasure n K σ, ∀ i, unitSite hL (cubeParameter n L X i)=σ i := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ X ∂unitSectorMeasure n K σ,
      (X i).1∈Ico (subcubeBase 0 1 (σ i)).1 ((subcubeBase 0 1 (σ i)).1+1) ∧
      (X i).2.1∈Ico (subcubeBase 0 1 (σ i)).2.1 ((subcubeBase 0 1 (σ i)).2.1+1) ∧
      (X i).2.2∈Ico (subcubeBase 0 1 (σ i)).2.2 ((subcubeBase 0 1 (σ i)).2.2+1) :=
    (Measure.tendsto_eval_ae_ae (μ := fun k : Fin n ↦ volume.restrict (cube (subcubeBase 0 1 (σ k)) 1)) (i := i)).eventually (cube_ae_halfOpen (subcubeBase 0 1 (σ i)) 1)
  filter_upwards [h] with X hX
  rcases hX with ⟨h0,h1,h2⟩
  apply Prod.ext
  · apply unitIndex_coe hL (σ i).1
    change (X i).1∈Ico _ _
    simpa only [subcubeBase,zero_add,mul_one,Prod.fst_zero] using h0
  · apply Prod.ext
    · apply unitIndex_coe hL (σ i).2.1
      change (X i).2.1∈Ico _ _
      simpa only [subcubeBase,zero_add,mul_one,Prod.fst_zero,Prod.snd_zero] using h1
    · apply unitIndex_coe hL (σ i).2.2
      change (X i).2.2∈Ico _ _
      simpa only [subcubeBase,zero_add,mul_one,Prod.snd_zero] using h2

lemma occupationWeight_nonneg {n K : ℕ} (p : Fin n → Prop) [DecidablePred p]
    {a : ℝ} (ha : 0≤a) (σ : Fin n → CubeCell K) : 0≤occupationWeight p a σ := by
  apply Finset.sum_nonneg
  intro v _
  simpa only [one_pow,div_one] using cube_energy_coefficient_nonneg
    (Fintype.card {i : {i // p i} // σ i.val=v}) ha (by norm_num : (0:ℝ)≤1)

lemma unitSector_norm {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (σ : Fin n → CubeCell K)
    (u : ScalarL2 n L) : ENNReal.ofReal (‖unitSectorRestriction hL σ u‖^2)=
      ∫⁻ X,ENNReal.ofReal (‖u (cubeParameter n L X)‖^2) ∂unitSectorMeasure n K σ := by
  have hn := smooth_norm_lintegral (Lp.memLp (unitSectorRestriction hL σ u))
  rw [Lp.toLp_coeFn] at hn
  rw [hn]
  apply lintegral_congr_ae
  filter_upwards [unitSectorRestriction_ae hL σ u] with X hX
  rw [hX]

lemma selectedUnitCellPenalty_eq_integral {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] {a : ℝ} (ha : 0≤a) (u : ScalarL2 n L) :
    ENNReal.ofReal (selectedUnitCellPenalty hL p a u)=
      ∫⁻ X, ENNReal.ofReal (∑ v : CubeCell K, 1/(64*Real.sqrt 3)*a*
        (unitOccupation hL p v X:ℝ)*((unitOccupation hL p v X:ℝ)-1))*
          ENNReal.ofReal (‖u X‖^2) := by
  let H : Configuration n L → ℝ≥0∞ := fun X ↦
    ENNReal.ofReal (occupationWeight p a (fun i ↦ unitSite hL (X i)))*ENNReal.ofReal (‖u X‖^2)
  have hm : Measurable H := by
    dsimp only [H]
    have h₁ : Measurable (fun X : Configuration n L ↦ ENNReal.ofReal (occupationWeight p a (fun i ↦ unitSite hL (X i)))) :=
      ((measurable_of_finite (occupationWeight (K := K) p a)).comp
        (Measurable.of_eval fun i ↦ (measurable_unitSite hL).comp (measurable_pi_apply i))).ennreal_ofReal
    have h₂ : Measurable (fun X : Configuration n L ↦ ENNReal.ofReal (‖u X‖^2)) :=
      ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2).ennreal_ofReal
    exact h₁.mul h₂
  change _ = ∫⁻ X,H X
  rw [← (cubeParameter_preserving n L).lintegral_comp hm]
  have hmμ : Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val))=
      ∑ σ : Fin n → CubeCell K, unitSectorMeasure n K σ := by
    rw [hL,← mul_one (K:ℝ),cube_configuration_subdivision 0 (by norm_num : (0:ℝ)≤1),Measure.sum_fintype]
    rfl
  rw [hmμ,MeasureTheory.lintegral_finsetSum_measure]
  change ENNReal.ofReal (∑ σ : Fin n → CubeCell K,
    occupationWeight p a σ*‖unitSectorRestriction hL σ u‖^2)=_
  rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ mul_nonneg (occupationWeight_nonneg p ha σ) (sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [ENNReal.ofReal_mul (occupationWeight_nonneg p ha σ),unitSector_norm]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [unitSector_site_ae hL σ] with X hX
  have he : (fun i ↦ unitSite hL (cubeParameter n L X i))=σ := funext hX
  change _ = ENNReal.ofReal (occupationWeight p a (fun i ↦ unitSite hL (cubeParameter n L X i)))*_
  rw [he]

lemma dirichlet_physical_cell_energy {n K : ℕ} {L : Length} {a : ℝ}
    (hL : L.val=(K:ℝ)) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    (∫⁻ X, ENNReal.ofReal (∑ v : CubeCell K, 1/(64*Real.sqrt 3)*a*
      (unitOccupation hL p v X:ℝ)*((unitOccupation hL p v X:ℝ)-1))*
        ENNReal.ofReal (‖u.1 X‖^2)) ≤ ENNReal.ofReal (selectedEnergy p u) := by
  rw [← selectedUnitCellPenalty_eq_integral hL p ha.le]
  exact ENNReal.ofReal_le_ofReal (dirichlet_selected_cell_energy hL p ha u hu)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridActivePenalty
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma continuous_gridActivePenalty {n j : ℕ} {L : Length} {l : ℝ}
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] :
    Continuous (gridActivePenalty (n := n) hl hL b p) := by
  apply continuous_finsetSum
  intro σ _
  exact continuous_const.mul ((gridSectorRestriction hl hL b σ).continuous.norm.pow 2)

lemma selectedEnergy_nonneg {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] (u : Jet n L) :
    0≤ selectedEnergy p u := by unfold selectedEnergy; positivity

lemma selectedEnergy_ofReal {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] (u : Jet n L) :
    ENNReal.ofReal (selectedEnergy p u)=∑ i : {i // p i},∑ q : Fin 3, ENNReal.ofReal (‖u.2 (i.val,q)‖^2) := by
  rw [selectedEnergy,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
  apply Finset.sum_congr rfl
  intro i _
  exact ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)

lemma SmoothTest.active_grid_energy {n j : ℕ} {L : Length} {a l : ℝ} (f : SmoothTest n L a)
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a) :
    gridActivePenalty hl hL b p f.jet.1≤Real.sqrt 3*l^3/a*selectedEnergy p f.jet := by
  have h := selected_subdivided_active_capacity (j := j) f.cube_smooth p ha hl b (f.cube_zero ha.le)
  rw [←hL] at h
  have hn (σ : Fin n → CubeCell j) := f.gridSector_norm hl hL b σ
  simp only [gridSectorMeasure] at hn
  simp_rw [←hn,f.cube_gradient_lintegral_base b] at h
  have hp : ENNReal.ofReal (gridActivePenalty hl hL b p f.jet.1)=
      ∑ σ : Fin n → CubeCell j,
        ((activeLabels (fun i : {i // p i} ↦ σ i.val)).card:ℝ≥0∞)*ENNReal.ofReal (‖gridSectorRestriction hl hL b σ f.jet.1‖^2) := by
    rw [gridActivePenalty,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
    apply Finset.sum_congr rfl
    intro σ _
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (selectedEnergy_nonneg p f.jet))).mp
  rw [hp,ENNReal.ofReal_mul (by positivity),selectedEnergy_ofReal]
  exact h

lemma dirichlet_active_grid_energy {n j : ℕ} {L : Length} {a l : ℝ}
    (hl : 0≤l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    gridActivePenalty hl hL b p u.1≤Real.sqrt 3*l^3/a*selectedEnergy p u := by
  have hc : IsClosed {u : Jet n L | gridActivePenalty hl hL b p u.1≤Real.sqrt 3*l^3/a*selectedEnergy p u} := by
    apply isClosed_le
    · exact (continuous_gridActivePenalty hl hL b p).comp continuous_fst
    · exact continuous_const.mul (continuous_finsetSum _ (fun i _ ↦ continuous_finsetSum _
        (fun q _ ↦ ((continuous_apply (i.val,q)).comp continuous_snd).norm.pow 2)))
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact f.active_grid_energy hl hL b p ha) hu

lemma measurable_gridSite {j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) : Measurable (gridSite hl hL b) := by
  have hm (c : ℝ) (q : Fin 3) : Measurable (fun x : Torus L ↦ (ZMod.finEquiv j).symm (GridGeometry.index hl hL c (x q))) :=
    (measurable_of_finite (ZMod.finEquiv j).symm).comp ((GridGeometry.measurable_index hl hL c).comp (measurable_pi_apply q))
  exact (hm b.1 0).prodMk ((hm b.2.1 1).prodMk (hm b.2.2 2))

lemma gridSector_site_ae {n j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (σ : Fin n → CubeCell j) :
    ∀ᵐ X ∂gridSectorMeasure n j b l σ, ∀ i, gridSite hl hL b (cubeParameter n L X i)=σ i := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ X ∂gridSectorMeasure n j b l σ,
      (X i).1∈Ico (subcubeBase b l (σ i)).1 ((subcubeBase b l (σ i)).1+l) ∧
      (X i).2.1∈Ico (subcubeBase b l (σ i)).2.1 ((subcubeBase b l (σ i)).2.1+l) ∧
      (X i).2.2∈Ico (subcubeBase b l (σ i)).2.2 ((subcubeBase b l (σ i)).2.2+l) :=
    (Measure.tendsto_eval_ae_ae (μ := fun k : Fin n ↦ volume.restrict (cube (subcubeBase b l (σ k)) l)) (i := i)).eventually (cube_ae_halfOpen (subcubeBase b l (σ i)) l)
  filter_upwards [h] with X hX
  rcases hX with ⟨h0,h1,h2⟩
  have he0 := GridGeometry.index_in_cell hl hL b.1 (σ i).1 h0
  have he1 := GridGeometry.index_in_cell hl hL b.2.1 (σ i).2.1 h1
  have he2 := GridGeometry.index_in_cell hl hL b.2.2 (σ i).2.2 h2
  change ((ZMod.finEquiv j).symm (GridGeometry.index hl hL b.1 ((X i).1 : AddCircle L.val)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL b.2.1 ((X i).2.1 : AddCircle L.val)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL b.2.2 ((X i).2.2 : AddCircle L.val)))=σ i
  rw [he0,he1,he2]
  simp only [RingEquiv.symm_apply_apply,Prod.eta]

lemma measurable_gridActiveCount {n j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] :
    Measurable (gridActiveCount (n := n) hl hL b p) :=
  (measurable_of_finite (fun σ : {i // p i} → CubeCell j ↦ (activeLabels σ).card)).comp
    (Measurable.of_eval fun i ↦ (measurable_gridSite hl hL b).comp (measurable_pi_apply i.val))

lemma gridActivePenalty_eq_integral {n j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p]
    (u : ScalarL2 n L) : ENNReal.ofReal (gridActivePenalty hl.le hL b p u)=
      ∫⁻ X, (gridActiveCount hl hL b p X:ℝ≥0∞)*ENNReal.ofReal (‖u X‖^2) := by
  let H : Configuration n L → ℝ≥0∞ := fun X ↦ (gridActiveCount hl hL b p X:ℝ≥0∞)*ENNReal.ofReal (‖u X‖^2)
  have hm : Measurable H := by
    have h₁ : Measurable (fun X : Configuration n L ↦ (gridActiveCount hl hL b p X:ℝ≥0∞)) :=
      (measurable_of_countable (fun k : ℕ ↦ (k:ℝ≥0∞))).comp (measurable_gridActiveCount hl hL b p)
    have h₂ : Measurable (fun X : Configuration n L ↦ ENNReal.ofReal (‖u X‖^2)) :=
      ((Lp.stronglyMeasurable u).measurable.norm.pow_const 2).ennreal_ofReal
    exact h₁.mul h₂
  change _ = ∫⁻ X,H X
  rw [← (cubeParameter_preserving_base n L b).lintegral_comp hm]
  have hmμ : Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b L.val))=
      ∑ σ : Fin n → CubeCell j, gridSectorMeasure n j b l σ := by
    rw [hL,cube_configuration_subdivision b hl.le,Measure.sum_fintype]
    rfl
  rw [hmμ,MeasureTheory.lintegral_finsetSum_measure]
  rw [gridActivePenalty,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
  apply Finset.sum_congr rfl
  intro σ _
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,gridSector_norm]
  rw [← lintegral_const_mul' _ _ (by simp)]
  apply lintegral_congr_ae
  filter_upwards [gridSector_site_ae hl hL b σ] with X hX
  have he : (fun i : {i // p i} ↦ gridSite hl hL b (cubeParameter n L X i.val))=fun i : {i // p i} ↦ σ i.val := funext (fun i ↦ hX i.val)
  change _ = ((activeLabels (fun i : {i // p i} ↦ gridSite hl hL b (cubeParameter n L X i.val))).card:ℝ≥0∞)*_
  rw [he]

lemma dirichlet_physical_grid_energy {n j : ℕ} [NeZero j] {L : Length} {a l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (b : Point) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    (∫⁻ X, (gridActiveCount hl hL b p X:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2)) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/a*selectedEnergy p u) := by
  rw [←gridActivePenalty_eq_integral]
  exact ENNReal.ofReal_le_ofReal (dirichlet_active_grid_energy hl.le hL b p ha u hu)

lemma coordinate_distance_le (L : Length) (x y : Torus L) (q : Fin 3) :
    dist (x q) (y q)≤torusDistance L x y := by
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun t _ ↦ sq_nonneg (dist (x t) (y t))) (Finset.mem_univ q)

lemma halfGrid_pair_cover {j : ℕ} [NeZero j] {L : Length} {l : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (x y : Torus L) (hd : torusDistance L x y<l/2) :
    ∃ b : Fin 3 → Bool, gridSite hl hL (halfGridBase l b) x=gridSite hl hL (halfGridBase l b) y := by
  have hh (q : Fin 3) : ∃ t : Bool, GridGeometry.index hl hL (if t then l/2 else 0) (x q)=GridGeometry.index hl hL (if t then l/2 else 0) (y q) := by
    rcases GridGeometry.index_pair_cover hl hL (x q) (y q) ((coordinate_distance_le L x y q).trans_lt hd) with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose b hb using hh
  refine ⟨b,?_⟩
  change ((ZMod.finEquiv j).symm (GridGeometry.index hl hL (if b 0 then l/2 else 0) (x 0)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL (if b 1 then l/2 else 0) (x 1)),
    (ZMod.finEquiv j).symm (GridGeometry.index hl hL (if b 2 then l/2 else 0) (x 2)))=_
  rw [hb 0,hb 1,hb 2]
  rfl

lemma nearLabels_card_le_grids {n j : ℕ} [NeZero j] {L : Length} {l s : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (hs : 4*s<l) (p : Fin n → Prop) [DecidablePred p]
    (X : Configuration n L) :
    (nearLabels p s X).card≤∑ b : Fin 3 → Bool, gridActiveCount hl hL (halfGridBase l b) p X := by
  classical
  let A := fun b : Fin 3 → Bool ↦ activeLabels (fun i : {i // p i} ↦ gridSite hl hL (halfGridBase l b) (X i.val))
  have hsub : nearLabels p s X⊆Finset.univ.biUnion A := by
    intro i hi
    obtain ⟨k,hki,hkd⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨b,hb⟩ := halfGrid_pair_cover hl hL (X k.val) (X i.val) (lt_of_le_of_lt hkd (by linarith))
    exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,(mem_activeLabels _ _).mpr ⟨k,hki,hb⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma dirichlet_near_energy_grid {n j : ℕ} [NeZero j] {L : Length} {a l s : ℝ}
    (hl : 0<l) (hL : L.val=(j:ℝ)*l) (hs : 4*s<l) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    (∫⁻ X, ((nearLabels p s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2)) ≤
      ENNReal.ofReal (8*Real.sqrt 3*l^3/a*selectedEnergy p u) := by
  calc
    _ ≤ ∫⁻ X, (∑ b : Fin 3 → Bool,(gridActiveCount hl hL (halfGridBase l b) p X:ℝ≥0∞))*ENNReal.ofReal (‖u.1 X‖^2) := by
      apply lintegral_mono
      intro X
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast nearLabels_card_le_grids hl hL hs p X
    _ = ∑ b : Fin 3 → Bool, ∫⁻ X,(gridActiveCount hl hL (halfGridBase l b) p X:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2) := by
      simp_rw [Finset.sum_mul]
      apply lintegral_finsetSum
      intro b _
      have h₁ : Measurable (fun X : Configuration n L ↦ (gridActiveCount hl hL (halfGridBase l b) p X:ℝ≥0∞)) :=
        (measurable_of_countable (fun k : ℕ ↦ (k:ℝ≥0∞))).comp (measurable_gridActiveCount hl hL (halfGridBase l b) p)
      have h₂ : Measurable (fun X : Configuration n L ↦ ENNReal.ofReal (‖u.1 X‖^2)) :=
        ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal
      exact h₁.mul h₂
    _ ≤ ∑ _b : Fin 3 → Bool, ENNReal.ofReal (Real.sqrt 3*l^3/a*selectedEnergy p u) :=
      Finset.sum_le_sum (fun b _ ↦ dirichlet_physical_grid_energy hl hL (halfGridBase l b) p ha u hu)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
      norm_num only [show 2^3=8 by norm_num]
      rw [show (8:ℝ≥0∞)=ENNReal.ofReal (8:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤8)]
      congr 1
      ring
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_NearGridScale
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma near_grid_scale {s L : ℝ} (hs : 0 < s) (hL : 10*s≤L) :
    ∃ j : ℕ, 0<j ∧ ∃ l : ℝ, 0<l ∧ L=(j:ℝ)*l ∧ 4*s<l ∧ l≤10*s := by
  let j := ⌊L/(5*s)⌋₊
  have h5 : 0<5*s := by positivity
  have hy : 2≤L/(5*s) := (le_div_iff₀ h5).mpr (by linarith)
  have hj : 0<j := Nat.floor_pos.mpr (by linarith)
  have hjr : 0<(j:ℝ) := by exact_mod_cast hj
  have hfloor := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤2) hy)
  have hfloor' := Nat.lt_floor_add_one (L/(5*s))
  change (j:ℝ)≤L/(5*s) at hfloor
  change L/(5*s)<(j:ℝ)+1 at hfloor'
  have hlow : 5*s≤L/(j:ℝ) := by
    rw [le_div_iff₀ hjr]
    have hh := (le_div_iff₀ h5).mp hfloor
    nlinarith
  have hupp : L/(j:ℝ)≤10*s := by
    rw [div_le_iff₀ hjr]
    have hh := (div_lt_iff₀ h5).mp hfloor'
    have hj1 : 1≤(j:ℝ) := by exact_mod_cast hj
    nlinarith
  refine ⟨j,hj,L/(j:ℝ),lt_of_lt_of_le (by positivity) hlow,?_,by linarith,hupp⟩
  field_simp

lemma dirichlet_near_energy {n : ℕ} {L : Length} {a s : ℝ}
    (hs : 0 < s) (hL : 10*s≤L.val) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    ENNReal.ofReal (27/(262144*Real.sqrt 3)*a/s^3)*
      (∫⁻ X, ((nearLabels p s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2)) ≤
        ENNReal.ofReal (selectedEnergy p u) := by
  obtain ⟨j,hj,l,hl,hLj,hsl,hls⟩ := near_grid_scale hs hL
  let : NeZero j := ⟨Nat.ne_of_gt hj⟩
  have h := dirichlet_near_energy_grid hl hLj hsl p ha u hu
  have he := selectedEnergy_nonneg p u
  have hc : 0≤27/(262144*Real.sqrt 3)*a/s^3 := by positivity
  have hs3 : 0 < s^3 := by positivity
  have hratio : l^3/s^3≤1000 := by
    apply (div_le_iff₀ hs3).mpr
    have hh := pow_le_pow_left₀ hl.le hls 3
    nlinarith
  have hf : (27/(262144*Real.sqrt 3)*a/s^3)*(8*Real.sqrt 3*l^3/a)≤1 := by
    calc
      _ = (216/262144:ℝ)*(l^3/s^3) := by
        field_simp [ne_of_gt ha,ne_of_gt hs,ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3))]
        ring
      _ ≤ (216/262144:ℝ)*1000 := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ ≤ 1 := by norm_num
  calc
    _ ≤ ENNReal.ofReal (27/(262144*Real.sqrt 3)*a/s^3) * ENNReal.ofReal (8*Real.sqrt 3*l^3/a*selectedEnergy p u) := mul_le_mul_of_nonneg_left h zero_le
    _ = ENNReal.ofReal ((27/(262144*Real.sqrt 3)*a/s^3)*(8*Real.sqrt 3*l^3/a)*selectedEnergy p u) := by
      rw [←ENNReal.ofReal_mul hc]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (1*selectedEnergy p u) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hf he)
    _ = _ := by rw [one_mul]
end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalizedNearLabels
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal

lemma spatialSiteDistance_triangle (L : Length) (A : Finset (Torus L)) (x y : Torus L) :
    spatialSiteDistance L A x≤ spatialSiteDistance L A y+torusDistance L x y := by
  simpa only [spatialSiteDistance,euclideanTorusPoint_dist] using
    (Metric.infDist_le_infDist_add_dist (x:=euclideanTorusPoint L x) (y:=euclideanTorusPoint L y)
      (s:=euclideanTorusPoint L '' (A:Set (Torus L))))

lemma spatialOutside_zero (L : Length) (A : Finset (Torus L)) (H : ℝ) (x : Torus L)
    (hx : spatialSiteDistance L A x≤H) : (spatialOutside L A H).orbital x=0 := by
  have hm := (abs_le.mp (smoothSpatialDistance_approximation L A x)).2
  have h : smoothSpatialDistance L A x-H≤1 := by linarith
  change (Real.cos (Real.pi/2*CellOrbital.profile 1 (smoothSpatialDistance L A x-H)):ℂ)=0
  rw [CellOrbital.profile_one (by norm_num : (0:ℝ)<1) h,mul_one,Real.cos_pi_div_two,Complex.ofReal_zero]

lemma productPartition_norm_unity {n : ℕ} {L : Length} (a c : SmoothMultiplier 1 L)
    (ha : ∀ X, conj (a.toFun X)=a.toFun X) (hc : ∀ X, conj (c.toFun X)=c.toFun X)
    (hp : ∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1)
    (X : Configuration n L) : (∑ σ : Fin n → Bool, ‖(productPartition n L a c σ).toFun X‖^2)=1 := by
  simp_rw [real_norm_sq _ (productPartition_real a c ha hc _ X)]
  rw [← Complex.re_sum,productPartition_unity a c hp,Complex.one_re]

lemma spatialPartition_forces_inside {n : ℕ} (L : Length) (A : Finset (Torus L)) (H : ℝ)
    (σ : Fin n → Bool) (X : Configuration n L)
    (hn : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X≠0)
    (i : Fin n) (hi : spatialSiteDistance L A (X i)≤H) : σ i=true := by
  have hprod : ∏ j : Fin n, (cond (σ j) (spatialInside L A H) (spatialOutside L A H)).orbital (X j)≠0 := hn
  have hh := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  cases he : σ i
  · rw [he,Bool.cond_false,spatialOutside_zero L A H (X i) hi] at hh
    exact False.elim (hh rfl)
  · rfl

lemma localizedNearLabels_card_le_selected {n : ℕ} (L : Length) (A : Finset (Torus L))
    {H s : ℝ} (hH : 8≤H) (hs : 2*s≤1) (σ : Fin n → Bool) (X : Configuration n L)
    (hn : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X≠0) :
    (localizedNearLabels L A s X).card≤(nearLabels (fun i ↦ σ i=true) s X).card := by
  classical
  have hforce := spatialPartition_forces_inside L A H σ X hn
  have hi {i : Fin n} (hi : i∈localizedNearLabels L A s X) : σ i=true := by
    have hd := (Finset.mem_filter.mp hi).2.2.1
    exact hforce i (by linarith)
  let f : {i // i∈localizedNearLabels L A s X} → {i // i∈nearLabels (fun i ↦ σ i=true) s X} := fun i ↦
    ⟨⟨i.val,hi i.property⟩,by
      obtain ⟨_,hd,k,hki,hkd⟩ := (Finset.mem_filter.mp i.property).2
      have hd' := spatialSiteDistance_triangle L A (X k) (X i.val)
      have hk : σ k=true := hforce k (by linarith)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨k,hk⟩,fun he ↦ hki (congrArg Subtype.val he),hkd⟩⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x ↦ x.val.val) hij
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

lemma spatialPartition_near_weight {n : ℕ} (L : Length) (A : Finset (Torus L))
    {H s : ℝ} (hH : 8≤H) (hs : 2*s≤1) (X : Configuration n L) :
    ((localizedNearLabels L A s X).card:ℝ)≤
      ∑ σ : Fin n → Bool, ((nearLabels (fun i ↦ σ i=true) s X).card:ℝ)*
        ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2 := by
  have hp := productPartition_norm_unity (spatialInside L A H) (spatialOutside L A H)
    (spatialInside_real L A H) (spatialOutside_real L A H) (spatialPartition_unity L A H) X
  calc
    _ = ((localizedNearLabels L A s X).card:ℝ)*
        (∑ σ : Fin n → Bool, ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2) := by rw [hp,mul_one]
    _ = _ := Finset.mul_sum ..
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hn : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X=0
      · simp only [hn,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero,le_refl]
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast localizedNearLabels_card_le_selected L A hH hs σ X hn) (sq_nonneg _)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ENNReal

lemma measurable_close_predicate {n : ℕ} {L : Length} (s : ℝ) (i k : Fin n) :
    MeasurableSet {X : Configuration n L | torusDistance L (X k) (X i)≤2*s} := by
  have hc : Continuous (fun X : Configuration n L ↦ torusDistance L (X k) (X i)) :=
    by unfold torusDistance; fun_prop
  exact measurableSet_le hc.measurable measurable_const

lemma measurable_near_predicate {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p]
    (s : ℝ) (i : {i // p i}) :
    MeasurableSet {X : Configuration n L | ∃ k : {k // p k}, k≠i ∧ torusDistance L (X k.val) (X i.val)≤2*s} := by
  simp only [Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion (fun k ↦ (MeasurableSet.const _).inter (measurable_close_predicate s i.val k.val))

lemma nearLabels_card_measurable {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] (s : ℝ) :
    Measurable (fun X : Configuration n L ↦ (nearLabels p s X).card) := by
  classical
  have h (i : {i // p i}) : Measurable (fun X : Configuration n L ↦
      if ∃ k : {k // p k}, k≠i ∧ torusDistance L (X k.val) (X i.val)≤2*s then (1:ℕ) else 0) :=
    Measurable.ite (measurable_near_predicate p s i) measurable_const measurable_const
  have hh := Finset.measurable_sum (s:=Finset.univ) (fun i _ ↦ h i)
  simpa only [nearLabels,Finset.card_eq_sum_ones,Finset.sum_filter] using hh

lemma measurable_localized_near_predicate {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) (i : Fin n) :
    MeasurableSet {X : Configuration n L | A.Nonempty ∧ spatialSiteDistance L A (X i)≤6 ∧
      ∃ k : Fin n, k≠i ∧ torusDistance L (X k) (X i)≤2*s} := by
  simp only [Set.ofPred_exists,Set.ofPred_and]
  refine (MeasurableSet.const _).inter ((measurableSet_le
    ((spatialSiteDistance_lipschitz L A).continuous.comp (continuous_apply i)).measurable measurable_const).inter ?_)
  exact MeasurableSet.iUnion (fun k ↦ (MeasurableSet.const _).inter (measurable_close_predicate s i k))

lemma localizedNearLabels_card_measurable {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) :
    Measurable (fun X : Configuration n L ↦ (localizedNearLabels L A s X).card) := by
  classical
  have h (i : Fin n) : Measurable (fun X : Configuration n L ↦
      if A.Nonempty ∧ spatialSiteDistance L A (X i)≤6 ∧
        ∃ k : Fin n, k≠i ∧ torusDistance L (X k) (X i)≤2*s then (1:ℕ) else 0) :=
    Measurable.ite (measurable_localized_near_predicate L A s i) measurable_const measurable_const
  have hh := Finset.measurable_sum (s:=Finset.univ) (fun i _ ↦ h i)
  simpa only [localizedNearLabels,Finset.card_eq_sum_ones,Finset.sum_filter] using hh

lemma spatialPartition_near_integral {n : ℕ} (L : Length) (A : Finset (Torus L))
    {H r s : ℝ} (hH : 8≤H) (hs : 0 < s) (hs' : 2*s≤1) (hL : 10*s≤L.val) (hr : 0 < r)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ENNReal.ofReal (27/(262144*Real.sqrt 3)*r/s^3)*
      (∫⁻ X, ((localizedNearLabels L A s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2))≤
      ENNReal.ofReal (spatialPartitionEnergy L A H u) := by
  let w := fun σ : Fin n → Bool ↦ productPartition n L (spatialInside L A H) (spatialOutside L A H) σ
  have hcoe : ∀ᵐ X ∂volume, ∀ σ, (w σ).onScalar u.1 X=(w σ).toFun X*u.1 X :=
    ae_all_iff.mpr (fun σ ↦ (w σ).coe_onScalar u.1)
  have hm (σ : Fin n → Bool) : Measurable (fun X : Configuration n L ↦
      ((nearLabels (fun i ↦ σ i=true) s X).card:ℝ≥0∞)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2)) :=
    ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ≥0∞))).comp (nearLabels_card_measurable _ s)).mul
      ((Lp.stronglyMeasurable ((w σ).onScalar u.1)).measurable.norm.pow_const 2).ennreal_ofReal
  calc
    _ ≤ ENNReal.ofReal (27/(262144*Real.sqrt 3)*r/s^3)*
        (∫⁻ X, ∑ σ : Fin n → Bool, ((nearLabels (fun i ↦ σ i=true) s X).card:ℝ≥0∞)*
          ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply lintegral_mono_ae
      filter_upwards [hcoe] with X hX
      have h := ENNReal.ofReal_le_ofReal (spatialPartition_near_weight L A hH hs' X)
      rw [ENNReal.ofReal_natCast,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))] at h
      simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] at h
      simp_rw [hX,norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _),← mul_assoc,← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right h zero_le
    _ = ∑ σ : Fin n → Bool, ENNReal.ofReal (27/(262144*Real.sqrt 3)*r/s^3)*
        (∫⁻ X, ((nearLabels (fun i ↦ σ i=true) s X).card:ℝ≥0∞)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2)) := by
      rw [lintegral_finsetSum _ (fun σ _ ↦ hm σ),Finset.mul_sum]
    _ ≤ ∑ σ : Fin n → Bool, ENNReal.ofReal (selectedEnergy (fun i ↦ σ i=true) ((w σ).onJet u)) :=
      Finset.sum_le_sum (fun σ _ ↦ dirichlet_near_energy hs hL (fun i ↦ σ i=true) hr ((w σ).onJet u) ((w σ).onJet_mem_domain hu))
    _ = _ := by rw [spatialPartitionEnergy,ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ selectedEnergy_nonneg _ _)]

theorem spatial_near_average {n : ℕ} (L : Length) (A : Finset (Torus L))
    {r s : ℝ} (hs : 0 < s) (hs' : 2*s≤1) (hL : 10*s≤L.val) (hr : 0 < r)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ENNReal.ofReal (Real.exp (-8)*(27/(262144*Real.sqrt 3))*r/s^3)*
      (∫⁻ X, ((localizedNearLabels L A s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2))≤
      ∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw := by
  let Q := ∫⁻ X, ((localizedNearLabels L A s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2)
  let c := ENNReal.ofReal (27/(262144*Real.sqrt 3)*r/s^3)
  have htail : radiusLaw (Ici (8:ℝ))=ENNReal.ofReal (Real.exp (-8)) := by
    rw [←radiusLaw_tail_eq (by norm_num : (0:ℝ)≤8)]
    exact (ENNReal.ofReal_toReal (measure_ne_top radiusLaw _)).symm
  have hbound := lintegral_mono (μ:=radiusLaw) (f:=(Ici (8:ℝ)).indicator (fun _ ↦ c*Q))
    (g:=fun H ↦ ENNReal.ofReal (spatialPartitionEnergy L A H u)) (fun H ↦ by
      by_cases hH : H∈Ici (8:ℝ)
      · rw [indicator_of_mem hH]
        exact spatialPartition_near_integral L A hH hs hs' hL hr u hu
      · rw [indicator_of_notMem hH]; exact zero_le)
  rw [lintegral_indicator_const measurableSet_Ici,htail] at hbound
  apply le_trans _ hbound
  apply le_of_eq
  rw [show Real.exp (-8)*(27/(262144*Real.sqrt 3))*r/s^3=
    Real.exp (-8)*(27/(262144*Real.sqrt 3)*r/s^3) by ring,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  dsimp [c,Q]
  ac_rfl

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_UnitCenter
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma unitIndex_dist_center {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (x : AddCircle L.val) :
    dist x ((((unitIndex hL x).val:ℝ)+1/2:ℝ) : AddCircle L.val)≤1/2 := by
  let t := ((AddCircle.equivIco L.val 0) x).val
  have ht : 0≤t := ((AddCircle.equivIco L.val 0) x).property.1
  have hlo := Nat.floor_le ht
  have hhi := Nat.lt_floor_add_one t
  have hab : |t-((⌊t⌋₊:ℝ)+1/2)|≤1/2 := by rw [abs_le]; constructor <;> linarith
  change dist x (((⌊t⌋₊:ℝ)+1/2:ℝ) : AddCircle L.val)≤1/2
  have he : (t:AddCircle L.val)=x := AddCircle.coe_equivIco
  rw [←he,dist_eq_norm,←QuotientAddGroup.mk_sub]
  exact (QuotientAddGroup.norm_mk_le_norm).trans (by simpa only [Real.norm_eq_abs] using hab)

lemma unitSite_dist_center {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (x : Torus L) :
    torusDistance L x (unitCenter L (unitSite hL x))≤1 := by
  have hc (j : Fin 3) : dist (x j) (unitCenter L (unitSite hL x) j)≤1/2 := by
    fin_cases j
    · exact unitIndex_dist_center hL (x 0)
    · exact unitIndex_dist_center hL (x 1)
    · exact unitIndex_dist_center hL (x 2)
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num,?_⟩
  calc
    _ ≤ ∑ j : Fin 3, (1/2:ℝ)^2 := Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ dist_nonneg (hc j) 2)
    _ ≤ (1:ℝ)^2 := by norm_num

lemma unitOccupation_eq_full {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L)
    (hp : ∀ i, unitSite hL (X i)=v → p i) :
    unitOccupation hL p v X=unitOccupation hL (fun _ ↦ True) v X := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun i ↦ ⟨⟨i.val.val,trivial⟩,i.property⟩
    invFun := fun i ↦ ⟨⟨i.val.val,hp i.val.val i.property⟩,i.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

lemma spatialPartition_cell_occupation {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (H : ℝ) (σ : Fin n → Bool) (X : Configuration n L)
    (hn : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X≠0)
    (v : CubeCell K) (hv : spatialSiteDistance L A (unitCenter L v)+1≤H) :
    unitOccupation hL (fun i ↦ σ i=true) v X=unitOccupation hL (fun _ ↦ True) v X := by
  apply unitOccupation_eq_full
  intro i hi
  apply spatialPartition_forces_inside L A H σ X hn
  have hd := spatialSiteDistance_triangle L A (X i) (unitCenter L v)
  have hc := unitSite_dist_center hL (X i)
  rw [hi] at hc
  linarith only [hd,hc,hv]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_UnitPairCount
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma unitPairCount_nonneg {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) :
    0≤unitPairCount hL p v X := by
  unfold unitPairCount
  by_cases h : unitOccupation hL p v X=0
  · simp only [h,Nat.cast_zero,zero_mul,le_refl]
  · have hp : (1:ℝ)≤unitOccupation hL p v X := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hp)

lemma unitPairCount_measurable {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) : Measurable (unitPairCount hL p v) := by
  have hm : Measurable (fun X : Configuration n L ↦ fun i ↦ unitSite hL (X i)) :=
    Measurable.of_eval (fun i ↦ (measurable_unitSite hL).comp (measurable_pi_apply i))
  let W : (Fin n → CubeCell K) → ℝ := fun σ ↦
    (Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)*((Fintype.card {i : {i // p i} // σ i.val=v}:ℝ)-1)
  have hW : Measurable W := measurable_of_finite W
  change Measurable (W ∘ fun X : Configuration n L ↦ fun i ↦ unitSite hL (X i))
  exact hW.comp hm

lemma spatialPartition_cell_weight {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (H : ℝ) (X : Configuration n L) :
    (∑ v : CubeCell K, if spatialSiteDistance L A (unitCenter L v)+1≤H then
      unitPairCount hL (fun _ ↦ True) v X else 0)≤
    ∑ σ : Fin n → Bool, (∑ v : CubeCell K, unitPairCount hL (fun i ↦ σ i=true) v X)*
      ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2 := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : spatialSiteDistance L A (unitCenter L v)+1≤H
  · rw [ite_eq_left hv]
    apply le_of_eq
    have hp := productPartition_norm_unity (spatialInside L A H) (spatialOutside L A H)
      (spatialInside_real L A H) (spatialOutside_real L A H) (spatialPartition_unity L A H) X
    calc
      _ = unitPairCount hL (fun _ ↦ True) v X*
          (∑ σ : Fin n → Bool, ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2) := by rw [hp,mul_one]
      _ = ∑ σ : Fin n → Bool, unitPairCount hL (fun _ ↦ True) v X*
          ‖(productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X‖^2 := Finset.mul_sum ..
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ _
        by_cases hz : (productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).toFun X=0
        · simp only [hz,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]
        · unfold unitPairCount
          rw [spatialPartition_cell_occupation hL A H σ X hz v hv]
  · rw [ite_eq_right hv]
    exact Finset.sum_nonneg (fun σ _ ↦ mul_nonneg (unitPairCount_nonneg hL _ v X) (sq_nonneg _))

lemma spatialPartition_cell_integral {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (H : ℝ) {r : ℝ} (hr : 0 < r) (u : Jet n L)
    (hu : u∈dirichletDomain n L r) :
    (∑ v : CubeCell K, (Ici (spatialSiteDistance L A (unitCenter L v)+1)).indicator
      (fun _ : ℝ ↦ ENNReal.ofReal (1/(64*Real.sqrt 3)*r)*
        (∫⁻ X, ENNReal.ofReal (unitPairCount hL (fun _ ↦ True) v X)*ENNReal.ofReal (‖u.1 X‖^2))) H)≤
      ENNReal.ofReal (spatialPartitionEnergy L A H u) := by
  classical
  let w := fun σ : Fin n → Bool ↦ productPartition n L (spatialInside L A H) (spatialOutside L A H) σ
  let c : ℝ := 1/(64*Real.sqrt 3)*r
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let q := fun (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) ↦ unitPairCount hL p v X
  have hcoe : ∀ᵐ X ∂volume, ∀ σ, (w σ).onScalar u.1 X=(w σ).toFun X*u.1 X :=
    ae_all_iff.mpr (fun σ ↦ (w σ).coe_onScalar u.1)
  have hm (σ : Fin n → Bool) : Measurable (fun X : Configuration n L ↦
      ENNReal.ofReal (c*∑ v : CubeCell K, q (fun i ↦ σ i=true) v X)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2)) :=
    ((Finset.measurable_sum _ (fun v _ ↦ unitPairCount_measurable hL _ v)).const_mul c).ennreal_ofReal.mul
      ((Lp.stronglyMeasurable ((w σ).onScalar u.1)).measurable.norm.pow_const 2).ennreal_ofReal
  have hn (σ : Fin n → Bool) (X : Configuration n L) : 0≤∑ v : CubeCell K, q (fun i ↦ σ i=true) v X :=
    Finset.sum_nonneg (fun v _ ↦ unitPairCount_nonneg hL _ v X)
  have havg : (∫⁻ X, ENNReal.ofReal (c*(∑ v : CubeCell K, if spatialSiteDistance L A (unitCenter L v)+1≤H then q (fun _ ↦ True) v X else 0))*ENNReal.ofReal (‖u.1 X‖^2))≤
      ENNReal.ofReal (spatialPartitionEnergy L A H u) := by
    calc
      _ ≤ ∫⁻ X, ∑ σ : Fin n → Bool, ENNReal.ofReal (c*∑ v : CubeCell K, q (fun i ↦ σ i=true) v X)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2) := by
        apply lintegral_mono_ae
        filter_upwards [hcoe] with X hX
        have hh := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (spatialPartition_cell_weight hL A H X) hc)
        conv_rhs at hh => rw [Finset.mul_sum]
        have hp (σ : Fin n → Bool) : 0 ≤ c*((∑ v : CubeCell K, q (fun i ↦ σ i=true) v X)*‖(w σ).toFun X‖^2) :=
          mul_nonneg hc (mul_nonneg (hn σ X) (sq_nonneg _))
        rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ hp σ)] at hh
        simp_rw [←mul_assoc,ENNReal.ofReal_mul (mul_nonneg hc (hn _ X))] at hh
        simp_rw [hX,norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg _),←mul_assoc,←Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hh zero_le
      _ = ∑ σ : Fin n → Bool, ∫⁻ X, ENNReal.ofReal (c*∑ v : CubeCell K, q (fun i ↦ σ i=true) v X)*ENNReal.ofReal (‖(w σ).onScalar u.1 X‖^2) := by
        rw [lintegral_finsetSum _ (fun σ _ ↦ hm σ)]
      _ ≤ ∑ σ : Fin n → Bool, ENNReal.ofReal (selectedEnergy (fun i ↦ σ i=true) ((w σ).onJet u)) := by
        apply Finset.sum_le_sum
        intro σ _
        have hh := dirichlet_physical_cell_energy hL (fun i ↦ σ i=true) hr ((w σ).onJet u) ((w σ).onJet_mem_domain hu)
        refine (le_of_eq ?_).trans hh
        apply lintegral_congr
        intro X
        congr 2
        dsimp [c,q,unitPairCount]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [spatialPartitionEnergy,ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ selectedEnergy_nonneg _ _)]
  apply le_trans _ havg
  apply le_of_eq
  have hp (X : Configuration n L) :
      ENNReal.ofReal (c*(∑ v : CubeCell K, if spatialSiteDistance L A (unitCenter L v)+1≤H then q (fun _ ↦ True) v X else 0))*ENNReal.ofReal (‖u.1 X‖^2)=
      ∑ v : CubeCell K, ENNReal.ofReal (c*(if spatialSiteDistance L A (unitCenter L v)+1≤H then q (fun _ ↦ True) v X else 0))*ENNReal.ofReal (‖u.1 X‖^2) := by
    have hpv (v : CubeCell K) : 0 ≤ c*(if spatialSiteDistance L A (unitCenter L v)+1≤H then q (fun _ ↦ True) v X else 0) := by
      apply mul_nonneg hc
      split_ifs
      · exact unitPairCount_nonneg hL _ v X
      · exact le_refl _
    rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg (fun v _ ↦ hpv v),Finset.sum_mul]
  simp_rw [hp]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro v _
    by_cases hv : spatialSiteDistance L A (unitCenter L v)+1≤H
    · rw [indicator_of_mem (show H∈Ici (spatialSiteDistance L A (unitCenter L v)+1) from hv)]
      simp only [ite_eq_left hv,ENNReal.ofReal_mul hc,mul_assoc]
      rw [lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
    · rw [indicator_of_notMem (show H∉Ici (spatialSiteDistance L A (unitCenter L v)+1) from hv)]
      simp only [ite_eq_right hv,mul_zero,ENNReal.ofReal_zero,zero_mul,lintegral_zero]
  · intro v _
    by_cases hv : spatialSiteDistance L A (unitCenter L v)+1≤H
    · simp only [ite_eq_left hv]
      exact (((unitPairCount_measurable hL _ v).const_mul c).ennreal_ofReal.mul
        ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal)
    · simp only [ite_eq_right hv,mul_zero,ENNReal.ofReal_zero,zero_mul]
      exact measurable_const

theorem spatial_cell_average {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) {r : ℝ} (hr : 0 < r) (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    (∑ v : CubeCell K, ENNReal.ofReal (Real.exp (-(spatialSiteDistance L A (unitCenter L v)+1)))*
      (ENNReal.ofReal (1/(64*Real.sqrt 3)*r)*
        (∫⁻ X, ENNReal.ofReal (unitPairCount hL (fun _ ↦ True) v X)*ENNReal.ofReal (‖u.1 X‖^2))))≤
      ∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw := by
  have hb := lintegral_mono (μ:=radiusLaw) (fun H ↦ spatialPartition_cell_integral hL A H hr u hu)
  rw [lintegral_finsetSum] at hb
  · apply le_trans _ hb
    apply Finset.sum_le_sum
    intro v _
    rw [lintegral_indicator_const measurableSet_Ici]
    have hd : 0≤ spatialSiteDistance L A (unitCenter L v)+1 := by
      have := spatialSiteDistance_nonneg L A (unitCenter L v)
      linarith
    have ht : radiusLaw (Ici (spatialSiteDistance L A (unitCenter L v)+1))=
        ENNReal.ofReal (Real.exp (-(spatialSiteDistance L A (unitCenter L v)+1))) := by
      rw [←radiusLaw_tail_eq hd]
      exact (ENNReal.ofReal_toReal (measure_ne_top radiusLaw _)).symm
    rw [ht,mul_comm]
  · intro v _
    exact measurable_const.indicator measurableSet_Ici

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_WeightedUnitPairCount
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma unitOccupation_le {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) :
    unitOccupation hL p v X≤n := by
  exact (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans (by simp))

lemma unitPairCount_le {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) :
    unitPairCount hL p v X≤(n:ℝ)^2 := by
  have hn : 0≤(unitOccupation hL p v X:ℝ) := Nat.cast_nonneg _
  have hb : (unitOccupation hL p v X:ℝ)≤n := by exact_mod_cast unitOccupation_le hL p v X
  unfold unitPairCount
  nlinarith only [hn, mul_self_le_mul_self hn hb]

lemma unitPairCount_integrable {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (u : ScalarL2 n L) :
    Integrable (fun X ↦ unitPairCount hL p v X*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u (unitPairCount_measurable hL p v)
    (fun X ↦ by rw [abs_of_nonneg (unitPairCount_nonneg hL p v X)]; exact unitPairCount_le hL p v X)

lemma localizedNearLabels_integrable {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) (u : ScalarL2 n L) :
    Integrable (fun X ↦ ((localizedNearLabels L A s X).card:ℝ)*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ))).comp (localizedNearLabels_card_measurable L A s))
    (B:=(n:ℝ)) (fun X ↦ by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast (show (localizedNearLabels L A s X).card≤n by simpa using (localizedNearLabels L A s X).card_le_univ))

lemma weightedUnitPairCount_integral {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (u : ScalarL2 n L) :
    (∫ X, weightedUnitPairCount hL A X*‖u X‖^2)=
      ∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u X‖^2) := by
  simp only [weightedUnitPairCount,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro v _
    exact (unitPairCount_integrable hL _ v u).const_mul _

lemma weightedUnitPairCount_integrable {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (u : ScalarL2 n L) :
    Integrable (fun X ↦ weightedUnitPairCount hL A X*‖u X‖^2) volume := by
  simp only [weightedUnitPairCount,Finset.sum_mul,mul_assoc]
  exact integrable_finsetSum _ (fun v _ ↦ (unitPairCount_integrable hL _ v u).const_mul _)

lemma spatial_cell_average_real {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) {r : ℝ} (hr : 0 < r) (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ENNReal.ofReal (Real.exp (-1)/(64*Real.sqrt 3)*r*(∫ X, weightedUnitPairCount hL A X*‖u.1 X‖^2))≤
      ∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw := by
  apply le_trans _ (spatial_cell_average hL A hr u hu)
  apply le_of_eq
  have hi (v : CubeCell K) : ENNReal.ofReal (∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u.1 X‖^2)=
      ∫⁻ X, ENNReal.ofReal (unitPairCount hL (fun _ ↦ True) v X)*ENNReal.ofReal (‖u.1 X‖^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (unitPairCount_integrable hL _ v u.1)
      (Eventually.of_forall (fun X ↦ mul_nonneg (unitPairCount_nonneg hL _ v X) (sq_nonneg _)))]
    simp only [ENNReal.ofReal_mul (unitPairCount_nonneg hL _ v _)]
  have hn (v : CubeCell K) : 0≤∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u.1 X‖^2 :=
    integral_nonneg (fun X ↦ mul_nonneg (unitPairCount_nonneg hL _ v X) (sq_nonneg _))
  rw [weightedUnitPairCount_integral,Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro v _
    have he : Real.exp (-1)/(64*Real.sqrt 3)*r*(Real.exp (-spatialSiteDistance L A (unitCenter L v))*(∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u.1 X‖^2))=
        Real.exp (-(spatialSiteDistance L A (unitCenter L v)+1))*(1/(64*Real.sqrt 3)*r)*(∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u.1 X‖^2) := by
      rw [neg_add,Real.exp_add]
      ring
    rw [he,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (Real.exp_pos _).le,hi]
    exact mul_assoc _ _ _
  · intro v _
    exact mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (hn v))

lemma spatial_near_average_real {n : ℕ} (L : Length) (A : Finset (Torus L))
    {r s : ℝ} (hs : 0 < s) (hs' : 2*s≤1) (hL : 10*s≤L.val) (hr : 0 < r)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ENNReal.ofReal (Real.exp (-8)*(27/(262144*Real.sqrt 3))*r/s^3*
      (∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2))≤
      ∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw := by
  have hi : ENNReal.ofReal (∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2)=
      ∫⁻ X, ((localizedNearLabels L A s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (localizedNearLabels_integrable L A s u.1)
      (Eventually.of_forall (fun X ↦ mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))]
    simp only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_mul (by positivity),hi]
  exact spatial_near_average L A hs hs' hL hr u hu

theorem spatial_before_square : ∃ C D : ℝ, 0<C ∧ 0<D ∧
    ∀ (n K : ℕ) (L : Length) (hL : L.val=(K:ℝ)) (r s : ℝ),
      0 < r → 0 < s → 2*s≤1 → 10*s≤L.val → (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), A.Nonempty → ∀ (u : Jet n L), u∈dirichletDomain n L r →
      Real.exp (-1)/(128*Real.sqrt 3)*r*(∫ X, weightedUnitPairCount hL A X*‖u.1 X‖^2)+
        Real.exp (-8)*(27/(524288*Real.sqrt 3))*r/s^3*(∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2)-
        (C*(n:ℝ)*r/L.val^3+D)*(∫ X, weightedSiteCount L A X*‖u.1 X‖^2)≤energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,D,hC,hD,hsp⟩ := spatial_spectral_average
  refine ⟨C,D,hC,hD,?_⟩
  intro n K L hL r s hr hs hs' hsL hsmall g hg A hA u hu
  have hF : 0≤∫ X, weightedSiteCount L A X*‖u.1 X‖^2 :=
    integral_nonneg (fun X ↦ mul_nonneg (weightedSiteCount_nonneg L A X) (sq_nonneg _))
  have hLpos : 0<L.val := L.property
  have hB : 0≤energy u-energy g*‖u.1‖^2+(C*(n:ℝ)*r/L.val^3+D)*(∫ X, weightedSiteCount L A X*‖u.1 X‖^2) :=
    add_nonneg (sub_nonneg.mpr (hg.rayleigh_all u hu)) (mul_nonneg (by positivity) hF)
  have hc := (ENNReal.ofReal_le_ofReal_iff hB).mp ((spatial_cell_average_real hL A hr u hu).trans
    (hsp n L r hr hsmall g hg A hA u hu))
  have hk := (ENNReal.ofReal_le_ofReal_iff hB).mp ((spatial_near_average_real L A hs hs' hsL hr u hu).trans
    (hsp n L r hr hsmall g hg A hA u hu))
  have he : Real.exp (-1)/(128*Real.sqrt 3)*r=Real.exp (-1)/(64*Real.sqrt 3)*r/2 := by ring
  have he' : Real.exp (-8)*(27/(524288*Real.sqrt 3))*r/s^3=Real.exp (-8)*(27/(262144*Real.sqrt 3))*r/s^3/2 := by ring
  rw [he,he']
  linarith only [hc,hk]

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_LatticeExponentialSum
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal
noncomputable section

lemma latticeExponential_summable : Summable (fun z : ℤ ↦ Real.exp (-|(z:ℝ)|/3)) := by
  have h : Summable (fun n : ℕ ↦ Real.exp (-(n:ℝ)/3)) := by
    have hg := summable_geometric_of_abs_lt_one (r:=Real.exp (-1/3)) (by
      rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; norm_num)
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  apply Summable.of_nat_of_neg
  · simpa using h
  · simpa using h

lemma latticeExponentialSum_pos : 0<latticeExponentialSum := by
  have h := latticeExponential_summable.le_tsum 0 (fun _ _ ↦ (Real.exp_pos _).le)
  simp only [Int.cast_zero,abs_zero,neg_zero,zero_div,Real.exp_zero] at h
  exact lt_of_lt_of_le zero_lt_one h

lemma periodicLatticeIndex_injective {K : ℕ} {L : Length} (x : AddCircle L.val) :
    Function.Injective (periodicLatticeIndex (K:=K) L x) := by
  intro v w hvw
  have h := congrArg (fun z : ℤ ↦ (z+⌊((AddCircle.equivIco L.val 0) x).val-1/2⌋)%(K:ℤ)) hvw
  simp only [periodicLatticeIndex,sub_add_cancel,Int.sub_mul_emod_self_right] at h
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast v.isLt),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast w.isLt)] at h
  exact Fin.ext (by exact_mod_cast h)

lemma periodicLatticeIndex_bound {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (x : AddCircle L.val) (v : Fin K) :
    |(periodicLatticeIndex L x v:ℝ)|≤dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x+1 := by
  let t := ((AddCircle.equivIco L.val 0) x).val
  let δ := t-1/2-(⌊t-1/2⌋:ℝ)
  have hδ0 : 0≤δ := Int.fract_nonneg (t-1/2)
  have hδ1 : δ<1 := Int.fract_lt_one (t-1/2)
  have hδ : |δ|≤1 := by rw [abs_of_nonneg hδ0]; exact hδ1.le
  have hd : dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x=
      |(periodicLatticeIndex L x v:ℝ)-δ| := by
    conv_lhs => rw [←(show (t:AddCircle L.val)=x from AddCircle.coe_equivIco)]
    rw [dist_eq_norm,←QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    congr 1
    dsimp [periodicLatticeIndex,δ,t]
    push_cast
    rw [←hL]
    simp only [Int.fract]
    ring
  rw [hd]
  calc
    _ = |((periodicLatticeIndex L x v:ℝ)-δ)+δ| := by congr 1; ring
    _ ≤ |(periodicLatticeIndex L x v:ℝ)-δ|+|δ| := abs_add_le _ _
    _ ≤ _ := add_le_add le_rfl hδ

lemma circle_lattice_exponential_bound {K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (x : AddCircle L.val) :
    (∑ v : Fin K, Real.exp (-dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) x/3))≤
      Real.exp (1/3)*latticeExponentialSum := by
  classical
  calc
    _ ≤ ∑ v : Fin K, Real.exp (1/3)*Real.exp (-|(periodicLatticeIndex L x v:ℝ)|/3) := by
      apply Finset.sum_le_sum
      intro v _
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := periodicLatticeIndex_bound hL x v
      linarith only [h]
    _ = Real.exp (1/3)*∑ v : Fin K, Real.exp (-|(periodicLatticeIndex L x v:ℝ)|/3) := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [←Finset.sum_image (f:=fun z : ℤ ↦ Real.exp (-|(z:ℝ)|/3)) (s:=Finset.univ) (periodicLatticeIndex_injective x).injOn]
      exact latticeExponential_summable.sum_le_tsum _ (fun _ _ ↦ (Real.exp_pos _).le)

lemma torus_exp_le_coordinate_exp (L : Length) (x y : Torus L) :
    Real.exp (-torusDistance L x y)≤Real.exp (-dist (x 0) (y 0)/3)*
      Real.exp (-dist (x 1) (y 1)/3)*Real.exp (-dist (x 2) (y 2)/3) := by
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h0 := coordinate_distance_le L x y 0
  have h1 := coordinate_distance_le L x y 1
  have h2 := coordinate_distance_le L x y 2
  linarith only [h0,h1,h2]

theorem unitGrid_exponential_bound : ∃ C : ℝ, 0<C ∧
    ∀ (K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ x : Torus L,
      (∑ v : CubeCell K, Real.exp (-torusDistance L (unitCenter L v) x))≤C := by
  let B := Real.exp (1/3)*latticeExponentialSum
  have hB : 0<B := mul_pos (Real.exp_pos _) latticeExponentialSum_pos
  refine ⟨B^3,pow_pos hB _,?_⟩
  intro K L hL x
  let f := fun (j : Fin 3) (v : Fin K) ↦ Real.exp (-dist (((v.val:ℝ)+1/2:ℝ):AddCircle L.val) (x j)/3)
  have hb (j : Fin 3) : (∑ v, f j v)≤B := circle_lattice_exponential_bound hL (x j)
  have hn (j : Fin 3) : 0≤∑ v, f j v := Finset.sum_nonneg (fun _ _ ↦ (Real.exp_pos _).le)
  calc
    _ ≤ ∑ v : CubeCell K, f 0 v.1*f 1 v.2.1*f 2 v.2.2 := by
      apply Finset.sum_le_sum
      intro v _
      exact torus_exp_le_coordinate_exp L (unitCenter L v) x
    _ = (∑ v, f 0 v)*(∑ v, f 1 v)*(∑ v, f 2 v) := by
      simp_rw [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul]
      rw [←Fintype.sum_mul_sum]
    _ ≤ B*B*B := mul_le_mul (mul_le_mul (hb 0) (hb 1) (hn 1) hB.le) (hb 2) (hn 2) (mul_nonneg hB.le hB.le)
    _ = B^3 := by ring

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal
noncomputable section

lemma unitGrid_site_exponential_bound : ∃ C : ℝ, 0<C ∧
    ∀ (K : ℕ) (L : Length), L.val=(K:ℝ) → ∀ (A : Finset (Torus L)), A.Nonempty →
      (∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v)))≤C*(A.card:ℝ) := by
  obtain ⟨C,hC,h⟩ := unitGrid_exponential_bound
  refine ⟨C,hC,?_⟩
  intro K L hL A hA
  calc
    _ ≤ ∑ v : CubeCell K, ∑ w∈A, Real.exp (-torusDistance L (unitCenter L v) w) := by
      apply Finset.sum_le_sum
      intro v _
      obtain ⟨w,hw,he⟩ := spatialSiteDistance_attained L A hA (unitCenter L v)
      rw [he]
      exact Finset.single_le_sum (f:=fun w ↦ Real.exp (-torusDistance L (unitCenter L v) w)) (fun _ _ ↦ (Real.exp_pos _).le) hw
    _ = ∑ w∈A, ∑ v : CubeCell K, Real.exp (-torusDistance L (unitCenter L v) w) := Finset.sum_comm
    _ ≤ ∑ _w∈A, C := Finset.sum_le_sum (fun w _ ↦ h K L hL w)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul,mul_comm]

lemma unitOccupation_full_card {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (v : CubeCell K) (X : Configuration n L) :
    unitOccupation hL (fun _ ↦ True) v X=Fintype.card {i : Fin n // unitSite hL (X i)=v} := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun i ↦ ⟨i.val.val,i.property⟩
    invFun := fun i ↦ ⟨⟨i.val,trivial⟩,i.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

lemma unitOccupation_sum_weight {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (a : CubeCell K → ℝ) (X : Configuration n L) :
    (∑ v : CubeCell K, a v*(unitOccupation hL (fun _ ↦ True) v X:ℝ))=
      ∑ i : Fin n, a (unitSite hL (X i)) := by
  classical
  rw [←Fintype.sum_fiberwise (fun i : Fin n ↦ unitSite hL (X i)) (fun i ↦ a (unitSite hL (X i)))]
  apply Finset.sum_congr rfl
  intro v _
  simp only [unitOccupation_full_card]
  have he : (fun i : {i : Fin n // unitSite hL (X i)=v} ↦ a (unitSite hL (X i.val)))=fun _ ↦ a v := by
    funext i
    rw [i.property]
  rw [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

lemma weightedSiteCount_le_cell {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (hA : A.Nonempty) (X : Configuration n L) :
    weightedSiteCount L A X≤Real.exp 1*(∑ v : CubeCell K,
      Real.exp (-spatialSiteDistance L A (unitCenter L v))*(unitOccupation hL (fun _ ↦ True) v X:ℝ)) := by
  rw [unitOccupation_sum_weight,Finset.mul_sum,weightedSiteCount,ite_eq_left hA]
  apply Finset.sum_le_sum
  intro i _
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd := spatialSiteDistance_triangle L A (unitCenter L (unitSite hL (X i))) (X i)
  have hc := unitSite_dist_center hL (X i)
  rw [torusDistance_comm] at hd
  linarith only [hd,hc]

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SpatialScalarSquare
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma spatial_scalar_square {c M D m : ℝ} (hc : 0< c) (hD : 1≤ D) (hm : 0≤ m) :
    M*m ≤ c/D*(m*(m-1))+(c+M)^2/(4*c)*D := by
  have hDpos : 0< D := zero_lt_one.trans_le hD
  have hd : c/D≤ c := (div_le_iff₀ hDpos).mpr (by nlinarith only [hc.le,hD])
  have he : c/D*(m-(c+M)*D/(2*c))^2=
      c/D*m^2-(c+M)*m+(c+M)^2/(4*c)*D := by
    field_simp
    ring
  have hp := mul_nonneg (div_nonneg hc.le hDpos.le) (sq_nonneg (m-(c+M)*D/(2*c)))
  rw [he] at hp
  have hh := mul_le_mul_of_nonneg_right hd hm
  nlinarith only [hp,hh]

lemma weightedSiteCount_integrable {n : ℕ} (L : Length) (A : Finset (Torus L)) (u : ScalarL2 n L) :
    Integrable (fun X ↦ weightedSiteCount L A X*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u (weightedSiteCount_continuous L A).measurable
    (fun X ↦ by rw [abs_of_nonneg (weightedSiteCount_nonneg L A X)]; exact weightedSiteCount_le L A X)

theorem weighted_count_coercivity (c M : ℝ) (hc : 0< c) (hM : 0< M) : ∃ B : ℝ, 0< B ∧
    ∀ (n K : ℕ) (L : Length) (hL : L.val=(K:ℝ)) (A : Finset (Torus L)), A.Nonempty →
    ∀ (D : ℝ), 1≤ D → ∀ (X : Configuration n L),
      M*weightedSiteCount L A X≤ c/D*weightedUnitPairCount hL A X+B*D*(A.card:ℝ) := by
  obtain ⟨Q,hQ,hgrid⟩ := unitGrid_site_exponential_bound
  let e := Real.exp 1
  let V := (c+M*e)^2/(4*c)
  have he : 0< e := Real.exp_pos _
  have hV : 0< V := by dsimp [V]; positivity
  refine ⟨V*Q,mul_pos hV hQ,?_⟩
  intro n K L hL A hA D hD X
  have hp (v : CubeCell K) : 0≤ Real.exp (-spatialSiteDistance L A (unitCenter L v)) := (Real.exp_pos _).le
  have hs := Finset.sum_le_sum (s:=(Finset.univ : Finset (CubeCell K))) (fun v _ ↦
    mul_le_mul_of_nonneg_left (spatial_scalar_square (M:=M*e) hc hD (Nat.cast_nonneg (unitOccupation hL (fun _ ↦ True) v X))) (hp v))
  change (∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(M*e*(unitOccupation hL (fun _ ↦ True) v X:ℝ)))≤
    ∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(c/D*unitPairCount hL (fun _ ↦ True) v X+V*D) at hs
  have hf := mul_le_mul_of_nonneg_left (weightedSiteCount_le_cell hL A hA X) hM.le
  have hg := mul_le_mul_of_nonneg_left (hgrid K L hL A hA) (mul_nonneg hV.le (zero_le_one.trans hD))
  calc
    _ ≤ M*(e*(∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(unitOccupation hL (fun _ ↦ True) v X:ℝ))) := hf
    _ = ∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(M*e*(unitOccupation hL (fun _ ↦ True) v X:ℝ)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ _ := hs
    _ = c/D*weightedUnitPairCount hL A X+V*D*(∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))) := by
      simp only [weightedUnitPairCount,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro v _ <;> ring
    _ ≤ c/D*weightedUnitPairCount hL A X+(V*Q)*D*(A.card:ℝ) := by
      have heq : V*D*(Q*(A.card:ℝ))=(V*Q)*D*(A.card:ℝ) := by ring
      rw [←heq]
      exact add_le_add le_rfl hg

lemma weighted_count_coercivity_integral (c M : ℝ) (hc : 0< c) (hM : 0< M) : ∃ B : ℝ, 0< B ∧
    ∀ (n K : ℕ) (L : Length) (hL : L.val=(K:ℝ)) (A : Finset (Torus L)), A.Nonempty →
    ∀ (D : ℝ), 1≤ D → ∀ (u : ScalarL2 n L),
      M*(∫ X, weightedSiteCount L A X*‖u X‖^2)≤
        c/D*(∫ X, weightedUnitPairCount hL A X*‖u X‖^2)+B*D*(A.card:ℝ)*‖u‖^2 := by
  obtain ⟨B,hB,hbound⟩ := weighted_count_coercivity c M hc hM
  refine ⟨B,hB,?_⟩
  intro n K L hL A hA D hD u
  have hf := weightedSiteCount_integrable L A u
  have hq := weightedUnitPairCount_integrable hL A u
  have hn : Integrable (fun X ↦ ‖u X‖^2) volume := (Lp.memLp u).integrable_norm_pow (by norm_num)
  have hh := integral_mono ((hf.const_mul M)) ((hq.const_mul (c/D)).add (hn.const_mul (B*D*(A.card:ℝ))))
    (fun X ↦ by have hp := mul_le_mul_of_nonneg_right (hbound n K L hL A hA D hD X) (sq_nonneg ‖u X‖); simpa only [Pi.add_apply,add_mul,mul_assoc] using hp)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hq.const_mul (c/D)) (hn.const_mul _)] at hh
  simp only [integral_const_mul,←IndicatorStrong.norm_sq_integral] at hh
  exact hh

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_SpatialCloseScale
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

theorem weighted_local_penalty : ∃ C c : ℝ, 0< C ∧ 0< c ∧
    ∀ (n K : ℕ) (L : Length) ( _hL : L.val=(K:ℝ)) (r s D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤ D → 1≤ D*r → 0< r → 0< s → 2*s≤1 → 10*s≤ L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤ L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), A.Nonempty → ∀ (u : Jet n L), u∈dirichletDomain n L r →
      (D*r)*((∫ X, weightedSiteCount L A X*‖u.1 X‖^2)-C*D*(A.card:ℝ)*‖u.1‖^2)+
        c*r/s^3*(∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2)≤ energy u-energy g*‖u.1‖^2 := by
  obtain ⟨P,R,hP,hR,hbefore⟩ := spatial_before_square
  let a : ℝ := Real.exp (-1)/(128*Real.sqrt 3)
  let c : ℝ := Real.exp (-8)*(27/(524288*Real.sqrt 3))
  have ha : 0< a := by dsimp [a]; positivity
  have hc : 0< c := by dsimp [c]; positivity
  have hM : 0< P+R+1 := by linarith only [hP,hR]
  obtain ⟨B,hB,hcount⟩ := weighted_count_coercivity_integral a (P+R+1) ha hM
  refine ⟨B,c,hB,hc,?_⟩
  intro n K L hL r s D hDeq hD hα hr hs hs' hsL hsmall g hg A hA u hu
  let α := D*r
  let F := ∫ X, weightedSiteCount L A X*‖u.1 X‖^2
  let Q := ∫ X, weightedUnitPairCount hL A X*‖u.1 X‖^2
  let T := ∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2
  let Z := B*D*(A.card:ℝ)*‖u.1‖^2
  have hF : 0≤ F := integral_nonneg (fun X ↦ mul_nonneg (weightedSiteCount_nonneg L A X) (sq_nonneg _))
  have hαpos : 0<α := zero_lt_one.trans_le hα
  have hDpos : 0< D := zero_lt_one.trans_le hD
  have hmul : α*(a/D)=a*r := by dsimp [α]; field_simp
  have hdensity : P*(n:ℝ)*r/L.val^3=P*α := by dsimp [α]; rw [hDeq]; ring
  have hb := hbefore n K L hL r s hr hs hs' hsL hsmall g hg A hA u hu
  rw [hdensity] at hb
  change a*r*Q+c*r/s^3*T-(P*α+R)*F≤ energy u-energy g*‖u.1‖^2 at hb
  have hq := mul_le_mul_of_nonneg_left (hcount n K L hL A hA D hD u.1) hαpos.le
  change α*((P+R+1)*F)≤α*(a/D*Q+Z) at hq
  rw [mul_add,←mul_assoc α (a/D),hmul] at hq
  have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα hR.le) hF
  dsimp [α,Z] at hq hb he ⊢
  nlinarith only [hq,hb,he]

lemma spatialCloseScale_pos {D b : ℝ} (hD : 0< D) (hb : 0< b) : 0< spatialCloseScale D b :=
  mul_pos hb (Real.rpow_pos_of_pos hD _)

lemma spatialCloseScale_cube {D b : ℝ} (hD : 0< D) : D*(spatialCloseScale D b)^3=b^3 := by
  unfold spatialCloseScale
  rw [mul_pow,←Real.rpow_mul_natCast hD.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

theorem spatial_localized_form_oai : ∃ C c : ℝ, 0< C ∧ 0< c ∧
    ∀ (n K : ℕ) (L : Length) ( _hL : L.val=(K:ℝ)) (r b D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤ D → 1≤ D*r → 0< r → 0< b →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤ L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤ L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)) (u : Jet n L), u∈dirichletDomain n L r →
      (D*r)*(∫ X, (weightedSiteCount L A X-C*D*(A.card:ℝ)+
        c/b^3*((localizedNearLabels L A (spatialCloseScale D b) X).card:ℝ))*‖u.1 X‖^2)≤
        energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,c,hC,hc,hbound⟩ := weighted_local_penalty
  refine ⟨C,c,hC,hc,?_⟩
  intro n K L hL r b D hDeq hD hα hr hb hs' hsL hsmall g hg A u hu
  by_cases hA : A.Nonempty
  · have hDpos : 0< D := zero_lt_one.trans_le hD
    have hs := spatialCloseScale_pos hDpos hb
    have h := hbound n K L hL r (spatialCloseScale D b) D hDeq hD hα hr hs hs' hsL hsmall g hg A hA u hu
    have hf := weightedSiteCount_integrable L A u.1
    have hk := localizedNearLabels_integrable L A (spatialCloseScale D b) u.1
    have hn : Integrable (fun X ↦ ‖u.1 X‖^2) volume := (Lp.memLp u.1).integrable_norm_pow (by norm_num)
    have hsub : Integrable (fun X ↦ weightedSiteCount L A X*‖u.1 X‖^2-(C*D*(A.card:ℝ))*‖u.1 X‖^2) volume := hf.sub (hn.const_mul _)
    have heq : (fun X ↦ (weightedSiteCount L A X-C*D*(A.card:ℝ)+c/b^3*((localizedNearLabels L A (spatialCloseScale D b) X).card:ℝ))*‖u.1 X‖^2)=
        fun X ↦ (weightedSiteCount L A X*‖u.1 X‖^2-(C*D*(A.card:ℝ))*‖u.1 X‖^2)+c/b^3*(((localizedNearLabels L A (spatialCloseScale D b) X).card:ℝ)*‖u.1 X‖^2) := by funext X; ring
    rw [heq,integral_add hsub (hk.const_mul _),integral_sub hf (hn.const_mul _),
      integral_const_mul,integral_const_mul,←IndicatorStrong.norm_sq_integral]
    have he : (D*r)*(c/b^3)=c*r/(spatialCloseScale D b)^3 := by
      rw [←spatialCloseScale_cube (b:=b) hDpos]
      field_simp
    rw [mul_add,←mul_assoc (D*r) (c/b^3),he]
    exact h
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    have hz (X : Configuration n L) : localizedNearLabels L ∅ (spatialCloseScale D b) X=∅ := by
      classical
      simp [localizedNearLabels]
    simp only [weightedSiteCount,Finset.not_nonempty_empty,ite_false,Finset.card_empty,Nat.cast_zero,
      mul_zero,sub_zero,hz,add_zero,zero_mul,integral_zero]
    exact sub_nonneg.mpr (hg.rayleigh_all u hu)

end HardSphere

end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.spatial_localized_form_oai := @OAI.HardSphere.spatial_localized_form_oai
