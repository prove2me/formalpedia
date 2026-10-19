-- Prove2me | solution 1 for OAI.ClassicalON.LatticeGraph.connection_exponential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:57:43.16104+00:00
-- url     : https://prove2.me/submissions/8827eda3-df09-47cb-a041-ec84da652610

import Mathlib
import Definitions.Def_ClassicalON
import Definitions.Def_OAIQWCO002
import Theorems.Thm_OAI_ClassicalON_LatticeGraph_annulus_response_small
import Theorems.Thm_OAI_ClassicalON_continuousFKG_pi
import Theorems.Thm_OAI_ClassicalON_ising_edge_covariance_nonneg

section
-- module Solutions.OAIQW_ClassicalON.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FiniteVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uR uS uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON

theorem hasDerivAt_integral_compact
    {Ω : Type uΩ} {F : Type uF} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f fd : ℝ → Ω → F)
    (hf : Continuous (Function.uncurry f)) (hfd : Continuous (Function.uncurry fd))
    (hd : ∀ t ω, HasDerivAt (fun u => f u ω) (fd t ω) t) (t : ℝ) :
    HasDerivAt (fun u => ∫ ω, f u ω ∂μ) (∫ ω, fd t ω ∂μ) t := by
  have hi (u : ℝ) : Integrable (f u) μ :=
    (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdi (u : ℝ) : Integrable (fd u) μ :=
    (hfd.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨C, hC⟩ := (((isCompact_closedBall t 1).prod
    (isCompact_univ : IsCompact (Set.univ : Set Ω))).image hfd).isBounded.exists_norm_le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall t 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun u => (hi u).aestronglyMeasurable)
    (hi t) (hdi t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω u hu => hC _ ⟨(u, ω), ⟨hu, Set.mem_univ _⟩, rfl⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun ω u _ => hd u ω)).2

theorem spinRotation_preserves_surface {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  open scoped Pointwise in
  refine ⟨(spinRotation R).measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (spinRotation R).measurable hs,
    Measure.toSphere_apply' _ ((spinRotation R).measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((spinRotation R) ⁻¹' s)) =
      R ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext v
    constructor
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨r, hr, R t.val, ⟨spinRotation R t, ht, rfl⟩, (R.map_smul r t.val).symm⟩
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, hv⟩
      refine ⟨r, hr, R.symm t.val, ⟨(spinRotation R).symm t, ?_, rfl⟩, ?_⟩
      · simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using ht
      · apply R.injective
        simpa only [map_smul, LinearIsometryEquiv.apply_symm_apply] using hv
  rw [hcone]
  have hm := R.toHomeomorph.measurableEmbedding.map_apply
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  change (Measure.map R volume) _ = volume (R ⁻¹' _) at hm
  rw [R.measurePreserving.map_eq] at hm
  exact hm.symm

theorem spinRotation_preserves_probability {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R) (sphereProbability n) (sphereProbability n) :=
  (spinRotation_preserves_surface R).smul_measure _

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem integrable_weight [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n) :
    Integrable (fun σ => Real.exp (S.energy K σ)) S.reference :=
  (S.continuous_energy K).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem Z_pos [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n) :
    0 < S.Z K := by
  unfold Z
  apply (integral_pos_iff_support_of_nonneg
    (fun σ => (Real.exp_pos _).le) (S.integrable_weight K)).mpr
  have hs : Function.support (fun σ => Real.exp (S.energy K σ)) = Set.univ := by
    ext σ
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs, measure_univ]
  exact zero_lt_one

omit [Fintype E] in
theorem rotateConfiguration_preserves_reference [NeZero n] (S : SpinSystem n V E)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (rotateConfiguration U) S.reference (S.rotatePins U).reference := by
  change MeasurePreserving (fun σ x => spinRotation (U x) (σ x))
    (Measure.pi (fun x => siteReference n (S.pin x)))
    (Measure.pi (fun x => siteReference n ((S.pin x).map (spinRotation (U x)))))
  apply measurePreserving_pi
  intro x
  cases S.pin x with
  | none => exact spinRotation_preserves_probability (U x)
  | some s =>
    exact ⟨(spinRotation (U x)).measurable, Measure.map_dirac s⟩

omit [Fintype V] in
theorem energy_gauge (S : SpinSystem n V E) (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (σ : V → Spin n) :
    S.energy (S.gauge K U) σ = (S.rotatePins U).energy K (rotateConfiguration U σ) := by
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  change ⟪(σ (S.left e)).val,
      (U (S.left e)).symm (K e (U (S.right e) (σ (S.right e)).val))⟫_ℝ =
    ⟪U (S.left e) (σ (S.left e)).val, K e (U (S.right e) (σ (S.right e)).val)⟫_ℝ
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    ((U (S.left e)).inner_map_map (σ (S.left e)).val
      ((U (S.left e)).symm (K e (U (S.right e) (σ (S.right e)).val)))).symm

theorem Z_gauge [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    S.Z (S.gauge K U) = (S.rotatePins U).Z K := by
  unfold Z
  simp_rw [energy_gauge]
  exact (S.rotateConfiguration_preserves_reference U).integral_comp
    (rotateConfiguration U).measurableEmbedding
    (fun σ => Real.exp ((S.rotatePins U).energy K σ))

@[simp] theorem W_zero [NeZero n] (S : SpinSystem n V E) : S.W 0 = 1 := by
  simp only [W, Pi.zero_apply, NormedSpace.exp_zero]
  exact div_self (S.Z_pos _).ne'

omit [Fintype V] in
theorem continuous_twistEnergy (S : SpinSystem n V E) (A : E → SpinOperator n)
    (k : ℕ) : Continuous (Function.uncurry (S.twistEnergy A k)) := by
  unfold twistEnergy energy Function.uncurry
  fun_prop

omit [Fintype V] in
theorem hasDerivAt_twistEnergy (S : SpinSystem n V E) (A : E → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.twistEnergy A k u σ) (S.twistEnergy A (k+1) t σ) t := by
  unfold twistEnergy energy
  have he (e : E) : HasDerivAt
      (fun u => NormedSpace.exp (u • A e) * A e ^ k)
      (NormedSpace.exp (t • A e) * A e ^ (k+1)) t := by
    exact ((hasDerivAt_exp_smul_const (A e) t).mul_const (A e ^ k)).congr_deriv
      (by rw [pow_succ', mul_assoc])
  apply HasDerivAt.fun_sum
  intro e _
  exact (((hasDerivAt_const t (σ (S.left e)).val).inner ℝ
    ((he e).clm_apply (hasDerivAt_const t (σ (S.right e)).val))).const_mul
      (S.strength e)).congr_deriv (by simp)

omit [Fintype V] in
theorem continuous_firstWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.firstWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul (S.continuous_twistEnergy A 1)

omit [Fintype V] in
theorem continuous_secondWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.secondWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    ((S.continuous_twistEnergy A 2).add ((S.continuous_twistEnergy A 1).pow 2))

omit [Fintype V] in
theorem hasDerivAt_weight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => Real.exp (S.twistEnergy A 0 u σ)) (S.firstWeight A t σ) t := by
  exact (S.hasDerivAt_twistEnergy A 0 t σ).exp

omit [Fintype V] in
theorem hasDerivAt_firstWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.firstWeight A u σ) (S.secondWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul (S.hasDerivAt_twistEnergy A 1 t σ)).congr_deriv
    (by unfold firstWeight secondWeight; ring)

theorem hasDerivAt_twistZ [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => S.Z (fun e => NormedSpace.exp (u • A e)))
      (∫ σ, S.firstWeight A t σ ∂S.reference) t := by
  simpa only [twistEnergy, pow_zero, mul_one, Z] using
    hasDerivAt_integral_compact S.reference
      (fun u σ => Real.exp (S.twistEnergy A 0 u σ)) (S.firstWeight A)
      (S.continuous_twistEnergy A 0).rexp (S.continuous_firstWeight A)
      (S.hasDerivAt_weight A) t

theorem hasDerivAt_firstVariation [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.firstWeight A u σ ∂S.reference)
      (∫ σ, S.secondWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.firstWeight A) (S.secondWeight A)
    (S.continuous_firstWeight A) (S.continuous_secondWeight A)
    (S.hasDerivAt_firstWeight A) t

omit [Fintype V] [Fintype E] in

theorem exp_smul_add (g : SpinOperator n) (r s : ℝ) :
    NormedSpace.exp ((r+s) • g) = NormedSpace.exp (r • g) * NormedSpace.exp (s • g) := by
  rw [add_smul r s g]
  apply NormedSpace.exp_add_of_commute
  change (r • g) * (s • g) = (s • g) * (r • g)
  rw [Algebra.smul_mul_assoc r g (s • g), Algebra.mul_smul_comm s g g,
    smul_smul r s (g*g), Algebra.smul_mul_assoc s g (r • g),
    Algebra.mul_smul_comm r g g, smul_smul s r (g*g), mul_comm r s]

@[simp] theorem average_const [NeZero n] (S : SpinSystem n V E) (c : ℝ) :
    S.average (fun _ => c) = c := by
  unfold average
  rw [integral_const_mul]
  change c * S.Z (fun _ => 1) / S.Z (fun _ => 1) = c
  exact mul_div_cancel_right₀ c (S.Z_pos _).ne'

end SpinSystem

open scoped Matrix

theorem axisC_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisC v = WithLp.toLp 2 ![-v 1, v 0, 0] := by
  rw [axisC, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SmoothProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped Topology ContDiff

namespace ClassicalON

theorem thetaBump_one {x : ℝ} (hx : |x| ≤ 4/3) : thetaBump x = 1 := by
  apply thetaBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, thetaBump] using hx

theorem thetaBump_zero {x : ℝ} (hx : 5/3 ≤ |x|) : thetaBump x = 0 := by
  apply thetaBump.zero_of_le_dist
  simpa [Real.dist_eq, thetaBump] using hx

theorem squareTheta_one (z : ℝ × ℝ) (hx : |z.1| ≤ 1) (hy : |z.2| ≤ 1) :
    squareTheta z = 1 := by
  rw [squareTheta, thetaBump_one (by linarith), thetaBump_one (by linarith), mul_one]

theorem squareTheta_zero (z : ℝ × ℝ) (h : 2 ≤ |z.1| ∨ 2 ≤ |z.2|) :
    squareTheta z = 0 := by
  rcases h with hx | hy
  · simp [squareTheta, thetaBump_zero (by linarith : 5/3 ≤ |z.1|)]
  · simp [squareTheta, thetaBump_zero (by linarith : 5/3 ≤ |z.2|)]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.LatticeRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON

theorem siteRadius_nonneg (z v : Site) : 0≤ siteRadius z v := le_trans (abs_nonneg _) (le_max_left _ _)

theorem siteRadius_le_iff (z v : Site) (N : ℤ) :
    siteRadius z v≤N ↔ |v.1-z.1|≤N ∧ |v.2-z.2|≤N := max_le_iff

theorem siteRadius_neighbor {x y : Site} (h : PositiveNeighbor x y) : siteRadius x y=1 := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp [siteRadius,h1,h2]

theorem siteRadius_neighbor_step (z : Site) {x y : Site} (h : PositiveNeighbor x y ∨ PositiveNeighbor y x) :
    siteRadius z y≤ siteRadius z x+1 ∧ siteRadius z x≤ siteRadius z y+1 := by
  have hh : siteRadius x y=1 := by
    rcases h with h | h
    · exact siteRadius_neighbor h
    · rw [siteRadius_symm]; exact siteRadius_neighbor h
  constructor
  · simpa only [hh] using siteRadius_triangle z x y
  · have := siteRadius_triangle z y x
    rwa [siteRadius_symm y x,hh] at this

theorem annulusSites_not_boundary (N : ℤ) (z v : Site) :
    v∈annulusSites N z ∧ v∉annulusBoundary N z ↔ v∈annulusInterior N z := by
  simp only [annulusSites,annulusBoundary,annulusInterior,mem_ofPred_eq]
  omega

theorem neighbor_in_annulus {N : ℤ} {z x y : Site} (hx : x∈annulusInterior N z)
    (hxy : PositiveNeighbor x y ∨ PositiveNeighbor y x) : y∈annulusSites N z := by
  have hh := siteRadius_neighbor_step z hxy
  change N<siteRadius z x ∧ siteRadius z x<2*N at hx
  change N≤ siteRadius z y ∧ siteRadius z y≤2*N
  omega

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK

noncomputable section
open Set
open scoped Classical
namespace ClassicalON
variable {K : Type uK}

namespace LatticeGraph

theorem annulus_vertex_edge_label (G : LatticeGraph) (N : ℤ) (_hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (e : G.edges) (v w : G.vertices)
    (he : (v=e.val.1 ∧ w=e.val.2) ∨ (v=e.val.2 ∧ w=e.val.1))
    (hv : v∉G.allAnnulusPins N z) : G.annulusVertexLabel N z v=G.annulusEdgeLabel N z e := by
  have hstep : PositiveNeighbor v.val w.val ∨ PositiveNeighbor w.val v.val := by
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl (G.nearest e.val e.property)
    · exact Or.inr (G.nearest e.val e.property)
  have hvp : v.val∉centerPins N z := hv
  cases hl : G.annulusVertexLabel N z v with
  | none =>
    cases hel : G.annulusEdgeLabel N z e with
    | none => rfl
    | some i =>
      have hh := (G.annulusEdgeLabel_some_iff N z hz e i).mp hel
      have hh' : v.val∈annulusSites N (z i) := by rcases he with ⟨rfl,_⟩ | ⟨rfl,_⟩; exact hh.1; exact hh.2
      have := (centerLabel_some_iff N z hz v.val i).mpr hh'
      change G.annulusVertexLabel N z v=some i at this
      rw [hl] at this
      cases this
  | some i =>
    have hi := (centerLabel_some_iff N z hz v.val i).mp hl
    have hvi : v.val∈annulusInterior N (z i) :=
      (annulusSites_not_boundary N (z i) v.val).mp ⟨hi,fun h => hvp ⟨i,h⟩⟩
    have hwi := neighbor_in_annulus hvi hstep
    symm
    apply (G.annulusEdgeLabel_some_iff N z hz e i).mpr
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hi,hwi⟩
    · exact ⟨hwi,hi⟩

theorem annulus_left_label (G : LatticeGraph) (N : ℤ) (hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (e : G.edges) (hv : e.val.1∉G.allAnnulusPins N z) :
    G.annulusVertexLabel N z e.val.1=G.annulusEdgeLabel N z e :=
  G.annulus_vertex_edge_label N hN z hz e e.val.1 e.val.2 (Or.inl ⟨rfl,rfl⟩) hv

theorem annulus_right_label (G : LatticeGraph) (N : ℤ) (hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (e : G.edges) (hv : e.val.2∉G.allAnnulusPins N z) :
    G.annulusVertexLabel N z e.val.2=G.annulusEdgeLabel N z e :=
  G.annulus_vertex_edge_label N hN z hz e e.val.2 e.val.1 (Or.inr ⟨rfl,rfl⟩) hv

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open scoped Classical
namespace ClassicalON

theorem siteRadius_scale (N : ℤ) (hN : 0≤N) (x y : Site) :
    siteRadius (coarseCenter N x) (coarseCenter N y)=N*siteRadius x y := by
  simp only [siteRadius,coarseCenter,← mul_sub,abs_mul,abs_of_nonneg hN]
  exact (mul_max_of_nonneg _ _ hN).symm

theorem coarseSite_close (N : ℤ) (hN : 0<N) (v : Site) :
    siteRadius (coarseCenter N (coarseSite N v)) v<N := by
  change max |v.1-N*(v.1/N)| |v.2-N*(v.2/N)|<N
  rw [max_lt_iff]
  constructor
  · have he := Int.emod_add_ediv_mul v.1 N
    rw [mul_comm (v.1/N) N] at he
    have hn := Int.emod_nonneg v.1 (ne_of_gt hN)
    have hl := Int.emod_lt_of_pos v.1 hN
    rw [show v.1-N*(v.1/N)=v.1%N by omega,abs_of_nonneg hn]
    exact hl
  · have he := Int.emod_add_ediv_mul v.2 N
    rw [mul_comm (v.2/N) N] at he
    have hn := Int.emod_nonneg v.2 (ne_of_gt hN)
    have hl := Int.emod_lt_of_pos v.2 hN
    rw [show v.2-N*(v.2/N)=v.2%N by omega,abs_of_nonneg hn]
    exact hl

theorem coarse_quotient_step (N : ℤ) (hN : 0<N) (a b : ℤ) (h : |b-a|≤1) :
    |b/N-a/N|≤1 := by
  have hab := abs_le.mp h
  have h1 : b≤a+N := by omega
  have h2 : a≤b+N := by omega
  have hh1 := Int.ediv_le_ediv hN h1
  have hh2 := Int.ediv_le_ediv hN h2
  rw [Int.add_ediv_of_dvd_right (dvd_refl N),Int.ediv_self (ne_of_gt hN)] at hh1 hh2
  exact abs_le.mpr ⟨by omega,by omega⟩

theorem coarseSite_step (N : ℤ) (hN : 0<N) {x y : Site} (h : siteRadius x y≤1) :
    siteRadius (coarseSite N x) (coarseSite N y)≤1 := by
  have hh := siteRadius_le_iff x y 1 |>.mp h
  exact max_le (coarse_quotient_step N hN _ _ hh.1) (coarse_quotient_step N hN _ _ hh.2)

theorem coarseSite_distance (N : ℤ) (hN : 0<N) (x y : Site) :
    siteRadius x y≤N*(siteRadius (coarseSite N x) (coarseSite N y)+2) := by
  have h1 := coarseSite_close N hN x
  have h2 := coarseSite_close N hN y
  have h3 := siteRadius_triangle x (coarseCenter N (coarseSite N x)) y
  have h4 := siteRadius_triangle (coarseCenter N (coarseSite N x)) (coarseCenter N (coarseSite N y)) y
  rw [siteRadius_scale N (le_of_lt hN)] at h4
  rw [siteRadius_symm x (coarseCenter N (coarseSite N x))] at h3
  nlinarith

theorem sameColor_far {x y : Site} (hxy : x≠y) (h : siteColor x=siteColor y) :
    4<siteRadius x y := by
  have h1 := congrArg (fun c : SiteColor => c.1.val) h
  have h2 := congrArg (fun c : SiteColor => c.2.val) h
  change (x.1%5).toNat=(y.1%5).toNat at h1
  change (x.2%5).toNat=(y.2%5).toNat at h2
  by_contra hn
  have hr : |y.1-x.1|≤4 ∧ |y.2-x.2|≤4 := (siteRadius_le_iff x y 4).mp (by omega)
  have ha := abs_le.mp hr.1
  have hb := abs_le.mp hr.2
  apply hxy
  apply Prod.ext <;> omega

theorem sameColor_separated {ι : Type uι} (N : ℤ) (hN : 0<N) (v : ι → Site)
    (hv : Function.Injective v) (c : SiteColor) :
    SeparatedCenters N (fun i : {i // siteColor (v i)=c} => coarseCenter N (v i.val)) := by
  intro i j hij
  rw [siteRadius_scale N (le_of_lt hN)]
  have hd : v i.val≠v j.val := fun h => hij (Subtype.ext (hv h))
  have hh := sameColor_far hd (i.property.trans j.property.symm)
  nlinarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarseCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

theorem codePosition_succ {L : ℕ} (z : Site) (c : CoarseCode L) (i : Fin L) :
    codePosition z c i.succ=codePosition z c i.castSucc+directionVector (c i) := by
  simp only [codePosition,Fin.partialSum_succ,Function.comp_apply,add_assoc]

theorem directionVector_surj {z w : Site} (h : siteRadius z w≤1) :
    ∃ d,directionVector d=w-z := by
  have hh := (siteRadius_le_iff z w 1).mp h
  have h1 := abs_le.mp hh.1
  have h2 := abs_le.mp hh.2
  refine ⟨(⟨(w.1-z.1+1).toNat,by omega⟩,⟨(w.2-z.2+1).toNat,by omega⟩),?_⟩
  apply Prod.ext <;> dsimp [directionVector] <;> omega

theorem codePosition_exists {L : ℕ} (p : Fin (L+1) → Site)
    (h : ∀ i : Fin L,siteRadius (p i.castSucc) (p i.succ)≤1) :
    ∃ c : CoarseCode L,codePosition (p 0) c=p := by
  choose c hc using fun i => directionVector_surj (h i)
  refine ⟨c,funext fun i => ?_⟩
  induction i using Fin.induction with
  | zero => exact codePosition_zero _ _
  | succ i ih => rw [codePosition_succ,ih,hc]; abel

theorem card_simpleCoarseCode (z : Site) (L : ℕ) : Fintype.card (SimpleCoarseCode z L)≤9^L := by
  calc
    _≤Fintype.card (CoarseCode L) := Fintype.card_subtype_le _
    _=9^L := by simp [CoarseCode,CoarseDirection]

theorem codeColor_card (t : ℕ) (z : Site) (c : CoarseCode (25*t)) :
    t≤Fintype.card {i : Fin (25*t+1) // siteColor (codePosition z c i)=codeColor t z c} :=
  (codeColor_exists t z c).choose_spec

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AssociationCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ClassicalON

section CompactIntegral
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} [IsFiniteMeasure μ]

theorem compact_integrable {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem compact_integral_pos [IsProbabilityMeasure μ] {w : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) : 0<∫ x,w x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) (compact_integrable hw)).2
  have he : Function.support w=univ := by ext x; simp [Function.mem_support,(hp x).ne']
  rw [he,measure_univ]
  exact zero_lt_one

omit [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
theorem compact_parametric_integral [FirstCountableTopology Y] [LocallyCompactSpace Y]
    (f : Y → X → ℝ) (hf : Continuous f.uncurry) : Continuous (fun y => ∫ x,f y x ∂μ) := by
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous hf (isCompact_univ : IsCompact (univ : Set X)))

end CompactIntegral

section Weighted
variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
  [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {w : X → ℝ}
  (hw : Continuous w) (hp : ∀ x,0<w x)

include hw hp

theorem weightedMean_nonneg {f : X → ℝ} (hf : ∀ x,0≤f x) : 0≤weightedMean μ w f := by
  exact div_nonneg (integral_nonneg (fun x => mul_nonneg (hp x).le (hf x)))
    (compact_integral_pos hw hp).le

theorem weightedMean_mono {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x,f x≤g x) : weightedMean μ w f ≤ weightedMean μ w g := by
  exact div_le_div_of_nonneg_right
    (integral_mono (compact_integrable (hw.mul hf)) (compact_integrable (hw.mul hg))
      (fun x => mul_le_mul_of_nonneg_left (hfg x) (hp x).le)) (compact_integral_pos hw hp).le

theorem weightedMean_inequality_iff {f g : X → ℝ} :
    weightedMean μ w f * weightedMean μ w g ≤ weightedMean μ w (fun x => f x*g x) ↔
    (∫ x,w x*f x ∂μ)*(∫ x,w x*g x ∂μ) ≤ (∫ x,w x ∂μ)*(∫ x,w x*(f x*g x) ∂μ) := by
  unfold weightedMean
  have hm := compact_integral_pos (μ := μ) hw hp
  rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos hm hm) hm]
  constructor <;> intro h <;> nlinarith

end Weighted

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.GibbsDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open MeasureTheory
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem hasDerivAt_exponentialIntegral {H A f : X → ℝ}
    (hH : Continuous H) (hA : Continuous A) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun u => ∫ x,Real.exp (H x+u*A x)*f x ∂μ)
      (∫ x,Real.exp (H x+t*A x)*(f x*A x) ∂μ) t := by
  apply hasDerivAt_integral_compact μ
    (fun u x => Real.exp (H x+u*A x)*f x)
    (fun u x => Real.exp (H x+u*A x)*(f x*A x)) (by fun_prop) (by fun_prop)
  intro u x
  exact ((((hasDerivAt_id u).mul_const (A x)).const_add (H x)).exp.mul_const (f x)).congr_deriv (by simp only [id_eq]; ring)

theorem hasDerivAt_exponentialMean {H A f : X → ℝ}
    (hH : Continuous H) (hA : Continuous A) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun u => exponentialMean μ (fun x => H x+u*A x) f)
      (exponentialMean μ (fun x => H x+t*A x) (fun x => f x*A x)-
        exponentialMean μ (fun x => H x+t*A x) f*
        exponentialMean μ (fun x => H x+t*A x) A) t := by
  have hN := hasDerivAt_exponentialIntegral μ hH hA hf t
  have hD := hasDerivAt_exponentialIntegral μ hH hA continuous_const t (f := fun _ => 1)
  simp only [mul_one,one_mul] at hD
  have hz : (∫ x,Real.exp (H x+t*A x) ∂μ)≠0 :=
    (compact_integral_pos (by fun_prop) (fun x => Real.exp_pos _)).ne'
  exact (hN.div hD hz).congr_deriv (by unfold exponentialMean weightedMean; field_simp)

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.WeightedLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  {w : X → ℝ}

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem weightedMean_const_mul (c : ℝ) (f : X → ℝ) :
    weightedMean μ w (fun x => c*f x)=c*weightedMean μ w f := by
  unfold weightedMean
  simp only [show (fun x => w x*(c*f x))=(fun x => c*(w x*f x)) from by funext; ring,
    integral_const_mul]
  ring

theorem weightedMean_sum (hw : Continuous w) {E : Type uE} [Fintype E] (f : E → X → ℝ)
    (hf : ∀ e,Continuous (f e)) : weightedMean μ w (fun x => ∑ e,f e x)=
      ∑ e,weightedMean μ w (f e) := by
  unfold weightedMean
  simp_rw [Finset.mul_sum]
  have hI (e : E) : Integrable (fun x => w x*f e x) μ := compact_integrable (by fun_prop)
  rw [integral_finsetSum _ (fun e _ => hI e),Finset.sum_div]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem exponentialMean_const_mul (H : X → ℝ) (c : ℝ) (f : X → ℝ) :
    exponentialMean μ H (fun x => c*f x)=c*exponentialMean μ H f :=
  weightedMean_const_mul μ c f

theorem exponentialMean_sum {E : Type uE} [Fintype E] {H : X → ℝ}
    (hH : Continuous H) (f : E → X → ℝ) (hf : ∀ e,Continuous (f e)) :
    exponentialMean μ H (fun x => ∑ e,f e x)=∑ e,exponentialMean μ H (f e) :=
  weightedMean_sum μ hH.rexp f hf

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem exponentialMean_zero (f : X → ℝ) :
    exponentialMean μ (fun _ => 0) f=∫ x,f x ∂μ := by
  simp [exponentialMean,weightedMean]

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FerromagneticMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_edgeHamiltonian (hT : ∀ e,Continuous (T e)) (b : E → ℝ) :
    Continuous (edgeHamiltonian T b) := by
  exact continuous_finsetSum _ (fun e _ => continuous_const.mul (hT e))

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem edgeMean_zero (f : X → ℝ) : edgeMean μ T (fun _ => 0) f=∫ x,f x ∂μ := by
  have hz : edgeHamiltonian T (fun _ => 0)=(fun _ => 0) := by funext x; simp [edgeHamiltonian]
  unfold edgeMean
  rw [hz,exponentialMean_zero]

theorem edgeMean_direction_derivative (hT : ∀ e,Continuous (T e)) (b d : E → ℝ)
    (e : E) (t : ℝ) :
    HasDerivAt (fun u => edgeMean μ T (fun g => b g+u*d g) (T e))
      (∑ g,d g*(edgeMean μ T (fun h => b h+t*d h) (fun x => T e x*T g x)-
        edgeMean μ T (fun h => b h+t*d h) (T e)*
        edgeMean μ T (fun h => b h+t*d h) (T g))) t := by
  have he (u : ℝ) (x : X) : edgeHamiltonian T (fun g => b g+u*d g) x=
      edgeHamiltonian T b x+u*edgeHamiltonian T d x := by
    simp only [edgeHamiltonian,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
  have hd := hasDerivAt_exponentialMean μ (continuous_edgeHamiltonian T hT b)
    (continuous_edgeHamiltonian T hT d) (hT e) t
  simp_rw [← he] at hd
  change HasDerivAt (fun u => exponentialMean μ (edgeHamiltonian T (fun g => b g+u*d g)) (T e)) _ _
  apply hd.congr_deriv
  rw [show (fun x => T e x*edgeHamiltonian T d x)=
    (fun x => ∑ g,d g*(T e x*T g x)) by funext; simp only [edgeHamiltonian,Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [exponentialMean_sum μ (continuous_edgeHamiltonian T hT _) _ (fun g => by fun_prop)]
  change (∑ g,exponentialMean μ _ (fun x => d g*(T e x*T g x)))-
    exponentialMean μ _ (T e)*exponentialMean μ _ (fun x => ∑ g,d g*T g x)=_
  rw [exponentialMean_sum μ (continuous_edgeHamiltonian T hT _) _ (fun g => by fun_prop)]
  simp only [exponentialMean_const_mul,Finset.mul_sum,← Finset.sum_sub_distrib,edgeMean]
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem edgeMean_mono_couplings (hT : ∀ e,Continuous (T e))
    (hCov : EdgeCovarianceNonneg μ T) {a b : E → ℝ}
    (ha : ∀ e,0≤a e) (hab : ∀ e,a e≤b e) (e : E) :
    edgeMean μ T a (T e)≤edgeMean μ T b (T e) := by
  let d := fun g => b g-a g
  let F := fun t => edgeMean μ T (fun g => a g+t*d g) (T e)
  have hD := edgeMean_direction_derivative μ T hT a d e
  have hM : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t _ => (hD t).continuousAt.continuousWithinAt)
      (fun t _ => (hD t).hasDerivWithinAt)
    intro t ht
    apply Finset.sum_nonneg
    intro g _
    apply mul_nonneg (sub_nonneg.mpr (hab g))
    apply sub_nonneg.mpr
    apply hCov
    intro h
    have ht0 : 0≤t := (interior_subset ht).1
    exact add_nonneg (ha h) (mul_nonneg ht0 (sub_nonneg.mpr (hab h)))
  have hh := hM (by simp : (0 : ℝ)∈Icc 0 1) (by simp : (1 : ℝ)∈Icc 0 1) (by norm_num)
  simpa only [F,d,zero_mul,add_zero,one_mul,add_sub_cancel] using hh

theorem edgeMean_nonneg (hT : ∀ e,Continuous (T e)) (hCov : EdgeCovarianceNonneg μ T)
    (h0 : ∀ e,0≤∫ x,T e x ∂μ) (b : E → ℝ) (hb : ∀ e,0≤b e) (e : E) :
    0≤edgeMean μ T b (T e) := by
  have hh := edgeMean_mono_couplings μ T hT hCov (fun _ => le_rfl) hb e
  rw [edgeMean_zero] at hh
  exact (h0 e).trans hh

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {V : Type uV} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ) (left right : E → V) (b : E → ℝ)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
 theorem continuous_amplitudeHamiltonian (hT : ∀ e,Continuous (T e)) :
    Continuous (fun p : (V → ℝ)×X => edgeHamiltonian T
      (amplitudeCoupling left right b p.1) p.2) := by
  unfold edgeHamiltonian amplitudeCoupling
  fun_prop

theorem amplitudePartition_pos (hT : ∀ e,Continuous (T e)) (a : V → ℝ) :
    0<amplitudePartition μ T left right b a := by
  exact compact_integral_pos (continuous_edgeHamiltonian T hT _).rexp (fun x => Real.exp_pos _)

theorem continuous_amplitudePartition [Fintype V] (hT : ∀ e,Continuous (T e)) :
    Continuous (amplitudePartition μ T left right b) := by
  exact compact_parametric_integral _ (continuous_amplitudeHamiltonian T left right b hT).rexp

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem amplitudeHamiltonian_direction_derivative (a d : V → ℝ) (t : ℝ) (x : X) :
    HasDerivAt (fun u => edgeHamiltonian T
      (amplitudeCoupling left right b (fun v => a v+u*d v)) x)
      (edgeHamiltonian T (amplitudeSlope left right b a d t) x) t := by
  unfold edgeHamiltonian
  apply HasDerivAt.fun_sum
  intro e _
  have hl := ((hasDerivAt_id t).mul_const (d (left e))).const_add (a (left e))
  have hr := ((hasDerivAt_id t).mul_const (d (right e))).const_add (a (right e))
  exact (((hl.const_mul (b e)).mul hr).mul_const (T e x)).congr_deriv (by
    simp only [id_eq,amplitudeSlope]; ring)

theorem log_amplitudePartition_direction_derivative (hT : ∀ e,Continuous (T e))
    (a d : V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => Real.log (amplitudePartition μ T left right b (fun v => a v+u*d v)))
      (∑ e,amplitudeSlope left right b a d t e*
        edgeMean μ T (amplitudeCoupling left right b (fun v => a v+t*d v)) (T e)) t := by
  let H := fun u x => edgeHamiltonian T
    (amplitudeCoupling left right b (fun v => a v+u*d v)) x
  let A := fun u x => edgeHamiltonian T (amplitudeSlope left right b a d u) x
  have hc : Continuous (fun p : ℝ×X => H p.1 p.2) := by
    unfold H edgeHamiltonian amplitudeCoupling; fun_prop
  have ha : Continuous (fun p : ℝ×X => A p.1 p.2) := by
    unfold A edgeHamiltonian amplitudeSlope; fun_prop
  have hI := hasDerivAt_integral_compact μ (fun u x => Real.exp (H u x))
    (fun u x => Real.exp (H u x)*A u x) hc.rexp (hc.rexp.mul ha) (fun u x =>
      (amplitudeHamiltonian_direction_derivative T left right b a d u x).exp) t
  have hz := amplitudePartition_pos μ T left right b hT (fun v => a v+t*d v)
  apply (hI.log hz.ne').congr_deriv
  change exponentialMean μ (H t) (A t)=_
  unfold A edgeHamiltonian
  rw [exponentialMean_sum μ (continuous_edgeHamiltonian T hT _) _ (fun e => by fun_prop)]
  simp only [exponentialMean_const_mul,edgeMean]

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype E] in
 theorem amplitudeCoupling_mono (hb : ∀ e,0≤b e) {a c : V → ℝ}
    (ha : ∀ v,0≤a v) (hac : ∀ v,a v≤c v) (e : E) :
    amplitudeCoupling left right b a e≤amplitudeCoupling left right b c e := by
  unfold amplitudeCoupling
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hac _) (hb e)) (hac _)
    (ha _) (mul_nonneg (hb e) ((ha _).trans (hac _)))

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype E] in
 theorem amplitudeSlope_nonneg (hb : ∀ e,0≤b e) {a d : V → ℝ}
    (ha : ∀ v,0≤a v) (hd : ∀ v,0≤d v) {t : ℝ} (ht : 0≤t) (e : E) :
    0≤amplitudeSlope left right b a d t e := by
  unfold amplitudeSlope
  exact mul_nonneg (hb e) (add_nonneg
    (mul_nonneg (hd _) (add_nonneg (ha _) (mul_nonneg ht (hd _))))
    (mul_nonneg (add_nonneg (ha _) (mul_nonneg ht (hd _))) (hd _)))

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype E] in
 theorem amplitudeSlope_mono (hb : ∀ e,0≤b e) {a c d : V → ℝ}
    (hd : ∀ v,0≤d v) (hac : ∀ v,a v≤c v) (t : ℝ) (e : E) :
    amplitudeSlope left right b a d t e≤amplitudeSlope left right b c d t e := by
  unfold amplitudeSlope
  apply mul_le_mul_of_nonneg_left _ (hb e)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (hac _) le_rfl) (hd _))
    (mul_le_mul_of_nonneg_right (add_le_add (hac _) le_rfl) (hd _))

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudeModular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {V : Type uV} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ) (left right : E → V) (b : E → ℝ)
  (hT : ∀ e,Continuous (T e)) (hCov : EdgeCovarianceNonneg μ T)
  (h0 : ∀ e,0≤∫ x,T e x ∂μ) (hb : ∀ e,0≤b e)

include hT hCov h0 hb

theorem log_amplitudePartition_increment_mono {a c d : V → ℝ}
    (ha : ∀ v,0≤a v) (hac : ∀ v,a v≤c v) (hd : ∀ v,0≤d v) :
    Real.log (amplitudePartition μ T left right b (fun v => a v+d v))-
        Real.log (amplitudePartition μ T left right b a) ≤
      Real.log (amplitudePartition μ T left right b (fun v => c v+d v))-
        Real.log (amplitudePartition μ T left right b c) := by
  let F := fun t => Real.log (amplitudePartition μ T left right b (fun v => c v+t*d v))-
    Real.log (amplitudePartition μ T left right b (fun v => a v+t*d v))
  have hD (t : ℝ) := (log_amplitudePartition_direction_derivative μ T left right b hT c d t).sub
    (log_amplitudePartition_direction_derivative μ T left right b hT a d t)
  have hM : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t _ => (hD t).continuousAt.continuousWithinAt)
      (fun t _ => (hD t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0≤t := (interior_subset ht).1
    apply sub_nonneg.mpr
    apply Finset.sum_le_sum
    intro e _
    have hJa : ∀ g,0≤amplitudeCoupling left right b (fun v => a v+t*d v) g := by
      intro g
      unfold amplitudeCoupling
      exact mul_nonneg (mul_nonneg (hb g) (add_nonneg (ha _) (mul_nonneg ht0 (hd _))))
        (add_nonneg (ha _) (mul_nonneg ht0 (hd _)))
    have hJ : ∀ g,amplitudeCoupling left right b (fun v => a v+t*d v) g≤
        amplitudeCoupling left right b (fun v => c v+t*d v) g := by
      apply amplitudeCoupling_mono left right b hb
      · intro v; exact add_nonneg (ha v) (mul_nonneg ht0 (hd v))
      · intro v; exact add_le_add (hac v) le_rfl
    have hm := edgeMean_mono_couplings μ T hT hCov hJa hJ e
    apply mul_le_mul (amplitudeSlope_mono left right b hb hd hac t e) hm
    · exact edgeMean_nonneg μ T hT hCov h0 _ hJa e
    · exact amplitudeSlope_nonneg left right b hb (fun v => (ha v).trans (hac v)) hd ht0 e
  have hi := hM (by simp : (0 : ℝ)∈Icc 0 1) (by simp : (1 : ℝ)∈Icc 0 1) (by norm_num)
  simp only [F,zero_mul,add_zero,one_mul] at hi
  linarith

theorem amplitudePartition_supermodular {u v : V → ℝ}
    (hu : ∀ i,0≤u i) (hv : ∀ i,0≤v i) :
    amplitudePartition μ T left right b u*amplitudePartition μ T left right b v ≤
      amplitudePartition μ T left right b (u⊓v)*amplitudePartition μ T left right b (u⊔v) := by
  let a := u⊓v
  let d := fun i => u i-a i
  have ha : ∀ i,0≤a i := by intro i; exact le_min (hu i) (hv i)
  have hd : ∀ i,0≤d i := by intro i; exact sub_nonneg.mpr (min_le_left _ _)
  have had : (fun i => a i+d i)=u := by funext i; dsimp [d]; ring
  have hvd : (fun i => v i+d i)=u⊔v := by
    funext i
    dsimp [d,a]
    rcases le_total (u i) (v i) with h | h
    · rw [min_eq_left h,max_eq_right h]; ring
    · rw [min_eq_right h,max_eq_left h]; ring
  have hi := log_amplitudePartition_increment_mono μ T left right b hT hCov h0 hb
    ha (fun i => min_le_right (u i) (v i)) hd
  rw [had,hvd] at hi
  have hp := amplitudePartition_pos μ T left right b hT
  apply (Real.log_le_log_iff (mul_pos (hp u) (hp v)) (mul_pos (hp _) (hp _))).mp
  rw [Real.log_mul (hp u).ne' (hp v).ne',Real.log_mul (hp _).ne' (hp _).ne']
  linarith

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ExpMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

theorem real_hasSum_exp (x : ℝ) : HasSum (fun k : ℕ => x^k/(k.factorial : ℝ)) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem hasSum_integral_mul_exp {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h) :
    HasSum (fun k : ℕ => (∫ x,f x*h x^k ∂μ)/(k.factorial : ℝ))
      (∫ x,f x*Real.exp (h x) ∂μ) := by
  let F : ℕ → X → ℝ := fun k x => f x*(h x^k/(k.factorial : ℝ))
  let B : ℕ → X → ℝ := fun k x => ‖f x‖*(‖h x‖^k/(k.factorial : ℝ))
  have hF : ∀ k,AEStronglyMeasurable (F k) μ := by
    intro k
    exact (compact_integrable (show Continuous (F k) from (hf.mul ((hh.pow k).div_const _)))).aestronglyMeasurable
  have hB : ∀ k,∀ᵐ x ∂μ,‖F k x‖≤B k x := by
    intro k
    filter_upwards with x
    simp only [F,B,norm_mul,norm_div,norm_pow,Real.norm_natCast]
    exact le_rfl
  have hS : ∀ᵐ x ∂μ,Summable (fun k => B k x) := by
    filter_upwards with x
    exact ((real_hasSum_exp ‖h x‖).mul_left ‖f x‖).summable
  have hI : Integrable (fun x => ∑' k,B k x) μ := by
    have he : (fun x => ∑' k : ℕ,B k x) = (fun x => ‖f x‖*Real.exp ‖h x‖) := by
      funext x; exact ((real_hasSum_exp ‖h x‖).mul_left ‖f x‖).tsum_eq
    rw [he]
    exact compact_integrable (hf.norm.mul hh.norm.rexp)
  have hL : ∀ᵐ x ∂μ,HasSum (fun k => F k x) (f x*Real.exp (h x)) := by
    filter_upwards with x
    exact (real_hasSum_exp (h x)).mul_left (f x)
  have ht := hasSum_integral_of_dominated_convergence B hF hB hS hI hL
  simpa only [F,← mul_div_assoc,integral_div] using ht

theorem integral_mul_exp_nonneg_of_moments {f h : X → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hm : ∀ k : ℕ,0≤∫ x,f x*h x^k ∂μ) : 0≤∫ x,f x*Real.exp (h x) ∂μ :=
  (hasSum_integral_mul_exp μ hf hh).nonneg (fun k => div_nonneg (hm k) (Nat.cast_nonneg _))

theorem integral_mul_sum_exp_nonneg {E : Type uE} [Fintype E]
    {f : X → ℝ} {a : E → X → ℝ} (hf : Continuous f)
    (ha : ∀ e,Continuous (a e)) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (hm : ∀ (k : ℕ) (p : Fin k → E),0≤∫ x,f x*∏ i,a (p i) x ∂μ) :
    0≤∫ x,f x*Real.exp (∑ e,b e*a e x) ∂μ := by
  apply integral_mul_exp_nonneg_of_moments μ hf (by fun_prop)
  intro k
  simp_rw [Fintype.sum_pow,Finset.mul_sum]
  rw [integral_finsetSum _ (fun p _ => compact_integrable (by fun_prop))]
  apply Finset.sum_nonneg
  intro p _
  have he : (fun x => f x*∏ i,b (p i)*a (p i) x)=
      (fun x => (∏ i,b (p i))*(f x*∏ i,a (p i) x)) := by
    funext x; rw [Finset.prod_mul_distrib]; ring
  rw [he,integral_const_mul]
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => hb (p i))) (hm k p)

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProductMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {I : Type uI} {X : Type uX} [Fintype V] [DecidableEq V]

theorem site_grouping (a : I → X → ℝ) (l : List (V×I)) (x : V → X) :
    (l.map (fun p => a p.2 (x p.1))).prod =
      ∏ v,((retainedIndices v l).map (fun i => a i (x v))).prod := by
  induction l with
  | nil => simp [retainedIndices]
  | cons p l ih =>
    have hv (v : V) :
        ((retainedIndices v (p::l)).map (fun i => a i (x v))).prod =
        (if p.1=v then a p.2 (x p.1) else 1)*
          ((retainedIndices v l).map (fun i => a i (x v))).prod := by
      by_cases h : p.1=v
      · subst v; simp [retainedIndices]
      · simp [retainedIndices,h]
    simp only [List.map_cons,List.prod_cons,ih,hv,Finset.prod_mul_distrib]
    congr 1
    simp

theorem independent_moments_nonneg [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (a : I → X → ℝ)
    (hm : ∀ l : List I,0≤∫ x,(l.map (fun i => a i x)).prod ∂μ)
    (l : List (V×I)) :
    0≤∫ x : V → X,(l.map (fun p => a p.2 (x p.1))).prod ∂Measure.pi (fun _ => μ) := by
  simp_rw [site_grouping a l]
  rw [integral_fintype_prod_eq_prod (fun v x =>
    (List.map (fun i => a i x) (retainedIndices v l)).prod)]
  exact Finset.prod_nonneg (fun v _ => hm (retainedIndices v l))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.GibbsCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open MeasureTheory
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem doubled_covariance_identity {w f g : X → ℝ}
    (hw : Continuous w) (hf : Continuous f) (hg : Continuous g) :
    (∫ p : X×X,w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2) ∂μ.prod μ) =
      2*((∫ x,w x ∂μ)*(∫ x,w x*(f x*g x) ∂μ)-
        (∫ x,w x*f x ∂μ)*(∫ x,w x*g x ∂μ)) := by
  have he : (fun p : X×X => w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2)) =
      (fun p : X×X => (w p.1*(f p.1*g p.1)*w p.2+w p.1*(w p.2*(f p.2*g p.2)))-
        (w p.1*f p.1*(w p.2*g p.2)+w p.1*g p.1*(w p.2*f p.2))) := by
    funext p; ring
  rw [he,integral_sub (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop)),
    integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop)),
    integral_add (compact_integrable (by fun_prop)) (compact_integrable (by fun_prop))]
  rw [integral_prod_mul (fun x => w x*(f x*g x)) w,
    integral_prod_mul w (fun x => w x*(f x*g x)),
    integral_prod_mul (fun x => w x*f x) (fun x => w x*g x),
    integral_prod_mul (fun x => w x*g x) (fun x => w x*f x)]
  ring

theorem covariance_nonneg_of_doubled {w f g : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) (hf : Continuous f) (hg : Continuous g)
    (h : 0≤∫ p : X×X,w p.1*w p.2*(f p.1-f p.2)*(g p.1-g p.2) ∂μ.prod μ) :
    weightedMean μ w f*weightedMean μ w g≤weightedMean μ w (fun x => f x*g x) := by
  rw [doubled_covariance_identity μ hw hf hg] at h
  apply (weightedMean_inequality_iff hw hp).2
  linarith

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.IsingPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

theorem signValue_product_moment (l : List Unit) :
    0≤∫ t,(l.map (fun _ => signValue t)).prod ∂signLaw := by
  have he (t : Bool) : (l.map (fun _ => signValue t)).prod=signValue t^l.length := by simp
  simp_rw [he]
  simp only [signLaw,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
    smul_eq_mul,integral_count,Fintype.sum_bool,signValue,Bool.false_eq_true,ite_false,ite_true,
    one_pow]
  have hh : -1≤(-1 : ℝ)^l.length := by
    simpa only [abs_pow,abs_neg,abs_one,one_pow] using neg_abs_le ((-1 : ℝ)^l.length)
  norm_num at *
  linarith

variable {V : Type uV} {E : Type uE} [Fintype V]

theorem ising_reference_mean_nonneg (left right : E → V) (e : E) :
    0≤∫ s,isingEnergy left right e s ∂isingReference := by
  classical
  have hh := independent_moments_nonneg (V := V) signLaw (fun (_ : Unit) t => signValue t)
    signValue_product_moment [(left e,()),(right e,())]
  simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,isingEnergy,
    isingReference] using hh

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.TorusDouble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
namespace ClassicalON

variable {V : Type uV} [Fintype V]

omit [Fintype V] in
theorem torusDouble_continuous : Continuous (torusDouble (V := V)) := by
  change Continuous (fun p : (V → PlanarAngle)×(V → PlanarAngle) => (p.1+p.2,p.1-p.2))
  fun_prop

omit [Fintype V] in
theorem torusDouble_surjective : Function.Surjective (torusDouble (V := V)) := by
  intro p
  let v := DivisibleBy.div (p.1+p.2) (2 : ℤ)
  have hv : (2 : ℤ) • v=p.1+p.2 := DivisibleBy.div_cancel _ (by norm_num)
  refine ⟨(v,p.1-v),?_⟩
  apply Prod.ext
  · change v+(p.1-v)=p.1; abel
  · change v-(p.1-v)=p.2
    rw [show v-(p.1-v)=(2 : ℤ) • v-p.1 by simp only [two_zsmul]; abel,hv]
    abel

theorem torusDouble_preserves : MeasurePreserving (torusDouble (V := V))
    ((planarReference (V := V)).prod (planarReference (V := V)))
    ((planarReference (V := V)).prod (planarReference (V := V))) :=
  by
    classical
    let : BorelSpace (V → PlanarAngle) := Pi.borelSpace
    let : SFinite (planarReference (V := V)) := inferInstance
    let : MeasurableAdd (V → PlanarAngle) := inferInstance
    let : ((planarReference (V := V)).prod (planarReference (V := V))).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure _ _
    exact AddMonoidHom.measurePreserving torusDouble_continuous torusDouble_surjective rfl

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PlanarAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
namespace ClassicalON

open scoped ComplexConjugate

theorem continuous_planarCos : Continuous planarCos := by
  unfold planarCos planarCharacter
  exact Complex.continuous_re.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)

theorem continuous_planarSin : Continuous planarSin := by
  unfold planarSin planarCharacter
  exact Complex.continuous_im.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)

theorem planarCharacter_add (x y : PlanarAngle) :
    planarCharacter (x+y)=planarCharacter x*planarCharacter y := by
  simp only [planarCharacter,AddCircle.toCircle_add,Circle.coe_mul]

theorem planarCharacter_neg (x : PlanarAngle) :
    planarCharacter (-x)=conj (planarCharacter x) := by
  simp only [planarCharacter,AddCircle.toCircle_neg,Circle.coe_inv_eq_conj]

theorem planarCos_add_sub (x y : PlanarAngle) :
    planarCos (x+y)+planarCos (x-y)=2*planarCos x*planarCos y := by
  simp only [planarCos,sub_eq_add_neg,planarCharacter_add,planarCharacter_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem planarCos_subtraction (x y : PlanarAngle) :
    planarCos (x+y)-planarCos (x-y)= -2*planarSin x*planarSin y := by
  simp only [planarCos,planarSin,sub_eq_add_neg,planarCharacter_add,planarCharacter_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

variable {V : Type uV} {E : Type uE}

theorem continuous_planarEnergy (left right : E → V) (e : E) :
    Continuous (planarEnergy left right e) := by
  exact continuous_planarCos.comp ((continuous_apply _).sub (continuous_apply _))

theorem continuous_planarSine (left right : E → V) (e : E) :
    Continuous (planarSine left right e) := by
  exact continuous_planarSin.comp ((continuous_apply _).sub (continuous_apply _))

theorem planarEnergy_double_sum (left right : E → V) (e : E)
    (p : (V → PlanarAngle)×(V → PlanarAngle)) :
    planarEnergy left right e (torusDouble p).1+planarEnergy left right e (torusDouble p).2=
      2*planarEnergy left right e p.1*planarEnergy left right e p.2 := by
  change planarCos ((p.1+p.2) (left e)-(p.1+p.2) (right e))+
    planarCos ((p.1-p.2) (left e)-(p.1-p.2) (right e))=_
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [show p.1 (left e)+p.2 (left e)-(p.1 (right e)+p.2 (right e))=
    (p.1 (left e)-p.1 (right e))+(p.2 (left e)-p.2 (right e)) by abel,
    show p.1 (left e)-p.2 (left e)-(p.1 (right e)-p.2 (right e))=
    (p.1 (left e)-p.1 (right e))-(p.2 (left e)-p.2 (right e)) by abel]
  exact planarCos_add_sub _ _

theorem planarEnergy_double_sub (left right : E → V) (e : E)
    (p : (V → PlanarAngle)×(V → PlanarAngle)) :
    planarEnergy left right e (torusDouble p).1-planarEnergy left right e (torusDouble p).2=
      -2*planarSine left right e p.1*planarSine left right e p.2 := by
  change planarCos ((p.1+p.2) (left e)-(p.1+p.2) (right e))-
    planarCos ((p.1-p.2) (left e)-(p.1-p.2) (right e))=_
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [show p.1 (left e)+p.2 (left e)-(p.1 (right e)+p.2 (right e))=
    (p.1 (left e)-p.1 (right e))+(p.2 (left e)-p.2 (right e)) by abel,
    show p.1 (left e)-p.2 (left e)-(p.1 (right e)-p.2 (right e))=
    (p.1 (left e)-p.1 (right e))-(p.2 (left e)-p.2 (right e)) by abel]
  exact planarCos_subtraction _ _

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PositiveKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

theorem exp_gram_integral_nonneg {X : Type uX} {E : Type uE} [Fintype E]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} {a : E → X → ℝ} (hf : Continuous f) (ha : ∀ e,Continuous (a e))
    (b : E → ℝ) (hb : ∀ e,0≤b e) :
    0≤∫ p : X×X,f p.1*f p.2*Real.exp (∑ e,b e*(a e p.1*a e p.2)) ∂μ.prod μ := by
  apply integral_mul_sum_exp_nonneg (μ.prod μ) (by fun_prop)
    (a := fun e p => a e p.1*a e p.2) (fun e => by fun_prop) b hb
  intro k p
  have he : (fun z : X×X => f z.1*f z.2*∏ i,a (p i) z.1*a (p i) z.2) =
      (fun z : X×X => (f z.1*∏ i,a (p i) z.1)*(f z.2*∏ i,a (p i) z.2)) := by
    funext z; rw [Finset.prod_mul_distrib]; ring
  rw [he,integral_prod_mul (fun x => f x*∏ i,a (p i) x) (fun x => f x*∏ i,a (p i) x)]
  exact mul_self_nonneg _

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PlanarGinibre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem continuous_planarHamiltonian (left right : E → V) (b : E → ℝ) :
    Continuous (planarHamiltonian left right b) := by
  exact continuous_finsetSum _ (fun e _ => continuous_const.mul (continuous_planarEnergy _ _ e))

omit [Fintype V] in
theorem planarHamiltonian_double (left right : E → V) (b : E → ℝ)
    (p : (V → PlanarAngle)×(V → PlanarAngle)) :
    planarHamiltonian left right b (torusDouble p).1+
      planarHamiltonian left right b (torusDouble p).2 =
      ∑ e,(2*b e)*(planarEnergy left right e p.1*planarEnergy left right e p.2) := by
  simp only [planarHamiltonian,← Finset.sum_add_distrib,← mul_add,
    planarEnergy_double_sum]
  apply Finset.sum_congr rfl; intro e _; ring

theorem planar_edge_covariance_nonneg (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (e f : E) :
    planarMean left right b (planarEnergy left right e)*
      planarMean left right b (planarEnergy left right f) ≤
    planarMean left right b (fun θ => planarEnergy left right e θ*planarEnergy left right f θ) := by
  classical
  let T := planarEnergy left right
  let S := planarSine left right
  let H := planarHamiltonian left right b
  have hT : ∀ g,Continuous (T g) := continuous_planarEnergy _ _
  have hS : ∀ g,Continuous (S g) := continuous_planarSine _ _
  have hH : Continuous H := continuous_planarHamiltonian _ _ _
  let F : ((V → PlanarAngle)×(V → PlanarAngle)) → ℝ := fun p =>
    Real.exp (H p.1)*Real.exp (H p.2)*(T e p.1-T e p.2)*(T f p.1-T f p.2)
  have hF : Continuous F := by unfold F; fun_prop
  apply covariance_nonneg_of_doubled planarReference hH.rexp
    (fun θ => Real.exp_pos (H θ)) (hT e) (hT f)
  change 0≤∫ p,F p ∂(planarReference (V := V)).prod planarReference
  have hi : (∫ p,F (torusDouble p) ∂(planarReference (V := V)).prod planarReference)=
      ∫ p,F p ∂(planarReference (V := V)).prod planarReference := by
    have hm := integral_map (μ := (planarReference (V := V)).prod planarReference)
      (torusDouble_preserves (V := V)).measurable.aemeasurable
      hF.aestronglyMeasurable
    rw [(torusDouble_preserves (V := V)).map_eq] at hm
    exact hm.symm
  rw [← hi]
  have hp : (fun p => F (torusDouble p))=(fun p =>
      4*((S e p.1*S f p.1)*(S e p.2*S f p.2)*
        Real.exp (∑ g,(2*b g)*(T g p.1*T g p.2)))) := by
    funext p
    dsimp only [F,H,T,S]
    rw [← Real.exp_add,planarHamiltonian_double,
      planarEnergy_double_sub,planarEnergy_double_sub]
    ring
  rw [hp,integral_const_mul]
  apply mul_nonneg (by norm_num)
  exact exp_gram_integral_nonneg planarReference ((hS e).mul (hS f)) hT
    (fun g => 2*b g) (fun g => mul_nonneg (by norm_num) (hb g))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PlanarPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
namespace ClassicalON

theorem planar_antipode_exists : ∃ t : PlanarAngle,planarCharacter t= -1 := by
  let h := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  refine ⟨h.symm (-1),?_⟩
  change (AddCircle.toCircle (h.symm (-1)) : ℂ)= -1
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  change (h (h.symm (-1)) : ℂ)= -1
  simp

theorem planarCos_add_antipode {s : PlanarAngle} (hs : planarCharacter s= -1) (t : PlanarAngle) :
    planarCos (s+t)= -planarCos t := by
  simp [planarCos,planarCharacter_add,hs]

variable {V : Type uV} {E : Type uE} [Fintype V]

theorem planar_reference_mean_nonneg (left right : E → V) (e : E) :
    0≤∫ θ : V → PlanarAngle,planarEnergy left right e θ ∂planarReference := by
  classical
  by_cases h : left e=right e
  · simp [planarEnergy,h,planarCos,planarCharacter]
  obtain ⟨t,ht⟩ := planar_antipode_exists
  let v : V → PlanarAngle := Function.update (fun _ => 0) (left e) t
  have he (θ : V → PlanarAngle) :
      planarEnergy left right e (v+θ)= -planarEnergy left right e θ := by
    unfold planarEnergy
    have hv : (v+θ) (left e)-(v+θ) (right e)=t+(θ (left e)-θ (right e)) := by
      simp only [Pi.add_apply,v,Function.update_self,Function.update_of_ne (Ne.symm h),zero_add]
      abel
    rw [hv,planarCos_add_antipode ht]
  have hh := integral_add_left_eq_self (μ := planarReference) (planarEnergy left right e) v
  simp_rw [he] at hh
  rw [integral_neg] at hh
  linarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
namespace ClassicalON

theorem continuous_transverseAmplitude : Continuous transverseAmplitude := by
  unfold transverseAmplitude; fun_prop

theorem transverseAmplitude_nonneg (r : Amplitude) : 0 ≤ transverseAmplitude r := Real.sqrt_nonneg _

theorem transverseAmplitude_antitone : Antitone transverseAmplitude := by
  intro r s hrs
  apply Real.sqrt_le_sqrt
  have hr := r.property.1
  have hs := s.property.1
  change (r : ℝ) ≤ s at hrs
  nlinarith

theorem transverseAmplitude_inf (r s : Amplitude) :
    transverseAmplitude (r⊓s)=max (transverseAmplitude r) (transverseAmplitude s) := by
  rcases le_total r s with h | h
  · rw [inf_eq_left.mpr h,max_eq_left (transverseAmplitude_antitone h)]
  · rw [inf_eq_right.mpr h,max_eq_right (transverseAmplitude_antitone h)]

theorem transverseAmplitude_sup (r s : Amplitude) :
    transverseAmplitude (r⊔s)=min (transverseAmplitude r) (transverseAmplitude s) := by
  rcases le_total r s with h | h
  · rw [sup_eq_right.mpr h,min_eq_right (transverseAmplitude_antitone h)]
  · rw [sup_eq_left.mpr h,min_eq_left (transverseAmplitude_antitone h)]

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem isingAmplitudePartition_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0 < isingAmplitudePartition left right b r :=
  amplitudePartition_pos _ _ _ _ _ (fun _ => continuous_of_discreteTopology) _

theorem planarAmplitudePartition_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0<planarAmplitudePartition left right b r :=
  amplitudePartition_pos _ _ _ _ _ (continuous_planarEnergy _ _) _

theorem continuous_isingAmplitudePartition (left right : E → V) (b : E → ℝ) :
    Continuous (isingAmplitudePartition left right b) := by
  apply (continuous_amplitudePartition isingReference (isingEnergy left right) left right b
    (fun _ => continuous_of_discreteTopology)).comp
  fun_prop

theorem continuous_planarAmplitudePartition (left right : E → V) (b : E → ℝ) :
    Continuous (planarAmplitudePartition left right b) := by
  apply (continuous_amplitudePartition planarReference (planarEnergy left right) left right b
    (continuous_planarEnergy _ _)).comp
  exact continuous_pi (fun v => continuous_transverseAmplitude.comp (continuous_apply v))

theorem amplitudeDensity_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0<amplitudeDensity left right b r :=
  mul_pos (isingAmplitudePartition_pos _ _ _ _) (planarAmplitudePartition_pos _ _ _ _)

theorem continuous_amplitudeDensity (left right : E → V) (b : E → ℝ) :
    Continuous (amplitudeDensity left right b) :=
  (continuous_isingAmplitudePartition _ _ _).mul (continuous_planarAmplitudePartition _ _ _)

theorem isingAmplitudePartition_logSupermodular (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) : LogSupermodular (isingAmplitudePartition left right b) := by
  intro r s
  exact amplitudePartition_supermodular isingReference (isingEnergy left right) left right b
    (fun _ => continuous_of_discreteTopology) (ising_edge_covariance_nonneg left right)
    (ising_reference_mean_nonneg left right) hb (fun v => (r v).property.1) (fun v => (s v).property.1)

theorem planarAmplitudePartition_logSupermodular (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) : LogSupermodular (planarAmplitudePartition left right b) := by
  intro r s
  have hh := amplitudePartition_supermodular planarReference (planarEnergy left right) left right b
    (continuous_planarEnergy _ _) (planar_edge_covariance_nonneg left right)
    (planar_reference_mean_nonneg left right) hb
    (fun v => transverseAmplitude_nonneg (r v)) (fun v => transverseAmplitude_nonneg (s v))
  have hmin : (fun v => transverseAmplitude ((r⊓s) v))=
      ((fun v => transverseAmplitude (r v))⊔(fun v => transverseAmplitude (s v))) := by
    funext v; exact transverseAmplitude_inf _ _
  have hmax : (fun v => transverseAmplitude ((r⊔s) v))=
      ((fun v => transverseAmplitude (r v))⊓(fun v => transverseAmplitude (s v))) := by
    funext v; exact transverseAmplitude_sup _ _
  unfold planarAmplitudePartition
  rw [hmin,hmax]
  simpa only [mul_comm] using hh

theorem amplitudeDensity_logSupermodular (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) : LogSupermodular (amplitudeDensity left right b) := by
  intro r s
  have hi := isingAmplitudePartition_logSupermodular left right b hb r s
  have hp := planarAmplitudePartition_logSupermodular left right b hb r s
  have hh := mul_le_mul hi hp
    (mul_nonneg (planarAmplitudePartition_pos _ _ _ _).le (planarAmplitudePartition_pos _ _ _ _).le)
    (mul_nonneg (isingAmplitudePartition_pos _ _ _ _).le (isingAmplitudePartition_pos _ _ _ _).le)
  unfold amplitudeDensity
  nlinarith only [hh]

theorem amplitude_associated_any (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e) :
    ContinuousAssociated (Measure.pi (fun _ : V => μ)) (amplitudeDensity left right b) :=
  continuousFKG_pi μ _ (continuous_amplitudeDensity _ _ _)
    (amplitudeDensity_pos _ _ _) (amplitudeDensity_logSupermodular _ _ _ hb)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ClassicalON

theorem planarCos_add (θ φ : PlanarAngle) :
    planarCos (θ+φ)=planarCos θ*planarCos φ-planarSin θ*planarSin φ := by
  simp [planarCos,planarSin,planarCharacter_add,Complex.mul_re]

theorem planarSin_add (θ φ : PlanarAngle) :
    planarSin (θ+φ)=planarSin θ*planarCos φ+planarCos θ*planarSin φ := by
  simp [planarCos,planarSin,planarCharacter_add,Complex.mul_im,add_comm]

theorem continuous_cylindricalSpin :
    Continuous (fun p : Amplitude×Bool×PlanarAngle => cylindricalSpin p.1 p.2.1 p.2.2) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Amplitude×Bool×PlanarAngle => (p.1:ℝ)*signValue p.2.1)
    exact continuous_fst.subtype_val.mul ((show Continuous signValue from continuous_of_discreteTopology).comp (continuous_fst.comp continuous_snd))
  · exact (continuous_transverseAmplitude.comp continuous_fst).mul
      (continuous_planarCos.comp (continuous_snd.comp continuous_snd))
  · exact (continuous_transverseAmplitude.comp continuous_fst).mul
      (continuous_planarSin.comp (continuous_snd.comp continuous_snd))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace ClassicalON

theorem continuous_firstAmplitude : Continuous firstAmplitude := by
  apply Continuous.subtype_mk
  exact ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val).abs

theorem planarAngle_exists (a b : ℝ) (hab : a^2+b^2=1) :
    ∃ θ : PlanarAngle,planarCos θ=a ∧ planarSin θ=b := by
  let z : Circle := ⟨⟨a,b⟩,by
    change (⟨a,b⟩ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [← Complex.normSq_eq_norm_sq]
    simpa [Complex.normSq_apply,pow_two] using hab⟩
  obtain ⟨θ,hθ⟩ := (AddCircle.homeomorphCircle (T := (1:ℝ)) (by norm_num)).surjective z
  rw [AddCircle.homeomorphCircle_apply] at hθ
  exact ⟨θ,congrArg (fun z : Circle => (z:ℂ).re) hθ,congrArg (fun z : Circle => (z:ℂ).im) hθ⟩

theorem cylindricalSpin_surjective_fiber (s : Spin 3) :
    ∃ τ θ,cylindricalSpin (firstAmplitude s) τ θ=s := by
  let r := firstAmplitude s
  let q := transverseAmplitude r
  have hq : q^2=s.val 1^2+s.val 2^2 := by
    have hh := normSq_three s.val
    rw [spin_norm] at hh
    have hr : (r:ℝ)^2=s.val 0^2 := sq_abs _
    dsimp only [q]
    rw [transverseAmplitude_sq,hr]
    nlinarith
  obtain ⟨τ,hτ⟩ : ∃ τ,(r:ℝ)*signValue τ=s.val 0 := by
    by_cases hs : 0 ≤ s.val 0
    · exact ⟨true,by simp [r,firstAmplitude,signValue,abs_of_nonneg hs]⟩
    · exact ⟨false,by simp [r,firstAmplitude,signValue,abs_of_neg (lt_of_not_ge hs)]⟩
  by_cases hzero : q=0
  · refine ⟨τ,0,Subtype.ext ?_⟩
    ext i
    have h1 : s.val 1=0 := by nlinarith [sq_nonneg (s.val 2)]
    have h2 : s.val 2=0 := by nlinarith [sq_nonneg (s.val 1)]
    fin_cases i
    · exact hτ
    · change q*planarCos 0=s.val 1
      rw [hzero,h1,zero_mul]
    · change q*planarSin 0=s.val 2
      rw [hzero,h2,zero_mul]
  · have hab : (s.val 1/q)^2+(s.val 2/q)^2=1 := by
      field_simp
      nlinarith
    obtain ⟨θ,hc,hs⟩ := planarAngle_exists _ _ hab
    refine ⟨τ,θ,Subtype.ext ?_⟩
    ext i
    fin_cases i
    · exact hτ
    · change q*planarCos θ=s.val 1
      rw [hc,mul_div_cancel₀ _ hzero]
    · change q*planarSin θ=s.val 2
      rw [hs,mul_div_cancel₀ _ hzero]

theorem cylinderRotation_cylindricalSpin (τ υ : Bool) (θ φ : PlanarAngle) (r : Amplitude) :
    spinRotation (cylinderRotation τ θ) (cylindricalSpin r υ φ)=
      cylindricalSpin r (τ==υ) (θ+φ) := by
  apply Subtype.ext
  ext i
  fin_cases i
  · change signValue τ*((r:ℝ)*signValue υ)=(r:ℝ)*signValue (τ==υ)
    cases τ <;> cases υ <;> simp [signValue]
  · change planarCos θ*(transverseAmplitude r*planarCos φ)-
      planarSin θ*(transverseAmplitude r*planarSin φ)=transverseAmplitude r*planarCos (θ+φ)
    rw [planarCos_add]; ring
  · change planarSin θ*(transverseAmplitude r*planarCos φ)+
      planarCos θ*(transverseAmplitude r*planarSin φ)=transverseAmplitude r*planarSin (θ+φ)
    rw [planarSin_add]; ring

theorem continuous_cylinderSpinRotation :
    Continuous (fun p : (Bool×PlanarAngle)×Spin 3 =>
      spinRotation (cylinderRotation p.1.1 p.1.2) p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => cylinderLinear p.1.1 p.1.2 p.2.val)
  unfold cylinderLinear
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  have hc : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => planarCos p.1.2) := continuous_planarCos.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => planarSin p.1.2) := continuous_planarSin.comp (continuous_snd.comp continuous_fst)
  have ht : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => signValue p.1.1) := (show Continuous signValue from continuous_of_discreteTopology).comp (continuous_fst.comp continuous_fst)
  have hv (j : Fin 3) : Continuous (fun p : (Bool×PlanarAngle)×Spin 3 => p.2.val j) := (PiLp.continuous_apply 2 _ j).comp (continuous_subtype_val.comp continuous_snd)
  fin_cases i
  · exact ht.mul (hv 0)
  · exact (hc.mul (hv 1)).sub (hs.mul (hv 2))
  · exact (hs.mul (hv 1)).add (hc.mul (hv 2))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ClassicalON

instance sphericalAmplitudeLaw_isProbability : IsProbabilityMeasure sphericalAmplitudeLaw :=
  (Measure.isProbabilityMeasure_map_iff continuous_firstAmplitude.measurable.aemeasurable).2 inferInstance

theorem integral_signLaw (f : Bool → ℝ) : (∫ τ,f τ ∂signLaw)=(f false+f true)/2 := by
  simp [signLaw,integral_smul_measure,integral_count,div_eq_mul_inv]
  ring

theorem integral_cylinderLaw (f : Bool×PlanarAngle → ℝ) (hf : Continuous f) :
    (∫ p,f p ∂cylinderLaw)=((∫ θ,f (false,θ) ∂angleLaw)+(∫ θ,f (true,θ) ∂angleLaw))/2 := by
  rw [cylinderLaw,integral_prod _ (compact_integrable hf),integral_signLaw]

theorem cylinder_orbit_average (f : Spin 3 → ℝ) (hf : Continuous f) (s : Spin 3) :
    (∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw)=
      ∫ p,f (cylindricalSpin (firstAmplitude s) p.1 p.2) ∂cylinderLaw := by
  obtain ⟨υ,φ,hspin⟩ := cylindricalSpin_surjective_fiber s
  have he (p : Bool×PlanarAngle) :
      spinRotation (cylinderRotation p.1 p.2) s=
        cylindricalSpin (firstAmplitude s) (p.1==υ) (p.2+φ) := by
    conv_lhs => rw [← hspin]
    rw [cylinderRotation_cylindricalSpin]
  simp_rw [he]
  have hc : Continuous (fun p : Bool×PlanarAngle => f (cylindricalSpin (firstAmplitude s) p.1 p.2)) :=
    hf.comp (continuous_cylindricalSpin.comp (continuous_const.prodMk continuous_id))
  have hm : Continuous (fun p : Bool×PlanarAngle => (p.1==υ,p.2+φ)) :=
    ((show Continuous (fun τ : Bool => τ==υ) from continuous_of_discreteTopology).comp continuous_fst).prodMk
      (continuous_snd.add continuous_const)
  have hh : Continuous (fun p : Bool×PlanarAngle => f (cylindricalSpin (firstAmplitude s) (p.1==υ) (p.2+φ))) := hc.comp hm
  rw [integral_cylinderLaw _ hh,integral_cylinderLaw _ hc]
  have hshift (τ : Bool) :
      (∫ θ,f (cylindricalSpin (firstAmplitude s) τ (θ+φ)) ∂angleLaw)=
        ∫ θ,f (cylindricalSpin (firstAmplitude s) τ θ) ∂angleLaw :=
    integral_add_right_eq_self (fun θ => f (cylindricalSpin (firstAmplitude s) τ θ)) φ
  cases υ <;> simp only [Bool.false_beq,Bool.true_beq,Bool.not_false,Bool.not_true]
  all_goals rw [hshift,hshift]
  all_goals ring

theorem integral_sphere_orbit (f : Spin 3 → ℝ) (hf : Continuous f) :
    (∫ s,∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw ∂sphereProbability 3)=
      ∫ s,f s ∂sphereProbability 3 := by
  have hcont : Continuous (fun p : Spin 3×(Bool×PlanarAngle) => f (spinRotation (cylinderRotation p.2.1 p.2.2) p.1)) :=
    hf.comp (continuous_cylinderSpinRotation.comp (f := (Prod.swap : Spin 3×(Bool×PlanarAngle) → (Bool×PlanarAngle)×Spin 3)) continuous_swap)
  have hi := integral_integral_swap (μ := sphereProbability 3) (ν := cylinderLaw)
    (f := fun s p => f (spinRotation (cylinderRotation p.1 p.2) s))
    (compact_integrable hcont)
  rw [hi]
  have hp (p : Bool×PlanarAngle) :
      (∫ s,f (spinRotation (cylinderRotation p.1 p.2) s) ∂sphereProbability 3)=∫ s,f s ∂sphereProbability 3 :=
    (spinRotation_preserves_probability _).integral_comp (spinRotation _).measurableEmbedding f
  simp_rw [hp]
  simp

theorem integral_sphere_cylinder (f : Spin 3 → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂sphereProbability 3)=
      ∫ r,∫ p,f (cylindricalSpin r p.1 p.2) ∂cylinderLaw ∂sphericalAmplitudeLaw := by
  have hc : Continuous (fun p : Amplitude×(Bool×PlanarAngle) => f (cylindricalSpin p.1 p.2.1 p.2.2)) :=
    hf.comp continuous_cylindricalSpin
  have hm : Continuous (fun r => ∫ p,f (cylindricalSpin r p.1 p.2) ∂cylinderLaw) :=
    compact_parametric_integral _ hc
  rw [sphericalAmplitudeLaw,integral_map continuous_firstAmplitude.measurable.aemeasurable hm.measurable.aestronglyMeasurable]
  calc
    _ = ∫ s,∫ p,f (spinRotation (cylinderRotation p.1 p.2) s) ∂cylinderLaw ∂sphereProbability 3 :=
      (integral_sphere_orbit f hf).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (cylinder_orbit_average f hf))

theorem cylindricalSpin_preserves : MeasurePreserving
    (fun p : Amplitude×Bool×PlanarAngle => cylindricalSpin p.1 p.2.1 p.2.2)
    (sphericalAmplitudeLaw.prod cylinderLaw) (sphereProbability 3) := by
  refine ⟨continuous_cylindricalSpin.measurable,?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hc : Continuous (fun p : Amplitude×Bool×PlanarAngle => f (cylindricalSpin p.1 p.2.1 p.2.2)) :=
    f.continuous.comp continuous_cylindricalSpin
  rw [integral_map (f := fun x => f x) continuous_cylindricalSpin.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_prod _ (compact_integrable hc)]
  exact (integral_sphere_cylinder f f.continuous).symm

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CylindricalConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem continuous_freeSpinEnergy (n : ℕ) (left right : E → V) (b : E → ℝ) :
    Continuous (freeSpinEnergy n left right b) := by unfold freeSpinEnergy; fun_prop

omit [Fintype V] [Fintype E] in
theorem continuous_cylindricalConfiguration :
    Continuous (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) =>
      cylindricalConfiguration p.1 p.2.1 p.2.2) := by
  apply continuous_pi
  intro v
  exact continuous_cylindricalSpin.comp
    (f := fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) => (p.1 v,p.2.1 v,p.2.2 v))
    (((continuous_apply v).comp continuous_fst).prodMk
      (((continuous_apply v).comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_apply v).comp (continuous_snd.comp continuous_snd))))

omit [Fintype E] in
theorem cylindricalConfiguration_preserves : MeasurePreserving
    (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) => cylindricalConfiguration p.1 p.2.1 p.2.2)
    ((Measure.pi fun _ : V => sphericalAmplitudeLaw).prod ((isingReference (V := V)).prod planarReference))
    (freeSpinReference 3) := by
  let A := MeasurableEquiv.arrowProdEquivProdArrow Amplitude (Bool×PlanarAngle) V
  let B := MeasurableEquiv.arrowProdEquivProdArrow Bool PlanarAngle V
  have hA := (measurePreserving_arrowProdEquivProdArrow Amplitude (Bool×PlanarAngle) V
    (fun _ => sphericalAmplitudeLaw) (fun _ => cylinderLaw)).symm A
  have hB := (measurePreserving_arrowProdEquivProdArrow Bool PlanarAngle V
    (fun _ => signLaw) (fun _ => angleLaw)).symm B
  have h1 := (MeasurePreserving.id (Measure.pi fun _ : V => sphericalAmplitudeLaw)).prod hB
  have h2 := hA.comp h1
  have h3 := measurePreserving_pi (fun _ : V => sphericalAmplitudeLaw.prod cylinderLaw)
    (fun _ => sphereProbability 3) (fun _ => cylindricalSpin_preserves)
  exact h3.comp h2

omit [Fintype E] in
theorem integral_freeSpinReference_cylinder (f : (V → Spin 3) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂freeSpinReference 3)=
      ∫ r,∫ τ,∫ θ,f (cylindricalConfiguration r τ θ) ∂planarReference ∂isingReference
        ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  let : BorelSpace ((V → Amplitude) × (V → Bool) × (V → PlanarAngle)) := Prod.borelSpace
  have hc : Continuous (fun p : (V → Amplitude)×(V → Bool)×(V → PlanarAngle) =>
      f (cylindricalConfiguration p.1 p.2.1 p.2.2)) := hf.comp continuous_cylindricalConfiguration
  rw [← cylindricalConfiguration_preserves.map_eq,
    integral_map continuous_cylindricalConfiguration.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ (compact_integrable hc)]
  apply integral_congr_ae
  filter_upwards with r
  have hr : Continuous (fun p : (V → Bool)×(V → PlanarAngle) => f (cylindricalConfiguration r p.1 p.2)) :=
    hc.comp (continuous_const.prodMk continuous_id)
  exact integral_prod _ (compact_integrable hr)

omit [Fintype V] [Fintype E] in
theorem cylindricalSpin_inner (r q : Amplitude) (τ υ : Bool) (θ φ : PlanarAngle) :
    ⟪(cylindricalSpin r τ θ).val,(cylindricalSpin q υ φ).val⟫_ℝ=
      (r:ℝ)*(q:ℝ)*(signValue τ*signValue υ)+
        transverseAmplitude r*transverseAmplitude q*planarCos (θ-φ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,Fin.sum_univ_succ,Fin.isValue,cylindricalSpin,
    WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_succ,star_trivial,Finset.univ_eq_empty,
    Finset.sum_empty,add_zero]
  simp only [planarCos,planarSin,sub_eq_add_neg,planarCharacter_add,planarCharacter_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

omit [Fintype V] in
theorem cylindricalConfiguration_energy (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) :
    freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ)=
      edgeHamiltonian (isingEnergy left right) (amplitudeCoupling left right b (fun v => (r v:ℝ))) τ+
      edgeHamiltonian (planarEnergy left right) (amplitudeCoupling left right b (fun v => transverseAmplitude (r v))) θ := by
  unfold freeSpinEnergy edgeHamiltonian cylindricalConfiguration
  simp_rw [cylindricalSpin_inner]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold amplitudeCoupling isingEnergy planarEnergy
  ring

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.UpperEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology Classical
namespace ClassicalON

instance sphericalAmplitudeLaw_isOpenPos : sphericalAmplitudeLaw.IsOpenPosMeasure :=
  continuous_firstAmplitude.isOpenPosMeasure_map (fun r =>
    ⟨cylindricalSpin r true 0,firstAmplitude_cylindricalSpin r true 0⟩)

variable {I : Type uI} [Fintype I]

theorem continuous_upperTent (δ : ℝ) : Continuous (upperTent (I := I) δ) := by
  unfold upperTent
  fun_prop

theorem upperTent_nonneg (δ : ℝ) (r : I → Amplitude) : 0≤upperTent δ r :=
  Finset.prod_nonneg (fun _ _ => le_max_left _ _)

theorem upperTent_monotone (δ : ℝ) : Monotone (upperTent (I := I) δ) := by
  intro r s hrs
  apply Finset.prod_le_prod (fun _ _ => le_max_left _ _)
  intro i _
  exact max_le_max le_rfl (sub_le_sub_right (show (r i:ℝ)≤(s i:ℝ) from hrs i) _)

theorem upperTent_top_pos {δ : ℝ} (hδ : 0<δ) : 0<upperTent (I := I) δ ⊤ := by
  apply Finset.prod_pos
  intro i _
  simpa using (lt_max_of_lt_right hδ : (0:ℝ) < max 0 δ)

theorem upperTent_support_ball {δ : ℝ} (hδ : 0<δ) {r : I → Amplitude}
    (hr : upperTent δ r≠0) : dist r ⊤<δ := by
  apply (dist_pi_lt_iff hδ).2
  intro i
  have hi : max 0 ((r i:ℝ)-(1-δ))≠0 := by
    intro he
    exact hr (Finset.prod_eq_zero (Finset.mem_univ i) he)
  have hip : 0<(r i:ℝ)-(1-δ) := by
    by_contra! hn
    exact hi (max_eq_left hn)
  change dist (r i:ℝ) 1<δ
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (r i).property.2)]
  linarith

theorem upperEndpoint_nonneg (μ : Measure (I → Amplitude)) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] {F : (I → Amplitude) → ℝ} (hF : Continuous F)
    (ht : ∀ h : (I → Amplitude) → ℝ,Continuous h → (∀ r,0≤h r) → Monotone h →
      0≤∫ r,h r*F r ∂μ) : 0≤F ⊤ := by
  by_contra! hneg
  obtain ⟨δ,hδ,hd⟩ := (Metric.continuousAt_iff.mp hF.continuousAt) (-F ⊤/2) (by linarith)
  let h := upperTent (I := I) δ
  have hc : Continuous (fun r => -(h r*F r)) := ((continuous_upperTent δ).mul hF).neg
  have hp : ∀ r,0≤ -(h r*F r) := by
    intro r
    by_cases hr : h r=0
    · simp [hr]
    · have hx := hd (upperTent_support_ball hδ hr)
      rw [Real.dist_eq,abs_lt] at hx
      have hfn : F r<0 := by linarith
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (upperTent_nonneg δ r) hfn.le)
  have hs : (Function.support (fun r => -(h r*F r))).Nonempty := by
    refine ⟨⊤,?_⟩
    exact neg_ne_zero.mpr (mul_ne_zero (upperTent_top_pos hδ).ne' hneg.ne)
  have hi : 0<∫ r,-(h r*F r) ∂μ :=
    (integral_pos_iff_support_of_nonneg hp (compact_integrable hc)).2
      (hc.isOpen_support.measure_pos μ hs)
  rw [integral_neg] at hi
  have hn := ht h (continuous_upperTent δ) (upperTent_nonneg δ) (upperTent_monotone δ)
  linarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AmplitudeSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology Classical
namespace ClassicalON

variable {V : Type uV} [Fintype V]

omit [Fintype V] in
theorem continuous_glueAmplitude (B : Set V) :
    Continuous (fun p : (B → Amplitude)×(↥(Bᶜ) → Amplitude) => glueAmplitude B p.1 p.2) :=
  (Homeomorph.piEquivPiSubtypeProd (·∈B) (fun _ : V => Amplitude)).symm.continuous

theorem integral_amplitude_split (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (B : Set V) (F : (V → Amplitude) → ℝ) (hF : Continuous F) :
    (∫ r,F r ∂Measure.pi (fun _ : V => μ))=
      ∫ a,∫ r,F (glueAmplitude B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ)
        ∂Measure.pi (fun _ : B => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => Amplitude) (·∈B)
  have hp := (measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) (·∈B)).symm e
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod _ (compact_integrable (hF.comp (continuous_glueAmplitude B)))

theorem pinEndpoint_nonneg (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (B : Set V) {F : (V → Amplitude) → ℝ} (hF : Continuous F)
    (ht : ∀ h : (B → Amplitude) → ℝ,Continuous h → (∀ a,0≤h a) → Monotone h →
      0≤∫ r,h (fun v : B => r v)*F r ∂Measure.pi (fun _ : V => μ)) :
    0≤∫ r,F (glueAmplitude B ⊤ r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ) := by
  have hc : Continuous (fun a => ∫ r,F (glueAmplitude B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ)) :=
    compact_parametric_integral _ (hF.comp (continuous_glueAmplitude B))
  apply upperEndpoint_nonneg (Measure.pi (fun _ : B => μ)) hc
  intro h hh hn hm
  have hh' : Continuous (fun r : V → Amplitude => h (fun v : B => r v)) := by
    apply hh.comp
    exact continuous_pi (fun v => continuous_apply v.val)
  have hs := integral_amplitude_split μ B (fun r => h (fun v : B => r v)*F r) (hh'.mul hF)
  have he : (fun a => ∫ r,h (fun v : B => glueAmplitude B a r v)*F (glueAmplitude B a r)
      ∂Measure.pi (fun _ : ↥(Bᶜ) => μ))=
      (fun a => h a*(∫ r,F (glueAmplitude B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ))) := by
    funext a
    simp only [glueAmplitude_in]
    exact integral_const_mul _ _
  rw [he] at hs
  rw [← hs]
  exact ht h hh hn hm

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {A : Type uA} [Fintype V]

omit [Fintype V] in
theorem continuous_glueFamily [TopologicalSpace A] (B : Set V) :
    Continuous (fun p : (B → A)×(↥(Bᶜ) → A) => glueFamily B p.1 p.2) :=
  (Homeomorph.piEquivPiSubtypeProd (·∈B) (fun _ : V => A)).symm.continuous

theorem sum_glueFamily [Fintype A] (B : Set V) (a : B → A) (f : (V → A) → ℝ) :
    (∑ r : ↥(Bᶜ) → A,f (glueFamily B a r))=
      ∑ s : V → A,if (fun v : B => s v)=a then f s else 0 := by
  let e := Equiv.piEquivPiSubtypeProd (·∈B) (fun _ : V => A)
  rw [← e.symm.sum_comp (fun s => if (fun v : B => s v)=a then f s else 0)]
  rw [Fintype.sum_prod_type]
  have he (p : B → A) (r : ↥(Bᶜ) → A) : (fun v : B => (e.symm (p,r)) v)=p := by
    funext v
    exact glueFamily_in B p r v
  simp_rw [he]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

section Measure
variable [MeasurableSpace A] [MeasurableSingletonClass A]

theorem measure_pi_dirac (a : V → A) : (Measure.pi (fun v => Measure.dirac (a v)))=Measure.dirac a := by
  apply Measure.pi_eq
  intro s hs
  by_cases h : ∀ v,a v∈s v
  · simp [h]
  · obtain ⟨v,hv⟩ := not_forall.mp h
    have hn : a∉Set.pi Set.univ s := by
      intro ha
      exact hv (ha v (Set.mem_univ v))
    rw [Measure.dirac_apply,Set.indicator_of_notMem hn]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv]

variable [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [BorelSpace A]

omit [T2Space A] in
theorem integral_pinProductMeasure (μ : Measure A) [IsProbabilityMeasure μ]
    (B : Set V) (a : B → A) (f : (V → A) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂pinProductMeasure μ B a)=
      ∫ r,f (glueFamily B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ) := by
  let ν (v : V) : Measure A := if h : v∈B then Measure.dirac (a ⟨v,h⟩) else μ
  have : ∀ v,IsProbabilityMeasure (ν v) := by intro v; dsimp [ν]; split <;> infer_instance
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => A) (·∈B)
  have hp := (measurePreserving_piEquivPiSubtypeProd ν (·∈B)).symm e
  have hB : (fun v : B => ν v)=(fun v : B => Measure.dirac (a v)) := by funext v; simp [ν,v.property]
  have hC : (fun v : ↥(Bᶜ) => ν v)=(fun _ : ↥(Bᶜ) => μ) := by
    funext v; simp [ν,show v.val∉B from v.property]
  change (∫ s,f s ∂Measure.pi ν)=_
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]
  change (∫ p : (B → A)×(↥(Bᶜ) → A), f (glueFamily B p.1 p.2)
    ∂(Measure.pi (fun v : B => ν v)).prod (Measure.pi (fun v : ↥(Bᶜ) => ν v)))=_
  rw [hB,hC,measure_pi_dirac]
  have hi : Integrable (fun p : (B → A)×(↥(Bᶜ) → A) => f (glueFamily B p.1 p.2))
      ((Measure.dirac a).prod (Measure.pi (fun _ : ↥(Bᶜ) => μ))) :=
    compact_integrable (hf.comp (continuous_glueFamily B))
  rw [integral_prod _ hi]
  rw [integral_dirac]

omit [MeasurableSingletonClass A] in
theorem integral_pi_split (μ : Measure A) [IsProbabilityMeasure μ]
    (B : Set V) (f : (V → A) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂Measure.pi (fun _ : V => μ))=
      ∫ a,∫ r,f (glueFamily B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ)
        ∂Measure.pi (fun _ : B => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => A) (·∈B)
  have hp := (measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) (·∈B)).symm e
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ (compact_integrable (hf.comp (continuous_glueFamily B)))

omit [MeasurableSingletonClass A] in
theorem integral_pi_restriction (μ : Measure A) [IsProbabilityMeasure μ]
    (B : Set V) (f : (↥(Bᶜ) → A) → ℝ) (hf : Continuous f) :
    (∫ s,f (fun v : ↥(Bᶜ) => s v) ∂Measure.pi (fun _ : V => μ))=
      ∫ r,f r ∂Measure.pi (fun _ : ↥(Bᶜ) => μ) := by
  have hc : Continuous (fun s : V → A => f (fun v : ↥(Bᶜ) => s v)) :=
    hf.comp (continuous_pi (fun v => continuous_apply v.val))
  rw [integral_pi_split μ B _ hc]
  simp only [glueFamily_out]
  simp

end Measure
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem cylindricalSpin_top (τ : Bool) (θ : PlanarAngle) : cylindricalSpin ⊤ τ θ=poleSpin τ := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [poleSpin,cylindricalSpin,transverseAmplitude]

omit [Fintype E] in
theorem poleSystem_reference (left right : E → V) (b : E → ℝ) (B : Set V) (t : B → Bool) :
    (poleSystem left right b B t).reference=pinProductMeasure (sphereProbability 3) B (fun v => poleSpin (t v)) := by
  unfold SpinSystem.reference poleSystem pinProductMeasure
  congr 1
  funext v
  by_cases h : v∈B <;> simp [siteReference,h]

omit [Fintype V] [Fintype E] in
theorem glue_cylindrical (B : Set V) (t : B → Bool) (r : ↥(Bᶜ) → Amplitude)
    (τ : ↥(Bᶜ) → Bool) (θ : V → PlanarAngle) :
    glueFamily B (fun v => poleSpin (t v))
      (cylindricalConfiguration r τ (fun v : ↥(Bᶜ) => θ v))=
    cylindricalConfiguration (glueAmplitude B ⊤ r) (glueFamily B t τ) θ := by
  funext v
  by_cases hv : v∈B
  · have h1 := glueFamily_in B (fun v => poleSpin (t v))
       (cylindricalConfiguration r τ (fun v : ↥(Bᶜ) => θ v)) ⟨v,hv⟩
    rw [h1]
    change _=cylindricalSpin (glueAmplitude B ⊤ r (⟨v,hv⟩ : B)) (glueFamily B t τ (⟨v,hv⟩ : B)) (θ v)
    rw [glueAmplitude_in,glueFamily_in]
    exact (cylindricalSpin_top _ _).symm
  · have h1 := glueFamily_out B (fun v => poleSpin (t v))
       (cylindricalConfiguration r τ (fun v : ↥(Bᶜ) => θ v)) ⟨v,hv⟩
    rw [h1]
    change _=cylindricalSpin (glueAmplitude B ⊤ r (⟨v,hv⟩ : ↥(Bᶜ)))
      (glueFamily B t τ (⟨v,hv⟩ : ↥(Bᶜ))) (θ v)
    rw [glueAmplitude_out,glueFamily_out]
    rfl

omit [Fintype E] in
theorem integral_poleSystem_cylinder (left right : E → V) (b : E → ℝ) (B : Set V) (t : B → Bool)
    (f : (V → Spin 3) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂(poleSystem left right b B t).reference)=
      ∫ r,∫ τ,∫ θ,f (cylindricalConfiguration (glueAmplitude B ⊤ r) (glueFamily B t τ) θ)
        ∂planarReference ∂isingReference ∂Measure.pi (fun _ : ↥(Bᶜ) => sphericalAmplitudeLaw) := by
  rw [poleSystem_reference,integral_pinProductMeasure _ _ _ _ hf]
  have hc : Continuous (fun s : ↥(Bᶜ) → Spin 3 => f (glueFamily B (fun v => poleSpin (t v)) s)) :=
    hf.comp ((continuous_glueFamily B).comp (continuous_const.prodMk continuous_id))
  change (∫ s,f (glueFamily B (fun v => poleSpin (t v)) s) ∂freeSpinReference 3)=_
  rw [integral_freeSpinReference_cylinder _ hc]
  apply integral_congr_ae
  filter_upwards with r
  apply integral_congr_ae
  filter_upwards with τ
  have hθ : Continuous (fun θ : ↥(Bᶜ) → PlanarAngle =>
      f (glueFamily B (fun v => poleSpin (t v)) (cylindricalConfiguration r τ θ))) :=
    hc.comp (continuous_cylindricalConfiguration.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
  have he := integral_pi_restriction angleLaw B _ hθ
  change (∫ θ,f (glueFamily B (fun v => poleSpin (t v)) (cylindricalConfiguration r τ θ))
    ∂Measure.pi (fun _ : ↥(Bᶜ) => angleLaw))=_
  rw [← he]
  apply integral_congr_ae
  filter_upwards with θ
  rw [glue_cylindrical]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondSubspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE}

theorem bondSubspace_antitone (left right : E → V) : Antitone (bondSubspace left right) := by
  intro η ξ h s hs e he
  apply hs e
  have hh := h e
  rw [he] at hh
  exact le_antisymm (show ξ e ≤ true from Bool.le_true _) hh

theorem bondSubspace_sup (left right : E → V) (η ξ : E → Bool) :
    bondSubspace left right (η⊔ξ)=bondSubspace left right η⊓bondSubspace left right ξ := by
  apply le_antisymm
  · exact le_inf (bondSubspace_antitone left right le_sup_left) (bondSubspace_antitone left right le_sup_right)
  · intro s hs e he
    have ht : η e=true ∨ ξ e=true := by simpa using he
    rcases ht with ht | ht
    · exact hs.1 e ht
    · exact hs.2 e ht

variable [Fintype V]

theorem bondRank_supermodular (left right : E → V) (η ξ : E → Bool) :
    bondRank left right η+bondRank left right ξ≤
      bondRank left right (η⊓ξ)+bondRank left right (η⊔ξ) := by
  unfold bondRank
  rw [bondSubspace_sup,← Submodule.finrank_sup_add_finrank_inf_eq]
  apply Nat.add_le_add_right
  apply Submodule.finrank_mono
  exact sup_le (bondSubspace_antitone left right inf_le_left) (bondSubspace_antitone left right inf_le_right)

omit [Fintype V] in
theorem clusterWeight_pos (left right : E → V) (η : E → Bool) : 0<clusterWeight left right η := by
  unfold clusterWeight; positivity

theorem clusterWeight_supermodular (left right : E → V) (η ξ : E → Bool) :
    clusterWeight left right η*clusterWeight left right ξ≤
      clusterWeight left right (η⊓ξ)*clusterWeight left right (η⊔ξ) := by
  unfold clusterWeight
  rw [← pow_add,← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (bondRank_supermodular left right η ξ)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uX

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem bondProduct_nonneg {t : E → ℝ} (ht : ∀ e,0 ≤ t e) (η : E → Bool) :
    0 ≤ bondProduct t η := Finset.prod_nonneg fun e _ => by split <;> [exact ht e; exact zero_le_one]

omit [Fintype V] in
theorem bondWeight_nonneg (left right : E → V) {t : E → ℝ} (ht : ∀ e,0 ≤ t e)
    (η : E → Bool) : 0 ≤ bondWeight left right t η :=
  mul_nonneg (clusterWeight_pos _ _ _).le (bondProduct_nonneg ht η)

theorem bondProduct_holley {t s : E → ℝ} (ht : ∀ e,0 ≤ t e) (hts : t ≤ s)
    (η ξ : E → Bool) :
    bondProduct t η*bondProduct s ξ ≤ bondProduct t (η⊓ξ)*bondProduct s (η⊔ξ) := by
  unfold bondProduct
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro e _
    exact mul_nonneg (by split <;> [exact ht e; exact zero_le_one]) (by split <;> [exact le_trans (ht e) (hts e); exact zero_le_one])
  · intro e _
    simp only [Pi.inf_apply,Pi.sup_apply]
    have hh (a b : Bool) : (if a then t e else 1)*(if b then s e else 1) ≤
        (if a⊓b then t e else 1)*(if a⊔b then s e else 1) := by
      cases a <;> cases b <;> simp [hts e]
    exact hh _ _

theorem bondWeight_holley (left right : E → V) {t s : E → ℝ}
    (ht : ∀ e,0 ≤ t e) (hts : t ≤ s) (η ξ : E → Bool) :
    bondWeight left right t η*bondWeight left right s ξ ≤
      bondWeight left right t (η⊓ξ)*bondWeight left right s (η⊔ξ) := by
  unfold bondWeight
  rw [mul_mul_mul_comm,mul_mul_mul_comm (clusterWeight left right (η⊓ξ))]
  exact mul_le_mul (clusterWeight_supermodular _ _ η ξ) (bondProduct_holley ht hts η ξ)
    (mul_nonneg (bondProduct_nonneg ht η) (bondProduct_nonneg (fun e => le_trans (ht e) (hts e)) ξ))
    (mul_nonneg (clusterWeight_pos _ _ _).le (clusterWeight_pos _ _ _).le)

omit [Fintype V] in
theorem bondWeight_sum_pos (left right : E → V) {t : E → ℝ} (ht : ∀ e,0 ≤ t e) :
    0 < ∑ η,bondWeight left right t η := by
  apply Finset.sum_pos' (fun η _ => bondWeight_nonneg left right ht η)
  refine ⟨fun _ => false,Finset.mem_univ _,?_⟩
  simpa [bondWeight,bondProduct] using clusterWeight_pos left right (fun _ => false)

section Finite
variable {X : Type uX} [Fintype X]

theorem finiteMean_nonneg {w f : X → ℝ} (hw : ∀ x,0 ≤ w x) (hf : ∀ x,0 ≤ f x) :
    0 ≤ finiteMean w f :=
  div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)) (Finset.sum_nonneg fun x _ => hw x)

theorem finiteMean_mono {w f g : X → ℝ} (hw : ∀ x,0 ≤ w x) (hf : f ≤ g) :
    finiteMean w f ≤ finiteMean w g := by
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg fun x _ => hw x)
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (hw x)

variable [DistribLattice X]

theorem finiteMean_associated {w f g : X → ℝ} (hw : ∀ x,0 ≤ w x) (hp : 0 < ∑ x,w x)
    (hLS : ∀ x y,w x*w y ≤ w (x⊓y)*w (x⊔y))
    (hf : ∀ x,0 ≤ f x) (hg : ∀ x,0 ≤ g x) (hfm : Monotone f) (hgm : Monotone g) :
    finiteMean w f*finiteMean w g ≤ finiteMean w (fun x => f x*g x) := by
  have hh := fkg f g w hw hf hg hfm hgm hLS
  unfold finiteMean
  rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos hp hp) hp]
  nlinarith

theorem finiteMean_holley {w v f : X → ℝ} (hw : ∀ x,0 ≤ w x) (hv : ∀ x,0 ≤ v x)
    (hp : 0 < ∑ x,w x) (hvp : 0 < ∑ x,v x) (hf : ∀ x,0 ≤ f x) (hfm : Monotone f)
    (hH : ∀ x y,w x*v y ≤ w (x⊓y)*v (x⊔y)) : finiteMean w f ≤ finiteMean v f := by
  have hh := four_functions_theorem_univ v (fun x => w x*f x) w (fun x => v x*f x)
    hv (fun x => mul_nonneg (hw x) (hf x)) hw (fun x => mul_nonneg (hv x) (hf x))
    (fun x y => show v x*(w y*f y) ≤ w (x⊓y)*(v (x⊔y)*f (x⊔y)) from by
      have h := mul_le_mul (hH y x) (hfm (show y ≤ x⊔y from le_sup_right))
        (hf y) (mul_nonneg (hw (y⊓x)) (hv (y⊔x)))
      simpa only [inf_comm,sup_comm,mul_assoc,mul_left_comm] using h)
  unfold finiteMean
  apply (div_le_div_iff₀ hp hvp).2
  nlinarith
end Finite

theorem bondMean_mono (left right : E → V) {t s : E → ℝ}
    (ht : ∀ e,0 ≤ t e) (hts : t ≤ s) {f : (E → Bool) → ℝ}
    (hf : ∀ η,0 ≤ f η) (hfm : Monotone f) :
    finiteMean (bondWeight left right t) f ≤ finiteMean (bondWeight left right s) f :=
  finiteMean_holley (bondWeight_nonneg left right ht)
    (bondWeight_nonneg left right (fun e => le_trans (ht e) (hts e)))
    (bondWeight_sum_pos left right ht) (bondWeight_sum_pos left right (fun e => le_trans (ht e) (hts e)))
    hf hfm (bondWeight_holley left right ht hts)

theorem bondMean_associated (left right : E → V) {t : E → ℝ} (ht : ∀ e,0 ≤ t e)
    {f g : (E → Bool) → ℝ} (hf : ∀ η,0 ≤ f η) (hg : ∀ η,0 ≤ g η)
    (hfm : Monotone f) (hgm : Monotone g) :
    finiteMean (bondWeight left right t) f*finiteMean (bondWeight left right t) g ≤
      finiteMean (bondWeight left right t) (fun η => f η*g η) :=
  finiteMean_associated (bondWeight_nonneg left right ht) (bondWeight_sum_pos left right ht)
    (bondWeight_holley left right ht le_rfl) hf hg hfm hgm

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype E] in
theorem compatibleSigns_card (left right : E → V) (η : E → Bool) :
    Fintype.card (compatibleSigns left right η)=2^bondRank left right η := by
  rw [Fintype.card_congr (compatibleSignsEquiv left right η),Module.card_eq_pow_finrank (K := SignField)]
  simp [bondRank,SignField]

omit [Fintype E] in
theorem compatibleSigns_sum (left right : E → V) (η : E → Bool) :
    (∑ s : V → Bool,if s∈compatibleSigns left right η then (1:ℝ) else 0)=clusterWeight left right η := by
  rw [Finset.sum_boole,← Fintype.card_subtype]
  unfold clusterWeight
  exact_mod_cast compatibleSigns_card left right η

omit [Fintype V] [Fintype E] in
theorem bondConnected_mono (left right : E → V) (x y : V) :
    Monotone (fun η => bondConnected left right η x y) := by
  intro η ξ h hη s hs
  exact hη s (bondSubspace_antitone left right h hs)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DiscreteReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

variable {V : Type uV} [Fintype V]

theorem isingReference_singleton (s : V → Bool) :
    isingReference {s}=(2 : ℝ≥0∞)⁻¹^Fintype.card V := by
  classical
  rw [isingReference,Measure.pi_singleton]
  simp [signLaw]

open scoped Classical in
theorem integral_isingReference (f : (V → Bool) → ℝ) :
    (∫ s,f s ∂isingReference)=(2 : ℝ)⁻¹^Fintype.card V*∑ s,f s := by
  classical
  rw [integral_fintype (compact_integrable continuous_of_discreteTopology)]
  simp only [Measure.real,isingReference_singleton,ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofNat,smul_eq_mul,← Finset.mul_sum]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem bondSignProduct_eq (left right : E → V) (t : E → ℝ) (η : E → Bool) (s : V → Bool) :
    bondSignProduct left right t η s=
      bondProduct t η*(if s∈compatibleSigns left right η then 1 else 0) := by
  by_cases h : s∈compatibleSigns left right η
  · simp only [h,ite_true,mul_one,bondSignProduct,bondProduct]
    apply Finset.prod_congr rfl
    intro e _
    cases he : η e
    · simp
    · simp [h e he]
  · simp only [h,ite_false,mul_zero]
    obtain ⟨e,he,hs⟩ : ∃ e,η e=true ∧ s (left e)≠s (right e) := by
      change ¬(∀ e,η e=true → s (left e)=s (right e)) at h
      push Not at h
      exact h
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he,hs]

omit [Fintype V] in
theorem ising_expansion (left right : E → V) (K : E → ℝ) (s : V → Bool) :
    Real.exp (edgeHamiltonian (isingEnergy left right) K s)=
      Real.exp (-∑ e,K e)*∑ η : E → Bool,bondSignProduct left right
        (fun e => Real.exp (2*K e)-1) η s := by
  have hedge (k : ℝ) (a b : Bool) :
      Real.exp (k*(signValue a*signValue b))=
        Real.exp (-k)*(∑ η : Bool,if η then (if a=b then Real.exp (2*k)-1 else 0) else 1) := by
    cases a <;> cases b <;> simp [signValue]
    all_goals ring_nf
    all_goals rw [← Real.exp_add]
    all_goals (congr 1; ring)
  unfold edgeHamiltonian isingEnergy
  rw [Real.exp_sum]
  simp_rw [hedge]
  rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib,Fintype.prod_sum]
  rfl

theorem ising_partition_bond_sum (left right : E → V) (K : E → ℝ) :
    (∫ s,Real.exp (edgeHamiltonian (isingEnergy left right) K s) ∂isingReference)=
      (2 : ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,K e)*
        ∑ η,bondWeight left right (fun e => Real.exp (2*K e)-1) η := by
  rw [integral_isingReference]
  simp_rw [ising_expansion,bondSignProduct_eq]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,compatibleSigns_sum]
  unfold bondWeight
  simp only [mul_comm (bondProduct _ _) (clusterWeight _ _ _)]
  ring

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinBondKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem continuous_spinBondParameter (left right : E → V) (b : E → ℝ) (e : E) :
    Continuous (fun s => spinBondParameter left right b s e) := by
  unfold spinBondParameter
  fun_prop

omit [Fintype V] in
theorem continuous_spinBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    Continuous (fun s => spinBondWeight left right b s η) := by
  unfold spinBondWeight
  apply continuous_finsetProd
  intro e _
  split <;> [exact continuous_spinBondParameter _ _ _ _;exact continuous_const.sub (continuous_spinBondParameter _ _ _ _)]

omit [Fintype V] [Fintype E] in
theorem spinBondParameter_bounds (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (s : V → Spin 3) (e : E) : 0 ≤ spinBondParameter left right b s e ∧ spinBondParameter left right b s e≤1 := by
  have hn : -2*b e*max ((s (left e)).val 0*(s (right e)).val 0) 0≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hb e)) (le_max_right _ _)
  have h := Real.exp_le_one_iff.mpr hn
  have hp := Real.exp_pos (-2*b e*max ((s (left e)).val 0*(s (right e)).val 0) 0)
  constructor <;> unfold spinBondParameter <;> linarith

omit [Fintype V] in
theorem spinBondWeight_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (s : V → Spin 3) (η : E → Bool) : 0 ≤ spinBondWeight left right b s η := by
  apply Finset.prod_nonneg
  intro e _
  split
  · exact (spinBondParameter_bounds _ _ _ hb s e).1
  · exact sub_nonneg.mpr (spinBondParameter_bounds _ _ _ hb s e).2

omit [Fintype V] in
theorem spinBondWeight_sum (left right : E → V) (b : E → ℝ) (s : V → Spin 3) :
    (∑ η,spinBondWeight left right b s η)=1 := by
  unfold spinBondWeight
  change (∑ η : E → Bool, ∏ e, (fun (e : E) (z : Bool) => if z then spinBondParameter left right b s e else 1-spinBondParameter left right b s e) e (η e)) = 1
  rw [← Fintype.prod_sum (fun (e : E) (z : Bool) => if z then spinBondParameter left right b s e else 1-spinBondParameter left right b s e)]
  simp

omit [Fintype V] [Fintype E] in
theorem spinBondParameter_cylinder (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) (e : E) :
    spinBondParameter left right b (cylindricalConfiguration r τ θ) e=
      if τ (left e)=τ (right e) then 1-Real.exp (-2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e) else 0 := by
  have hp : 0≤(r (left e):ℝ)*(r (right e):ℝ) := mul_nonneg (r (left e)).property.1 (r (right e)).property.1
  unfold spinBondParameter cylindricalConfiguration cylindricalSpin
  simp only [Fin.isValue,Matrix.cons_val_zero]
  have hmul : (r (left e):ℝ)*signValue (τ (left e))*((r (right e):ℝ)*signValue (τ (right e)))=
      (r (left e):ℝ)*(r (right e):ℝ)*(signValue (τ (left e))*signValue (τ (right e))) := by ring
  rw [hmul]
  cases τ (left e) <;> cases τ (right e) <;> simp only [signValue,Bool.false_eq_true,ite_false,ite_true,
    mul_neg,neg_mul,mul_one,neg_neg]
  all_goals simp only [max_eq_left hp,max_eq_right (neg_nonpos.mpr hp),mul_zero,neg_zero,Real.exp_zero,sub_self]
  all_goals (congr 2 <;> (unfold amplitudeCoupling; ring))

omit [Fintype V] in
theorem cylindrical_ising_bond_weight (left right : E → V) (K : E → ℝ) (τ : V → Bool) (η : E → Bool) :
    Real.exp (edgeHamiltonian (isingEnergy left right) K τ)*
      (∏ e,if η e then (if τ (left e)=τ (right e) then 1-Real.exp (-2*K e) else 0)
        else 1-(if τ (left e)=τ (right e) then 1-Real.exp (-2*K e) else 0))=
      Real.exp (-∑ e,K e)*bondSignProduct left right (fun e => Real.exp (2*K e)-1) η τ := by
  have he (k : ℝ) (a d z : Bool) :
      Real.exp (k*(signValue a*signValue d))*(if z then (if a=d then 1-Real.exp (-2*k) else 0)
        else 1-(if a=d then 1-Real.exp (-2*k) else 0))=
      Real.exp (-k)*(if z then (if a=d then Real.exp (2*k)-1 else 0) else 1) := by
    have h1 : Real.exp k*Real.exp (-(2*k))=Real.exp (-k) := by rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-k)*Real.exp (2*k)=Real.exp k := by rw [← Real.exp_add]; congr 1; ring
    cases a <;> cases d <;> cases z <;> simp [signValue,mul_sub,h1,h2]
  unfold edgeHamiltonian isingEnergy
  rw [Real.exp_sum,← Finset.prod_mul_distrib]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib]
  rfl

omit [Fintype V] in
theorem cylindrical_spin_bond_weight (left right : E → V) (b : E → ℝ)
    (r : V → Amplitude) (τ : V → Bool) (θ : V → PlanarAngle) (η : E → Bool) :
    Real.exp (freeSpinEnergy 3 left right b (cylindricalConfiguration r τ θ))*
      spinBondWeight left right b (cylindricalConfiguration r τ θ) η=
      Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
        bondSignProduct left right (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1) η τ*
        Real.exp (edgeHamiltonian (planarEnergy left right)
          (amplitudeCoupling left right b (fun v => transverseAmplitude (r v))) θ) := by
  rw [cylindricalConfiguration_energy,Real.exp_add]
  unfold spinBondWeight
  simp_rw [spinBondParameter_cylinder]
  rw [mul_right_comm, cylindrical_ising_bond_weight]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.JointBond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem amplitudeBondParam_nonneg (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) (r : V → Amplitude) (e : E) :
    0 ≤ amplitudeBondParam left right b r e := by
  apply sub_nonneg.mpr
  apply Real.one_le_exp
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hb e)) (r (left e)).property.1) (r (right e)).property.1

omit [Fintype V] [Fintype E] in
theorem amplitudeBondParam_monotone (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0 ≤ b e) : Monotone (amplitudeBondParam left right b) := by
  intro r s hrs e
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (hrs (left e)) (mul_nonneg (by norm_num) (hb e))
  · exact hrs (right e)
  · exact (r (right e)).property.1
  · exact mul_nonneg (mul_nonneg (by norm_num) (hb e)) (s (left e)).property.1

omit [Fintype V] [Fintype E] in
theorem continuous_amplitudeBondParam (left right : E → V) (b : E → ℝ) (e : E) :
    Continuous (fun r => amplitudeBondParam left right b r e) := by
  unfold amplitudeBondParam; fun_prop

omit [Fintype V] in
theorem continuous_bondConditionalMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ η,Continuous (fun r => f r η)) :
    Continuous (bondConditionalMean left right b f) := by
  have hw (η : E → Bool) : Continuous (fun r => bondWeight left right (amplitudeBondParam left right b r) η) := by
    unfold bondWeight bondProduct
    apply Continuous.mul continuous_const
    apply continuous_finsetProd
    intro e _
    split
    · exact continuous_amplitudeBondParam left right b e
    · exact continuous_const
  exact (continuous_finsetSum _ (fun η _ => (hw η).mul (hf η))).div
    (continuous_finsetSum _ (fun η _ => hw η))
    (fun r => (bondWeight_sum_pos left right (amplitudeBondParam_nonneg left right b hb r)).ne')

omit [Fintype V] in
theorem bondConditionalMean_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ r η,0 ≤ f r η) (r : V → Amplitude) :
    0 ≤ bondConditionalMean left right b f r :=
  finiteMean_nonneg (bondWeight_nonneg left right (amplitudeBondParam_nonneg left right b hb r)) (hf r)

theorem bondConditionalMean_monotone (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f : (V → Amplitude) → (E → Bool) → ℝ} (hf : ∀ r η,0 ≤ f r η)
    (hmr : ∀ η,Monotone (fun r => f r η)) (hmη : ∀ r,Monotone (f r)) :
    Monotone (bondConditionalMean left right b f) := by
  intro r s hrs
  apply le_trans (bondMean_mono left right (amplitudeBondParam_nonneg left right b hb r)
    (amplitudeBondParam_monotone left right b hb hrs) (hf r) (hmη r))
  exact finiteMean_mono (bondWeight_nonneg left right (amplitudeBondParam_nonneg left right b hb s))
    (fun η => hmr η hrs)

theorem jointBond_associated (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    {f g : (V → Amplitude) → (E → Bool) → ℝ}
    (hf : ∀ η,Continuous (fun r => f r η)) (hg : ∀ η,Continuous (fun r => g r η))
    (hfn : ∀ r η,0 ≤ f r η) (hgn : ∀ r η,0 ≤ g r η)
    (hfr : ∀ η,Monotone (fun r => f r η)) (hgr : ∀ η,Monotone (fun r => g r η))
    (hfη : ∀ r,Monotone (f r)) (hgη : ∀ r,Monotone (g r)) :
    jointBondMean μ left right b f*jointBondMean μ left right b g ≤
      jointBondMean μ left right b (fun r η => f r η*g r η) := by
  have hcf := continuous_bondConditionalMean left right b hb hf
  have hcg := continuous_bondConditionalMean left right b hb hg
  apply le_trans (amplitude_associated_any μ left right b hb
    _ _ hcf hcg (bondConditionalMean_nonneg left right b hb hfn)
    (bondConditionalMean_nonneg left right b hb hgn)
    (bondConditionalMean_monotone left right b hb hfn hfr hfη)
    (bondConditionalMean_monotone left right b hb hgn hgr hgη))
  apply weightedMean_mono (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
    (hcf.mul hcg) (continuous_bondConditionalMean left right b hb (fun η => (hf η).mul (hg η)))
  intro r
  exact bondMean_associated left right (amplitudeBondParam_nonneg left right b hb r)
    (hfn r) (hgn r) (hfη r) (hgη r)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem isingAmplitudePartition_bond_sum (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    isingAmplitudePartition left right b r=
      (2:ℝ)⁻¹^Fintype.card V*Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
        ∑ η,bondWeight left right (amplitudeBondParam left right b r) η := by
  have hp : (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1)=
      amplitudeBondParam left right b r := by
    funext e
    unfold amplitudeBondParam amplitudeCoupling
    congr 2
    ring
  rw [isingAmplitudePartition,amplitudePartition,ising_partition_bond_sum,hp]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.RawBond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem amplitudeBondPrefactor_pos (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    0<amplitudeBondPrefactor left right b r := by
  unfold amplitudeBondPrefactor
  exact mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (planarAmplitudePartition_pos _ _ _ _)

theorem continuous_amplitudeBondPrefactor (left right : E → V) (b : E → ℝ) :
    Continuous (amplitudeBondPrefactor left right b) := by
  unfold amplitudeBondPrefactor
  apply Continuous.mul _ (continuous_planarAmplitudePartition _ _ _)
  unfold amplitudeCoupling
  fun_prop

theorem continuous_amplitudeBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    Continuous (fun r => amplitudeBondWeight left right b r η) := by
  apply (continuous_amplitudeBondPrefactor _ _ _).mul
  unfold bondWeight bondProduct
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro e _
  split
  · exact continuous_amplitudeBondParam left right b e
  · exact continuous_const

theorem amplitudeBondWeight_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (r : V → Amplitude) (η : E → Bool) : 0≤amplitudeBondWeight left right b r η :=
  mul_nonneg (amplitudeBondPrefactor_pos _ _ _ _).le
    (bondWeight_nonneg _ _ (amplitudeBondParam_nonneg _ _ _ hb r) η)

theorem amplitudeBondWeight_sum (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    (∑ η,amplitudeBondWeight left right b r η)=amplitudeDensity left right b r := by
  unfold amplitudeBondWeight amplitudeDensity
  rw [isingAmplitudePartition_bond_sum]
  rw [← Finset.mul_sum]
  unfold amplitudeBondPrefactor
  ring

theorem amplitudeDensity_bondConditionalMean (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (f : (V → Amplitude) → (E → Bool) → ℝ) (r : V → Amplitude) :
    amplitudeDensity left right b r*bondConditionalMean left right b f r=
      ∑ η,amplitudeBondWeight left right b r η*f r η := by
  rw [← amplitudeBondWeight_sum left right b r]
  unfold amplitudeBondWeight bondConditionalMean finiteMean
  rw [← Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have hs := (bondWeight_sum_pos left right (amplitudeBondParam_nonneg left right b hb r)).ne'
  field_simp

theorem jointBondMean_raw (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (f : (V → Amplitude) → (E → Bool) → ℝ) :
    jointBondMean μ left right b f=
      (∫ r,∑ η,amplitudeBondWeight left right b r η*f r η ∂Measure.pi (fun _ : V => μ))/
        (∫ r,∑ η,amplitudeBondWeight left right b r η ∂Measure.pi (fun _ : V => μ)) := by
  unfold jointBondMean weightedMean
  simp_rw [amplitudeDensity_bondConditionalMean _ _ _ hb,amplitudeBondWeight_sum]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinBonds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem amplitudeBondParam_eq (left right : E → V) (b : E → ℝ) (r : V → Amplitude) :
    (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1)=
      amplitudeBondParam left right b r := by
  funext e
  unfold amplitudeBondParam amplitudeCoupling
  congr 2
  ring

theorem integral_spinBondWeight (left right : E → V) (b : E → ℝ) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η ∂freeSpinReference 3)=
      ∫ r,amplitudeBondWeight left right b r η ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*
      spinBondWeight left right b s η) :=
    (continuous_freeSpinEnergy 3 left right b).rexp.mul (continuous_spinBondWeight left right b η)
  rw [integral_freeSpinReference_cylinder _ hc]
  apply integral_congr_ae
  filter_upwards with r
  simp_rw [cylindrical_spin_bond_weight,integral_const_mul]
  change (∫ τ,Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (r v:ℝ)) e)*
    bondSignProduct left right (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (r v:ℝ)) e)-1) η τ*
    planarAmplitudePartition left right b r ∂isingReference)=_
  rw [integral_mul_const,integral_const_mul,integral_isingReference]
  simp_rw [bondSignProduct_eq,← Finset.mul_sum,compatibleSigns_sum]
  rw [amplitudeBondParam_eq]
  unfold amplitudeBondWeight amplitudeBondPrefactor bondWeight
  ring

theorem integral_freeSpinWeight (left right : E → V) (b : E → ℝ) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂freeSpinReference 3)=
      ∫ r,amplitudeDensity left right b r ∂Measure.pi (fun _ : V => sphericalAmplitudeLaw) := by
  have he (s : V → Spin 3) : Real.exp (freeSpinEnergy 3 left right b s)=
      ∑ η,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η := by
    rw [← Finset.mul_sum,spinBondWeight_sum,mul_one]
  rw [show (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s))=
    (fun s => ∑ η,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η) from funext he]
  rw [integral_finsetSum]
  · simp_rw [integral_spinBondWeight]
    rw [← integral_finsetSum]
    · simp_rw [amplitudeBondWeight_sum]
    · intro η _
      exact compact_integrable (continuous_amplitudeBondWeight _ _ _ _)
  · intro η _
    exact compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul (continuous_spinBondWeight _ _ _ _))

theorem freeBondMean_eq_jointBondMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (f : (E → Bool) → ℝ) :
    freeBondMean left right b f=jointBondMean sphericalAmplitudeLaw left right b (fun _ η => f η) := by
  rw [jointBondMean_raw _ _ _ _ hb]
  unfold freeBondMean freeSpinMean weightedMean
  rw [integral_freeSpinWeight]
  simp_rw [amplitudeBondWeight_sum]
  congr 1
  simp_rw [Finset.mul_sum,← mul_assoc]
  rw [integral_finsetSum,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro η _
    rw [integral_mul_const,integral_mul_const,integral_spinBondWeight]
  · intro η _
    exact (compact_integrable (continuous_amplitudeBondWeight _ _ _ _)).mul_const _
  · intro η _
    exact (compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul
      (continuous_spinBondWeight _ _ _ _))).mul_const _

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondPin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V]

omit [Fintype V] in
theorem bondPinFactor_pos (left right : E → V) (B : Set V) (η : E → Bool) :
    0 < bondPinFactor left right B η := by unfold bondPinFactor; positivity

theorem bondPinRank_antitone (left right : E → V) (B : Set V) :
    Antitone (bondPinRank left right B) := by
  intro η ξ h
  apply Submodule.finrank_mono
  exact Submodule.map_mono (bondSubspace_antitone left right h)

theorem bondPinFactor_monotone (left right : E → V) (B : Set V) :
    Monotone (bondPinFactor left right B) := by
  intro η ξ h
  apply inv_anti₀ (by positivity : 0 < (2:ℝ)^bondPinRank left right B ξ)
  exact pow_le_pow_right₀ (by norm_num) (bondPinRank_antitone left right B h)

theorem pinnedBond_rank_add (left right : E → V) (B : Set V) (η : E → Bool) :
    Module.finrank SignField (pinnedBondSubspace left right B η)+bondPinRank left right B η =
      bondRank left right η := by
  let K := bondSubspace left right η
  let f := (pinRestriction B).domRestrict K
  have hk : LinearMap.ker f=(pinnedBondSubspace left right B η).comap K.subtype := by
    ext s
    simp [f,pinnedBondSubspace,K]
  have hh := LinearMap.finrank_range_add_finrank_ker f
  rw [show LinearMap.range f=K.map (pinRestriction B) from LinearMap.range_domRestrict K _,hk,
    (Submodule.comapSubtypeEquivOfLe (show pinnedBondSubspace left right B η ≤ K from inf_le_left)).finrank_eq] at hh
  exact (Nat.add_comm _ _).trans hh

theorem pinnedBond_card (left right : E → V) (B : Set V) (η : E → Bool) :
    (Fintype.card (pinnedBondSubspace left right B η) : ℝ)=
      clusterWeight left right η*bondPinFactor left right B η := by
  rw [Module.card_eq_pow_finrank (K := SignField)]
  simp only [SignField,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  unfold clusterWeight bondPinFactor
  rw [← pinnedBond_rank_add left right B η,pow_add,mul_assoc,mul_inv_cancel₀ (by positivity),mul_one]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V]

theorem positiveCompatibleSigns_card (left right : E → V) (B : Set V) (η : E → Bool) :
    (Fintype.card (positiveCompatibleSigns left right B η):ℝ)=
      clusterWeight left right η*bondPinFactor left right B η := by
  rw [Fintype.card_congr (positiveCompatibleSignsEquiv left right B η)]
  exact pinnedBond_card left right B η

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE}

theorem bondGraph_endpoint_reachable (left right : E → V) (η : E → Bool) (e : E)
    (he : η e=true) : (bondGraph left right η).Reachable (left e) (right e) := by
  by_cases h : left e=right e
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h,e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem bondConnected_iff_reachable (left right : E → V) (η : E → Bool) (x y : V) :
    bondConnected left right η x y ↔ (bondGraph left right η).Reachable x y := by
  constructor
  · intro h
    let s : V → SignField := fun v => if (bondGraph left right η).Reachable x v then 0 else 1
    have hs : s∈bondSubspace left right η := by
      intro e he
      have hh := bondGraph_endpoint_reachable left right η e he
      have hi : (bondGraph left right η).Reachable x (left e) ↔
          (bondGraph left right η).Reachable x (right e) :=
        ⟨fun hp => hp.trans hh,fun hp => hp.trans hh.symm⟩
      simp only [s,hi]
    have hh := h s hs
    by_contra hy
    simp [s,hy] at hh
  · rintro ⟨p⟩ s hs
    induction p with
    | nil => rfl
    | @cons u v w huv p ih =>
      apply Eq.trans _ ih
      obtain ⟨_,e,he,hor⟩ := huv
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hs e he
      · exact (hs e he).symm

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SignedSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE}

theorem bondConnected_refl (left right : E → V) (η : E → Bool) (x : V) :
    bondConnected left right η x x := fun _ _ => rfl

theorem bondConnected_symm (left right : E → V) (η : E → Bool) {x y : V}
    (h : bondConnected left right η x y) : bondConnected left right η y x := fun s hs => (h s hs).symm

theorem bondConnected_trans (left right : E → V) (η : E → Bool) {x y z : V}
    (h : bondConnected left right η x y) (k : bondConnected left right η y z) :
    bondConnected left right η x z := fun s hs => (h s hs).trans (k s hs)

theorem bondConnected_endpoints (left right : E → V) (η : E → Bool) (e : E) (he : η e=true) :
    bondConnected left right η (left e) (right e) := fun _ hs => hs e he

theorem compatibleSigns_connected (left right : E → V) (η : E → Bool)
    {s : V → Bool} (hs : s∈compatibleSigns left right η) {x y : V}
    (h : bondConnected left right η x y) : s x=s y := by
  apply signFieldEquiv.injective
  apply h
  intro e he
  exact congrArg signFieldEquiv (hs e he)

variable [Fintype V]

theorem prescribedCompatibleSigns_card_of_nonempty (left right : E → V) (B : Set V)
    (p : V → Bool) (η : E → Bool) (h : (prescribedCompatibleSigns left right B p η).Nonempty) :
    (Fintype.card (prescribedCompatibleSigns left right B p η):ℝ)=
      clusterWeight left right η*bondPinFactor left right B η := by
  obtain ⟨t,ht⟩ := h
  rw [← Fintype.card_congr (prescribedCompatibleSignsEquiv left right B p η ⟨t,ht⟩)]
  exact positiveCompatibleSigns_card _ _ _ _

omit [Fintype V] in
theorem layerSigns_consistent_iff (left right : E → V) (I O : Set V) (hIO : Disjoint I O)
    (η : E → Bool) : (prescribedCompatibleSigns left right (I∪O) (layerSigns I) η).Nonempty ↔
      ¬bondCrossing left right I O η := by
  constructor
  · rintro ⟨s,hs,hp⟩ ⟨x,hx,y,hy,hxy⟩
    have he := compatibleSigns_connected left right η hs hxy
    have hx' := hp x (Or.inl hx)
    have hy' := hp y (Or.inr hy)
    have hyI : y∉I := fun h => Set.disjoint_left.mp hIO h hy
    simp only [layerSigns,hx,hyI,ite_true,ite_false] at hx' hy'
    rw [hx',hy'] at he
    cases he
  · intro hn
    let t : V → Bool := fun v => if ∃ x∈I,bondConnected left right η x v then false else true
    refine ⟨t,?_,?_⟩
    · intro e he
      have hc := bondConnected_endpoints left right η e he
      have hi : (∃ x∈I,bondConnected left right η x (left e)) ↔
          ∃ x∈I,bondConnected left right η x (right e) := by
        constructor
        · rintro ⟨x,hx,hxc⟩
          exact ⟨x,hx,bondConnected_trans left right η hxc hc⟩
        · rintro ⟨x,hx,hxc⟩
          exact ⟨x,hx,bondConnected_trans left right η hxc (bondConnected_symm left right η hc)⟩
      simp only [t,hi]
    · intro v hv
      rcases hv with hv | hv
      · have hc : ∃ x∈I,bondConnected left right η x v := ⟨v,hv,bondConnected_refl _ _ _ _⟩
        simp [t,layerSigns,hv,hc]
      · have hc : ¬∃ x∈I,bondConnected left right η x v := by
          rintro ⟨x,hx,hxv⟩
          exact hn ⟨x,hx,v,hv,hxv⟩
        have hvI : v∉I := fun h => Set.disjoint_left.mp hIO h hv
        simp [t,layerSigns,hvI,hc]

theorem layerSigns_card (left right : E → V) (I O : Set V) (hIO : Disjoint I O) (η : E → Bool) :
    (Fintype.card (prescribedCompatibleSigns left right (I∪O) (layerSigns I) η):ℝ)=
      clusterWeight left right η*bondPinFactor left right (I∪O) η*
        (if bondCrossing left right I O η then 0 else 1) := by
  split_ifs with h
  · have he : prescribedCompatibleSigns left right (I∪O) (layerSigns I) η=∅ := by
      exact Set.not_nonempty_iff_eq_empty.mp (fun hn => (layerSigns_consistent_iff _ _ _ _ hIO _).mp hn h)
    simp [he]
  · rw [prescribedCompatibleSigns_card_of_nonempty _ _ _ _ _ ((layerSigns_consistent_iff _ _ _ _ hIO _).mpr h)]
    simp

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondAssociation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem rawBond_tilt_defect_nonneg (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f g : (V → Amplitude) → (E → Bool) → ℝ}
    (hf : ∀ η,Continuous (fun r => f r η)) (hg : ∀ η,Continuous (fun r => g r η))
    (hfn : ∀ r η,0≤f r η) (hgn : ∀ r η,0≤g r η)
    (hfr : ∀ η,Monotone (fun r => f r η)) (hgr : ∀ η,Monotone (fun r => g r η))
    (hfη : ∀ r,Monotone (f r)) (hgη : ∀ r,Monotone (g r)) :
    0≤∫ r,∑ η,amplitudeBondWeight left right b r η*g r η*
      (f r η-jointBondMean μ left right b f) ∂Measure.pi (fun _ : V => μ) := by
  let c := jointBondMean μ left right b f
  have h := jointBond_associated μ left right b hb hf hg hfn hgn hfr hgr hfη hgη
  change c*jointBondMean μ left right b g≤jointBondMean μ left right b (fun r η => f r η*g r η) at h
  rw [jointBondMean_raw _ _ _ _ hb,jointBondMean_raw _ _ _ _ hb] at h
  have hD : 0<∫ r,∑ η,amplitudeBondWeight left right b r η ∂Measure.pi (fun _ : V => μ) := by
    simp_rw [amplitudeBondWeight_sum]
    exact compact_integral_pos (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
  rw [← mul_div_assoc,div_le_div_iff_of_pos_right hD] at h
  have hi1 : Integrable (fun r => ∑ η,amplitudeBondWeight left right b r η*(f r η*g r η))
      (Measure.pi (fun _ : V => μ)) := by
    apply compact_integrable
    exact continuous_finsetSum _ (fun η _ => (continuous_amplitudeBondWeight _ _ _ η).mul ((hf η).mul (hg η)))
  have hi2 : Integrable (fun r => c*∑ η,amplitudeBondWeight left right b r η*g r η)
      (Measure.pi (fun _ : V => μ)) := by
    apply compact_integrable
    exact continuous_const.mul (continuous_finsetSum _ (fun η _ => (continuous_amplitudeBondWeight _ _ _ η).mul (hg η)))
  have he (r : V → Amplitude) :
      (∑ η,amplitudeBondWeight left right b r η*g r η*(f r η-c))=
        (∑ η,amplitudeBondWeight left right b r η*(f r η*g r η))-
          c*∑ η,amplitudeBondWeight left right b r η*g r η := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro η _
    ring
  change 0≤∫ r,∑ η,amplitudeBondWeight left right b r η*g r η*(f r η-c) ∂Measure.pi (fun _ : V => μ)
  simp_rw [he]
  rw [integral_sub hi1 hi2,integral_const_mul]
  exact sub_nonneg.mpr h

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem continuous_pinWeightedSum (left right : E → V) (b : E → ℝ) (B : Set V)
    (f : (E → Bool) → ℝ) :
    Continuous (fun r => ∑ η,amplitudeBondWeight left right b r η*bondPinFactor left right B η*f η) := by
  exact continuous_finsetSum _ (fun η _ => ((continuous_amplitudeBondWeight _ _ _ η).mul continuous_const).mul continuous_const)

theorem pinWeightedSum_pos (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (B : Set V) (r : V → Amplitude) :
    0<∑ η,amplitudeBondWeight left right b r η*bondPinFactor left right B η*(1:ℝ) := by
  apply Finset.sum_pos'
  · intro η _
    exact mul_nonneg (mul_nonneg (amplitudeBondWeight_nonneg _ _ _ hb r η)
      (bondPinFactor_pos _ _ _ _).le) zero_le_one
  · refine ⟨fun _ => false,Finset.mem_univ _,?_⟩
    simp only [amplitudeBondWeight,bondWeight,bondProduct,Bool.false_eq_true,ite_false,Finset.prod_const_one,mul_one]
    exact mul_pos (mul_pos (amplitudeBondPrefactor_pos _ _ _ _) (clusterWeight_pos _ _ _)) (bondPinFactor_pos _ _ _ _)

theorem pinnedBondNumerator_one_pos (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (B : Set V) :
    0<pinnedBondNumerator μ left right b B (fun _ => 1) := by
  apply compact_integral_pos
  · exact (continuous_pinWeightedSum _ _ _ _ _).comp
      ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id))
  · intro r
    exact pinWeightedSum_pos _ _ _ hb _ _

theorem jointBond_le_pinnedBond (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (B : Set V) (f : (E → Bool) → ℝ) (hfn : ∀ η,0≤f η) (hfm : Monotone f) :
    jointBondMean μ left right b (fun _ η => f η)≤pinnedBondMean μ left right b B f := by
  let c := jointBondMean μ left right b (fun _ η => f η)
  let F : (V → Amplitude) → ℝ := fun r => ∑ η,amplitudeBondWeight left right b r η*
    bondPinFactor left right B η*(f η-c)
  have hF : Continuous F := continuous_pinWeightedSum _ _ _ _ _
  have ht : 0≤∫ r,F (glueAmplitude B ⊤ r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ) := by
    apply pinEndpoint_nonneg μ B hF
    intro h hh hn hm
    let g : (V → Amplitude) → (E → Bool) → ℝ := fun r η => h (fun v : B => r v)*bondPinFactor left right B η
    have hgr : ∀ η,Monotone (fun r => g r η) := by
      intro η r s hrs
      exact mul_le_mul_of_nonneg_right (hm (fun v => hrs v)) (bondPinFactor_pos _ _ _ _).le
    have hgη : ∀ r,Monotone (g r) := by
      intro r η ξ hη
      exact mul_le_mul_of_nonneg_left (bondPinFactor_monotone _ _ _ hη) (hn _)
    have hgc : ∀ η,Continuous (fun r => g r η) := by
      intro η
      exact (hh.comp (continuous_pi (fun v : B => continuous_apply v.val))).mul continuous_const
    have hi := rawBond_tilt_defect_nonneg μ left right b hb
      (f := fun _ η => f η) (g := g)
      (fun _ => continuous_const) hgc (fun _ η => hfn η)
      (fun r η => mul_nonneg (hn _) (bondPinFactor_pos _ _ _ _).le)
      (fun _ => monotone_const) hgr (fun _ => hfm) hgη
    convert hi using 1
    congr 1
    funext r
    dsimp only [F,g,c]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    ring
  have he (r : ↥(Bᶜ) → Amplitude) : F (glueAmplitude B ⊤ r)=
      (∑ η,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*bondPinFactor left right B η*f η)-
        c*(∑ η,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*bondPinFactor left right B η*1) := by
    dsimp only [F]
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro η _
    ring
  simp_rw [he] at ht
  have hc (q : (E → Bool) → ℝ) : Continuous (fun r : ↥(Bᶜ) → Amplitude =>
      ∑ η,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*bondPinFactor left right B η*q η) :=
    (continuous_pinWeightedSum _ _ _ _ q).comp ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id))
  rw [integral_sub (compact_integrable (hc f)) ((compact_integrable (hc (fun _ => 1))).const_mul c),integral_const_mul] at ht
  apply (le_div_iff₀ (pinnedBondNumerator_one_pos μ _ _ _ hb B)).2
  exact sub_nonneg.mp ht

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedBonds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem pinNormalization_pos (B : Set V) : 0<pinNormalization B := by
  unfold pinNormalization
  positivity

theorem sum_prescribed_bondSignProduct (left right : E → V) (t : E → ℝ)
    (B : Set V) (p : V → Bool) (η : E → Bool) :
    (∑ τ : ↥(Bᶜ) → Bool,bondSignProduct left right t η (glueFamily B (fun v => p v) τ))=
      bondProduct t η*(Fintype.card (prescribedCompatibleSigns left right B p η):ℝ) := by
  rw [sum_glueFamily]
  simp_rw [bondSignProduct_eq]
  have he (s : V → Bool) :
      (if (fun v : B => s v)=(fun v : B => p v) then
        bondProduct t η*(if s∈compatibleSigns left right η then 1 else 0) else 0)=
      bondProduct t η*(if s∈prescribedCompatibleSigns left right B p η then 1 else 0) := by
    have h : (fun v : B => s v)=(fun v : B => p v) ↔ ∀ v∈B,s v=p v := by
      simp only [funext_iff,Subtype.forall]
    have hp : s∈prescribedCompatibleSigns left right B p η ↔
        s∈compatibleSigns left right η ∧ ∀ v∈B,s v=p v := Iff.rfl
    simp only [hp,h]
    by_cases hB : ∀ v∈B,s v=p v
    · rw [ite_eq_left hB]
      by_cases hC : s∈compatibleSigns left right η
      · rw [ite_eq_left hC,ite_eq_left ⟨hC,hB⟩]
      · rw [ite_eq_right hC,ite_eq_right (fun h => hC h.1)]
    · rw [ite_eq_right hB,ite_eq_right (fun h => hB h.2),mul_zero]
  simp_rw [he]
  rw [← Finset.mul_sum,Finset.sum_boole,← Fintype.card_subtype]

theorem integral_pole_spinBondWeight_card (left right : E → V) (b : E → ℝ)
    (B : Set V) (p : V → Bool) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η
      ∂(poleSystem left right b B (fun v => p v)).reference)=
      pinNormalization B * ∫ r,amplitudeBondPrefactor left right b (glueAmplitude B ⊤ r)*
        bondProduct (amplitudeBondParam left right b (glueAmplitude B ⊤ r)) η*
        (Fintype.card (prescribedCompatibleSigns left right B p η):ℝ)
        ∂Measure.pi (fun _ : ↥(Bᶜ) => sphericalAmplitudeLaw) := by
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*
      spinBondWeight left right b s η) :=
    (continuous_freeSpinEnergy 3 left right b).rexp.mul (continuous_spinBondWeight left right b η)
  rw [integral_poleSystem_cylinder _ _ _ _ _ _ hc,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  simp_rw [cylindrical_spin_bond_weight,integral_const_mul]
  change (∫ τ,Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)*
    bondSignProduct left right (fun e => Real.exp (2*amplitudeCoupling left right b
      (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)-1) η (glueFamily B (fun v => p v) τ)*
    planarAmplitudePartition left right b (glueAmplitude B ⊤ r) ∂isingReference)=_
  rw [integral_mul_const,integral_const_mul,integral_isingReference]
  have hh := sum_prescribed_bondSignProduct left right
    (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)-1) B p η
  convert_to Real.exp (-∑ e,amplitudeCoupling left right b (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)*
    ((2:ℝ)⁻¹^Fintype.card ↥(Bᶜ)*
      (∑ τ : ↥(Bᶜ) → Bool,bondSignProduct left right
        (fun e => Real.exp (2*amplitudeCoupling left right b (fun v => (glueAmplitude B ⊤ r v:ℝ)) e)-1) η
        (glueFamily B (fun v => p v) τ)))*
    planarAmplitudePartition left right b (glueAmplitude B ⊤ r)=_ using 1
  · congr!
  rw [hh,amplitudeBondParam_eq]
  unfold amplitudeBondPrefactor pinNormalization
  have hn : ((2:ℝ)⁻¹^Fintype.card V)≠0 := by positivity
  field_simp

omit [Fintype E] in
theorem prescribed_positive_card (left right : E → V) (B : Set V) (η : E → Bool) :
    (Fintype.card (prescribedCompatibleSigns left right B (fun _ => true) η):ℝ)=
      clusterWeight left right η*bondPinFactor left right B η :=
  positiveCompatibleSigns_card _ _ _ _

theorem integral_positive_spinBondWeight (left right : E → V) (b : E → ℝ)
    (B : Set V) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η
      ∂(poleSystem left right b B (fun _ => true)).reference)=
      pinNormalization B * ∫ r,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*
        bondPinFactor left right B η ∂Measure.pi (fun _ : ↥(Bᶜ) => sphericalAmplitudeLaw) := by
  rw [integral_pole_spinBondWeight_card left right b B (fun _ => true) η]
  simp_rw [prescribed_positive_card]
  simp only [amplitudeBondWeight,bondWeight,mul_assoc,mul_left_comm,mul_comm]

theorem integral_layer_spinBondWeight (left right : E → V) (b : E → ℝ)
    (I O : Set V) (hIO : Disjoint I O) (η : E → Bool) :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η
      ∂(poleSystem left right b (I∪O) (fun v => layerSigns I v)).reference)=
      pinNormalization (I∪O) * ∫ r,amplitudeBondWeight left right b (glueAmplitude (I∪O) ⊤ r) η*
        bondPinFactor left right (I∪O) η*(if bondCrossing left right I O η then 0 else 1)
        ∂Measure.pi (fun _ : ↥((I∪O)ᶜ) => sphericalAmplitudeLaw) := by
  rw [integral_pole_spinBondWeight_card]
  simp_rw [layerSigns_card _ _ _ _ hIO]
  simp only [amplitudeBondWeight,bondWeight,mul_assoc,mul_left_comm,mul_comm]
  all_goals congr!

theorem integral_spinWeight_sum (left right : E → V) (b : E → ℝ)
    (μ : Measure (V → Spin 3)) [IsFiniteMeasure μ] :
    (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂μ)=
      ∑ η,∫ s,Real.exp (freeSpinEnergy 3 left right b s)*spinBondWeight left right b s η ∂μ := by
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with s
    rw [← Finset.mul_sum,spinBondWeight_sum,mul_one]
  · intro η _
    exact compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul (continuous_spinBondWeight _ _ _ _))

theorem positive_Z (left right : E → V) (b : E → ℝ) (B : Set V) :
    (poleSystem left right b B (fun _ => true)).Z (fun _ => 1)=
      pinNormalization B*pinnedBondNumerator sphericalAmplitudeLaw left right b B (fun _ => 1) := by
  change (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂(poleSystem left right b B (fun _ => true)).reference)=_
  rw [integral_spinWeight_sum]
  simp_rw [integral_positive_spinBondWeight]
  rw [← Finset.mul_sum,← integral_finsetSum]
  · simp only [mul_one,pinnedBondNumerator]
  · intro η _
    exact compact_integrable (((continuous_amplitudeBondWeight _ _ _ _).comp
      ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id))).mul continuous_const)

theorem layer_Z (left right : E → V) (b : E → ℝ) (I O : Set V) (hIO : Disjoint I O) :
    (poleSystem left right b (I∪O) (fun v => layerSigns I v)).Z (fun _ => 1)=
      pinNormalization (I∪O)*pinnedBondNumerator sphericalAmplitudeLaw left right b (I∪O)
        (fun η => if bondCrossing left right I O η then 0 else 1) := by
  change (∫ s,Real.exp (freeSpinEnergy 3 left right b s) ∂(poleSystem left right b (I∪O) (fun v => layerSigns I v)).reference)=_
  rw [integral_spinWeight_sum]
  simp_rw [integral_layer_spinBondWeight _ _ _ _ _ hIO]
  rw [← Finset.mul_sum,← integral_finsetSum]
  · simp only [pinnedBondNumerator]
    congr!
  · intro η _
    exact compact_integrable ((((continuous_amplitudeBondWeight _ _ _ _).comp
      ((continuous_glueAmplitude (I∪O)).comp (continuous_const.prodMk continuous_id))).mul continuous_const).mul continuous_const)

theorem poleBondMean_eq_pinnedBondMean (left right : E → V) (b : E → ℝ) (B : Set V)
    (f : (E → Bool) → ℝ) :
    poleBondMean left right b B (fun _ => true) f=
      pinnedBondMean sphericalAmplitudeLaw left right b B f := by
  unfold poleBondMean weightedMean
  change _/(poleSystem left right b B (fun _ => true)).Z (fun _ => 1)=_
  rw [positive_Z]
  simp_rw [Finset.mul_sum,← mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_mul_const,integral_positive_spinBondWeight]
    simp_rw [mul_assoc (pinNormalization B)]
    rw [← Finset.mul_sum]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum]
    · exact mul_div_mul_left _ _ (ne_of_gt (pinNormalization_pos B))
    · intro η _
      exact compact_integrable ((((continuous_amplitudeBondWeight _ _ _ _).comp
        ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id))).mul continuous_const).mul continuous_const)
  · intro η _
    exact (compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul
      (continuous_spinBondWeight _ _ _ _))).mul_const _

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProductGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uC uD uK uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {K : Type uK} [Fintype V] [Fintype K]
variable (A : V → Type uA) (label : V → K)

variable [∀ v,MeasurableSpace (A v)]

theorem grouped_measurePreserving (μ : (v : V) → Measure (A v)) [∀ v,SigmaFinite (μ v)] :
    MeasurePreserving (groupedMeasurableEquiv A label)
      (Measure.pi (fun k : K => Measure.pi (fun v : {v // label v=k} => μ v.val))) (Measure.pi μ) := by
  refine ⟨(groupedMeasurableEquiv A label).measurable,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (groupedMeasurableEquiv A label) ⁻¹' (Set.pi Set.univ s)=
      Set.pi Set.univ (fun k : K => Set.pi Set.univ (fun v : {v // label v=k} => s v.val)) := by
    ext x
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies]
    constructor
    · intro h k v
      have hv := h v.val
      rcases v with ⟨v,hv'⟩
      subst k
      exact hv
    · intro h v
      exact h (label v) ⟨v,rfl⟩
  rw [he,Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_sigma (fun v : Σ k : K, {v // label v=k} => μ v.2.val (s v.2.val))]
  exact (Equiv.sigmaFiberEquiv label).prod_comp (fun v => μ v (s v))

theorem integral_grouped_product (μ : (v : V) → Measure (A v)) [∀ v,SigmaFinite (μ v)]
    (f : (k : K) → ((v : {v // label v=k}) → A v.val) → ℝ) :
    (∫ s,(∏ k,f k (fun v => s v.val)) ∂Measure.pi μ)=
      ∏ k,∫ s,f k s ∂Measure.pi (fun v : {v // label v=k} => μ v.val) := by
  rw [← (grouped_measurePreserving A label μ).integral_comp']
  have he (s : GroupedFamily A label) :
      (∏ k,f k (fun v => groupedMeasurableEquiv A label s v.val))=∏ k,f k (s k) := by
    apply Finset.prod_congr rfl
    intro k _
    congr 1
    funext v
    rcases v with ⟨v,h⟩
    subst k
    rfl
  simp_rw [he]
  exact integral_fintype_prod_eq_prod _

theorem sum_grouped_product {D : Type uD} [Fintype D] (elabel : D → K)
    {C : D → Type uC} [∀ e,Fintype (C e)]
    (f : (k : K) → ((e : {e // elabel e=k}) → C e.val) → ℝ) :
    (∑ η : (e : D) → C e,∏ k,f k (fun e => η e.val))=
      ∏ k,∑ η,f k η := by
  rw [← (groupedEquiv C elabel).sum_comp]
  have he (s : GroupedFamily C elabel) :
      (∏ k,f k (fun e => groupedEquiv C elabel s e.val))=∏ k,f k (s k) := by
    apply Finset.prod_congr rfl
    intro k _
    congr 1
    funext e
    rcases e with ⟨e,h⟩
    subst k
    rfl
  simp_rw [he]
  exact (Fintype.prod_sum f).symm

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.WeightedProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uK uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {K : Type uK} [Fintype V] [Fintype K]
variable (A : V → Type uA) [∀ v,MeasurableSpace (A v)] (label : V → K)

theorem weightedMean_grouped_product (μ : (v : V) → Measure (A v)) [∀ v,SigmaFinite (μ v)]
    (w f : (k : K) → ((v : {v // label v=k}) → A v.val) → ℝ) :
    weightedMean (Measure.pi μ) (fun s => ∏ k,w k (fun v => s v.val))
      (fun s => ∏ k,f k (fun v => s v.val))=
      ∏ k,weightedMean (Measure.pi (fun v : {v // label v=k} => μ v.val)) (w k) (f k) := by
  unfold weightedMean
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_grouped_product A label μ (fun k s => w k s*f k s),
    integral_grouped_product A label μ w,Finset.prod_div_distrib]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PinnedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} {K : Type uK} [Fintype V] [Fintype E] [Fintype K]

omit [Fintype E] in
theorem sum_fibers (label : V → K) (f : V → ℝ) :
    (∑ k,∑ v : {v // label v=k},f v.val)=∑ v,f v := by
  rw [← Fintype.sum_sigma (fun v : Σ k : K,{v // label v=k} => f v.2.val)]
  exact (Equiv.sigmaFiberEquiv label).sum_comp f

omit [Fintype E] in
theorem prod_fibers (label : V → K) (f : V → ℝ) :
    (∏ k,∏ v : {v // label v=k},f v.val)=∏ v,f v := by
  rw [← Fintype.prod_sigma (fun v : Σ k : K,{v // label v=k} => f v.2.val)]
  exact (Equiv.sigmaFiberEquiv label).prod_comp f

omit [Fintype V] [Fintype E] [Fintype K] in
theorem continuous_blockSpin (B : Set V) (label : V → K) (k : K) :
    Continuous (blockSpin B label k) := by
  apply continuous_pi
  intro v
  by_cases hv : v∈B
  · simp only [blockSpin,hv,↓reduceDIte]
    exact continuous_const
  · by_cases hk : label v=k
    · simp only [blockSpin,hv,hk,↓reduceDIte]
      exact continuous_apply _
    · simp only [blockSpin,hv,hk,↓reduceDIte]
      exact continuous_const

omit [Fintype V] [Fintype E] [Fintype K] in
theorem blockSpin_eq_glue (B : Set V) (label : V → K) (k : K) (s : ↥(Bᶜ) → Spin 3)
    (v : V) (h : v∉B → label v=k) :
    blockSpin B label k (fun w => s w.val) v=glueFamily B (fun _ => poleSpin true) s v := by
  by_cases hv : v∈B
  · rw [show glueFamily B (fun _ => poleSpin true) s v=poleSpin true from
      glueFamily_in B _ _ ⟨v,hv⟩]
    simp only [blockSpin,hv,↓reduceDIte]
  · rw [show glueFamily B (fun _ => poleSpin true) s v=s ⟨v,hv⟩ from
      glueFamily_out B _ _ ⟨v,hv⟩]
    simp only [blockSpin,hv,h hv,↓reduceDIte]

omit [Fintype V] in
theorem block_energy_sum (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (hl : ∀ e,left e∉B → label (left e)=elabel e)
    (hr : ∀ e,right e∉B → label (right e)=elabel e) (s : ↥(Bᶜ) → Spin 3) :
    (∑ k,blockEnergy left right b B label elabel k (fun v => s v.val))=
      freeSpinEnergy 3 left right b (glueFamily B (fun _ => poleSpin true) s) := by
  unfold blockEnergy freeSpinEnergy
  have he (k : K) (e : {e // elabel e=k}) :
      b e.val*⟪(blockSpin B label k (fun v => s v.val) (left e.val)).val,
        (blockSpin B label k (fun v => s v.val) (right e.val)).val⟫_ℝ=
      b e.val*⟪(glueFamily B (fun _ => poleSpin true) s (left e.val)).val,
        (glueFamily B (fun _ => poleSpin true) s (right e.val)).val⟫_ℝ := by
    rw [blockSpin_eq_glue _ _ _ _ _ (fun h => (hl _ h).trans e.property),
      blockSpin_eq_glue _ _ _ _ _ (fun h => (hr _ h).trans e.property)]
  simp_rw [he]
  convert sum_fibers elabel (fun e => b e*⟪(glueFamily B (fun _ => poleSpin true) s (left e)).val,
    (glueFamily B (fun _ => poleSpin true) s (right e)).val⟫_ℝ) using 1

omit [Fintype V] in
theorem block_bond_product (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (hl : ∀ e,left e∉B → label (left e)=elabel e)
    (hr : ∀ e,right e∉B → label (right e)=elabel e) (s : ↥(Bᶜ) → Spin 3) (η : E → Bool) :
    (∏ k,blockBondWeight left right b B label elabel k (fun v => s v.val) (fun e => η e.val))=
      spinBondWeight left right b (glueFamily B (fun _ => poleSpin true) s) η := by
  unfold blockBondWeight spinBondWeight spinBondParameter
  have he (k : K) (e : {e // elabel e=k}) :
      blockSpin B label k (fun v => s v.val) (left e.val)=glueFamily B (fun _ => poleSpin true) s (left e.val) :=
    blockSpin_eq_glue _ _ _ _ _ (fun h => (hl _ h).trans e.property)
  have he' (k : K) (e : {e // elabel e=k}) :
      blockSpin B label k (fun v => s v.val) (right e.val)=glueFamily B (fun _ => poleSpin true) s (right e.val) :=
    blockSpin_eq_glue _ _ _ _ _ (fun h => (hr _ h).trans e.property)
  simp_rw [he,he']
  convert prod_fibers elabel (fun e => if η e then spinBondParameter left right b
    (glueFamily B (fun _ => poleSpin true) s) e else 1-spinBondParameter left right b
    (glueFamily B (fun _ => poleSpin true) s) e) using 1 <;> congr!

theorem poleBondMean_collapse (left right : E → V) (b : E → ℝ) (B : Set V) (f : (E → Bool) → ℝ) :
    poleBondMean left right b B (fun _ => true) f=
      weightedMean (Measure.pi (fun _ : ↥(Bᶜ) => sphereProbability 3))
        (fun s => Real.exp (freeSpinEnergy 3 left right b (glueFamily B (fun _ => poleSpin true) s)))
        (fun s => ∑ η,spinBondWeight left right b (glueFamily B (fun _ => poleSpin true) s) η*f η) := by
  unfold poleBondMean weightedMean
  rw [poleSystem_reference]
  have hc : Continuous (fun s : V → Spin 3 => Real.exp (freeSpinEnergy 3 left right b s)*
      ∑ η,spinBondWeight left right b s η*f η) :=
    (continuous_freeSpinEnergy _ _ _ _).rexp.mul
      (continuous_finsetSum _ (fun _ _ => (continuous_spinBondWeight _ _ _ _).mul continuous_const))
  rw [integral_pinProductMeasure _ _ _ _ hc,
    integral_pinProductMeasure _ _ _ _ (continuous_freeSpinEnergy 3 left right b).rexp]

omit [Fintype V] in
theorem block_event_product (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (hl : ∀ e,left e∉B → label (left e)=elabel e)
    (hr : ∀ e,right e∉B → label (right e)=elabel e)
    (f : (k : K) → ({e // elabel e=k} → Bool) → ℝ) (s : ↥(Bᶜ) → Spin 3) :
    (∑ η,spinBondWeight left right b (glueFamily B (fun _ => poleSpin true) s) η*
        ∏ k,f k (fun e => η e.val))=
      ∏ k,∑ η,blockBondWeight left right b B label elabel k (fun v => s v.val) η*f k η := by
  have hp (η : E → Bool) := (block_bond_product left right b B label elabel hl hr s η).symm
  simp_rw [hp,← Finset.prod_mul_distrib]
  convert sum_grouped_product (C := fun _ => Bool) elabel (fun k η =>
    blockBondWeight left right b B label elabel k (fun v => s v.val) η*f k η) using 1

theorem poleBondMean_blocks (left right : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (hl : ∀ e,left e∉B → label (left e)=elabel e)
    (hr : ∀ e,right e∉B → label (right e)=elabel e)
    (f : (k : K) → ({e // elabel e=k} → Bool) → ℝ) :
    poleBondMean left right b B (fun _ => true) (fun η => ∏ k,f k (fun e => η e.val))=
      ∏ k,blockBondMean left right b B label elabel k (f k) := by
  rw [poleBondMean_collapse]
  have hw (s : ↥(Bᶜ) → Spin 3) :
      Real.exp (freeSpinEnergy 3 left right b (glueFamily B (fun _ => poleSpin true) s))=
      ∏ k,Real.exp (blockEnergy left right b B label elabel k (fun v => s v.val)) := by
    rw [← block_energy_sum _ _ _ _ _ _ hl hr,Real.exp_sum]
  have hf := block_event_product left right b B label elabel hl hr f
  simp_rw [hw,hf]
  unfold blockBondMean
  convert weightedMean_grouped_product (fun _ : ↥(Bᶜ) => Spin 3) (fun v => label v.val)
    (fun _ => sphereProbability 3)
    (fun k s => Real.exp (blockEnergy left right b B label elabel k s))
    (fun k s => ∑ η,blockBondWeight left right b B label elabel k s η*f k η) using 1

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ReindexIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uV uW

noncomputable section
open MeasureTheory
namespace ClassicalON
variable {V : Type uV} {W : Type uW} {A : Type uA} [Fintype V] [Fintype W] [MeasurableSpace A]

theorem integral_pi_reindex (e : V ≃ W) (μ : W → Measure A) [∀ w,SigmaFinite (μ w)]
    (f : (V → A) → ℝ) :
    (∫ s : W → A,f (fun v => s (e v)) ∂Measure.pi μ)=
      ∫ s : V → A,f s ∂Measure.pi (fun v => μ (e v)) := by
  have h := (measurePreserving_piCongrLeft (fun v => μ (e v)) e.symm).integral_comp' f
  have he (s : W → A) : MeasurableEquiv.piCongrLeft (fun _ : V => A) e.symm s=(fun v => s (e v)) := by
    funext v
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  simpa only [he,Equiv.apply_symm_apply] using h

theorem weightedMean_pi_reindex (e : V ≃ W) (μ : W → Measure A) [∀ w,SigmaFinite (μ w)]
    (w f : (V → A) → ℝ) :
    weightedMean (Measure.pi μ) (fun s => w (fun v => s (e v))) (fun s => f (fun v => s (e v)))=
      weightedMean (Measure.pi (fun v => μ (e v))) w f := by
  unfold weightedMean
  rw [integral_pi_reindex e μ (fun s => w s*f s),integral_pi_reindex e μ w]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uE uF uV uW

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {W : Type uW} {E : Type uE} {F : Type uF} {A : Type uA} [Fintype V] [Fintype W] [Fintype E] [Fintype F]

omit [Fintype V] [Fintype W] in
theorem freeSpinEnergy_edgeEquiv (n : ℕ) (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W) (b : E → ℝ) (b' : F → ℝ)
    (s : V → Spin n) (s' : W → Spin n)
    (hb : ∀ e,b' (ee e)=b e) (hl : ∀ e,s' (l' (ee e))=s (l e))
    (hr : ∀ e,s' (r' (ee e))=s (r e)) :
    freeSpinEnergy n l' r' b' s'=freeSpinEnergy n l r b s := by
  unfold freeSpinEnergy
  rw [← ee.sum_comp]
  simp_rw [hb,hl,hr]

omit [Fintype V] [Fintype W] in
theorem spinBondWeight_edgeEquiv (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W) (b : E → ℝ) (b' : F → ℝ)
    (s : V → Spin 3) (s' : W → Spin 3)
    (hb : ∀ e,b' (ee e)=b e) (hl : ∀ e,s' (l' (ee e))=s (l e))
    (hr : ∀ e,s' (r' (ee e))=s (r e)) (η : F → Bool) :
    spinBondWeight l' r' b' s' η=spinBondWeight l r b s (fun e => η (ee e)) := by
  unfold spinBondWeight spinBondParameter
  rw [← ee.prod_comp]
  simp_rw [hb,hl,hr]

omit [Fintype V] [Fintype W] in
theorem sum_spinBondWeight_edgeEquiv (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W) (b : E → ℝ) (b' : F → ℝ)
    (s : V → Spin 3) (s' : W → Spin 3)
    (hb : ∀ e,b' (ee e)=b e) (hl : ∀ e,s' (l' (ee e))=s (l e))
    (hr : ∀ e,s' (r' (ee e))=s (r e)) (f : (E → Bool) → ℝ) :
    (∑ η,spinBondWeight l' r' b' s' η*f (fun e => η (ee e)))=
      ∑ η,spinBondWeight l r b s η*f η := by
  simp_rw [spinBondWeight_edgeEquiv ee l r l' r' b b' s s' hb hl hr]
  exact (arrowEquiv (A := Bool) ee).symm.sum_comp (fun η => spinBondWeight l r b s η*f η)

theorem poleBondMean_reindex (ev : V ≃ W) (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W) (b : E → ℝ) (b' : F → ℝ)
    (B : Set V) (B' : Set W) (hb : ∀ e,b' (ee e)=b e)
    (hl : ∀ e,l' (ee e)=ev (l e)) (hr : ∀ e,r' (ee e)=ev (r e))
    (hB : ∀ v,ev v∈B' ↔ v∈B) (f : (E → Bool) → ℝ) :
    poleBondMean l' r' b' B' (fun _ => true) (fun η => f (fun e => η (ee e)))=
      poleBondMean l r b B (fun _ => true) f := by
  unfold poleBondMean
  rw [poleSystem_reference,poleSystem_reference]
  have he (s : W → Spin 3) : freeSpinEnergy 3 l' r' b' s=
      freeSpinEnergy 3 l r b (fun v => s (ev v)) :=
    freeSpinEnergy_edgeEquiv 3 ee _ _ _ _ _ _ _ _ hb
      (fun e => congrArg s (hl e)) (fun e => congrArg s (hr e))
  have hs (s : W → Spin 3) := sum_spinBondWeight_edgeEquiv ee l r l' r' b b'
    (fun v => s (ev v)) s hb (fun e => congrArg s (hl e)) (fun e => congrArg s (hr e)) f
  simp_rw [he,hs]
  let μ (w : W) : Measure (Spin 3) := if w∈B' then Measure.dirac (poleSpin true) else sphereProbability 3
  have : ∀ w,IsProbabilityMeasure (μ w) := by intro w; dsimp [μ]; split <;> infer_instance
  change weightedMean (Measure.pi μ) _ _=_
  rw [weightedMean_pi_reindex ev μ (fun s => Real.exp (freeSpinEnergy 3 l r b s))
    (fun s => ∑ η,spinBondWeight l r b s η*f η)]
  have hμ : (fun v => μ (ev v))=(fun v => if v∈B then Measure.dirac (poleSpin true) else sphereProbability 3) := by
    funext v
    simp only [μ,hB]
  rw [hμ]
  rfl

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] in
theorem bondConnected_reindex (ev : V ≃ W) (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W)
    (hl : ∀ e,l' (ee e)=ev (l e)) (hr : ∀ e,r' (ee e)=ev (r e))
    (η : F → Bool) (x y : V) :
    bondConnected l' r' η (ev x) (ev y) ↔ bondConnected l r (fun e => η (ee e)) x y := by
  constructor
  · intro h s hs
    have ht : (fun w => s (ev.symm w))∈bondSubspace l' r' η := by
      intro f hf
      obtain ⟨e,rfl⟩ := ee.surjective f
      simpa only [hl,hr,Equiv.symm_apply_apply] using hs e hf
    simpa only [Equiv.symm_apply_apply] using h _ ht
  · intro h s hs
    apply h (fun v => s (ev v))
    intro e he
    simpa only [hl,hr] using hs (ee e) he

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] in
theorem bondCrossing_reindex (ev : V ≃ W) (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W)
    (hl : ∀ e,l' (ee e)=ev (l e)) (hr : ∀ e,r' (ee e)=ev (r e))
    (I O : Set V) (I' O' : Set W) (hI : ∀ v,ev v∈I' ↔ v∈I)
    (hO : ∀ v,ev v∈O' ↔ v∈O) (η : F → Bool) :
    bondCrossing l' r' I' O' η ↔ bondCrossing l r I O (fun e => η (ee e)) := by
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩
    obtain ⟨x,rfl⟩ := ev.surjective x
    obtain ⟨y,rfl⟩ := ev.surjective y
    exact ⟨x,(hI x).mp hx,y,(hO y).mp hy,(bondConnected_reindex ev ee l r l' r' hl hr η x y).mp hxy⟩
  · rintro ⟨x,hx,y,hy,hxy⟩
    exact ⟨ev x,(hI x).mpr hx,ev y,(hO y).mpr hy,(bondConnected_reindex ev ee l r l' r' hl hr η x y).mpr hxy⟩

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BlockLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uK uV uW

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {W : Type uW} {E : Type uE} {F : Type uF} {K : Type uK} [Fintype V] [Fintype W] [Fintype E] [Fintype F] [Fintype K]

omit [Fintype K] in
theorem blockBondMean_local (l r : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) (l' r' : F → W) (b' : F → ℝ) (B' : Set W)
    (ev : BlockVertex B label k ≃ ↥(B'ᶜ)) (ee : {e // elabel e=k} ≃ F)
    (hb : ∀ e,b' (ee e)=b e.val)
    (hl : ∀ (s : ↥(B'ᶜ) → Spin 3) e,
      glueFamily B' (fun _ => poleSpin true) s (l' (ee e))=
        blockSpin B label k (fun v => s (ev v)) (l e.val))
    (hr : ∀ (s : ↥(B'ᶜ) → Spin 3) e,
      glueFamily B' (fun _ => poleSpin true) s (r' (ee e))=
        blockSpin B label k (fun v => s (ev v)) (r e.val))
    (f : (F → Bool) → ℝ) :
    poleBondMean l' r' b' B' (fun _ => true) f=
      blockBondMean l r b B label elabel k (fun η => f (arrowEquiv ee η)) := by
  rw [poleBondMean_collapse]
  have he (s : ↥(B'ᶜ) → Spin 3) :
      freeSpinEnergy 3 l' r' b' (glueFamily B' (fun _ => poleSpin true) s)=
        blockEnergy l r b B label elabel k (fun v => s (ev v)) :=
    freeSpinEnergy_edgeEquiv 3 ee _ _ _ _ _ _ _ _ hb (hl s) (hr s)
  have hs (s : ↥(B'ᶜ) → Spin 3) :
      (∑ η,spinBondWeight l' r' b' (glueFamily B' (fun _ => poleSpin true) s) η*f η)=
        ∑ η,blockBondWeight l r b B label elabel k (fun v => s (ev v)) η*f (arrowEquiv ee η) := by
    have h := sum_spinBondWeight_edgeEquiv ee (fun e => l e.val) (fun e => r e.val) l' r'
      (fun e => b e.val) b' (blockSpin B label k (fun v => s (ev v)))
      (glueFamily B' (fun _ => poleSpin true) s) hb (hl s) (hr s)
      (fun η => f (arrowEquiv ee η))
    simp only [arrowEquiv,Equiv.coe_fn_mk,Equiv.apply_symm_apply] at h
    convert h using 1; congr!
  simp_rw [he,hs]
  unfold blockBondMean
  convert weightedMean_pi_reindex ev (fun _ => sphereProbability 3)
    (fun s => Real.exp (blockEnergy l r b B label elabel k s))
    (fun s => ∑ η,blockBondWeight l r b B label elabel k s η*f (arrowEquiv ee η)) using 1

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph
variable {K : Type uK}

theorem annulus_blockSpin (G : LatticeGraph) (N : ℤ) (hN : 0≤N) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) (s : ↥((G.annulusPins N (z i))ᶜ) → Spin 3)
    (v : (G.annulusGraph N (z i)).vertices) :
    glueFamily (G.annulusPins N (z i)) (fun _ => poleSpin true) s v=
      blockSpin (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (some i)
        (fun w => s (G.annulusFreeEquiv N hN z hz i w)) (G.restrictVertex _ v) := by
  by_cases hp : v∈G.annulusPins N (z i)
  · have hB : G.restrictVertex _ v∈G.allAnnulusPins N z := ⟨i,hp⟩
    rw [show glueFamily (G.annulusPins N (z i)) (fun _ => poleSpin true) s v=poleSpin true from
      glueFamily_in _ _ _ ⟨v,hp⟩]
    simp only [blockSpin,hB,↓reduceDIte]
  · have hB : G.restrictVertex _ v∉G.allAnnulusPins N z := by
      intro h
      exact hp ((local_centerPins_iff N hN z hz v.val i (Finset.mem_filter.mp v.property).2).mp h)
    have hl : G.annulusVertexLabel N z (G.restrictVertex _ v)=some i :=
      (centerLabel_some_iff N z hz v.val i).mpr (Finset.mem_filter.mp v.property).2
    rw [show glueFamily (G.annulusPins N (z i)) (fun _ => poleSpin true) s v=s ⟨v,hp⟩ from
      glueFamily_out _ _ _ ⟨v,hp⟩]
    simp only [blockSpin,hB,hl,↓reduceDIte]
    rfl

theorem annulus_blockMean (G : LatticeGraph) (b : G.edges → ℝ) (N : ℤ) (hN : 0≤N)
    (z : K → Site) (hz : SeparatedCenters N z) (i : K)
    (f : ((G.annulusGraph N (z i)).edges → Bool) → ℝ) :
    poleBondMean (fun e : (G.annulusGraph N (z i)).edges => e.val.1) (fun e => e.val.2)
      (G.annulusCoupling b N (z i)) (G.annulusPins N (z i)) (fun _ => true) f=
    blockBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b
      (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (G.annulusEdgeLabel N z) (some i)
      (fun η => f (arrowEquiv (G.annulusEdgesEquiv N z hz i) η)) := by
  apply blockBondMean_local (fun e : G.edges => e.val.1) (fun e => e.val.2) b
    (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (G.annulusEdgeLabel N z) (some i)
    (fun e : (G.annulusGraph N (z i)).edges => e.val.1) (fun e => e.val.2)
    (G.annulusCoupling b N (z i)) (G.annulusPins N (z i)) (G.annulusFreeEquiv N hN z hz i)
    (G.annulusEdgesEquiv N z hz i)
  · intro e; rfl
  · intro s e
    exact G.annulus_blockSpin N hN z hz i s (G.annulusEdgesEquiv N z hz i e).val.1
  · intro s e
    exact G.annulus_blockSpin N hN z hz i s (G.annulusEdgesEquiv N z hz i e).val.2

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.MixedWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

variable {n : ℕ}

omit [Fintype V] [Fintype E] in
theorem operator_smul_pow (r : ℝ) (M : SpinOperator n) (k : ℕ) :
    (r • M)^k = r^k • M^k := by
  induction k with
  | zero => simp only [pow_zero, one_smul]
  | succ k ih =>
    rw [pow_succ, ih, Algebra.smul_mul_assoc (r^k) (M^k) (r • M),
      Algebra.mul_smul_comm r (M^k) M, smul_smul (r^k) r (M^k*M),
      ← pow_succ, ← pow_succ]

attribute [local fun_prop] continuous_energy

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ObservableBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [NeZero n]

@[simp] theorem averageLinear_const (S : SpinSystem n V E) (c : ℝ) :
    S.averageLinear (ContinuousMap.const _ c) = c := S.average_const c

@[simp] theorem averageLinear_one (S : SpinSystem n V E) : S.averageLinear 1 = 1 :=
  S.average_const 1

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SecondGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem secondAxisResponse_integral (S : SpinSystem 3 V E) (u : E → ℝ) :
    S.secondAxisResponse u u =
      (∫ σ, S.secondWeight (fun e => u e • axisC) 0 σ ∂S.reference) / S.Z (fun _ => 1) := by
  unfold secondAxisResponse average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  have hz (e : E) : (0 : ℝ) • (u e • axisC) = 0 := zero_smul ℝ (u e • axisC)
  simp only [secondWeight, twistEnergy, hz, NormedSpace.exp_zero, one_mul,
    pow_zero, pow_one]
  have hp (e : E) : (u e • axisC)^2 = (u e*u e) • axisC^2 := by
    rw [operator_smul_pow, sq]
  simp only [hp, pow_two]
  ring

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AxisRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Real
namespace ClassicalON

theorem axisC_cube : axisC^3 = -axisC := by
  rw [axisC,← map_pow,← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisMatrixC,pow_succ,Matrix.mul_apply,Fin.sum_univ_succ]

theorem axisC_sq_mul : axisC^2*axisC = -axisC := by
  rw [← pow_succ,axisC_cube]

theorem axis_smul_mul (r : ℝ) (A B : SpinOperator 3) : (r • A)*B = r • (A*B) :=
  Algebra.smul_mul_assoc r A B

theorem axis_mul_smul (r : ℝ) (A B : SpinOperator 3) : A*(r • B) = r • (A*B) :=
  Algebra.mul_smul_comm r A B

theorem axisPolynomial_derivative (t : ℝ) :
    HasDerivAt axisPolynomial (axisPolynomial t*axisC) t := by
  have h := ((hasDerivAt_const t (1:SpinOperator 3)).add ((Real.hasDerivAt_sin t).smul_const axisC)).add
    (((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)).smul_const (axisC^2))
  apply h.congr_deriv
  change 0 + (Real.cos t) • axisC + (0 - -Real.sin t) • axisC^2 = axisPolynomial t*axisC
  simp only [axisPolynomial,add_mul,one_mul,axis_smul_mul,axisC_sq_mul,← pow_two]
  module

theorem axisPolynomial_commute (t : ℝ) : Commute (axisPolynomial t) axisC := by
  change axisPolynomial t*axisC = axisC*axisPolynomial t
  simp only [axisPolynomial,add_mul,mul_add,one_mul,mul_one,axis_smul_mul,
    axis_mul_smul,← pow_succ,← pow_succ']

theorem exp_axisC (t : ℝ) : NormedSpace.exp (t • axisC)=axisPolynomial t := by
  let f := fun t : ℝ => NormedSpace.exp (t • (-axisC))*axisPolynomial t
  have hd (t : ℝ) : HasDerivAt f 0 t := by
    apply ((hasDerivAt_exp_smul_const (-axisC) t).mul (axisPolynomial_derivative t)).congr_deriv
    rw [mul_assoc,neg_mul axisC (axisPolynomial t),← (axisPolynomial_commute t).eq]
    simp
  have he : f t = f 0 := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0
  have h0 : f 0 = 1 := by simp [f,axisPolynomial,zero_smul ℝ axisC,zero_smul ℝ (axisC^2)]
  rw [h0] at he
  have hm := congrArg (fun Q : SpinOperator 3 => NormedSpace.exp (t • axisC)*Q) he
  dsimp only [f] at hm
  rw [← mul_assoc,smul_neg,← NormedSpace.exp_add_of_commute (Commute.refl (t • axisC)).neg_right,
    add_neg_cancel,NormedSpace.exp_zero,mul_one,one_mul] at hm
  exact hm.symm

theorem exp_axisC_periodic : Function.Periodic (fun t : ℝ => NormedSpace.exp (t • axisC)) (2*Real.pi) := by
  intro t
  simp [exp_axisC,axisPolynomial,Real.sin_add_two_pi,Real.cos_add_two_pi]

theorem exp_axisC_pi_apply (v : EuclideanSpace ℝ (Fin 3)) :
    NormedSpace.exp (Real.pi • axisC) v = WithLp.toLp 2 ![-v 0,-v 1,v 2] := by
  rw [exp_axisC]
  ext i
  fin_cases i <;> simp [axisPolynomial,axisC_apply,pow_two] <;> ring

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PotentialRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
namespace ClassicalON
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem gauge_potential_shift (S : SpinSystem 3 V E) (f : V → ℝ) (t u : ℝ) :
    S.gauge (fun e => NormedSpace.exp (u • S.potentialOperators f e)) (potentialRotation f t) =
      (fun e => NormedSpace.exp ((t+u) • S.potentialOperators f e)) := by
  funext e
  apply ContinuousLinearMap.ext
  intro v
  change (potentialRotation f t (S.left e)).symm
    (NormedSpace.exp (u • S.potentialOperators f e) (potentialRotation f t (S.right e) v)) = _
  simp only [potentialRotation,rotationExp_symm_apply,rotationExp_apply,potentialOperators,
    smul_smul,← neg_smul (t*f (S.left e)) axisC]
  rw [← mul_apply_eq_comp,← mul_apply_eq_comp,← exp_smul_add,← exp_smul_add]
  apply congrArg (fun r : ℝ => NormedSpace.exp (r • axisC) v)
  simp only [differential]
  ring

theorem potential_shift_Z (S : SpinSystem 3 V E) (f : V → ℝ) (t u : ℝ) :
    S.Z (fun e => NormedSpace.exp ((t+u) • S.potentialOperators f e)) =
      (S.rotatePotential f t).Z (fun e => NormedSpace.exp (u • S.potentialOperators f e)) := by
  rw [← S.gauge_potential_shift]
  exact S.Z_gauge _ _

theorem potential_shift_first (S : SpinSystem 3 V E) (f : V → ℝ) (t u : ℝ) :
    (∫ σ, S.firstWeight (S.potentialOperators f) (t+u) σ ∂S.reference) =
      ∫ σ, (S.rotatePotential f t).firstWeight (S.potentialOperators f) u σ ∂(S.rotatePotential f t).reference := by
  have h := (S.hasDerivAt_twistZ (S.potentialOperators f) (t+u)).comp u
    ((hasDerivAt_id u).const_add t)
  simp only [mul_one] at h
  have he : (fun v => S.Z (fun e => NormedSpace.exp ((t+v) • S.potentialOperators f e))) =
      (fun v => (S.rotatePotential f t).Z (fun e => NormedSpace.exp (v • S.potentialOperators f e))) :=
    funext fun v => S.potential_shift_Z f t v
  change HasDerivAt (fun v => S.Z (fun e => NormedSpace.exp ((t+v) • S.potentialOperators f e))) _ u at h
  rw [he] at h
  exact h.unique ((S.rotatePotential f t).hasDerivAt_twistZ (S.potentialOperators f) u)

theorem potential_shift_second (S : SpinSystem 3 V E) (f : V → ℝ) (t u : ℝ) :
    (∫ σ, S.secondWeight (S.potentialOperators f) (t+u) σ ∂S.reference) =
      ∫ σ, (S.rotatePotential f t).secondWeight (S.potentialOperators f) u σ ∂(S.rotatePotential f t).reference := by
  have h := (S.hasDerivAt_firstVariation (S.potentialOperators f) (t+u)).comp u
    ((hasDerivAt_id u).const_add t)
  simp only [mul_one] at h
  have he : (fun v => ∫ σ, S.firstWeight (S.potentialOperators f) (t+v) σ ∂S.reference) =
      (fun v => ∫ σ, (S.rotatePotential f t).firstWeight (S.potentialOperators f) v σ ∂(S.rotatePotential f t).reference) :=
    funext fun v => S.potential_shift_first f t v
  change HasDerivAt (fun v => ∫ σ, S.firstWeight (S.potentialOperators f) (t+v) σ ∂S.reference) _ u at h
  rw [he] at h
  exact h.unique ((S.rotatePotential f t).hasDerivAt_firstVariation (S.potentialOperators f) u)

theorem potential_second_response (S : SpinSystem 3 V E) (f : V → ℝ) (t : ℝ) :
    (∫ σ, S.secondWeight (S.potentialOperators f) t σ ∂S.reference) /
      S.Z (fun e => NormedSpace.exp (t • S.potentialOperators f e)) =
      (S.rotatePotential f t).secondAxisResponse (S.differential f) (S.differential f) := by
  have hZ := S.potential_shift_Z f t 0
  have h2 := S.potential_shift_second f t 0
  simp only [add_zero,zero_smul ℝ (S.potentialOperators f _),NormedSpace.exp_zero] at hZ
  simp only [add_zero] at h2
  rw [hZ,h2,(S.rotatePotential f t).secondAxisResponse_integral]
  rfl

omit [Fintype V] [Fintype E] in
theorem spinRotation_potential_periodic (f : V → ℝ) (x : V)
    (h : f x=0 ∨ f x=1) (s : Spin 3) (t : ℝ) :
    spinRotation (potentialRotation f (t+2*Real.pi) x) s =
      spinRotation (potentialRotation f t x) s := by
  apply Subtype.ext
  simp only [spinRotation_val,potentialRotation,rotationExp_apply]
  rcases h with h | h
  · simp only [h,mul_zero]
  · simp only [h,mul_one,exp_axisC_periodic t]

omit [Fintype V] [Fintype E] in
theorem rotatePotential_periodic (S : SpinSystem 3 V E) (f : V → ℝ)
    (hP : ∀ x s, S.pin x=some s → f x=0 ∨ f x=1) :
    Function.Periodic (S.rotatePotential f) (2*Real.pi) := by
  intro t
  have hpin : (S.rotatePotential f (t+2*Real.pi)).pin = (S.rotatePotential f t).pin := by
    funext x
    apply Option.map_congr
    intro s hs
    exact spinRotation_potential_periodic f x (hP x s hs) s t
  exact congrArg (fun p => SpinSystem.mk S.left S.right S.strength p) hpin

end SpinSystem
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PeriodicODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace ClassicalON

theorem lower_second_derivative_tangent (f f' f'' : ℝ → ℝ) (a c x : ℝ)
    (h1 : ∀ t, HasDerivAt f (f' t) t) (h2 : ∀ t, HasDerivAt f' (f'' t) t)
    (hsec : ∀ t, -c ≤ f'' t) (ha : f' a = 0) :
    f a - c/2*(x-a)^2 ≤ f x := by
  let g := fun t => f t + c/2*(t-a)^2
  let g' := fun t => f' t + c*(t-a)
  let g'' := fun t => f'' t + c
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    convert (h1 t).add ((((hasDerivAt_id t).sub_const a).pow 2).const_mul (c/2)) using 1 <;>
      first | rfl | (change f' t + c * (t-a) = f' t + c/2*(2*(t-a)^(2-1)*1); ring)
  have hg' (t : ℝ) : HasDerivAt g' (g'' t) t := by
    convert (h2 t).add (((hasDerivAt_id t).sub_const a).const_mul c) using 1 <;>
      first | rfl | (change f'' t + c = f'' t + c*1; ring)
  have hcv : ConvexOn ℝ univ g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).hasDerivWithinAt)
      (fun t _ => (hg' t).hasDerivWithinAt)
    intro t _
    dsimp only [g'']
    linarith [hsec t]
  have hd : derivWithin g (Ioi a) a = 0 := by
    rw [(hg a).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi a)]
    simp [g', ha]
  have hm := hcv.isMinOn_of_rightDeriv_eq_zero (by simp) hd (mem_univ x)
  change f a + c/2*(a-a)^2 ≤ f x + c/2*(x-a)^2 at hm
  nlinarith

theorem periodic_ode_ratio (f f' f'' : ℝ → ℝ) (P δ : ℝ) (hP : 0 < P) (hδ : 0 ≤ δ)
    (hper : Function.Periodic f P) (hfpos : ∀ t, 0 < f t)
    (h1 : ∀ t, HasDerivAt f (f' t) t) (h2 : ∀ t, HasDerivAt f' (f'' t) t)
    (hode : ∀ t, -(δ*f t) ≤ f'' t) (x y : ℝ) :
    1 - δ*P^2/2 ≤ f x / f y := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t => (h1 t).continuousAt
  obtain ⟨a, ha, ham⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) P).Nonempty from ⟨0, le_rfl, hP.le⟩) hf.continuousOn
  have hmax (t : ℝ) : f t ≤ f a := by
    obtain ⟨s, hs, he⟩ := hper.exists_mem_Ioc hP t 0
    rw [he]
    exact ham ⟨hs.1.le, by simpa only [zero_add] using hs.2⟩
  have halocal : IsLocalMax f a := Filter.Eventually.of_forall hmax
  have hstationary : f' a = 0 := by rw [← (h1 a).deriv, halocal.deriv_eq_zero]
  have hsec (t : ℝ) : -(δ*f a) ≤ f'' t :=
    (neg_le_neg (mul_le_mul_of_nonneg_left (hmax t) hδ)).trans (hode t)
  obtain ⟨s, hs, he⟩ := hper.exists_mem_Ioc hP x a
  have ht := lower_second_derivative_tangent f f' f'' a (δ*f a) s h1 h2 hsec hstationary
  have hdist : (s-a)^2 ≤ P^2 := by
    apply pow_le_pow_left₀ (sub_nonneg.mpr hs.1.le)
    linarith [hs.2]
  have hnear : f a*(1-δ*P^2/2) ≤ f x := by
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hdist (div_nonneg (mul_nonneg hδ (hfpos a).le) (by norm_num : (0:ℝ) ≤ 2))
    nlinarith
  apply (le_div_iff₀ (hfpos y)).mpr
  by_cases hc : 0 ≤ 1-δ*P^2/2
  · exact (mul_le_mul_of_nonneg_left (hmax y) hc).trans (by simpa only [mul_comm] using hnear)
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (hfpos y).le).trans (hfpos x).le

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PeriodicPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem potential_partition_ratio (S : SpinSystem 3 V E) (f : V → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ x s, S.pin x=some s → f x=0 ∨ f x=1)
    (hR : ∀ t, -(S.rotatePotential f t).secondAxisResponse (S.differential f) (S.differential f) ≤ δ)
    (x y : ℝ) :
    1-δ*(2*Real.pi)^2/2 ≤ (S.rotatePotential f x).Z (fun _ => 1) /
      (S.rotatePotential f y).Z (fun _ => 1) := by
  let A := S.potentialOperators f
  let F := fun t : ℝ => S.Z (fun e => NormedSpace.exp (t • A e))
  let F' := fun t => ∫ σ, S.firstWeight A t σ ∂S.reference
  let F'' := fun t => ∫ σ, S.secondWeight A t σ ∂S.reference
  have hZ (t : ℝ) : F t=(S.rotatePotential f t).Z (fun _ => 1) := by
    have h := S.potential_shift_Z f t 0
    simpa only [add_zero,zero_smul ℝ (S.potentialOperators f _),NormedSpace.exp_zero] using h
  have hper : Function.Periodic F (2*Real.pi) := by
    intro t
    rw [hZ,hZ,S.rotatePotential_periodic f hP t]
  have hpos (t : ℝ) : 0<F t := S.Z_pos _
  have hode (t : ℝ) : -(δ*F t) ≤ F'' t := by
    have hr := hR t
    rw [← S.potential_second_response] at hr
    change -(F'' t/F t) ≤ δ at hr
    rw [← neg_div,div_le_iff₀ (hpos t)] at hr
    linarith
  have h := ClassicalON.periodic_ode_ratio F F' F'' (2*Real.pi) δ (by positivity) hδ
    hper hpos (S.hasDerivAt_twistZ A) (S.hasDerivAt_firstVariation A) hode x y
  simpa only [hZ] using h

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ClassicalON.LatticeGraph

theorem thetaPotential_binary_pins (G : LatticeGraph) (k : ℕ)
    (P : G.vertices → Option (Spin 3)) (hP : G.BoundaryPins k 3 P) :
    ∀ x s, P x=some s → G.thetaPotential k x=0 ∨ G.thetaPotential k x=1 := by
  intro x s hs
  rcases hP x s hs with h | h
  · exact Or.inr (squareTheta_one _ h.1 h.2)
  · exact Or.inl (squareTheta_zero _ h)

theorem rotatedBoundaryPins_boundary (G : LatticeGraph) (k : ℕ)
    (P : G.vertices → Option (Spin 3)) (hP : G.BoundaryPins k 3 P) (t : ℝ) :
    G.BoundaryPins k 3 (G.rotatedBoundaryPins k P t) := by
  intro x s hs
  cases hp : P x with
  | none => simp [rotatedBoundaryPins,hp] at hs
  | some u => exact hP x u hp

theorem annulus_partition_ratio (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ, 4 ≤ k ∧ ∀ (G : LatticeGraph), G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ), (∀ e,0 ≤ b e ∧ b e ≤ β) →
      ∀ (P : G.vertices → Option (Spin 3)), G.BoundaryPins k 3 P → ∀ x y : ℝ,
      1-ε ≤ (G.spinSystem 3 b (G.rotatedBoundaryPins k P x)).Z (fun _ => 1) /
        (G.spinSystem 3 b (G.rotatedBoundaryPins k P y)).Z (fun _ => 1) := by
  let δ := 2*ε/(2*Real.pi)^2
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨k,hk,hR⟩ := annulus_response_small β hβ δ hδ
  refine ⟨k,hk,?_⟩
  intro G hG b hb P hP x y
  have hp := G.thetaPotential_binary_pins k P hP
  have hr (t : ℝ) : -((G.spinSystem 3 b P).rotatePotential (G.thetaPotential k) t).secondAxisResponse
      ((G.spinSystem 3 b P).differential (G.thetaPotential k))
      ((G.spinSystem 3 b P).differential (G.thetaPotential k)) ≤ δ := by
    exact hR G hG b hb (G.rotatedBoundaryPins k P t) (G.rotatedBoundaryPins_boundary k P hP t)
  have h := (G.spinSystem 3 b P).potential_partition_ratio (G.thetaPotential k) δ hδ.le hp hr x y
  have he : δ*(2*Real.pi)^2/2=ε := by dsimp [δ]; field_simp
  rw [he] at h
  exact h

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.PoleCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem crossingIndicator_nonneg (left right : E → V) (I O : Set V) (η : E → Bool) :
    0≤crossingIndicator left right I O η := by unfold crossingIndicator; split_ifs <;> positivity

omit [Fintype V] [Fintype E] in
theorem crossingIndicator_monotone (left right : E → V) (I O : Set V) :
    Monotone (crossingIndicator left right I O) := by
  intro η ξ hη
  have h : bondCrossing left right I O η → bondCrossing left right I O ξ := by
    rintro ⟨x,hx,y,hy,hxy⟩
    exact ⟨x,hx,y,hy,bondConnected_mono left right x y hη hxy⟩
  unfold crossingIndicator
  split_ifs <;> simp_all

theorem pinnedBondNumerator_sub (μ : Measure Amplitude) [IsFiniteMeasure μ]
    (left right : E → V) (b : E → ℝ) (B : Set V) (f g : (E → Bool) → ℝ) :
    pinnedBondNumerator μ left right b B (fun η => f η-g η)=
      pinnedBondNumerator μ left right b B f-pinnedBondNumerator μ left right b B g := by
  unfold pinnedBondNumerator
  simp only [mul_sub,Finset.sum_sub_distrib]
  apply integral_sub
  all_goals exact compact_integrable ((continuous_pinWeightedSum _ _ _ _ _).comp
    ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id)))

theorem pole_crossing_ratio (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (I O : Set V) (hIO : Disjoint I O) :
    poleBondMean left right b (I∪O) (fun _ => true) (crossingIndicator left right I O)=
      1-(poleSystem left right b (I∪O) (fun v => layerSigns I v)).Z (fun _ => 1)/
        (poleSystem left right b (I∪O) (fun _ => true)).Z (fun _ => 1) := by
  rw [poleBondMean_eq_pinnedBondMean,layer_Z _ _ _ _ _ hIO,positive_Z,
    mul_div_mul_left _ _ (ne_of_gt (pinNormalization_pos (I∪O)))]
  have he : (fun η : E → Bool => if bondCrossing left right I O η then (0:ℝ) else 1)=
      (fun η => 1-crossingIndicator left right I O η) := by
    funext η
    unfold crossingIndicator
    split_ifs <;> norm_num
  rw [he,pinnedBondNumerator_sub,sub_div,div_self
    (ne_of_gt (pinnedBondNumerator_one_pos sphericalAmplitudeLaw _ _ _ hb _))]
  unfold pinnedBondMean
  ring

theorem freeBondMean_le_poleBondMean (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (B : Set V) (f : (E → Bool) → ℝ) (hf : ∀ η,0≤f η) (hm : Monotone f) :
    freeBondMean left right b f≤poleBondMean left right b B (fun _ => true) f := by
  rw [freeBondMean_eq_jointBondMean _ _ _ hb,poleBondMean_eq_pinnedBondMean]
  exact jointBond_le_pinnedBond _ _ _ _ hb _ _ hf hm

omit [Fintype V] [Fintype E] in
theorem rotate_pole (a : V → ℝ) (x : V) (h : a x=1) :
    spinRotation (SpinSystem.potentialRotation a Real.pi x) (poleSpin true)=poleSpin false := by
  apply Subtype.ext
  change NormedSpace.exp ((Real.pi*a x) • axisC) (poleSpin true).val=(poleSpin false).val
  rw [h,mul_one,exp_axisC_pi_apply]
  ext i
  fin_cases i <;> simp [poleSpin,cylindricalSpin,transverseAmplitude,signValue]

omit [Fintype V] [Fintype E] in
theorem rotation_zero_potential (a : V → ℝ) (t : ℝ) (x : V) (h : a x=0) (s : Spin 3) :
    spinRotation (SpinSystem.potentialRotation a t x) s=s := by
  apply Subtype.ext
  change NormedSpace.exp ((t*a x) • axisC) s.val=s.val
  simp [h,zero_smul ℝ axisC]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph

theorem inner_outer_disjoint (G : LatticeGraph) (k : ℕ) : Disjoint (G.innerSet k) (G.outerSet k) := by
  apply Set.disjoint_left.mpr
  intro x hx ho
  rcases ho with h | h <;> linarith [hx.1,hx.2]

theorem positiveLayerPins_boundary (G : LatticeGraph) (k : ℕ) (I O : Set G.vertices)
    (hI : I⊆G.innerSet k) (hO : O⊆G.outerSet k) :
    G.BoundaryPins k 3 (G.positiveLayerPins I O) := by
  intro x s hs
  by_cases h : x∈I∪O
  · rcases h with h | h
    · exact Or.inl (hI h)
    · exact Or.inr (hO h)
  · simp only [positiveLayerPins,poleSystem,h,↓reduceDIte] at hs
    cases hs

theorem rotate_positiveLayerPins_pi (G : LatticeGraph) (k : ℕ) (I O : Set G.vertices)
    (hI : I⊆G.innerSet k) (hO : O⊆G.outerSet k) :
    G.rotatedBoundaryPins k (G.positiveLayerPins I O) Real.pi=
      (poleSystem (fun e : G.edges => e.val.1) (fun e => e.val.2) (fun _ => 0) (I∪O)
        (fun v => layerSigns I v)).pin := by
  funext x
  by_cases hx : x∈I∪O
  · have htheta : G.thetaPotential k x=if x∈I then 1 else 0 := by
      by_cases h : x∈I
      · simp only [h,ite_true,thetaPotential]
        exact squareTheta_one _ (hI h).1 (hI h).2
      · simp only [h,ite_false,thetaPotential]
        exact squareTheta_zero _ (hO (hx.resolve_left h))
    simp only [rotatedBoundaryPins,positiveLayerPins,poleSystem,hx,↓reduceDIte,Option.map_some]
    by_cases hi : x∈I
    · rw [show layerSigns I x=false by simp [layerSigns,hi]]
      congr 1
      exact rotate_pole _ _ (by simpa [hi] using htheta)
    · rw [show layerSigns I x=true by simp [layerSigns,hi]]
      congr 1
      exact rotation_zero_potential _ _ _ (by simpa [hi] using htheta) _
  · simp only [rotatedBoundaryPins,positiveLayerPins,poleSystem,hx,↓reduceDIte,Option.map_none]

theorem rotate_positiveLayerPins_zero (G : LatticeGraph) (k : ℕ) (I O : Set G.vertices) :
    G.rotatedBoundaryPins k (G.positiveLayerPins I O) 0=G.positiveLayerPins I O := by
  funext x
  simp only [rotatedBoundaryPins]
  cases hp : G.positiveLayerPins I O x with
  | none => rfl
  | some s =>
    simp only [Option.map_some]
    congr 1
    apply Subtype.ext
    change NormedSpace.exp ((0*G.thetaPotential k x) • axisC) s.val=s.val
    simp [zero_smul ℝ axisC]

theorem annulus_crossing_small (β : ℝ) (hβ : 0≤β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ,4≤k ∧ ∀ (G : LatticeGraph),G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ (I O : Set G.vertices),I⊆G.innerSet k → O⊆G.outerSet k →
      poleBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (I∪O) (fun _ => true)
        (crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O)≤ε := by
  obtain ⟨k,hk,hr⟩ := annulus_partition_ratio β hβ ε hε
  refine ⟨k,hk,?_⟩
  intro G hG b hb I O hI hO
  have hd : Disjoint I O := (G.inner_outer_disjoint k).mono hI hO
  rw [pole_crossing_ratio _ _ _ (fun e => (hb e).1) _ _ hd]
  have h := hr G hG b hb (G.positiveLayerPins I O)
    (G.positiveLayerPins_boundary k I O hI hO) Real.pi 0
  rw [G.rotate_positiveLayerPins_pi k I O hI hO,G.rotate_positiveLayerPins_zero k I O] at h
  change 1-ε≤(poleSystem _ _ b (I∪O) (fun v => layerSigns I v)).Z (fun _ => 1)/
    (poleSystem _ _ b (I∪O) (fun _ => true)).Z (fun _ => 1) at h
  linarith

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CenteredAnnulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph

theorem centered_crossing_small (β : ℝ) (hβ : 0≤β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ,4≤k ∧ ∀ (G : LatticeGraph) (z : Site),
      (∀ v : G.vertices,siteRadius z v.val≤2*(2^k:ℕ)) →
      ∀ (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ (I O : Set G.vertices),(∀ v∈I,siteRadius z v.val≤(2^k:ℕ)) →
        (∀ v∈O,2*(2^k:ℕ)≤ siteRadius z v.val) →
      poleBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (I∪O) (fun _ => true)
        (crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O)≤ε := by
  obtain ⟨k,hk,hsmall⟩ := annulus_crossing_small β hβ ε hε
  refine ⟨k,hk,?_⟩
  intro G z hG b hb I O hI hO
  let H := G.translate z
  let ev : G.vertices ≃ H.vertices := G.translateVertexEquiv z
  let ee : G.edges ≃ H.edges := G.translateEdgeEquiv z
  let I' : Set H.vertices := ev.symm ⁻¹' I
  let O' : Set H.vertices := ev.symm ⁻¹' O
  have hi (v : G.vertices) : ev v∈I' ↔ v∈I := by simp only [I',mem_preimage,Equiv.symm_apply_apply]
  have ho (v : G.vertices) : ev v∈O' ↔ v∈O := by simp only [O',mem_preimage,Equiv.symm_apply_apply]
  have hl (e : G.edges) : (ee e).val.1=ev e.val.1 := rfl
  have hr (e : G.edges) : (ee e).val.2=ev e.val.2 := rfl
  have he (η : H.edges → Bool) :
      crossingIndicator (fun e : H.edges => e.val.1) (fun e => e.val.2) I' O' η=
        crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O (fun e => η (ee e)) := by
    unfold crossingIndicator
    rw [bondCrossing_reindex ev ee _ _ _ _ hl hr I O I' O' hi ho]
  have hmean := poleBondMean_reindex ev ee (fun e : G.edges => e.val.1) (fun e => e.val.2)
    (fun e : H.edges => e.val.1) (fun e => e.val.2) b (fun e => b (ee.symm e)) (I∪O) (I'∪O')
    (fun e => by simp) hl hr (fun v => by simp only [mem_union,hi,ho])
    (crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O)
  have hbox : H.WithinDyadicBox k := by
    intro v
    obtain ⟨v,rfl⟩ := ev.surjective v
    change |v.val.1-z.1|≤2*(2^k:ℕ) ∧ |v.val.2-z.2|≤2*(2^k:ℕ)
    exact (siteRadius_le_iff z v.val _).mp (hG v)
  have hinner : I'⊆H.innerSet k := by
    intro v hv
    obtain ⟨v,rfl⟩ := ev.surjective v
    have hv' := (siteRadius_le_iff z v.val _).mp (hI v ((hi v).mp hv))
    have hn : (0:ℝ)<2^k := by positivity
    change |((v.val.1-z.1:ℤ):ℝ)/(2:ℝ)^k|≤1 ∧ |((v.val.2-z.2:ℤ):ℝ)/(2:ℝ)^k|≤1
    simp only [abs_div,abs_of_pos hn,div_le_one hn]
    exact ⟨by exact_mod_cast hv'.1,by exact_mod_cast hv'.2⟩
  have houter : O'⊆H.outerSet k := by
    intro v hv
    obtain ⟨v,rfl⟩ := ev.surjective v
    have hv' := hO v ((ho v).mp hv)
    have hn : (0:ℝ)<2^k := by positivity
    change 2≤|((v.val.1-z.1:ℤ):ℝ)/(2:ℝ)^k| ∨ 2≤|((v.val.2-z.2:ℤ):ℝ)/(2:ℝ)^k|
    simp only [abs_div,abs_of_pos hn,le_div_iff₀ hn]
    change _≤ max _ _ at hv'
    rcases le_max_iff.mp hv' with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hs := hsmall H hbox (fun e => b (ee.symm e)) (fun e => hb _) I' O' hinner houter
  rw [show crossingIndicator (fun e : H.edges => e.val.1) (fun e => e.val.2) I' O'=
    (fun η => crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O
      (fun e => η (ee e))) from funext he] at hs
  rwa [hmean] at hs

theorem local_annulus_small (β : ℝ) (hβ : 0≤β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ,4≤k ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ z : Site,let H := G.annulusGraph (2^k:ℕ) z
      poleBondMean (fun e : H.edges => e.val.1) (fun e => e.val.2) (G.annulusCoupling b (2^k:ℕ) z)
        (G.annulusPins (2^k:ℕ) z) (fun _ => true)
        (crossingIndicator (fun e : H.edges => e.val.1) (fun e => e.val.2)
          (G.annulusInner (2^k:ℕ) z) (G.annulusOuter (2^k:ℕ) z))≤ε := by
  obtain ⟨k,hk,hs⟩ := centered_crossing_small β hβ ε hε
  refine ⟨k,hk,?_⟩
  intro G b hb z
  apply hs (G.annulusGraph (2^k:ℕ) z) z
  · intro v
    exact ((Finset.mem_filter.mp v.property).2).2
  · intro e
    exact hb (G.restrictEdge _ e)
  · intro v hv
    exact le_of_eq hv
  · intro v hv
    exact le_of_eq hv.symm

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SpinCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem jointBondMean_mono (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f g : (V → Amplitude) → (E → Bool) → ℝ}
    (hf : ∀ η,Continuous (fun r => f r η)) (hg : ∀ η,Continuous (fun r => g r η))
    (hfg : ∀ r η,f r η≤g r η) : jointBondMean μ left right b f≤jointBondMean μ left right b g := by
  apply weightedMean_mono (continuous_amplitudeDensity _ _ _) (amplitudeDensity_pos _ _ _)
    (continuous_bondConditionalMean _ _ _ hb hf) (continuous_bondConditionalMean _ _ _ hb hg)
  intro r
  exact finiteMean_mono (bondWeight_nonneg _ _ (amplitudeBondParam_nonneg _ _ _ hb r)) (hfg r)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.BondMeanOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} {K : Type uK} [Fintype V] [Fintype E] [Fintype K]

theorem freeBondMean_mono (l r : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    {f g : (E → Bool) → ℝ} (hfg : ∀ η,f η≤g η) : freeBondMean l r b f≤freeBondMean l r b g := by
  rw [freeBondMean_eq_jointBondMean _ _ _ hb,freeBondMean_eq_jointBondMean _ _ _ hb]
  exact jointBondMean_mono _ _ _ _ hb (fun _ => continuous_const) (fun _ => continuous_const) (fun _ η => hfg η)

theorem freeBondMean_sum (l r : E → V) (b : E → ℝ) (f : K → (E → Bool) → ℝ) :
    freeBondMean l r b (fun η => ∑ k,f k η)=∑ k,freeBondMean l r b (f k) := by
  unfold freeBondMean freeSpinMean weightedMean
  simp_rw [Finset.mul_sum]
  rw [show (fun s : V → Spin 3 => ∑ η,∑ k,Real.exp (freeSpinEnergy 3 l r b s)*
      (spinBondWeight l r b s η*f k η))=
    (fun s => ∑ k,∑ η,Real.exp (freeSpinEnergy 3 l r b s)*(spinBondWeight l r b s η*f k η)) by
      funext s; rw [Finset.sum_comm]]
  rw [integral_finsetSum,Finset.sum_div]
  intro k _
  exact compact_integrable (continuous_finsetSum _ (fun η _ =>
    (continuous_freeSpinEnergy _ _ _ _).rexp.mul ((continuous_spinBondWeight _ _ _ _).mul continuous_const)))

theorem freeBondMean_one (l r : E → V) (b : E → ℝ) : freeBondMean l r b (fun _ => 1)=1 := by
  unfold freeBondMean freeSpinMean weightedMean
  simp only [mul_one,spinBondWeight_sum]
  exact div_self (ne_of_gt (compact_integral_pos (continuous_freeSpinEnergy 3 l r b).rexp (fun _ => Real.exp_pos _)))

omit [Fintype K] in
theorem blockBondMean_one (l r : E → V) (b : E → ℝ) (B : Set V) (label : V → K)
    (elabel : E → K) (k : K) : blockBondMean l r b B label elabel k (fun _ => 1)=1 := by
  have hs (s : BlockVertex B label k → Spin 3) :
      (∑ η,blockBondWeight l r b B label elabel k s η)=1 := by
    convert spinBondWeight_sum (fun e : {e // elabel e=k} => l e.val) (fun e => r e.val)
      (fun e => b e.val) (blockSpin B label k s) using 1; congr!
  unfold blockBondMean weightedMean
  simp only [mul_one,hs]
  apply div_self
  apply ne_of_gt
  exact compact_integral_pos
    ((continuous_freeSpinEnergy _ _ _ _).comp (continuous_blockSpin B label k)).rexp
      (fun _ => Real.exp_pos _)

omit [Fintype K] in
theorem blockBondMean_nonneg (l r : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (B : Set V) (label : V → K) (elabel : E → K) (k : K)
    {f : ({e // elabel e=k} → Bool) → ℝ} (hf : ∀ η,0≤f η) :
    0≤blockBondMean l r b B label elabel k f := by
  apply weightedMean_nonneg
    ((continuous_freeSpinEnergy _ _ _ _).comp (continuous_blockSpin B label k)).rexp
    (fun _ => Real.exp_pos _)
  intro s
  exact Finset.sum_nonneg (fun η _ => mul_nonneg (spinBondWeight_nonneg (fun e : {e // elabel e=k} => l e.val)
    (fun e => r e.val) (fun e => b e.val) (fun e => hb e.val) _ _) (hf η))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SeparatedAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK

noncomputable section
open Set
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph
variable {K : Type uK} [Fintype K]

omit [Fintype K] in
theorem annulusIndicator_nonneg (G : LatticeGraph) (N : ℤ) (z : Site) (η : G.edges → Bool) :
    0≤G.annulusIndicator N z η := crossingIndicator_nonneg _ _ _ _ _

omit [Fintype K] in
theorem annulusIndicator_monotone (G : LatticeGraph) (N : ℤ) (z : Site) :
    Monotone (G.annulusIndicator N z) := by
  intro η ξ h
  apply crossingIndicator_monotone
  intro e
  exact h (G.restrictEdge _ e)

omit [Fintype K] in
theorem annulusEdgesEquiv_symm_val (G : LatticeGraph) (N : ℤ) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) (e : (G.annulusGraph N (z i)).edges) :
    ((G.annulusEdgesEquiv N z hz i).symm e).val=G.restrictEdge _ e := by
  obtain ⟨e,rfl⟩ := (G.annulusEdgesEquiv N z hz i).surjective e
  simp only [Equiv.symm_apply_apply,annulusEdgesEquiv_restrictEdge]

theorem separated_annuli_factor (G : LatticeGraph) (b : G.edges → ℝ) (N : ℤ) (hN : 0≤N)
    (z : K → Site) (hz : SeparatedCenters N z)
    (f : (i : K) → ((G.annulusGraph N (z i)).edges → Bool) → ℝ) :
    poleBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (G.allAnnulusPins N z)
      (fun _ => true) (fun η => ∏ i,f i (fun e => η (G.restrictEdge _ e)))=
    ∏ i,poleBondMean (fun e : (G.annulusGraph N (z i)).edges => e.val.1) (fun e => e.val.2)
      (G.annulusCoupling b N (z i)) (G.annulusPins N (z i)) (fun _ => true) (f i) := by
  let F : (k : Option K) → ({e : G.edges // G.annulusEdgeLabel N z e=k} → Bool) → ℝ :=
    fun k => match k with
    | none => fun _ => 1
    | some i => fun η => f i (arrowEquiv (G.annulusEdgesEquiv N z hz i) η)
  have he (η : G.edges → Bool) : (∏ k,F k (fun e => η e.val))=
      ∏ i,f i (fun e => η (G.restrictEdge _ e)) := by
    rw [Fintype.prod_option]
    simp only [F,one_mul,arrowEquiv,Equiv.coe_fn_mk,annulusEdgesEquiv_symm_val]
  have hp := poleBondMean_blocks (fun e : G.edges => e.val.1) (fun e => e.val.2) b
    (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (G.annulusEdgeLabel N z)
    (fun e => G.annulus_left_label N hN z hz e) (fun e => G.annulus_right_label N hN z hz e) F
  simpa only [he,Fintype.prod_option,F,blockBondMean_one,one_mul,← G.annulus_blockMean b N hN z hz] using hp

theorem separated_annuli_small (β : ℝ) (hβ : 0≤β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ,4≤k ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ (K : Type) [Fintype K] (z : K → Site),SeparatedCenters (2^k:ℕ) z →
      freeBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b
        (fun η => ∏ i,G.annulusIndicator (2^k:ℕ) (z i) η)≤ε^Fintype.card K := by
  obtain ⟨k,hk,hs⟩ := local_annulus_small β hβ ε hε
  refine ⟨k,hk,?_⟩
  intro G b hb K _ z hz
  have hn : (0:ℤ)≤(2^k:ℕ) := by positivity
  apply le_trans (freeBondMean_le_poleBondMean _ _ _ (fun e => (hb e).1) (G.allAnnulusPins (2^k:ℕ) z)
    _ (fun η => Finset.prod_nonneg (fun i _ => G.annulusIndicator_nonneg _ _ η)) ?_)
  · rw [show (fun η => ∏ i,G.annulusIndicator (2^k:ℕ) (z i) η)=
      (fun η => ∏ i,crossingIndicator (fun e : (G.annulusGraph (2^k:ℕ) (z i)).edges => e.val.1)
        (fun e => e.val.2) (G.annulusInner (2^k:ℕ) (z i)) (G.annulusOuter (2^k:ℕ) (z i))
          (fun e => η (G.restrictEdge _ e))) from rfl]
    rw [G.separated_annuli_factor b _ hn z hz]
    calc
      _≤∏ _i : K,ε := by
        apply Finset.prod_le_prod
        · intro i _
          rw [G.annulus_blockMean b _ hn z hz i]
          exact blockBondMean_nonneg _ _ _ (fun e => (hb e).1) _ _ _ _
            (fun η => crossingIndicator_nonneg _ _ _ _ _)
        · intro i _
          exact hs G b hb (z i)
      _=ε^Fintype.card K := by simp
  · intro η ξ h
    apply Finset.prod_le_prod
    · intro i _; exact G.annulusIndicator_nonneg _ _ η
    · intro i _; exact G.annulusIndicator_monotone _ _ h

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical
namespace ClassicalON.LatticeGraph

theorem extendAnnulusSign_in (G : LatticeGraph) (N : ℤ) (z : Site)
    (s : (G.annulusGraph N z).vertices → Bool) (v : (G.annulusGraph N z).vertices) :
    G.extendAnnulusSign N z s (G.restrictVertex _ v)=s v := by
  simp only [extendAnnulusSign,show (G.restrictVertex _ v).val∈annulusSites N z from
    (Finset.mem_filter.mp v.property).2,↓reduceDIte]
  rfl

theorem extendAnnulusSign_inner (G : LatticeGraph) (N : ℤ) (hN : 0<N) (z : Site)
    (s : (G.annulusGraph N z).vertices → Bool)
    (hs : ∀ v∈G.annulusPins N z,s v=layerSigns (G.annulusInner N z) v)
    (v : G.vertices) (hv : siteRadius z v.val≤N) : G.extendAnnulusSign N z s v=false := by
  unfold extendAnnulusSign
  split_ifs with h
  · let w : (G.annulusGraph N z).vertices := ⟨v.val,Finset.mem_filter.mpr ⟨v.property,h⟩⟩
    have hw : w∈G.annulusInner N z := le_antisymm hv h.1
    have hh := hs w (Or.inl hw)
    simpa only [layerSigns,hw,ite_true] using hh
  · have hh : ¬2*N<siteRadius z v.val := by omega
    simp only [decide_eq_false hh]

theorem extendAnnulusSign_outer (G : LatticeGraph) (N : ℤ) (hN : 0<N) (z : Site)
    (s : (G.annulusGraph N z).vertices → Bool)
    (hs : ∀ v∈G.annulusPins N z,s v=layerSigns (G.annulusInner N z) v)
    (v : G.vertices) (hv : 2*N≤ siteRadius z v.val) : G.extendAnnulusSign N z s v=true := by
  unfold extendAnnulusSign
  split_ifs with h
  · let w : (G.annulusGraph N z).vertices := ⟨v.val,Finset.mem_filter.mpr ⟨v.property,h⟩⟩
    have hw : w∈G.annulusOuter N z := le_antisymm h.2 hv
    have hw' : w∉G.annulusInner N z := by change siteRadius z v.val≠N; omega
    have hh := hs w (Or.inr hw)
    simpa only [layerSigns,hw',ite_false] using hh
  · have hh : 2*N<siteRadius z v.val := by
      by_contra hn
      apply h
      change N≤ siteRadius z v.val ∧ siteRadius z v.val≤2*N
      omega
    simp only [decide_eq_true hh]

theorem extendAnnulusSign_compatible (G : LatticeGraph) (N : ℤ) (hN : 0<N) (z : Site)
    (η : G.edges → Bool) (s : (G.annulusGraph N z).vertices → Bool)
    (hs : s∈prescribedCompatibleSigns (fun e : (G.annulusGraph N z).edges => e.val.1)
      (fun e => e.val.2) (G.annulusPins N z) (layerSigns (G.annulusInner N z))
      (fun e => η (G.restrictEdge _ e))) :
    G.extendAnnulusSign N z s∈compatibleSigns (fun e : G.edges => e.val.1) (fun e => e.val.2) η := by
  intro e he
  have hstep := siteRadius_neighbor_step z (Or.inl (G.nearest e.val e.property))
  by_cases hl : siteRadius z e.val.1.val<N
  · rw [G.extendAnnulusSign_inner N hN z s hs.2 e.val.1 (by omega),
      G.extendAnnulusSign_inner N hN z s hs.2 e.val.2 (by omega)]
  by_cases hl' : 2*N<siteRadius z e.val.1.val
  · rw [G.extendAnnulusSign_outer N hN z s hs.2 e.val.1 (by omega),
      G.extendAnnulusSign_outer N hN z s hs.2 e.val.2 (by omega)]
  by_cases hr : siteRadius z e.val.2.val<N
  · rw [G.extendAnnulusSign_inner N hN z s hs.2 e.val.1 (by omega),
      G.extendAnnulusSign_inner N hN z s hs.2 e.val.2 (by omega)]
  by_cases hr' : 2*N<siteRadius z e.val.2.val
  · rw [G.extendAnnulusSign_outer N hN z s hs.2 e.val.1 (by omega),
      G.extendAnnulusSign_outer N hN z s hs.2 e.val.2 (by omega)]
  have h1 : e.val.1.val∈annulusSites N z := ⟨by omega,by omega⟩
  have h2 : e.val.2.val∈annulusSites N z := ⟨by omega,by omega⟩
  let e' := G.restrictEdgeEquiv (·∈annulusSites N z) ⟨e,h1,h2⟩
  have hcomp := hs.1 e' he
  rw [← G.extendAnnulusSign_in N z s e'.val.1,← G.extendAnnulusSign_in N z s e'.val.2] at hcomp
  exact hcomp

theorem annulus_crossing_of_connected (G : LatticeGraph) (N : ℤ) (hN : 0<N) (z : Site)
    (η : G.edges → Bool) (x y : G.vertices) (hx : siteRadius z x.val≤N) (hy : 2*N≤ siteRadius z y.val)
    (hxy : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y) :
    G.annulusIndicator N z η=1 := by
  have hd : Disjoint (G.annulusInner N z) (G.annulusOuter N z) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    change siteRadius z v.val=N at hv
    change siteRadius z v.val=2*N at hw
    omega
  have hc : bondCrossing (fun e : (G.annulusGraph N z).edges => e.val.1) (fun e => e.val.2)
      (G.annulusInner N z) (G.annulusOuter N z) (fun e => η (G.restrictEdge _ e)) := by
    by_contra hn
    obtain ⟨s,hs⟩ := (layerSigns_consistent_iff (fun e : (G.annulusGraph N z).edges => e.val.1)
      (fun e => e.val.2) _ _ hd _).mpr hn
    have he := compatibleSigns_connected _ _ η (G.extendAnnulusSign_compatible N hN z η s hs) hxy
    rw [G.extendAnnulusSign_inner N hN z s hs.2 x hx,G.extendAnnulusSign_outer N hN z s hs.2 y hy] at he
    cases he
  exact ite_eq_left hc

theorem annulus_crossing_of_component (G : LatticeGraph) (N : ℤ) (hN : 0<N)
    (η : G.edges → Bool) (x y w : G.vertices) (hfar : 4*N≤ siteRadius x.val y.val)
    (hxy : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y)
    (hxw : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x w)
    (z : Site) (hw : siteRadius z w.val≤N) : G.annulusIndicator N z η=1 := by
  have hout : 2*N≤ siteRadius z x.val ∨ 2*N≤ siteRadius z y.val := by
    have ht := siteRadius_triangle x.val z y.val
    rw [siteRadius_symm x.val z] at ht
    omega
  rcases hout with hx | hy
  · exact G.annulus_crossing_of_connected N hN z η w x hw hx (bondConnected_symm _ _ _ hxw)
  · exact G.annulus_crossing_of_connected N hN z η w y hw hy
      (bondConnected_trans _ _ _ (bondConnected_symm _ _ _ hxw) hxy)

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarsePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace ClassicalON.LatticeGraph

theorem fine_edge_radius (G : LatticeGraph) (η : G.edges → Bool) {v w : G.vertices}
    (h : (bondGraph (fun e : G.edges => e.val.1) (fun e => e.val.2) η).Adj v w) :
    siteRadius v.val w.val=1 := by
  obtain ⟨_,e,_,he⟩ := h
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact siteRadius_neighbor (G.nearest e.val e.property)
  · rw [siteRadius_symm]; exact siteRadius_neighbor (G.nearest e.val e.property)

theorem coarse_reachable_of_walk (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices)
    (N : ℤ) (hN : 0<N) {v w : G.vertices}
    (p : (bondGraph (fun e : G.edges => e.val.1) (fun e => e.val.2) η).Walk v w)
    (hv : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x v) :
    (G.coarseCluster η x N).Reachable (coarseSite N v.val) (coarseSite N w.val) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons v w u hvw p ih =>
    have hw := bondConnected_trans _ _ _ hv ((bondConnected_iff_reachable _ _ _ _ _).mpr hvw.reachable)
    apply SimpleGraph.Reachable.trans (v := coarseSite N w.val) ?_ (ih hw)
    by_cases he : coarseSite N v.val=coarseSite N w.val
    · rw [he]
    · apply SimpleGraph.Adj.reachable
      refine ⟨he,coarseSite_step N hN (le_of_eq (G.fine_edge_radius η hvw)),⟨v,hv,rfl⟩,⟨w,hw,rfl⟩⟩

theorem coarse_walk_visited (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices)
    (N : ℤ) {z w : Site} (p : (G.coarseCluster η x N).Walk z w)
    (hz : G.cellVisited η x N z) (i : ℕ) : G.cellVisited η x N (p.getVert i) := by
  induction p generalizing i with
  | nil => exact hz
  | @cons z v w h p ih =>
    cases i with
    | zero => exact hz
    | succ i => exact ih h.2.2.2 i

theorem coarse_walk_radius (G : LatticeGraph) (η : G.edges → Bool) (x : G.vertices)
    (N : ℤ) {z w : Site} (p : (G.coarseCluster η x N).Walk z w) : siteRadius z w≤p.length := by
  induction p with
  | nil => simp
  | @cons z v w h p ih =>
    have ht := siteRadius_triangle z v w
    have hs := h.2.1
    simpa only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one] using (show siteRadius z w≤(p.length:ℤ)+1 by omega)

theorem connected_has_coarse_code (G : LatticeGraph) (η : G.edges → Bool) (x y : G.vertices)
    (N : ℤ) (hN : 0<N) (L : ℕ) (hfar : N*((L:ℤ)+2)≤ siteRadius x.val y.val)
    (hxy : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y) :
    ∃ c : SimpleCoarseCode (coarseSite N x.val) L,
      ∀ i : Fin (L+1),G.cellVisited η x N (codePosition (coarseSite N x.val) c.val i) := by
  obtain ⟨p⟩ := (bondConnected_iff_reachable _ _ _ _ _).mp hxy
  obtain ⟨q⟩ := G.coarse_reachable_of_walk η x N hN p (fun _ _ => rfl)
  let r := q.toPath.val
  have hr : r.IsPath := q.toPath.property
  have hl : L≤r.length := by
    have hd := coarseSite_distance N hN x.val y.val
    have hq := G.coarse_walk_radius η x N r
    by_contra hn
    have hln : (r.length:ℤ)<(L:ℤ) := by exact_mod_cast (Nat.lt_of_not_ge hn)
    nlinarith
  let a : Fin (L+1) → Site := fun i => r.getVert i.val
  have ha : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    exact hr.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega) (by simp only [Set.mem_ofPred_eq]; omega) hij
  have hs (i : Fin L) : siteRadius (a i.castSucc) (a i.succ)≤1 :=
    (r.adj_getVert_succ (by omega : i.val<r.length)).2.1
  obtain ⟨c,hc⟩ := codePosition_exists a hs
  have h0 : a 0=coarseSite N x.val := r.getVert_zero
  rw [h0] at hc
  refine ⟨⟨c,hc ▸ ha⟩,?_⟩
  intro i
  rw [congrFun hc i]
  exact G.coarse_walk_visited η x N r ⟨x,(fun _ _ => rfl),rfl⟩ i.val

theorem connected_code_crossings (G : LatticeGraph) (η : G.edges → Bool) (x y : G.vertices)
    (N : ℤ) (hN : 0<N) (L : ℕ) (hfar : N*((L:ℤ)+4)≤ siteRadius x.val y.val)
    (hxy : bondConnected (fun e : G.edges => e.val.1) (fun e => e.val.2) η x y) :
    ∃ c : SimpleCoarseCode (coarseSite N x.val) L,
      ∀ i : Fin (L+1),G.annulusIndicator N (coarseCenter N (codePosition (coarseSite N x.val) c.val i)) η=1 := by
  obtain ⟨c,hc⟩ := G.connected_has_coarse_code η x y N hN L (by nlinarith) hxy
  refine ⟨c,?_⟩
  intro i
  obtain ⟨w,hw,he⟩ := hc i
  apply G.annulus_crossing_of_component N hN η x y w (by nlinarith) hxy hw
  rw [← he]
  exact le_of_lt (coarseSite_close N hN w.val)

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarseTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph

theorem codeEvent_nonneg (G : LatticeGraph) (N : ℤ) (t : ℕ) (z : Site) (c : CoarseCode (25*t))
    (η : G.edges → Bool) : 0≤G.codeEvent N t z c η :=
  Finset.prod_nonneg (fun _ _ => G.annulusIndicator_nonneg _ _ _)

theorem connectionProbability_le_one (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e,0≤b e) (x y : G.vertices) :
    G.connectionProbability b x y≤1 := by
  unfold connectionProbability
  calc
    _≤freeBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (fun _ => 1) := by
      apply freeBondMean_mono _ _ _ hb
      intro η
      split_ifs <;> norm_num
    _=1 := freeBondMean_one _ _ _

theorem connection_le_codeSum (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e,0≤b e)
    (x y : G.vertices) (N : ℤ) (hN : 0<N) (t : ℕ)
    (hfar : N*((25*t:ℕ)+4)≤ siteRadius x.val y.val) :
    G.connectionProbability b x y≤
      ∑ c : SimpleCoarseCode (coarseSite N x.val) (25*t),
        freeBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (G.codeEvent N t (coarseSite N x.val) c.val) := by
  rw [← freeBondMean_sum]
  apply freeBondMean_mono _ _ _ hb
  intro η
  split_ifs with hxy
  · obtain ⟨c,hc⟩ := G.connected_code_crossings η x y N hN (25*t) hfar hxy
    have he : G.codeEvent N t (coarseSite N x.val) c.val η=1 := by
      unfold codeEvent
      simp only [hc,Finset.prod_const_one]
    rw [← he]
    exact Finset.single_le_sum (fun c _ => G.codeEvent_nonneg _ _ _ c.val η) (Finset.mem_univ c)
  · exact Finset.sum_nonneg (fun c _ => G.codeEvent_nonneg _ _ _ c.val η)

theorem connection_geometric_tail (β : ℝ) (hβ : 0≤β) :
    ∃ N : ℕ,0<N ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ (x y : G.vertices) (t : ℕ),(N:ℤ)*((25*t:ℕ)+4)≤ siteRadius x.val y.val →
        G.connectionProbability b x y≤(1/2:ℝ)^t := by
  let ε : ℝ := (1/2)/(9:ℝ)^25
  have hε : 0<ε := by positivity
  have hε1 : ε≤1 := by norm_num [ε]
  obtain ⟨k,hk,hs⟩ := separated_annuli_small β hβ ε hε
  refine ⟨2^k,by positivity,?_⟩
  intro G b hb x y t hfar
  have hN : (0:ℤ)<(2^k:ℕ) := by positivity
  apply le_trans (G.connection_le_codeSum b (fun e => (hb e).1) x y _ hN t hfar)
  calc
    _≤∑ _c : SimpleCoarseCode (coarseSite (2^k:ℕ) x.val) (25*t),ε^t := by
      apply Finset.sum_le_sum
      intro c _
      have hh := hs G b hb {i : Fin (25*t+1) // siteColor (codePosition (coarseSite (2^k:ℕ) x.val) c.val i)=
        codeColor t (coarseSite (2^k:ℕ) x.val) c.val}
        (fun i => coarseCenter (2^k:ℕ) (codePosition (coarseSite (2^k:ℕ) x.val) c.val i.val))
        (sameColor_separated _ hN _ c.property _)
      apply le_trans hh
      exact pow_le_pow_of_le_one (le_of_lt hε) hε1 (codeColor_card t _ c.val)
    _=(Fintype.card (SimpleCoarseCode (coarseSite (2^k:ℕ) x.val) (25*t)):ℝ)*ε^t := by simp
    _≤(9:ℝ)^(25*t)*ε^t := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_simpleCoarseCode (coarseSite (2^k:ℕ) x.val) (25*t)
    _=(1/2:ℝ)^t := by
      rw [pow_mul,← mul_pow]
      congr 1
      dsimp [ε]
      field_simp

end ClassicalON.LatticeGraph

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.CoarseExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace ClassicalON

theorem siteDistance_nonneg (x y : Site) : 0 ≤ siteDistance x y := Real.sqrt_nonneg _

theorem siteDistance_le_radius_twice (x y : Site) : siteDistance x y ≤ 2*(siteRadius x y:ℝ) := by
  have hi := siteRadius_nonneg x y
  have h1 : |(y.1:ℝ)-(x.1:ℝ)| ≤ (siteRadius x y:ℝ) := by
    exact_mod_cast (le_max_left |y.1-x.1| |y.2-x.2|)
  have h2 : |(y.2:ℝ)-(x.2:ℝ)| ≤ (siteRadius x y:ℝ) := by
    exact_mod_cast (le_max_right |y.1-x.1| |y.2-x.2|)
  have hr : (0:ℝ) ≤ siteRadius x y := by exact_mod_cast hi
  rw [abs_sub_comm] at h1 h2
  have hs1 := mul_self_le_mul_self (abs_nonneg _) h1
  have hs2 := mul_self_le_mul_self (abs_nonneg _) h2
  have hab1 := sq_abs ((x.1:ℝ)-(y.1:ℝ))
  have hab2 := sq_abs ((x.2:ℝ)-(y.2:ℝ))
  unfold siteDistance
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

theorem half_pow_exp (t : ℕ) : (1/2:ℝ)^t=Real.exp (-Real.log 2*(t:ℝ)) := by
  rw [mul_comm,Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

namespace LatticeGraph

theorem connection_exponential_oai (β : ℝ) (hβ : 0 ≤ β) :
    ∃ m : ℝ,0 < m  ∧  ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0 ≤ b e  ∧  b e ≤ β) →
      ∀ x y : G.vertices,G.connectionProbability b x y ≤ 4*Real.exp (-m*siteDistance x.val y.val) := by
  obtain ⟨N,hN,ht⟩ := connection_geometric_tail β hβ
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let m := Real.log 2/(50*(N:ℝ))
  refine ⟨m,by positivity,?_⟩
  intro G b hb x y
  let f := siteDistance x.val y.val/(50*(N:ℝ))
  have hf : 0 ≤ f := div_nonneg (siteDistance_nonneg _ _) (by positivity)
  let t : ℕ := Nat.floor f-1
  have hft : f < (t:ℝ)+2 := by
    have h1 := Nat.lt_floor_add_one f
    have h2 : Nat.floor f ≤ t+1 := by dsimp [t]; omega
    have h3 : (Nat.floor f:ℝ) ≤ (t:ℝ)+1 := by exact_mod_cast h2
    linarith
  have hp : G.connectionProbability b x y ≤ (1/2:ℝ)^t := by
    by_cases ht0 : t=0
    · simpa only [ht0,pow_zero] using G.connectionProbability_le_one b (fun e => (hb e).1) x y
    · apply ht G b hb x y t
      have he : Nat.floor f=t+1 := by dsimp [t] at *; omega
      have hfl := Nat.floor_le hf
      rw [he,Nat.cast_add,Nat.cast_one] at hfl
      have hmul := (le_div_iff₀ (show (0:ℝ) < 50*(N:ℝ) by positivity)).mp hfl
      have hd := siteDistance_le_radius_twice x.val y.val
      have hr : (N:ℝ)*((25*t:ℕ)+4) ≤ (siteRadius x.val y.val:ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast hr
  apply le_trans hp
  rw [half_pow_exp]
  calc
    _ ≤ Real.exp (Real.log 2*(2-f)) := Real.exp_le_exp.mpr (by nlinarith)
    _=4*Real.exp (-m*siteDistance x.val y.val) := by
      have he : Real.exp (Real.log 2*2)=(4:ℝ) := by
        rw [mul_comm,show (2:ℝ)=(2:ℕ) by norm_num,Real.exp_nat_mul]
        norm_num [Real.exp_log]
      rw [show Real.log 2*(2-f)=Real.log 2*2+(-Real.log 2*f) by ring,Real.exp_add,he]
      congr 2
      dsimp [f,m]
      ring

end LatticeGraph
end ClassicalON

end

end OAI
end

theorem solution : type_of% @OAI.ClassicalON.LatticeGraph.connection_exponential_oai := @OAI.ClassicalON.LatticeGraph.connection_exponential_oai
