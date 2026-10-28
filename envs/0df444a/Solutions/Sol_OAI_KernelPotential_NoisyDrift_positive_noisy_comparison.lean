-- Prove2me | solution 1 for OAI.KernelPotential.NoisyDrift.positive_noisy_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:04:14.303997+00:00
-- url     : https://prove2.me/submissions/714d2f9a-bb3d-410c-8df6-ff25e80c495d

import Mathlib
import Definitions.Def_GaussianInformation_003
import Definitions.Def_OAIQWRLC001

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GaussianRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaussianTools
open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma row_memLp {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun a : Fin d → ℝ => ∑ j,a j*v j) 2 (scalarRow d) := by
  apply memLp_finsetSum
  intro j _
  exact ((memLp_id_gaussianReal (2 : NNReal)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j)).mul_const (v j)

lemma row_integral {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (∫ a : Fin d → ℝ,∑ j,a j*v j ∂scalarRow d)=0 := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi (j : Fin d) : Integrable (fun a : Fin d → ℝ => a j*v j) (scalarRow d) :=
    (((memLp_id_gaussianReal (2 : NNReal)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j)).mul_const (v j)).integrable (by norm_num)
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [integral_mul_const,scalarRow,integral_eval,integral_id_gaussianReal,zero_mul,Finset.sum_const_zero]

lemma row_energy {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (∫ a : Fin d → ℝ,(∑ j,a j*v j)^2 ∂scalarRow d)=‖v‖^2 := by
  have h := variance_sum_pi (μ := fun _ : Fin d => gaussianReal 0 1)
    (X := fun j x => x*v j) (fun j => (memLp_id_gaussianReal (2 : NNReal)).mul_const (v j))
  have hm : Measurable (fun a : Fin d → ℝ => ∑ j,a j*v j) := by fun_prop
  simp only [Finset.sum_fn] at h
  rw [variance_eq_integral hm.aemeasurable] at h
  change (∫ a,(∑ j,a j*v j - ∫ a,∑ j,a j*v j ∂scalarRow d)^2 ∂scalarRow d)=_ at h
  rw [row_integral] at h
  simp only [sub_zero,variance_mul_const] at h
  rw [h,EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma labelDensity_pos {p : ℕ} {r : ℝ} (hr : 0 < r) (y : Fin p → ℝ) :
    0 < labelDensity r y := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (by intro hh; have he := congrArg (fun t : NNReal => (t : ℝ)) hh; exact (pow_ne_zero 2 hr.ne') he)

lemma log_labelDensity {p : ℕ} {r : ℝ} (hr : 0 < r) (y : Fin p → ℝ) :
    Real.log (labelDensity r y) =
      -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi) -
        (∑ i,(y i)^2)/(2*r^2) := by
  unfold labelDensity
  rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos 0 (NNReal.mk (r^2) (sq_nonneg r)) (y i) (by intro hh; have he := congrArg (fun t : NNReal => (t : ℝ)) hh; exact (pow_ne_zero 2 hr.ne') he)).ne')]
  simp only [gaussianPDFReal,NNReal.coe_mk,sub_zero]
  have hs : Real.sqrt (2*Real.pi*r^2)=Real.sqrt (2*Real.pi)*r := by
    rw [Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hr]
  simp_rw [Real.log_mul (by positivity : (Real.sqrt (2*Real.pi*r^2))⁻¹ ≠ 0) (Real.exp_pos _).ne',
    Real.log_inv,hs,Real.log_mul (by positivity : Real.sqrt (2*Real.pi) ≠ 0) hr.ne',
    Real.log_sqrt (by positivity : 0 ≤ 2*Real.pi),Real.log_exp]
  simp_rw [neg_div]
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,← Finset.sum_div,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma rows_energy {p d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (∫ X : Fin p → Fin d → ℝ, ∑ i,(∑ j,X i j*v j)^2
      ∂Measure.pi (fun _ : Fin p => scalarRow d)) = (p:ℝ)*‖v‖^2 := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi (i : Fin p) : Integrable (fun X : Fin p → Fin d → ℝ => (∑ j,X i j*v j)^2)
      (Measure.pi (fun _ : Fin p => scalarRow d)) :=
    ((row_memLp v).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin p => scalarRow d) i)).integrable_sq
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin p) : (∫ X : Fin p → Fin d → ℝ,(∑ j,X i j*v j)^2
      ∂Measure.pi (fun _ : Fin p => scalarRow d)) = ‖v‖^2 := by
    rw [← row_energy v]
    exact integral_comp_eval (μ := fun _ : Fin p => scalarRow d) (i := i)
      (f := fun a : Fin d → ℝ => (∑ j,a j*v j)^2) ((by fun_prop : Measurable
      (fun a : Fin d → ℝ => (∑ j,a j*v j)^2)).aestronglyMeasurable)
  simp_rw [he]
  simp

lemma rows_shift_energy {p d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (e : Fin p → ℝ) :
    (∫ X : Fin p → Fin d → ℝ, ∑ i,((∑ j,X i j*v j)+e i)^2
      ∂Measure.pi (fun _ : Fin p => scalarRow d)) ≤
      2*(p:ℝ)*‖v‖^2+2*∑ i,(e i)^2 := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi (i : Fin p) : MemLp (fun X : Fin p → Fin d → ℝ => ∑ j,X i j*v j) 2
      (Measure.pi (fun _ : Fin p => scalarRow d)) :=
    (row_memLp v).comp_measurePreserving (measurePreserving_eval (fun _ : Fin p => scalarRow d) i)
  have hil : Integrable (fun X : Fin p → Fin d → ℝ => ∑ i,((∑ j,X i j*v j)+e i)^2)
      (Measure.pi (fun _ : Fin p => scalarRow d)) :=
    integrable_finsetSum _ (fun i _ => ((hi i).add (memLp_const (e i))).integrable_sq)
  have hir : Integrable (fun X : Fin p → Fin d → ℝ => 2*(∑ i,(∑ j,X i j*v j)^2) + 2*∑ i,(e i)^2)
      (Measure.pi (fun _ : Fin p => scalarRow d)) :=
    ((integrable_finsetSum _ (fun i _ => (hi i).integrable_sq)).const_mul 2).add (integrable_const _)
  calc
    _ ≤ ∫ X : Fin p → Fin d → ℝ, 2*(∑ i,(∑ j,X i j*v j)^2) + 2*∑ i,(e i)^2
        ∂Measure.pi (fun _ : Fin p => scalarRow d) := by
      apply integral_mono hil hir
      intro X
      dsimp only
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_nonneg ((∑ j,X i j*v j)-e i)]
    _ = _ := by
      rw [integral_add ((integrable_finsetSum _ (fun i _ => (hi i).integrable_sq)).const_mul 2)
        (integrable_const _),integral_const_mul, rows_energy]
      simp
      ring

end GaussianTools

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Covers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Geometry
section Cover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma card_separated_le (s : Finset E) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ ((2 * R + δ) / δ) ^ Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hsmall : 0 < δ / 2 := by positivity
  have hlarge : 0 < R + δ / 2 := by positivity
  let A := ⋃ c ∈ s, ball c (δ / 2)
  have hdisj : (s : Set E).PairwiseDisjoint (fun c => ball c (δ / 2)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep c hc d hd hcd using 1
    ring
  have hsub : A ⊆ ball (0 : E) (R + δ / 2) := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    linarith [hs x hx]
  have hb : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2)^Module.finrank ℝ E) *
       μ (ball 0 1) ≤ ENNReal.ofReal ((R + δ / 2)^Module.finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hsmall, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball 0 (R + δ / 2)) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hlarge
  have hb' := (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
    measure_ball_lt_top.ne).mp hb
  have hbR : (s.card : ℝ) * (δ / 2)^Module.finrank ℝ E ≤
      (R + δ / 2)^Module.finrank ℝ E := by
    simpa [ENNReal.toReal_ofReal (pow_nonneg hsmall.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hlarge.le _) hb'
  calc
    (s.card : ℝ) ≤ (R + δ / 2)^Module.finrank ℝ E / (δ / 2)^Module.finrank ℝ E :=
      (le_div_iff₀ (pow_pos hsmall _)).mpr hbR
    _ = ((2 * R + δ) / δ)^Module.finrank ℝ E := by
      rw [← div_pow]
      congr 1
      field_simp

lemma exists_ball_cover_card_le {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset E, (∀ c ∈ s, ‖c‖ ≤ R) ∧
      (∀ x : E, ‖x‖ ≤ R → ∃ c ∈ s, dist x c ≤ δ) ∧
      (s.card : ℝ) ≤ ((2 * R + δ) / δ)^Module.finrank ℝ E := by
  classical
  let ε : ℝ≥0 := ⟨δ, hδ.le⟩
  let A := closedBall (0 : E) R
  have hεpos : 0 < ε := hδ
  have hε : ε ≠ 0 := ne_of_gt hεpos
  obtain ⟨N, _, hNfin, hNcov⟩ := Metric.exists_finite_isCover_of_isCompact
    (s := A) (ε := ε / 2) (by positivity) (isCompact_closedBall _ _)
  have hp : Metric.packingNumber ε A < ⊤ := by
    calc
      _ = Metric.packingNumber (2 * (ε / 2)) A := by congr 1; ring
      _ ≤ Metric.externalCoveringNumber (ε / 2) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ N.encard := hNcov.externalCoveringNumber_le_encard
      _ < ⊤ := hNfin.encard_lt_top
  let S := Metric.maximalSeparatedSet ε A
  have hSfin : S.Finite := Set.encard_lt_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard < ⊤
    rw [Metric.encard_maximalSeparatedSet hp.ne]
    exact hp)
  have hSsub : ∀ c ∈ hSfin.toFinset, ‖c‖ ≤ R := by
    intro c hc
    have : c ∈ S := by simpa using hc
    simpa [A] using (Metric.maximalSeparatedSet_subset this)
  refine ⟨hSfin.toFinset, hSsub, ?_, card_separated_le _ hR hδ hSsub ?_⟩
  · intro x hx
    have hcov := Metric.isCover_iff_subset_iUnion_closedBall.mp
      (Metric.isCover_maximalSeparatedSet hp.ne)
    have hm : x ∈ A := by simpa [A] using hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcov hm)
    exact ⟨c, by simpa using hc, hxc⟩
  · intro c hc d hd hcd
    have hs := Metric.isSeparated_maximalSeparatedSet (ε := ε) (A := A)
      (by simpa using hc) (by simpa using hd) hcd
    have ht := ENNReal.toReal_mono (edist_ne_top c d) hs.le
    change δ ≤ (edist c d).toReal at ht
    simpa [ε, edist_dist, dist_eq_norm] using ht

end Cover

section PlaneCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma exists_affine_tube_cover (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset E,
      (∀ x : E, ‖x‖ ≤ R → infDist x (V : Set E) ≤ δ → ∃ c ∈ s, dist x c ≤ 2 * δ) ∧
      (s.card : ℝ) ≤ ((4 * R + 5 * δ) / δ)^Module.finrank ℝ V.direction := by
  classical
  by_cases hempty : {x : E | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ δ}.Nonempty
  · obtain ⟨x₀, hx₀n, hx₀d⟩ := hempty
    obtain ⟨v₀, hv₀V, hv₀d⟩ := V.closed_of_finiteDimensional.exists_infDist_eq_dist hV x₀
    have hn₀ : ‖v₀‖ ≤ R + δ := by
      have ht := dist_triangle v₀ x₀ 0
      rw [dist_zero_right, dist_zero_right, dist_comm v₀ x₀, ← hv₀d] at ht
      linarith
    obtain ⟨s, _, hcover, hcard⟩ := exists_ball_cover_card_le (E := V.direction)
      (R := 2 * (R + δ)) (δ := δ) (by positivity) hδ
    let f : V.direction ↪ E := ⟨fun v => (v : E) + v₀, by
      intro v w h
      exact Subtype.ext (add_right_cancel h)⟩
    refine ⟨s.map f, ?_, ?_⟩
    · intro x hxn hxd
      obtain ⟨v, hvV, hvd⟩ := V.closed_of_finiteDimensional.exists_infDist_eq_dist hV x
      have hnv : ‖v‖ ≤ R + δ := by
        have ht := dist_triangle v x 0
        rw [dist_zero_right, dist_zero_right, dist_comm v x, ← hvd] at ht
        linarith
      let u : V.direction := ⟨v - v₀, V.vsub_mem_direction hvV hv₀V⟩
      have hnu : ‖u‖ ≤ 2 * (R + δ) := by
        change ‖v - v₀‖ ≤ _
        exact (norm_sub_le v v₀).trans (by linarith)
      obtain ⟨a, ha, hu⟩ := hcover u hnu
      refine ⟨f a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
      have he : dist v (f a) = dist u a := by
        rw [dist_eq_norm, dist_eq_norm]
        change ‖v - ((a : E) + v₀)‖ = ‖(v - v₀) - (a : E)‖
        congr 1
        abel
      calc
        dist x (f a) ≤ dist x v + dist v (f a) := dist_triangle _ _ _
        _ ≤ δ + δ := add_le_add (hvd ▸ hxd) (he ▸ hu)
        _ = 2 * δ := by ring
    · simpa only [Finset.card_map, show 2 * (2 * (R + δ)) + δ = 4 * R + 5 * δ by ring] using hcard
  · refine ⟨∅, ?_, ?_⟩
    · intro x hxn hxd
      exact (hempty ⟨x, hxn, hxd⟩).elim
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity

end PlaneCover

end Geometry
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SmallBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Geometry
lemma inv_pow_dyadic_majorant (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (x⁻¹ ^ k) ≤ 1 + ∑' j : ℕ,
      ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := by
  by_cases hx0 : x = 0
  · simp [hx0, hk.ne']
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  by_cases hx1 : 1 ≤ x
  · have hle : ENNReal.ofReal (x⁻¹ ^ k) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_one₀ (inv_nonneg.mpr hx) ((inv_le_one₀ hxpos).mpr hx1)
    exact hle.trans (le_add_right le_rfl)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near_of_lt_one hxpos
    (le_of_not_ge hx1) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hbound : x⁻¹ ^ k ≤ (2 : ℝ) ^ ((j + 1) * k) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (inv_nonneg.mpr hx)
    have hinv := (inv_le_inv₀ hxpos (pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) (j+1))).mpr hj.le
    simpa only [one_div, inv_pow, inv_inv] using hinv
  calc
    ENNReal.ofReal (x⁻¹ ^ k) ≤ ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k)) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := by
      simp only [Set.indicator, Set.mem_ofPred_eq, hj', ite_true]
    _ ≤ ∑' j : ℕ, ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x :=
      ENNReal.le_tsum (f := fun index : ℕ =>
        ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ index}).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((index + 1) * k))) x) j
    _ ≤ 1 + ∑' j : ℕ, ({x : ℝ | x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))) x := le_add_left le_rfl

lemma dyadic_weight_product (j k : ℕ) :
    (2 : ℝ) ^ ((j + 1) * k) * (1 / 2 : ℝ) ^ ((k + 1) * j) =
      (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ j := by
  simp only [Nat.add_mul, one_mul, pow_add, one_div, inv_pow]
  have hpow : (2 : ℝ) ^ (k * j) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Nat.mul_comm j k]
  field_simp

theorem inverseMoment_of_dyadic_tails {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : α → ℝ) (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x)
    (k : ℕ) (hk : 0 < k) (A : ℝ≥0∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1 / 2 : ℝ) ^ j} ≤
      A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) :
    (∫⁻ x, ENNReal.ofReal ((D x)⁻¹ ^ k) ∂μ) ≤
      μ univ + A * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
  let S : ℕ → Set α := fun j => {x | D x ≤ (1 / 2 : ℝ) ^ j}
  let w : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((2 : ℝ) ^ ((j + 1) * k))
  have hS : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hD measurable_const
  have hmeas : ∀ j, Measurable ((S j).indicator (fun _ => w j)) :=
    fun j => measurable_const.indicator (hS j)
  calc
    (∫⁻ x, ENNReal.ofReal ((D x)⁻¹ ^ k) ∂μ) ≤
        ∫⁻ x, (1 + ∑' j, (S j).indicator (fun _ => w j) x) ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [S, w, Set.indicator, Set.mem_ofPred_eq] using
        inv_pow_dyadic_majorant (D x) (hD0 x) k hk
    _ = μ univ + ∑' j, w j * μ (S j) := by
      rw [lintegral_add_left measurable_const,
        lintegral_tsum (fun j => (hmeas j).aemeasurable)]
      simp only [lintegral_const, one_mul, lintegral_indicator (hS _), Measure.restrict_apply_univ]
    _ ≤ μ univ + ∑' j, w j * (A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) := by
      gcongr with j
      exact htail j
    _ = μ univ + ∑' j, (A * ENNReal.ofReal ((2 : ℝ) ^ k)) * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
      congr 1
      apply tsum_congr
      intro j
      dsimp [w]
      rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), dyadic_weight_product,
        ENNReal.ofReal_mul (by positivity)]
      ac_rfl
    _ = μ univ + A * ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
      simp only [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)), ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div, ENNReal.one_sub_inv_two,
        inv_inv, pow_succ, ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k),
        ENNReal.ofReal_ofNat, mul_assoc]

theorem zeroSet_null_of_dyadic_tails {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (D : α → ℝ) (k : ℕ) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1 / 2 : ℝ) ^ j} ≤
      A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j))) :
    μ {x | D x = 0} = 0 := by
  have hr : ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have ht := ENNReal.Tendsto.const_mul
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr hA)
  apply le_antisymm _ bot_le
  change μ {x | D x = 0} ≤ (0 : ℝ≥0∞)
  apply ge_of_tendsto' (show Tendsto
    (fun j : ℕ => A * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) ^ j) atTop (𝓝 (0 : ℝ≥0∞)) from
    by simpa only [mul_zero] using ht)
  intro j
  calc
    μ {x | D x = 0} ≤ μ {x | D x ≤ (1 / 2 : ℝ) ^ j} := by
      apply measure_mono
      intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hx]
      positivity
    _ ≤ A * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((k + 1) * j)) := htail j
    _ = A * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) ^ j := by
      rw [pow_mul, ENNReal.ofReal_pow (by positivity)]

end Geometry
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_MixedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Geometry
section MixedGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma tube_ball_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {a k : ℕ} {B R t : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) (ht : 0 < t) (ht1 : t ≤ 1)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction + (k+1) ≤ a) :
    μ {x | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ R*t} ≤
      ENNReal.ofReal (B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a * t^(k+1)) := by
  classical
  let j := Module.finrank ℝ V.direction
  obtain ⟨s, hs, hcard⟩ := exists_affine_tube_cover V hV hR.le (mul_pos hR ht)
  have hsub : {x | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ R*t} ⊆
      ⋃ c ∈ s, ball c (3*(R*t)) := by
    intro x hx
    obtain ⟨c,hc,hxc⟩ := hs x hx.1 hx.2
    exact mem_iUnion₂.mpr ⟨c,hc,lt_of_le_of_lt hxc (by nlinarith)⟩
  have hc : (s.card : ℝ) ≤ (9/t)^j := by
    apply hcard.trans
    apply pow_le_pow_left₀ (by positivity)
    calc
      (4*R+5*(R*t))/(R*t) ≤ (9*R)/(R*t) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left ht1 hR.le]
      _ = 9/t := by field_simp
  have halg : (9/t)^j * (B*(3*(R*t))^a) ≤
      B*9^j*3^a*R^a*t^(k+1) := by
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hdim
    have htj : t^j ≠ 0 := pow_ne_zero _ ht.ne'
    have hte : t^e ≤ 1 := pow_le_one₀ ht.le ht1
    have heq : (9/t)^j * (B*(3*(R*t))^a) =
        (B*9^j*3^a*R^a*t^(k+1))*t^e := by
      simp only [he, j, mul_pow, div_pow, pow_add]
      field_simp
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) hte

  calc
    _ ≤ ∑ c ∈ s, μ (ball c (3*(R*t))) := (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _c ∈ s, ENNReal.ofReal (B*(3*(R*t))^a) := by gcongr; exact hball _ _ (by positivity)
    _ = ENNReal.ofReal ((s.card:ℝ)*(B*(3*(R*t))^a)) := by
      simp [ENNReal.ofReal_mul, hB]
    _ ≤ ENNReal.ofReal (B*9^j*3^a*R^a*t^(k+1)) := by
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans halg

lemma inverseMoment_extended_of_tails {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (D : E → ℝ)
    (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x) (k : ℕ) (hk : 0 < k)
    (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1/2:ℝ)^j} ≤
      A * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j))) :
    (∫⁻ x, (ENNReal.ofReal (D x))⁻¹^k ∂μ) ≤
      μ univ + A*ENNReal.ofReal ((2:ℝ)^(k+1)) := by
  have hz : ∀ᵐ x ∂μ, D x ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using zeroSet_null_of_dyadic_tails μ D k A hA htail
  have heq : (fun x => (ENNReal.ofReal (D x))⁻¹^k) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((D x)⁻¹^k)) := by
    filter_upwards [hz] with x hx
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr (hD0 x)),
      ENNReal.ofReal_inv_of_pos (lt_of_le_of_ne (hD0 x) hx.symm)]
  rw [lintegral_congr_ae heq]
  exact inverseMoment_of_dyadic_tails μ D hD hD0 k hk A htail

end MixedGeometry

end Geometry

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Sphere
open KernelPotential.Geometry

lemma unit_ball_pos (d : ℕ) : 0 < volume (ball (0 : Ambient d) 1) :=
  measure_ball_pos volume _ zero_lt_one

lemma unit_ball_ne_top (d : ℕ) : volume (ball (0 : Ambient d) 1) ≠ ∞ :=
  measure_ball_lt_top.ne

lemma unitVolume_ball (d : ℕ) (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    unitVolume d (ball z r) = ENNReal.ofReal (r^d) := by
  rw [unitVolume,Measure.smul_apply,smul_eq_mul,volume.addHaar_ball_of_pos z hr]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [mul_left_comm, ENNReal.inv_mul_cancel (unit_ball_pos d).ne' (unit_ball_ne_top d),mul_one]

lemma measurable_radial (d : ℕ) : Measurable (@radial d) :=
  measurable_norm.inv.smul measurable_id

lemma sphereProbability_eq (d : ℕ) :
    sphereProbability d = ((unitVolume d).restrict (ball 0 1)).map radial := by
  simp only [sphereProbability,unitVolume,Measure.restrict_smul]

instance sphereProbability_probability (d : ℕ) : IsProbabilityMeasure (sphereProbability d) := by
  rw [sphereProbability_eq]
  have : IsProbabilityMeasure ((unitVolume d).restrict (ball 0 1)) := by
    constructor
    simp only [Measure.restrict_apply_univ, unitVolume_ball d _ zero_lt_one, one_pow, ENNReal.ofReal_one]
  exact Measure.isProbabilityMeasure_map_iff (measurable_radial d).aemeasurable |>.mpr inferInstance

lemma radial_rescale {d : ℕ} (x : Ambient d) : ‖x‖ • radial x = x := by
  by_cases hx : x = 0
  · simp [hx,radial]
  · simp only [radial,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

lemma norm_radial {d : ℕ} (x : Ambient d) (hx : x ≠ 0) : ‖radial x‖ = 1 := by
  rw [radial,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma ae_unit_norm {d : ℕ} (hd : 0 < d) : ∀ᵐ s ∂sphereProbability d, ‖s‖ = 1 := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have : Nontrivial (Ambient d) := inferInstance
  rw [sphereProbability_eq]
  apply (ae_map_iff (measurable_radial d).aemeasurable (measurableSet_eq_fun measurable_norm measurable_const)).mpr
  have hz : ∀ᵐ x ∂((unitVolume d).restrict (ball 0 1)), x ≠ 0 := by
    have ha : ((unitVolume d).restrict (ball 0 1)) ≪ (volume : Measure (Ambient d)) :=
      Measure.absolutelyContinuous_restrict.trans Measure.smul_absolutelyContinuous
    apply ha.ae_le
    exact ae_iff.mpr (by simp)
  filter_upwards [hz] with x hx
  exact norm_radial x hx

lemma singleton_span_finrank_le {d : ℕ} (z : Ambient d) :
    Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))) ≤ 1 := by
  by_cases hz : z = 0
  · rw [hz,Submodule.span_singleton_eq_bot.mpr rfl,finrank_bot]
    omega
  · exact (finrank_span_singleton hz).le

lemma preimage_cap_tube {d : ℕ} (z : Ambient d) {r : ℝ} (_hr : 0 < r) :
    radial ⁻¹' ball z r ∩ ball 0 1 ⊆
      {x | ‖x‖ ≤ 1 ∧ infDist x (Submodule.span ℝ ({z} : Set (Ambient d)) : Set (Ambient d)) ≤ r} := by
  intro x hx
  have hxn : ‖x‖ < 1 := by simpa using hx.2
  have hxz : dist (radial x) z < r := hx.1
  refine ⟨hxn.le, ?_⟩
  have hz : ‖x‖ • z ∈ Submodule.span ℝ ({z} : Set (Ambient d)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  apply (infDist_le_dist_of_mem hz).trans
  calc
    dist x (‖x‖ • z) = ‖x‖ * dist (radial x) z := by
      calc
        _ = dist (‖x‖ • radial x) (‖x‖ • z) := congrArg (fun y => dist y (‖x‖ • z)) (radial_rescale x).symm
        _ = _ := by rw [dist_smul₀,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    _ ≤ 1*r := mul_le_mul hxn.le hxz.le dist_nonneg (by norm_num)
    _ = r := one_mul _

lemma cap_bound {d : ℕ} (hd : 2 ≤ d) (z : Ambient d) {r : ℝ} (hr : 0 < r) :
    sphereProbability d (ball z r) ≤ ENNReal.ofReal ((9*3^d:ℝ)*r^(d-1)) := by
  by_cases hr1 : r ≤ 1
  · let V : AffineSubspace ℝ (Ambient d) := (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace
    have hdim : Module.finrank ℝ V.direction + ((d-2)+1) ≤ d := by
      have hz := singleton_span_finrank_le z
      change Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace.direction + _ ≤ d
      rw [Submodule.toAffineSubspace_direction]
      omega
    have ht := tube_ball_bound (unitVolume d) (a := d) (k := d-2) (B := 1) (R := 1)
      (by norm_num) (by norm_num) hr hr1 (fun z r hr => by simpa using (unitVolume_ball d z hr).le)
      V ⟨0,Submodule.zero_mem _⟩ hdim
    calc
      _ = unitVolume d (radial ⁻¹' ball z r ∩ ball 0 1) := by
        rw [sphereProbability_eq,Measure.map_apply (measurable_radial d) measurableSet_ball,
          Measure.restrict_apply ((measurable_radial d) measurableSet_ball)]
      _ ≤ unitVolume d {x | ‖x‖ ≤ 1 ∧ infDist x (V : Set (Ambient d)) ≤ 1*r} :=
        measure_mono (by
          change radial ⁻¹' ball z r ∩ ball 0 1 ⊆ {x | ‖x‖ ≤ 1 ∧
            infDist x (Submodule.span ℝ ({z} : Set (Ambient d)) : Set (Ambient d)) ≤ 1*r}
          simpa only [one_mul] using preimage_cap_tube z hr)
      _ ≤ ENNReal.ofReal (1 * 9^(Module.finrank ℝ V.direction) * 3^d * 1^d * r^((d-2)+1)) := ht
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [show (d-2)+1=d-1 by omega]
        simp only [one_mul,one_pow,mul_one]
        gcongr
        calc
          (9:ℝ)^(Module.finrank ℝ V.direction) ≤ 9^1 := by
            apply pow_le_pow_right₀ (by norm_num)
            change Module.finrank ℝ (Submodule.span ℝ ({z} : Set (Ambient d))).toAffineSubspace.direction ≤ 1
            rw [Submodule.toAffineSubspace_direction]
            exact singleton_span_finrank_le z
          _ = 9 := pow_one _
  · apply (prob_le_one (μ := sphereProbability d)).trans
    apply ENNReal.one_le_ofReal.mpr
    have h3 : (1:ℝ) ≤ 3^d := one_le_pow₀ (by norm_num)
    have hrp : (1:ℝ) ≤ r^(d-1) := one_le_pow₀ (by linarith : (1:ℝ) ≤ r)
    nlinarith

end Sphere

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace EntropySupport

lemma continuous_xlog : Continuous xlog := Real.continuous_mul_log
lemma xlog_mul (x y : ℝ) : xlog (x*y) = y*xlog x+x*xlog y := by
  have h := Real.negMulLog_mul x y
  simp only [Real.negMulLog_def, neg_mul] at h
  dsimp [xlog]
  linarith

lemma integrable_bounded_measurable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, Function.comp_def] using hC x)

lemma integrable_xlog_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M) : Integrable (fun x => xlog (f x)) μ := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := M)).image continuous_xlog).isBounded.exists_norm_le
  apply integrable_bounded_measurable μ _ (continuous_xlog.measurable.comp hf)
  intro x
  simpa only [Real.norm_eq_abs,Function.comp_def] using hC _ (Set.mem_image_of_mem _ ⟨hf0 x,hfM x⟩)

lemma klDiv_withDensity_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    InformationTheory.klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (∫ x,xlog (f x) ∂μ) := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfM x)
  have hix := integrable_xlog_bounded μ f hf hf0 hfM
  have hib : Integrable (fun x => InformationTheory.klFun (f x)) μ :=
    (hix.add (integrable_const 1)).sub hif
  have hfint : ∫ x,f x ∂μ = 1 := by
    have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hif (ae_of_all _ hf0)] at h
    exact (ENNReal.ofReal_eq_one.mp h)
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous μ _)]
  have hrn := Measure.rnDeriv_withDensity μ hf.ennreal_ofReal
  have he : (fun x => ENNReal.ofReal (InformationTheory.klFun (((μ.withDensity
      (fun x => ENNReal.ofReal (f x))).rnDeriv μ x).toReal))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (InformationTheory.klFun (f x))) := by
    filter_upwards [hrn] with x hx
    rw [hx,ENNReal.toReal_ofReal (hf0 x)]
  rw [lintegral_congr_ae he,← ofReal_integral_eq_lintegral_ofReal hib
    (ae_of_all _ (fun x => InformationTheory.klFun_nonneg (hf0 x)))]
  congr 1
  change (∫ x,xlog (f x)+1-f x ∂μ) = _
  rw [integral_sub (f := fun x => xlog (f x)+1) (hix.add (integrable_const 1)) hif,
    integral_add hix (integrable_const 1),hfint]
  simp

end EntropySupport

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Coercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Coercivity
open _root_.OAI.KernelPotential.Geometry Sphere

lemma inverse_kernel_bound {d n q : ℕ} (μ : Measure (Ambient d)) [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hqn : q+1 ≤ n)
    (hball : ∀ s r, 0 < r → μ (ball s r) ≤ ENNReal.ofReal (C*r^n)) (s : Ambient d) :
    (∫⁻ u, (ENNReal.ofReal ‖u-s‖)⁻¹^q ∂μ) ≤ ENNReal.ofReal (1+C*2^(n+q+1)) := by
  have ht : ∀ j : ℕ, μ {u | ‖u-s‖ ≤ (1/2:ℝ)^j} ≤
      ENNReal.ofReal (C*2^n)*ENNReal.ofReal ((1/2:ℝ)^((q+1)*j)) := by
    intro j
    calc
      _ ≤ μ (ball s (2*(1/2:ℝ)^j)) := measure_mono (by
        intro u hu
        change dist u s < _
        rw [dist_eq_norm]
        have hp : 0 < (1/2:ℝ)^j := by positivity
        change ‖u-s‖ ≤ (1/2:ℝ)^j at hu
        linarith)
      _ ≤ ENNReal.ofReal (C*(2*(1/2:ℝ)^j)^n) := hball _ _ (by positivity)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow, ← mul_assoc, Nat.mul_comm (q+1) j, pow_mul]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_of_le_one (by positivity : 0 ≤ (1/2:ℝ)^j) (pow_le_one₀ (by norm_num) (by norm_num)) hqn
  have h := inverseMoment_extended_of_tails μ (fun u => ‖u-s‖)
    (measurable_id.sub_const s).norm (fun u => norm_nonneg _) q hq
    (ENNReal.ofReal (C*2^n)) ENNReal.ofReal_ne_top ht
  apply h.trans_eq
  rw [measure_univ, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  rw [mul_assoc, ← pow_add]
  congr 3

lemma measurable_J {d : ℕ} (ν : Measure (Ambient d)) [SFinite ν] : Measurable (J ν) := by
  unfold J
  apply Measurable.lintegral_prod_right
  exact ((measurable_snd.sub measurable_fst).norm.ennreal_ofReal.inv).pow_const _

lemma bounded_density_representation {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • μ) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x,0 ≤ f x) ∧ (∀ x,f x ≤ H) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  have hr : ν.rnDeriv μ ≤ᵐ[μ] fun _ => ENNReal.ofReal H := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ)
    intro s hs _
    calc
      _ ≤ ν s := Measure.setLIntegral_rnDeriv_le s
      _ ≤ (ENNReal.ofReal H • μ) s := hν s
      _ = _ := by simp [Measure.smul_apply]
  let f : α → ℝ := fun x => min H (ν.rnDeriv μ x).toReal
  refine ⟨f,measurable_const.min (Measure.measurable_rnDeriv ν μ).ennreal_toReal,
    fun x => le_min hH.le ENNReal.toReal_nonneg,fun x => min_le_left _ _,?_⟩
  rw [← Measure.withDensity_rnDeriv_eq ν μ hac]
  apply withDensity_congr_ae
  filter_upwards [hr] with x hx
  dsimp [f]
  have hxt : ν.rnDeriv μ x ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hxH : (ν.rnDeriv μ x).toReal ≤ H := by
    exact (ENNReal.toReal_le_toReal hxt ENNReal.ofReal_ne_top).mpr hx |>.trans_eq (ENNReal.toReal_ofReal hH.le)
  rw [min_eq_right hxH, ENNReal.ofReal_toReal hxt]

lemma bounded_J {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) :
    J ν s ≤ ENNReal.ofReal (H*(1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1))) := by
  have hk : 0 < d/16 := Nat.div_pos (by omega) (by norm_num)
  calc
    J ν s ≤ ∫⁻ u,(ENNReal.ofReal ‖u-s‖)⁻¹^(2*(d/16)) ∂(ENNReal.ofReal H • sphereProbability d) :=
      lintegral_mono' hν (le_refl _)
    _ = ENNReal.ofReal H * J (sphereProbability d) s := by rw [J,lintegral_smul_measure,smul_eq_mul]
    _ ≤ ENNReal.ofReal H * ENNReal.ofReal (1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1)) := by
      gcongr
      exact inverse_kernel_bound (sphereProbability d) (by positivity) (by omega)
        (by omega) (fun s r hr => cap_bound (by omega) s hr) s
    _ = _ := (ENNReal.ofReal_mul hH.le).symm

lemma lower_J_on_sphere {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν, ‖u‖=1) (s : Ambient d) (hs : ‖s‖=1) :
    ENNReal.ofReal ((1/2:ℝ)^(2*(d/16))) ≤ J ν s := by
  calc
    _ = ∫⁻ u, ENNReal.ofReal ((1/2:ℝ)^(2*(d/16))) ∂ν := by simp
    _ ≤ J ν s := by
      apply lintegral_mono_ae
      filter_upwards [hν] with u hu
      have hn : ‖u-s‖ ≤ 2 := by calc
        ‖u-s‖ ≤ ‖u‖+‖s‖ := norm_sub_le _ _
        _ = 2 := by rw [hu,hs]; norm_num
      rw [ENNReal.ofReal_pow (by norm_num),show ENNReal.ofReal (1/2:ℝ)=(ENNReal.ofReal (2:ℝ))⁻¹ by rw [one_div,ENNReal.ofReal_inv_of_pos (by norm_num)]]
      exact pow_le_pow_left₀ zero_le (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hn)) _

lemma integrable_log_of_bounds {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    {a b : ℝ} (ha : 0 < a)
    (hbound : ∀ᵐ x ∂μ, a ≤ f x ∧ f x ≤ b) : Integrable (fun x => Real.log (f x)) μ := by
  apply Integrable.mono' (integrable_const (|Real.log a|+|Real.log b|)) hf.log.aestronglyMeasurable
  filter_upwards [hbound] with x hx
  have hl := Real.log_le_log ha hx.1
  have hu := Real.log_le_log (ha.trans_le hx.1) hx.2
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hh := neg_abs_le (Real.log a)
    have hb0 := abs_nonneg (Real.log b)
    linarith
  · have hh := le_abs_self (Real.log b)
    have ha0 := abs_nonneg (Real.log a)
    linarith

lemma J_real_bounds {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1) :
    (1/2:ℝ)^(2*(d/16)) ≤ (J ν s).toReal ∧
      (J ν s).toReal ≤ H*(1+(9*3^d:ℝ)*2^((d-1)+2*(d/16)+1)) := by
  have hu := bounded_J hd ν hH hν s
  have ht := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hnorm : ∀ᵐ u ∂ν, ‖u‖=1 := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega))
  have hl := lower_J_on_sphere ν hnorm s hs
  constructor
  · convert ENNReal.toReal_mono ht hl using 1
    rw [ENNReal.toReal_ofReal (by positivity)]
  · convert ENNReal.toReal_mono ENNReal.ofReal_ne_top hu using 1
    rw [ENNReal.toReal_ofReal (by positivity)]

lemma integrable_log_J {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (hν : BoundedDensity ν) (μ : Measure (Ambient d))
    [IsFiniteMeasure μ] (hμ : ∀ᵐ s ∂μ, ‖s‖=1) :
    Integrable (fun s => Real.log (J ν s).toReal) μ := by
  obtain ⟨H,hH,hνH⟩ := hν
  apply integrable_log_of_bounds μ _ (measurable_J ν).ennreal_toReal (by positivity : 0 < (1/2:ℝ)^(2*(d/16)))
  filter_upwards [hμ] with s hs
  exact J_real_bounds hd ν hH hνH s hs

open EntropySupport

lemma density_integral_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    ∫ x,f x ∂μ = 1 := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfH x)
  have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hif (ae_of_all _ hf0)] at h
  exact ENNReal.ofReal_eq_one.mp h

lemma density_entropy_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    0 ≤ ∫ x,xlog (f x) ∂μ := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfH x)
  have hix := integrable_xlog_bounded μ f hf hf0 hfH
  have h := integral_mono (hif.sub (integrable_const 1)) hix
    (fun x => Real.self_sub_one_le_mul_log (hf0 x))
  change (∫ x,f x-1 ∂μ) ≤ _ at h
  rw [integral_sub hif (integrable_const 1),density_integral_one μ f hf hf0 hfH] at h
  simpa using h

lemma Phi_density_formula {d : ℕ} (hd : 16 ≤ d) (f : Ambient d → ℝ)
    (hf : Measurable f) (hf0 : ∀ x,0 ≤ f x) {H : ℝ} (hfH : ∀ x,f x ≤ H)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (hν : BoundedDensity ν)
    (heq : ν = (sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))) :
    Phi ν = ∫ s, xlog (f s)-f s*Real.log (J ν s).toReal ∂sphereProbability d := by
  have : IsProbabilityMeasure ((sphereProbability d).withDensity (fun x => ENNReal.ofReal (f x))) := heq ▸ inferInstance
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  have hil := integrable_log_J hd ν hν (sphereProbability d) (ae_unit_norm (by omega))
  have hib := hil.bdd_mul hf.aestronglyMeasurable (ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hf0 x)]; exact hfH x))
  have hD : (InformationTheory.klDiv ν (sphereProbability d)).toReal = ∫ s,xlog (f s) ∂sphereProbability d := by
    rw [heq,klDiv_withDensity_bounded _ f hf hf0 hfH,
      ENNReal.toReal_ofReal (density_entropy_nonneg _ f hf hf0 hfH)]
  have hB : B ν = ∫ s,f s*Real.log (J ν s).toReal ∂sphereProbability d := by
    unfold B
    nth_rw 1 [heq]
    rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _),smul_eq_mul]
  rw [Phi,hD,hB,integral_sub hix hib]

end Coercivity
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Mixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Coercivity
open KernelPotential.Geometry Sphere
open EntropySupport

lemma density_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ) {H : ℝ} (hfH : ∀ x,f x ≤ H) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) ≤ ENNReal.ofReal H • μ := by
  intro s
  rw [withDensity_apply' _ s,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∫⁻ x in s, ENNReal.ofReal H ∂μ := lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfH x))
    _ = _ := by simp

end Coercivity

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_BoxKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Projection

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Support

lemma measurableSet_closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) :
    MeasurableSet (closedBox c η) := by
  simp only [closedBox, ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le ((measurable_pi_apply i).sub measurable_const).abs measurable_const

lemma volume_closedBox {k : ℕ} (c : Fin k → ℝ) (η : ℝ) (hη : 0 ≤ η) :
    volume (closedBox c η) = ENNReal.ofReal ((2*η)^k) := by
  have heq : closedBox c η = univ.pi (fun i => Icc (c i-η) (c i+η)) := by
    ext u
    simp only [closedBox, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_true_left,
      mem_Icc, abs_le]
    congr! 1
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [heq, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, show ∀ i, c i+η-(c i-η)=2*η from fun i => by ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

lemma measurable_boxKernel {k : ℕ} (η : ℝ) :
    Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => boxKernel η p.1 p.2) := by
  have hs : MeasurableSet {p : (Fin k → ℝ) × (Fin k → ℝ) | ∀ i, |p.2 i-p.1 i| ≤ η} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)).abs measurable_const
  exact measurable_const.indicator hs

lemma boxKernel_le {k : ℕ} (η : ℝ) (c u : Fin k → ℝ) :
    boxKernel η c u ≤ boxScale k η := Set.indicator_le_self (closedBox c η) (fun _ => boxScale k η) u

lemma boxKernel_ne_zero_mem {k : ℕ} {η : ℝ} {c u : Fin k → ℝ}
    (h : boxKernel η c u ≠ 0) : u ∈ closedBox c η := by
  by_contra hu
  exact h (Set.indicator_of_notMem hu _)

lemma lintegral_boxKernel {k : ℕ} (η : ℝ) (hη : 0 < η) (c : Fin k → ℝ) :
    (∫⁻ u, boxKernel η c u) = 1 := by
  change (∫⁻ u, (closedBox c η).indicator (fun _ => boxScale k η) u) = 1
  rw [lintegral_indicator (measurableSet_closedBox c η), lintegral_const,
    Measure.restrict_apply_univ, volume_closedBox c η hη.le]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

end Support

open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

end Projection
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Reweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Reweight
open Coercivity Sphere

lemma rho_le {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) : rho ν ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))) • ν := by
  intro E
  unfold rho
  rw [withDensity_apply' _ E,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∫⁻ s in E, ENNReal.ofReal ((2:ℝ)^(2*(d/16))) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hν] with s hs
      have h := ENNReal.inv_le_inv.mpr (lower_J_on_sphere ν hν s hs)
      simpa only [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),ENNReal.inv_pow,
        show (ENNReal.ofReal (1/2:ℝ))⁻¹ = ENNReal.ofReal (2:ℝ) by rw [← ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
        ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)] using h
    _ = _ := by simp

lemma rho_finite {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν, ‖s‖=1) : IsFiniteMeasure (rho ν) := by
  have := Measure.smul_finite ν (c := ENNReal.ofReal ((2:ℝ)^(2*(d/16)))) ENNReal.ofReal_ne_top
  exact isFiniteMeasure_of_le _ (rho_le ν hν)

end Reweight
end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoiseLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight

lemma measurable_noise_density {k : ℕ} (η : ℝ) : Measurable (boxKernel (k := k) η 0) :=
  (measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)

lemma noise_probability (k : ℕ) {η : ℝ} (hη : 0 < η) : IsProbabilityMeasure (noiseLaw k η) := by
  constructor
  rw [noiseLaw,withDensity_apply _ MeasurableSet.univ]
  simpa using lintegral_boxKernel (k := k) η hη 0

lemma noise_support (k : ℕ) (η : ℝ) : ∀ᵐ e ∂noiseLaw k η, e ∈ closedBox 0 η := by
  rw [noiseLaw,ae_withDensity_iff (measurable_noise_density η)]
  filter_upwards [] with e
  intro he
  exact boxKernel_ne_zero_mem he

lemma boxScale_ne_top (k : ℕ) {η : ℝ} (hη : 0 < η) : boxScale k η ≠ ∞ := by
  unfold boxScale
  exact ENNReal.inv_ne_top.mpr (by positivity)

lemma projectedReference_measurable {k d : ℕ} (ν : Measure (Ambient d)) [SFinite (rho ν)]
    (η : ℝ) : Measurable (fun t : ((Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ)) ×
      ((Fin k → ℝ) × (Fin k → ℝ)) => projectedReference ν η t.1.1 t.1.2 t.2.1 t.2.2) := by
  unfold projectedReference
  apply Measurable.lintegral_prod_right
  have hA := measurable_boxKernel (k := k) η
  have hP := continuous_projectVector (k := k) (d := d)
  fun_prop

lemma projectedReference_le {k d : ℕ} (ν : Measure (Ambient d)) (η : ℝ)
    (X Z : Fin k → Fin d → ℝ) (y z : Fin k → ℝ) :
    projectedReference ν η X Z y z ≤ boxScale k η^2*(rho ν Set.univ) := by
  calc
    _ ≤ ∫⁻ _u,boxScale k η*boxScale k η ∂rho ν :=
      lintegral_mono (fun _ => mul_le_mul' (boxKernel_le η _ _) (boxKernel_le η _ _))
    _ = _ := by simp [pow_two]

end KernelPotential.Noise

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_EntropyDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.DriftTools

lemma compensated_log_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f q c : α → ℝ)
    (hf : ∀ᵐ x ∂μ, 0 < f x) (hq : ∀ᵐ x ∂μ, 0 < q x)
    (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (hu : AEStronglyMeasurable (fun x => q x*f x/(1+c x)) μ)
    (hmass : (∫⁻ x, ENNReal.ofReal (q x*f x/(1+c x)) ∂μ) ≤ 1)
    (hflog : Integrable (fun x => Real.log (f x)) μ)
    (hqlog : Integrable (fun x => Real.log (q x)) μ)
    (hclog : Integrable (fun x => Real.log (1+c x)) μ) :
    (∫ x,Real.log (f x) ∂μ) ≤
      (∫ x,Real.log (1+c x) ∂μ) - ∫ x,Real.log (q x) ∂μ := by
  have hu0 : ∀ᵐ x ∂μ, 0 ≤ q x*f x/(1+c x) := by
    filter_upwards [hf,hq,hc] with x hfx hqx hcx
    positivity
  have hui : Integrable (fun x => q x*f x/(1+c x)) μ :=
    ⟨hu,(hasFiniteIntegral_iff_ofReal hu0).mpr (hmass.trans_lt (by norm_num))⟩
  have huint : (∫ x,q x*f x/(1+c x) ∂μ) ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hui hu0] at hmass
    exact (ENNReal.ofReal_le_one).mp hmass
  have hpoint : ∀ᵐ x ∂μ, Real.log (f x) ≤
      q x*f x/(1+c x)-1+Real.log (1+c x)-Real.log (q x) := by
    filter_upwards [hf,hq,hc] with x hfx hqx hcx
    have hcp : 0 < 1+c x := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos hqx hfx) hcp)
    rw [Real.log_div (mul_ne_zero hqx.ne' hfx.ne') hcp.ne',Real.log_mul hqx.ne' hfx.ne'] at h
    linarith
  have hbound := integral_mono_ae hflog (((hui.sub (integrable_const 1)).add hclog).sub hqlog) hpoint
  simp only [Pi.sub_apply,Pi.add_apply] at hbound
  have he : (∫ x,q x*f x/(1+c x)-1+Real.log (1+c x)-Real.log (q x) ∂μ) =
      (∫ x,q x*f x/(1+c x) ∂μ)-1+(∫ x,Real.log (1+c x) ∂μ)-(∫ x,Real.log (q x) ∂μ) := by
    rw [integral_sub (f := fun x => q x*f x/(1+c x)-1+Real.log (1+c x))
      (g := fun x => Real.log (q x)) ((hui.sub (integrable_const 1)).add hclog) hqlog,
      integral_add (f := fun x => q x*f x/(1+c x)-1) (g := fun x => Real.log (1+c x))
        (hui.sub (integrable_const 1)) hclog,
      integral_sub (f := fun x => q x*f x/(1+c x)) (g := fun _ => (1:ℝ)) hui (integrable_const 1)]
    simp
  rw [he] at hbound
  linarith

lemma compensation_lintegral {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] (ν : Measure α) (Λ : Measure β)
    (K : β → α → ℝ≥0∞) (hxK : ∀ z, Measurable (K z))
    (κ : β → ι → ℝ≥0∞) (hκ : ∀ z, ∑ w,κ z w=1)
    (x : ι → α → ℝ≥0∞) (hx : ∀ w, Measurable (x w))
    (q : β → ℝ≥0∞) (hq : ∫⁻ z,q z ∂Λ=1) :
    (∫⁻ z,∑ w, ∫⁻ s, K z s * κ z w * q z * x w s /
      (1+∫⁻ u,K z u*x w u ∂ν) ∂ν ∂Λ) ≤ 1 := by
  calc
    _ ≤ ∫⁻ z,q z ∂Λ := by
      apply lintegral_mono
      intro z
      calc
        _ = ∑ w,κ z w*q z*((∫⁻ s,K z s*x w s ∂ν)/(1+∫⁻ u,K z u*x w u ∂ν)) := by
          apply Finset.sum_congr rfl
          intro w _
          let C := ∫⁻ u,K z u*x w u ∂ν
          calc
            _ = ∫⁻ s, (κ z w*q z/(1+C))*(K z s*x w s) ∂ν := by
              apply lintegral_congr; intro s; dsimp [C]; simp only [div_eq_mul_inv]; ring
            _ = (κ z w*q z/(1+C))*C :=
              lintegral_const_mul _ ((hxK z).mul (hx w))
            _ = _ := by dsimp [C]; simp only [div_eq_mul_inv]; ring
        _ ≤ ∑ w,κ z w*q z*1 := by
          apply Finset.sum_le_sum
          intro w _
          gcongr
          exact ENNReal.div_le_of_le_mul (by simp)
        _ = q z := by simp only [mul_one,← Finset.sum_mul,hκ z,one_mul]
    _ = 1 := hq

end KernelPotential.DriftTools

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential

namespace Geometry
lemma truncated_inverseMoment {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (D : E → ℝ) (hD : Measurable D) (hD0 : ∀ x,0 ≤ D x)
    (k : ℕ) (hk : 0 < k) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1/2:ℝ)^j} ≤
      A * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j))) (L : ℕ) :
    (∫⁻ x,(ENNReal.ofReal (D x))⁻¹^k ∂μ) ≤ μ univ +
      (∑ j ∈ Finset.range L, ENNReal.ofReal ((2:ℝ)^((j+1)*k))*μ {x|D x ≤ (1/2:ℝ)^j}) +
      A*ENNReal.ofReal ((2:ℝ)^(k+1))*ENNReal.ofReal ((1/2:ℝ)^L) := by
  let S : ℕ → Set E := fun j => {x|D x ≤ (1/2:ℝ)^j}
  let w : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((2:ℝ)^((j+1)*k))
  have hS (j : ℕ) : MeasurableSet (S j) := measurableSet_le hD measurable_const
  have hz : ∀ᵐ x ∂μ,D x ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using zeroSet_null_of_dyadic_tails μ D k A hA htail
  have heq : (fun x => (ENNReal.ofReal (D x))⁻¹^k) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((D x)⁻¹^k)) := by
    filter_upwards [hz] with x hx
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr (hD0 x)),
      ENNReal.ofReal_inv_of_pos (lt_of_le_of_ne (hD0 x) hx.symm)]
  rw [lintegral_congr_ae heq]
  calc
    _ ≤ ∫⁻ x, 1+∑' j,(S j).indicator (fun _ => w j) x ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [S,w,Set.indicator,Set.mem_ofPred_eq] using
        inv_pow_dyadic_majorant (D x) (hD0 x) k hk
    _ = μ univ+∑' j,w j*μ (S j) := by
      rw [lintegral_add_left measurable_const,lintegral_tsum (fun j =>
        (measurable_const.indicator (hS j)).aemeasurable)]
      simp only [lintegral_const,one_mul,lintegral_indicator (hS _),Measure.restrict_apply_univ]
    _ = μ univ + (∑ j ∈ Finset.range L,w j*μ (S j)) + ∑' j,w (j+L)*μ (S (j+L)) := by
      have hh : (∑ j ∈ Finset.range L,w j*μ (S j)) + (∑' j,w (j+L)*μ (S (j+L))) =
          ∑' j,w j*μ (S j) :=
        Summable.sum_add_tsum_nat_add' (f := fun j => w j*μ (S j)) (k := L) ENNReal.summable
      exact (congrArg (fun x => μ univ+x) hh.symm).trans (add_assoc _ _ _).symm
    _ ≤ μ univ+(∑ j ∈ Finset.range L,w j*μ (S j))+
        ∑' j,A*ENNReal.ofReal ((2:ℝ)^k)*ENNReal.ofReal ((1/2:ℝ)^(j+L)) := by
      refine add_le_add_right ?_ _
      apply ENNReal.tsum_le_tsum
      intro j
      calc
        w (j+L)*μ (S (j+L)) ≤ w (j+L)*(A*ENNReal.ofReal ((1/2:ℝ)^((k+1)*(j+L)))) := by
          exact mul_le_mul_right (htail (j+L)) _
        _ = _ := by
          dsimp [w]
          rw [mul_left_comm,← ENNReal.ofReal_mul (by positivity),dyadic_weight_product,
            ENNReal.ofReal_mul (by positivity)]
          ac_rfl
    _ = _ := by
      have hs : (∑' j,A*ENNReal.ofReal ((2:ℝ)^k)*ENNReal.ofReal ((1/2:ℝ)^(j+L))) =
          A*ENNReal.ofReal ((2:ℝ)^(k+1))*ENNReal.ofReal ((1/2:ℝ)^L) := by
        simp_rw [pow_add,ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1/2:ℝ)^_),
          ← mul_assoc,ENNReal.tsum_mul_right,ENNReal.tsum_mul_left,
          ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),ENNReal.tsum_geometric]
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
        simp only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat,one_div,ENNReal.one_sub_inv_two,
          inv_inv,pow_succ,ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k),mul_assoc]
        norm_num
      rw [hs]
lemma exists_good_dyadic_scale {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (D : E → ℝ) (hD : Measurable D)
    (hD0 : ∀ x,0 ≤ D x) (hD1 : ∀ᵐ x ∂μ,D x ≤ 1)
    (k : ℕ) (hk : 0 < k) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x|D x ≤ (1/2:ℝ)^j} ≤
      A*ENNReal.ofReal ((1/2:ℝ)^((k+1)*j))) (L : ℕ) (hL : 0 < L)
    (hcut : A*ENNReal.ofReal ((2:ℝ)^(k+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1) :
    ∃ j : ℕ,j<L ∧ 0 < μ {x|D x ≤ (1/2:ℝ)^j} ∧
      (∫⁻ x,(ENNReal.ofReal (D x))⁻¹^k ∂μ) ≤
        ENNReal.ofReal ((2:ℝ)^k*((L:ℝ)+2))*
          (ENNReal.ofReal ((2:ℝ)^(j*k))*μ {x|D x ≤ (1/2:ℝ)^j}) := by
  classical
  let S : ℕ → Set E := fun j => {x|D x ≤ (1/2:ℝ)^j}
  let f : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((2:ℝ)^(j*k))*μ (S j)
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range L) f
    ⟨0,Finset.mem_range.mpr hL⟩
  have hS0 : μ (S 0)=1 := by
    have he : S 0 =ᵐ[μ] univ := by
      filter_upwards [hD1] with x hx
      apply propext
      change (D x ≤ (1/2:ℝ)^0) ↔ True
      simpa using hx
    rw [measure_congr he,measure_univ]
  have hf0 : f 0=1 := by simp [f,hS0]
  have hfj : 1 ≤ f j := by rw [← hf0]; exact hmax 0 (Finset.mem_range.mpr hL)
  have hjpos : 0 < μ (S j) := by
    by_contra hn
    have hz : μ (S j)=0 := le_antisymm (not_lt.mp hn) bot_le
    simp only [f,hz,mul_zero] at hfj
    exact absurd hfj (by norm_num)
  refine ⟨j,Finset.mem_range.mp hj,hjpos,?_⟩
  have hsum : (∑ i ∈ Finset.range L,ENNReal.ofReal ((2:ℝ)^((i+1)*k))*μ (S i)) ≤
      (L:ℝ≥0∞)*(ENNReal.ofReal ((2:ℝ)^k)*f j) := by
    calc
      _ = ∑ i ∈ Finset.range L,ENNReal.ofReal ((2:ℝ)^k)*f i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [f]
        rw [Nat.add_mul,one_mul,pow_add,ENNReal.ofReal_mul (by positivity)]
        ac_rfl
      _ ≤ ∑ _i ∈ Finset.range L,ENNReal.ofReal ((2:ℝ)^k)*f j := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_right (hmax i hi) _
      _ = _ := by simp
  have hk1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal ((2:ℝ)^k) := by
    exact_mod_cast (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ 2^k)
  have h1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal ((2:ℝ)^k)*f j := by
    calc (1:ℝ≥0∞)=1*1 := by simp
         _ ≤ _ := mul_le_mul hk1 hfj (by positivity) (by positivity)
  have h := truncated_inverseMoment μ D hD hD0 k hk A hA htail L
  change _ ≤ μ univ+(∑ i ∈ Finset.range L,ENNReal.ofReal ((2:ℝ)^((i+1)*k))*μ (S i))+_ at h
  rw [measure_univ] at h
  calc
    _ ≤ 1+(L:ℝ≥0∞)*(ENNReal.ofReal ((2:ℝ)^k)*f j)+1 :=
      h.trans (add_le_add (add_le_add_right hsum 1) hcut)
    _ ≤ ENNReal.ofReal ((2:ℝ)^k)*f j+(L:ℝ≥0∞)*(ENNReal.ofReal ((2:ℝ)^k)*f j)+
        ENNReal.ofReal ((2:ℝ)^k)*f j := add_le_add (add_le_add_left h1 _) h1
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (by positivity) (by positivity)]
      simp only [ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
      change _ = _*f j
      ring
end Geometry

namespace Scale
open KernelPotential.Geometry Sphere Coercivity

lemma radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

lemma closed_cap {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Ambient d))
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) {r : ℝ} (hr : 0 < r) :
    ν (closedBall s r) ≤ ENNReal.ofReal (H*(9*3^d)*(2*r)^(d-1)) := by
  calc
    _ ≤ ν (ball s (2*r)) := measure_mono (closedBall_subset_ball (by linarith))
    _ ≤ ENNReal.ofReal H*sphereProbability d (ball s (2*r)) := by
      simpa only [Measure.smul_apply,smul_eq_mul] using hν (ball s (2*r))
    _ ≤ ENNReal.ofReal H*ENNReal.ofReal ((9*3^d:ℝ)*(2*r)^(d-1)) :=
      mul_le_mul_right (cap_bound hd s (by linarith)) _
    _ = _ := by rw [← ENNReal.ofReal_mul hH.le]; congr 1; ring

lemma norm_half_tail {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (j : ℕ) :
    ν {u | ‖u-s‖/2 ≤ (1/2:ℝ)^j} ≤
      ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
        ENNReal.ofReal ((1/2:ℝ)^((2*(d/16)+1)*j)) := by
  have he : {u : Ambient d|‖u-s‖/2 ≤ (1/2:ℝ)^j}=closedBall s (radius j) := by
    ext u
    rw [mem_closedBall,dist_eq_norm]
    change ‖u-s‖/2 ≤ (1/2:ℝ)^j ↔ ‖u-s‖ ≤ 2*(1/2:ℝ)^j
    constructor <;> intro h <;> linarith
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (H*(9*3^d)*(2*radius j)^(d-1)) := closed_cap (by omega) ν hH hν s (radius_pos j)
    _ ≤ ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1)*((1/2:ℝ)^j)^(2*(d/16)+1)) := by
      apply ENNReal.ofReal_le_ofReal
      have heq : 2*radius j=4*((1/2:ℝ)^j) := by unfold radius; ring
      rw [heq,mul_pow]
      simp only [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hj0 : (0:ℝ) ≤ (1/2:ℝ)^j := by positivity
      have hj1 : (1/2:ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact pow_le_pow_of_le_one hj0 hj1 (by have hh := Nat.div_mul_le_self d 16; omega)
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity),← pow_mul, Nat.mul_comm j]

lemma exists_J_scale {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (hs : ‖s‖=1) (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1) :
    ∃ j : ℕ,j<L ∧ 0 < ν (closedBall s (radius j)) ∧
      J ν s ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*((L:ℝ)+2))*
        (ENNReal.ofReal ((2:ℝ)^(j*(2*(d/16))))*ν (closedBall s (radius j))) := by
  have hsupport : ∀ᵐ u ∂ν,‖u‖=1 :=
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega))
  have hD1 : ∀ᵐ u ∂ν,‖u-s‖/2 ≤ 1 := by
    filter_upwards [hsupport] with u hu
    have hh := norm_sub_le u s
    rw [hu,hs] at hh
    linarith
  obtain ⟨j,hj,hjm,hjb⟩ := exists_good_dyadic_scale ν (fun u => ‖u-s‖/2)
    (by fun_prop) (fun _ => by positivity) hD1 (2*(d/16)) (by omega)
    (ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))) ENNReal.ofReal_ne_top
    (norm_half_tail hd ν hH hν s) L hL hcut
  have he : {u : Ambient d|‖u-s‖/2 ≤ (1/2:ℝ)^j}=closedBall s (radius j) := by
    ext u
    rw [mem_closedBall,dist_eq_norm]
    change ‖u-s‖/2 ≤ (1/2:ℝ)^j ↔ ‖u-s‖ ≤ 2*(1/2:ℝ)^j
    constructor <;> intro h <;> linarith
  rw [he] at hjm hjb
  refine ⟨j,hj,hjm,le_trans ?_ hjb⟩
  apply lintegral_mono
  intro u
  apply pow_le_pow_left₀ zero_le
  apply ENNReal.inv_le_inv.mpr
  apply ENNReal.ofReal_le_ofReal
  have hh := norm_nonneg (u-s)
  linarith

end Scale

end KernelPotential

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_GaussianReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open GaussianTools

lemma applyRows_sub {p d : ℕ} (X : Mat p d) (s u : Vec d) :
    applyRows X (s-u)=applyRows X s-applyRows X u := by
  ext i
  simp [applyRows,mul_sub,Finset.sum_sub_distrib]

lemma atDensity_pos {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ) (u : Vec d) :
    0 < atDensity r X y u := labelDensity_pos hr _

lemma continuous_atDensity {p d : ℕ} (r : ℝ) :
    Continuous (fun t : (Mat p d × (Fin p → ℝ)) × Vec d => atDensity r t.1.1 t.1.2 t.2) := by
  unfold atDensity labelDensity gaussianPDFReal applyRows
  fun_prop

lemma densityBound_pos (p : ℕ) {r : ℝ} (hr : 0 < r) : 0 < densityBound p r := by
  unfold densityBound; positivity

lemma atDensity_le {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ) (u : Vec d) :
    atDensity r X y u ≤ densityBound p r := by
  unfold atDensity labelDensity
  calc
    _ ≤ ∏ _i : Fin p,(Real.sqrt (2*Real.pi*r^2))⁻¹ := by
      apply Finset.prod_le_prod (fun _ _ => gaussianPDFReal_nonneg _ _ _)
      intro i _
      unfold gaussianPDFReal
      simp only [NNReal.coe_mk]
      calc
        _ ≤ (Real.sqrt (2*Real.pi*r^2))⁻¹*1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith [sq_nonneg ((y-applyRows X u) i)]) (by positivity))
        _ = _ := mul_one _
    _ = _ := by simp [densityBound]

lemma integrable_atDensity {p d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ) :
    Integrable (atDensity r X y) ν := by
  have hm : Measurable (atDensity r X y) := by
    unfold atDensity labelDensity gaussianPDFReal applyRows
    fun_prop
  refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := densityBound p r) ?_⟩
  exact (Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs,abs_of_pos (atDensity_pos hr X y u)]
      exact atDensity_le hr X y u))

lemma integral_atDensity_pos {p d : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ) :
    0 < ∫ u,atDensity r X y u ∂ν := by
  apply (integral_pos_iff_support_of_nonneg (fun u => (atDensity_pos hr X y u).le)
    (integrable_atDensity ν hr X y)).mpr
  have he : Function.support (atDensity r X y)=univ := by
    ext u; simp [Function.mem_support,(atDensity_pos hr X y u).ne']
  rw [he,measure_univ]
  norm_num

lemma integral_density_y {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d) (u : Vec d) :
    (∫ y : Fin p → ℝ,atDensity r X y u)=1 := by
  have hv : (NNReal.mk (r^2) (sq_nonneg r)) ≠ 0 := by
    intro h; have hh := congrArg (fun t : NNReal => (t:ℝ)) h
    exact (pow_ne_zero 2 hr.ne') hh
  have he (y : Fin p → ℝ) : atDensity r X y u =
      ∏ i,gaussianPDFReal (applyRows X u i) (NNReal.mk (r^2) (sq_nonneg r)) (y i) := by
    unfold atDensity labelDensity gaussianPDFReal
    simp
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_gaussianPDFReal_eq_one _ hv]

lemma lintegral_density_y {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d) (u : Vec d) :
    (∫⁻ y : Fin p → ℝ,ENNReal.ofReal (atDensity r X y u))=1 := by
  have hi : Integrable (fun y : Fin p → ℝ => atDensity r X y u) volume :=
    Integrable.of_integral_ne_zero (by rw [integral_density_y hr X u]; norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => (atDensity_pos hr _ _ _).le)),
    integral_density_y hr X u,ENNReal.ofReal_one]

lemma measurable_mixture {p d L : ℕ} (ν : Measure (Vec d)) [SFinite ν] (r : Fin L → ℝ) :
    Measurable (fun t : Mat p d × (Fin p → ℝ) => mixture ν r t.1 t.2) := by
  unfold mixture
  apply Measurable.const_mul
  apply Finset.measurable_fun_sum
  intro j _
  exact (continuous_atDensity (p := p) (d := d) (r j)).stronglyMeasurable.integral_prod_right.measurable

lemma mixture_lower {p d L : ℕ} (ν : Measure (Vec d)) (r : Fin L → ℝ)
    (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ) (j : Fin L) :
    (∫ u,atDensity (r j) X y u ∂ν)/(L:ℝ) ≤ mixture ν r X y := by
  unfold mixture
  rw [div_eq_mul_inv,mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.single_le_sum (fun i _ => integral_nonneg (fun u => (atDensity_pos (hr i) X y u).le)) (Finset.mem_univ j)

lemma mixture_pos {p d L : ℕ} (hL : 0 < L) (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ) :
    0 < mixture ν r X y :=
  lt_of_lt_of_le (div_pos (integral_atDensity_pos ν (hr ⟨0,hL⟩) X y) (by positivity))
    (mixture_lower ν r hr X y ⟨0,hL⟩)

lemma lintegral_mixture {p d L : ℕ} (hL : 0 < L) (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X : Mat p d) :
    (∫⁻ y : Fin p → ℝ,ENNReal.ofReal (mixture ν r X y))=1 := by
  have he (y : Fin p → ℝ) : ENNReal.ofReal (mixture ν r X y)=
      (L:ℝ≥0∞)⁻¹*∑ j,∫⁻ u,ENNReal.ofReal (atDensity (r j) X y u) ∂ν := by
    unfold mixture
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_natCast,
      ENNReal.ofReal_sum_of_nonneg]
    · congr 1; apply Finset.sum_congr rfl; intro j _
      exact ofReal_integral_eq_lintegral_ofReal (integrable_atDensity ν (hr j) X y)
        (Filter.Eventually.of_forall (fun u => (atDensity_pos (hr j) _ _ _).le))
    · intro j _; exact integral_nonneg (fun u => (atDensity_pos (hr j) _ _ _).le)
  simp_rw [he]
  rw [lintegral_const_mul]
  · rw [lintegral_finsetSum]
    · have hj (j : Fin L) : (∫⁻ y : Fin p → ℝ,∫⁻ u,ENNReal.ofReal (atDensity (r j) X y u) ∂ν)=1 := by
        rw [lintegral_lintegral_swap]
        · simp only [lintegral_density_y (hr j) X,lintegral_one,measure_univ]
        · exact ((continuous_atDensity (r j)).measurable.comp
            ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).ennreal_ofReal.aemeasurable
      simp_rw [hj]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast hL.ne') (by simp)
    · intro j _
      apply Measurable.lintegral_prod_right
      exact ((continuous_atDensity (r j)).measurable.comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  · apply Finset.measurable_fun_sum; intro j _
    apply Measurable.lintegral_prod_right
    exact ((continuous_atDensity (r j)).measurable.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).ennreal_ofReal

end ReferenceGaussian

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open GaussianTools

lemma continuous_integrable_on_support {d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {f : Vec d → ℝ} (hf : Continuous f) (s : Vec d) (R : ℝ)
    (hs : ∀ᵐ u ∂ν, u ∈ closedBall s R) : Integrable f ν := by
  have h := hf.continuousOn.integrableOn_compact (μ := ν) (isCompact_closedBall s R)
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hs] at h

lemma integrable_log_atDensity {p d : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 < r) (X : Mat p d) (y : Fin p → ℝ)
    (s : Vec d) (R : ℝ) (hs : ∀ᵐ u ∂ν,u ∈ closedBall s R) :
    Integrable (fun u => Real.log (atDensity r X y u)) ν := by
  apply continuous_integrable_on_support ν _ s R hs
  have hc : Continuous (fun u => atDensity r X y u) := by
    unfold atDensity labelDensity gaussianPDFReal applyRows
    fun_prop
  exact hc.log (fun u => (atDensity_pos hr X y u).ne')

lemma log_integral_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (v : α → ℝ)
    (hv : ∀ᵐ x ∂μ,0 < v x) (hvi : Integrable v μ)
    (hvlog : Integrable (fun x => Real.log (v x)) μ)
    {a : ℝ} (ha : 0 < a) (hva : (∫ x,v x ∂μ) ≤ a) :
    (∫ x,Real.log (v x) ∂μ) ≤ Real.log a := by
  have hpoint : ∀ᵐ x ∂μ,Real.log (v x) ≤ v x/a-1+Real.log a := by
    filter_upwards [hv] with x hx
    have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
    rw [Real.log_div hx.ne' ha.ne'] at h
    linarith
  have h := integral_mono_ae hvlog (((hvi.div_const a).sub (integrable_const 1)).add (integrable_const (Real.log a))) hpoint
  have he : (∫ x,v x/a-1+Real.log a ∂μ) = (∫ x,v x ∂μ)/a-1+Real.log a := by
    rw [integral_add (f := fun x => v x/a-1) (g := fun _ => Real.log a)
        ((hvi.div_const a).sub (integrable_const 1)) (integrable_const _),
      integral_sub (f := fun x => v x/a) (g := fun _ => (1:ℝ)) (hvi.div_const a) (integrable_const 1),
      integral_div]
    simp
  change (∫ x,Real.log (v x) ∂μ) ≤ (∫ x,v x/a-1+Real.log a ∂μ) at h
  rw [he] at h
  have hb : (∫ x,v x ∂μ)/a ≤ 1 := (div_le_one ha).mpr hva
  linarith

lemma local_log_lower {p d L : ℕ} (hL : 0 < L) (ν τ : Measure (Vec d))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure τ] {m : ℝ} (hm : 0 < m)
    (hdom : ENNReal.ofReal m • τ ≤ ν)
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ)
    (s : Vec d) (R : ℝ) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R) (j : Fin L) :
    Real.log m-Real.log L+(∫ u,Real.log (atDensity (r j) X y u) ∂τ) ≤
      Real.log (mixture ν r X y) := by
  have hpos := integral_atDensity_pos τ (hr j) X y
  have hpoint : m*(∫ u,atDensity (r j) X y u ∂τ)/(L:ℝ) ≤ mixture ν r X y := by
    have h := integral_mono_measure hdom
      (Filter.Eventually.of_forall (fun u => (atDensity_pos (hr j) X y u).le))
      (integrable_atDensity ν (hr j) X y)
    rw [integral_smul_measure,ENNReal.toReal_ofReal hm.le,smul_eq_mul] at h
    exact (div_le_div_of_nonneg_right h (by positivity)).trans (mixture_lower ν r hr X y j)
  have hj := log_integral_ge τ (atDensity (r j) X y)
    (Filter.Eventually.of_forall (fun u => atDensity_pos (hr j) X y u))
    (integrable_atDensity τ (hr j) X y) (integrable_log_atDensity τ (hr j) X y s R hs) hpos le_rfl
  have hlog := Real.log_le_log (by positivity : 0 < m*(∫ u,atDensity (r j) X y u ∂τ)/(L:ℝ)) hpoint
  rw [Real.log_div (mul_ne_zero hm.ne' hpos.ne') (by positivity),Real.log_mul hm.ne' hpos.ne'] at hlog
  linarith

lemma energy_nonneg {p d : ℕ} (X : Mat p d) (v : Vec d) (e : Fin p → ℝ) :
    0 ≤ energy X v e := Finset.sum_nonneg (fun i _ => sq_nonneg (applyRows X v i+e i))
lemma matEnergy_nonneg {p d : ℕ} (X : Mat p d) : 0 ≤ matEnergy X :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (X i j)))

lemma energy_le {p d : ℕ} (X : Mat p d) (v : Vec d) (e : Fin p → ℝ) :
    energy X v e ≤ 2*matEnergy X*‖v‖^2+2*∑ i,(e i)^2 := by
  have hh (i : Fin p) : (applyRows X v i)^2 ≤ (∑ j,(X i j)^2)*‖v‖^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) (fun j => v j)
    dsimp [applyRows]
    rw [EuclideanSpace.norm_sq_eq]
    simpa using h
  calc
    _ ≤ ∑ i,(2*((∑ j,(X i j)^2)*‖v‖^2)+2*(e i)^2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [hh i,sq_nonneg (applyRows X v i-e i)]
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]; dsimp [matEnergy]; ring

lemma integrable_matEnergy {p d : ℕ} :
    Integrable (@matEnergy p d) (Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (((memLp_id_gaussianReal (2:NNReal)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) j)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin p => scalarRow d) i)).integrable_sq

lemma energy_rows_le {p d : ℕ} (v : Vec d) (e : Fin p → ℝ) :
    (∫ X : Mat p d,energy X v e ∂Measure.pi (fun _ : Fin p => scalarRow d)) ≤
      2*(p:ℝ)*‖v‖^2+2*∑ i,(e i)^2 := rows_shift_energy v e

lemma log_atDensity_shift {p d : ℕ} {r : ℝ} (hr : 0 < r) (X : Mat p d)
    (s u : Vec d) (e : Fin p → ℝ) :
    Real.log (atDensity r X (applyRows X s+e) u) =
      -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-energy X (s-u) e/(2*r^2) := by
  rw [atDensity,log_labelDensity hr]
  congr 2
  unfold energy
  apply Finset.sum_congr rfl
  intro i _
  rw [applyRows_sub]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

end ReferenceGaussian

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open GaussianTools

lemma integrable_energy_joint {p d : ℕ} (τ : Measure (Vec d)) [IsProbabilityMeasure τ]
    (s : Vec d) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R)
    (e : Fin p → ℝ) :
    Integrable (fun t : Mat p d × Vec d => energy t.1 (s-t.2) e)
      ((Measure.pi (fun _ : Fin p => scalarRow d)).prod τ) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hm : Measurable (fun t : Mat p d × Vec d => energy t.1 (s-t.2) e) := by
    unfold energy applyRows; fun_prop
  apply ((((integrable_matEnergy (p := p) (d := d)).comp_fst τ).const_mul (2*R^2)).add
    (integrable_const (2*∑ i,e i^2))).mono' hm.aestronglyMeasurable
  have hae : ∀ᵐ t : Mat p d × Vec d ∂(Measure.pi (fun _ : Fin p => scalarRow d)).prod τ,
      t.2 ∈ closedBall s R := measurePreserving_snd.quasiMeasurePreserving.ae hs
  filter_upwards [hae] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (energy_nonneg _ _ _)]
  have ht' : ‖s-t.2‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using ht
  have hb := energy_le t.1 (s-t.2) e
  have hsq : ‖s-t.2‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr ht'
  change energy t.1 (s-t.2) e ≤ 2*R^2*matEnergy t.1+2*∑ i,e i^2
  nlinarith [mul_le_mul_of_nonneg_left hsq (matEnergy_nonneg t.1)]

lemma energy_rows_local_le {p d : ℕ} (τ : Measure (Vec d)) [IsProbabilityMeasure τ]
    (s : Vec d) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R)
    (e : Fin p → ℝ) :
    (∫ X : Mat p d,∫ u,energy X (s-u) e ∂τ ∂Measure.pi (fun _ : Fin p => scalarRow d)) ≤
      2*(p:ℝ)*R^2+2*∑ i,e i^2 := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  rw [integral_integral_swap (integrable_energy_joint τ s hR hs e)]
  have hi := (integrable_energy_joint τ s hR hs e).integral_prod_right
  calc
    _ ≤ ∫ _u,2*(p:ℝ)*R^2+2*∑ i,e i^2 ∂τ := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hs] with u hu
      have hu' : ‖s-u‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using hu
      have hsq : ‖s-u‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hu' 2
      exact (energy_rows_le (s-u) e).trans (by gcongr)
    _ = _ := by simp

lemma integrable_log_shift_rows {p d : ℕ} (τ : Measure (Vec d)) [IsProbabilityMeasure τ]
    (s : Vec d) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R)
    {r : ℝ} (hr : 0 < r) (e : Fin p → ℝ) :
    Integrable (fun X : Mat p d => ∫ u,Real.log (atDensity r X (applyRows X s+e) u) ∂τ)
      (Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi := (integrable_energy_joint τ s hR hs e).integral_prod_left
  have he (X : Mat p d) :
      (∫ u,Real.log (atDensity r X (applyRows X s+e) u) ∂τ) =
      -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-(∫ u,energy X (s-u) e ∂τ)/(2*r^2) := by
    simp_rw [log_atDensity_shift hr]
    have hei : Integrable (fun u => energy X (s-u) e) τ := by
      apply continuous_integrable_on_support τ _ s R hs
      unfold energy applyRows; fun_prop
    rw [integral_sub (integrable_const _) (hei.div_const _),integral_div]
    simp
  simp_rw [he]
  exact (integrable_const _).sub (hi.div_const _)

lemma log_shift_rows_local_ge {p d : ℕ} (τ : Measure (Vec d)) [IsProbabilityMeasure τ]
    (s : Vec d) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R)
    {r : ℝ} (hr : 0 < r) (e : Fin p → ℝ) :
    -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-
      ((p:ℝ)*R^2+∑ i,e i^2)/r^2 ≤
      (∫ X : Mat p d,∫ u,Real.log (atDensity r X (applyRows X s+e) u) ∂τ
        ∂Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  simp_rw [log_atDensity_shift hr]
  have hi := integrable_energy_joint τ s hR hs e
  have he (X : Mat p d) :
      (∫ u,-(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-energy X (s-u) e/(2*r^2) ∂τ) =
      -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-(∫ u,energy X (s-u) e ∂τ)/(2*r^2) := by
    have hei : Integrable (fun u => energy X (s-u) e) τ := by
      apply continuous_integrable_on_support τ _ s R hs
      unfold energy applyRows; fun_prop
    rw [integral_sub (integrable_const _) (hei.div_const _),integral_div]; simp
  simp_rw [he]
  rw [integral_sub (integrable_const _) (hi.integral_prod_left.div_const _),integral_div]
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  have hb := energy_rows_local_le τ s hR hs e
  have hrr : 0 < r^2 := sq_pos_of_pos hr
  have hdiv := (div_le_div_of_nonneg_right hb (by positivity : 0 ≤ 2*r^2))
  have heq : (2*(p:ℝ)*R^2+2*∑ i,e i^2)/(2*r^2)=((p:ℝ)*R^2+∑ i,e i^2)/r^2 := by ring
  rw [heq] at hdiv
  linarith

end ReferenceGaussian

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open GaussianTools

lemma mixture_upper {p d L : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X : Mat p d) (y : Fin p → ℝ) :
    mixture ν r X y ≤ (L:ℝ)⁻¹*∑ j,densityBound p (r j) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∫ _u,densityBound p (r j) ∂ν := integral_mono (integrable_atDensity ν (hr j) X y)
      (integrable_const _) (fun u => atDensity_le (hr j) X y u)
    _ = _ := by simp

lemma integrable_log_mixture_rows {p d L : ℕ} (hL : 0 < L)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (s : Vec d)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂ν,u ∈ closedBall s R) (e : Fin p → ℝ) :
    Integrable (fun X : Mat p d => Real.log (mixture ν r X (applyRows X s+e)))
      (Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  let j : Fin L := ⟨0,hL⟩
  let U : ℝ := (L:ℝ)⁻¹*∑ j,densityBound p (r j)
  have hU : 0 < U := by
    apply mul_pos (by positivity)
    exact Finset.sum_pos (fun j _ => densityBound_pos p (hr j)) ⟨j,Finset.mem_univ _⟩
  have hm : Measurable (fun X : Mat p d => Real.log (mixture ν r X (applyRows X s+e))) := by
    apply Measurable.log
    unfold mixture
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro l _
    have hi : Continuous (fun t : Mat p d × Vec d => atDensity (r l) t.1 (applyRows t.1 s+e) t.2) := by
      unfold atDensity labelDensity gaussianPDFReal applyRows
      fun_prop
    exact hi.stronglyMeasurable.integral_prod_right.measurable
  refine integrable_of_le_of_le hm.aestronglyMeasurable ?_ ?_
    ((integrable_const (-Real.log L)).add (integrable_log_shift_rows ν s hR hs (hr j) e))
    (integrable_const (Real.log U))
  · filter_upwards [] with X
    have h := local_log_lower hL ν ν (m := 1) (by norm_num) (by simp) r hr X
      (applyRows X s+e) s R hs j
    simpa using h
  · filter_upwards [] with X
    exact Real.log_le_log (mixture_pos hL ν r hr X _) (mixture_upper ν r hr X _)

lemma local_mixture_rows_ge {p d L : ℕ} (hL : 0 < L)
    (ν τ : Measure (Vec d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    {m : ℝ} (hm : 0 < m) (hdom : ENNReal.ofReal m • τ ≤ ν)
    (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (s : Vec d)
    {R R₀ : ℝ} (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀)
    (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R) (hs₀ : ∀ᵐ u ∂ν,u ∈ closedBall s R₀)
    (e : Fin p → ℝ) (j : Fin L) :
    Real.log m-Real.log L-(p:ℝ)*Real.log (r j)-(p:ℝ)/2*Real.log (2*Real.pi)-
      ((p:ℝ)*R^2+∑ i,e i^2)/(r j)^2 ≤
      (∫ X : Mat p d,Real.log (mixture ν r X (applyRows X s+e))
        ∂Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi := integrable_log_shift_rows τ s hR hs (hr j) e
  have h := integral_mono ((integrable_const (Real.log m-Real.log L)).add hi)
    (integrable_log_mixture_rows hL ν r hr s hR₀ hs₀ e)
    (fun X => local_log_lower hL ν τ hm hdom r hr X (applyRows X s+e) s R hs j)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) hi] at h
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at h
  have hb := log_shift_rows_local_ge τ s hR hs (hr j) e
  linarith

end ReferenceGaussian

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ScaledReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KernelPotential.Scale
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Sphere Coercivity ReferenceGaussian GaussianTools

lemma normalized_restriction {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (E : Set α) (hE : MeasurableSet E) (hm : 0 < ν E) :
    ∃ τ : Measure α, IsProbabilityMeasure τ ∧
      ENNReal.ofReal (ν E).toReal • τ ≤ ν ∧ (∀ᵐ u ∂τ,u ∈ E) := by
  let τ := (ν E)⁻¹ • ν.restrict E
  have hmt : ν E ≠ ∞ := measure_ne_top _ _
  refine ⟨τ,?_,?_,?_⟩
  · constructor
    simp only [τ,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hm.ne' hmt
  · rw [ENNReal.ofReal_toReal hmt]
    dsimp [τ]
    rw [smul_smul,ENNReal.mul_inv_cancel hm.ne' hmt,one_smul]
    exact Measure.restrict_le_self
  · exact (Measure.smul_absolutelyContinuous (μ := ν.restrict E) (c := (ν E)⁻¹)).ae_le (ae_restrict_mem hE)

lemma dyadic_log_identity (p j : ℕ) :
    Real.log ((2:ℝ)^(j*p)) = (p:ℝ)*Real.log 2-(p:ℝ)*Real.log (radius j) := by
  unfold radius
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow,
    Real.log_div (by norm_num) (by norm_num),Real.log_one]
  push_cast
  ring

lemma chosen_scale_log {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    {L j : ℕ} (hm : 0 < ν (closedBall s (radius j)))
    (hJ : J ν s ≤ ENNReal.ofReal ((2:ℝ)^(2*(d/16))*((L:ℝ)+2))*
      (ENNReal.ofReal ((2:ℝ)^(j*(2*(d/16))))*ν (closedBall s (radius j)))) :
    Real.log ((J ν s).toReal) ≤
      2*(2*(d/16):ℕ)*Real.log 2+Real.log ((L:ℝ)+2)+
       Real.log (ν (closedBall s (radius j))).toReal-(2*(d/16):ℕ)*Real.log (radius j) := by
  have hjpos : 0 < (J ν s).toReal :=
    lt_of_lt_of_le (by positivity) (J_real_bounds hd ν hH hν s hs).1
  have hmt : ν (closedBall s (radius j)) ≠ ∞ := measure_ne_top _ _
  have hmr : 0 < (ν (closedBall s (radius j))).toReal := ENNReal.toReal_pos hm.ne' hmt
  have hto := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt)) hJ
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2^(2*(d/16))*((L:ℝ)+2)),
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2^(j*(2*(d/16))))] at hto
  have hlog := Real.log_le_log hjpos hto
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hmr.ne',Real.log_pow,dyadic_log_identity] at hlog
  push_cast at hlog ⊢
  linarith

lemma radius_mono {i j : ℕ} (hij : i ≤ j) : radius j ≤ radius i := by
  unfold radius
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hij) (by norm_num)

lemma reference_J_lower {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (hs : ‖s‖=1) (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1)
    (e : Fin (2*(d/16)) → ℝ) (he : ∀ i,|e i| ≤ radius L) :
    Real.log (J ν s).toReal-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤
      (∫ X : Mat (2*(d/16)) d,
        Real.log (mixture ν (fun j : Fin L => radius j) X (applyRows X s+e))
        ∂Measure.pi (fun _ : Fin (2*(d/16)) => scalarRow d)) := by
  obtain ⟨j,hj,hm,hjb⟩ := exists_J_scale hd ν hH hν s hs L hL hcut
  obtain ⟨τ,hτ,hdom,hτs⟩ := normalized_restriction ν (closedBall s (radius j)) measurableSet_closedBall hm
  have := hτ
  have hmr : 0 < (ν (closedBall s (radius j))).toReal := ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)
  have hsupport : ∀ᵐ u ∂ν,u ∈ closedBall s 2 := by
    filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega))] with u hu
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by rw [hu,hs]; norm_num)
  have hlow := local_mixture_rows_ge hL ν τ hmr hdom (fun j : Fin L => radius j)
    (fun j => radius_pos j) s (radius_pos j).le (by norm_num : (0:ℝ) ≤ 2)
    hτs hsupport e ⟨j,hj⟩
  have hJlog := chosen_scale_log hd ν hH hν s hs hm hjb
  have he2 : (∑ i : Fin (2*(d/16)),e i^2) ≤ (2*(d/16):ℕ)*(radius j)^2 := by
    calc
      _ ≤ ∑ _i : Fin (2*(d/16)),(radius j)^2 := by
        apply Finset.sum_le_sum; intro i _
        have hie : |e i| ≤ radius j := (he i).trans (radius_mono (by omega))
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hie 2
      _ = _ := by simp
  have henergy : ((2*(d/16):ℕ)*(radius j)^2+∑ i,e i^2)/(radius j)^2 ≤ 2*(2*(d/16):ℕ) := by
    apply (div_le_iff₀ (sq_pos_of_pos (radius_pos j))).mpr
    linarith
  have hlL : Real.log L ≤ Real.log ((L:ℝ)+2) := Real.log_le_log (by positivity) (by linarith)
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hlpi : Real.log (2*Real.pi) ≤ 7 := by
    have hh := Real.log_le_sub_one_of_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)
    linarith [Real.pi_lt_four]
  have hp : ((2*(d/16):ℕ):ℝ) ≤ (d:ℝ) := by
    have h := Nat.div_mul_le_self d 16
    exact_mod_cast (show 2*(d/16) ≤ d by omega)
  dsimp only at hlow
  push_cast at hlow hJlog he2 henergy hp ⊢
  have hk0 : (0:ℝ) ≤ (d/16:ℕ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl2 (show (0:ℝ) ≤ 4*(d/16:ℕ) by positivity),
    mul_le_mul_of_nonneg_left hlpi (show (0:ℝ) ≤ (d/16:ℕ) by positivity)]

end KernelPotential.Scale
open MeasureTheory ProbabilityTheory

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_RowConcatenation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace RowConcat

lemma join_apply {E : Type*} [MeasurableSpace E] (k : ℕ) (x y : Fin k → E) (i : Fin (2*k)) :
    join k (x,y) i=Sum.elim x y ((index k).symm i) := by
  obtain ⟨j,rfl⟩ := (index k).surjective i
  change (Equiv.piCongrLeft (fun _ : Fin (2*k) => E) (index k))
    ((Equiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => E)).symm (x,y)) ((index k) j)=_
  rw [Equiv.piCongrLeft_apply_apply,Equiv.symm_apply_apply]
  cases j <;> rfl

lemma join_bound {E : Type*} [MeasurableSpace E] (k : ℕ) (x y : Fin k → E)
    (P : E → Prop) (hx : ∀ i,P (x i)) (hy : ∀ i,P (y i)) : ∀ i,P (join k (x,y) i) := by
  intro i
  rw [join_apply]
  cases (index k).symm i with
  | inl i => exact hx i
  | inr i => exact hy i

lemma join_add (k : ℕ) (x y e f : Fin k → ℝ) :
    join k (x+e,y+f)=join k (x,y)+join k (e,f) := by
  ext i
  simp only [join_apply,Pi.add_apply]
  cases (index k).symm i <;> rfl

lemma join_rows (k d : ℕ) (X Z : Fin k → Fin d → ℝ) (s : Fin d → ℝ) :
    join k ((fun i => ∑ j,X i j*s j),(fun i => ∑ j,Z i j*s j))=
      (fun i => ∑ j,join k (X,Z) i j*s j) := by
  ext i
  simp only [join_apply]
  cases (index k).symm i <;> rfl

lemma join_measurePreserving {E : Type*} [MeasurableSpace E] (k : ℕ) (μ : Measure E) [SigmaFinite μ] :
    MeasurePreserving (join (E := E) k)
      ((Measure.pi (fun _ : Fin k => μ)).prod (Measure.pi (fun _ : Fin k => μ)))
      (Measure.pi (fun _ : Fin (2*k) => μ)) := by
  exact (measurePreserving_piCongrLeft (fun _ : Fin (2*k) => μ) (index k)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin k ⊕ Fin k => μ))

lemma join_volume_measurePreserving (k : ℕ) :
    MeasurePreserving (join (E := ℝ) k) (volume.prod volume) volume := by
  simpa only [← volume_pi] using join_measurePreserving k (volume : Measure ℝ)
end RowConcat

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_PairReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.PairReference
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Sphere Coercivity Scale ReferenceGaussian GaussianTools RowConcat

lemma density_pos {k d L : ℕ} (hL : 0 < L) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (r : Fin L → ℝ) (hr : ∀ j,0 < r j)
    (X Z : Mat k d) (y z : Fin k → ℝ) : 0 < density ν r X Z y z :=
  mixture_pos hL ν r hr _ _

lemma density_measurable {k d L : ℕ} (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (r : Fin L → ℝ) : Measurable (fun t : (Mat k d × Mat k d) × ((Fin k → ℝ) × (Fin k → ℝ)) =>
      density ν r t.1.1 t.1.2 t.2.1 t.2.2) := by
  have hM := measurable_mixture (p := 2*k) ν r
  have hX := (join (E := Fin d → ℝ) k).measurable
  have hY := (join (E := ℝ) k).measurable
  unfold density
  fun_prop

lemma density_probability {k d L : ℕ} (hL : 0 < L) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (r : Fin L → ℝ) (hr : ∀ j,0 < r j) (X Z : Mat k d) :
    (∫⁻ yz : (Fin k → ℝ) × (Fin k → ℝ),ENNReal.ofReal (density ν r X Z yz.1 yz.2)
      ∂(volume : Measure (Fin k → ℝ)).prod volume)=1 := by
  have hm : Measurable (fun y : Fin (2*k) → ℝ => ENNReal.ofReal (mixture ν r (join k (X,Z)) y)) :=
    ((measurable_mixture ν r).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have h := (join_volume_measurePreserving k).lintegral_comp hm
  change (∫⁻ yz,ENNReal.ofReal (mixture ν r (join k (X,Z)) (join k yz)) ∂volume.prod volume)=1
  rw [h]
  exact lintegral_mixture hL ν r hr _

end KernelPotential.PairReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open GaussianTools
lemma log_mixture_lower_linear {p d L : ℕ} (hL : 0 < L)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] (r : Fin L → ℝ)
    (hr : ∀ j,0 < r j) (s : Vec d) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hs : ∀ᵐ u ∂ν,u ∈ closedBall s R) (X : Mat p d) (e : Fin p → ℝ)
    (he : ∀ i,|e i| ≤ T) (j : Fin L) :
    -Real.log L-(p:ℝ)*Real.log (r j)-(p:ℝ)/2*Real.log (2*Real.pi)-
      (R^2*matEnergy X+(p:ℝ)*T^2)/(r j)^2 ≤
        Real.log (mixture ν r X (applyRows X s+e)) := by
  have hl := local_log_lower hL ν ν (m := 1) (by norm_num) (by simp) r hr X
    (applyRows X s+e) s R hs j
  have hei : Integrable (fun u => energy X (s-u) e) ν := by
    apply continuous_integrable_on_support ν _ s R hs
    unfold energy applyRows; fun_prop
  have henergy : (∫ u,energy X (s-u) e ∂ν) ≤ 2*R^2*matEnergy X+2*(p:ℝ)*T^2 := by
    calc
      _ ≤ ∫ _u,2*R^2*matEnergy X+2*(p:ℝ)*T^2 ∂ν := by
        apply integral_mono_ae hei (integrable_const _)
        filter_upwards [hs] with u hu
        have huv : ‖s-u‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using hu
        have hs2 := (sq_le_sq₀ (norm_nonneg _) hR).2 huv
        have he2 : (∑ i,e i^2) ≤ (p:ℝ)*T^2 := by
          calc
            _ ≤ ∑ _i : Fin p,T^2 := Finset.sum_le_sum (fun i _ => by
              simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT).2 (he i))
            _ = _ := by simp
        have hb := energy_le X (s-u) e
        nlinarith [mul_le_mul_of_nonneg_left hs2 (matEnergy_nonneg X)]
      _ = _ := by simp
  have heq : (∫ u,Real.log (atDensity (r j) X (applyRows X s+e) u) ∂ν)=
      -(p:ℝ)*Real.log (r j)-(p:ℝ)/2*Real.log (2*Real.pi)-(∫ u,energy X (s-u) e ∂ν)/(2*(r j)^2) := by
    simp_rw [log_atDensity_shift (hr j)]
    rw [integral_sub (integrable_const _) (hei.div_const _),integral_div]
    simp
  rw [heq,Real.log_one,zero_sub] at hl
  have hb := div_le_div_of_nonneg_right henergy (by positivity : 0 ≤ 2*(r j)^2)
  have hd : (2*R^2*matEnergy X+2*(p:ℝ)*T^2)/(2*(r j)^2)=
      (R^2*matEnergy X+(p:ℝ)*T^2)/(r j)^2 := by ring
  rw [hd] at hb
  linarith

lemma log_mixture_uniform_bound {p d L : ℕ} (hL : 0 < L)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] (r : Fin L → ℝ)
    (hr : ∀ j,0 < r j) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (s : Vec d), (∀ᵐ u ∂ν,u ∈ closedBall s R) →
      ∀ (X : Mat p d) (e : Fin p → ℝ), (∀ i,|e i| ≤ T) →
        |Real.log (mixture ν r X (applyRows X s+e))| ≤ M*(1+matEnergy X) := by
  let j : Fin L := ⟨0,hL⟩
  let a := -Real.log L-(p:ℝ)*Real.log (r j)-(p:ℝ)/2*Real.log (2*Real.pi)-(p:ℝ)*T^2/(r j)^2
  let b := R^2/(r j)^2
  let c := Real.log ((L:ℝ)⁻¹*∑ j,densityBound p (r j))
  let M := |a|+b+|c|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  intro s hs X e he
  have hl := log_mixture_lower_linear hL ν r hr s hR hT hs X e he j
  have hu := Real.log_le_log (mixture_pos hL ν r hr X (applyRows X s+e)) (mixture_upper ν r hr X (applyRows X s+e))
  have hl' : a-b*matEnergy X ≤ Real.log (mixture ν r X (applyRows X s+e)) := by
    dsimp [a,b]; convert hl using 1; ring
  have hu' : Real.log (mixture ν r X (applyRows X s+e)) ≤ c := hu
  apply abs_le.mpr
  have hm := matEnergy_nonneg X
  have hmb : b ≤ M := by dsimp [M]; linarith [abs_nonneg a,abs_nonneg c]
  have hab := neg_abs_le a
  have hcb := le_abs_self c
  have hmul := mul_le_mul_of_nonneg_right hmb hm
  dsimp [M] at hM hmb ⊢
  constructor <;> nlinarith [abs_nonneg a,abs_nonneg c,mul_nonneg (abs_nonneg a) hm,mul_nonneg (abs_nonneg c) hm]
end ReferenceGaussian

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SampleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight

lemma boxKernel_translate {k : ℕ} (η : ℝ) (a e : Fin k → ℝ) :
    boxKernel η a (a+e)=boxKernel η 0 e := by
  have he : a+e ∈ closedBox a η ↔ e ∈ closedBox 0 η := by
    simp [closedBox,Pi.add_apply]
  unfold boxKernel
  by_cases h : e ∈ closedBox 0 η
  · rw [Set.indicator_of_mem (he.mpr h),Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hh => h (he.mp hh)),Set.indicator_of_notMem h]

lemma lintegral_noisy_translate {k : ℕ} (η : ℝ) (a : Fin k → ℝ)
    (f : (Fin k → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y,boxKernel η a y*f y ∂volume)=∫⁻ e,f (a+e) ∂noiseLaw k η := by
  rw [noiseLaw]
  have hm : Measurable (fun e : Fin k → ℝ => f (a+e)) := hf.comp (measurable_const.add measurable_id)
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_noise_density η) hm]
  rw [← lintegral_add_left_eq_self (fun y => boxKernel η a y*f y) a]
  simp only [Pi.mul_apply,boxKernel_translate]

lemma observationKernel_measurable {k d : ℕ} (η : ℝ) :
    Measurable (Function.uncurry (observationKernel (k := k) (d := d) η)) := by
  have hA := measurable_boxKernel (k := k) η
  have hP := continuous_projectVector (k := k) (d := d)
  unfold observationKernel Function.uncurry
  fun_prop

lemma observationKernel_probability {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d) :
    (∫⁻ z,observationKernel (k := k) η z s ∂observationBase k d)=1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  rw [observationBase,lintegral_prod _ (by
    exact ((observationKernel_measurable η).comp (measurable_id.prodMk measurable_const)).aemeasurable)]
  have inner (X Z : Fin k → Fin d → ℝ) :
      (∫⁻ yz : (Fin k → ℝ) × (Fin k → ℝ),
        boxKernel η (projectVector X s) yz.1*boxKernel η (projectVector Z s) yz.2
        ∂(volume : Measure (Fin k → ℝ)).prod volume)=1 := by
    have hm (c : Fin k → ℝ) : Measurable (boxKernel η c) :=
      (measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod_mul (hm _).aemeasurable (hm _).aemeasurable,
      lintegral_boxKernel η hη,lintegral_boxKernel η hη,one_mul]
  simp only [observationKernel,inner,lintegral_one,measure_univ]

lemma observation_lintegral {k d : ℕ} (η : ℝ) (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z,observationKernel η z s*f z ∂observationBase k d)=
      ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  have hM : Measurable (fun z : Observation k d => observationKernel η z s*f z) :=
    ((observationKernel_measurable η).comp (measurable_id.prodMk measurable_const)).mul hf
  rw [observationBase,lintegral_prod _ hM.aemeasurable,lintegral_prod]
  · apply lintegral_congr; intro X
    apply lintegral_congr; intro Z
    have hz : Measurable (fun yz : (Fin k → ℝ) × (Fin k → ℝ) =>
        observationKernel η ((X,Z),yz) s*f ((X,Z),yz)) :=
      hM.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hz.aemeasurable]
    dsimp only [observationKernel]
    have hinside (y : Fin k → ℝ) :
        (∫⁻ z,boxKernel η (projectVector X s) y*boxKernel η (projectVector Z s) z*f ((X,Z),(y,z)))=
          boxKernel η (projectVector X s) y*(∫⁻ e',f ((X,Z),(y,projectVector Z s+e')) ∂noiseLaw k η) := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul]
      · congr 1
        exact lintegral_noisy_translate η (projectVector Z s) (fun z => f ((X,Z),(y,z)))
          (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      · exact ((measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)).mul
          (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    simp_rw [hinside]
    apply lintegral_noisy_translate
    have hi : Measurable (fun yz : (Fin k → ℝ) × (Fin k → ℝ) =>
        f ((X,Z),(yz.1,projectVector Z s+yz.2))) := by fun_prop
    exact Measurable.lintegral_prod_right hi
  · exact (Measurable.lintegral_prod_right hM).aemeasurable

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_SampleEquivalence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support

lemma sampling_lintegral {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t,f (sampleEquiv s t) ∂samplingLaw k d η)=
      ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  have hm : Measurable (fun t : Observation k d => f (sampleEquiv s t)) := hf.comp (sampleEquiv s).measurable
  rw [samplingLaw,lintegral_prod _ hm.aemeasurable,lintegral_prod]
  · apply lintegral_congr; intro X
    apply lintegral_congr; intro Z
    have hi : Measurable (fun ef : (Fin k → ℝ) × (Fin k → ℝ) =>
        f (sampleEquiv s ((X,Z),ef))) := hm.comp (measurable_const.prodMk measurable_id)
    exact lintegral_prod _ hi.aemeasurable
  · exact (Measurable.lintegral_prod_right hm).aemeasurable

attribute [local irreducible] sampleEquiv

lemma sample_measurePreserving {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d) :
    MeasurePreserving (sampleEquiv (k := k) s) (samplingLaw k d η)
      ((observationBase k d).withDensity (fun z => observationKernel η z s)) := by
  refine ⟨(sampleEquiv s).measurable,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  have hk : Measurable (fun z : Observation k d => observationKernel η z s) := by
    have hK := observationKernel_measurable (k := k) (d := d) η
    fun_prop
  calc
    _ = ∫⁻ t,f (sampleEquiv s t) ∂samplingLaw k d η := lintegral_map hf (sampleEquiv s).measurable
    _ = ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := sampling_lintegral hη s f hf
    _ = ∫⁻ z,observationKernel η z s*f z ∂observationBase k d := (observation_lintegral η hη s f hf).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul (observationBase k d) hk hf).symm

lemma sampling_probability (k d : ℕ) {η : ℝ} (hη : 0 < η) :
    IsProbabilityMeasure (samplingLaw k d η) := by
  have := noise_probability k hη
  unfold samplingLaw gaussianRows
  infer_instance

lemma sample_integral {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ) :
    (∫ z,f z ∂(observationBase k d).withDensity (fun z => observationKernel η z s))=
      ∫ t,f (sampleEquiv s t) ∂samplingLaw k d η :=
  ((sample_measurePreserving hη s).integral_comp (sampleEquiv s).measurableEmbedding f).symm

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_Bayes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open EntropySupport Coercivity Sphere

lemma integrable_rule {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1) : Integrable r ν :=
  integrable_bounded_measurable ν r hr (fun s => by rw [abs_of_nonneg (hr0 s)]; exact hr1 s)

lemma mass_bounds {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (r : α → ℝ) (hr : Measurable r) {ε : ℝ} (hε : 0 < ε)
    (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) : ε ≤ mass ν r ∧ mass ν r ≤ 1 := by
  have hi := integrable_rule ν r hr (fun s => hε.le.trans (hrε s)) hr1
  constructor
  · simpa [mass] using integral_mono (integrable_const ε) hi hrε
  · simpa [mass] using integral_mono hi (integrable_const 1) hr1

lemma post_probability {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) : IsProbabilityMeasure (post ν r) := by
  have hi := integrable_rule ν r hr hr0 hr1
  constructor
  rw [post,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (ae_of_all _ (fun s => div_nonneg (hr0 s) ha.le)),
    integral_div]
  change ENNReal.ofReal (mass ν r/mass ν r)=1
  simp [ha.ne']

lemma post_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (r : α → ℝ) (hr1 : ∀ s,r s ≤ 1) (ha : 0 < mass ν r) :
    post ν r ≤ ENNReal.ofReal (1/mass ν r) • ν :=
  density_bounded ν _ (fun s => div_le_div_of_nonneg_right (hr1 s) ha.le)

lemma post_bounded {d : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr1 : ∀ s,r s ≤ 1) (ha : 0 < mass ν r) :
    post ν r ≤ ENNReal.ofReal (H/mass ν r) • sphereProbability d := by
  calc
    _ ≤ ENNReal.ofReal (1/mass ν r) • ν := post_le ν r hr1 ha
    _ ≤ ENNReal.ofReal (1/mass ν r) • (ENNReal.ofReal H • sphereProbability d) := smul_le_smul_left _ hν
    _ = _ := by rw [smul_smul,← ENNReal.ofReal_mul' hH.le]; congr 2; ring

lemma post_density {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (f r : α → ℝ) (hf : Measurable f) (hf0 : ∀ s,0 ≤ f s) (hr : Measurable r)
    (hν : ν=μ.withDensity (fun s => ENNReal.ofReal (f s))) :
    post ν r = μ.withDensity (fun s => ENNReal.ofReal (f s*r s/mass ν r)) := by
  unfold post
  nth_rw 1 [hν]
  rw [← withDensity_mul _ hf.ennreal_ofReal (hr.div_const _).ennreal_ofReal]
  congr 1
  ext s
  simp only [Pi.mul_apply,← ENNReal.ofReal_mul (hf0 s),mul_div_assoc]

lemma clippedJ_measurable {d : ℕ} (ν : Measure (Ambient d)) [SFinite ν] :
    Measurable (clippedJ ν) := measurable_const.max (measurable_J ν).ennreal_toReal
lemma clippedJ_pos {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : 0 < clippedJ ν s :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)
lemma clippedJ_eq {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (s : Ambient d) (hs : ‖s‖=1) : clippedJ ν s=(J ν s).toReal :=
  max_eq_right (J_real_bounds hd ν hH hν s hs).1

lemma integrable_log_clippedJ {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : BoundedDensity ν) (μ : Measure (Ambient d)) [IsFiniteMeasure μ] :
    Integrable (fun s => Real.log (clippedJ ν s)) μ := by
  obtain ⟨H,hH,hνH⟩ := hν
  apply integrable_log_of_bounds μ _ (clippedJ_measurable ν)
    (b := max ((1/2:ℝ)^(2*(d/16))) (H*(1+9*3^d*2^((d-1)+2*(d/16)+1))))
    (by positivity : (0:ℝ) < (1/2:ℝ)^(2*(d/16)))
  filter_upwards [] with s
  refine ⟨le_max_left _ _, max_le_max le_rfl ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (bounded_J hd ν hH hνH s)).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

lemma xlog_posterior_identity {f r a j : ℝ} (hr : 0 < r) (ha : 0 < a) (hj : 0 < j) :
    a*(xlog (f*r/a)-(f*r/a)*Real.log j) =
      r*xlog f+f*r*Real.log (r/(a*j)) := by
  rw [show f*r/a=f*(r/a) by ring,xlog_mul]
  simp only [xlog]
  rw [Real.log_div hr.ne' ha.ne',Real.log_div hr.ne' (mul_ne_zero ha.ne' hj.ne'),
    Real.log_mul ha.ne' hj.ne']
  field_simp
  ring

lemma weighted_Phi_identity {d : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (f : Ambient d → ℝ) (hf : Measurable f) (hf0 : ∀ s,0 ≤ f s)
    {H : ℝ} (hH : 0 < H) (hfH : ∀ s,f s ≤ H)
    (hν : ν=(sphereProbability d).withDensity (fun s => ENNReal.ofReal (f s)))
    (r : Ambient d → ℝ) (hr : Measurable r) {ε : ℝ} (hε : 0 < ε)
    (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    mass ν r*Phi (post ν r) =
      (∫ s,r s*xlog (f s) ∂sphereProbability d)+
        ∫ s,r s*Real.log (referenceWeight ν r s) ∂ν := by
  have hr0 (s : Ambient d) : 0 ≤ r s := hε.le.trans (hrε s)
  have hrpos (s : Ambient d) : 0 < r s := hε.trans_le (hrε s)
  have ha := hε.trans_le (mass_bounds ν r hr hε hrε hr1).1
  have hνb : ν ≤ ENNReal.ofReal H • sphereProbability d := by rw [hν]; exact density_bounded _ _ hfH
  have hp := post_bounded ν hH hνb r hr1 ha
  have := post_probability ν r hr hr0 hr1 ha
  have hpb : BoundedDensity (post ν r) := ⟨H/mass ν r,div_pos hH ha,hp⟩
  let F : Ambient d → ℝ := fun s => f s*r s/mass ν r
  have hF : Measurable F := (hf.mul hr).div_const _
  have hF0 (s : Ambient d) : 0 ≤ F s := div_nonneg (mul_nonneg (hf0 s) (hr0 s)) ha.le
  have hFH (s : Ambient d) : F s ≤ H/mass ν r := by
    apply div_le_div_of_nonneg_right _ ha.le
    exact (mul_le_mul_of_nonneg_left (hr1 s) (hf0 s)).trans (by simpa using hfH s)
  have hpost : post ν r=(sphereProbability d).withDensity (fun s => ENNReal.ofReal (F s)) :=
    post_density _ ν f r hf hf0 hr hν
  have hlogr : Integrable (fun s => Real.log (r s)) (sphereProbability d) :=
    integrable_log_of_bounds _ _ hr hε (ae_of_all _ (fun s => ⟨hrε s,hr1 s⟩))
  have hlogj := integrable_log_clippedJ hd (post ν r) hpb (sphereProbability d)
  have hlogx : Integrable (fun s => Real.log (referenceWeight ν r s)) (sphereProbability d) := by
    have he : (fun s => Real.log (referenceWeight ν r s)) =
        (fun s => Real.log (r s)-Real.log (mass ν r)-Real.log (clippedJ (post ν r) s)) := by
      ext s
      rw [referenceWeight,Real.log_div (hrpos s).ne' (mul_ne_zero ha.ne' (clippedJ_pos _ _).ne'),
        Real.log_mul ha.ne' (clippedJ_pos _ _).ne']
      ring
    rw [he]
    exact (hlogr.sub (integrable_const _)).sub hlogj
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  have hleft := hix.bdd_mul hr.aestronglyMeasurable (ae_of_all _ (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hr0 s)]; exact hr1 s))
  have hxright : Integrable (fun s => f s*(r s*Real.log (referenceWeight ν r s))) (sphereProbability d) :=
    (hlogx.bdd_mul hr.aestronglyMeasurable (ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hr0 s)]; exact hr1 s))).bdd_mul hf.aestronglyMeasurable
      (ae_of_all _ (fun s => by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 s)]; exact hfH s))
  rw [Phi_density_formula hd F hF hF0 hFH (post ν r) hpb hpost,← integral_const_mul]
  have hνint : (∫ s,r s*Real.log (referenceWeight ν r s) ∂ν) =
      ∫ s,f s*(r s*Real.log (referenceWeight ν r s)) ∂sphereProbability d := by
    rw [hν,integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hf0 _),smul_eq_mul]
  rw [hνint,← integral_add hleft hxright]
  apply integral_congr_ae
  filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
  rw [referenceWeight,clippedJ_eq hd (post ν r) (div_pos hH ha) hp s hs]
  simpa only [F,mul_assoc] using xlog_posterior_identity (f := f s) (hrpos s) ha
    (lt_of_lt_of_le (by positivity : (0:ℝ)<(1/2:ℝ)^(2*(d/16)))
      (J_real_bounds hd (post ν r) (div_pos hH ha) hp s hs).1)

end KernelPotential.Bayes

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_JointCompensation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.DriftTools

namespace FiniteReference
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_integral_nonneg (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K))
    (hκ : Measurable (Function.uncurry κ))
    (f : α × β × ι → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x,f x ∂joint ν Λ K κ) = ∫⁻ s,∫⁻ z,∑ w,K z s*κ z w*f (s,z,w) ∂Λ ∂ν := by
  rw [joint,lintegral_withDensity_eq_lintegral_mul]
  · rw [lintegral_prod]
    · apply lintegral_congr; intro s
      rw [lintegral_prod]
      · apply lintegral_congr; intro z
        simp only [lintegral_count,tsum_fintype]
        rfl
      · fun_prop
    · fun_prop
  · fun_prop
  · exact hf

lemma joint_probability (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1) (hκ1 : ∀ z,∑ w,κ z w=1) :
    IsProbabilityMeasure (joint ν Λ K κ) := by
  constructor
  rw [← lintegral_one,(joint_integral_nonneg ν Λ K κ hK hκ _ measurable_const)]
  simp only [mul_one,← Finset.mul_sum,hκ1,mul_one,hK1,lintegral_one,measure_univ]

lemma measurable_C (ν : Measure α) [SFinite ν]
    (K : β → α → ℝ≥0∞) (x : ι → α → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hx : Measurable (Function.uncurry x)) :
    Measurable (Function.uncurry (C ν K x)) := by
  apply measurable_from_prod_countable_left
  intro index
  unfold C
  apply Measurable.lintegral_prod_right
  fun_prop

lemma joint_compensation (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hκ1 : ∀ z,∑ w,κ z w=1)
    (x : ι → α → ℝ≥0∞) (hx : Measurable (Function.uncurry x))
    (q : β → ℝ≥0∞) (hq : Measurable q) (hq1 : ∫⁻ z,q z ∂Λ=1) :
    (∫⁻ t,q t.2.1*x t.2.2 t.1/(1+C ν K x t.2.1 t.2.2) ∂joint ν Λ K κ) ≤ 1 := by
  rw [joint_integral_nonneg ν Λ K κ hK hκ]
  · have hm : Measurable (fun t : α × β => ∑ w,K t.2 t.1*κ t.2 w*
        (q t.2*x w t.1/(1+C ν K x t.2 w))) := by
      have hC := measurable_C ν K x hK hx
      fun_prop
    rw [lintegral_lintegral_swap hm.aemeasurable]
    have he : (∫⁻ z,∫⁻ s,∑ w,K z s*κ z w*(q z*x w s/(1+C ν K x z w)) ∂ν ∂Λ) =
        ∫⁻ z,∑ w,∫⁻ s,K z s*κ z w*q z*x w s/(1+C ν K x z w) ∂ν ∂Λ := by
      apply lintegral_congr; intro z
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl; intro w _
        apply lintegral_congr; intro s
        dsimp only [C]; simp only [div_eq_mul_inv]; ring
      · intro w _; fun_prop
    rw [he]
    exact compensation_lintegral ν Λ K (fun z => hK.comp (measurable_const.prodMk measurable_id))
      κ hκ1 x (fun w => hx.comp (measurable_const.prodMk measurable_id)) q hq1
  · have hC := measurable_C ν K x hK hx
    fun_prop

lemma log_comparison (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1) (hκ1 : ∀ z,∑ w,κ z w=1)
    (x : ι → α → ℝ≥0∞) (hx : Measurable (Function.uncurry x))
    (hxpos : ∀ w s,0 < x w s) (hxfin : ∀ w s,x w s ≠ ∞)
    (q : β → ℝ≥0∞) (hq : Measurable q) (hqpos : ∀ z,0 < q z)
    (hqfin : ∀ z,q z ≠ ∞) (hq1 : ∫⁻ z,q z ∂Λ=1)
    (hCfin : ∀ z w,C ν K x z w ≠ ∞)
    (hlogx : Integrable (fun t => Real.log (x t.2.2 t.1).toReal) (joint ν Λ K κ))
    (hlogq : Integrable (fun t => Real.log (q t.2.1).toReal) (joint ν Λ K κ))
    (hlogC : Integrable (fun t => Real.log (1+(C ν K x t.2.1 t.2.2).toReal)) (joint ν Λ K κ)) :
    (∫ t,Real.log (x t.2.2 t.1).toReal ∂joint ν Λ K κ) ≤
      (∫ t,Real.log (1+(C ν K x t.2.1 t.2.2).toReal) ∂joint ν Λ K κ) -
        ∫ t,Real.log (q t.2.1).toReal ∂joint ν Λ K κ := by
  have := joint_probability ν Λ K κ hK hκ hK1 hκ1
  have hC := measurable_C ν K x hK hx
  apply compensated_log_bound (joint ν Λ K κ)
    (fun t => (x t.2.2 t.1).toReal) (fun t => (q t.2.1).toReal)
    (fun t => (C ν K x t.2.1 t.2.2).toReal)
    (Filter.Eventually.of_forall (fun t => ENNReal.toReal_pos (hxpos _ _).ne' (hxfin _ _)))
    (Filter.Eventually.of_forall (fun t => ENNReal.toReal_pos (hqpos _).ne' (hqfin _)))
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    (by
      have hm : Measurable (fun t : α × β × ι => (q t.2.1).toReal*(x t.2.2 t.1).toReal /
        (1+(C ν K x t.2.1 t.2.2).toReal)) := by fun_prop
      exact hm.aestronglyMeasurable) _ hlogx hlogq hlogC
  have he (t : α × β × ι) : ENNReal.ofReal ((q t.2.1).toReal*(x t.2.2 t.1).toReal /
      (1+(C ν K x t.2.1 t.2.2).toReal)) =
      q t.2.1*x t.2.2 t.1/(1+C ν K x t.2.1 t.2.2) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hqfin _),ENNReal.ofReal_toReal (hxfin _ _),
      ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg,
      ENNReal.ofReal_one,ENNReal.ofReal_toReal (hCfin _ _)]
  simp_rw [he]
  exact joint_compensation ν Λ K κ hK hκ hκ1 x hx q hq hq1

end FiniteReference

end KernelPotential.DriftTools

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_integral (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hκfin : ∀ z w,κ z w ≠ ∞)
    (f : α × β × ι → ℝ) (hi : Integrable f (joint ν Λ K κ)) :
    (∫ t,f t ∂joint ν Λ K κ)=∫ s,∫ z,∑ w,(K z s).toReal*(κ z w).toReal*f (s,z,w) ∂Λ ∂ν := by
  have hm : Measurable (fun t : α × β × ι => K t.2.1 t.1*κ t.2.1 t.2.2) := by fun_prop
  have hfin : ∀ᵐ t ∂ν.prod (Λ.prod Measure.count),K t.2.1 t.1*κ t.2.1 t.2.2 < ∞ :=
    ae_of_all _ (fun t => ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hKfin _ _)) (lt_top_iff_ne_top.mpr (hκfin _ _)))
  have hweight : Integrable (fun t : α × β × ι =>
      (K t.2.1 t.1).toReal*(κ t.2.1 t.2.2).toReal*f t) (ν.prod (Λ.prod Measure.count)) := by
    simpa only [joint,ENNReal.toReal_mul,smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' hm hfin).mp hi
  rw [joint,integral_withDensity_eq_integral_toReal_smul hm hfin]
  simp only [ENNReal.toReal_mul,smul_eq_mul]
  rw [integral_prod _ hweight]
  apply integral_congr_ae
  filter_upwards [hweight.prod_right_ae] with s hs
  rw [integral_prod _ hs]
  congr 1
  ext z
  rw [integral_count]

lemma likelihood_bounds {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    {ε : ℝ≥0∞} (hκε : ∀ z w,ε ≤ κ z w) (hκ1 : ∀ z w,κ z w ≤ 1) (s : α) (w : ι) :
    ε ≤ ∫⁻ z,K z s*κ z w ∂Λ ∧ (∫⁻ z,K z s*κ z w ∂Λ) ≤ 1 := by
  have hm : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  constructor
  · calc
      ε = ∫⁻ z,K z s*ε ∂Λ := by rw [lintegral_mul_const _ hm,hK1,one_mul]
      _ ≤ _ := lintegral_mono (fun z => mul_le_mul_right (hκε z w) _)
  · calc
      _ ≤ ∫⁻ z,K z s*1 ∂Λ := lintegral_mono (fun z => mul_le_mul_right (hκ1 z w) _)
      _ = 1 := by simp only [mul_one,hK1]
end KernelPotential.DriftTools.FiniteReference
namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma kernel_rule_real_integrable (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    (hκ1 : ∀ z w,κ z w ≤ 1) (s : α) (w : ι) :
    Integrable (fun z => (K z s).toReal*(κ z w).toReal) Λ := by
  have hm : Measurable (fun z => K z s*κ z w) :=
    (hK.comp (measurable_id.prodMk measurable_const)).mul
      (hκ.comp (measurable_id.prodMk measurable_const))
  have hfin : ∀ z,K z s*κ z w ≠ ∞ := fun z => ENNReal.mul_ne_top (hKfin _ _)
    (ne_of_lt ((hκ1 z w).trans_lt (by norm_num)))
  have hb := (likelihood_bounds Λ K κ hK hK1 (ε := 0) (fun _ _ => bot_le) hκ1 s w).2
  simpa only [ENNReal.toReal_mul] using
    (integrable_toReal_iff hm.aemeasurable (ae_of_all _ hfin)).mpr (ne_of_lt (hb.trans_lt (by norm_num)))

lemma kernel_rule_integral {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hκ1 : ∀ z w,κ z w ≤ 1) (s : α) (w : ι) :
    (∫ z,(K z s).toReal*(κ z w).toReal ∂Λ)=likelihood Λ K κ s w := by
  have hm : Measurable (fun z => K z s*κ z w) :=
    (hK.comp (measurable_id.prodMk measurable_const)).mul
      (hκ.comp (measurable_id.prodMk measurable_const))
  simpa only [likelihood,ENNReal.toReal_mul] using integral_toReal hm.aemeasurable
    (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (hKfin _ _)
      (ne_of_lt ((hκ1 z w).trans_lt (by norm_num))))))

lemma likelihood_measurable (Λ : Measure β) [SFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ)) :
    Measurable (Function.uncurry (likelihood Λ K κ)) := by
  apply measurable_from_prod_countable_left
  intro index
  unfold likelihood Function.uncurry
  apply Measurable.ennreal_toReal
  apply Measurable.lintegral_prod_right
  fun_prop

lemma joint_integral_signal (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    (hκ1 : ∀ z,∑ w,κ z w=1)
    (f : α → ι → ℝ) (hf : Measurable (Function.uncurry f)) {M : ℝ}
    (hfM : ∀ s w,‖f s w‖ ≤ M) :
    (∫ t,f t.1 t.2.2 ∂joint ν Λ K κ)=∑ w,∫ s,likelihood Λ K κ s w*f s w ∂ν := by
  classical
  have hb (z : β) (w : ι) : κ z w ≤ 1 := by
    rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
  have := joint_probability ν Λ K κ hK hκ hK1 hκ1
  have hi : Integrable (fun t : α × β × ι => f t.1 t.2.2) (joint ν Λ K κ) :=
    Integrable.of_bound (hf.comp (measurable_fst.prodMk measurable_snd.snd)).aestronglyMeasurable M
      (ae_of_all _ (fun t => hfM _ _))
  rw [joint_integral ν Λ K κ hK hκ hKfin (fun z w => ne_of_lt ((hb z w).trans_lt (by norm_num))) _ hi]
  have he (s : α) :
      (∫ z,∑ w,(K z s).toReal*(κ z w).toReal*f s w ∂Λ)=∑ w,likelihood Λ K κ s w*f s w := by
    rw [integral_finsetSum _ (fun w _ => (kernel_rule_real_integrable Λ K κ hK hκ hKfin hK1 hb s w).mul_const _)]
    apply Finset.sum_congr rfl; intro w _
    rw [integral_mul_const,kernel_rule_integral Λ K κ hK hκ hKfin hb]
  simp_rw [he]
  apply integral_finsetSum
  intro w _
  have hm : Measurable (fun s => likelihood Λ K κ s w) :=
    (likelihood_measurable Λ K κ hK hκ).comp (measurable_id.prodMk measurable_const)
  have hbR (s : α) : likelihood Λ K κ s w ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by simpa using (likelihood_bounds Λ K κ hK hK1 (ε := 0) (fun _ _ => bot_le) hb s w).2)
  apply Integrable.of_bound (hm.mul (hf.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable M
  filter_upwards [] with s
  change ‖likelihood Λ K κ s w*f s w‖ ≤ M
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ likelihood Λ K κ s w from ENNReal.toReal_nonneg)]
  exact (mul_le_mul_of_nonneg_right (hbR s) (norm_nonneg _)).trans (by simpa using hfM s w)
end KernelPotential.DriftTools.FiniteReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_DriftCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.DriftCutoff

lemma level_pos (d : ℕ) (H : ℝ) : 0 < level d H := by unfold level; omega

lemma level_lower (d : ℕ) (H : ℝ) : 2*Real.log H+20*(d:ℝ) ≤ (level d H:ℝ) := by
  have h := Nat.le_ceil (2*Real.log H+20*(d:ℝ))
  unfold level
  push_cast
  linarith

lemma log_constant_bound (d : ℕ) (hd : 16 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    Real.log (H*(9*3^d)*(4:ℝ)^(d-1)*(2:ℝ)^(2*(d/16)+1)) ≤
      (level d H:ℝ)*Real.log 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlog2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hu2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hu3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<3 by norm_num)]
  have hu4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)]
  have hu9 : Real.log 9 ≤ 8 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<9 by norm_num)]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul hHpos.ne' (by positivity),Real.log_mul (by norm_num) (by positivity)]
  simp only [Real.log_pow]
  have hdR : 16 ≤ (d:ℝ) := by exact_mod_cast hd
  have hn : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
  have hk : ((2*(d/16)+1:ℕ):ℝ) ≤ (d:ℝ)+1 := by
    exact_mod_cast (show 2*(d/16)+1 ≤ d+1 by have hh := Nat.div_mul_le_self d 16; omega)
  have hL := level_lower d H
  have hp := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ) ≤ level d H by positivity)
  have h3 := mul_le_mul_of_nonneg_left hu3 (show (0:ℝ) ≤ d by positivity)
  have h4 := mul_le_mul_of_nonneg_left hu4 (show (0:ℝ) ≤ (d-1:ℕ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hu2 (show (0:ℝ) ≤ (2*(d/16)+1:ℕ) by positivity)
  linarith

lemma reference_cut (d : ℕ) (hd : 16 ≤ d) {H : ℝ} (hH : 1 ≤ H) :
    ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^(level d H)) ≤ 1 := by
  have hp := Real.le_pow_of_log_le (show (0:ℝ)<2 by norm_num) (log_constant_bound d hd hH)
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_one.mpr
  calc
    _ ≤ (2:ℝ)^(level d H)*(1/2:ℝ)^(level d H) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

end KernelPotential.DriftCutoff

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisyReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.NoisyReference
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support Noise ReferenceGaussian GaussianTools RowConcat Scale

lemma sample_density {k d L : ℕ} (ν : Measure (Ambient d)) (r : Fin L → ℝ)
    (s : Ambient d) (t : Observation k d) :
    PairReference.density ν r (sampleEquiv s t).1.1 (sampleEquiv s t).1.2
      (sampleEquiv s t).2.1 (sampleEquiv s t).2.2 =
      mixture ν r (join k t.1) (applyRows (join k t.1) s+join k t.2) := by
  change mixture ν r (join k t.1) (join k (applyRows t.1.1 s+t.2.1,applyRows t.1.2 s+t.2.2))=_
  rw [join_add,show join k (applyRows t.1.1 s,applyRows t.1.2 s)=applyRows (join k t.1) s from join_rows k d _ _ s]

lemma pair_noise_support (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),∀ i,|join k e i| ≤ η := by
  have := noise_probability k hη
  have h1 : ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),e.1 ∈ closedBox 0 η :=
    measurePreserving_fst.quasiMeasurePreserving.ae (noise_support k η)
  have h2 : ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),e.2 ∈ closedBox 0 η :=
    measurePreserving_snd.quasiMeasurePreserving.ae (noise_support k η)
  filter_upwards [h1,h2] with e h1 h2
  apply join_bound k e.1 e.2 (fun x : ℝ => |x| ≤ η)
  · simpa only [closedBox,Set.mem_ofPred_eq,Pi.zero_apply,sub_zero] using h1
  · simpa only [closedBox,Set.mem_ofPred_eq,Pi.zero_apply,sub_zero] using h2

lemma sampling_noise_support (k d : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ t ∂samplingLaw k d η,∀ i,|join k t.2 i| ≤ η := by
  have := noise_probability k hη
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  exact measurePreserving_snd.quasiMeasurePreserving.ae (pair_noise_support k hη)

lemma integrable_pairEnergy (k d : ℕ) :
    Integrable (fun t : (Mat k d) × (Mat k d) => matEnergy (join k t))
      ((gaussianRows k d).prod (gaussianRows k d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  exact (join_measurePreserving k (scalarRow d)).integrable_comp_of_integrable integrable_matEnergy

lemma sampling_log_integrable {k d L : ℕ} (hL : 0 < L)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (r : Fin L → ℝ) (hr : ∀ j,0 < r j)
    (s : Ambient d) {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η)
    (hs : ∀ᵐ u ∂ν,u ∈ closedBall s R) :
    Integrable (fun t : Observation k d => Real.log (PairReference.density ν r
      (sampleEquiv s t).1.1 (sampleEquiv s t).1.2 (sampleEquiv s t).2.1 (sampleEquiv s t).2.2))
      (samplingLaw k d η) := by
  have := noise_probability k hη
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  obtain ⟨M,_,hb⟩ := log_mixture_uniform_bound (p := 2*k) hL ν r hr hR hη.le
  have hm : Measurable (fun t : Observation k d => Real.log (PairReference.density ν r
      (sampleEquiv s t).1.1 (sampleEquiv s t).1.2 (sampleEquiv s t).2.1 (sampleEquiv s t).2.2)) := by
    have hD := PairReference.density_measurable (k := k) ν r
    have hS := (sampleEquiv (k := k) s).measurable
    exact Real.measurable_log.comp (hD.comp hS)
  refine ((integrable_const 1).add ((integrable_pairEnergy k d).comp_fst _)).const_mul M |>.mono' hm.aestronglyMeasurable ?_
  filter_upwards [sampling_noise_support k d hη] with t ht
  rw [Real.norm_eq_abs,sample_density]
  exact hb s hs (join k t.1) (join k t.2) ht

lemma noisy_reference_J_lower {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1)
    {η : ℝ} (hη : 0 < η) (hηL : η ≤ radius L) :
    Real.log (J ν s).toReal-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤
      (∫ z : Observation (d/16) d,Real.log (PairReference.density ν (fun j : Fin L => radius j)
        z.1.1 z.1.2 z.2.1 z.2.2)
        ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have := noise_probability (d/16) hη
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  have hiSupport : ∀ᵐ u ∂ν,u ∈ closedBall s 2 := by
    filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le (Sphere.ae_unit_norm (by omega : 0 < d))] with u hu
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by rw [hu,hs]; norm_num)
  have hi := sampling_log_integrable (k := d/16) hL ν (fun j : Fin L => radius j) (fun j => radius_pos j)
    s (by norm_num : (0:ℝ) ≤ 2) hη hiSupport
  rw [sample_integral hη s,samplingLaw,integral_prod _ hi,integral_integral_swap hi]
  have hir := hi.integral_prod_right
  calc
    _ = ∫ _e : (Fin (d/16) → ℝ) × (Fin (d/16) → ℝ),
        Real.log (J ν s).toReal-10*(d:ℝ)-2*Real.log ((L:ℝ)+2)
        ∂(noiseLaw (d/16) η).prod (noiseLaw (d/16) η) := by simp
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) hir
      filter_upwards [pair_noise_support (d/16) hη] with e he
      have he' : ∀ i,|join (d/16) e i| ≤ radius L := fun i => (he i).trans hηL
      have h := reference_J_lower hd ν hH hν s hs L hL hcut _ he'
      have hrw : (∫ XZ : Mat (d/16) d × Mat (d/16) d,
          Real.log (PairReference.density ν (fun j : Fin L => radius j)
            (sampleEquiv s (XZ,e)).1.1 (sampleEquiv s (XZ,e)).1.2
            (sampleEquiv s (XZ,e)).2.1 (sampleEquiv s (XZ,e)).2.2)
          ∂(gaussianRows (d/16) d).prod (gaussianRows (d/16) d))=
          ∫ X : Mat (2*(d/16)) d,Real.log (mixture ν (fun j : Fin L => radius j) X
            (applyRows X s+join (d/16) e)) ∂Measure.pi (fun _ : Fin (2*(d/16)) => scalarRow d) := by
        simp only [sample_density]
        exact (join_measurePreserving (d/16) (scalarRow d)).integral_comp'
          (fun X : Mat (2*(d/16)) d => Real.log (mixture ν (fun j : Fin L => radius j) X
            (applyRows X s+join (d/16) e)))
      rw [hrw]
      exact h
end KernelPotential.NoisyReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_EntropyComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_observation_lintegral (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hκ1 : ∀ z,∑ w,κ z w=1) (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t,f (t.1,t.2.1) ∂joint ν Λ K κ)=∫⁻ s,∫⁻ z,K z s*f (s,z) ∂Λ ∂ν := by
  have hm : Measurable (fun t : α × β × ι => f (t.1,t.2.1)) :=
    hf.comp (measurable_fst.prodMk measurable_snd.fst)
  rw [joint_integral_nonneg ν Λ K κ hK hκ _ hm]
  apply lintegral_congr; intro s
  apply lintegral_congr; intro z
  change (∑ w,K z s*κ z w*f (s,z))=_
  rw [← Finset.sum_mul,← Finset.mul_sum,hκ1,mul_one]

lemma joint_observation_integrable (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hκ1 : ∀ z,∑ w,κ z w=1) (f : α × β → ℝ) (hf : Measurable f)
    (hi : (∫⁻ s,∫⁻ z,K z s*‖f (s,z)‖ₑ ∂Λ ∂ν)<∞) :
    Integrable (fun t => f (t.1,t.2.1)) (joint ν Λ K κ) := by
  refine ⟨(hf.comp (measurable_fst.prodMk measurable_snd.fst)).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm,joint_observation_lintegral ν Λ K κ hK hκ hκ1 _ hf.enorm]
  exact hi

lemma joint_observation_integral (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hκ1 : ∀ z,∑ w,κ z w=1)
    (f : α × β → ℝ) (hi : Integrable (fun t => f (t.1,t.2.1)) (joint ν Λ K κ)) :
    (∫ t,f (t.1,t.2.1) ∂joint ν Λ K κ)=∫ s,∫ z,f (s,z) ∂Λ.withDensity (fun z => K z s) ∂ν := by
  classical
  have hκfin (z : β) (w : ι) : κ z w ≠ ∞ := by
    have hb : κ z w ≤ 1 := by rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
    exact ne_of_lt (hb.trans_lt (by norm_num))
  have hκR (z : β) : ∑ w,(κ z w).toReal=1 := by
    rw [← ENNReal.toReal_sum (fun w _ => hκfin z w),hκ1,ENNReal.toReal_one]
  rw [joint_integral ν Λ K κ hK hκ hKfin hκfin _ hi]
  apply integral_congr_ae
  filter_upwards [] with s
  have hKs : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  rw [integral_withDensity_eq_integral_toReal_smul hKs
    (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (hKfin z s)))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [smul_eq_mul]
  rw [← Finset.sum_mul,← Finset.mul_sum,hκR,mul_one]
end KernelPotential.DriftTools.FiniteReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_BayesEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Sphere Reweight

lemma clippedJ_upper {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) :
    clippedJ ν s ≤ max ((1/2:ℝ)^(2*(d/16))) (H*(1+9*3^d*2^((d-1)+2*(d/16)+1))) := by
  apply max_le_max le_rfl
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (bounded_J hd ν hH hν s)).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

lemma referenceWeight_measurable {d : ℕ} (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) : Measurable (referenceWeight ν r) := by
  have := post_probability ν r hr hr0 hr1 ha
  exact hr.div (measurable_const.mul (clippedJ_measurable _))

lemma referenceWeight_bounds {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr : Measurable r) {ε : ℝ} (hε : 0 < ε)
    (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    ∃ a b : ℝ,0 < a ∧ ∀ s,a ≤ referenceWeight ν r s ∧ referenceWeight ν r s ≤ b := by
  have ha := hε.trans_le (mass_bounds ν r hr hε hrε hr1).1
  have := post_probability ν r hr (fun s => hε.le.trans (hrε s)) hr1 ha
  have hp := post_bounded ν hH hν r hr1 ha
  let U := max ((1/2:ℝ)^(2*(d/16))) ((H/mass ν r)*(1+9*3^d*2^((d-1)+2*(d/16)+1)))
  have hU : 0 < U := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨ε/(mass ν r*U),1/(mass ν r*((1/2:ℝ)^(2*(d/16)))),by positivity,?_⟩
  intro s
  have hj := clippedJ_pos (post ν r) s
  constructor
  · exact (div_le_div_of_nonneg_left hε.le (mul_pos ha hj)
      (mul_le_mul_of_nonneg_left (clippedJ_upper hd _ (div_pos hH ha) hp s) ha.le)).trans
      (div_le_div_of_nonneg_right (hrε s) (mul_nonneg ha.le hj.le))
  · exact (div_le_div_of_nonneg_right (hr1 s) (mul_nonneg ha.le hj.le)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le))

lemma rho_post_eq_weight {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) :
    rho (post ν r)=ν.withDensity (fun s => ENNReal.ofReal (referenceWeight ν r s)) := by
  have := post_probability ν r hr hr0 hr1 ha
  have hp := post_bounded ν hH hν r hr1 ha
  have hA : Measurable (fun s => ENNReal.ofReal (r s/mass ν r)) := (hr.div_const _).ennreal_ofReal
  have hJ : Measurable (fun s => (J (post ν r) s)⁻¹) := (measurable_J _).inv
  change (ν.withDensity (fun s => ENNReal.ofReal (r s/mass ν r))).withDensity
    (fun s => (J (post ν r) s)⁻¹)=_
  rw [← withDensity_mul _ hA hJ]
  apply withDensity_congr_ae
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))] with s hs
  have hJfin : J (post ν r) s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (bounded_J hd _ (div_pos hH ha) hp s)
  have hJp : 0 < (J (post ν r) s).toReal := lt_of_lt_of_le (by positivity)
    (J_real_bounds hd _ (div_pos hH ha) hp s hs).1
  change ENNReal.ofReal (r s/mass ν r)*(J (post ν r) s)⁻¹=_
  rw [referenceWeight,clippedJ_eq hd _ (div_pos hH ha) hp s hs]
  rw [show r s/(mass ν r*(J (post ν r) s).toReal)=(r s/mass ν r)*((J (post ν r) s).toReal)⁻¹ by ring,
    ENNReal.ofReal_mul (div_nonneg (hr0 s) ha.le),ENNReal.ofReal_inv_of_pos hJp,ENNReal.ofReal_toReal hJfin]

lemma C_eq_projectedReference {d k : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) (η : ℝ) (z : Noise.Observation k d) :
    (∫⁻ s,Noise.observationKernel η z s*ENNReal.ofReal (referenceWeight ν r s) ∂ν)=
      Noise.projectedReference (post ν r) η z.1.1 z.1.2 z.2.1 z.2.2 := by
  rw [Noise.projectedReference,rho_post_eq_weight hd ν hH hν r hr hr0 hr1 ha]
  have hK : Measurable (fun s => Noise.observationKernel η z s) := by
    have hKall := Noise.observationKernel_measurable (k := k) (d := d) η
    fun_prop
  change _=(∫⁻ s,Noise.observationKernel η z s ∂ν.withDensity (fun s => ENNReal.ofReal (referenceWeight ν r s)))
  rw [lintegral_withDensity_eq_lintegral_mul _
    (referenceWeight_measurable ν r hr hr0 hr1 ha).ennreal_ofReal hK]
  apply lintegral_congr
  intro s
  exact mul_comm _ _
end KernelPotential.Bayes

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ReferenceCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian

lemma observationKernel_ne_top {k d : ℕ} {η : ℝ} (hη : 0 < η) (z : Observation k d) (s : Ambient d) :
    observationKernel η z s ≠ ∞ :=
  ENNReal.mul_ne_top (ne_top_of_le_ne_top (boxScale_ne_top k hη) (boxKernel_le η _ _))
    (ne_top_of_le_ne_top (boxScale_ne_top k hη) (boxKernel_le η _ _))

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisyRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian DriftTools.FiniteReference Bayes

lemma likelihood_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ] (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1) (hκ1 : ∀ z,∑ w,κ z w=1) (s : α) :
    ∑ w,likelihood Λ K κ s w=1 := by
  have hb (z : β) (w : ι) : κ z w ≤ 1 := by
    rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
  have hfin (w : ι) : (∫⁻ z,K z s*κ z w ∂Λ) ≠ ∞ :=
    ne_of_lt (((likelihood_bounds Λ K κ hK hK1 (ε := 0) (fun _ _ => bot_le) hb s w).2).trans_lt (by norm_num))
  unfold likelihood
  rw [← ENNReal.toReal_sum (fun w _ => hfin w),← lintegral_finsetSum]
  · simp only [← Finset.mul_sum,hκ1,mul_one,hK1,ENNReal.toReal_one]
  · intro w _; fun_prop

lemma likelihood_real_bounds {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ] (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    {ε : ℝ} (hε : 0 ≤ ε) (hκε : ∀ z w,ENNReal.ofReal ε ≤ κ z w) (hκ1 : ∀ z w,κ z w ≤ 1)
    (s : α) (w : ι) : ε ≤ likelihood Λ K κ s w ∧ likelihood Λ K κ s w ≤ 1 := by
  obtain ⟨hl,hu⟩ := likelihood_bounds Λ K κ hK hK1 hκε hκ1 s w
  have hfin := ne_of_lt (hu.trans_lt (by norm_num : (1:ℝ≥0∞)<∞))
  exact ⟨by simpa [likelihood,ENNReal.toReal_ofReal hε] using ENNReal.toReal_mono hfin hl,
    by simpa [likelihood] using ENNReal.toReal_mono ENNReal.one_ne_top hu⟩

lemma log_bounded_of_bounds {α : Type*} (f : α → ℝ) {a b : ℝ} (ha : 0 < a)
    (hf : ∀ x,a ≤ f x ∧ f x ≤ b) :
    ∀ x,‖Real.log (f x)‖ ≤ |Real.log a|+|Real.log b| := by
  intro x
  rw [Real.norm_eq_abs]
  have hl := Real.log_le_log ha (hf x).1
  have hh := Real.log_le_log (ha.trans_le (hf x).1) (hf x).2
  apply abs_le.mpr
  constructor
  · have := neg_abs_le (Real.log a); have := abs_nonneg (Real.log b); linarith
  · have := le_abs_self (Real.log b); have := abs_nonneg (Real.log a); linarith

lemma referenceWeight_log_bounded {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (r : Ambient d → ℝ) (hr : Measurable r)
    {ε : ℝ} (hε : 0 < ε) (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ s,‖Real.log (referenceWeight ν r s)‖ ≤ M := by
  obtain ⟨a,b,ha,hb⟩ := referenceWeight_bounds hd ν hH hν r hr hε hrε hr1
  exact ⟨|Real.log a|+|Real.log b|,by positivity,log_bounded_of_bounds _ ha hb⟩

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_PositiveRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference

namespace PositiveRule
variable {k d N : ℕ} (rule : PositiveRule k d N)
lemma nonneg (t) (w) : 0 ≤ rule.prob t w := rule.lower_pos.le.trans (rule.lower_prob t w)
lemma le_one (t) (w) : rule.prob t w ≤ 1 := by
  rw [← rule.sum_prob t]
  exact Finset.single_le_sum (fun v _ => rule.nonneg t v) (Finset.mem_univ w)
lemma measurable_kernel : Measurable (Function.uncurry rule.kernel) := by
  unfold kernel
  exact (rule.measurable_prob.comp ((measurable_fst.fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd)).ennreal_ofReal
lemma sum_kernel (z) : ∑ w,rule.kernel z w=1 := by
  unfold kernel
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => rule.nonneg _ w),rule.sum_prob,ENNReal.ofReal_one]
lemma kernel_le_one (z) (w) : rule.kernel z w ≤ 1 :=
  ENNReal.ofReal_le_one.mpr (rule.le_one _ _)
lemma lower_kernel (z) (w) : ENNReal.ofReal rule.lower ≤ rule.kernel z w :=
  ENNReal.ofReal_le_ofReal (rule.lower_prob _ _)
lemma measurable_response (η : ℝ) (w : Fin N) : Measurable (rule.response η w) := by
  have hK : Measurable (Function.uncurry (observationKernel (k := k) (d := d) η)) := observationKernel_measurable η
  have hκ : Measurable (fun z : Observation k d => rule.kernel z w) :=
    rule.measurable_kernel.comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (fun a : Ambient d × Observation k d => observationKernel η a.2 a.1*rule.kernel a.2 w) :=
    (hK.comp measurable_swap).mul (hκ.comp measurable_snd)
  unfold response likelihood
  exact hm.lintegral_prod_right.ennreal_toReal
lemma response_bounds {η : ℝ} (hη : 0 < η) (w) (s) :
    rule.lower ≤ rule.response η w s ∧ rule.response η w s ≤ 1 :=
  likelihood_real_bounds (observationBase k d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) (observationKernel_probability hη) rule.lower_pos.le
    rule.lower_kernel rule.kernel_le_one s w
lemma response_sum {η : ℝ} (hη : 0 < η) (s) : ∑ w,rule.response η w s=1 :=
  likelihood_sum (observationBase k d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_probability hη)
    rule.sum_kernel s
lemma mass_pos {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w) :
    0 < mass ν (rule.response η w) :=
  rule.lower_pos.trans_le (mass_bounds ν _ (rule.measurable_response η w) rule.lower_pos
    (fun s => (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)).1
lemma post_prob {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w) :
    IsProbabilityMeasure (post ν (rule.response η w)) :=
  post_probability ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
    (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)
end PositiveRule
end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisyCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Reweight Sphere DriftTools

lemma projectedReference_real_bound {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν,‖s‖=1) {η : ℝ} (hη : 0 < η) (z : Observation k d) :
    (projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal ≤
      (boxScale k η).toReal^2*2^(2*(d/16)) := by
  have hb := (rho_le ν hν Set.univ).trans_eq (by simp :
    ((ENNReal.ofReal ((2:ℝ)^(2*(d/16)))) • ν) Set.univ=ENNReal.ofReal ((2:ℝ)^(2*(d/16))))
  have hc := (projectedReference_le ν η z.1.1 z.1.2 z.2.1 z.2.2).trans (mul_le_mul_right hb _)
  apply (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) ENNReal.ofReal_ne_top) hc).trans_eq
  simp [ENNReal.toReal_mul,ENNReal.toReal_pow]

lemma projectedReference_finite {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν,‖s‖=1) {η : ℝ} (hη : 0 < η) (z : Observation k d) :
    projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2 ≠ ∞ := by
  have := rho_finite ν hν
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) (measure_ne_top _ _))
    (projectedReference_le ν η z.1.1 z.1.2 z.2.1 z.2.2)

lemma projected_log_bounded {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν,‖s‖=1) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ z : Observation k d,
      0 ≤ Real.log (1+(projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal) ∧
      Real.log (1+(projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal) ≤ M := by
  refine ⟨Real.log (1+(boxScale k η).toReal^2*2^(2*(d/16))),Real.log_nonneg (by
      have hb : 0 ≤ (boxScale k η).toReal^2*2^(2*(d/16)) := by positivity
      linarith),?_⟩
  intro z
  exact ⟨Real.log_nonneg (by have := ENNReal.toReal_nonneg (a := projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2); linarith),
    Real.log_le_log (by positivity) (add_le_add_right (projectedReference_real_bound ν hν hη z) _)⟩

end KernelPotential.Noise

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_NoisyMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.NoisyReference
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian RowConcat Scale Noise DriftTools.FiniteReference

lemma sample_joint_measurable {k d : ℕ} :
    Measurable (fun a : Ambient d × Observation k d => sampleEquiv a.1 a.2) := by
  have hP := continuous_projectVector (k := k) (d := d)
  unfold sampleEquiv
  dsimp
  fun_prop

lemma joint_reference_log {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (κ : Observation (d/16) d → Fin N → ℝ≥0∞)
    (hκ : Measurable (Function.uncurry κ)) (hκ1 : ∀ z,∑ w,κ z w=1)
    (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1)
    {η : ℝ} (hη : 0 < η) (hηL : η ≤ radius L) :
    Integrable (fun t : Ambient d × Observation (d/16) d × Fin N =>
      Real.log (PairReference.density ν (fun j : Fin L => radius j) t.2.1.1.1 t.2.1.1.2 t.2.1.2.1 t.2.1.2.2))
      (joint ν (observationBase (d/16) d) (observationKernel η) κ) ∧
    B ν-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤
      ∫ t : Ambient d × Observation (d/16) d × Fin N,
        Real.log (PairReference.density ν (fun j : Fin L => radius j) t.2.1.1.1 t.2.1.1.2 t.2.1.2.1 t.2.1.2.2)
        ∂joint ν (observationBase (d/16) d) (observationKernel η) κ := by
  have := sampling_probability (d/16) d hη
  have := noise_probability (d/16) hη
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  let q : Observation (d/16) d → ℝ := fun z =>
    Real.log (PairReference.density ν (fun j : Fin L => radius j) z.1.1 z.1.2 z.2.1 z.2.2)
  have hq : Measurable q := (PairReference.density_measurable ν _).log
  let g : Ambient d × Observation (d/16) d → ℝ := fun a => q (sampleEquiv a.1 a.2)
  have hg : Measurable g := hq.comp sample_joint_measurable
  have hnorm : ∀ᵐ s ∂ν,‖s‖=1 :=
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (Sphere.ae_unit_norm (by omega : 0 < d))
  obtain ⟨M,_,hb⟩ := log_mixture_uniform_bound (p := 2*(d/16)) hL ν
    (fun j : Fin L => radius j) (fun j => radius_pos j) (by norm_num : (0:ℝ) ≤ 2) hη.le
  have hiE : Integrable (fun t : Observation (d/16) d => matEnergy (join (d/16) t.1))
      (samplingLaw (d/16) d η) := (integrable_pairEnergy (d/16) d).comp_fst _
  have hi : Integrable g (ν.prod (samplingLaw (d/16) d η)) := by
    refine (((integrable_const 1).add hiE).comp_snd ν).const_mul M |>.mono' hg.aestronglyMeasurable ?_
    have hs : ∀ᵐ a ∂ν.prod (samplingLaw (d/16) d η),‖a.1‖=1 :=
      measurePreserving_fst.quasiMeasurePreserving.ae hnorm
    have ht : ∀ᵐ a ∂ν.prod (samplingLaw (d/16) d η),∀ i,|join (d/16) a.2.2 i| ≤ η :=
      measurePreserving_snd.quasiMeasurePreserving.ae (sampling_noise_support (d/16) d hη)
    filter_upwards [hs,ht] with a hs ht
    have hsupport : ∀ᵐ u ∂ν,u ∈ closedBall a.1 2 := by
      filter_upwards [hnorm] with u hu
      rw [mem_closedBall,dist_eq_norm]
      exact (norm_sub_le _ _).trans (by rw [hu,hs]; norm_num)
    change |q (sampleEquiv a.1 a.2)| ≤ M*(1+matEnergy (join (d/16) a.2.1))
    dsimp only [q]
    rw [sample_density]
    exact hb a.1 hsupport (join (d/16) a.2.1) (join (d/16) a.2.2) ht
  have hK := observationKernel_measurable (k := d/16) (d := d) η
  have he (s : Ambient d) : (∫⁻ z,observationKernel η z s*‖q z‖ₑ ∂observationBase (d/16) d)=
      ∫⁻ t,‖g (s,t)‖ₑ ∂samplingLaw (d/16) d η := by
    have hKs : Measurable (fun z : Observation (d/16) d => observationKernel η z s) := by fun_prop
    calc
      _ = ∫⁻ z,‖q z‖ₑ ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s) := by
        simpa only [Pi.mul_apply] using (lintegral_withDensity_eq_lintegral_mul (observationBase (d/16) d) hKs hq.enorm).symm
      _ = _ := ((sample_measurePreserving hη s).lintegral_comp hq.enorm).symm
  have hiq : Integrable (fun t : Ambient d × Observation (d/16) d × Fin N => q t.2.1)
      (joint ν (observationBase (d/16) d) (observationKernel η) κ) := by
    apply joint_observation_integrable ν _ _ κ hK hκ hκ1 (fun a => q a.2) (hq.comp measurable_snd)
    simp_rw [he]
    rw [← lintegral_prod _ hg.enorm.aemeasurable]
    exact hi.hasFiniteIntegral
  refine ⟨hiq,?_⟩
  have hidentity := joint_observation_integral ν (observationBase (d/16) d) (observationKernel η) κ
    hK hκ (observationKernel_ne_top hη) hκ1 (fun a : Ambient d × Observation (d/16) d => q a.2) hiq
  change B ν-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤ ∫ t,q t.2.1 ∂joint ν _ _ κ
  rw [hidentity]
  have hiqν : Integrable (fun s => ∫ z,q z ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) ν :=
    hi.integral_prod_left.congr (ae_of_all _ (fun s => (sample_integral hη s q).symm))
  have hiJ := Coercivity.integrable_log_J hd ν ⟨H,hH,hν⟩ ν hnorm
  have hl := integral_mono_ae ((hiJ.sub (integrable_const (10*(d:ℝ)))).sub (integrable_const (2*Real.log ((L:ℝ)+2)))) hiqν
    (by
      filter_upwards [hnorm] with s hs
      exact noisy_reference_J_lower hd ν hH hν s hs L hL hcut hη hηL)
  simp only [Pi.sub_apply] at hl
  rw [integral_sub (show Integrable (fun s => Real.log (J ν s).toReal-10*(d:ℝ)) ν from hiJ.sub (integrable_const _)) (integrable_const (2*Real.log ((L:ℝ)+2))),
    integral_sub hiJ (integrable_const (10*(d:ℝ)))] at hl
  simpa only [integral_const,probReal_univ,one_smul,B] using hl
end KernelPotential.NoisyReference

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_JointRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity Sphere

lemma measurable_postCharge {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    {H : ℝ} (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    Measurable (Function.uncurry (postCharge ν rule η)) := by
  apply measurable_from_prod_countable_left
  intro w
  have := rule.post_prob hη ν w
  have hnorm : ∀ᵐ s ∂ν,‖s‖=1 := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have := Reweight.rho_finite (post ν (rule.response η w)) (withDensity_absolutelyContinuous _ _ |>.ae_le hnorm)
  exact (measurable_const.add (projectedReference_measurable (post ν (rule.response η w)) η).ennreal_toReal).log

lemma postCharge_uniform_bound {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ z w,0 ≤ postCharge ν rule η z w ∧ postCharge ν rule η z w ≤ M := by
  classical
  have hh (w : Fin N) : ∃ M : ℝ,0 ≤ M ∧ ∀ z,0 ≤ postCharge ν rule η z w ∧ postCharge ν rule η z w ≤ M := by
    have := rule.post_prob hη ν w
    have hb := post_bounded ν hH hν (rule.response η w) (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)
    have hnorm : ∀ᵐ s ∂post ν (rule.response η w),‖s‖=1 :=
      (Measure.absolutelyContinuous_of_le_smul hb).ae_le (ae_unit_norm (by omega : 0 < d))
    exact projected_log_bounded (post ν (rule.response η w)) hnorm hη
  choose M hM hb using hh
  refine ⟨∑ w,M w,Finset.sum_nonneg (fun w _ => hM w),fun z w => ⟨(hb w z).1,(hb w z).2.trans ?_⟩⟩
  exact Finset.single_le_sum (fun v _ => hM v) (Finset.mem_univ w)

end KernelPotential.NoisyDrift

end OAI
end

section
-- module Solutions.OAIQW_RepeatedLocalization.GaussianInformation_Kernel_ConditionalCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity

lemma reference_log_measurable {d N : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    Measurable (fun a : Ambient d × Fin N => Real.log (referenceWeight ν (rule.response η a.2) a.1)) := by
  apply measurable_from_prod_countable_left
  intro w
  exact (referenceWeight_measurable ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
    (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)).log

lemma reference_log_uniform_bound {d N : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,∀ s w,‖Real.log (referenceWeight ν (rule.response η w) s)‖ ≤ M := by
  classical
  have hb (w : Fin N) := referenceWeight_log_bounded hd ν hH hν _ (rule.measurable_response η w)
    rule.lower_pos (fun s => (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)
  choose M hM hb using hb
  refine ⟨∑ w,M w,fun s w => (hb w s).trans ?_⟩
  exact Finset.single_le_sum (fun v _ => hM v) (Finset.mem_univ w)

lemma joint_Phi_identity {d N : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w)))=
      (InformationTheory.klDiv ν (sphereProbability d)).toReal+
        ∫ t : Ambient d × Observation (d/16) d × Fin N,
          Real.log (referenceWeight ν (rule.response η t.2.2) t.1)
          ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel := by
  obtain ⟨f,hf,hf0,hfH,hνf⟩ := bounded_density_representation (sphereProbability d) ν hH hν
  have : IsProbabilityMeasure ((sphereProbability d).withDensity (fun s => ENNReal.ofReal (f s))) := hνf ▸ inferInstance
  have hD : (InformationTheory.klDiv ν (sphereProbability d)).toReal=∫ s,xlog (f s) ∂sphereProbability d := by
    rw [hνf,klDiv_withDensity_bounded _ f hf hf0 hfH,
      ENNReal.toReal_ofReal (density_entropy_nonneg _ f hf hf0 hfH)]
  obtain ⟨M,hM⟩ := reference_log_uniform_bound hd ν hH hν rule hη
  have hj := joint_integral_signal ν (observationBase (d/16) d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_ne_top hη)
    (observationKernel_probability hη) rule.sum_kernel
    (fun s w => Real.log (referenceWeight ν (rule.response η w) s)) (reference_log_measurable ν rule hη) hM
  rw [hj]
  change (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w)))=
    (InformationTheory.klDiv ν (sphereProbability d)).toReal+
      ∑ w,∫ s,rule.response η w s*Real.log (referenceWeight ν (rule.response η w) s) ∂ν
  simp_rw [weighted_Phi_identity hd ν f hf hf0 hH hfH hνf _ (rule.measurable_response η _)
    rule.lower_pos (fun s => (rule.response_bounds hη _ s).1) (fun s => (rule.response_bounds hη _ s).2)]
  rw [Finset.sum_add_distrib,hD]
  congr 1
  have hix := integrable_xlog_bounded (sphereProbability d) f hf hf0 hfH
  rw [← integral_finsetSum _ (fun w _ => hix.bdd_mul (rule.measurable_response η w).aestronglyMeasurable
    (ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rule.lower_pos.le.trans (rule.response_bounds hη w s).1)]
      exact (rule.response_bounds hη w s).2)))]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← Finset.sum_mul,rule.response_sum hη,one_mul]
end KernelPotential.NoisyDrift

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity Sphere
lemma referenceWeight_pos {d N : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (w) (s) :
    0 < referenceWeight ν (rule.response η w) s := by
  have := rule.post_prob hη ν w
  exact div_pos (rule.lower_pos.trans_le (rule.response_bounds hη w s).1)
    (mul_pos (rule.mass_pos hη ν w) (clippedJ_pos _ s))

lemma positive_noisy_comparison_oai {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (hηL : η ≤ Scale.radius (DriftCutoff.level d H)) :
    (∑ w,mass ν (rule.response η w)*Phi (post ν (rule.response η w))) ≤
      Phi ν+10*(d:ℝ)+2*Real.log ((DriftCutoff.level d H:ℝ)+2)+
        ∫ t : Ambient d × Observation (d/16) d × Fin N,postCharge ν rule η t.2.1 t.2.2
          ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let L := DriftCutoff.level d H
  have hL : 0 < L := DriftCutoff.level_pos d H
  let q : Observation (d/16) d → ℝ := fun z =>
    PairReference.density ν (fun j : Fin L => Scale.radius j) z.1.1 z.1.2 z.2.1 z.2.2
  have hq : Measurable q := PairReference.density_measurable ν _
  have hqp (z) : 0 < q z := PairReference.density_pos hL ν _ (fun j => Scale.radius_pos j) _ _ _ _
  have hq1 : ∫⁻ z,ENNReal.ofReal (q z) ∂observationBase (d/16) d=1 := by
    unfold observationBase
    rw [lintegral_prod _ hq.ennreal_ofReal.aemeasurable]
    simp_rw [q,PairReference.density_probability hL ν _ (fun j => Scale.radius_pos j)]
    have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
    simp
  let x : Fin N → Ambient d → ℝ≥0∞ := fun w s => ENNReal.ofReal (referenceWeight ν (rule.response η w) s)
  have hx : Measurable (Function.uncurry x) := by
    apply measurable_from_prod_countable_right
    intro w
    exact (referenceWeight_measurable ν _ (rule.measurable_response η w)
      (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
      (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)).ennreal_ofReal
  have hxe (w s) : (x w s).toReal=referenceWeight ν (rule.response η w) s :=
    ENNReal.toReal_ofReal (referenceWeight_pos ν rule hη w s).le
  have hCe (z : Observation (d/16) d) (w : Fin N) : C ν (observationKernel η) x z w=
      projectedReference (post ν (rule.response η w)) η z.1.1 z.1.2 z.2.1 z.2.2 :=
    C_eq_projectedReference hd ν hHp hν _ (rule.measurable_response η w)
      (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
      (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w) η z
  have hCf (z : Observation (d/16) d) (w : Fin N) : C ν (observationKernel η) x z w ≠ ∞ := by
    rw [hCe]
    have := rule.post_prob hη ν w
    have hp := post_bounded ν hHp hν _ (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)
    exact projectedReference_finite _ ((Measure.absolutelyContinuous_of_le_smul hp).ae_le
      (ae_unit_norm (by omega : 0 < d))) hη z
  have := joint_probability ν (observationBase (d/16) d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_probability hη) rule.sum_kernel
  obtain ⟨Mx,hMx⟩ := reference_log_uniform_bound hd ν hHp hν rule hη
  have hix : Integrable (fun t : Ambient d × Observation (d/16) d × Fin N => Real.log (x t.2.2 t.1).toReal)
      (joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel) := by
    simp_rw [hxe]
    refine Integrable.of_bound ((reference_log_measurable ν rule hη).comp (f := fun t : Ambient d × Observation (d/16) d × Fin N => (t.1,t.2.2))
      (measurable_fst.prodMk measurable_snd.snd)).aestronglyMeasurable Mx ?_
    exact ae_of_all _ (fun _ => hMx _ _)
  obtain ⟨Mq,_hMq,hMqb⟩ := postCharge_uniform_bound hd ν hHp hν rule hη
  have hiC : Integrable (fun t : Ambient d × Observation (d/16) d × Fin N =>
      Real.log (1+(C ν (observationKernel η) x t.2.1 t.2.2).toReal))
      (joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel) := by
    simp_rw [hCe]
    refine Integrable.of_bound ((measurable_postCharge hd ν hν rule hη).comp (f := fun t : Ambient d × Observation (d/16) d × Fin N => t.2) measurable_snd).aestronglyMeasurable Mq ?_
    exact ae_of_all _ (fun t => by change ‖postCharge ν rule η t.2.1 t.2.2‖ ≤ Mq; rw [Real.norm_eq_abs,abs_of_nonneg (hMqb _ _).1]; exact (hMqb _ _).2)
  obtain ⟨hiq,hqlo⟩ := NoisyReference.joint_reference_log hd ν hHp hν rule.kernel rule.measurable_kernel
    rule.sum_kernel L hL (DriftCutoff.reference_cut d hd hH) hη hηL
  have hqto (z) : (ENNReal.ofReal (q z)).toReal=q z := ENNReal.toReal_ofReal (hqp z).le
  have hc := log_comparison ν (observationBase (d/16) d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_probability hη) rule.sum_kernel
    x hx (fun w s => ENNReal.ofReal_pos.mpr (referenceWeight_pos ν rule hη w s))
    (fun _ _ => ENNReal.ofReal_ne_top) (fun z => ENNReal.ofReal (q z)) hq.ennreal_ofReal
    (fun z => ENNReal.ofReal_pos.mpr (hqp z)) (fun _ => ENNReal.ofReal_ne_top) hq1 hCf hix
    (by simpa only [hqto] using hiq) hiC
  simp_rw [hxe,hCe,hqto] at hc
  rw [joint_Phi_identity hd ν hHp hν rule hη]
  change (InformationTheory.klDiv ν (sphereProbability d)).toReal+_ ≤ _
  unfold Phi
  change B ν-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤ ∫ t,Real.log (q t.2.1)
    ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel at hqlo
  change _ ≤ (∫ t,postCharge ν rule η t.2.1 t.2.2 ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel)-
    ∫ t,Real.log (q t.2.1) ∂joint ν (observationBase (d/16) d) (observationKernel η) rule.kernel at hc
  linarith
end KernelPotential.NoisyDrift

end OAI
end

theorem solution : type_of% @OAI.KernelPotential.NoisyDrift.positive_noisy_comparison_oai := @OAI.KernelPotential.NoisyDrift.positive_noisy_comparison_oai
