-- Prove2me | solution 1 for NoHair.static_vacuum_linearized_einstein_decay
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:27:05.75051+00:00
-- url     : https://prove2.me/submissions/d3a4fc98-3c59-42b7-b69c-2f682589e2b2

import Theorems.Thm_NoHair_static_linearized_einstein_trace_identity
import Theorems.Thm_NoHair_asymptotic_static_cartesian_ricci_expansion
open NoHair Set Filter
open scoped ContDiff Manifold Topology

private theorem partial_eq_on_open {s : Set E4} (hs : IsOpen s) {f g : E4 → ℝ}
    (h : EqOn f g s) (k : Fin 4) {z : E4} (hz : z ∈ s) :
    coordPartial f k z = coordPartial g k z :=
  congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis k))
    (h.eventuallyEq_of_mem (hs.mem_nhds hz)).fderiv_eq

private lemma block_ricci_congr {s : Set E4} (hs : IsOpen s)
    {G' G : E4 → Matrix (Fin 4) (Fin 4) ℝ}
    (hG : EqOn G' G s) {y : E4} (hy : y ∈ s) (i j : Fin 4) :
    ricci G' y i j = ricci G y i j := by
  have dG (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => G' w i j) k z = coordPartial (fun w => G w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hG hw)) k hz
  have chr (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      christoffel G' z i j k = christoffel G z i j k := by
    simp only [christoffel, invMetric, hG hz, dG z hz]
  have dChr (z : E4) (hz : z ∈ s) (i j k l : Fin 4) :
      coordPartial (fun w => christoffel G' w i j k) l z =
      coordPartial (fun w => christoffel G w i j k) l z :=
    partial_eq_on_open hs (fun w hw => chr w hw i j k) l hz
  simp only [ricci, riemann, dChr y hy, chr y hy]

private lemma spatial_cont : Continuous conformalSpatialPoint := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> change Continuous (fun x : E4 => x _) <;> fun_prop

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ → ∀ i j : Fin 3,
      |negativeTwiceLinearEinstein (lapseCorrectedADMMetric c.N c.h) i j x| ≤ C / ‖x‖^4 := by
  classical
  obtain ⟨B,hB⟩ := c.compactComplement.isBounded.subset_closedBall (0 : ADMPoint)
  have tail (x : ADMPoint) (hx : B < ‖x‖) : x ∈ c.Ω := by
    by_contra hn
    have h := Metric.mem_closedBall.mp (hB hn)
    exact hx.not_ge (by simpa only [dist_zero_right] using h)
  have smooth (x : ADMPoint) (hx : B < ‖x‖) : ContDiffAt ℝ ∞ c.N x ∧
      (∀ i j, ContDiffAt ℝ ∞ (fun y => c.h y i j) x) ∧ (∀ i j, c.h x i j = c.h x j i) := by
    have w := c.extendsAcross (subset_closure (tail x hx))
    have n := c.openExtension.mem_nhds w
    refine ⟨c.smoothLapse.contDiffAt n,fun i j => (c.smoothMetric i j).contDiffAt n,?_⟩
    intro i j
    simpa only [star_trivial] using (c.positiveMetric x w).isHermitian.apply j i
  obtain ⟨R,C,rp,cp,err⟩ := asymptotic_static_cartesian_ricci_expansion c.N c.h ⟨B,smooth⟩
    (fun k _ => c.falloff k)
  let S := conformalSpatialPoint ⁻¹' c.Ω
  have so : IsOpen S := c.openSlice.preimage spatial_cont
  have eq : EqOn (pullbackCoeffs g c.ψ) (staticCartesianBlock c.N c.h) S := by
    intro z hz
    ext i j
    have v := c.staticMetric z hz (coordBasis i) (coordBasis j)
    change pullbackCoeffs g c.ψ z i j = _ at v
    rw [v]
    fin_cases i <;> fin_cases j <;>
      simp +decide [staticCartesianBlock,coordBasis,PiLp.single_apply,Fin.sum_univ_three] <;> rfl
  refine ⟨max R B,6*C,rp.trans_le (le_max_left _ _),by positivity,?_⟩
  intro x hx i j
  obtain ⟨hr,hb⟩ := max_lt_iff.mp hx
  have point : conformalSpatialPoint (staticTimeZero x) = x := by
    ext k
    fin_cases k <;> rfl
  have hxS : staticTimeZero x ∈ S := point ▸ tail x hb
  have vac (a b : Fin 4) : ricci (staticCartesianBlock c.N c.h) (staticTimeZero x) a b = 0 :=
    (block_ricci_congr so eq hxS a b).symm.trans (c.vacuum _ hxS a b)
  have er := err x hr
  simp only [vac,zero_sub,abs_neg] at er
  let Q := C / ‖x‖^4
  let A := fun i j : Fin 3 => staticPrincipalRicci c.N c.h i j x
  let L := flatLapseLaplacian c.N x
  have ha (i j : Fin 3) : |A i j| ≤ Q := er.2 i j
  have hl : |L| ≤ Q := er.1
  have tr : |∑ l : Fin 3, A l l| ≤ 3*Q := calc
    _ ≤ ∑ l : Fin 3, |A l l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin 3, Q := Finset.sum_le_sum fun l _ => ha l l
    _ = _ := by simp [Fin.sum_univ_three] <;> ring
  have qpos : 0 ≤ Q := by dsimp [Q]; positivity
  have he := smooth x hb
  rw [static_linearized_einstein_trace_identity c.N c.h x he.1 he.2.1 i j]
  change |-2 * A i j + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * ((∑ l : Fin 3, A l l) - L)| ≤ _
  have d : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    by_cases e : i=j <;> simp [Matrix.one_apply,e]
  calc
    _ ≤ |(-2:ℝ) * A i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j * ((∑ l : Fin 3, A l l)-L)| := abs_add_le _ _
    _ ≤ 2*Q + 1*(3*Q+Q) := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul (by norm_num) (ha i j) (abs_nonneg _) (by norm_num))
        (mul_le_mul d ((abs_sub _ _).trans (add_le_add tr hl)) (abs_nonneg _) zero_le_one)
    _ = 6*C/‖x‖^4 := by dsimp only [Q]; ring
